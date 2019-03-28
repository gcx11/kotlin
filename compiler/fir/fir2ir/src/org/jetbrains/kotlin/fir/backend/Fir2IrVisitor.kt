/*
 * Copyright 2010-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license
 * that can be found in the license/LICENSE.txt file.
 */

package org.jetbrains.kotlin.fir.backend

import com.intellij.psi.PsiFile
import org.jetbrains.kotlin.backend.common.descriptors.*
import org.jetbrains.kotlin.descriptors.*
import org.jetbrains.kotlin.fir.*
import org.jetbrains.kotlin.fir.declarations.*
import org.jetbrains.kotlin.fir.declarations.impl.*
import org.jetbrains.kotlin.fir.descriptors.FirModuleDescriptor
import org.jetbrains.kotlin.fir.expressions.*
import org.jetbrains.kotlin.fir.expressions.impl.FirElseIfTrueCondition
import org.jetbrains.kotlin.fir.expressions.impl.FirWhenSubjectExpression
import org.jetbrains.kotlin.fir.references.FirPropertyFromParameterCallableReference
import org.jetbrains.kotlin.fir.resolve.FirSymbolProvider
import org.jetbrains.kotlin.fir.resolve.buildUseSiteScope
import org.jetbrains.kotlin.fir.resolve.getCallableSymbols
import org.jetbrains.kotlin.fir.resolve.toSymbol
import org.jetbrains.kotlin.fir.scopes.ProcessorAction
import org.jetbrains.kotlin.fir.symbols.CallableId
import org.jetbrains.kotlin.fir.symbols.ConeClassLikeLookupTagImpl
import org.jetbrains.kotlin.fir.symbols.impl.FirClassSymbol
import org.jetbrains.kotlin.fir.symbols.impl.FirFunctionSymbol
import org.jetbrains.kotlin.fir.symbols.impl.FirTypeAliasSymbol
import org.jetbrains.kotlin.fir.symbols.impl.FirVariableSymbol
import org.jetbrains.kotlin.fir.types.ConeClassLikeType
import org.jetbrains.kotlin.fir.types.FirResolvedTypeRef
import org.jetbrains.kotlin.fir.types.FirTypeRef
import org.jetbrains.kotlin.fir.types.impl.ConeClassTypeImpl
import org.jetbrains.kotlin.fir.types.impl.FirResolvedTypeRefImpl
import org.jetbrains.kotlin.fir.visitors.FirVisitor
import org.jetbrains.kotlin.ir.IrElement
import org.jetbrains.kotlin.ir.IrStatement
import org.jetbrains.kotlin.ir.declarations.*
import org.jetbrains.kotlin.ir.declarations.impl.*
import org.jetbrains.kotlin.ir.descriptors.IrBuiltIns
import org.jetbrains.kotlin.ir.expressions.*
import org.jetbrains.kotlin.ir.expressions.impl.*
import org.jetbrains.kotlin.ir.symbols.*
import org.jetbrains.kotlin.ir.types.IrType
import org.jetbrains.kotlin.ir.types.classifierOrFail
import org.jetbrains.kotlin.ir.types.impl.IrErrorTypeImpl
import org.jetbrains.kotlin.ir.types.makeNullable
import org.jetbrains.kotlin.ir.util.*
import org.jetbrains.kotlin.name.ClassId
import org.jetbrains.kotlin.name.FqName
import org.jetbrains.kotlin.name.Name
import org.jetbrains.kotlin.psi.*
import org.jetbrains.kotlin.psi2ir.PsiSourceManager
import org.jetbrains.kotlin.types.Variance

class Fir2IrVisitor(
    private val session: FirSession,
    private val moduleDescriptor: FirModuleDescriptor,
    private val symbolTable: SymbolTable,
    private val irBuiltIns: IrBuiltIns
) : FirVisitor<IrElement, Any?>() {
    companion object {
        private val KOTLIN = FqName("kotlin")
    }

    private val typeContext = session.typeContext

    private val declarationStorage = Fir2IrDeclarationStorage(session, symbolTable, moduleDescriptor)

    private fun FqName.simpleType(name: String): IrType =
        FirResolvedTypeRefImpl(
            session, null,
            ConeClassTypeImpl(
                ConeClassLikeLookupTagImpl(
                    ClassId(this, Name.identifier(name))
                ),
                typeArguments = emptyArray(),
                isNullable = false
            ),
            isMarkedNullable = false,
            annotations = emptyList()
        ).toIrType(session, declarationStorage)

    private val nothingType = KOTLIN.simpleType("Nothing")

    private val unitType = KOTLIN.simpleType("Unit")

    private val booleanType = KOTLIN.simpleType("Boolean")

    private fun ModuleDescriptor.findPackageFragmentForFile(file: FirFile): PackageFragmentDescriptor =
        getPackage(file.packageFqName).fragments.first()

    private val parentStack = mutableListOf<IrDeclarationParent>()

    private fun <T : IrDeclarationParent> T.withParent(f: T.() -> Unit): T {
        parentStack += this
        f()
        parentStack.removeAt(parentStack.size - 1)
        return this
    }

    private fun <T : IrDeclaration> T.setParentByParentStack(): T {
        this.parent = parentStack.last()
        return this
    }

    private val functionStack = mutableListOf<IrSimpleFunction>()

    private fun <T : IrSimpleFunction> T.withFunction(f: T.() -> Unit): T {
        functionStack += this
        f()
        functionStack.removeAt(functionStack.size - 1)
        return this
    }

    private val propertyStack = mutableListOf<IrProperty>()

    private fun IrProperty.withProperty(f: IrProperty.() -> Unit): IrProperty {
        propertyStack += this
        f()
        propertyStack.removeAt(propertyStack.size - 1)
        return this
    }

    private val classStack = mutableListOf<IrClass>()

    private fun IrClass.withClass(f: IrClass.() -> Unit): IrClass {
        classStack += this
        f()
        classStack.removeAt(classStack.size - 1)
        return this
    }

    private val subjectVariableStack = mutableListOf<IrVariable>()

    private fun <T> IrVariable?.withSubject(f: () -> T): T {
        if (this != null) subjectVariableStack += this
        val result = f()
        if (this != null) subjectVariableStack.removeAt(subjectVariableStack.size - 1)
        return result
    }

    override fun visitElement(element: FirElement, data: Any?): IrElement {
        TODO("Should not be here")
    }

    override fun visitFile(file: FirFile, data: Any?): IrFile {
        return IrFileImpl(
            PsiSourceManager.PsiFileEntry(file.psi as PsiFile),
            moduleDescriptor.findPackageFragmentForFile(file)
        ).withParent {
            file.declarations.forEach {
                declarations += it.accept(this@Fir2IrVisitor, data) as IrDeclaration
            }

            file.annotations.forEach {
                annotations += it.accept(this@Fir2IrVisitor, data) as IrCall
            }
        }
    }

    private fun FirTypeRef.collectFunctionNamesFromThisAndSupertypes(result: MutableList<Name> = mutableListOf()): List<Name> {
        if (this is FirResolvedTypeRef) {
            val superType = type
            if (superType is ConeClassLikeType) {
                when (val superSymbol = superType.lookupTag.toSymbol(this@Fir2IrVisitor.session)) {
                    is FirClassSymbol -> {
                        val superClass = superSymbol.fir
                        for (declaration in superClass.declarations) {
                            if (declaration is FirNamedFunction) {
                                result += declaration.name
                            }
                        }
                        superClass.collectFunctionNamesFromSupertypes(result)
                    }
                    is FirTypeAliasSymbol -> {
                        val superAlias = superSymbol.fir
                        superAlias.expandedTypeRef.collectFunctionNamesFromThisAndSupertypes(result)
                    }
                }
            }
        }
        return result
    }

    private fun FirClass.collectFunctionNamesFromSupertypes(result: MutableList<Name> = mutableListOf()): List<Name> {
        for (superTypeRef in superTypeRefs) {
            superTypeRef.collectFunctionNamesFromThisAndSupertypes(result)
        }
        return result
    }

    private fun FirClass.getPrimaryConstructorIfAny(): FirConstructor? =
        (declarations.firstOrNull() as? FirConstructor)?.takeIf { it.isPrimary }

    private fun IrClass.setClassContent(klass: FirClass) {
        for (superTypeRef in klass.superTypeRefs) {
            superTypes += superTypeRef.toIrType(session, declarationStorage)
        }
        if (klass is FirRegularClass) {
            for ((index, typeParameter) in klass.typeParameters.withIndex()) {
                typeParameters += declarationStorage.getIrTypeParameter(typeParameter, index).setParentByParentStack()
            }
        }
        val useSiteScope = (klass as? FirRegularClass)?.buildUseSiteScope(session)
        val superTypesFunctionNames = klass.collectFunctionNamesFromSupertypes()
        symbolTable.enterScope(descriptor)
        val primaryConstructor = klass.getPrimaryConstructorIfAny()
        val irPrimaryConstructor = primaryConstructor?.accept(this@Fir2IrVisitor, null) as IrConstructor?
        withClass {
            if (irPrimaryConstructor != null) {
                declarations += irPrimaryConstructor
            }
            val processedFunctionNames = mutableListOf<Name>()
            klass.declarations.forEach {
                if (it !is FirConstructor || !it.isPrimary) {
                    declarations += it.accept(this@Fir2IrVisitor, null) as IrDeclaration
                    if (it is FirNamedFunction) {
                        processedFunctionNames += it.name
                    }
                }
            }
            for (name in superTypesFunctionNames) {
                if (name in processedFunctionNames) continue
                processedFunctionNames += name
                useSiteScope?.processFunctionsByName(name) { functionSymbol ->
                    if (functionSymbol is FirFunctionSymbol) {
                        val originalFunction = functionSymbol.fir as FirNamedFunction

                        val fakeOverrideSymbol = FirFunctionSymbol(functionSymbol.callableId, true)
                        val fakeOverrideFunction = with(originalFunction) {
                            // TODO: consider using here some light-weight functions instead of pseudo-real FirMemberFunctionImpl
                            // As second alternative, we can invent some light-weight kind of FirRegularClass
                            FirMemberFunctionImpl(
                                this@Fir2IrVisitor.session, psi, fakeOverrideSymbol,
                                name, receiverTypeRef, returnTypeRef
                            ).apply {
                                status = originalFunction.status as FirDeclarationStatusImpl
                                valueParameters += originalFunction.valueParameters.map { valueParameter ->
                                    with(valueParameter) {
                                        FirValueParameterImpl(
                                            this@Fir2IrVisitor.session, psi,
                                            this.name, this.returnTypeRef,
                                            defaultValue, isCrossinline, isNoinline, isVararg,
                                            FirVariableSymbol(valueParameter.symbol.callableId)
                                        )
                                    }
                                }
                            }
                        }

                        val irFunction = declarationStorage.getIrFunction(
                            fakeOverrideFunction, setParent = false, origin = IrDeclarationOrigin.FAKE_OVERRIDE
                        )
                        declarations += irFunction.setParentByParentStack().withFunction {
                            setFunctionContent(irFunction.descriptor, fakeOverrideFunction, firOverriddenSymbol = functionSymbol)
                        }

                    }
                    ProcessorAction.STOP
                }
            }
            klass.annotations.forEach {
                annotations += it.accept(this@Fir2IrVisitor, null) as IrCall
            }
        }
        if (irPrimaryConstructor != null) {
            symbolTable.leaveScope(irPrimaryConstructor.descriptor)
        }
        symbolTable.leaveScope(descriptor)
    }

    override fun visitRegularClass(regularClass: FirRegularClass, data: Any?): IrElement {
        return declarationStorage.getIrClass(regularClass, setParent = false)
            .setParentByParentStack()
            .withParent {
                setClassContent(regularClass)
            }
    }

    private fun <T : IrFunction> T.setFunctionContent(
        descriptor: FunctionDescriptor,
        firFunction: FirFunction,
        firOverriddenSymbol: FirFunctionSymbol? = null
    ): T {
        setParentByParentStack()
        withParent {
            val firFunctionSymbol = (firFunction as? FirNamedFunction)?.symbol
            val lastClass = classStack.lastOrNull()
            val containingClass = if (firOverriddenSymbol == null || firFunctionSymbol == null) {
                lastClass
            } else {
                val callableId = firFunctionSymbol.callableId
                val ownerClassId = callableId.classId
                if (ownerClassId == null) {
                    lastClass
                } else {
                    val classLikeSymbol = session.service<FirSymbolProvider>().getClassLikeSymbolByFqName(ownerClassId)
                    if (classLikeSymbol !is FirClassSymbol) {
                        lastClass
                    } else {
                        val firClass = classLikeSymbol.fir
                        declarationStorage.getIrClass(firClass, setParent = false)
                    }
                }
            }
            if (firFunction !is FirConstructor && containingClass != null) {
                val thisOrigin = IrDeclarationOrigin.DEFINED
                val thisType = containingClass.thisReceiver!!.type
                dispatchReceiverParameter = symbolTable.declareValueParameter(
                    startOffset, endOffset, thisOrigin, WrappedValueParameterDescriptor(),
                    thisType
                ) { symbol ->
                    IrValueParameterImpl(
                        startOffset, endOffset, thisOrigin, symbol,
                        Name.special("<this>"), -1, thisType,
                        varargElementType = null, isCrossinline = false, isNoinline = false
                    ).setParentByParentStack()
                }
            }
            for ((valueParameter, firValueParameter) in valueParameters.zip(firFunction.valueParameters)) {
                valueParameter.setDefaultValue(firValueParameter)
            }
            if (firOverriddenSymbol != null && this is IrSimpleFunction && firFunctionSymbol != null) {
                val overriddenSymbol = declarationStorage.getIrFunctionSymbol(firOverriddenSymbol)
                if (overriddenSymbol is IrSimpleFunctionSymbol) {
                    overriddenSymbols += overriddenSymbol
                }
            }
            body = firFunction.body?.convertToIrBlockBody()
            if (this !is IrConstructor || !this.isPrimary) {
                // Scope for primary constructor should be left after class declaration
                symbolTable.leaveScope(descriptor)
            }
        }
        return this
    }

    override fun visitConstructor(constructor: FirConstructor, data: Any?): IrElement {
        val irConstructor = declarationStorage.getIrConstructor(constructor, setParent = false)
        return irConstructor.setParentByParentStack().setFunctionContent(irConstructor.descriptor, constructor).apply {
            if (!parentAsClass.isAnnotationClass) {
                val body = this.body as IrBlockBody? ?: IrBlockBodyImpl(startOffset, endOffset)
                val delegatedConstructor = constructor.delegatedConstructor
                if (delegatedConstructor != null) {
                    body.statements += delegatedConstructor.accept(this@Fir2IrVisitor, null) as IrStatement
                }
                if (delegatedConstructor?.isThis == false) {
                    val irClass = parent as IrClass
                    body.statements += IrInstanceInitializerCallImpl(
                        startOffset, endOffset, irClass.symbol, constructedClassType
                    )
                }
                if (body.statements.isNotEmpty()) {
                    this.body = body
                }
            }
        }
    }

    override fun visitAnonymousInitializer(anonymousInitializer: FirAnonymousInitializer, data: Any?): IrElement {
        val origin = IrDeclarationOrigin.DEFINED
        val parent = parentStack.last() as IrClass
        return anonymousInitializer.convertWithOffsets { startOffset, endOffset ->
            symbolTable.declareAnonymousInitializer(
                startOffset, endOffset, origin, parent.descriptor
            ).apply {
                symbolTable.enterScope(descriptor)
                body = anonymousInitializer.body!!.convertToIrBlockBody()
                symbolTable.leaveScope(descriptor)
            }
        }
    }

    override fun visitDelegatedConstructorCall(delegatedConstructorCall: FirDelegatedConstructorCall, data: Any?): IrElement {
        val constructedTypeRef = delegatedConstructorCall.constructedTypeRef
        val constructedClassSymbol = with(typeContext) {
            (constructedTypeRef as FirResolvedTypeRef).type.typeConstructor()
        } as FirClassSymbol
        val constructedIrType = constructedTypeRef.toIrType(session, declarationStorage)
        // TODO: find delegated constructor correctly
        val classId = constructedClassSymbol.classId
        val constructorId = CallableId(classId.packageFqName, classId.relativeClassName, classId.shortClassName)
        val constructorSymbol = session.service<FirSymbolProvider>().getCallableSymbols(constructorId).first {
            delegatedConstructorCall.arguments.size <= ((it as FirFunctionSymbol).fir as FirFunction).valueParameters.size
        }
        return delegatedConstructorCall.convertWithOffsets { startOffset, endOffset ->
            IrDelegatingConstructorCallImpl(
                startOffset, endOffset,
                constructedIrType,
                declarationStorage.getIrFunctionSymbol(constructorSymbol as FirFunctionSymbol) as IrConstructorSymbol
            ).apply {
                for ((index, argument) in delegatedConstructorCall.arguments.withIndex()) {
                    val argumentExpression = argument.accept(this@Fir2IrVisitor, data) as IrExpression
                    putValueArgument(index, argumentExpression)
                }
            }
        }
    }

    override fun visitNamedFunction(namedFunction: FirNamedFunction, data: Any?): IrElement {
        val irFunction = declarationStorage.getIrFunction(namedFunction, setParent = false)
        return irFunction.setParentByParentStack().withFunction {
            setFunctionContent(irFunction.descriptor, namedFunction)
        }
    }

    private fun IrValueParameter.setDefaultValue(firValueParameter: FirValueParameter) {
        val firDefaultValue = firValueParameter.defaultValue
        if (firDefaultValue != null) {
            this.defaultValue = IrExpressionBodyImpl(
                firDefaultValue.accept(this@Fir2IrVisitor, null) as IrExpression
            )
        }
    }

    override fun visitVariable(variable: FirVariable, data: Any?): IrElement {
        val irVariable = declarationStorage.getIrVariable(variable)
        return irVariable.setParentByParentStack().apply {
            val initializer = variable.initializer
            if (initializer != null) {
                this.initializer = initializer.accept(this@Fir2IrVisitor, data) as IrExpression
            }
        }
    }

    private fun IrProperty.setPropertyContent(descriptor: PropertyDescriptor, property: FirProperty): IrProperty {
        val initializer = property.initializer
        val irParent = this.parent
        val type = property.returnTypeRef.toIrType(session, declarationStorage)
        // TODO: this checks are very preliminary, FIR resolve should determine backing field presence itself
        if (property.modality != Modality.ABSTRACT && (irParent !is IrClass || !irParent.isInterface)) {
            if (initializer != null || property.getter is FirDefaultPropertyGetter ||
                property.isVar && property.setter is FirDefaultPropertySetter
            ) {
                val backingOrigin = IrDeclarationOrigin.PROPERTY_BACKING_FIELD
                backingField = symbolTable.declareField(
                    startOffset, endOffset, backingOrigin, descriptor, type
                ) { symbol ->
                    IrFieldImpl(
                        startOffset, endOffset, backingOrigin, symbol,
                        property.name, type, property.visibility,
                        isFinal = property.isVal, isExternal = false, isStatic = property.isStatic
                    )
                }.apply {
                    val initializerExpression = initializer?.accept(this@Fir2IrVisitor, null) as IrExpression?
                    this.initializer = initializerExpression?.let { IrExpressionBodyImpl(it) }
                }
            }
        }
        getter = property.getter.accept(this@Fir2IrVisitor, type) as IrSimpleFunction
        if (property.isVar) {
            setter = property.setter.accept(this@Fir2IrVisitor, type) as IrSimpleFunction
        }
        property.annotations.forEach {
            annotations += it.accept(this@Fir2IrVisitor, null) as IrCall
        }
        return this
    }

    override fun visitProperty(property: FirProperty, data: Any?): IrProperty {
        val irProperty = declarationStorage.getIrProperty(property, setParent = false)
        return irProperty.setParentByParentStack().withProperty { setPropertyContent(irProperty.descriptor, property) }
    }

    private fun IrFieldAccessExpression.setReceiver(declaration: IrDeclaration): IrFieldAccessExpression {
        if (declaration is IrFunction) {
            val dispatchReceiver = declaration.dispatchReceiverParameter
            if (dispatchReceiver != null) {
                receiver = IrGetValueImpl(startOffset, endOffset, dispatchReceiver.symbol)
            }
        }
        return this
    }

    private fun createPropertyAccessor(
        propertyAccessor: FirPropertyAccessor, startOffset: Int, endOffset: Int,
        correspondingProperty: IrProperty, isDefault: Boolean, propertyType: IrType
    ): IrSimpleFunction {
        val origin = when {
            isDefault -> IrDeclarationOrigin.DEFAULT_PROPERTY_ACCESSOR
            else -> IrDeclarationOrigin.DEFINED
        }
        val isSetter = propertyAccessor.isSetter
        val prefix = if (isSetter) "set" else "get"
        val descriptor = WrappedSimpleFunctionDescriptor()
        return symbolTable.declareSimpleFunction(
            startOffset, endOffset, origin, descriptor
        ) { symbol ->
            val accessorReturnType = propertyAccessor.returnTypeRef.toIrType(session, declarationStorage)
            IrFunctionImpl(
                startOffset, endOffset, origin, symbol,
                Name.special("<$prefix-${correspondingProperty.name}>"),
                propertyAccessor.visibility, correspondingProperty.modality, accessorReturnType,
                isInline = false, isExternal = false, isTailrec = false, isSuspend = false
            ).withFunction {
                descriptor.bind(this)
                symbolTable.enterScope(descriptor)
                setFunctionContent(descriptor, propertyAccessor).apply {
                    correspondingPropertySymbol = symbolTable.referenceProperty(correspondingProperty.descriptor)
                    if (isDefault) {
                        withParent {
                            symbolTable.enterScope(descriptor)
                            val backingField = correspondingProperty.backingField
                            if (isSetter) {
                                valueParameters += symbolTable.declareValueParameter(
                                    startOffset, endOffset, origin, WrappedValueParameterDescriptor(), propertyType
                                ) { symbol ->
                                    IrValueParameterImpl(
                                        startOffset, endOffset, IrDeclarationOrigin.DEFINED, symbol,
                                        Name.special("<set-?>"), 0, propertyType,
                                        varargElementType = null,
                                        isCrossinline = false, isNoinline = false
                                    ).setParentByParentStack()
                                }
                            }
                            val fieldSymbol = symbolTable.referenceField(correspondingProperty.descriptor)
                            val declaration = this
                            if (backingField != null) {
                                body = IrBlockBodyImpl(
                                    startOffset, endOffset,
                                    listOf(
                                        if (isSetter) {
                                            IrSetFieldImpl(startOffset, endOffset, fieldSymbol, accessorReturnType).apply {
                                                setReceiver(declaration)
                                                value = IrGetValueImpl(startOffset, endOffset, propertyType, valueParameters.first().symbol)
                                            }
                                        } else {
                                            IrReturnImpl(
                                                startOffset, endOffset, nothingType, symbol,
                                                IrGetFieldImpl(startOffset, endOffset, fieldSymbol, propertyType).setReceiver(declaration)
                                            )
                                        }
                                    )
                                )
                            }
                            symbolTable.leaveScope(descriptor)
                        }
                    }
                }
            }
        }
    }

    override fun visitPropertyAccessor(propertyAccessor: FirPropertyAccessor, data: Any?): IrElement {
        val correspondingProperty = propertyStack.last()
        return propertyAccessor.convertWithOffsets { startOffset, endOffset ->
            createPropertyAccessor(
                propertyAccessor, startOffset, endOffset, correspondingProperty,
                isDefault = propertyAccessor is FirDefaultPropertyGetter || propertyAccessor is FirDefaultPropertySetter,
                propertyType = data as IrType
            )
        }
    }

    override fun visitReturnExpression(returnExpression: FirReturnExpression, data: Any?): IrElement {
        val firTarget = returnExpression.target.labeledElement
        var irTarget = functionStack.last()
        for (potentialTarget in functionStack.asReversed()) {
            // TODO: remove comparison by name
            if (potentialTarget.name == (firTarget as? FirNamedFunction)?.name) {
                irTarget = potentialTarget
                break
            }
        }
        return returnExpression.convertWithOffsets { startOffset, endOffset ->
            IrReturnImpl(
                startOffset, endOffset, nothingType,
                symbolTable.referenceSimpleFunction(irTarget.descriptor),
                returnExpression.result.accept(this, data) as IrExpression
            )
        }
    }

    private fun FirQualifiedAccess.toIrExpression(typeRef: FirTypeRef): IrExpression {
        val type = typeRef.toIrType(this@Fir2IrVisitor.session, declarationStorage)
        val symbol = calleeReference.toSymbol(declarationStorage)
        return typeRef.convertWithOffsets { startOffset, endOffset ->
            when {
                symbol is IrFunctionSymbol -> IrCallImpl(startOffset, endOffset, type, symbol)
                symbol is IrPropertySymbol && symbol.isBound -> {
                    val getter = symbol.owner.getter
                    if (getter != null) {
                        IrCallImpl(startOffset, endOffset, type, getter.symbol)
                    } else {
                        IrErrorCallExpressionImpl(startOffset, endOffset, type, "No getter found for ${calleeReference.render()}")
                    }
                }
                symbol is IrValueSymbol -> IrGetValueImpl(
                    startOffset, endOffset, type, symbol,
                    if (calleeReference is FirPropertyFromParameterCallableReference) {
                        IrStatementOrigin.INITIALIZE_PROPERTY_FROM_PARAMETER
                    } else null
                )
                else -> IrErrorCallExpressionImpl(startOffset, endOffset, type, "Unresolved reference: ${calleeReference.render()}")
            }
        }
    }

    override fun visitFunctionCall(functionCall: FirFunctionCall, data: Any?): IrElement {
        return when (val irCall = functionCall.toIrExpression(functionCall.typeRef)) {
            is IrCallImpl -> irCall.apply {
                for ((index, argument) in functionCall.arguments.withIndex()) {
                    val argumentExpression = argument.accept(this@Fir2IrVisitor, data) as IrExpression
                    putValueArgument(index, argumentExpression)
                }
            }
            is IrErrorCallExpressionImpl -> irCall.apply {
                for (argument in functionCall.arguments) {
                    addArgument(argument.accept(this@Fir2IrVisitor, data) as IrExpression)
                }
            }
            else -> irCall
        }
    }

    override fun visitQualifiedAccessExpression(qualifiedAccessExpression: FirQualifiedAccessExpression, data: Any?): IrElement {
        return qualifiedAccessExpression.toIrExpression(qualifiedAccessExpression.typeRef)
    }

    private fun generateErrorCallExpression(startOffset: Int, endOffset: Int, calleeReference: FirReference): IrErrorCallExpression {
        return IrErrorCallExpressionImpl(
            startOffset, endOffset, IrErrorTypeImpl(null, emptyList(), Variance.INVARIANT),
            "Unresolved reference: ${calleeReference.render()}"
        )
    }

    override fun visitVariableAssignment(variableAssignment: FirVariableAssignment, data: Any?): IrElement {
        val calleeReference = variableAssignment.calleeReference
        val symbol = calleeReference.toSymbol(declarationStorage)
        return variableAssignment.convertWithOffsets { startOffset, endOffset ->
            if (symbol != null && symbol.isBound) {
                when (symbol) {
                    is IrFieldSymbol -> IrSetFieldImpl(
                        startOffset, endOffset, symbol, symbol.owner.type
                    ).apply {
                        value = variableAssignment.rValue.accept(this@Fir2IrVisitor, data) as IrExpression
                    }
                    is IrPropertySymbol -> {
                        val irProperty = symbol.owner
                        val backingField = irProperty.backingField
                        if (backingField != null) {
                            IrSetFieldImpl(
                                startOffset, endOffset, backingField.symbol, backingField.symbol.owner.type
                            ).apply {
                                value = variableAssignment.rValue.accept(this@Fir2IrVisitor, data) as IrExpression
                            }
                        } else {
                            generateErrorCallExpression(startOffset, endOffset, calleeReference)
                        }
                    }
                    else -> generateErrorCallExpression(startOffset, endOffset, calleeReference)
                }
            } else {
                generateErrorCallExpression(startOffset, endOffset, calleeReference)
            }
        }
    }

    override fun <T> visitConstExpression(constExpression: FirConstExpression<T>, data: Any?): IrElement {
        return constExpression.convertWithOffsets { startOffset, endOffset ->
            IrConstImpl(
                startOffset, endOffset,
                constExpression.typeRef.toIrType(session, declarationStorage),
                constExpression.kind, constExpression.value
            )
        }
    }

    override fun visitAnonymousObject(anonymousObject: FirAnonymousObject, data: Any?): IrElement {
        return anonymousObject.convertWithOffsets { startOffset, endOffset ->
            val descriptor = WrappedClassDescriptor()
            val origin = IrDeclarationOrigin.DEFINED
            val modality = Modality.FINAL
            val anonymousClass = symbolTable.declareClass(startOffset, endOffset, origin, descriptor, modality) { symbol ->
                IrClassImpl(
                    startOffset, endOffset, origin, symbol,
                    Name.special("<no name provided>"), anonymousObject.classKind,
                    Visibilities.LOCAL, modality,
                    isCompanion = false, isInner = false, isData = false, isExternal = false, isInline = false
                ).setParentByParentStack().withParent {
                    setClassContent(anonymousObject)
                }
            }
            val anonymousClassType = anonymousClass.thisReceiver!!.type
            IrBlockImpl(
                startOffset, endOffset, anonymousClassType, IrStatementOrigin.OBJECT_LITERAL,
                listOf(
                    anonymousClass,
                    IrCallImpl(startOffset, endOffset, anonymousClassType, anonymousClass.constructors.first().symbol)
                )
            )
        }
    }

    // ==================================================================================

    private fun FirBlock.convertToIrBlockBody(): IrBlockBody {
        return convertWithOffsets { startOffset, endOffset ->
            IrBlockBodyImpl(
                startOffset, endOffset, statements.map { it.accept(this@Fir2IrVisitor, null) as IrStatement }
            )
        }
    }

    private fun FirBlock.convertToIrExpressionOrBlock(): IrExpression {
        if (statements.size == 1) {
            val firStatement = statements.single()
            if (firStatement is FirExpression) {
                return firStatement.toIrExpression()
            }
        }
        val type =
            (statements.lastOrNull() as? FirExpression)?.typeRef?.toIrType(this@Fir2IrVisitor.session, declarationStorage) ?: unitType
        return convertWithOffsets { startOffset, endOffset ->
            IrBlockImpl(startOffset, endOffset, type, null, statements.map { it.accept(this@Fir2IrVisitor, null) as IrStatement })
        }
    }

    private fun FirExpression.toIrExpression(): IrExpression {
        return when {
            this is FirBlock -> convertToIrExpressionOrBlock()
            this is FirWhenSubjectExpression -> {
                val lastSubjectVariable = subjectVariableStack.last()
                convertWithOffsets { startOffset, endOffset ->
                    IrGetValueImpl(startOffset, endOffset, lastSubjectVariable.type, lastSubjectVariable.symbol)
                }
            }
            else -> accept(this@Fir2IrVisitor, null) as IrExpression
        }
    }

    private fun generateWhenSubjectVariable(whenExpression: FirWhenExpression): IrVariable? {
        val subjectVariable = whenExpression.subjectVariable
        val subjectExpression = whenExpression.subject
        return when {
            subjectVariable != null -> subjectVariable.accept(this, null) as IrVariable
            subjectExpression != null -> declarationStorage.declareTemporaryVariable(subjectExpression.toIrExpression(), "subject")
            else -> null
        }
    }

    override fun visitWhenExpression(whenExpression: FirWhenExpression, data: Any?): IrElement {
        val subjectVariable = generateWhenSubjectVariable(whenExpression)
        val origin = when (whenExpression.psi) {
            is KtWhenExpression -> IrStatementOrigin.WHEN
            is KtIfExpression -> IrStatementOrigin.IF
            is KtBinaryExpression -> IrStatementOrigin.ELVIS
            is KtUnaryExpression -> IrStatementOrigin.EXCLEXCL
            else -> null
        }
        return subjectVariable.withSubject {
            whenExpression.convertWithOffsets { startOffset, endOffset ->
                val irWhen = IrWhenImpl(
                    startOffset, endOffset,
                    whenExpression.typeRef.toIrType(session, declarationStorage),
                    origin
                ).apply {
                    for (branch in whenExpression.branches) {
                        if (branch.condition !is FirElseIfTrueCondition || branch.result.statements.isNotEmpty()) {
                            branches += branch.accept(this@Fir2IrVisitor, data) as IrBranch
                        }
                    }
                }
                if (subjectVariable == null) {
                    irWhen
                } else {
                    IrBlockImpl(startOffset, endOffset, irWhen.type, origin, listOf(subjectVariable, irWhen))
                }
            }
        }
    }

    override fun visitWhenBranch(whenBranch: FirWhenBranch, data: Any?): IrElement {
        return whenBranch.convertWithOffsets { startOffset, endOffset ->
            val condition = whenBranch.condition
            val irResult = whenBranch.result.toIrExpression()
            if (condition is FirElseIfTrueCondition) {
                IrElseBranchImpl(IrConstImpl.boolean(irResult.startOffset, irResult.endOffset, booleanType, true), irResult)
            } else {
                IrBranchImpl(startOffset, endOffset, condition.toIrExpression(), irResult)
            }
        }
    }

    override fun visitDoWhileLoop(doWhileLoop: FirDoWhileLoop, data: Any?): IrElement {
        return doWhileLoop.convertWithOffsets { startOffset, endOffset ->
            IrDoWhileLoopImpl(
                startOffset, endOffset, unitType,
                IrStatementOrigin.DO_WHILE_LOOP
            ).apply {
                condition = doWhileLoop.condition.toIrExpression()
                body = doWhileLoop.block.convertToIrExpressionOrBlock()
            }
        }
    }

    override fun visitWhileLoop(whileLoop: FirWhileLoop, data: Any?): IrElement {
        return whileLoop.convertWithOffsets { startOffset, endOffset ->
            IrWhileLoopImpl(
                startOffset, endOffset, unitType,
                if (whileLoop.psi is KtForExpression) IrStatementOrigin.FOR_LOOP_INNER_WHILE
                else IrStatementOrigin.WHILE_LOOP
            ).apply {
                condition = whileLoop.condition.toIrExpression()
                body = whileLoop.block.convertToIrExpressionOrBlock()
            }
        }
    }

    override fun visitThrowExpression(throwExpression: FirThrowExpression, data: Any?): IrElement {
        return throwExpression.convertWithOffsets { startOffset, endOffset ->
            IrThrowImpl(startOffset, endOffset, nothingType, throwExpression.exception.toIrExpression())
        }
    }

    override fun visitTryExpression(tryExpression: FirTryExpression, data: Any?): IrElement {
        return tryExpression.convertWithOffsets { startOffset, endOffset ->
            IrTryImpl(
                startOffset, endOffset, tryExpression.typeRef.toIrType(session, declarationStorage),
                tryExpression.tryBlock.convertToIrExpressionOrBlock(),
                tryExpression.catches.map { it.accept(this, data) as IrCatch },
                tryExpression.finallyBlock?.convertToIrExpressionOrBlock()
            )
        }
    }

    override fun visitCatch(catch: FirCatch, data: Any?): IrElement {
        return catch.convertWithOffsets { startOffset, endOffset ->
            IrCatchImpl(startOffset, endOffset, declarationStorage.getIrVariable(catch.parameter)).apply {
                result = catch.block.convertToIrExpressionOrBlock()
            }
        }
    }

    override fun visitOperatorCall(operatorCall: FirOperatorCall, data: Any?): IrElement {
        return operatorCall.convertWithOffsets { startOffset, endOffset ->
            val (type, symbol) = when (operatorCall.operation) {
                FirOperation.EQ -> booleanType to irBuiltIns.eqeqSymbol
                FirOperation.NOT_EQ -> TODO()
                FirOperation.RANGE -> TODO()
                FirOperation.IDENTITY -> TODO()
                FirOperation.NOT_IDENTITY -> TODO()
                FirOperation.LT -> TODO()
                FirOperation.GT -> TODO()
                FirOperation.LT_EQ -> TODO()
                FirOperation.GT_EQ -> TODO()
                FirOperation.AND -> TODO()
                FirOperation.OR -> TODO()
                FirOperation.IN -> TODO()
                FirOperation.NOT_IN -> TODO()
                FirOperation.ASSIGN -> TODO()
                FirOperation.PLUS_ASSIGN -> TODO()
                FirOperation.MINUS_ASSIGN -> TODO()
                FirOperation.TIMES_ASSIGN -> TODO()
                FirOperation.DIV_ASSIGN -> TODO()
                FirOperation.REM_ASSIGN -> TODO()
                FirOperation.EXCL -> TODO()
                FirOperation.OTHER -> TODO()
                FirOperation.IS, FirOperation.NOT_IS,
                FirOperation.AS, FirOperation.SAFE_AS -> {
                    TODO("Should not be here")
                }
            }
            IrBinaryPrimitiveImpl(
                startOffset, endOffset, type, null, symbol,
                operatorCall.arguments[0].toIrExpression(),
                operatorCall.arguments[1].toIrExpression()
            )
        }
    }

    override fun visitTypeOperatorCall(typeOperatorCall: FirTypeOperatorCall, data: Any?): IrElement {
        return typeOperatorCall.convertWithOffsets { startOffset, endOffset ->
            val irTypeOperand = typeOperatorCall.conversionTypeRef.toIrType(session, declarationStorage)
            val (irType, irTypeOperator) = when (typeOperatorCall.operation) {
                FirOperation.IS -> booleanType to IrTypeOperator.INSTANCEOF
                FirOperation.NOT_IS -> booleanType to IrTypeOperator.NOT_INSTANCEOF
                FirOperation.AS -> irTypeOperand to IrTypeOperator.CAST
                FirOperation.SAFE_AS -> irTypeOperand.makeNullable() to IrTypeOperator.SAFE_CAST
                else -> TODO("Should not be here: ${typeOperatorCall.operation} in type operator call")
            }

            IrTypeOperatorCallImpl(
                startOffset, endOffset, irType, irTypeOperator, irTypeOperand,
                irTypeOperand.classifierOrFail, typeOperatorCall.argument.toIrExpression()
            )
        }
    }

    override fun visitGetClassCall(getClassCall: FirGetClassCall, data: Any?): IrElement {
        return getClassCall.convertWithOffsets { startOffset, endOffset ->
            IrGetClassImpl(
                startOffset, endOffset, getClassCall.typeRef.toIrType(session, declarationStorage),
                getClassCall.argument.toIrExpression()
            )
        }
    }
}