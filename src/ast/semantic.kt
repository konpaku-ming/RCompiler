package ast

sealed interface ResolvedType {
    val name: String
}

data class NamedResolvedType(
    override val name: String,
    val symbol: Symbol
) : ResolvedType

data class PrimitiveResolvedType(
    override val name: String
) : ResolvedType

data class ReferenceResolvedType(
    val inner: ResolvedType,
    val mutable: Boolean
) : ResolvedType {
    override val name: String = if (mutable) {
        "&mut " + inner.name
    } else {
        "&" + inner.name
    }
}

data class ArrayResolvedType(
    val elementType: ResolvedType,
    val length: Int // 数组长度应在编译时可以得到
) : ResolvedType {
    override val name: String = "[${elementType.name}; ${length}]"
}

class UnitResolvedType : ResolvedType {
    override val name: String = "()"
}

class SelfResolvedType : ResolvedType {
    override val name: String = "Self"
}

class BottomResolvedType : ResolvedType {
    // 将必定return的expr标记为bottom类型
    override val name: String = "bottom"
}

class NeverResolvedType : ResolvedType {
    // 将必定break的expr标记为bottom类型
    override val name: String = "!"
}

// 未知类型，待推断
class UnknownResolvedType : ResolvedType {
    override val name: String = "<unknown>"
}

class SemanticVisitor(private val scopeStack: ScopeStack) : ASTVisitor {
    private var currentLoopNode: LoopExprNode? = null // 标记当前循环块，用于break检查
    private var currentFnType: ResolvedType? = null
    private var currentImpl: Pair<ResolvedType, TraitSymbol?>? = null
    private var currentTrait: String? = null
    private val implRegistry = ImplRegistry()
    private val errors = mutableListOf<String>()

    // tool functions
    private fun reportError(msg: String) {
        errors.add(msg)
        println("Semantic Error: $msg")
    }

    fun getErrors(): List<String> = errors

    fun evalConstExpr(expr: ExprNode): Int {
        return when (expr) {
            is IntLiteralExprNode -> stringToInt(expr.raw)
            // 这里可以扩展支持简单的常量运算
            else -> error("Unknown const expr")
        }
    }

    fun resolveType(node: TypeNode): ResolvedType {
        return when (node) {
            is TypePathNode -> {
                when (val name = node.path.segment.value) {
                    "Self" -> SelfResolvedType()
                    "u32" -> PrimitiveResolvedType("u32")
                    "i32" -> PrimitiveResolvedType("i32")
                    "bool" -> PrimitiveResolvedType("bool")
                    "char" -> PrimitiveResolvedType("char")
                    "str" -> PrimitiveResolvedType("str")
                    else -> {
                        val symbol = scopeStack.lookup(name)
                        if (symbol is StructSymbol || symbol is TraitSymbol || symbol is EnumSymbol) {
                            NamedResolvedType(symbol.name, symbol)
                        } else {
                            reportError("Unknown type: $name")
                            UnknownResolvedType()
                        }
                    }
                }
            }

            is ReferenceTypeNode -> {
                val inner = resolveType(node.tar)
                ReferenceResolvedType(inner, node.isMut)
            }

            is ArrayTypeNode -> {
                val element = resolveType(node.elementType)
                val lengthValue = evalConstExpr(node.length) // 常量求值
                ArrayResolvedType(element, lengthValue)
            }

            is UnitTypeNode -> UnitResolvedType()
        }
    }

    fun isNumeric(resolvedType: ResolvedType): Boolean {
        return when (resolvedType) {
            PrimitiveResolvedType("i32"),
            PrimitiveResolvedType("u32") -> true

            else -> false
        }
    }

    fun resolvePathExpr(path: PathExprNode): Symbol {
        val firstSegment = path.first.segment
        val secondSegment = path.second
        when (firstSegment.type) {
            TokenType.IDENTIFIER -> {
                val symbol = scopeStack.lookup(firstSegment.value)
                if (symbol == null) {
                    error("cannot resolve path '$path'")
                } else {
                    // 解析第一层
                    when (symbol) {
                        is VariableSymbol,
                        is ConstantSymbol,
                        is FunctionSymbol -> {
                            if (secondSegment == null) {
                                return symbol
                            } else {
                                error("cannot resolve path '$path'")
                            }
                        }

                        is StructSymbol -> {
                            if (secondSegment == null) {
                                error("cannot resolve path '$path'")
                            } else {
                                // 找到struct对应类型
                                val secondName = secondSegment.segment.value
                                val type = NamedResolvedType(symbol.name, symbol)
                                val implList = implRegistry.getImplsForType(type)
                                for (impl in implList) {
                                    val constant = impl.constants[secondName]
                                    if (constant != null) return constant
                                    val function = impl.functions[secondName]
                                    if (function != null) return function
                                }
                                error("cannot resolve path '$path'")
                            }
                        }

                        is EnumSymbol -> {
                            if (secondSegment == null) {
                                error("cannot resolve path '$path'")
                            } else {
                                val secondName = secondSegment.segment.value
                                if (symbol.variants.contains(secondName)) {
                                    return VariableSymbol(
                                        name = secondName,
                                        type = NamedResolvedType(firstSegment.value, symbol),
                                        isMut = false
                                    )
                                } else {
                                    error("cannot resolve path '$path'")
                                }
                            }
                        }

                        is TraitSymbol -> {
                            if (secondSegment == null) {
                                error("cannot resolve path '$path'")
                            } else error("Cannot refer to the associated item on trait '$symbol'")
                        }
                    }
                }
            }

            TokenType.SELF -> {
                // 当前impl的item
                if (currentImpl != null) {
                    val implType = currentImpl!!.first
                    if (implType is NamedResolvedType) {
                        return implType.symbol
                    } else {
                        error("cannot resolve path '$path'")
                    }
                } else {
                    error("cannot resolve path '$path'")
                }
            }

            TokenType.SELF_CAP -> {
                val implInfo = currentImpl
                if (implInfo != null) {
                    val implHistory = implRegistry.getTraitImpl(implInfo.first, implInfo.second)
                    if (implHistory != null && secondSegment != null) {
                        val secondName = secondSegment.segment.value
                        val constant = implHistory.constants[secondName]
                        if (constant != null) return constant
                        val function = implHistory.functions[secondName]
                        if (function != null) return function
                        error("cannot resolve path '$path'")
                    } else {
                        error("cannot resolve path '$path'")
                    }
                } else if (currentTrait != null) {
                    if (secondSegment != null) {
                        val secondName = secondSegment.segment.value
                        val trait = scopeStack.lookup(currentTrait!!)
                        if (trait is TraitSymbol) {
                            val constant = trait.constants[secondName]
                            if (constant != null) return constant
                            val function = trait.functions[secondName]
                            if (function != null) return function
                            error("cannot resolve path '$path'")
                        } else {
                            error("cannot resolve path '$path'")
                        }
                    } else {
                        error("cannot resolve path '$path'")
                    }
                } else {
                    error("cannot resolve path '$path'")
                }
            }

            else -> error("cannot resolve path '$path'")
        }
    }

    fun isPlaceExpr(expr: ExprNode): Boolean {
        return when (expr) {
            is DerefExprNode -> true
            is IndexExprNode -> true
            is FieldExprNode -> true
            is GroupedExprNode -> isPlaceExpr(expr.inner)
            is PathExprNode -> {
                val symbol = resolvePathExpr(expr)
                when (symbol) {
                    is VariableSymbol -> {
                        expr.second == null
                    }

                    else -> false
                }
            }

            else -> false
        }
    }

    fun isAssigneeExpr(expr: ExprNode): Boolean {
        if (isPlaceExpr(expr)) return true
        when (expr) {
            is UnderscoreExprNode -> {
                return true
            }

            is StructExprNode -> {
                for (field in expr.fields) {
                    if (!isAssigneeExpr(field.value)) {
                        return false
                    }
                }
                return true
            }

            else -> {
                return false
            }
        }
    }


    // ASTNode visitor
    override fun visitCrate(node: CrateNode) {
        // 依次visit每个item
        for (item in node.items) {
            item.accept(this)
        }
    }

    override fun visitStructItem(node: StructItemNode) {
        val structName = node.structName.value
        if (scopeStack.lookup(structName) != null) {
            reportError("struct redeclaration : '$structName'")
            return
        }
        // struct fields
        val fields = mutableMapOf<String, StructFieldSymbol>()
        if (node.fields != null) {
            for (field in node.fields) {
                val fieldName = field.name.value
                if (fields.containsKey(fieldName)) {
                    reportError("Duplicate field '$fieldName' in struct '$structName'")
                } else {
                    val fieldType = resolveType(field.type)
                    fields[fieldName] = StructFieldSymbol(fieldName, fieldType)
                }
            }
        }
        // 加入符号表
        val symbol = StructSymbol(structName, fields)
        scopeStack.define(symbol)
    }

    override fun visitEnumItem(node: EnumItemNode) {
        val enumName = node.enumName.value
        if (scopeStack.lookup(enumName) != null) {
            reportError("enum redeclaration: '$enumName'")
            return
        }

        val variants = mutableListOf<String>()

        for (variant in node.variants) {
            val variantName = variant.value
            if (variants.contains(variantName)) {
                reportError("Duplicate field '$variantName' in struct '$enumName'")
            } else {
                variants.add(variantName)
            }
        }
        val symbol = EnumSymbol(enumName, variants)
        // 加入符号表
        scopeStack.define(symbol)
    }

    override fun visitConstantItem(node: ConstantItemNode) {
        val constName = node.constantName.value
        val isAssociated = currentImpl != null || currentTrait != null

        // 检查重定义
        val traitName = currentTrait
        val implInfo = currentImpl
        val alreadyDefined = when {
            traitName != null -> {
                val trait = scopeStack.lookup(traitName)
                if (trait is TraitSymbol) {
                    trait.constants[constName]
                } else {
                    error("missing trait: '$traitName'")
                }
            }

            implInfo != null -> {
                // 找到对应的impl块
                val implHistory = implRegistry.getTraitImpl(implInfo.first, implInfo.second)
                if (implHistory != null) {
                    implHistory.constants[constName]
                } else {
                    error("missing impl: '${implInfo.first.name}'")
                }
            }

            else -> scopeStack.lookup(constName)
        }

        if (alreadyDefined != null) {
            reportError("constant redeclaration: '$constName'")
            return
        }
        val resolvedType = resolveType(node.constantType)

        val value = if (node.value == null) {
            null
        } else {
            evalConstExpr(node.value)
        }
        val symbol = ConstantSymbol(constName, resolvedType, value, isAssociated)

        when {
            traitName != null -> {
                val trait = scopeStack.lookup(traitName)
                if (trait is TraitSymbol) {
                    trait.constants[constName] = symbol
                } else {
                    error("missing trait: '$traitName'")
                }
            }

            implInfo != null -> {
                val implHistory = implRegistry.getTraitImpl(implInfo.first, implInfo.second)
                if (implHistory != null) {
                    implHistory.constants[constName] = symbol
                } else {
                    error("missing impl: '${implInfo.first.name}'")
                }
            }

            else -> scopeStack.define(symbol)
        }
    }

    override fun visitTraitItem(node: TraitItemNode) {
        val traitName = node.traitName.value
        if (scopeStack.lookup(traitName) != null) {
            reportError("trait redeclaration: '$traitName'")
            return
        }
        val symbol = TraitSymbol(traitName)
        scopeStack.define(symbol)
        if (currentTrait != null) {
            error("already in trait: '$currentTrait'")
        }
        currentTrait = traitName
        for (item in node.items) {
            item.accept(this)
        }
        // 离开trait
        currentTrait = null
    }

    override fun visitFunctionItem(node: FunctionItemNode) {
        val fnName = node.fnName.value
        val isAssociated = currentImpl != null || currentTrait != null

        // 检查重定义
        val traitName = currentTrait
        val implInfo = currentImpl
        val alreadyDefined = when {
            traitName != null -> {
                val trait = scopeStack.lookup(traitName)
                if (trait is TraitSymbol) {
                    trait.methods[fnName] != null || trait.functions[fnName] != null
                } else {
                    error("missing trait: '$traitName'")
                }
            }

            implInfo != null -> {
                // 找到对应的impl块
                val implHistory = implRegistry.getTraitImpl(implInfo.first, implInfo.second)
                if (implHistory != null) {
                    implHistory.methods[fnName] != null || implHistory.functions[fnName] != null
                } else {
                    error("missing impl: '${implInfo.first.name}'")
                }
            }

            else -> {
                scopeStack.lookup(fnName) != null
            }
        }

        if (alreadyDefined) {
            reportError("function redeclaration: '$fnName'")
            return
        }

        // 处理参数
        val parameters = mutableListOf<FunctionParameter>()
        var isMethod = false

        val paramCheck = mutableSetOf<String>()

        if (node.body != null) scopeStack.enterScope() // 进入函数作用域方便注册参数

        if (node.selfParam != null) {
            isMethod = true
            val selfType = if (node.selfParam.isRef) {
                ReferenceResolvedType(SelfResolvedType(), node.selfParam.isMut)
            } else {
                SelfResolvedType()
            }
            parameters.add(
                FunctionParameter(
                    "self",
                    selfType,
                    true,
                    node.selfParam.isMut,
                    node.selfParam.isRef
                )
            )
            // 注册参数
            if (node.body != null) {
                scopeStack.define(
                    VariableSymbol("self", selfType, node.selfParam.isMut)
                )
            }
        }

        if (isMethod && !isAssociated) {
            reportError("'$fnName' as a method must in some impl or trait")
            return
        }

        for (param in node.params) {
            val paramType = resolveType(param.type)
            when (val pattern = param.paramPattern) {
                is IdentifierPatternNode -> {
                    val name = pattern.name.value
                    if (paramCheck.add(name)) {
                        parameters.add(
                            FunctionParameter(
                                name,
                                paramType,
                                isSelf = false,
                                pattern.isMut,
                                pattern.isRef
                            )
                        )
                    } else {
                        error("duplicate parameter name: '$name'")
                    }
                    // 注册参数
                    if (node.body != null) {
                        scopeStack.define(
                            VariableSymbol(name, paramType, pattern.isMut)
                        )
                    }
                }

                is WildcardPatternNode -> {
                    parameters.add(
                        FunctionParameter(
                            "_",
                            paramType,
                            isSelf = false,
                            isMut = false,
                            isRef = false
                        )
                    )
                    // 无需注册
                }

                is ReferencePatternNode -> {
                    var name = "&"
                    var inner = pattern.inner
                    var type = if (paramType is ReferenceResolvedType) {
                        paramType.inner
                    } else {
                        error("mismatch type in function: '$fnName'")
                    }

                    while (inner is ReferencePatternNode) {
                        name += "&"
                        inner = inner.inner
                        type = if (type is ReferenceResolvedType) {
                            paramType.inner
                        } else {
                            error("mismatch type in function: '$fnName'")
                        }
                    }

                    when (inner) {
                        is IdentifierPatternNode -> {
                            name += inner.name.value
                            if (paramCheck.add(name)) {
                                parameters.add(
                                    FunctionParameter(
                                        name,
                                        paramType,
                                        isSelf = false,
                                        inner.isMut,
                                        isRef = false
                                    )
                                )
                            } else {
                                error("duplicate parameter name: '$name'")
                            }
                            // 注册参数
                            if (node.body != null) {
                                scopeStack.define(
                                    VariableSymbol(name, type, inner.isMut)
                                )
                            }
                        }

                        is WildcardPatternNode -> {
                            name += "_"
                            parameters.add(
                                FunctionParameter(
                                    name,
                                    paramType,
                                    isSelf = false,
                                    isMut = false,
                                    isRef = false
                                )
                            )
                        }

                        else -> {
                            reportError("unexpected pattern in function: '$fnName'")
                            return
                        }
                    }
                }

                else -> {
                    reportError("unexpected pattern in function: '$fnName'")
                    return
                }
            }
        }

        val returnType = if (node.returnType != null) {
            resolveType(node.returnType)
        } else {
            UnitResolvedType()
        }

        val symbol = FunctionSymbol(
            fnName,
            parameters,
            returnType,
            isAssociated,
            isMethod
        )

        when {
            traitName != null -> {
                val trait = scopeStack.lookup(traitName)
                if (trait is TraitSymbol) {
                    if (isMethod) trait.methods[fnName] = symbol
                    else trait.functions[fnName] = symbol
                } else {
                    error("missing trait: '$traitName'")
                }
            }

            implInfo != null -> {
                val implHistory = implRegistry.getTraitImpl(implInfo.first, implInfo.second)
                if (implHistory != null) {
                    if (isMethod) implHistory.methods[fnName] = symbol
                    else implHistory.functions[fnName] = symbol
                } else {
                    error("missing impl: '${implInfo.first.name}'")
                }
            }

            else -> scopeStack.define(symbol)
        }

        if (node.body != null) {
            val previousFn = currentFnType // 暂存FnType
            currentFnType = returnType
            val previousLoop = currentLoopNode // 暂存LoopNode
            currentLoopNode = null
            visitBlockExpr(node.body, createScope = false) // 这里已经创建作用域了

            // 还原作用域外环境
            currentLoopNode = previousLoop
            currentFnType = previousFn

            // 检查返回类型
            if (node.body.resolvedType !is BottomResolvedType && node.body.resolvedType != returnType) {
                reportError("return type mismatch in function: '$fnName'")
                return
            }
            scopeStack.exitScope()
        }
    }

    override fun visitImplItem(node: ImplItemNode) {
        val resolvedType = resolveType(node.implType)
        val traitSymbol: TraitSymbol? = if (node.traitName != null) {
            val symbol = scopeStack.lookup(node.traitName.value)
            if (symbol is TraitSymbol) {
                symbol
            } else {
                reportError("missing trait: '${node.traitName.value}'")
                return
            }
        } else {
            null
        }
        val impl = Impl(resolvedType, traitSymbol)
        implRegistry.register(impl)
        currentImpl = Pair(resolvedType, traitSymbol)
        for (item in node.methods) {
            item.accept(this)
        }
        currentImpl = null
    }

    override fun visitEmptyStmt(node: EmptyStmtNode) {
        // nothing to do
    }

    override fun visitItemStmt(node: ItemStmtNode) {
        node.item.accept(this)
    }

    override fun visitLetStmt(node: LetStmtNode) {
        TODO("Not yet implemented")
    }

    override fun visitExprStmt(node: ExprStmtNode) {
        node.expr.accept(this)
    }

    override fun visitBlockExpr(node: BlockExprNode, createScope: Boolean) {
        if (createScope) scopeStack.enterScope()

        for (stmt in node.statements) {
            stmt.accept(this)
            if (stmt is ExprStmtNode) {
                if (stmt.expr.resolvedType is BottomResolvedType) {
                    node.resolvedType = BottomResolvedType()
                }
            }
        }

        if (node.tailExpr != null) {
            node.tailExpr.accept(this)
            if (node.resolvedType is UnknownResolvedType) {
                node.resolvedType = node.tailExpr.resolvedType
            }
        } else {
            if (node.resolvedType is UnknownResolvedType) {
                node.resolvedType = UnitResolvedType()
            }
        }

        if (createScope) scopeStack.exitScope()
    }

    override fun visitReturnExpr(node: ReturnExprNode) {
        node.resolvedType = BottomResolvedType()
        if (currentFnType != null) {
            val returnType: ResolvedType = if (node.value != null) {
                node.value.accept(this)
                node.value.resolvedType
            } else {
                UnitResolvedType()
            }
            // 检查与函数返回类型是否匹配
            if (returnType != currentFnType) {
                reportError("returned type mismatch: '$returnType'")
                return
            }
        } else {
            error("return must be in a function block")
        }
    }

    override fun visitInfiniteLoopExpr(node: InfiniteLoopExprNode) {
        val previousLoop = currentLoopNode
        currentLoopNode = node
        // 进入循环
        node.block.accept(this)
        if (node.block.resolvedType !is UnitResolvedType &&
            node.block.resolvedType !is BottomResolvedType
        ) {
            error("loop block should be UnitType")
        }
        currentLoopNode = previousLoop
    }

    override fun visitPredicateLoopExpr(node: PredicateLoopExprNode) {
        node.condition.expr.accept(this)
        if (node.condition.expr.resolvedType == PrimitiveResolvedType("bool")) {
            // condition类型正确
            node.resolvedType = UnitResolvedType()
            val previousLoop = currentLoopNode
            currentLoopNode = node
            // 进入循环
            node.block.accept(this)
            if (node.block.resolvedType !is BottomResolvedType &&
                node.block.resolvedType !is UnitResolvedType
            ) {
                error("loop block should be UnitType")
            }
            currentLoopNode = previousLoop
        } else {
            reportError("condition must be boolean")
            return
        }
    }

    override fun visitBreakExpr(node: BreakExprNode) {
        node.resolvedType = NeverResolvedType()
        if (currentLoopNode != null) {
            val breakType: ResolvedType = if (node.value != null) {
                node.value.accept(this)
                node.value.resolvedType
            } else {
                UnitResolvedType() // 单独的break
            }

            // 检查与函数返回类型是否匹配
            if (breakType !is NeverResolvedType) {
                if (breakType == currentLoopNode!!.resolvedType) {
                    return
                } else if (currentLoopNode!!.resolvedType is BottomResolvedType) {
                    currentLoopNode!!.resolvedType = breakType
                    return
                } else if (breakType !is BottomResolvedType) {
                    // break BottomType不用改
                    reportError("loop type mismatch: '$breakType'")
                    return
                }
            }
        } else {
            error("break must be in 'loop' or 'while'")
        }
    }

    override fun visitContinueExpr(node: ContinueExprNode) {
        // nothing to do
    }

    override fun visitBorrowExpr(node: BorrowExprNode) {
        node.expr.accept(this)
        node.resolvedType = ReferenceResolvedType(
            inner = node.expr.resolvedType,
            mutable = node.isMut
        )
    }

    override fun visitDerefExpr(node: DerefExprNode) {
        node.expr.accept(this)
        val type = node.expr.resolvedType
        if (type is ReferenceResolvedType) {
            node.resolvedType = type.inner
        } else {
            reportError("Type '$type' cannot be dereferenced")
            return
        }
    }

    override fun visitNegationExpr(node: NegationExprNode) {
        node.expr.accept(this)
        val type = node.expr.resolvedType
        when (node.operator.type) {
            TokenType.SubNegate -> {
                if (isNumeric(type)) {
                    node.resolvedType = type
                } else {
                    reportError("Negation operator '${node.operator}' requires numeric operands")
                }
            }

            TokenType.Not -> {
                if (isNumeric(type) ||
                    type == PrimitiveResolvedType("bool")
                ) {
                    node.resolvedType = type
                } else {
                    reportError("Negation operator '${node.operator}' requires numeric or bool operands")
                }
            }

            else -> {
                reportError("Unsupported negation operator '${node.operator}'")
                return
            }
        }
    }

    override fun visitBinaryExpr(node: BinaryExprNode) {
        node.left.accept(this)
        node.right.accept(this)
        // 解析出左右类型
        val leftType = node.left.resolvedType
        val rightType = node.right.resolvedType

        when (node.operator.type) {
            TokenType.Add, TokenType.SubNegate, TokenType.Mul, TokenType.Div, TokenType.Mod -> {
                if (isNumeric(leftType) &&
                    isNumeric(rightType) &&
                    leftType == rightType
                ) {
                    node.resolvedType = leftType
                } else {
                    reportError("Arithmetic operator '${node.operator}' requires numeric operands")
                    return
                }
            }

            TokenType.BitAnd, TokenType.BitOr, TokenType.BitXor -> {
                if ((isNumeric(leftType) || leftType == PrimitiveResolvedType("bool")) &&
                    (isNumeric(rightType) || rightType == PrimitiveResolvedType("bool")) &&
                    leftType == rightType
                ) {
                    node.resolvedType = leftType
                } else {
                    reportError("Arithmetic operator '${node.operator}' requires numeric or bool operands")
                    return
                }
            }

            TokenType.Shl, TokenType.Shr -> {
                if (isNumeric(leftType) && isNumeric(rightType)) {
                    node.resolvedType = leftType
                } else {
                    reportError("Arithmetic operator '${node.operator}' requires numeric operands")
                    return
                }
            }

            else -> {
                reportError("Unsupported binary operator '${node.operator}'")
                return
            }
        }
    }

    override fun visitComparisonExpr(node: ComparisonExprNode) {
        node.left.accept(this)
        node.right.accept(this)
        // 解析出左右类型
        val leftType = node.left.resolvedType
        val rightType = node.right.resolvedType

        when (node.operator.type) {
            TokenType.Eq, TokenType.Neq, TokenType.Gt, TokenType.Lt, TokenType.Ge, TokenType.Le -> {
                if (leftType == rightType) {
                    node.resolvedType = PrimitiveResolvedType("bool")
                } else {
                    reportError("Comparison operator '${node.operator}' requires same type operands")
                    return
                }
            }

            else -> {
                reportError("Unsupported comparison operator '${node.operator}'")
                return
            }
        }
    }

    override fun visitLazyBooleanExpr(node: LazyBooleanExprNode) {
        node.left.accept(this)
        node.right.accept(this)
        // 解析出左右类型
        val leftType = node.left.resolvedType
        val rightType = node.right.resolvedType

        when (node.operator.type) {
            TokenType.And, TokenType.Or -> {
                if (leftType == PrimitiveResolvedType("bool") &&
                    rightType == PrimitiveResolvedType("bool")
                ) {
                    node.resolvedType = PrimitiveResolvedType("bool")
                } else {
                    reportError("LazyBoolean operator '${node.operator}' requires bool operands")
                    return
                }
            }

            else -> {
                reportError("Unsupported lazy boolean operator '${node.operator}'")
                return
            }
        }
    }

    override fun visitTypeCastExpr(node: TypeCastExprNode) {
        node.expr.accept(this)
        val currentType = node.expr.resolvedType
        val targetType = resolveType(node.targetType)
        if (isNumeric(targetType)) {
            if (isNumeric(currentType)
            ) {
                // 整数 -> 整数
                node.resolvedType = targetType
                return
            } else if (currentType == PrimitiveResolvedType("bool") ||
                currentType == PrimitiveResolvedType("char")
            ) {
                // bool/char -> 整数
                node.resolvedType = targetType
                return
            }
        }
        reportError("Cannot cast '$currentType' to $targetType'")
        return
    }

    override fun visitAssignExpr(node: AssignExprNode) {
        node.left.accept(this)
        node.right.accept(this)
        // 解析出左右类型
        val leftType = node.left.resolvedType
        val rightType = node.right.resolvedType

        if (isAssigneeExpr(node.left) && leftType == rightType) {
            node.resolvedType = UnitResolvedType() // AssignExpr is always unitType
        } else {
            error("cannot assign '${node.right}' to '${node.left}'")
        }
    }

    override fun visitCompoundAssignExpr(node: CompoundAssignExprNode) {
        node.left.accept(this)
        node.right.accept(this)
        // 解析出左右类型
        val leftType = node.left.resolvedType
        val rightType = node.right.resolvedType

        if (!isPlaceExpr(node.left)) {
            reportError("Cannot assign '${node.right}' to '${node.left}'")
            return
        }

        when (node.operator.type) {
            TokenType.AddAssign, TokenType.SubAssign, TokenType.MulAssign, TokenType.DivAssign, TokenType.ModAssign -> {
                if (isNumeric(leftType) &&
                    isNumeric(rightType) &&
                    leftType == rightType
                ) {
                    node.resolvedType = UnitResolvedType()
                } else {
                    reportError("operator '${node.operator}' requires numeric operands")
                    return
                }
            }

            TokenType.AndAssign, TokenType.OrAssign, TokenType.XorAssign -> {
                if ((isNumeric(leftType) || leftType == PrimitiveResolvedType("bool")) &&
                    (isNumeric(rightType) || rightType == PrimitiveResolvedType("bool")) &&
                    leftType == rightType
                ) {
                    node.resolvedType = UnitResolvedType()
                } else {
                    reportError("operator '${node.operator}' requires numeric or bool operands")
                    return
                }
            }

            TokenType.ShlAssign, TokenType.ShrAssign -> {
                if (isNumeric(leftType) && isNumeric(rightType)) {
                    node.resolvedType = UnitResolvedType()
                } else {
                    reportError("operator '${node.operator}' requires numeric operands")
                    return
                }
            }

            else -> {
                reportError("Unsupported compound assign operator '${node.operator}'")
                return
            }
        }
    }

    override fun visitGroupedExpr(node: GroupedExprNode) {
        node.inner.accept(this)
        node.resolvedType = node.inner.resolvedType
    }

    override fun visitIntLiteralExpr(node: IntLiteralExprNode) {
        node.resolvedType = PrimitiveResolvedType("i32")
    }

    override fun visitCharLiteralExpr(node: CharLiteralExprNode) {
        node.resolvedType = PrimitiveResolvedType("char")
    }

    override fun visitBooleanLiteralExpr(node: BooleanLiteralExprNode) {
        node.resolvedType = PrimitiveResolvedType("bool")
    }
}

