package ast

import kotlin.collections.set

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

// 未知类型
class UnknownResolvedType : ResolvedType {
    override val name: String = "<unknown>"
}

class SemanticVisitor(private val scopeStack: ScopeStack) : ASTVisitor {
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
                when (val name = node.path.identSegment.value) {
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
        // 加入符号表
        val symbol = EnumSymbol(enumName, variants)
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
                    trait.methods[fnName]
                } else {
                    error("missing trait: '$traitName'")
                }
            }

            implInfo != null -> {
                // 找到对应的impl块
                val implHistory = implRegistry.getTraitImpl(implInfo.first, implInfo.second)
                if (implHistory != null) {
                    implHistory.methods[fnName]
                } else {
                    error("missing impl: '${implInfo.first.name}'")
                }
            }

            else -> scopeStack.lookup(fnName)
        }

        if (alreadyDefined != null) {
            reportError("function redeclaration: '$fnName'")
            return
        }
        // 处理参数
        val parameters = mutableListOf<FunctionParameter>()
        var isMethod = false

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
        }

        if (isMethod && !isAssociated) {
            reportError("'$fnName' as a method must in some impl or trait")
            return
        }

        for (param in node.params) {
            val paramType = resolveType(param.type)
            when (val pattern = param.paramPattern) {
                is IdentifierPatternNode -> {
                    parameters.add(
                        FunctionParameter(
                            pattern.name.value,
                            paramType,
                            false,
                            pattern.isMut,
                            pattern.isRef
                        )
                    )
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
                    trait.methods[fnName] = symbol
                } else {
                    error("missing trait: '$traitName'")
                }
            }

            implInfo != null -> {
                val implHistory = implRegistry.getTraitImpl(implInfo.first, implInfo.second)
                if (implHistory != null) {
                    implHistory.methods[fnName] = symbol
                } else {
                    error("missing impl: '${implInfo.first.name}'")
                }
            }

            else -> scopeStack.define(symbol)
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
}
