package ast

sealed class Symbol

data class Variable(
    val name: String,
    val type: TypeNode
) : Symbol()

data class Function(
    val name: String,
    val paramTypes: List<TypeNode>, // params
    val returnType: TypeNode?
) : Symbol()

data class Struct(
    val name: String,
    val fields: List<StructField> // fields
) : Symbol()

data class Enum(
    val name: String,
    val variants: List<String> // variants
) : Symbol()

data class Trait(
    val name: String,
    val methods: List<ItemNode> // items
) : Symbol()

data class Impl(
    val target: TypeNode,
    val traitName: String?,
    val methods: List<ItemNode> // items
) : Symbol()

data class Constant(
    val name: String,
    val type: TypeNode,
    val value: ExprNode?
) : Symbol()


class SymbolTable(val parent: SymbolTable? = null) {
    private val symbols = HashMap<String, Symbol>()

    fun contains(name: String): Boolean {
        return symbols.containsKey(name)
    }

    fun define(name: String, symbol: Symbol): Boolean {
        if (contains(name)) return false // 重复
        symbols[name] = symbol // 写入SymbolTable
        return true
    }

    fun lookup(name: String): Symbol? {
        if (contains(name)) return symbols[name]
        if (parent != null) return parent.lookup(name)
        return null
    }
}

