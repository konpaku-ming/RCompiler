package ast

// symbol
enum class SymbolKind {
    VariableSymbol,
    FunctionSymbol,
    StructSymbol,
    EnumSymbol,
    TraitSymbol,
    ConstantSymbol,
}

sealed class Symbol {
    abstract val name: String
    abstract val kind: SymbolKind
}

data class VariableSymbol(
    override val name: String,
    val type: ResolvedType,
    val isMut: Boolean
) : Symbol() {
    override val kind = SymbolKind.VariableSymbol
}

data class FunctionParameter(
    val name: String,
    val type: ResolvedType,
    val isSelf: Boolean,
    val isMut: Boolean,
    val isRef: Boolean
)

data class FunctionSymbol(
    override val name: String,
    val parameters: List<FunctionParameter>,
    val returnType: ResolvedType,
    val isAssociated: Boolean,
    val isMethod: Boolean
) : Symbol() {
    override val kind = SymbolKind.FunctionSymbol
}

data class ConstantSymbol(
    override val name: String,
    val type: ResolvedType,
    val value: Any?, // null表示为trait里的
    val isAssociated: Boolean
) : Symbol() {
    override val kind = SymbolKind.ConstantSymbol
}

data class StructFieldSymbol(
    val name: String,
    val type: ResolvedType,
)

data class StructSymbol(
    override val name: String,
    val fields: Map<String, StructFieldSymbol> // fieldName to field
) : Symbol() {
    override val kind = SymbolKind.StructSymbol
}

data class EnumSymbol(
    override val name: String,
    val variants: List<String>, // variants
) : Symbol() {
    override val kind = SymbolKind.EnumSymbol
}

data class TraitSymbol(
    override val name: String,
    val methods: MutableMap<String, FunctionSymbol> = mutableMapOf(),
    val constants: MutableMap<String, ConstantSymbol> = mutableMapOf()
) : Symbol() {
    override val kind = SymbolKind.TraitSymbol
}

// impl register
data class Impl(
    val implType: ResolvedType,
    val trait: TraitSymbol?,
    val methods: MutableMap<String, FunctionSymbol> = mutableMapOf(),
    val constants: MutableMap<String, ConstantSymbol> = mutableMapOf()
)

class ImplRegistry {
    private val impls: MutableMap<ResolvedType, MutableList<Impl>> = mutableMapOf()

    fun register(impl: Impl) {
        val targetImpl = impls[impl.implType]
        if (targetImpl != null) {
            targetImpl.add(impl)
        } else {
            impls[impl.implType] = mutableListOf(impl)
        }
    }

    fun getImplsForType(type: ResolvedType): List<Impl> {
        val targetImpl = impls[type]
        return targetImpl ?: emptyList()
    }

    fun getTraitImpl(type: ResolvedType, trait: TraitSymbol?): Impl? {
        val targetImpl = getImplsForType(type)
        for (impl in targetImpl) {
            if (impl.trait == trait) {
                return impl
            }
        }
        return null
    }
}

// scope
class Scope(
    val parent: Scope? = null // 上一层scope
) {
    private val symbols = mutableMapOf<String, Symbol>()

    fun define(symbol: Symbol) {
        symbols[symbol.name] = symbol
    }

    fun lookupLocal(name: String): Symbol? {
        // 仅在本scope里查找Symbol
        return symbols[name]
    }

    fun lookup(name: String): Symbol? {
        return symbols[name] ?: parent?.lookup(name)
    }

    fun containsLocal(name: String): Boolean {
        return symbols.containsKey(name)
    }

    fun allSymbols(): Map<String, Symbol> = symbols
}

class ScopeStack {
    private val scopeStack = ArrayDeque<Scope>()

    init {
        // 初始位于 global scope
        scopeStack.addFirst(Scope(null))
    }

    fun enterScope() {
        val newScope = Scope(scopeStack.first())
        scopeStack.addFirst(newScope)
    }

    fun exitScope() {
        if (scopeStack.size > 1) {
            scopeStack.removeFirst()
        } else {
            error("error: exit global scope")
        }
    }

    fun currentScope(): Scope = scopeStack.first()

    fun define(symbol: Symbol) {
        currentScope().define(symbol)
    }

    fun lookup(name: String): Symbol? {
        return currentScope().lookup(name)
    }

    fun lookupLocal(name: String): Symbol? {
        return currentScope().lookupLocal(name)
    }

    fun containsLocal(name: String): Boolean {
        return currentScope().containsLocal(name)
    }

    fun dump() {
        println("Scope Stack:")
        scopeStack.forEachIndexed { i, scope ->
            println("  Scope[$i]: ${scope.allSymbols().keys}")
        }
    }
}

