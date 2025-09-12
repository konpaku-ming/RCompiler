package ast

import kotlin.system.exitProcess
import kotlin.text.Regex

enum class TokenType {
    AS,
    BREAK,
    CONST,
    CONTINUE,
    CRATE,
    ELSE,
    ENUM,
    FALSE,
    FN,
    FOR,
    IF,
    IMPL,
    IN,
    LET,
    LOOP,
    MATCH,
    MOD,
    MOVE,
    MUT,
    PUB,
    REF,
    RETURN,
    SELF,
    SELF_CAP,
    STATIC,
    STRUCT,
    SUPER,
    TRAIT,
    TRUE,
    TYPE,
    UNSAFE,
    USE,
    WHERE,
    WHILE,
    DYN,
    RAW,

    IDENTIFIER,
    WHITESPACE,
    INTEGER_LITERAL,
    CHAR_LITERAL,
    STRING_LITERAL,
    RAW_STRING_LITERAL,
    C_STRING_LITERAL,
    RAW_C_STRING_LITERAL,

    Assign,
    AddAssign,
    SubAssign,
    MulAssign,
    DivAssign,
    ModAssign,
    ShlAssign,
    ShrAssign,
    AndAssign,
    OrAssign,
    XorAssign,

    Add, SubNegate, Mul,
    Div, Mod,
    Shl, Shr,
    BitAnd, BitOr, BitXor,
    And, Or,
    Eq, Neq, Lt,
    Gt, Le, Ge,

    Not,

    Ellipsis,
    RangeInclusive,
    Range,
    Dot,
    DoubleColon,
    Arrow,
    BackArrow,
    FatArrow,

    Comma,
    Semicolon,
    Colon,
    Hash,
    Underscore,
    Dollar,

    LeftBrace,
    RightBrace,
    LeftBracket,
    RightBracket,
    LeftParen,
    RightParen,

    EOF,

    INVALID,
}

val tokenPatterns: List<Pair<Regex, TokenType>> = listOf(
    Regex("""^\s+""") to TokenType.WHITESPACE,
    Regex("^as") to TokenType.AS,
    Regex("^break") to TokenType.BREAK,
    Regex("^const") to TokenType.CONST,
    Regex("^continue") to TokenType.CONTINUE,
    Regex("^crate") to TokenType.CRATE,
    Regex("^else") to TokenType.ELSE,
    Regex("^enum") to TokenType.ENUM,
    Regex("^false") to TokenType.FALSE,
    Regex("^fn") to TokenType.FN,
    Regex("^for") to TokenType.FOR,
    Regex("^if") to TokenType.IF,
    Regex("^impl") to TokenType.IMPL,
    Regex("^in") to TokenType.IN,
    Regex("^let") to TokenType.LET,
    Regex("^loop") to TokenType.LOOP,
    Regex("^match") to TokenType.MATCH,
    Regex("^mod") to TokenType.MOD,
    Regex("^move") to TokenType.MOVE,
    Regex("^mut") to TokenType.MUT,
    Regex("^pub") to TokenType.PUB,
    Regex("^ref") to TokenType.REF,
    Regex("^return") to TokenType.RETURN,
    Regex("^self") to TokenType.SELF,
    Regex("^Self") to TokenType.SELF_CAP,
    Regex("^static") to TokenType.STATIC,
    Regex("^struct") to TokenType.STRUCT,
    Regex("^super") to TokenType.SUPER,
    Regex("^trait") to TokenType.TRAIT,
    Regex("^true") to TokenType.TRUE,
    Regex("^type") to TokenType.TYPE,
    Regex("^unsafe") to TokenType.UNSAFE,
    Regex("^use") to TokenType.USE,
    Regex("^where") to TokenType.WHERE,
    Regex("^while") to TokenType.WHILE,
    Regex("^dyn") to TokenType.DYN,
    Regex("^raw") to TokenType.RAW,

    Regex("^[a-zA-Z][a-zA-Z0-9_]*") to TokenType.IDENTIFIER,

    Regex("^>>=") to TokenType.ShrAssign,
    Regex("^<<=") to TokenType.ShlAssign,
    Regex("""^\+=""") to TokenType.AddAssign,
    Regex("^-=") to TokenType.SubAssign,
    Regex("""^\*=""") to TokenType.MulAssign,
    Regex("^/=") to TokenType.DivAssign,
    Regex("^%=") to TokenType.ModAssign,
    Regex("""^\^=""") to TokenType.XorAssign,
    Regex("^&=") to TokenType.AndAssign,
    Regex("""^\|=""") to TokenType.OrAssign,
    Regex("""^==""") to TokenType.Eq,
    Regex("""^!=""") to TokenType.Neq,
    Regex("""^<=""") to TokenType.Le,
    Regex("""^>=""") to TokenType.Ge,
    Regex("""^<<""") to TokenType.Shl,
    Regex("""^>>""") to TokenType.Shr,
    Regex("""^&&""") to TokenType.And,
    Regex("""^\|\|""") to TokenType.Or,
    Regex("""^=""") to TokenType.Assign,
    Regex("""^\+""") to TokenType.Add,
    Regex("""^-""") to TokenType.SubNegate,
    Regex("""^\*""") to TokenType.Mul,
    Regex("""^/""") to TokenType.Div,
    Regex("""^%""") to TokenType.Mod,
    Regex("""^\^""") to TokenType.BitXor,
    Regex("""^!""") to TokenType.Not,
    Regex("""^&""") to TokenType.BitAnd,
    Regex("""^\|""") to TokenType.BitOr,
    Regex("""^<""") to TokenType.Lt,
    Regex("""^>""") to TokenType.Gt,

    Regex("""^\.{3}""") to TokenType.Ellipsis,
    Regex("""^\.{2}=""") to TokenType.RangeInclusive,
    Regex("""^\.{2}""") to TokenType.Range,
    Regex("""^\.""") to TokenType.Dot,
    Regex("""^::""") to TokenType.DoubleColon,
    Regex("""^->""") to TokenType.Arrow,
    Regex("""^<-""") to TokenType.BackArrow,
    Regex("""^=>""") to TokenType.FatArrow,

    Regex("""^,""") to TokenType.Comma,
    Regex("""^;""") to TokenType.Semicolon,
    Regex("""^:""") to TokenType.Colon,
    Regex("""^#""") to TokenType.Hash,
    Regex("""^_""") to TokenType.Underscore,
    Regex("""^$""") to TokenType.Dollar,

    Regex("""^\{""") to TokenType.LeftBrace,
    Regex("""^}""") to TokenType.RightBrace,
    Regex("""^\[""") to TokenType.LeftBracket,
    Regex("""^]""") to TokenType.RightBracket,
    Regex("""^\(""") to TokenType.LeftParen,
    Regex("""^\)""") to TokenType.RightParen,

    Regex(
        """^(
        |0x[0-9a-fA-F_]*[0-9a-fA-F][0-9a-fA-F_]*|
        |0b[01_]*[01][01_]*|
        |0o[0-7_]*[0-7][0-7_]*|
        |[0-9][0-9_]*|
        )([iu](?:32|size))?"""
            .trimMargin()
            .replace("\n", "")
    ) to TokenType.INTEGER_LITERAL,
    Regex(
        """^'([^'\\\n\r\t]|\\[nrt'"\\0]|\\x[0-7][0-9a-fA-F])'"""
    ) to TokenType.CHAR_LITERAL,
    Regex(
        """^"([^"\\\r]|\\[nrt'"\\0]|\\x[0-9a-fA-F]{2}|\\\r)*""""
    ) to TokenType.STRING_LITERAL,
    Regex(
        """^r(#*)"([^"\\\r]|\\[nrt'"\\0]|\\x[0-9a-fA-F]{2}|\\\r)*"\1"""
    ) to TokenType.RAW_STRING_LITERAL,
    Regex(
        """^c"([^"\\\r]|\\[nrt'"\\0]|\\x[0-9a-fA-F]{2}|\\\r)*""""
    ) to TokenType.C_STRING_LITERAL,
    Regex(
        """^cr(#*)"([^"\\\r]|\\[nrt'"\\0]|\\x[0-9a-fA-F]{2}|\\\r)*"\1"""
    ) to TokenType.RAW_C_STRING_LITERAL,
)

data class Token(val type: TokenType, val value: String) {
    fun printToken() {
        if (type == TokenType.INVALID) {
            println("invalid token : $value")
            exitProcess(1)
        }
        println("type = $type , value = $value")
    }
}