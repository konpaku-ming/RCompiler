package ast

import kotlin.system.exitProcess

class Lexer(input: String) {
    var code = input
    val vec = mutableListOf<Token>()

    fun getNextToken(): Int {
        var matchStr = ""
        var matchType = TokenType.INVALID

        for (item in tokenPatterns) {
            val str = item.first.find(code)
            if (str != null) {
                val len = str.value.length
                if (len > matchStr.length) {
                    matchStr = str.value
                    matchType = item.second
                }
            }
        }
        if (matchStr.isEmpty()) {
            println("无法识别token : $code")
            exitProcess(1)
        } else {
            if (matchType != TokenType.WHITESPACE) vec.add(Token(matchType, matchStr))
            return matchStr.length
        }
    }

    fun getTokens(): MutableList<Token> {
        while (!code.isEmpty()) {
            val len = getNextToken()
            if (len == code.length) break
            else code = code.substring(len)
        }
        vec.add(Token(TokenType.EOF, ""))
        return vec
    }
}