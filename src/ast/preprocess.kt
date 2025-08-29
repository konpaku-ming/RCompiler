package ast

fun removeComments(code: String): String {
    val multiLine = Regex("""/\*.*?\*/""", RegexOption.DOT_MATCHES_ALL)
    val code1 = code.replace(multiLine, " ")
    val singleLine = Regex("//.*")
    val code2 = code1.replace(singleLine, " ")
    //val code3 = code2.replace("\n", " ")
    return code2
}