import ast.Lexer
import ast.Parser
import ast.removeComments

fun main() {
    val input = """
        fn main() {
            let greeting = "Helloworld";
            print("{}", greeting);
            let number = 0x_4_2_;
            let ch = '\0';
            if number > 10 {
                println!("Number is greater than 10");
            } else {
                println!("Number is 10 or less");
            }
            for i in 0..5 {
                println!("i = {}", i);
            }

            let result = add(3, 4);
            println!("3 + 4 = {}", result);
        }

        fn add(x: i32, y: i32) -> i32 {
            x + y
        }
    """.trimIndent()

    val lexer = Lexer(removeComments(input))
    val parser = Parser(lexer.getTokens())
    val ast = parser.parse()
    val tokenList = lexer.getTokens()
    for (item in tokenList) {
        item.printToken()
    }

    /*
    val regex = Regex(
        """^(
        |0x[0-9a-fA-F](?:[0-9a-fA-F_]*[0-9a-fA-F])?|
        |0b[01](?:[01_]*[01])?|
        |0o[0-7](?:[0-7_]*[0-7])?|
        |[0-9](?:[0-9_]*[0-9])?|
        )([iu](?:32|size))?"""
            .trimMargin()
            .replace("\n", "")
    )
    val test = "0x42;"
    var res = "!!!"
    val match = regex.find(test)
    if (match != null) res = match.value;
    println(res)

     */

}