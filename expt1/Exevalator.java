/*
 * A long code example, for the experiment which examines 
 * how this code looks from AIs through their web-browsing feature.
 * 
 * Also, this code is a single-file expression calculator library "Exevalator".
 * Its repository is: https://github.com/RINEARN/exevalator
 */

import java.util.List;
import java.util.ArrayList;
import java.util.Deque;
import java.util.ArrayDeque;
import java.util.Set;
import java.util.HashSet;
import java.util.EnumSet;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;
import java.util.regex.Matcher;
import java.util.regex.Pattern;


/**
 * Interpreter Engine of Exevalator.
 */
public final class Exevalator {

    /** The array used as as a virtual memory storing values of variables. */
    private volatile double[] memory;

    /** The current usage (max used index + 1) of the memory. */
    private volatile int memoryUsage;

    /** The object evaluating the value of the expression. */
    private volatile Evaluator evaluator;

    /** The Map mapping each variable name to an address of the variable. */
    private volatile Map<String, Integer> variableTable;

    /** The Map mapping each function name to an IExevalatorFunction instance. */
    private volatile Map<String, FunctionInterface> functionTable;

    /** Caches the content of the expression evaluated last time, to skip re-parsing. */
    private volatile String lastEvaluatedExpression;

    /**
     * Creates a new interpreter of the Exevalator.
     */
    public Exevalator() {
        this.memory = new double[64];
        this.memoryUsage = 0;
        this.evaluator = new Evaluator();
        this.variableTable = new ConcurrentHashMap<String, Integer>();
        this.functionTable = new ConcurrentHashMap<String, FunctionInterface>();
        this.lastEvaluatedExpression = null;
    }

    /**
     * Evaluates (computes) the value of an expression.
     *
     * @param expression The expression to be evaluated.
     * @return The evaluated value.
     */
    public synchronized double eval(String expression) {
        if (expression == null) {
            throw new NullPointerException();
        }
        if (StaticSettings.MAX_EXPRESSION_CHAR_COUNT < expression.length()) {
            throw new Exevalator.Exception(
                "The length of the expression exceeds the limit "
                + "(StaticSettings.MAX_EXPRESSION_CHAR_COUNT: "
                + StaticSettings.MAX_EXPRESSION_CHAR_COUNT + ")"
            );
        }

        try {
            boolean expressionChanged = expression != this.lastEvaluatedExpression
            && !expression.equals(this.lastEvaluatedExpression);

            // If the expression changed from the last-evaluated expression, re-parsing is necessary.
            if (expressionChanged || !this.evaluator.isEvaluatable()) {

                // Split the expression into tokens, and analyze them.
                Token[] tokens = LexicalAnalyzer.analyze(expression);

                /*
                // Temporary, for debugging tokens
                for (Token token: tokens) {
                    System.out.println(token.toString());
                }
                */

                // Construct AST (Abstract Syntax Tree) by parsing tokens.
                AstNode ast = Parser.parse(tokens);

                /*
                // Temporary, for debugging AST
                System.out.println(ast.toMarkuppedText());
                */

                // Update the evaluator, to evaluate the parsed AST.
                this.evaluator.update(ast, this.variableTable, this.functionTable);

                this.lastEvaluatedExpression = expression;
            }

            // Evaluate the value of the expression, and return it.
            double evaluatedValue = this.evaluator.evaluate(this.memory);
            return evaluatedValue;

        } catch (Exevalator.Exception ee) {
            throw ee;

        // Wrap an unexpected exception by Exevalator.Exception and rethrow it.
        } catch (java.lang.Exception e) {
            throw new Exevalator.Exception("Unexpected exception/error occurred", e);
        }
    }

    /**
     * Re-evaluates (re-computes) the value of the expression evaluated by "eval" method last time.
     * This method may (slightly) work faster than calling "eval" method repeatedly for the same expression.
     * Note that, the result value may different with the last evaluated value, 
     * if values of variables or behaviour of functions had changed.
     * 
     * @return The evaluated value
     */
    public synchronized double reeval() {
        if (!this.evaluator.isEvaluatable()) {
            throw new Exevalator.Exception("\"reeval\" is not available before using \"eval\"");
        } else {
            double evaluatedValue = this.evaluator.evaluate(this.memory);
            return evaluatedValue;
        }
    }

    /**
     * Declares a new variable, for using the value of it in expressions.
     *
     * @param name The name of the variable to be declared.
     * @return The virtual address of the declared variable,
     *             which useful for accessing to the variable faster.
     *             See "writeVariableAt" and "readVariableAt" method.
     */
    public synchronized int declareVariable(String name) {
        if (name == null) {
            throw new NullPointerException();
        }
        if (StaticSettings.MAX_NAME_CHAR_COUNT < name.length()) {
            throw new Exevalator.Exception(
                "The length of the variable name exceeds the limit (StaticSettings.MAX_NAME_CHAR_COUNT: "
                + StaticSettings.MAX_NAME_CHAR_COUNT + ")"
            );
        }

        // If the memory is full, expand the memory size.
        if (this.memory.length == this.memoryUsage) {
            double[] stock = new double[this.memory.length];
            System.arraycopy(this.memory, 0, stock, 0, this.memory.length);
            this.memory = new double[ this.memory.length * 2 ];
            System.arraycopy(stock, 0, this.memory, 0, stock.length);
        }

        // Assign an address to the new variable,
        // and register the address and the name to the variable table.
        int address = this.memoryUsage;
        this.variableTable.put(name, address);
        this.memoryUsage++;
        return address;
    }

    /**
     * Writes the value to the variable having the specified name.
     *
     * @param name The name of the variable to be written.
     * @param value The new value of the variable.
     */
    public synchronized void writeVariable(String name, double value) {
        if (name == null) {
            throw new NullPointerException();
        }
        if (StaticSettings.MAX_NAME_CHAR_COUNT < name.length() || !this.variableTable.containsKey(name)) {
            throw new Exevalator.Exception("Variable not found: " + name);
        }
        int address = this.variableTable.get(name);
        this.writeVariableAt(address, value);
    }

    /**
     * Writes the value to the variable at the specified virtual address.
     * This method works faster than "WriteVariable" method.
     *
     * @param address The virtual address of the variable to be written.
     * @param value The new value of the variable.
     */
    public synchronized void writeVariableAt(int address, double value) {
        if (address < 0 || this.memoryUsage <= address) {
            throw new Exevalator.Exception("Invalid variable address: " + address);
        }
        this.memory[address] = value;
    }

    /**
     * Reads the value of the variable having the specified name.
     *
     * @param name The name of the variable to be read.
     * @return The current value of the variable.
     */
    public synchronized double readVariable(String name) {
        if (name == null) {
            throw new NullPointerException();
        }
        if (StaticSettings.MAX_NAME_CHAR_COUNT < name.length() || !this.variableTable.containsKey(name)) {
            throw new Exevalator.Exception("Variable not found: " + name);
        }
        int address = this.variableTable.get(name);
        return this.readVariableAt(address);
    }

    /**
     * Reads the value of the variable at the specified virtual address.
     * This method works faster than "EeadVariable" method.
     *
     * @param address The virtual address of the variable to be read.
     * @return The current value of the variable.
     */
    public synchronized double readVariableAt(int address) {
        if (address < 0 || this.memoryUsage <= address) {
            throw new Exevalator.Exception("Invalid variable address: " + address);
        }
        return this.memory[address];
    }

    /**
     * Connects a function, for using it in expressions.
     *
     * @param name The name of the function used in the expression.
     * @param function The function to be connected.
     */
    public synchronized void connectFunction(String name, FunctionInterface function) {
        if (name == null || function == null) {
            throw new NullPointerException();
        }
        if (StaticSettings.MAX_NAME_CHAR_COUNT < name.length()) {
            throw new Exevalator.Exception(
                "The length of the variable name exceeds the limit (StaticSettings.MAX_NAME_CHAR_COUNT: "
                + StaticSettings.MAX_NAME_CHAR_COUNT + ")"
            );
        }
        this.functionTable.put(name, function);
    }

    /**
     * The interface to implement functions available in expressions.
     */
    public interface FunctionInterface {

        /**
         * Invokes the function.
         * 
         * @param arguments An array storing values of arguments.
         * @return The return value of the function.
         */
        public double invoke(double[] arguments);
    }

    /**
     * The Exception class thrown in/by this engine.
     */
    @SuppressWarnings("serial")
    public static final class Exception extends RuntimeException {

        /**
         * Create an instance having the specified error message.
         *
         * @param errorMessage The error message explaining the cause of this exception.
         */
        public Exception(String errorMessage) {
            super(errorMessage);
        }

        /**
         * Create an instance having the specified error message and the cause exception.
         *
         * @param errorMessage The error message explaining the cause of this exception.
         * @param causeException The cause exception of this exception.
         */
        public Exception(String errorMessage, java.lang.Exception causeException) {
            super(errorMessage, causeException);
        }
    }
}


/**
 * The class performing functions of a lexical analyzer.
 */
final class LexicalAnalyzer {

    /**
     * Splits (tokenizes) the expression into tokens, and analyze them.
     *
     * @param expression The expression to be tokenized/analyzed.
     * @return Analyzed tokens.
     */
    public static Token[] analyze(String expression) {

        // Firstly, to simplify the tokenization,
        // replace number literals in the expression to the escaped representation: "@NUMBER_LITERAL",
        // because number literals may contains "+" or "-" in their exponent part.
        List<String> numberLiteralList = new ArrayList<String>();
        expression = escapeNumberLiterals(expression, numberLiteralList);

        // Tokenize (split) the expression into token words.
        for (char splitter: StaticSettings.TOKEN_SPLITTER_SYMBOL_LIST) {
            expression = expression.replace(Character.toString(splitter), " " + splitter + " ");
        }
        String[] tokenWords = expression.trim().split("\\s+");

        // For an empty expression (containing no tokens), the above returns { "" }, not { }.
        // So we should detect/handle it as follows.
        if (tokenWords.length == 1 && tokenWords[0].length() == 0) {
            throw new Exevalator.Exception("The inputted expression is empty");
        }

        // Checks the total number of tokens.
        if (StaticSettings.MAX_TOKEN_COUNT < tokenWords.length) {
            throw new Exevalator.Exception(
                "The number of tokens exceeds the limit (StaticSettings.MAX_TOKEN_COUNT: "
                + StaticSettings.MAX_TOKEN_COUNT + ")"
            );
        }

        // Create Token instances.
        // Also, escaped number literals will be recovered.
        Token[] tokens = createTokensFromTokenWords(tokenWords, numberLiteralList);

        // Checks syntactic correctness of tokens of inputted expressions.
        checkParenthesisOpeningClosings(tokens);
        checkEmptyParentheses(tokens);
        checkLocationsOfOperatorsAndLeafs(tokens);

        return tokens;
    }

    /**
     * Creates Token-type instances from token words (String).
     *
     * @param tokenWords Token words (String) to be converted to Token instances.
     * @param numberLiterals The List storing number literals.
     * @return Created Token instances.
     */
    private static Token[] createTokensFromTokenWords(String[] tokenWords, List<String> numberLiterals) {
        int tokenCount = tokenWords.length;

        // Stores the parenthesis-depth, which will increase at "(" and decrease at ")".
        int parenthesisDepth = 0;

        // Stores the parenthesis-depth when a function call operator begins,
        // for detecting the end of the function operator.
        Set<Integer> callParenthesisDepths = new HashSet<Integer>();

        Token[] tokens = new Token[tokenCount];
        Token lastToken = null;
        int iliteral = 0;
        for (int itoken=0; itoken<tokenCount; itoken++) {
            String word = tokenWords[itoken];

            // Cases of open parentheses, or beginning of function calls.
            if (word.equals("(")) {
                parenthesisDepth++;
                if (1 <= itoken && tokens[itoken - 1].type == TokenType.FUNCTION_IDENTIFIER) {
                    callParenthesisDepths.add(parenthesisDepth);
                    Operator op = StaticSettings.CALL_OPERATOR_SYMBOL_MAP.get(word.charAt(0));
                    tokens[itoken] = new Token(TokenType.OPERATOR, word, op);
                } else {
                    tokens[itoken] = new Token(TokenType.PARENTHESIS, word);
                }

            // Cases of closes parentheses, or end of function calls.
            } else if (word.equals(")")) {
                if (callParenthesisDepths.contains(parenthesisDepth)) {
                    callParenthesisDepths.remove(parenthesisDepth);
                    Operator op = StaticSettings.CALL_OPERATOR_SYMBOL_MAP.get(word.charAt(0));
                    tokens[itoken] = new Token(TokenType.OPERATOR, word, op);
                } else {
                    tokens[itoken] = new Token(TokenType.PARENTHESIS, word);
                }
                parenthesisDepth--;

            // Cases of operators.
            } else if (word.length() == 1 && StaticSettings.OPERATOR_SYMBOL_SET.contains(word.charAt(0))) {
                Operator op = null;

                // Cases of unary-prefix operators.
                if (lastToken == null
                        || lastToken.word.equals("(")
                        || (lastToken.type == TokenType.OPERATOR && lastToken.operator.type != OperatorType.CALL) ) {

                    if (!StaticSettings.UNARY_PREFIX_OPERATOR_SYMBOL_MAP.containsKey(word.charAt(0))) {
                        throw new Exevalator.Exception("Unknown unary-prefix operator: " + word);
                    }
                    op = StaticSettings.UNARY_PREFIX_OPERATOR_SYMBOL_MAP.get(word.charAt(0));

                // Cases of binary operators.
                } else if (lastToken.word.equals(")")
                        || lastToken.type == TokenType.NUMBER_LITERAL
                        || lastToken.type == TokenType.VARIABLE_IDENTIFIER) {

                    if (!StaticSettings.BINARY_OPERATOR_SYMBOL_MAP.containsKey(word.charAt(0))) {
                        throw new Exevalator.Exception("Unknown binary operator: " + word);
                    }
                    op = StaticSettings.BINARY_OPERATOR_SYMBOL_MAP.get(word.charAt(0));

                } else {
                    throw new Exevalator.Exception("Unexpected operator syntax: " + word);
                }
                tokens[itoken] = new Token(TokenType.OPERATOR, word, op);

                // Cases of literals, and separator.
            } else if (word.equals(StaticSettings.ESCAPED_NUMBER_LITERAL)) {
                tokens[itoken] = new Token(TokenType.NUMBER_LITERAL, numberLiterals.get(iliteral));
                iliteral++;
            } else if (word.equals(",")) {
                tokens[itoken] = new Token(TokenType.EXPRESSION_SEPARATOR, word);

            // Cases of variable identifier of function identifier.
            } else {
                if (itoken < tokenCount - 1 && tokenWords[itoken + 1].equals("(")) {
                    tokens[itoken] = new Token(TokenType.FUNCTION_IDENTIFIER, word);
                } else {
                    tokens[itoken] = new Token(TokenType.VARIABLE_IDENTIFIER, word);
                }
            }
            lastToken = tokens[itoken];
        }
        return tokens;
    }

    /**
     * Replaces number literals in the expression to the escaped representation: "@NUMBER_LITERAL@".
     *
     * @param expression The expression of which number literals are not escaped yet.
     * @param literalStoreList The list to which number literals will be added.
     * @return The expression in which number literals are escaped.
     */
    private static String escapeNumberLiterals(String expression, List<String> literalStoreList) {
        Pattern numberLiteralPattern = Pattern.compile(StaticSettings.NUMBER_LITERAL_REGEX);
        Matcher numberLiteralMatcher = numberLiteralPattern.matcher(expression);

        // Search the next number literal, and loops while any literals undetected yet exist.
        while(numberLiteralMatcher.find()) {

            // Extract a number literal detected by the above searching.
            String matchedLiteral = numberLiteralMatcher.group();

            // Add the extracted literal to the List specified to the argument.
            literalStoreList.add(matchedLiteral);
        }

        // Replace all number literals in the expression to the escaped representation.
        numberLiteralMatcher.reset();
        String replacedExpression = numberLiteralMatcher.replaceAll(StaticSettings.ESCAPED_NUMBER_LITERAL);
        return replacedExpression;
    }

    /**
     * Checks the number and correspondence of open "(" / closed ")" parentheses.
     * An ExevalatorException will be thrown when any errors detected.
     * If no error detected, nothing will occur.
     *
     * @param tokens Tokens of the inputted expression.
     */
    private static void checkParenthesisOpeningClosings(Token[] tokens) {
        int tokenCount = tokens.length;
        int hierarchy = 0; // Increases at "(" and decreases at ")".

        for (int tokenIndex=0; tokenIndex<tokenCount; tokenIndex++) {
            Token token = tokens[tokenIndex];
            if (token.word.equals("(")) {
                hierarchy++;
            } else if (token.word.equals(")")) {
                hierarchy--;
            }

            // If the value of hierarchy is negative, the open parenthesis is deficient.
            if (hierarchy < 0) {
                throw new Exevalator.Exception(
                    "The number of open parenthesis \"(\" is deficient."
                );
            }
        }

        // If the value of hierarchy is not zero at the end of the expression,
        // the closed parentheses ")" is deficient.
        if (hierarchy > 0) {
            throw new Exevalator.Exception(
                "The number of closed parenthesis \")\" is deficient."
            );
        }
    }

    /**
     * Checks that empty parentheses "()" are not contained in the expression.
     * An ExevalatorException will be thrown when any errors detected.
     * If no error detected, nothing will occur.
     *
     * @param tokens Tokens of the inputted expression.
     */
    private static void checkEmptyParentheses(Token[] tokens) {
        int tokenCount = tokens.length;
        int contentCounter = 0;
        for (int tokenIndex=0; tokenIndex<tokenCount; tokenIndex++) {
            Token token = tokens[tokenIndex];
            if (token.type == TokenType.PARENTHESIS) { // Excepting CALL operators
                if (token.word.equals("(")) {
                    contentCounter = 0;
                } else if (token.word.equals(")")) {
                    if (contentCounter == 0) {
                        throw new Exevalator.Exception(
                            "The content parentheses \"()\" should not be empty (excluding function calls)."
                        );
                    }
                }
            } else {
                contentCounter++;
            }
        }
    }

    /**
     * Checks correctness of locations of operators and leaf elements (literals and identifiers).
     * An ExevalatorException will be thrown when any errors detected.
     * If no error detected, nothing will occur.
     *
     * @param tokens Tokens of the inputted expression.
     */
    private static void checkLocationsOfOperatorsAndLeafs(Token[] tokens) {
        int tokenCount = tokens.length;
        Set<TokenType> leafTypeSet = EnumSet.noneOf(TokenType.class);
        leafTypeSet.add(TokenType.NUMBER_LITERAL);
        leafTypeSet.add(TokenType.VARIABLE_IDENTIFIER);

        // Reads and check tokens from left to right.
        for (int tokenIndex=0; tokenIndex<tokenCount; tokenIndex++) {
            Token token = tokens[tokenIndex];

            // Prepare information of next/previous token.
            boolean nextIsLeaf = tokenIndex!=tokenCount-1 && leafTypeSet.contains(tokens[tokenIndex+1].type);
            boolean prevIsLeaf = tokenIndex!=0 && leafTypeSet.contains(tokens[tokenIndex-1].type);
            boolean nextIsOpenParenthesis = tokenIndex < tokenCount-1 && tokens[tokenIndex+1].word.equals("(");
            boolean prevIsCloseParenthesis = tokenIndex != 0 && tokens[tokenIndex-1].word.equals(")");
            boolean nextIsPrefixOperator = tokenIndex < tokenCount-1
                    && tokens[tokenIndex+1].type == TokenType.OPERATOR
                    && tokens[tokenIndex+1].operator.type == OperatorType.UNARY_PREFIX;
            boolean nextIsFunctionCallBegin = nextIsOpenParenthesis
                    && tokens[tokenIndex+1].type == TokenType.OPERATOR
                    && tokens[tokenIndex+1].operator.type == OperatorType.CALL;
            boolean nextIsFunctionIdentifier = tokenIndex < tokenCount-1
                    && tokens[tokenIndex+1].type == TokenType.FUNCTION_IDENTIFIER;

            // Case of operators
            if (token.type == TokenType.OPERATOR) {

                // Cases of unary-prefix operators
                if (token.operator.type == OperatorType.UNARY_PREFIX) {

                    // Only leafs, open parentheses, and unary-prefix operators can be operands.
                    if ( !(  nextIsLeaf || nextIsOpenParenthesis || nextIsPrefixOperator  ) ) {
                        throw new Exevalator.Exception("An operand is required at the right of: \"" + token.word + "\"");
                    }
                } // Cases of unary-prefix operators

                // Cases of binary operators or a separator of partial expressions
                if (token.operator.type == OperatorType.BINARY || token.word.equals(",")) {

                    // Only leaf elements, open parenthesis, and unary-prefix operator can be a right-operand.
                    if( !(  nextIsLeaf || nextIsOpenParenthesis || nextIsPrefixOperator || nextIsFunctionIdentifier ) ) {
                        throw new Exevalator.Exception("An operand is required at the right of: \"" + token.word + "\"");
                    }
                    // Only leaf elements and closed parenthesis can be a right-operand.
                    if( !(  prevIsLeaf || prevIsCloseParenthesis  ) ) {
                        throw new Exevalator.Exception("An operand is required at the left of: \"" + token.word + "\"");
                    }
                } // Cases of binary operators or a separator of partial expressions

            } // Case of operators

            // Case of leaf elements
            if (leafTypeSet.contains(token.type)) {

                // An other leaf element or an open parenthesis can not be at the right of an leaf element.
                if (!nextIsFunctionCallBegin && (nextIsOpenParenthesis || nextIsLeaf)) {
                    throw new Exevalator.Exception("An operator is required at the right of: \"" + token.word + "\"");
                }

                // An other leaf element or a closed parenthesis can not be at the left of an leaf element.
                if (prevIsCloseParenthesis || prevIsLeaf) {
                    throw new Exevalator.Exception("An operator is required at the left of: \"" + token.word + "\"");
                }
            } // Case of leaf elements
        } // Loops for each token
    } // End of this method
}


/**
 * The class performing functions of a parser.
 */
final class Parser {

    /**
     * Parses tokens and construct Abstract Syntax Tree (AST).
     *
     * @param tokens Tokens to be parsed.
     * @return The root node of the constructed AST.
     */
    public static AstNode parse(Token[] tokens) {

        /* In this method, we use a non-recursive algorithm for the parsing.
        * Processing cost is maybe O(N), where N is the number of tokens. */

        // Number of tokens
        int tokenCount = tokens.length;

        // Working stack to form multiple AstNode instances into a tree-shape.
        Deque<AstNode> stack = new ArrayDeque<AstNode>();

        // Temporary nodes used in the above working stack, for isolating ASTs of partial expressions.
        AstNode parenthesisStackLid = new AstNode(new Token(TokenType.STACK_LID, "(PARENTHESIS_STACK_LID)"));
        AstNode separatorStackLid = new AstNode(new Token(TokenType.STACK_LID, "(SEPARATOR_STACK_LID)"));
        AstNode callBeginStackLid = new AstNode(new Token(TokenType.STACK_LID, "(CALL_BEGIN_STACK_LID)"));

        // The array storing next operator's precedence for each token.
        // At [i], it is stored that the precedence of the first operator of which token-index is greater than i.
        int[] nextOperatorPrecedences = getNextOperatorPrecedences(tokens);

        // Read tokens from left to right.
        int itoken = 0;
        do {
            Token token = tokens[itoken];
            AstNode operatorNode = null;

            // Case of literals and identifiers: "1.23", "x", "f", etc.
            if (token.type == TokenType.NUMBER_LITERAL
                    || token.type == TokenType.VARIABLE_IDENTIFIER
                    || token.type == TokenType.FUNCTION_IDENTIFIER) {
                stack.push(new AstNode(token));
                itoken++;
                continue;

            // Case of parenthesis: "(" or ")"
            } else if (token.type == TokenType.PARENTHESIS) {
                if (token.word.equals("(")) {
                    stack.push(parenthesisStackLid);
                    itoken++;
                    continue;
                } else { // Case of ")"
                    operatorNode = popPartialExprNodes(stack, parenthesisStackLid)[0];
                }

            // Case of separator: ","
            } else if (token.type == TokenType.EXPRESSION_SEPARATOR) {
                stack.push(separatorStackLid);
                itoken++;
                continue;

            // Case of operators: "+", "-", etc.
            } else if (token.type == TokenType.OPERATOR) {
                operatorNode = new AstNode(token);
                int nextOpPrecedence = nextOperatorPrecedences[itoken];

                // Case of unary-prefix operators:
                // * Connect the node of right-token as an operand, if necessary (depending the next operator's precedence).
                if (token.operator.type == OperatorType.UNARY_PREFIX) {
                    if (shouldAddRightOperand(token.operator.precedence, nextOpPrecedence)) {
                        operatorNode.childNodeList.add(new AstNode(tokens[itoken + 1]));
                        itoken++;
                    } // else: Operand will be connected later. See the bottom of this loop.

                // Case of binary operators:
                // * Always connect the node of left-token as an operand.
                // * Connect the node of right-token as an operand, if necessary (depending the next operator's precedence).
                } else if (token.operator.type == OperatorType.BINARY) {
                    operatorNode.childNodeList.add(stack.pop());
                    if (shouldAddRightOperand(token.operator.precedence, nextOpPrecedence)) {
                        operatorNode.childNodeList.add(new AstNode(tokens[itoken + 1]));
                        itoken++;
                    } // else: Right-operand will be connected later. See the bottom of this loop.

                // Case of function-call operators.
                } else if (token.operator.type == OperatorType.CALL) {
                    if (token.word.equals("(")) {
                        operatorNode.childNodeList.add(stack.pop()); // Add function-identifier node at the top of the stack.
                        stack.push(operatorNode);
                        stack.push(callBeginStackLid); // The marker to correct partial expressions of args from the stack.
                        itoken++;
                        continue;
                    } else { // Case of ")"
                        AstNode[] argNodes = popPartialExprNodes(stack, callBeginStackLid);
                        operatorNode = stack.pop();
                        for (AstNode argNode: argNodes) {
                            operatorNode.childNodeList.add(argNode);
                        }
                    }
                }
            }

            // If the precedence of the operator at the top of the stack is stronger than the next operator,
            // connect all "unconnected yet" operands and operators in the stack.
            while (shouldAddRightOperandToStackedOperator(stack, nextOperatorPrecedences[itoken])) {
                AstNode oldOperatorNode = operatorNode;
                operatorNode = stack.pop();
                operatorNode.childNodeList.add(oldOperatorNode);
            }
            stack.push(operatorNode);
            itoken++;

        } while (itoken < tokenCount);

        // The AST has been constructed on the stack, and only its root node is stored in the stack.
        AstNode rootNodeOfExpressionAst = stack.pop();

        // Check that the depth of the constructed AST does not exceeds the limit.
        rootNodeOfExpressionAst.checkDepth(1, StaticSettings.MAX_AST_DEPTH);

        return rootNodeOfExpressionAst;
    }

    /**
     * Judges whether the right-side token should be connected directly as an operand, to the target operator.
     *
     * @param targetOperatorPrecedence The precedence of the target operator (smaller value gives higher precedence).
     * @param nextOperatorPrecedence The precedence of the next operator (smaller value gives higher precedence).
     * @return Returns true if the right-side token (operand) should be connected to the target operator.
     */
    private static boolean shouldAddRightOperand(int targetOperatorPrecedence, int nextOperatorPrecedence) {
        return targetOperatorPrecedence <= nextOperatorPrecedence; // left is stronger
    }

    /**
     * Judges whether the right-side token should be connected directly as an operand,
     * to the operator at the top of the working stack.
     *
     * @param stack The working stack used for the parsing.
     * @param nextOperatorPrecedence The precedence of the next operator (smaller value gives higher precedence).
     * @return Returns true if the right-side token (operand) should be connected to the operator at the top of the stack.
     */
    private static boolean shouldAddRightOperandToStackedOperator(Deque<AstNode> stack, int nextOperatorPrecedence) {
        if (stack.size() == 0 || stack.peek().token.type != TokenType.OPERATOR) {
            return false;
        }
        return shouldAddRightOperand(stack.peek().token.operator.precedence, nextOperatorPrecedence);
    }

    /**
     * Pops root nodes of ASTs of partial expressions constructed on the stack.
     *
     * @param stack The working stack used for the parsing.
     * @param endStackLidNode The temporary node pushed in the stack, at the end of partial expressions to be popped.
     * @return Root nodes of ASTs of partial expressions.
     */
    private static AstNode[] popPartialExprNodes(Deque<AstNode> stack, AstNode endStackLidNode) {
        if (stack.size() == 0) {
            throw new Exevalator.Exception("Unexpected end of a partial expression");
        }
        List<AstNode> partialExprNodeList = new ArrayList<AstNode>();
        while(stack.size() != 0) {
            if (stack.peek().token.type == TokenType.STACK_LID) {
                AstNode stackLidNode = stack.pop();
                if (stackLidNode == endStackLidNode) {
                    break;
                }
            } else {
                partialExprNodeList.add(stack.pop());
            }
        }
        return partialExprNodeList.toArray(new AstNode[partialExprNodeList.size()]);
    }

    /**
     * Returns an array storing next operator's precedence for each token.
     * In the returned array, it will stored at [i] that
     * precedence of the first operator of which token-index is greater than i.
     *
     * @param tokens All tokens to be parsed.
     * @return The array storing next operator's precedence for each token.
     */
    private static int[] getNextOperatorPrecedences(Token[] tokens) {
        int tokenCount = tokens.length;
        int lastOperatorPrecedence = Integer.MAX_VALUE; // least prior
        int[] nextOperatorPrecedences = new int[tokenCount];

        for (int itoken=tokenCount-1; 0<=itoken; itoken--) {
            Token token = tokens[itoken];
            nextOperatorPrecedences[itoken] = lastOperatorPrecedence;

            if (token.type == TokenType.OPERATOR) {
                lastOperatorPrecedence = token.operator.precedence;
            }

            if (token.type == TokenType.PARENTHESIS) {
                if (token.word.equals("(")) {
                    lastOperatorPrecedence = 0; // most prior
                } else { // case of ")"
                    lastOperatorPrecedence = Integer.MAX_VALUE; // least prior
                }
            }
        }
        return nextOperatorPrecedences;
    }
}


/**
 * The enum representing types of operators.
 */
enum OperatorType {

    /** Represents unary operator, for example: - of -1.23 */
    UNARY_PREFIX,

    /** Represents binary operator, for example: + of 1+2 */
    BINARY,

    /** Represents function-call operator */
    CALL
}


/**
 * The class storing information of an operator.
 */
final class Operator {

    /** The symbol of this operator (for example: '+'). */
    public final char symbol;

    /** The precedence of this operator (smaller value gives higher precedence). */
    public final int precedence;

    /** The type of operator tokens. */
    public final OperatorType type;

    /**
     * Create an Operator instance storing specified information.
     *
     * @param type The type of this operator.
     * @param symbol The symbol of this operator.
     * @param precedence The precedence of this operator.
     */
    public Operator(OperatorType type, char symbol, int precedence) {
        this.type = type;
        this.symbol = symbol;
        this.precedence = precedence;
    }

    /**
     * Returns the String representation of this Operator instance.
     */
    @Override
    public String toString() {
        return "Operator [symbol=" + symbol + ", precedence=" + precedence + ", type=" + type + "]";
    }
}


/**
 * The enum representing types of tokens.
 */
enum TokenType {

    /** Represents number literal tokens, for example: 1.23 */
    NUMBER_LITERAL,

    /** Represents operator tokens, for example: + */
    OPERATOR,

    /** Represents separator tokens of partial expressions: , */
    EXPRESSION_SEPARATOR,

    /** Represents parenthesis, for example: ( and ) of (1*(2+3)) */
    PARENTHESIS,

    /** Represents variable-identifier tokens, for example: x */
    VARIABLE_IDENTIFIER,

    /** Represents function-identifier tokens, for example: f */
    FUNCTION_IDENTIFIER,

    /** Represents temporary token for isolating partial expressions in the stack, in parser */
    STACK_LID
}


/**
 * The class storing information of an token.
 */
final class Token {

    /** The type of this token. */
    public final TokenType type;

    /** The text representation of this token. */
    public final String word;

    /** The detailed information of the operator, if the type of this token is OPERATOR. */
    public final Operator operator;

    /**
     * Create an Token instance storing specified information.
     *
     * @param type The type of this token.
     * @param word The text representation of this token.
     */
    public Token(TokenType type, String word) {
        this.type = type;
        this.word = word;
        this.operator = null;
    }

    /**
     * Create an Token instance storing specified information.
     *
     * @param type The type of this token.
     * @param word The text representation of this token.
     * @param operator The detailed information of the operator, for OPERATOR type tokens.
     */
    public Token(TokenType type, String word, Operator operator) {
        this.type = type;
        this.word = word;
        this.operator = operator;
    }

    /**
     * Returns the String representation of this Token instance.
     */
    @Override
    public String toString() {
        if (this.operator == null) {
            return "Token [type=" + type + ", word=" + word + "]";
        } else {
            return "Token [type=" + type + ", word=" + word +
                ", operator.type=" + operator.type + ", operator.precedence=" + operator.precedence + "]";
        }
    }
}


/**
 * The class storing information of an node of an AST.
 */
final class AstNode {

    /** The token corresponding with this AST node. */
    public final Token token;

    /** The list of child nodes of this AST node. */
    public final List<AstNode> childNodeList;

    /**
     * Create an AST node instance storing specified information.
     *
     * @param token The token corresponding with this AST node
     */
    public AstNode(Token token) {
        this.token = token;
        this.childNodeList = new ArrayList<AstNode>();
    }

    /**
     * Checks that depths in the AST of all nodes under this node (child nodes, grandchild nodes, and so on)
     * does not exceeds the specified maximum value.
     * An ExevalatorException will be thrown when the depth exceeds the maximum value.
     * If the depth does not exceeds the maximum value, nothing will occur.
     *
     * @param depthOfThisNode The depth of this node in the AST.
     * @param maxAstDepth The maximum value of the depth of the AST.
     */
    public void checkDepth(int depthOfThisNode, int maxAstDepth) {
        if (maxAstDepth < depthOfThisNode) {
            throw new Exevalator.Exception(
                "The depth of the AST exceeds the limit (StaticSettings.MAX_AST_DEPTH: "
                + StaticSettings.MAX_AST_DEPTH + ")"
            );
        }
        for (AstNode childNode: this.childNodeList) {
            childNode.checkDepth(depthOfThisNode + 1, maxAstDepth);
        }
    }

    /**
     * Expresses the AST under this node in XML-like text format.
     *
     * @return XML-like text representation of the AST under this node.
     */
    public String toMarkuppedText() {
        return this.toMarkuppedText(0);
    }

    /**
     * Expresses the AST under this node in XML-like text format.
     *
     * @param indentStage The stage of indent of this node.
     * @return XML-like text representation of the AST under this node.
     */
    public String toMarkuppedText(int indentStage) {
        StringBuilder indentBuilder = new StringBuilder();
        for (int istage=0; istage<indentStage; istage++) {
            indentBuilder.append(StaticSettings.AST_INDENT);
        }
        final String indent = indentBuilder.toString();
        final String eol = System.getProperty("line.separator");
        StringBuilder resultBuilder = new StringBuilder();

        resultBuilder.append(indent);
        resultBuilder.append("<");
        resultBuilder.append(this.token.type);
        resultBuilder.append(" word=\"");
        resultBuilder.append(this.token.word);
        resultBuilder.append("\"");
        if (this.token.type == TokenType.OPERATOR) {
            resultBuilder.append(" optype=\"");
            resultBuilder.append(this.token.operator.type);
            resultBuilder.append("\" precedence=\"");
            resultBuilder.append(this.token.operator.precedence);
            resultBuilder.append("\"");
        }

        if (0 < this.childNodeList.size()) {
            resultBuilder.append(">");
            for (AstNode childNode: this.childNodeList) {
                resultBuilder.append(eol);
                resultBuilder.append(childNode.toMarkuppedText(indentStage + 1));
            }
            resultBuilder.append(eol);
            resultBuilder.append(indent);
            resultBuilder.append("</");
            resultBuilder.append(this.token.type);
            resultBuilder.append(">");

        } else {
            resultBuilder.append(" />");
        }

        return resultBuilder.toString();
    }
}


/**
 * The class for evaluating the value of an AST.
 */
final class Evaluator {

    /** The tree of evaluator nodes, which evaluates an expression. */
    private volatile EvaluatorNode evaluatorNodeTree = null;

    /**
     * Updates the state to evaluate the value of the AST.
     *
     * @param ast The root node of the AST.
     * @param variableTable The Map mapping each variable name to an address of the variable.
     * @param functionTable The Map mapping each function name to an IExevalatorFunction instance.
     */
    public void update(AstNode ast, Map<String, Integer> variableTable, Map<String, Exevalator.FunctionInterface> functionTable) {
        this.evaluatorNodeTree = Evaluator.createEvaluatorNodeTree(ast, variableTable, functionTable);
    }

    /**
     * Returns whether "evaluate" method is available on the current state.
     *
     * @return Return value - True if "evaluate" method is available.
     */
    public boolean isEvaluatable() {
        return this.evaluatorNodeTree != null;
    }

    /**
     * Evaluates the value of the AST set by "update" method.
     *
     * @param memory The Vec used as as a virtual memory storing values of variables.
     * @return The evaluated value.
     */
    public double evaluate(double[] memory) {
        return this.evaluatorNodeTree.evaluate(memory);
    }

    /**
     * Creates a tree of evaluator nodes corresponding with the specified AST.
     *
     * @param ast The root node of the AST.
     * @param variableTable The Map mapping each variable name to an address of the variable.
     * @param functionTable The Map mapping each function name to an IExevalatorFunction instance.
     * @return The root node of the created tree of evaluator nodes.
     */
    public static EvaluatorNode createEvaluatorNodeTree(
            AstNode ast, Map<String, Integer> variableTable, Map<String, Exevalator.FunctionInterface> functionTable) {

        // Note: This method creates a tree of evaluator nodes by traversing each node in the AST recursively.

        List<AstNode> childNodeList = ast.childNodeList;
        int childCount = childNodeList.size();

        // Creates evaluator nodes of child nodes, and store then into an array.
        Evaluator.EvaluatorNode childNodeNodes[] = new Evaluator.EvaluatorNode[childCount];
        for (int ichild=0; ichild<childCount; ichild++) {
            AstNode childAstNode = childNodeList.get(ichild);
            childNodeNodes[ichild] = createEvaluatorNodeTree(childAstNode, variableTable, functionTable);
        }

        // Initialize evaluator nodes of this node.
        Token token = ast.token;
        if (token.type == TokenType.NUMBER_LITERAL) {
            return new Evaluator.NumberLiteralEvaluatorNode(token.word);
        } else if (token.type == TokenType.VARIABLE_IDENTIFIER) {
            if (!variableTable.containsKey(token.word)) {
                throw new Exevalator.Exception("Variable not found: " + token.word);
            }
            int address = variableTable.get(token.word);
            return new Evaluator.VariableEvaluatorNode(address);
        } else if (token.type == TokenType.FUNCTION_IDENTIFIER) {
            return null;
        } else if (token.type == TokenType.OPERATOR) {
            Operator op = token.operator;

            if (op.type == OperatorType.UNARY_PREFIX && op.symbol == '-') {
                return new Evaluator.MinusEvaluatorNode(childNodeNodes[0]);
            } else if (op.type == OperatorType.BINARY && op.symbol == '+') {
                return new Evaluator.AdditionEvaluatorNode(childNodeNodes[0], childNodeNodes[1]);
            } else if (op.type == OperatorType.BINARY && op.symbol == '-') {
                return new Evaluator.SubtractionEvaluatorNode(childNodeNodes[0], childNodeNodes[1]);
            } else if (op.type == OperatorType.BINARY && op.symbol == '*') {
                return new Evaluator.MultiplicationEvaluatorNode(childNodeNodes[0], childNodeNodes[1]);
            } else if (op.type == OperatorType.BINARY && op.symbol == '/') {
                return new Evaluator.DivisionEvaluatorNode(childNodeNodes[0], childNodeNodes[1]);
            } else if (op.type == OperatorType.CALL && op.symbol == '(') {
                String identifier = childNodeList.get(0).token.word;
                if (!functionTable.containsKey(identifier)) {
                    throw new Exevalator.Exception("Function not found: " + identifier);
                }
                Exevalator.FunctionInterface function = functionTable.get(identifier);
                int argCount = childCount - 1;
                Evaluator.EvaluatorNode[] argNodes = new Evaluator.EvaluatorNode[argCount];
                for (int iarg=0; iarg<argCount; iarg++) {
                    argNodes[iarg] = childNodeNodes[iarg + 1];
                }
                return new Evaluator.FunctionEvaluatorNode(function, identifier, argNodes);
            } else {
                throw new Exevalator.Exception("Unexpected operator: " + op);
            }
        } else {
            throw new Exevalator.Exception("Unexpected token type: " + token.type);
        }
    }

    /**
     * The super class of evaluator nodes.
     */
    public static abstract class EvaluatorNode {

        /**
         * Performs the evaluation.
         *
         * @param memory The array storing values of variables.
         * @return The evaluated value.
         */
        public abstract double evaluate(double[] memory);
    }

    /**
     * The super class of evaluator nodes of binary operations.
     */
    public static abstract class BinaryOperationEvaluatorNode extends EvaluatorNode {

        /** The node for evaluating the right-side operand. */
        protected final EvaluatorNode leftOperandNode;

        /** The node for evaluating the left-side operand. */
        protected final EvaluatorNode rightOperandNode;

        /**
         * Initializes operands.
         *
         * @param leftOperandNode The node for evaluating the left-side operand
         * @param rightOperandNode The node for evaluating the right-side operand
         */
        protected BinaryOperationEvaluatorNode(EvaluatorNode leftOperandNode, EvaluatorNode rightOperandNode) {
            this.leftOperandNode = leftOperandNode;
            this.rightOperandNode = rightOperandNode;
        }
    }

    /**
     * The evaluator node for evaluating the value of a addition operator.
     */
    public static final class AdditionEvaluatorNode extends BinaryOperationEvaluatorNode {

        /**
         * Initializes operands.
         *
         * @param leftOperandNode The node for evaluating the left-side operand.
         * @param rightOperandNode The node for evaluating the right-side operand.
         */
        public AdditionEvaluatorNode(EvaluatorNode leftOperandNode, EvaluatorNode rightOperandNode) {
            super(leftOperandNode, rightOperandNode);
        }

        /**
         * Performs the addition.
         *
         * @param memory The array storing values of variables.
         * @return The result value of the addition.
         */
        @Override
        public double evaluate(double[] memory) {
            return this.leftOperandNode.evaluate(memory) + this.rightOperandNode.evaluate(memory);
        }
    }

    /**
     * The evaluator node for evaluating the value of a subtraction operator.
     */
    public static final class SubtractionEvaluatorNode extends BinaryOperationEvaluatorNode {

        /**
         * Initializes operands.
         *
         * @param leftOperandNode The node for evaluating the left-side operand.
         * @param rightOperandNode The node for evaluating the right-side operand.
         */
        public SubtractionEvaluatorNode(EvaluatorNode leftOperandNode, EvaluatorNode rightOperandNode) {
            super(leftOperandNode, rightOperandNode);
        }

        /**
         * Performs the subtraction.
         *
         * @param memory The array storing values of variables.
         * @return The result value of the subtraction.
         */
        @Override
        public double evaluate(double[] memory) {
            return this.leftOperandNode.evaluate(memory) - this.rightOperandNode.evaluate(memory);
        }
    }

    /**
     * The evaluator node for evaluating the value of a multiplication operator.
     */
    public static final class MultiplicationEvaluatorNode extends BinaryOperationEvaluatorNode {

        /**
         * Initializes operands.
         *
         * @param leftOperandNode The node for evaluating the left-side operand.
         * @param rightOperandNode The node for evaluating the right-side operand.
         */
        public MultiplicationEvaluatorNode(EvaluatorNode leftOperandNode, EvaluatorNode rightOperandNode) {
            super(leftOperandNode, rightOperandNode);
        }

        /**
         * Performs the multiplication.
         *
         * @param memory The array storing values of variables.
         * @return The result value of the multiplication.
         */
        @Override
        public double evaluate(double[] memory) {
            return this.leftOperandNode.evaluate(memory) * this.rightOperandNode.evaluate(memory);
        }
    }

    /**
     * The evaluator node for evaluating the value of a division operator.
     */
    public static final class DivisionEvaluatorNode extends BinaryOperationEvaluatorNode {

        /**
         * Initializes operands.
         *
         * @param leftOperandNode The node for evaluating the left-side operand.
         * @param rightOperandNode The node for evaluating the right-side operand.
         */
        public DivisionEvaluatorNode(EvaluatorNode leftOperandNode, EvaluatorNode rightOperandNode) {
            super(leftOperandNode, rightOperandNode);
        }

        /**
         * Performs the division.
         *
         * @param memory The array storing values of variables.
         * @return The result value of the division.
         */
        @Override
        public double evaluate(double[] memory) {
            return this.leftOperandNode.evaluate(memory) / this.rightOperandNode.evaluate(memory);
        }
    }

    /**
     * The evaluator node for evaluating the value of a unary-minus operator.
     */
    public static final class MinusEvaluatorNode extends EvaluatorNode {

        /** The node for evaluating the operand. */
        private final EvaluatorNode operandNode;

        /**
         * Initializes the operand.
         *
         * @param operandNode The node for evaluating the operand
         */
        public MinusEvaluatorNode(EvaluatorNode operandNode) {
            this.operandNode = operandNode;
        }

        /**
         * Performs the division.
         *
         * @param memory The array storing values of variables.
         * @return The result value of the division.
         */
        @Override
        public double evaluate(double[] memory) {
            return -this.operandNode.evaluate(memory);
        }
    }

    /**
     * The evaluator node for evaluating the value of a number literal.
     */
    public static final class NumberLiteralEvaluatorNode extends EvaluatorNode {

        /** The value of the number literal. */
        private final double value;

        /**
         * Initializes the value of the number literal.
         *
         * @param literal The number literal.
         */
        public NumberLiteralEvaluatorNode(String literal) {
            try {
                this.value = Double.parseDouble(literal);
            } catch (NumberFormatException nfe) {
                throw new Exevalator.Exception("Invalid number literal: " + literal);
            }
        }

        /**
         * Returns the value of the number literal.
         *
         * @param memory The array storing values of variables.
         * @return The value of the number literal.
         */
        @Override
        public double evaluate(double[] memory) {
            return this.value;
        }
    }

    /**
     * The evaluator node for evaluating the value of a variable.
     */
    public static final class VariableEvaluatorNode extends EvaluatorNode {

        /** The address of the variable. */
        private volatile int address;

        /**
         * Initializes the address of the variable.
         *
         * @param address The address of the variable.
         */
        public VariableEvaluatorNode(int address) {
            this.address = address;
        }

        /**
         * Returns the value of the variable.
         *
         * @param memory The array storing values of variables.
         * @return The value of the variable.
         */
        @Override
        public double evaluate(double[] memory) {
            if (address < 0 || memory.length <= address) {
                throw new Exevalator.Exception("Invalid memory address: " + address);
            }
            return memory[this.address];
        }
    }

    /**
     * The evaluator node for evaluating a function-call operator.
     *
     */
    public static final class FunctionEvaluatorNode extends EvaluatorNode {

        /** The function to be called. */
        private volatile Exevalator.FunctionInterface function;

        /** The name of the function. */
        private volatile String functionName;

        /** Evaluator nodes for evaluating values of arguments. */
        private volatile EvaluatorNode[] argumentEvalNodes;

        /** An array storing evaluated values of arguments. */
        private volatile double[] argumentArrayBuffer;

        /**
         * Initializes information of functions to be called.
         *
         * @param function The function to be called.
         * @param functionName The name of the function.
         * @param argumentEvalNodes Evaluator nodes for evaluating values of arguments.
         */
        public FunctionEvaluatorNode(
                Exevalator.FunctionInterface function, String functionName, EvaluatorNode[] argumentEvalNodes) {
            this.function = function;
            this.functionName = functionName;
            this.argumentEvalNodes = argumentEvalNodes;
            this.argumentArrayBuffer = new double[this.argumentEvalNodes.length];
        }

        /**
         * Calls the function and returns the returned value of the function.
         *
         * @param memory The array storing values of variables.
         * @return The returned value of the function.
         */
        @Override
        public double evaluate(double[] memory) {
            int argCount = this.argumentEvalNodes.length;
            for (int iarg=0; iarg<argCount; iarg++) {
                this.argumentArrayBuffer[iarg] = this.argumentEvalNodes[iarg].evaluate(memory);
            }
            try {
                return this.function.invoke(this.argumentArrayBuffer);
            } catch (Exception e) {
                throw new Exevalator.Exception("Function error (" + this.functionName + ")", e);
            }
        }
    }
}


/**
 * The class defining static setting values.
 */
final class StaticSettings {

    /** The maximum number of characters in an expression. */
    public static final int MAX_EXPRESSION_CHAR_COUNT = 256;

    /** The maximum number of characters of variable/function names. */
    public static final int MAX_NAME_CHAR_COUNT = 64;

    /** The maximum number of tokens in an expression. */
    public static final int MAX_TOKEN_COUNT = 64;

    /** The maximum depth of an Abstract Syntax Tree (AST). */
    public static final int MAX_AST_DEPTH = 32;

    /** The indent used in text representations of ASTs. */
    public static final String AST_INDENT = "  ";

    /** The regular expression of number literals. */
    public static final String NUMBER_LITERAL_REGEX =
        "(?<=(\\s|\\+|-|\\*|/|\\(|\\)|,|^))" + // Token splitters, or beginning of the expression
        "([0-9]+(\\.[0-9]+)?)" +               // Significand part
        "((e|E)(\\+|-)?[0-9]+)?";              // Exponent part

    /** The escaped representation of number literals in expressions */
    public static final String ESCAPED_NUMBER_LITERAL = "@NUMBER_LITERAL@";

    /** The set of symbols of available operators. */
    public static final Set<Character> OPERATOR_SYMBOL_SET;

    /** The Map mapping each symbol of an unary-prefix operator to an instance of Operator class. */
    public static final Map<Character, Operator> UNARY_PREFIX_OPERATOR_SYMBOL_MAP;

    /** The Map mapping each symbol of an binary operator to an instance of Operator class. */
    public static final Map<Character, Operator> BINARY_OPERATOR_SYMBOL_MAP;

    /** The Map mapping each symbol of an call operator to an instance of Operator class. */
    public static final Map<Character, Operator> CALL_OPERATOR_SYMBOL_MAP;

    /** The list of symbols to split an expression into tokens. */
    public static final List<Character> TOKEN_SPLITTER_SYMBOL_LIST;

    static {
        Operator additionOperator       = new Operator(OperatorType.BINARY, '+', 400);
        Operator subtractionOperator    = new Operator(OperatorType.BINARY, '-', 400);
        Operator multiplicationOperator = new Operator(OperatorType.BINARY, '*', 300);
        Operator divisionOperator       = new Operator(OperatorType.BINARY, '/', 300);
        Operator minusOperator          = new Operator(OperatorType.UNARY_PREFIX, '-', 200);
        Operator callBeginOperator      = new Operator(OperatorType.CALL, '(', 100);
        Operator callEndOperator        = new Operator(OperatorType.CALL, ')', Integer.MAX_VALUE); // least prior

        OPERATOR_SYMBOL_SET = new HashSet<Character>();
        OPERATOR_SYMBOL_SET.add('+');
        OPERATOR_SYMBOL_SET.add('-');
        OPERATOR_SYMBOL_SET.add('*');
        OPERATOR_SYMBOL_SET.add('/');
        OPERATOR_SYMBOL_SET.add('(');
        OPERATOR_SYMBOL_SET.add(')');

        UNARY_PREFIX_OPERATOR_SYMBOL_MAP = new ConcurrentHashMap<Character, Operator>();
        UNARY_PREFIX_OPERATOR_SYMBOL_MAP.put('-', minusOperator);

        BINARY_OPERATOR_SYMBOL_MAP = new ConcurrentHashMap<Character, Operator>();
        BINARY_OPERATOR_SYMBOL_MAP.put('+', additionOperator);
        BINARY_OPERATOR_SYMBOL_MAP.put('-', subtractionOperator);
        BINARY_OPERATOR_SYMBOL_MAP.put('*', multiplicationOperator);
        BINARY_OPERATOR_SYMBOL_MAP.put('/', divisionOperator);

        CALL_OPERATOR_SYMBOL_MAP = new ConcurrentHashMap<Character, Operator>();
        CALL_OPERATOR_SYMBOL_MAP.put('(', callBeginOperator);
        CALL_OPERATOR_SYMBOL_MAP.put(')', callEndOperator);

        TOKEN_SPLITTER_SYMBOL_LIST = new ArrayList<Character>();
        TOKEN_SPLITTER_SYMBOL_LIST.add('+');
        TOKEN_SPLITTER_SYMBOL_LIST.add('-');
        TOKEN_SPLITTER_SYMBOL_LIST.add('*');
        TOKEN_SPLITTER_SYMBOL_LIST.add('/');
        TOKEN_SPLITTER_SYMBOL_LIST.add('(');
        TOKEN_SPLITTER_SYMBOL_LIST.add(')');
        TOKEN_SPLITTER_SYMBOL_LIST.add(',');
    };
}
