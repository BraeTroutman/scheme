{-# LANGUAGE ExistentialQuantification #-}

module Lib
    ( 
    symbol,
    readExpr,
    eval,
    extractValue,
    trapError
    ) where

import Text.ParserCombinators.Parsec hiding (spaces)
import Control.Monad (liftM)
import Control.Monad.Except
import Numeric (readHex, readOct, readFloat)
import Data.Char (digitToInt)
import Data.Ratio (Ratio, (%))
import Data.Complex (Complex (..))

-- types
data LispVal = Atom String
             | List [LispVal]
             | DottedList [LispVal] LispVal
             | Number Integer
             | String String
	     | Character Char
	     | Float Double
             | Ratio Rational
             | Complex (Complex Double)
             | Bool Bool

data LispError = NumArgs Integer [LispVal]
	       | TypeMismatch String LispVal
	       | Parser ParseError
	       | BadSpecialForm String LispVal
	       | NotFunction String String
               | UnboundVar String String
	       | Default String

type ThrowsError = Either LispError

data Unpacker = forall a. Eq a => AnyUnpacker (LispVal -> ThrowsError a)

-- exports
symbol :: Parser Char
symbol = oneOf "~!@#$%^&*_-+=?<>|/:"

readExpr :: String -> ThrowsError LispVal
readExpr input = case parse parseExpr "lisp" input of
		   Left err -> throwError $ Parser err
		   Right val -> return val

-- data to string conversion
showVal :: LispVal -> String
showVal (String contents) = "\"" ++ contents ++ "\""
showVal (Atom name) = name
showVal (Number n) = show n
showVal (Bool True) = "#t"
showVal (Bool False) = "#f"
showVal (Complex (n :+ d)) = (show n) ++ "+" ++ (show d) ++ "i"
showVal (List contents) = "(" ++ unwordsList contents ++ ")"
showVal (DottedList car cdr) = "(" ++ unwordsList car ++ " . " ++ showVal cdr ++ ")"

unwordsList :: [LispVal] -> String
unwordsList = unwords . map showVal

showError :: LispError -> String
showError (UnboundVar message varname)  = message ++ ": " ++ varname
showError (BadSpecialForm message form) = message ++ ": " ++ show form
showError (NotFunction message func)    = message ++ ": " ++ show func
showError (NumArgs expected found)      = "Expected " ++ show expected
				       ++ " args; found values: " ++ unwordsList found
showError (TypeMismatch expected found) = "Invalid type: expected " ++ expected
				       ++ ", found " ++ show found
showError (Parser parseErr)		= "Parse error at " ++ show parseErr 

instance Show LispError where show = showError
instance Show LispVal where show = showVal

-- data evaluation
eval :: LispVal -> ThrowsError LispVal
eval val@(String _) = return val
eval val@(Number _) = return val
eval val@(Bool _) = return val
eval (List [Atom "quote", val]) = return val
eval (List [Atom "if", pred, conseq, alt]) = do
		     result <- eval pred
		     case result of
			Bool False -> eval alt
			Bool True -> eval conseq
			notBool -> throwError $ TypeMismatch "boolean" notBool
eval (List (Atom func : args)) = mapM eval args >>= apply func
eval badForm = throwError $ BadSpecialForm "Unrecognized special form" badForm

apply :: String -> [LispVal] -> ThrowsError LispVal
apply func args = maybe (throwError $ NotFunction "Unrecognized primitive function" func)
			($ args)
			(lookup func primitives)

primitives :: [(String, [LispVal] -> ThrowsError LispVal)]
primitives = [("+", numericBinop (+)),
	      ("-", numericBinop (-)), 
	      ("*", numericBinop (*)),
	      ("/", numericBinop div),
	      ("mod", numericBinop mod),
	      ("quotient", numericBinop quot),
	      ("remainder", numericBinop rem),
	      ("symbol?", monop symbolp),
	      ("string?", monop stringp),
	      ("bool?", monop boolp),
	      ("list?", monop listp),
	      ("number?", monop numberp),
	      ("symbol->string", monop symbolToString),
	      ("string->symbol", monop stringToSymbol),
	      ("=", numBoolBinop (==)),
	      ("<", numBoolBinop (<)),
	      (">", numBoolBinop (>)),
	      ("/=", numBoolBinop (/=)),
	      (">=", numBoolBinop (/=)),
	      ("<=", numBoolBinop (<=)),
	      ("&&", boolBoolBinop (&&)),
	      ("||", boolBoolBinop (||)),
	      ("string=?", strBoolBinop (==)),
	      ("string<?", strBoolBinop (<)),
	      ("string>?", strBoolBinop (>)),
	      ("string<=?", strBoolBinop (<=)),
	      ("string>=?", strBoolBinop (>=)),
	      ("car", car),
	      ("cdr", cdr),
	      ("cons", cons),
	      ("eqv?", eqv),
	      ("eq?", eqv),
	      ("equal?", equal)
	     ]

-- lift haskell functions into lisp world
monop :: (LispVal -> LispVal) -> [LispVal] -> ThrowsError LispVal
monop op []  	  = throwError $ NumArgs 1 []
monop op [v] 	  = return $ op v
monop _  params@_ = throwError $ NumArgs 1 params

numericBinop :: (Integer -> Integer -> Integer) -> [LispVal] -> ThrowsError LispVal
numericBinop op		  []  = throwError $ NumArgs 2 []
numericBinop op singleVal@[_] = throwError $ NumArgs 2 singleVal
numericBinop op params 	      = mapM unpackNum params >>= return . Number . foldl1 op

unpackNum :: LispVal -> ThrowsError Integer
unpackNum (Number n) = return n
unpackNum (String n) = let parsed = reads n in
			   if null parsed
			      then throwError $ TypeMismatch "number" $ String n
			      else return $ fst $ parsed !! 0
unpackNum (List [n]) = unpackNum n
unpackNum notNum = throwError $ TypeMismatch "number" notNum

boolBinop :: (LispVal -> ThrowsError a) -> (a -> a -> Bool) -> [LispVal] -> ThrowsError LispVal
boolBinop unpacker op args = if length args /= 2
				then throwError $ NumArgs 2 args
				else do left <- unpacker $ args !! 0
					right <- unpacker $ args !! 1
					return $ Bool $ left `op` right

strMonop :: (LispVal -> ThrowsError a) -> (a -> String) -> [LispVal] -> ThrowsError LispVal
strMonop unpacker op args = if length args /= 1
			      then throwError $ NumArgs 1 args
			      else do val <- unpacker $ args !! 0
				      return $ String $ op val
boolMonop :: (LispVal -> ThrowsError a) -> (a -> Bool) -> [LispVal] -> ThrowsError LispVal
boolMonop unpacker op args = if length args /= 1
				then throwError $ NumArgs 1 args
				else do val <- unpacker $ args !! 0
					return $ Bool $ op val
numMonop :: (LispVal -> ThrowsError a) -> (a -> Integer) -> [LispVal] -> ThrowsError LispVal
numMonop unpacker op args = if length args /= 1
			       then throwError $ NumArgs 1 args
			       else do val <- unpacker $ args !! 0
				       return $ Number $ op val

numBoolBinop = boolBinop unpackNum
numBoolMonop = boolMonop unpackNum
strBoolBinop = boolBinop unpackStr
strBoolMonop = boolMonop unpackStr
boolBoolBinop = boolBinop unpackBool
boolBoolMonop = boolMonop unpackBool

unpackStr :: LispVal -> ThrowsError String
unpackStr (String s) = return s
unpackStr (Number n) = return $ show n
unpackStr (Bool b)   = return $ show b
unpackStr notString  = throwError $ TypeMismatch "string" notString

unpackBool :: LispVal -> ThrowsError Bool
unpackBool (Bool b) = return b
unpackBool (String "#t") = return True
unpackBool (String "#f") = return False
unpackBool notBool = throwError $ TypeMismatch "boolean" notBool

unpackEquals :: LispVal -> LispVal -> Unpacker -> ThrowsError Bool
unpackEquals arg1 arg2 (AnyUnpacker unpacker) = do
    unpacked1 <- unpacker arg1
    unpacked2 <- unpacker arg2
    return $ unpacked1 == unpacked2
    `catchError` (const $ return False)

equal :: [LispVal] -> ThrowsError LispVal
equal listPair@[List _, List _] = eqvList equal listPair
equal [(DottedList xs x), (DottedList ys y)] = equal [List $ x:xs, List $ y:ys]
equal [arg1, arg2] = do
    primitiveEquals <- liftM or $ mapM (unpackEquals arg1 arg2) 
		       [AnyUnpacker unpackNum, AnyUnpacker unpackStr, AnyUnpacker unpackBool]
    eqvEquals <- eqv [arg1, arg2]
    return $ Bool $ (primitiveEquals || let (Bool x) = eqvEquals in x)
equal badArgList = throwError $ NumArgs 2 badArgList

eqvList :: ([LispVal] -> ThrowsError LispVal) -> [LispVal] -> ThrowsError LispVal
eqvList eqvFunc [(List arg1), (List arg2)] = return $ Bool $ (length arg1 == length arg2) && (all eqvPair $ zip arg1 arg2) where
    eqvPair (x1, x2) = case eqvFunc [x1, x2] of
			 Left err -> False
			 Right (Bool val) -> val

-- haskell equivalents to lisp functions
symbolp, numberp, stringp, boolp, listp :: LispVal -> LispVal
symbolp (Atom _) = Bool True
symbolp _ = Bool False
numberp (Number _) = Bool True
numberp _ = Bool False
stringp (String _) = Bool True
stringp _ = Bool False
boolp (Bool _) = Bool True
boolp _ = Bool False
listp (List _) = Bool True
listp _ = Bool False

symbolToString :: LispVal -> LispVal
symbolToString (Atom s) = String s

stringToSymbol :: LispVal -> LispVal
stringToSymbol (String s) = Atom s

car :: [LispVal] -> ThrowsError LispVal
car [List (x:xs)] = return x
car [DottedList (x:xs) _] = return x
car [badArg] = throwError $ TypeMismatch "pair" badArg
car badArgList = throwError $ NumArgs 1 badArgList

cdr :: [LispVal] -> ThrowsError LispVal
cdr [List (x:xs)]         = return $ List xs
cdr [DottedList [_] x]    = return x
cdr [DottedList (_:xs) x] = return $ DottedList xs x
cdr [badArg]              = throwError $ TypeMismatch "pair" badArg
cdr badArgList            = throwError $ NumArgs 1 badArgList

cons :: [LispVal] -> ThrowsError LispVal
cons [x, List []] = return $ List [x]
cons [x, List xs] = return $ List $ x:xs
cons [x, DottedList xs xlast] = return $ DottedList (x:xs) xlast
cons [x,y] = return $ DottedList [x] y
cons badArgList = throwError $ NumArgs 2 badArgList

eqv :: [LispVal] -> ThrowsError LispVal
eqv [(Bool arg1), (Bool arg2)]     	   = return $ Bool $ arg1 == arg2
eqv [(Number arg1), (Number arg2)] 	   = return $ Bool $ arg1 == arg2
eqv [(String arg1), (String arg2)] 	   = return $ Bool $ arg1 == arg2
eqv [(Atom arg1), (Atom arg2)]     	   = return $ Bool $ arg1 == arg2
eqv [(DottedList xs x), (DottedList ys y)] = eqv [List $ x:xs, List $ y:ys]
eqv listPair@[List _, List _] 		   = eqvList eqv listPair
eqv [_, _] 				   = return $ Bool False
eqv badArgList 				   = throwError $ NumArgs 2 badArgList

-- error handling
trapError action = catchError action (return . show)

extractValue :: ThrowsError a -> a
extractValue (Right val) = val

-- parsers
parseExpr :: Parser LispVal
parseExpr = try parseComplex
	 <|> try parseFloat
	 <|> try parseRatio
	 <|> parseNumber 
         <|> parseAtom 
	 <|> parseString
	 <|> parseQuotes
	 <|> parseSexp

parseString :: Parser LispVal
parseString = do
    char '"'
    x <- many (escapedChars <|> noneOf "\"\\")
    char '"'
    return $ String x

parseAtom :: Parser LispVal
parseAtom = do
    first <- letter <|> symbol
    rest <- many (letter <|> digit <|> symbol)
    let atom = first : rest
    return $ case atom of
	       "#t" -> Bool True
	       "#f" -> Bool False
	       _    -> Atom atom

parseFloat :: Parser LispVal
parseFloat = do
  x <- many1 digit
  char '.'
  y <- many1 digit
  return $ Float (fst.head $ readFloat (x++"."++y))

parseRatio :: Parser LispVal
parseRatio = do
    x <- many1 digit
    char '/'
    y <- many1 digit
    return $ Ratio ((read x) % (read y))

toDouble :: LispVal -> Double
toDouble (Float f) = realToFrac f
toDouble (Number n) = fromIntegral n

parseComplex :: Parser LispVal
parseComplex = do
    x <- (try parseFloat <|> parseDecimal)
    char '+'
    y <- (try parseFloat <|> parseDecimal)
    char 'i'
    return $ Complex (toDouble x :+ toDouble y)

parseCharacter :: Parser LispVal
parseCharacter = do
    try $ string "#\\"
    value <- try (string "newline" <|> string "space")
	<|> do
	    x <- anyChar
	    notFollowedBy alphaNum
	    return [x]
    return $ Character $ case value of
			   "space"   -> ' '
			   "newline" -> '\n'
			   _	     -> (value !! 0)

binToInt :: String -> Int
binToInt = foldl (\acc n -> acc * 2 + digitToInt n) 0

parseBin :: Parser LispVal
parseBin = do
    try $ string "#b"
    x <- many1 (oneOf "10")
    return $ (Number . toInteger . binToInt) x

parseOct :: Parser LispVal
parseOct = do
    try $ string "#o"
    x <- many1 (oneOf "012345678")
    return $ Number (fst $ readOct x !! 0)

parseHex :: Parser LispVal
parseHex = do
    try $ string "#x"
    x <- (many1 (oneOf "0123456789abcdef")) 
      <|> (many1 (oneOf "0123456789ABCDEF"))
    return $ Number (fst $ readHex x !! 0)

parseDecimal :: Parser LispVal
parseDecimal = do
    x <- many1 digit
    return $ (Number . read) x

parseDecimal' :: Parser LispVal
parseDecimal' = do
    try $ string "#d"
    x <- many1 digit
    return $ (Number . read) x

parseNumber :: Parser LispVal
parseNumber = parseDecimal
	   <|> parseHex
	   <|> parseBin
	   <|> parseOct
	   <|> parseDecimal'

parseList :: Parser LispVal
parseList = liftM List $ sepBy parseExpr spaces

parseDottedList :: Parser LispVal
parseDottedList = do
    head <- endBy parseExpr spaces
    tail <- char '.' >> spaces >> parseExpr
    return $ DottedList head tail

parseQuoted :: Parser LispVal
parseQuoted = do
    char '\''
    x <- parseExpr
    return $ List [Atom "quote", x]

parseQuasiQuoted :: Parser LispVal
parseQuasiQuoted = do
    char '`'
    x <- parseExpr
    return $ List [Atom "quasiquote", x]

parseUnQuoted :: Parser LispVal
parseUnQuoted = do
    char ','
    x <- parseExpr
    return $ List [Atom "unquote", x]

parseUnQuoteSplicing :: Parser LispVal
parseUnQuoteSplicing = do
    char ','
    char '@'
    x <- parseExpr
    return $ List [Atom "unquote-splicing", x]

parseQuotes :: Parser LispVal
parseQuotes = parseQuasiQuoted <|> parseQuoted <|> parseUnQuoted <|> parseUnQuoteSplicing

parseSexp :: Parser LispVal
parseSexp = do
    char '('
    x <- try parseList <|> parseDottedList
    char ')'
    return x

spaces :: Parser ()
spaces = skipMany1 space

escapedChars :: Parser Char
escapedChars = do
    char '\\'
    x <- oneOf "\\\"nrt"
    return $ case x of
	       '\\' -> x
	       '"' -> x
	       'n' -> '\n'
	       't' -> '\t'
	       'r' -> '\r'

