
module IML.Lexer (
  Token(..), SubsumesToken(..), module IML.Lexer ) where

import GLL.Combinators (Token(..), SubsumesToken(..))

import IML.Grammar.Shared (prebound_mvar)

import Data.Char
import Text.Read (readEither)
import Text.Regex.Applicative
import IML.Trans.ProMan

lexer :: Component String [Token]
lexer = component_ iml_lexer

iml_lexer :: String -> [Token]
iml_lexer = lState "DEF" True lTokens (const iml_lexer) Just 

lState :: String -> Bool -> RE Char t -> (t -> String -> [Token]) ->
                  (t -> Maybe Token) -> String -> [Token]
lState _ _ _ _ _ [] = []
lState stateName discardLayout myTokens mySelector adder s =
    let re | discardLayout = Just <$> myTokens <|> ws
           | otherwise     = Just <$> myTokens
        ws =      (Nothing <$ some (psym isSpace))
              <|> (Nothing <$ string "//" <* many (psym ((/=) '\n')))
    in case findLongestPrefix re s of
        Just (Just tok, rest)   -> (maybe id (:) (adder tok)) (mySelector tok rest)
        Just (Nothing,rest)     -> lState stateName discardLayout myTokens mySelector adder rest
        Nothing                 -> error ("lexical error at " ++ stateName ++ ": " ++ show (take 10 s))


lTokens :: SubsumesToken t => RE Char t
lTokens =
        lCharacters
    <|> lKeywords
    <|> upcast . Token "BAR" . Just <$> lBar
    <|> upcast . Token "REL-SYMB" . Just <$> lRelSymbs
    <|> upcast . IDLit . Just <$> lName
    <|> upcast . AltIDLit . Just <$> lVar
    <|> upcast . StringLit . Just <$> lStringLit
    <|> upcast . IntLit . Just . read <$> some (psym isDigit)
    where
            lCharacters = foldr ((<|>) . lChar) empty keycharacters
              where lChar c = upcast (Char c) <$ sym c

            lKeywords = foldr ((<|>) . lKeyword) empty keywords
              where lKeyword k  = upcast (Keyword k) <$ string k

            lRelSymbs = (\a xs z -> a : xs ++ [z]) <$>
                          anyOf symcharacters_start <*> 
                          inRange 0 5 (anyOf symcharacters_middle <|> psym isAlpha) <*>
                          anyOf symcharacters_end

              where anyOf = foldr ((<|>) . sym) empty
 
            lStringLit = toString <$ sym '\"' <*> many strChar <* sym '\"'
             where strChar =  sym '\\' *> sym '\"'
                              <|> psym ((/=) '\"')
                   toString inner = case readEither ("\"" ++ inner ++ "\"") of
                      Left _  -> inner
                      Right v -> v

            keycharacters = "()_;,|?!*#-{}>=<[]'"
   
            symcharacters_start = "-~^=:"
            symcharacters_middle = "-~^=>+:"
            symcharacters_end = "^=>+:"
  
            keywords =  --["branches", "pm-args", "pm"
                        --,"trans", "commit","get", "set"] ++ 
                        ["sseq"] ++
                        ["is-terminal", "is-non-terminal"] ++
                        ["is_terminal", "is_non_terminal"] ++
                        ["entity", "terminal", "relation", "RESET-BINDINGS"] ++
                        ["CONTEXT-FREE", "TERMINAL-REFLEXIVE","REFLEXIVE", "REPEATABLE","VALUE-OPERATIONS"] ++ 
                        ["value-constructor"] ++ 
                        ["procedure", "with", "seq-variable", "LONGEST", "SHORTEST", "RANDOM"] ++ 
                        ["|-", "|>"] ++
                        ["INTEGERS", "BOOLEANS", "STRINGS", "CHARACTERS", "VALUES"
                        ,"LISTS", "SETS", "ADTS", "TUPLES", "TYPES", "MAPS", "ATOMS"] ++
                        ["<:", ":>"] ++
                        [prebound_mvar]
                        
lBar = "----" <$ inRange 6 6 (sym '-') <* many (sym '-')
lName = (:) <$> psym isLower <*> many (psym (\c -> isAlphaNum c || c == '-' || c == '_'))
lVar  = merge <$> psym isUpper <*> many (psym (\c -> isAlpha c || isDigit c)) 
                    <*> many (sym '\'')
  where merge s ss ms = s:ss++ms

inRange :: Int -> Int -> RE Char Char -> RE Char String
inRange n m = inRange' 0 n m  
  where inRange' :: Int -> Int -> Int -> RE Char Char -> RE Char String
        inRange' i l u s 
          -- may no longer do more
          | i > u     = empty 
          -- must do more!
          | i < l     = (:) <$> s <*> inRange' (i+1) l u s
          -- may do more, or may stop 
          | otherwise = (:) <$> s <*> inRange' (i+1) l u s
                            <|> pure []
          
