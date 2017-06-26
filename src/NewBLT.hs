{-# LANGUAGE DeriveDataTypeable #-}
-- | new BLT : a more modular approach 
module Main where

import Options.Applicative 
import System.FilePath

data Input = FileInput FilePath | StdIn

fileInput :: Parser Input
fileInput = FileInput <$> strOption
  ( long "file"
    <> short 'f'
    <> metavar "FILENAME"
    <> help "Source .bpl file"
  )

stdInput :: Parser Input
stdInput = flag' StdIn
  ( long "stdin"
    <> help "Read from stdin" 
  )

input = fileInput <|> stdInput

