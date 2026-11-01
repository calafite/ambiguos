parseAtomicExpression :: Parser Expression
parseAtomicExpression = do
  nextToken <- peekToken
  case nextToken of
    Just TokenKeywordType -> do
      _ <- consumeToken
      pure Universe
    Just TokenKeywordId -> do
      _ <- consumeToken
      pure Identity
    Just TokenKeywordRefl -> do
      _ <- consumeToken
      pure Reflexivity
    Just TokenKeywordJ -> do
      _ <- consumeToken
      pure J
    Just (TokenIdentifier ident) -> do
      _ <- consumeToken
      pure (Variable ident)
    Just TokenLeftParen -> do
      _ <- consumeToken
      expr <- expressionParser
      expectToken TokenRightParen "')'"
      pure expr
    Just other -> Parser $ \_ -> Left (UnexpectedToken other)
    Nothing    -> Parser $ \_ -> Left UnexpectedEndOfInput
