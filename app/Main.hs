{-# LANGUAGE DuplicateRecordFields#-}
{-# LANGUAGE OverloadedStrings #-}

module Main where

import           System.IO
import           Control.Lens            hiding (Iso)
import           Control.Monad.IO.Class
import           Control.Monad.Reader
import           Control.Concurrent.STM
import qualified Data.Aeson              as Aeson
import qualified Data.Aeson.Types        as Aeson
import           Data.List
import qualified Data.Map                as Map
import qualified Data.Text               as T
import qualified Data.Text.Lazy          as TL
import qualified Data.Text.Lazy.Encoding as T
import           Language.LSP.Diagnostics
import           Language.LSP.Server
import           Language.LSP.VFS
import qualified Language.LSP.Types      as LSP
import qualified Language.LSP.Types.Lens as LSP
import           Text.Parsec             hiding (Line)
import           TLS.Computer
import           TLS.Parser
import           TLS.Tokenizer
import           TLS.Types

type ServerState c = ReaderT (TVar (Map.Map LSP.NormalizedUri ParsedFile)) (LspM c)

lineRange :: SourcePos -> LSP.Range
lineRange pos = LSP.Range (LSP.Position (sourceLine pos) 0) (LSP.Position (sourceLine pos) 0)

inRange :: LSP.Position -> LSP.Range -> Bool
inRange pos (LSP.Range b e) = pos >= b && pos < e

updateFile :: LSP.NormalizedUri -> ServerState () ()
updateFile uri = do mvf <- getVirtualFile uri
                    case mvf of
                        Nothing -> pure ()
                        Just vf -> do
                            let text = virtualFileText vf
                                version = virtualFileVersion vf
                                tokenized = tokenizeFile "" text
                            map <- ask
                            case tokenized of
                                Right (TokenizeError pos c) -> do
                                    let line = lineRange pos
                                        message = T.pack $ "Unexpected character " ++ show c ++ " at " ++ show pos
                                        diag = LSP.Diagnostic line (Just LSP.DsError) Nothing (Just "tls-tokenizer") message Nothing Nothing
                                    publishDiagnostics 1 uri (Just version) $ partitionBySource [diag]
                                Left tokens ->  do
                                    flushDiagnosticsBySource 100 (Just "tls-tokenizer")
                                    let parseResult = parse parseFile "" tokens
                                    case parseResult of
                                       Left error -> do
                                           let line = lineRange $ errorPos error
                                               message = T.pack $ show error
                                               diag = LSP.Diagnostic line (Just LSP.DsError) Nothing (Just "tls-parser") message Nothing Nothing
                                           publishDiagnostics 1 uri (Just version) $ partitionBySource [diag]
                                       Right theorems -> do flushDiagnosticsBySource 100 (Just "tls-parser")
                                                            flushDiagnosticsBySource 100 (Just "TNT-prover")
                                                            let (diags, computeds) = computeTheorems theorems
                                                            publishDiagnostics 100 uri (Just version) $ partitionBySource diags
                                                            liftIO $ atomically $ modifyTVar' map (Map.insert uri computeds)

isInEmptyLine :: [Line] -> LSP.Position -> Bool
isInEmptyLine [] _ = False
isInEmptyLine ((Line Nothing _ _):lines) pos = isInEmptyLine lines pos
isInEmptyLine ((Line (Just range) _ empty):lines) pos = (inRange pos range && empty) || isInEmptyLine lines pos


isInTheorem :: ComputedTheorem -> LSP.Position -> Bool
isInTheorem (ComputedTheorem Nothing Nothing) pos = False
isInTheorem (ComputedTheorem (Just range) Nothing) pos = False
isInTheorem (ComputedTheorem (Just range) (Just lines)) pos = inRange pos range && isInEmptyLine lines pos

checkAutocomp :: ParsedFile -> LSP.Position -> Bool
checkAutocomp [] _ = False
checkAutocomp (th:ths) pos= isInTheorem th pos || checkAutocomp ths pos

instrToAutocompletion :: String -> LSP.CompletionItem
instrToAutocompletion instr = LSP.CompletionItem { LSP._label = T.pack instr
                                                 , LSP._kind = Just LSP.CiMethod
                                                 , LSP._tags = Nothing
                                                 , LSP._detail = Nothing
                                                 , LSP._documentation = Nothing
                                                 , LSP._deprecated = Nothing
                                                 , LSP._preselect = Nothing
                                                 , LSP._sortText = Nothing
                                                 , LSP._filterText = Nothing
                                                 , LSP._insertText = Just $ T.pack instr
                                                 , LSP._insertTextFormat = Nothing
                                                 , LSP._insertTextMode = Nothing
                                                 , LSP._textEdit = Nothing
                                                 , LSP._additionalTextEdits = Nothing
                                                 , LSP._commitCharacters = Nothing
                                                 , LSP._command = Nothing
                                                 , LSP._xdata = Nothing
                                                 }

specialAutocompletion :: T.Text  -> T.Text -> LSP.CompletionItem
specialAutocompletion name symbol = LSP.CompletionItem { LSP._label = name
                                                       , LSP._kind = Just LSP.CiText
                                                       , LSP._tags = Nothing
                                                       , LSP._detail = Nothing
                                                       , LSP._documentation = Nothing
                                                       , LSP._deprecated = Nothing
                                                       , LSP._preselect = Nothing
                                                       , LSP._sortText = Nothing
                                                       , LSP._filterText = Nothing
                                                       , LSP._insertText = Just symbol
                                                       , LSP._insertTextFormat = Nothing
                                                       , LSP._insertTextMode = Nothing
                                                       , LSP._textEdit = Nothing
                                                       , LSP._additionalTextEdits = Nothing
                                                       , LSP._commitCharacters = Nothing
                                                       , LSP._command = Nothing
                                                       , LSP._xdata = Nothing
                                                       }

handlers :: Handlers (ServerState ())
handlers = mconcat
  [ notificationHandler LSP.SInitialized $ \msg -> do
      pure ()
  , notificationHandler LSP.STextDocumentDidOpen $ \msg -> do
      let uri = LSP.toNormalizedUri $ msg ^. LSP.params . LSP.textDocument . LSP.uri
      map <- ask
      liftIO $ atomically $ modifyTVar' map (Map.insert uri [])
      updateFile uri
  , notificationHandler LSP.STextDocumentDidChange $ \msg -> do
      let uri = LSP.toNormalizedUri $ msg ^. LSP.params . LSP.textDocument . LSP.uri
      updateFile uri
  , requestHandler LSP.STextDocumentCompletion $ \req responder -> do
      let uri = LSP.toNormalizedUri $ req ^. LSP.params . LSP.textDocument . LSP.uri
      let pos = req ^. LSP.params . LSP.position
      map <- ask
      map <- liftIO $ readTVarIO map
      let computed = Map.lookup uri map
      let specials = LSP.List [specialAutocompletion "forall" "∀",specialAutocompletion "exist" "∃",specialAutocompletion "implie" "⊂"]
      let rsp = case computed of
                    Nothing -> specials
                    Just computed -> if checkAutocomp computed pos
                                     then LSP.List $ instrToAutocompletion <$> instrs
                                     else specials
      responder (Right $ LSP.InL rsp)
  , requestHandler (LSP.SCustomMethod "getTheorems") $ \req responder -> do
      let result = Aeson.parse Aeson.parseJSON $ req ^. LSP.params :: Aeson.Result [T.Text]
      case result of
          Aeson.Error str -> responder (Left $ LSP.ResponseError LSP.InternalError (T.pack str) Nothing)
          Aeson.Success str -> do
            let uri = LSP.toNormalizedUri (LSP.Uri $ head str)
            map <- ask
            map' <- liftIO $ readTVarIO map
            let computeds = Map.lookup uri map'
            responder (Right $ Aeson.toJSON computeds)
  ]

main :: IO Int
main = do initState <- newTVarIO Map.empty
          runServer $ ServerDefinition
            { onConfigurationChange = const $ pure $ Right ()
            , defaultConfig = ()
            , staticHandlers = handlers
            , interpretHandler = \(env,st) -> Iso (runLspT env . flip runReaderT st) liftIO
            , doInitialize = \env _req -> pure $ Right (env, initState)
            , options = lspOptions
            }

syncOptions :: LSP.TextDocumentSyncOptions
syncOptions = LSP.TextDocumentSyncOptions
  { LSP._openClose         = Just True
  , LSP._change            = Just LSP.TdSyncIncremental
  , LSP._willSave          = Just False
  , LSP._willSaveWaitUntil = Just False
  , LSP._save              = Just $ LSP.InR $ LSP.SaveOptions $ Just False
  }

lspOptions :: Options
lspOptions = defaultOptions
  { textDocumentSync = Just syncOptions
  }