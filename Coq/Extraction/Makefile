# Haskell EDSL path
EDSL_PATH = ./contracts-haskell/src/Contracts

# Contract extraction
CONTRACT_TARGET = Contract.hs
CONTRACT_EXTRACTED = ContractExtracted.hs
CONTRACT_HEADER = Header.hs
CONTRACT_SED_SCRIPT = '/^data Var =/,$$'p

# Contract translation extraction
TRANSLATION_TARGET = ContractTranslation.hs
TRANSLATION_EXTRACTED = ContractTranslationExtracted.hs
TRANSLATION_HEADER = TranslationHeader.hs
TRANSLATION_SED_SCRIPT = '/^data ILTExpr =/,$$'p

COQ_FILE = Extraction.v

default: $(CONTRACT_TARGET) $(TRANSLATION_TARGET)
	cd ./contracts-haskell/ && stack build

Contract.hs:
	cp $(EDSL_PATH)/$(CONTRACT_HEADER)  $(EDSL_PATH)/$(CONTRACT_TARGET)
	sed -n $(CONTRACT_SED_SCRIPT)  $(EDSL_PATH)/$(CONTRACT_EXTRACTED) >>  $(EDSL_PATH)/$(CONTRACT_TARGET)

ContractTranslation.hs:
	cp  $(EDSL_PATH)/$(TRANSLATION_HEADER)  $(EDSL_PATH)/$(TRANSLATION_TARGET)
	sed -n $(TRANSLATION_SED_SCRIPT)  $(EDSL_PATH)/$(TRANSLATION_EXTRACTED) >>  $(EDSL_PATH)/$(TRANSLATION_TARGET)


clean:
	rm -rf *~
	rm -f $(EDSL_PATH)/$(CONTRACT_TARGET) $(EDSL_PATH)/$(CONTRACT_EXTRACTED)
	rm -f  $(EDSL_PATH)/$(TRANSLATION_TARGET)  $(EDSL_PATH)/$(TRANSLATION_EXTRACTED)

test: default
	stack ghc Examples/*.hs
