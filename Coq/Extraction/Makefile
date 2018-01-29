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

Contract.hs:
	cp $(CONTRACT_HEADER) $(CONTRACT_TARGET)
	sed -n $(CONTRACT_SED_SCRIPT) $(CONTRACT_EXTRACTED) >> $(CONTRACT_TARGET)

ContractTranslation.hs:
	cp $(TRANSLATION_HEADER) $(TRANSLATION_TARGET)
	sed -n $(TRANSLATION_SED_SCRIPT) $(TRANSLATION_EXTRACTED) >> $(TRANSLATION_TARGET)


clean:
	rm -rf *~
	rm -f $(CONTRACT_TARGET) $(CONTRACT_EXTRACTED)
	rm -f $(TRANSLATION_TARGET) $(TRANSLATION_EXTRACTED)
	rm -rf $(COQ_FILE:.v=.vo) $(COQ_FILE:.v=.glob)

test: default
	ghc -fno-code -no-hs-main Examples/*.hs
