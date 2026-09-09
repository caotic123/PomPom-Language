COQC ?= coqc
COQDEP ?= coqdep
COQFLAGS ?= -Q . ''

OPEN_SIGNATURE_SOURCES := OpenSignaturesSyntax.v OpenSignaturesCore.v \
 OpenSignaturesElaboration.v OpenSignaturesExamples.v OpenSignaturesTheorems.v OpenSignatures.v
OPEN_SIGNATURE_OBJECTS := $(OPEN_SIGNATURE_SOURCES:.v=.vo)

SOURCES := $(OPEN_SIGNATURE_SOURCES) TypeRulesCore.v Progress.v ConversionInversion.v TypingSubstitution.v PayloadInversion.v Preservation.v PreservationEval.v \
 PreservationType.v Normalization.v CanonicalFormsSig.v Consistency.v \
 ConsistencyEnum.v ConsistencyEmptySig.v AgainstSound.v TypeRules.v \
 SignatureLemmas.v ErasureCounterexample.v SignatureConversion.v \
 SignatureInstances.v SignatureTagTransport.v SignatureProgressReduction.v
OBJECTS := $(SOURCES:.v=.vo)

.PHONY: all audit check open-signatures audit-open-signatures
all: $(OBJECTS)

open-signatures: $(OPEN_SIGNATURE_OBJECTS)

audit-open-signatures: open-signatures
	$(COQC) $(COQFLAGS) OpenSignaturesAudit.v

audit: all
	$(COQC) $(COQFLAGS) MetatheoryAudit.v

check: audit test_check.vo test_size.vo

%.vo: %.v
	$(COQC) $(COQFLAGS) $<

.depend: $(SOURCES) MetatheoryAudit.v OpenSignaturesAudit.v test_check.v test_size.v Makefile
	$(COQDEP) $(COQFLAGS) $(SOURCES) MetatheoryAudit.v OpenSignaturesAudit.v test_check.v test_size.v > $@

include .depend
