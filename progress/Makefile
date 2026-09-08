COQC ?= coqc
COQDEP ?= coqdep
COQFLAGS ?= -Q . ''

SOURCES := TypeRulesCore.v Progress.v ConversionInversion.v TypingSubstitution.v PayloadInversion.v Preservation.v PreservationEval.v \
 PreservationType.v Normalization.v CanonicalFormsSig.v Consistency.v \
 ConsistencyEnum.v ConsistencyEmptySig.v AgainstSound.v TypeRules.v \
 SignatureLemmas.v ErasureCounterexample.v SignatureConversion.v \
 SignatureInstances.v SignatureTagTransport.v SignatureProgressReduction.v
OBJECTS := $(SOURCES:.v=.vo)

.PHONY: all audit check
all: $(OBJECTS)

audit: all
	$(COQC) $(COQFLAGS) MetatheoryAudit.v

check: audit test_check.vo test_size.vo

%.vo: %.v
	$(COQC) $(COQFLAGS) $<

.depend: $(SOURCES) MetatheoryAudit.v test_check.v test_size.v Makefile
	$(COQDEP) $(COQFLAGS) $(SOURCES) MetatheoryAudit.v test_check.v test_size.v > $@

include .depend
