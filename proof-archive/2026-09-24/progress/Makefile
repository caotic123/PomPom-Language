COQC ?= rocq compile
COQDEP ?= rocq dep
COQFLAGS ?= -Q . ''

OPEN_SIGNATURE_SOURCES := OpenSignaturesSyntax.v OpenSignaturesCore.v \
 OpenSignaturesElaboration.v OpenSignaturesExamples.v OpenSignaturesTheorems.v OpenSignatures.v
OPEN_SIGNATURE_OBJECTS := $(OPEN_SIGNATURE_SOURCES:.v=.vo)

OPEN_SIGNATURE_PROGRESS_SOURCES := OpenSignaturesProgress.v
OPEN_SIGNATURE_PROGRESS_OBJECTS := $(OPEN_SIGNATURE_PROGRESS_SOURCES:.v=.vo)

SOURCES := $(OPEN_SIGNATURE_SOURCES) $(OPEN_SIGNATURE_PROGRESS_SOURCES)

.PHONY: all open-signatures open-signatures-progress audit-open-signatures
all: open-signatures

open-signatures: $(OPEN_SIGNATURE_OBJECTS)

open-signatures-progress: open-signatures $(OPEN_SIGNATURE_PROGRESS_OBJECTS)

audit-open-signatures: open-signatures
	$(COQC) $(COQFLAGS) OpenSignaturesAudit.v

%.vo: %.v
	$(COQC) $(COQFLAGS) $<

.depend: $(SOURCES) OpenSignaturesAudit.v Makefile
	$(COQDEP) $(COQFLAGS) $(SOURCES) OpenSignaturesAudit.v > $@

include .depend
