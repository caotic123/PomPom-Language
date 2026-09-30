COQC ?= rocq compile
COQDEP ?= rocq dep
COQFLAGS ?= -Q . ''

OPEN_SIGNATURE_SOURCES := OpenSignaturesSyntax.v OpenSignaturesAlpha.v OpenSignaturesCore.v \
 OpenSignaturesBinding.v OpenSignaturesSubstitution.v OpenSignaturesProgress.v OpenSignaturesDerivedTyping.v OpenSignaturesElaboration.v OpenSignaturesDataTyping.v OpenSignaturesRowTyping.v OpenSignaturesCaseTyping.v OpenSignaturesElaborationSoundness.v OpenSignaturesCoercionTyping.v OpenSignaturesTransport.v OpenSignaturesSubtypingSoundness.v OpenSignaturesExamples.v OpenSignaturesExampleTyping.v nameless/DBSyntax.v nameless/DBCore.v nameless/DBParallelBase.v nameless/DBInversion.v nameless/DBParallel.v nameless/DBEta.v nameless/DBCommutation.v nameless/DBReduction.v nameless/DBConfluence.v OpenSignaturesEncoding.v OpenSignaturesEncodingReduction.v OpenSignaturesEncodingFreshness.v OpenSignaturesEncodingReflection.v OpenSignaturesConfluence.v OpenSignaturesLabels.v OpenSignaturesObservers.v OpenSignaturesContexts.v OpenSignaturesCanonical.v OpenSignaturesConstructorInversion.v OpenSignaturesDeadTyping.v OpenSignaturesNamedCanonical.v OpenSignaturesEndless.v OpenSignaturesContextInclusion.v OpenSignaturesClosedSubstitution.v nameless/DBTyping.v nameless/DBWeakening.v nameless/DBSubstitution.v nameless/DBDerivedTyping.v OpenSignaturesEncodingTyping.v OpenSignaturesDecoding.v OpenSignaturesTypingReflection.v OpenSignaturesTypingEncoding.v nameless/DBContexts.v nameless/DBGeneration.v nameless/DBBeta.v OpenSignaturesBeta.v nameless/DBClosePayload.v OpenSignaturesPayloadInversion.v OpenSignaturesTheorems.v OpenSignatures.v
OPEN_SIGNATURE_OBJECTS := $(OPEN_SIGNATURE_SOURCES:.v=.vo)

SOURCES := $(OPEN_SIGNATURE_SOURCES) OpenSignaturesBindingTests.v OpenSignaturesEtaCounterexample.v

.PHONY: all open-signatures audit-open-signatures check-bindings check-eta-counterexample
all: open-signatures

open-signatures: $(OPEN_SIGNATURE_OBJECTS)

check-bindings: OpenSignaturesBindingTests.vo

check-eta-counterexample: OpenSignaturesEtaCounterexample.vo

audit-open-signatures: open-signatures
	$(COQC) $(COQFLAGS) OpenSignaturesAudit.v

%.vo: %.v
	$(COQC) $(COQFLAGS) $<

.depend: $(SOURCES) OpenSignaturesAudit.v Makefile
	$(COQDEP) $(COQFLAGS) $(SOURCES) OpenSignaturesAudit.v > $@

include .depend
