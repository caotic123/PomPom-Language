COQC ?= rocq compile
COQDEP ?= rocq dep
COQFLAGS ?= -Q . ''

OPEN_SIGNATURE_SOURCES := OpenSignaturesSyntax.v OpenSignaturesAlpha.v OpenSignaturesCore.v \
 OpenSignaturesBinding.v OpenSignaturesSubstitution.v OpenSignaturesProgress.v OpenSignaturesDerivedTyping.v OpenSignaturesElaboration.v OpenSignaturesDataTyping.v OpenSignaturesRowTyping.v OpenSignaturesCaseTyping.v OpenSignaturesElaborationSoundness.v OpenSignaturesCoercionTyping.v OpenSignaturesTransport.v OpenSignaturesSubtypingSoundness.v OpenSignaturesExamples.v OpenSignaturesExampleTyping.v nameless/DBSyntax.v nameless/DBCore.v nameless/DBParallelBase.v nameless/DBInversion.v nameless/DBParallel.v nameless/DBEta.v nameless/DBCommutation.v nameless/DBReduction.v nameless/DBConfluence.v OpenSignaturesEncoding.v OpenSignaturesEncodingReduction.v OpenSignaturesEncodingFreshness.v OpenSignaturesEncodingReflection.v OpenSignaturesConfluence.v OpenSignaturesLabels.v OpenSignaturesObservers.v OpenSignaturesContexts.v OpenSignaturesCanonical.v OpenSignaturesConstructorInversion.v OpenSignaturesDeadTyping.v OpenSignaturesNamedCanonical.v OpenSignaturesEndless.v OpenSignaturesContextInclusion.v OpenSignaturesClosedSubstitution.v nameless/DBTyping.v nameless/DBWeakening.v nameless/DBSubstitution.v nameless/DBDerivedTyping.v OpenSignaturesEncodingTyping.v OpenSignaturesDecoding.v OpenSignaturesTypingReflection.v OpenSignaturesTypingEncoding.v nameless/DBContexts.v nameless/DBGeneration.v nameless/DBBeta.v OpenSignaturesBeta.v nameless/DBClosePayload.v OpenSignaturesPayloadInversion.v nameless/DBInductionBeta.v OpenSignaturesInductionBeta.v nameless/DBConstructorGeneration.v nameless/DBDescriptionBeta.v nameless/DBMuBeta.v nameless/DBEnumBeta.v nameless/DBRootPreservation.v nameless/DBPreservation.v OpenSignaturesPreservation.v OpenSignaturesComputationPreservation.v nameless/DBOperatorFormations.v nameless/DBFullPreservation.v nameless/DBComputationPreservation.v nameless/DBParallelPreservation.v nameless/DBActiveParallel.v nameless/DBActivePostponement.v nameless/DBNormalization.v nameless/DBComputationSubstitution.v nameless/DBReducibility.v nameless/DBFullReductionStructure.v nameless/DBFullNormalForms.v nameless/DBFullReducibility.v nameless/DBSemanticTypes.v nameless/DBUniverseModel.v nameless/DBPositiveCandidates.v nameless/DBIndexedCandidates.v nameless/DBDescriptionCandidates.v nameless/DBEnumCandidates.v nameless/DBDescriptionModel.v nameless/DBSmallTypeModel.v nameless/DBCalculusModel.v nameless/DBSemanticGeneration.v nameless/DBHeadExpansion.v nameless/DBInterpretationComputability.v nameless/DBAllComputability.v nameless/DBHypsComputability.v nameless/DBSaturatedElimination.v nameless/DBCloseCaseComputability.v nameless/DBEnumComputability.v nameless/DBSwitchComputability.v nameless/DBEliminatorCandidates.v nameless/DBBetaExpansion.v nameless/DBIndComputability.v nameless/DBDataComputability.v nameless/DBCloseIndComputability.v nameless/DBSemanticBinders.v nameless/DBSemanticJudgments.v nameless/DBSemanticVariance.v nameless/DBSemanticSubstitution.v nameless/DBSemanticFamilies.v nameless/DBSemanticData.v nameless/DBSemanticCloseMethods.v nameless/DBSemanticOperators.v nameless/DBSemanticPrimitiveRules.v nameless/DBSemanticCloseCase.v nameless/DBSemanticFundamental.v OpenSignaturesNormalization.v nameless/DBEtaTyping.v nameless/DBEtaSafety.v nameless/DBEtaPostponement.v nameless/DBDescriptionViews.v nameless/DBCumulativeTyping.v nameless/DBTypedPiViews.v nameless/DBTypeComparison.v nameless/DBEtaPrincipal.v nameless/DBEtaPolymorphism.v OpenSignaturesEtaPolymorphism.v OpenSignaturesObservations.v OpenSignaturesObservationalLaws.v OpenSignaturesObservationalTypes.v OpenSignaturesRowCoherence.v OpenSignaturesRowViews.v OpenSignaturesDescriptionCoherence.v OpenSignaturesTheorems.v OpenSignatures.v
OPEN_SIGNATURE_OBJECTS := $(OPEN_SIGNATURE_SOURCES:.v=.vo)

ANNOTATED_SOURCES := annotated/ASyntax.v annotated/ABinding.v annotated/AErase.v \
 annotated/AErasure.v annotated/AFreshness.v annotated/AEta.v annotated/ATyping.v \
 annotated/AWeakening.v annotated/ASubstitution.v annotated/AComparison.v \
 annotated/AGeneration.v annotated/ABeta.v annotated/AFunctions.v annotated/ARegression.v
ANNOTATED_OBJECTS := $(ANNOTATED_SOURCES:.v=.vo)

SOURCES := $(OPEN_SIGNATURE_SOURCES) $(ANNOTATED_SOURCES) annotated/AAudit.v OpenSignaturesBindingTests.v OpenSignaturesEtaRegression.v

.PHONY: all open-signatures annotated-core audit-annotated-core audit-open-signatures check-bindings check-eta-cumulativity check-eta-polymorphism
all: open-signatures annotated-core

open-signatures: $(OPEN_SIGNATURE_OBJECTS)

annotated-core: $(ANNOTATED_OBJECTS)

audit-annotated-core: annotated-core
	$(COQC) $(COQFLAGS) annotated/AAudit.v

check-bindings: OpenSignaturesBindingTests.vo

check-eta-cumulativity: OpenSignaturesEtaRegression.vo

check-eta-polymorphism: OpenSignaturesEtaPolymorphism.vo

audit-open-signatures: open-signatures
	$(COQC) $(COQFLAGS) OpenSignaturesAudit.v

%.vo: %.v
	$(COQC) $(COQFLAGS) $<

.depend: $(SOURCES) OpenSignaturesAudit.v Makefile
	$(COQDEP) $(COQFLAGS) $(SOURCES) OpenSignaturesAudit.v > $@

include .depend
