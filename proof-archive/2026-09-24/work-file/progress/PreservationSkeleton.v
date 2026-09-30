Require Import TypeRulesCore.

Scheme wf_mut_ind := Induction for wf Sort Prop
with synth_mut_ind := Induction for synth Sort Prop
with check_mut_ind := Induction for check Sort Prop
with branches_mut_ind := Induction for check_branches Sort Prop
with sub_mut_ind := Induction for sub Sort Prop.

Combined Scheme typing_mut_ind
  from wf_mut_ind, synth_mut_ind, check_mut_ind,
       branches_mut_ind, sub_mut_ind.

Check typing_mut_ind.
