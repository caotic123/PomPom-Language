(* Operational semantics and declarative core typing for the revised sketch.
   No source subtyping, enabled-label lists, or raw named case lists occur here.
   Conversion is beta/eta plus typed-operator computation and full congruence.
   It has NO equation unfolding a close type or identifying its diagonal
   judgmentally with the separately retained EID reference fixed point. *)
From Stdlib Require Import List Arith String.
Require Export ProofDB.DBSyntax.
Import ListNotations.
Set Implicit Arguments.

Definition root_step (t : term) : option term :=
  match t with
  | TApp (TLam b) a => Some (subst a 0 b)
  | TFst (TPair a b) => Some a
  | TSnd (TPair a b) => Some b
  | TEPi k TNilE P => Some TUnitT
  | TEPi k (TConsE tag E) P =>
      Some (product (TApp P TEZero)
        (TEPi k E (TLam (TApp (lift 1 0 P) (TESucc (TVar 0))))))
  | TSwitch k (TConsE tag E) P (TPair p ps) TEZero => Some p
  | TSwitch k (TConsE tag E) P (TPair p ps) (TESucc n) =>
      Some (TSwitch k E (TLam (TApp (lift 1 0 P) (TESucc (TVar 0)))) ps n)
  | TInterp IT (TIVar i) X => Some (TApp X i)
  | TInterp IT TI1 X => Some TUnitT
  | TInterp IT TIBot X => Some Bot
  | TInterp IT (TIProd A B) X =>
      Some (product (TInterp IT A X) (TInterp IT B X))
  | TInterp IT (TIPi A D) X =>
      Some (TPi A (TInterp (lift 1 0 IT) (TApp (lift 1 0 D) (TVar 0)) (lift 1 0 X)))
  | TInterp IT (TISig A D) X =>
      Some (TSigma A (TInterp (lift 1 0 IT) (TApp (lift 1 0 D) (TVar 0)) (lift 1 0 X)))
  | TInterp IT (TIChoice E D) X =>
      Some (TSigma (TEnumT E)
        (TInterp (lift 1 0 IT) (TApp (lift 1 0 D) (TVar 0)) (lift 1 0 X)))
  | TIAll IT (TIVar i) X x P => Some (TApp P (TPair i x))
  | TIAll IT TI1 X TUnit P => Some TUnitT
  | TIAll IT TIBot X x P => Some TUnitT
  | TIAll IT (TIProd A B) X (TPair a b) P =>
      Some (product (TIAll IT A X a P) (TIAll IT B X b P))
  | TIAll IT (TIPi A D) X f P =>
      Some (TPi A (TIAll (lift 1 0 IT) (TApp (lift 1 0 D) (TVar 0))
        (lift 1 0 X) (TApp (lift 1 0 f) (TVar 0)) (lift 1 0 P)))
  | TIAll IT (TISig A D) X (TPair a x) P =>
      Some (TIAll IT (TApp D a) X x P)
  | TIAll IT (TIChoice E D) X (TPair e x) P =>
      Some (TIAll IT (TApp D e) X x P)
  | THyps IT (TIVar i) X P h x => Some (TApp (TApp h i) x)
  | THyps IT TI1 X P h TUnit => Some TUnit
  | THyps IT TIBot X P h x => Some TUnit
  | THyps IT (TIProd A B) X P h (TPair a b) =>
      Some (TPair (THyps IT A X P h a) (THyps IT B X P h b))
  | THyps IT (TIPi A D) X P h f =>
      Some (TLam (THyps (lift 1 0 IT) (TApp (lift 1 0 D) (TVar 0))
        (lift 1 0 X) (lift 1 0 P) (lift 1 0 h)
        (TApp (lift 1 0 f) (TVar 0))))
  | THyps IT (TISig A D) X P h (TPair a x) =>
      Some (THyps IT (TApp D a) X P h x)
  | THyps IT (TIChoice E D) X P h (TPair e x) =>
      Some (THyps IT (TApp D e) X P h x)
  | TInd IT D P st i (TIn xs) =>
      Some (TApp (TApp (TApp st i) xs)
        (THyps IT (TApp D i) (TMuI IT D) P
          (TLam (TLam (TInd (lift 2 0 IT) (lift 2 0 D) (lift 2 0 P)
            (lift 2 0 st) (TVar 1) (TVar 0)))) xs))
  | TCloseCase k IT F G i Q b (TIn xs) => Some (TApp b xs)
  | TCloseInd IT G P st F i (TIn xs) =>
      Some (TApp (TApp (TApp (TApp st F) i) xs)
        (THyps IT (TApp F i) (carrier IT G) (diagonal_motive G P)
          (TLam (TLam (TCloseInd (lift 2 0 IT) (lift 2 0 G)
            (lift 2 0 P) (lift 2 0 st) (lift 2 0 G)
            (TVar 1) (TVar 0)))) xs))
  | _ => None
  end.

Inductive step : term -> term -> Prop :=
| st_root : forall t u, root_step t = Some u -> step t u
| st_TApp_f : forall f a f', step f f' ->
    step (TApp f a) (TApp f' a)
| st_TPair_a : forall a b a', step a a' ->
    step (TPair a b) (TPair a' b)
| st_TPair_b : forall a b b', step b b' ->
    step (TPair a b) (TPair a b')
| st_TFst_p : forall p p', step p p' ->
    step (TFst p) (TFst p')
| st_TSnd_p : forall p p', step p p' ->
    step (TSnd p) (TSnd p')
| st_TESucc_n : forall n n', step n n' ->
    step (TESucc n) (TESucc n')
| st_TEPi_E : forall k E P E', step E E' ->
    step (TEPi k E P) (TEPi k E' P)
| st_TSwitch_E : forall k E P p e E', step E E' ->
    step (TSwitch k E P p e) (TSwitch k E' P p e)
| st_TSwitch_p : forall k E P p e p', step p p' ->
    step (TSwitch k E P p e) (TSwitch k E P p' e)
| st_TSwitch_e : forall k E P p e e', step e e' ->
    step (TSwitch k E P p e) (TSwitch k E P p e')
| st_TInterp_D : forall IT D X D', step D D' ->
    step (TInterp IT D X) (TInterp IT D' X)
| st_TIn_x : forall x x', step x x' ->
    step (TIn x) (TIn x')
| st_TInd_x : forall IT D P s i x x', step x x' ->
    step (TInd IT D P s i x) (TInd IT D P s i x')
| st_TIAll_D : forall IT D X x P D', step D D' ->
    step (TIAll IT D X x P) (TIAll IT D' X x P)
| st_TIAll_x : forall IT D X x P x', step x x' ->
    step (TIAll IT D X x P) (TIAll IT D X x' P)
| st_THyps_D : forall IT D X P h x D', step D D' ->
    step (THyps IT D X P h x) (THyps IT D' X P h x)
| st_THyps_x : forall IT D X P h x x', step x x' ->
    step (THyps IT D X P h x) (THyps IT D X P h x')
| st_TCloseCase_x : forall k IT F G i Q b x x', step x x' ->
    step (TCloseCase k IT F G i Q b x) (TCloseCase k IT F G i Q b x')
| st_TCloseInd_x : forall IT G P s F i x x', step x x' ->
    step (TCloseInd IT G P s F i x) (TCloseInd IT G P s F i x').

Inductive eval : term -> term -> Prop :=
| ev_refl : forall t, eval t t
| ev_step : forall t u v, step t u -> eval u v -> eval t v.

(* Full compatible beta/eta reduction for normalization and confluence
   statements. Unlike [step], it also reduces under binders and in type
   arguments. There is no close-type unfolding rule. *)
Inductive reduction : term -> term -> Prop :=
| red_root : forall t u, root_step t = Some u -> reduction t u
| red_eta : forall f, reduction (TLam (TApp (lift 1 0 f) (TVar 0))) f
| red_TPi_A : forall A B A', reduction A A' ->
    reduction (TPi A B) (TPi A' B)
| red_TPi_B : forall A B B', reduction B B' ->
    reduction (TPi A B) (TPi A B')
| red_TLam_b : forall b b', reduction b b' ->
    reduction (TLam b) (TLam b')
| red_TApp_f : forall f a f', reduction f f' ->
    reduction (TApp f a) (TApp f' a)
| red_TApp_a : forall f a a', reduction a a' ->
    reduction (TApp f a) (TApp f a')
| red_TSigma_A : forall A B A', reduction A A' ->
    reduction (TSigma A B) (TSigma A' B)
| red_TSigma_B : forall A B B', reduction B B' ->
    reduction (TSigma A B) (TSigma A B')
| red_TPair_a : forall a b a', reduction a a' ->
    reduction (TPair a b) (TPair a' b)
| red_TPair_b : forall a b b', reduction b b' ->
    reduction (TPair a b) (TPair a b')
| red_TFst_p : forall p p', reduction p p' ->
    reduction (TFst p) (TFst p')
| red_TSnd_p : forall p p', reduction p p' ->
    reduction (TSnd p) (TSnd p')
| red_TConsE_tag : forall tag E tag', reduction tag tag' ->
    reduction (TConsE tag E) (TConsE tag' E)
| red_TConsE_E : forall tag E E', reduction E E' ->
    reduction (TConsE tag E) (TConsE tag E')
| red_TEnumT_E : forall E E', reduction E E' ->
    reduction (TEnumT E) (TEnumT E')
| red_TESucc_n : forall n n', reduction n n' ->
    reduction (TESucc n) (TESucc n')
| red_TEPi_E : forall k E P E', reduction E E' ->
    reduction (TEPi k E P) (TEPi k E' P)
| red_TEPi_P : forall k E P P', reduction P P' ->
    reduction (TEPi k E P) (TEPi k E P')
| red_TSwitch_E : forall k E P p e E', reduction E E' ->
    reduction (TSwitch k E P p e) (TSwitch k E' P p e)
| red_TSwitch_P : forall k E P p e P', reduction P P' ->
    reduction (TSwitch k E P p e) (TSwitch k E P' p e)
| red_TSwitch_p : forall k E P p e p', reduction p p' ->
    reduction (TSwitch k E P p e) (TSwitch k E P p' e)
| red_TSwitch_e : forall k E P p e e', reduction e e' ->
    reduction (TSwitch k E P p e) (TSwitch k E P p e')
| red_TIDesc_IT : forall IT IT', reduction IT IT' ->
    reduction (TIDesc IT) (TIDesc IT')
| red_TIVar_i : forall i i', reduction i i' ->
    reduction (TIVar i) (TIVar i')
| red_TIProd_A : forall A B A', reduction A A' ->
    reduction (TIProd A B) (TIProd A' B)
| red_TIProd_B : forall A B B', reduction B B' ->
    reduction (TIProd A B) (TIProd A B')
| red_TIPi_A : forall A D A', reduction A A' ->
    reduction (TIPi A D) (TIPi A' D)
| red_TIPi_D : forall A D D', reduction D D' ->
    reduction (TIPi A D) (TIPi A D')
| red_TISig_A : forall A D A', reduction A A' ->
    reduction (TISig A D) (TISig A' D)
| red_TISig_D : forall A D D', reduction D D' ->
    reduction (TISig A D) (TISig A D')
| red_TIChoice_E : forall E D E', reduction E E' ->
    reduction (TIChoice E D) (TIChoice E' D)
| red_TIChoice_D : forall E D D', reduction D D' ->
    reduction (TIChoice E D) (TIChoice E D')
| red_TInterp_IT : forall IT D X IT', reduction IT IT' ->
    reduction (TInterp IT D X) (TInterp IT' D X)
| red_TInterp_D : forall IT D X D', reduction D D' ->
    reduction (TInterp IT D X) (TInterp IT D' X)
| red_TInterp_X : forall IT D X X', reduction X X' ->
    reduction (TInterp IT D X) (TInterp IT D X')
| red_TMuI_IT : forall IT D IT', reduction IT IT' ->
    reduction (TMuI IT D) (TMuI IT' D)
| red_TMuI_D : forall IT D D', reduction D D' ->
    reduction (TMuI IT D) (TMuI IT D')
| red_TIn_x : forall x x', reduction x x' ->
    reduction (TIn x) (TIn x')
| red_TInd_IT : forall IT D P s i x IT', reduction IT IT' ->
    reduction (TInd IT D P s i x) (TInd IT' D P s i x)
| red_TInd_D : forall IT D P s i x D', reduction D D' ->
    reduction (TInd IT D P s i x) (TInd IT D' P s i x)
| red_TInd_P : forall IT D P s i x P', reduction P P' ->
    reduction (TInd IT D P s i x) (TInd IT D P' s i x)
| red_TInd_s : forall IT D P s i x s', reduction s s' ->
    reduction (TInd IT D P s i x) (TInd IT D P s' i x)
| red_TInd_i : forall IT D P s i x i', reduction i i' ->
    reduction (TInd IT D P s i x) (TInd IT D P s i' x)
| red_TInd_x : forall IT D P s i x x', reduction x x' ->
    reduction (TInd IT D P s i x) (TInd IT D P s i x')
| red_TIAll_IT : forall IT D X x P IT', reduction IT IT' ->
    reduction (TIAll IT D X x P) (TIAll IT' D X x P)
| red_TIAll_D : forall IT D X x P D', reduction D D' ->
    reduction (TIAll IT D X x P) (TIAll IT D' X x P)
| red_TIAll_X : forall IT D X x P X', reduction X X' ->
    reduction (TIAll IT D X x P) (TIAll IT D X' x P)
| red_TIAll_x : forall IT D X x P x', reduction x x' ->
    reduction (TIAll IT D X x P) (TIAll IT D X x' P)
| red_TIAll_P : forall IT D X x P P', reduction P P' ->
    reduction (TIAll IT D X x P) (TIAll IT D X x P')
| red_THyps_IT : forall IT D X P h x IT', reduction IT IT' ->
    reduction (THyps IT D X P h x) (THyps IT' D X P h x)
| red_THyps_D : forall IT D X P h x D', reduction D D' ->
    reduction (THyps IT D X P h x) (THyps IT D' X P h x)
| red_THyps_X : forall IT D X P h x X', reduction X X' ->
    reduction (THyps IT D X P h x) (THyps IT D X' P h x)
| red_THyps_P : forall IT D X P h x P', reduction P P' ->
    reduction (THyps IT D X P h x) (THyps IT D X P' h x)
| red_THyps_h : forall IT D X P h x h', reduction h h' ->
    reduction (THyps IT D X P h x) (THyps IT D X P h' x)
| red_THyps_x : forall IT D X P h x x', reduction x x' ->
    reduction (THyps IT D X P h x) (THyps IT D X P h x')
| red_TClose_IT : forall IT F G IT', reduction IT IT' ->
    reduction (TClose IT F G) (TClose IT' F G)
| red_TClose_F : forall IT F G F', reduction F F' ->
    reduction (TClose IT F G) (TClose IT F' G)
| red_TClose_G : forall IT F G G', reduction G G' ->
    reduction (TClose IT F G) (TClose IT F G')
| red_TCloseCase_IT : forall k IT F G i Q b x IT', reduction IT IT' ->
    reduction (TCloseCase k IT F G i Q b x) (TCloseCase k IT' F G i Q b x)
| red_TCloseCase_F : forall k IT F G i Q b x F', reduction F F' ->
    reduction (TCloseCase k IT F G i Q b x) (TCloseCase k IT F' G i Q b x)
| red_TCloseCase_G : forall k IT F G i Q b x G', reduction G G' ->
    reduction (TCloseCase k IT F G i Q b x) (TCloseCase k IT F G' i Q b x)
| red_TCloseCase_i : forall k IT F G i Q b x i', reduction i i' ->
    reduction (TCloseCase k IT F G i Q b x) (TCloseCase k IT F G i' Q b x)
| red_TCloseCase_Q : forall k IT F G i Q b x Q', reduction Q Q' ->
    reduction (TCloseCase k IT F G i Q b x) (TCloseCase k IT F G i Q' b x)
| red_TCloseCase_b : forall k IT F G i Q b x b', reduction b b' ->
    reduction (TCloseCase k IT F G i Q b x) (TCloseCase k IT F G i Q b' x)
| red_TCloseCase_x : forall k IT F G i Q b x x', reduction x x' ->
    reduction (TCloseCase k IT F G i Q b x) (TCloseCase k IT F G i Q b x')
| red_TCloseInd_IT : forall IT G P s F i x IT', reduction IT IT' ->
    reduction (TCloseInd IT G P s F i x) (TCloseInd IT' G P s F i x)
| red_TCloseInd_G : forall IT G P s F i x G', reduction G G' ->
    reduction (TCloseInd IT G P s F i x) (TCloseInd IT G' P s F i x)
| red_TCloseInd_P : forall IT G P s F i x P', reduction P P' ->
    reduction (TCloseInd IT G P s F i x) (TCloseInd IT G P' s F i x)
| red_TCloseInd_s : forall IT G P s F i x s', reduction s s' ->
    reduction (TCloseInd IT G P s F i x) (TCloseInd IT G P s' F i x)
| red_TCloseInd_F : forall IT G P s F i x F', reduction F F' ->
    reduction (TCloseInd IT G P s F i x) (TCloseInd IT G P s F' i x)
| red_TCloseInd_i : forall IT G P s F i x i', reduction i i' ->
    reduction (TCloseInd IT G P s F i x) (TCloseInd IT G P s F i' x)
| red_TCloseInd_x : forall IT G P s F i x x', reduction x x' ->
    reduction (TCloseInd IT G P s F i x) (TCloseInd IT G P s F i x').

Inductive reduces : term -> term -> Prop :=
| reduces_refl : forall t, reduces t t
| reduces_step : forall t u v, reduction t u -> reduces u v -> reduces t v.

Inductive conv : term -> term -> Prop :=
| cv_step : forall t u, step t u -> conv t u
| cv_refl : forall t, conv t t
| cv_sym : forall t u, conv t u -> conv u t
| cv_trans : forall t u v, conv t u -> conv u v -> conv t v
| cv_eta : forall f, conv (TLam (TApp (lift 1 0 f) (TVar 0))) f
| cv_compatible : forall t u, compatible conv t u -> conv t u.

(* A deterministic reduction strategy for concrete computation checks.
   Fuel exhaustion is NOT evidence of normality, conversion, or emptiness. *)
Fixpoint next_step (t : term) : option term :=
  match root_step t with
  | Some u => Some u
  | None =>
    match t with
    | TApp f a =>
      match next_step f with
      | Some f' => Some (TApp f' a)
      | None => None
      end
    | TPair a b =>
      match next_step a with
      | Some a' => Some (TPair a' b)
      | None => match next_step b with
      | Some b' => Some (TPair a b')
      | None => None
      end
      end
    | TFst p =>
      match next_step p with
      | Some p' => Some (TFst p')
      | None => None
      end
    | TSnd p =>
      match next_step p with
      | Some p' => Some (TSnd p')
      | None => None
      end
    | TESucc n =>
      match next_step n with
      | Some n' => Some (TESucc n')
      | None => None
      end
    | TEPi k E P =>
      match next_step E with
      | Some E' => Some (TEPi k E' P)
      | None => None
      end
    | TSwitch k E P p e =>
      match next_step E with
      | Some E' => Some (TSwitch k E' P p e)
      | None => match next_step p with
      | Some p' => Some (TSwitch k E P p' e)
      | None => match next_step e with
      | Some e' => Some (TSwitch k E P p e')
      | None => None
      end
      end
      end
    | TInterp IT D X =>
      match next_step D with
      | Some D' => Some (TInterp IT D' X)
      | None => None
      end
    | TIn x =>
      match next_step x with
      | Some x' => Some (TIn x')
      | None => None
      end
    | TInd IT D P s i x =>
      match next_step x with
      | Some x' => Some (TInd IT D P s i x')
      | None => None
      end
    | TIAll IT D X x P =>
      match next_step D with
      | Some D' => Some (TIAll IT D' X x P)
      | None => match next_step x with
      | Some x' => Some (TIAll IT D X x' P)
      | None => None
      end
      end
    | THyps IT D X P h x =>
      match next_step D with
      | Some D' => Some (THyps IT D' X P h x)
      | None => match next_step x with
      | Some x' => Some (THyps IT D X P h x')
      | None => None
      end
      end
    | TCloseCase k IT F G i Q b x =>
      match next_step x with
      | Some x' => Some (TCloseCase k IT F G i Q b x')
      | None => None
      end
    | TCloseInd IT G P s F i x =>
      match next_step x with
      | Some x' => Some (TCloseInd IT G P s F i x')
      | None => None
      end
    | _ => None
    end
  end.

Fixpoint run (fuel : nat) (t : term) : term :=
  match fuel with
  | 0 => t
  | S fuel => match next_step t with Some u => run fuel u | None => t end
  end.

Inductive value : term -> Prop :=
| v_sort : forall k, value (TSort k)
| v_pi : forall A B, value (TPi A B)
| v_lam : forall b, value (TLam b)
| v_sigma : forall A B, value (TSigma A B)
| v_pair : forall a b, value (TPair a b)
| v_unitT : value TUnitT
| v_unit : value TUnit
| v_uid : value TUId
| v_tag : forall s, value (TTag s)
| v_enumu : value TEnumU
| v_nile : value TNilE
| v_conse : forall s E, value (TConsE s E)
| v_enumt : forall E, value (TEnumT E)
| v_zero : value TEZero
| v_succ : forall n, value (TESucc n)
| v_idesc : forall IT, value (TIDesc IT)
| v_ivar : forall i, value (TIVar i)
| v_i1 : value TI1
| v_ibot : value TIBot
| v_iprod : forall A B, value (TIProd A B)
| v_ipi : forall A D, value (TIPi A D)
| v_isig : forall A D, value (TISig A D)
| v_ichoice : forall E D, value (TIChoice E D)
| v_mui : forall IT D, value (TMuI IT D)
| v_mui_app : forall IT D i, value (MuAt IT D i)
| v_close : forall IT F G, value (TClose IT F G)
| v_close_app : forall IT F G i, value (CloseAt IT F G i)
| v_in : forall xs, value (TIn xs).

(* Declarative core typing. The target of conversion must itself be a type;
   no source coercion relation occurs in these mutually inductive rules. *)
