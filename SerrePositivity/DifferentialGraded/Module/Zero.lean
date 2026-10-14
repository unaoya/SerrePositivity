module
public import SerrePositivity.DifferentialGraded.Module.ClosedMaps
public import SerrePositivity.DifferentialGraded.Complexes.Zero

/-! # 全次数の零加群と閉零加群圏の零対象 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits MonoidalCategory Opposite
open scoped ZeroObject
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

/-- 各対象で零複体、全次数の Hom 作用で零となる右 dg 加群。 -/
abbrev zeroModule : RightModule A D where
  obj _ := 0
  map _ _ := 0
  map_id _ := (homComplex_isZero_src (isZero_zero (Complex A))).eq_of_tgt _ _
  map_comp _ _ _ := (homComplex_isZero_src (isZero_zero (Complex A))).eq_of_tgt _ _

/-- 零加群の対象での評価は零複体。 -/
lemma zeroModule_obj (x : Dᵒᵖ) : (zeroModule A D).obj x = (0 : Complex A) := rfl

variable [Small.{u} D]

/-- objectwise 零加群からの Hom end 自体が零複体になる。 -/
lemma moduleHom_isZero_src (M N : RightModule A D)
    (hM : ∀ x : D, IsZero (M.obj (op x))) : IsZero (moduleHom A D M N) := by
  apply (IsZero.iff_id_eq_zero _).2
  apply moduleHom_ext
  intro x
  exact (homComplex_isZero_src (hM x)).eq_of_tgt _ _

/-- objectwise 零加群への Hom end 自体が零複体になる。 -/
lemma moduleHom_isZero_tgt (M N : RightModule A D)
    (hN : ∀ x : D, IsZero (N.obj (op x))) : IsZero (moduleHom A D M N) := by
  apply (IsZero.iff_id_eq_zero _).2
  apply moduleHom_ext
  intro x
  exact (homComplex_isZero_tgt (hN x)).eq_of_tgt _ _

/-- 閉次数零加群圏に置いた具体的零加群。 -/
abbrev moduleZero : ModuleCategory A D := ForgetEnrichment.of (Complex A) (zeroModule A D)

/-- 全次数自然性を保持した零加群からの射。 -/
def moduleZeroTo (M : ModuleCategory A D) : moduleZero A D ⟶ M :=
  moduleMorphismMk A D (M := zeroModule A D)
    (N := ForgetEnrichment.to (Complex A) M) (fun _ => 0)
    (fun _ _ => (homComplex_isZero_src (isZero_zero (Complex A))).eq_of_tgt _ _)

/-- 全次数自然性を保持した零加群への射。 -/
def moduleToZero (M : ModuleCategory A D) : M ⟶ moduleZero A D :=
  moduleMorphismMk A D (M := ForgetEnrichment.to (Complex A) M)
    (N := zeroModule A D) (fun _ => 0)
    (fun _ _ => (homComplex_isZero_tgt (isZero_zero (Complex A))).eq_of_tgt _ _)

/-- 零加群からの射は各評価で零 chain map。 -/
@[simp] lemma moduleZeroTo_eval (M : ModuleCategory A D) (x : D) :
    (moduleEvaluation A D x).map (moduleZeroTo A D M) = 0 :=
  moduleMorphismMk_eval A D _ _ x

/-- 零加群への射は各評価で零 chain map。 -/
@[simp] lemma moduleToZero_eval (M : ModuleCategory A D) (x : D) :
    (moduleEvaluation A D x).map (moduleToZero A D M) = 0 :=
  moduleMorphismMk_eval A D _ _ x

/-- 具体的零加群は閉零圏の零対象の普遍性を満たす。 -/
lemma moduleZero_isZero : IsZero (moduleZero A D) := by
  constructor
  · intro M
    refine ⟨⟨⟨moduleZeroTo A D M⟩, fun f => ?_⟩⟩
    apply moduleMorphism_ext
    intro x
    exact (isZero_zero (Complex A)).eq_of_src _ _
  · intro M
    refine ⟨⟨⟨moduleToZero A D M⟩, fun f => ?_⟩⟩
    apply moduleMorphism_ext
    intro x
    exact (isZero_zero (Complex A)).eq_of_tgt _ _

instance moduleHasZeroObject : HasZeroObject (ModuleCategory A D) :=
  (moduleZero_isZero A D).hasZeroObject

/-- 各評価は加法的であり、零射を保存する。 -/
instance moduleEvaluationAdditive (x : D) : (moduleEvaluation A D x).Additive := by
  change ((moduleEvaluationDG A D x).onClosed ⋙ closedToComplex A).Additive
  infer_instance

/-- 零対象性は全対象での零複体性と同値。 -/
lemma module_isZero_iff (M : ModuleCategory A D) :
    IsZero M ↔ ∀ x : D, IsZero ((moduleEvaluation A D x).obj M) := by
  constructor
  · intro h x
    exact (moduleEvaluation A D x).map_isZero h
  · intro h
    apply (IsZero.iff_id_eq_zero M).2
    apply moduleMorphism_ext
    intro x
    rw [CategoryTheory.Functor.map_id, Functor.map_zero]
    exact (h x).eq_of_src _ _

/-- 選ばれた圏の零対象を評価すると零複体に標準的に同型。 -/
def moduleEvaluationZeroIso (x : D) :
    (moduleEvaluation A D x).obj (0 : ModuleCategory A D) ≅ (0 : Complex A) :=
  ((moduleEvaluation A D x).map_isZero (isZero_zero (ModuleCategory A D))).isoZero
end SerrePositivity.DifferentialGraded
