module
public import SerrePositivity.KST.Fibration.WeakStringTwoHornComponents
public import SerrePositivity.KST.Fibration.WeakStringFiniteComparison
public import SerrePositivity.KST.Fibration.WeakStringCofiberSource

/-! # 元の二辺の有限比較の厳密な切断因子分解

元の初期頂点と両 cofiber の射を、接続した二辺の引き戻し模型上で回収する。
既知の圏同値を前段に持つ因子分解により、未証明の積比較を厳密に切り分ける。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration

/-- 接続した二辺から元の初期頂点を取る完全関手。 -/
def composableWeakInitialExact {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    composableWeakArrowModel q ⟶ closedStableModel (ClosedStablePredicate.top (sInputModel B)) :=
  composableWeakFirstExact q ≫ (weakArrowCofiberEquivalence q).inv ≫
    relativeCofiberSubobject (ClosedStablePredicate.top (sInputModel B)) (kernelClosedPredicate q)

/-- 接続した二辺の各辺の共通 cofiber を取る完全関手。 -/
def composableWeakCofiberExact {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (i : Fin 2) :
    composableWeakArrowModel q ⟶ closedStableModel (kernelClosedPredicate q) :=
  Fin.cases (composableWeakFirstExact q) (fun _ => composableWeakNextExact q) i ≫
    (weakArrowCofiberEquivalence q).inv ≫
      relativeCofiberQuotient (ClosedStablePredicate.top (sInputModel B)) (kernelClosedPredicate q)

/-- 切断後の初期評価は元の初期頂点の評価である。 -/
lemma weakStringTwoHorn_initial {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    weakStringTwoHornExact q ≫ composableWeakInitialExact q =
      weakStringVertexTopExact q ⦋2⦌ 0 := by
  unfold composableWeakInitialExact
  rw [← Category.assoc, weakStringTwoHornExact_first]
  have hv : (SimplexCategory.δ (2 : Fin 3)).toOrderHom 0 = (0 : Fin 3) := by decide
  exact (Category.assoc (weakStringEdgeExact q (SimplexCategory.δ (2 : Fin 3)))
    (weakArrowCofiberEquivalence q).inv
    (relativeCofiberSubobject (ClosedStablePredicate.top (sInputModel B))
      (kernelClosedPredicate q))).symm.trans
        ((weakStringCofiberSubobject_eq q (SimplexCategory.δ (2 : Fin 3))).trans
          (congrArg (weakStringVertexTopExact q ⦋2⦌) hv))

/-- 切断後の両 cofiber は、元の同じ連続辺の共通補完を厳密に回収する。 -/
lemma weakStringTwoHorn_cofiber {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (i : Fin 2) :
    weakStringTwoHornExact q ≫ composableWeakCofiberExact q i =
      weakStringKernelCofiber q (consecutiveWeakStringEdge 2 i) := by
  fin_cases i
  · have he : consecutiveWeakStringEdge 2 0 = SimplexCategory.δ (2 : Fin 3) := by decide
    change weakStringTwoHornExact q ≫ (composableWeakFirstExact q ≫ _) = _
    calc
      _ = (weakStringTwoHornExact q ≫ composableWeakFirstExact q) ≫ _ :=
        (Category.assoc _ _ _).symm
      _ = weakStringEdgeExact q (SimplexCategory.δ (2 : Fin 3)) ≫ _ :=
        congrArg (· ≫ _) (weakStringTwoHornExact_first q)
      _ = weakStringKernelCofiber q (SimplexCategory.δ (2 : Fin 3)) :=
        (Category.assoc _ _ _).symm
      _ = _ := congrArg (weakStringKernelCofiber q) he.symm
  · have he : consecutiveWeakStringEdge 2 1 = SimplexCategory.δ (0 : Fin 3) := by decide
    change weakStringTwoHornExact q ≫ (composableWeakNextExact q ≫ _) = _
    calc
      _ = (weakStringTwoHornExact q ≫ composableWeakNextExact q) ≫ _ :=
        (Category.assoc _ _ _).symm
      _ = weakStringEdgeExact q (SimplexCategory.δ (0 : Fin 3)) ≫ _ :=
        congrArg (· ≫ _) (weakStringTwoHornExact_next q)
      _ = weakStringKernelCofiber q (SimplexCategory.δ (0 : Fin 3)) :=
        (Category.assoc _ _ _).symm
      _ = _ := congrArg (weakStringKernelCofiber q) he.symm

/-- 接続した二辺の模型上で、同じ初期頂点と同じ両 cofiber を束ねた積比較。 -/
def composableWeakTwoComparison {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (r : ℕ) :
    (multiRealizationFunctor r).obj (composableWeakArrowModel q) ⟶
      (multiRealizationFunctor r).obj
        (closedStableModel (ClosedStablePredicate.top (sInputModel B))) ⊗
        ∏ᶜ (fun _ : Fin 2 =>
          (multiRealizationFunctor r).obj (closedStableModel (kernelClosedPredicate q))) :=
  lift ((multiRealizationFunctor r).map (composableWeakInitialExact q))
    (Pi.lift (fun i => (multiRealizationFunctor r).map (composableWeakCofiberExact q i)))

/-- 元の二辺の有限比較は、元の圏同値と引き戻し模型上の同じ積比較の合成。 -/
lemma weakStringFiniteComparison_two_factor {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    (r : ℕ) :
    (multiRealizationFunctor r).map (weakStringTwoHornExact q) ≫
      composableWeakTwoComparison q r = weakStringFiniteComparison q 2 r := by
  unfold composableWeakTwoComparison weakStringFiniteComparison
  rw [comp_lift]
  apply congrArg₂ lift
  · rw [← Functor.map_comp, weakStringTwoHorn_initial]
  · apply Pi.hom_ext
    intro i
    rw [Category.assoc, Pi.lift_comp_π, weakStringConsecutiveCofibers_projection,
      ← Functor.map_comp, weakStringTwoHorn_cofiber]
    rfl

/-- 二辺の有限比較の同値性は、引き戻し模型上の同じ具体的積比較の同値性と同値。 -/
lemma weakStringFiniteComparison_two_localized_isIso_iff {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (r : ℕ) :
    IsIso (AnodyneHomotopy.anodyneQ.map (weakStringFiniteComparison q 2 (r + 1))) ↔
      IsIso (AnodyneHomotopy.anodyneQ.map (composableWeakTwoComparison q (r + 1))) := by
  have : IsIso (AnodyneHomotopy.anodyneQ.map
      ((multiRealizationFunctor (r + 1)).map (weakStringTwoHornExact q))) :=
    weakStringTwoHorn_multiRealization_localized_isIso q r
  rw [← weakStringFiniteComparison_two_factor, Functor.map_comp]
  exact isIso_comp_left_iff _ _

end SerrePositivity.KST.Fibration
