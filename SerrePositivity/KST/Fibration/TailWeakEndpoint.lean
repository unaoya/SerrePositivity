module
public import SerrePositivity.KST.Fibration.TailWeakPullback
public import SerrePositivity.KST.Fibration.ComposableWeakArrowEndpointPullback
public import SerrePositivity.KST.Fibration.WeakStringVertices

/-! # 先行 W 列の元の最終頂点と相対 subobject の値域の照合 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Fibration

/-- 先行 W 列の共有端点を、元の一点図式として抽出する完全関手。 -/
def tailPrefixEndpointDiagram {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (n : ℕ) :
    weakStringModel q ⦋n + 1⦌ ⟶ ambientDiagramModel (Δ[0] : SSet.{u}) B :=
  closedStableInclusion (weakStringClosedPredicate q ⦋n + 1⦌) ≫
    ambientDiagramRestriction B (standardTailEndpoint n)

/-- 元の共有端点を相対 subobject と同じ全頂点部分圏に値を持たせる。 -/
def tailPrefixEndpointTop {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (n : ℕ) :
    weakStringModel q ⦋n + 1⦌ ⟶ closedStableModel (ClosedStablePredicate.top (sInputModel B)) :=
  tailPrefixEndpointDiagram q n ≫ (ambientPointExactIso B).hom ≫ closedTopLift (sInputModel B)

/-- 一点図式を元の圏へ戻すと、元の先行列の最後の頂点評価を厳密に回収する。 -/
lemma tailPrefixEndpointDiagram_evaluate {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (n : ℕ) :
    tailPrefixEndpointDiagram q n ≫ (ambientPointExactIso B).hom =
      weakStringVertexExact q ⦋n + 1⦌ (Fin.last (n + 1)) := by
  apply Subtype.ext
  change (_ ≫ (pre (standardTailEndpoint n)).app B.obj) ≫
    (SConstruction.pointFunctorEvaluationIso B.obj).hom = _
  rw [Category.assoc, standardTailEndpoint_eq_yoneda, evaluateFunctorAt_factor]
  rfl

/-- 全頂点部分圏値でも共有端点は、元の最後の頂点評価と一致する。 -/
lemma tailPrefixEndpointTop_eq {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (n : ℕ) :
    tailPrefixEndpointTop q n = weakStringVertexTopExact q ⦋n + 1⦌ (Fin.last (n + 1)) := by
  apply (cancel_mono (closedTopExactIso (sInputModel B)).hom).1
  change (tailPrefixEndpointDiagram q n ≫ (ambientPointExactIso B).hom ≫
    (closedTopExactIso (sInputModel B)).inv) ≫ (closedTopExactIso (sInputModel B)).hom = _
  rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    tailPrefixEndpointDiagram_evaluate]
  apply Subtype.ext
  exact (weakStringVertexTopMap_ι q ⦋n + 1⦌ (Fin.last (n + 1))).symm

/-- 元の先行列・最後の辺の厳密引き戻しを、相対 subobject と同じ全頂点部分圏上に移す。 -/
theorem tailWeak_top_isPullback {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (n : ℕ) :
    IsPullback (tailWeakPrefixExact q n).val (tailWeakEdgeExact q n).val
      (tailPrefixEndpointTop q n).val (weakArrowSourceTopExact q).val := by
  let e := stableModelForget.mapIso
    (ambientPointExactIso B ≪≫ (closedTopExactIso (sInputModel B)).symm)
  apply (tailWeak_isPullback q n).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) e
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    rfl
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    rfl
  · rfl
  · rfl

end SerrePositivity.KST.Fibration
