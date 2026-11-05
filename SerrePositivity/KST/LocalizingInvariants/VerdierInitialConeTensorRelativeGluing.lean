module

public import SerrePositivity.KST.LocalizingInvariants.InitialConeTensorCornerGluing
public import SerrePositivity.KST.LocalizingInvariants.VerdierInitialConeTensorRelativeBoundary

/-!
概要：元の図式側で定値な比較を貼り、同じ側を固定した実延長を構成する。
方針：実 pushout で比較を貼り、その実辺を相対境界延長へ直接渡す。
規約：全境界と比較辺を実構成し、元の図式側の定値性を全円柱で保持する。
使われ方：c5 の次元帰納の相対貼合せ。任意完成族からの尾部回収は別途必要。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

/-- 元の図式側で定値な比較を貼り、その側を固定した同じ実延長を得る。 -/
lemma exists_verdierInitialConeTensorRelativeGluing {A₀ B C : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}}
    {i : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A₀ B} {q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap B C} (h : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.IsVerdierSequence i q)
    (A L : SSet.{u}) [A.Finite] [L.Finite]
    (F : (A.op ⊗ join L.op (Δ[0] : SSet.{u})).op ⟶ B.obj)
    (G : (join A.op (Δ[0] : SSet.{u}) ⊗ L.op).op ⟶ B.obj)
    (w : SSet.opFunctor.map (A.op ◁ joinInl L.op (Δ[0] : SSet.{u})) ≫ F =
      SSet.opFunctor.map (joinInl A.op (Δ[0] : SSet.{u}) ▷ L.op) ≫ G)
    (H : join (Δ[0] : SSet.{u}) A ⊗ join (Δ[0] : SSet.{u}) L ⟶ C.obj)
    (J : SSet.Homotopy
      (initialConeTensorOldInclusion A L ≫ initialConeTensorCornerInclusion A L ≫ H)
      (F ≫ q.hom))
    (K : SSet.Homotopy
      (initialConeTensorTailInclusion A L ≫ initialConeTensorCornerInclusion A L ≫ H)
      (G ≫ q.hom))
    (hw : (SSet.opFunctor.map (A.op ◁ joinInl L.op (Δ[0] : SSet.{u})) ▷ Δ[1]) ≫ J.h =
      (SSet.opFunctor.map (joinInl A.op (Δ[0] : SSet.{u}) ▷ L.op) ▷ Δ[1]) ≫ K.h)
    (hJ : ∀ x, IsInvertibleEdge (simplicialHomotopyVertexEdge J x).toTruncated)
    (hK : ∀ x, IsInvertibleEdge (simplicialHomotopyVertexEdge K x).toTruncated)
    (hJfixed : J.h = fst _ (Δ[1] : SSet.{u}) ≫ (F ≫ q.hom)) :
    ∃ (D : join (Δ[0] : SSet.{u}) A ⊗ join (Δ[0] : SSet.{u}) L ⟶ B.obj)
      (V : SSet.Homotopy (D ≫ q.hom) H),
      (initialConeTensorOldInclusion A L ≫ initialConeTensorCornerInclusion A L) ≫ D = F ∧
      (initialConeTensorTailInclusion A L ≫ initialConeTensorCornerInclusion A L) ≫ D = G ∧
      ((initialConeTensorOldInclusion A L ≫ initialConeTensorCornerInclusion A L) ▷
        (Δ[1] : SSet.{u})) ≫ V.h = fst _ Δ[1] ≫ (F ≫ q.hom) ∧
      ∀ x, IsInvertibleEdge (simplicialHomotopyVertexEdge V x).toTruncated := by
  let p := initialConeTensorCornerGlue F G w
  have hpF : initialConeTensorOldInclusion A L ≫ (p ≫ q.hom) = F ≫ q.hom := by
    rw [← Category.assoc, initialConeTensorCornerGlue_old]
  have hpG : initialConeTensorTailInclusion A L ≫ (p ≫ q.hom) = G ≫ q.hom := by
    rw [← Category.assoc, initialConeTensorCornerGlue_tail]
  let J' : SSet.Homotopy
      (initialConeTensorOldInclusion A L ≫ (initialConeTensorCornerInclusion A L ≫ H))
      (initialConeTensorOldInclusion A L ≫ (p ≫ q.hom)) := {
    h := J.h
    h₀ := J.h₀
    h₁ := J.h₁.trans hpF.symm
    rel := J.rel }
  let K' : SSet.Homotopy
      (initialConeTensorTailInclusion A L ≫ (initialConeTensorCornerInclusion A L ≫ H))
      (initialConeTensorTailInclusion A L ≫ (p ≫ q.hom)) := {
    h := K.h
    h₀ := K.h₀
    h₁ := K.h₁.trans hpG.symm
    rel := K.rel }
  have hiJ : ∀ x, IsInvertibleEdge (simplicialHomotopyVertexEdge J' x).toTruncated := by
    intro x
    exact (isInvertibleEdge_congr (e := (simplicialHomotopyVertexEdge J' x).toTruncated)
      (f := (simplicialHomotopyVertexEdge J x).toTruncated) rfl).mpr (hJ x)
  have hiK : ∀ x, IsInvertibleEdge (simplicialHomotopyVertexEdge K' x).toTruncated := by
    intro x
    exact (isInvertibleEdge_congr (e := (simplicialHomotopyVertexEdge K' x).toTruncated)
      (f := (simplicialHomotopyVertexEdge K x).toTruncated) rfl).mpr (hK x)
  let U := pushoutComparisonHomotopy (initialConeTensorCorner_isPushout A L) J' K' hw
  have hi : IsInvertibleEdge (functorEdgeOfSimplicialHomotopy U) :=
    pushoutComparisonHomotopy_isInvertible (initialConeTensorCorner_isPushout A L)
      J' K' hw hiJ hiK
  have hpre : curry U.h ≫ (pre (initialConeTensorOldInclusion A L)).app C.obj =
      SSet.const (functorVertex (F ≫ q.hom)) := by
    apply uncurry_injective
    rw [uncurry_pre_app, uncurry_curry, uncurry_const_functorVertex]
    rw [pushoutComparisonHomotopy_left]
    exact hJfixed
  let a := SSet.Edge.ofTruncated (functorEdgeOfSimplicialHomotopy U)
  have hk : ((pre (initialConeTensorOldInclusion A L)).app C.obj).app
      (Opposite.op ⦋1⦌) a.edge =
      (Truncated.Edge.id (X := (truncation 2).obj
        ((ihom ((A.op ⊗ join L.op (Δ[0] : SSet.{u})).op)).obj C.obj))
        (functorVertex (initialConeTensorOldInclusion A L ≫ p ≫ q.hom))).edge := by
    change ((pre (initialConeTensorOldInclusion A L)).app C.obj).app
      (Opposite.op ⦋1⦌) (SSet.yonedaEquiv (curry U.h)) = _
    rw [← SSet.yonedaEquiv_comp, hpre, hpF]
    change PinchedHom.constant (functorVertex (F ≫ q.hom)) 1 = _
    exact pinchedConstant_one _
  obtain ⟨D, V, hD, hV, hiV⟩ := exists_verdierInitialConeTensorRelativeBoundary
    h A L p H a hi (initialConeTensorOldInclusion A L) hk
  refine ⟨D, V, ?_, ?_, ?_, hiV⟩
  · rw [Category.assoc, hD]
    exact initialConeTensorCornerGlue_old F G w
  · rw [Category.assoc, hD]
    exact initialConeTensorCornerGlue_tail F G w
  · simpa only [hpF] using hV

end SerrePositivity.KST.LocalizingInvariants
