module

public import SerrePositivity.KST.Spectra.PointedBasedPathClosed

/-!
概要：内部 Hom の辺を元の基点固定区間として読み、部分対象への区間全体の制限を計算する。
方針：Yoneda と相対 curry の包含式を使う。端点だけの同定へ弱めない。
規約：Kan 性不要。使われ方：非零境界の段調整区間と構造比較のトレース。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
namespace SerrePositivity.KST.Spectra.PointedMapping

/-- 元の辺そのものを区間族として持つ、基点固定区間。 -/
def basedPathOfEdge {A E : PointedSimplicialSet.{u}} {f g : A ⟶ E}
    (e : (PointedObject.basedHom A E).right.Edge (familyVertex f) (familyVertex g)) :
    VerticalPath (PointedObject.toPoint E) f g where
  path := SSet.yonedaEquiv.symm e.edge
  zero := by
    rw [SSet.Edge.δ_one_yonedaEquiv_symm]
    exact SSet.yonedaEquiv.symm_apply_apply (pointFamily f)
  one := by
    rw [SSet.Edge.δ_zero_yonedaEquiv_symm]
    exact SSet.yonedaEquiv.symm_apply_apply (pointFamily g)
  «over» := by
    apply (cancel_mono (PointedObject.basedHomι A PointedObject.point)).1
    apply uncurry_injective
    exact toUnit_unique _ _

/-- 辺から区間を作っても、元の辺の単体データを変更しない。 -/
lemma basedPathOfEdge_edge {A E : PointedSimplicialSet.{u}} {f g : A ⟶ E}
    (e : (PointedObject.basedHom A E).right.Edge (familyVertex f) (familyVertex g)) :
    (basedPathOfEdge e).edge = e :=
  SSet.Edge.ext (SSet.yonedaEquiv.apply_symm_apply e.edge)

/-- 区間族の部分対象への制限は、評価したホモトピーの同じ制限を curry したもの。 -/
lemma paramCurry_restrict {A B E : PointedSimplicialSet.{u}} (j : B ⟶ A)
    (F : A.right ⊗ (Δ[1] : SSet.{u}) ⟶ E.right)
    (hb : A.hom ▷ (Δ[1] : SSet.{u}) ≫ F =
      toUnit (𝟙_ SSet.{u} ⊗ (Δ[1] : SSet.{u})) ≫ E.hom)
    (G : B.right ⊗ (Δ[1] : SSet.{u}) ⟶ E.right)
    (hg : B.hom ▷ (Δ[1] : SSet.{u}) ≫ G =
      toUnit (𝟙_ SSet.{u} ⊗ (Δ[1] : SSet.{u})) ≫ E.hom)
    (h : j.right ▷ (Δ[1] : SSet.{u}) ≫ F = G) :
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.paramCurry A E F hb ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed j E).right = _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.paramCurry B E G hg := by
  apply (cancel_mono (PointedObject.basedHomι B E)).1
  change _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre j E ≫ _ = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre_ι, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.paramCurry_ι, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.paramCurry_ι]
  apply uncurry_injective
  rw [uncurry_pre_app, uncurry_curry, uncurry_curry]
  exact h

/-- 元の区間に二度前合成したトレースは、合成した元の入力への一度の前合成。 -/
lemma pre_restriction_homotopy {S A B E : PointedSimplicialSet.{u}} {f g : S ⟶ E}
    (P : VerticalPath (PointedObject.toPoint E) f g) (e : A ⟶ S) (j : B ⟶ A) :
    j.right ▷ (Δ[1] : SSet.{u}) ≫ (P.pre e).homotopy.h =
      ((j ≫ e).right ▷ (Δ[1] : SSet.{u})) ≫ P.homotopy.h := by
  rw [VerticalPath.pre_homotopy_h, ← comp_whiskerRight_assoc]
  rfl

end SerrePositivity.KST.Spectra.PointedMapping
