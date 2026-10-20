module

public import SerrePositivity.InfinityCategories.F1.RelativeHomRecoveryPointedComparison

/-!
概要：元の相対 Hom と coherent 変換空間を、実際の比較と回収による同値にする。
方針：既存の片側の往復を主比較の同値性で消去し、反対向きの往復も恒等へ結ぶ。
規約：順方向と逆方向は既存の射そのもの。
使われ方：標準 Hom の族から全空間の自然な比較を回収する主経路。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 元の回収に主比較を続ける反対向きの往復も、全 coherent 変換空間で恒等と同型。 -/
def relativeHomCoherentRecoveryComparisonIso {B : SSet.{u}} (a q : LeftFibrationObject B) :
    FunctorIso (relativeHomCoherentRecovery a q ≫ relativeHomCoherentComparison a q)
      (𝟙 (pinchedHom (functorVertex (leftFibrationCoherentEvaluation q.val))
        (functorVertex (leftFibrationCoherentEvaluation a.val)))) := by
  let e := (relativeHomCoherentComparison_isQCatEquivalence a q).choose
  have he : e.hom = relativeHomCoherentComparison a q := rfl
  have i := (e.invHomIso.postcomp (relativeHomCoherentRecovery a q)).symm
  have j := (relativeHomCoherentComparisonRecoveryIso a q).precomp e.inv
  rw [← he] at j
  have h : FunctorIso (relativeHomCoherentRecovery a q) e.inv :=
    (show FunctorIso (relativeHomCoherentRecovery a q)
      (e.inv ≫ e.hom ≫ relativeHomCoherentRecovery a q) from
        by simpa only [Category.assoc, Category.id_comp] using i) ≪≫
      (by simpa only [Category.comp_id] using j)
  have n := h.postcomp e.hom ≪≫ e.invHomIso
  rw [he] at n
  exact n

/-- 反対向きの往復と恒等を結ぶ、実際の全 coherent 変換空間上の単体的ホモトピー。 -/
def relativeHomCoherentRecoveryComparisonHomotopy {B : SSet.{u}}
    (a q : LeftFibrationObject B) :
    SSet.Homotopy (relativeHomCoherentRecovery a q ≫ relativeHomCoherentComparison a q)
      (𝟙 (pinchedHom (functorVertex (leftFibrationCoherentEvaluation q.val))
        (functorVertex (leftFibrationCoherentEvaluation a.val)))) :=
  (relativeHomCoherentRecoveryComparisonIso a q).simplicialHomotopy

/-- 相対 Hom と coherent 変換空間の同値は、元の主比較と恒等射での回収を両方向に持つ。 -/
def relativeHomCoherentEquivalence {B : SSet.{u}} (a q : LeftFibrationObject B) :
    QCatEquivalence
      ((SSet.uliftFunctor.{u + 1, u}).obj (relativeFunctorSpace q.val.hom a.val.hom))
      (pinchedHom (functorVertex (leftFibrationCoherentEvaluation q.val))
        (functorVertex (leftFibrationCoherentEvaluation a.val))) where
  hom := relativeHomCoherentComparison a q
  inv := relativeHomCoherentRecovery a q
  homInvIso := relativeHomCoherentComparisonRecoveryIso a q
  invHomIso := relativeHomCoherentRecoveryComparisonIso a q

end SerrePositivity.InfinityCategories
