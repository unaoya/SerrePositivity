module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SliceSquareDiagramEvaluation

/-! # Slice の四角形表示と固定 cospan

概要：slice からの四角形図式は右・上辺を固定し、終点評価が定値となる。
方針：普遍錐の固定条件と形状同型の逆則を使う。
規約：値域に追加仮定なし。使われ方：D7 の前合成比較の終点成分。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped _root_.Simplicial

/-- 全錐の図式表示を固定図式へ制限すると定値になる。 -/
lemma sliceConeDiagramMap_restriction {K X : SSet.{u}} (p : K ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.sliceConeDiagramMap p ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction K X = SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p) := by
  change curry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.sliceConeFamilyUncurry p) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction K X = _
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.sliceConeFamilyUncurry_curry_fixed p

/-- 四角形表示の cospan への制限は全錐図式の制限と同じ。 -/
lemma sliceSquareDiagramMap_restriction {X : SSet.{u}}
    (p : (horn 2 2 : SSet.{u}) ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.sliceSquareDiagramMap p ≫ (pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary).app X =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.sliceConeDiagramMap p ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction (horn 2 2 : SSet.{u}) X := by
  unfold _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.sliceSquareDiagramMap _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction
  rw [Category.assoc, ← NatTrans.comp_app, ← pre_map]
  congr 2
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- Slice の四角形表示は元の cospan を固定する。 -/
lemma sliceSquareDiagramMap_fixed {X : SSet.{u}} (p : (horn 2 2 : SSet.{u}) ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.sliceSquareDiagramMap p ≫ (pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary).app X =
      SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p) := by
  rw [sliceSquareDiagramMap_restriction, sliceConeDiagramMap_restriction]

/-- Cospan の共通終点の指定頂点。 -/
def cospanTargetVertex : (horn 2 2 : SSet.{u}) _⦋0⦌ :=
  horn₂₂.ι₀₂.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (1 : Fin 2))

/-- Cospan の終点は正方形の終点へ写る。 -/
lemma cospanSquareBoundary_targetVertex :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary.app (Opposite.op ⦋0⦌) cospanTargetVertex =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (𝟙 ((Δ[1] : SSet.{u}) ⊗ Δ[1])) 1 1 := by
  have h := congrArg (fun q => q.app (Opposite.op ⦋0⦌)
    (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary_rightEdge.{u}
  exact h.trans (by apply Prod.ext <;> decide)

/-- Slice の四角形表示の終点評価は cospan の共通終点に定値。 -/
lemma sliceSquareDiagramMap_targetEvaluation {X : SSet.{u}}
    (p : (horn 2 2 : SSet.{u}) ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.sliceSquareDiagramMap p ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X)
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (𝟙 ((Δ[1] : SSet.{u}) ⊗ Δ[1])) 1 1) =
      SSet.const (p.app (Opposite.op ⦋0⦌) cospanTargetVertex) := by
  have he := _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.stable_pre_evaluateFunctorAt (X := X) _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary cospanTargetVertex
  rw [cospanSquareBoundary_targetVertex] at he
  rw [← he, ← Category.assoc, sliceSquareDiagramMap_fixed, SSet.const_comp,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex]

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
