module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFiniteOreRefinement
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PinchedClosedStandardConstant
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHomCompositionHomotopy

/-! # 有限実 Ore 細分の同じホモトピーと全次元 AW 合成

概要：実分母細分のホモトピーを、同じ二実閉辺の定数族との AW 合成の比較に直す。
方針：全次元の実閉前後合成の等式で端点だけを輸送する。
規約：円柱上の写像は元の実 Ore ホモトピーと厳密に同じ。
使われ方：実屋根の合成三角形の高次パラメータ化の入力。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable (P : Set D) {K : SSet.{max u v}} {x y z : D}
variable {f : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y}
variable {s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) z ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) y}
variable (R : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFiniteOreRefinement A D P f s)

/-- 同じ実 Ore ホモトピーを、指定実閉辺の定数族との二 AW 合成の比較として表示する。 -/
def DGFiniteOreRefinement.compositionHomotopy : SSet.Homotopy
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomCompositionFamily (SSet.const (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex A D R.combinedDenominator)) f)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomCompositionFamily R.lift (SSet.const (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex A D s))) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHomotopyRetarget R.combinedHomotopy
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomCompositionFamily_closed_pre A D R.combinedDenominator f).symm
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomCompositionFamily_closed_post A D R.lift s).symm

/-- AW 端点への輸送は、実 Ore 比較の円柱上の写像を全時刻で変えない。 -/
lemma DGFiniteOreRefinement.compositionHomotopy_h :
    R.compositionHomotopy.h = R.combinedHomotopy.h :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.homotopyRetarget_h _ _ _

end SerrePositivity.InfinityCategories.Project.DerivedCategories
