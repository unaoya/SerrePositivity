module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.DGActualRoofFiberReduction

/-! # 共通 fiber 還元後の実 pinched Hom 係数

概要：相対屋根問題の還元を、同じ始対象からの元・商の実 pinched Hom 上に表示する。
方針：二つの fiber 同型で移し、比較の共役公式で厳密な相対正方形を得る。
規約：全次数の実単体写像。使われ方：商係数の有限相対充填への入力。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable (P : Set D) (x y : D) {L K : SSet.{max u v}}
variable {i : L ⟶ K} {a : L ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondence A D P x y}
variable {g : K ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientRoofCorrespondence A D P x y}
variable (R : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGActualRoofFiberReduction A D P x y i a g)

/-- 還元後の元境界の実 pinched Hom 係数。 -/
def dgActualRoofSourceCoefficient : L ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOverVertexSource A D x R.cone.vertex.val) y :=
  R.boundary ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceFiberIso A D P x y R.cone.vertex).hom

/-- 還元後の商図式の実 pinched Hom 係数。 -/
def dgActualRoofTargetCoefficient : K ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A (DGQuotient.QuotientObject D P)
      ((DGQuotient.inclusion A D P).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOverVertexSource A D x R.cone.vertex.val))
      ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y) :=
  R.target ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientRoofCorrespondenceFiberIso A D P x y R.cone.vertex).hom

/-- 還元後の元・商の実係数は、元の Hom 鎖写像上で厳密な相対問題をなす。 -/
lemma dgActualRoofCoefficient_square :
    dgActualRoofSourceCoefficient A D P x y R ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap ((DGQuotient.inclusion A D P).map
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOverVertexSource A D x R.cone.vertex.val) y) =
      i ≫ dgActualRoofTargetCoefficient A D P x y R := by
  change (R.boundary ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceFiberIso A D P x y R.cone.vertex).hom) ≫ _ = _
  rw [Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceFiberMap_comparison, ← Category.assoc]
  have h := R.square (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceMap_projection A D P x y)
  change R.boundary ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceFiberMap A D P x y R.cone.vertex = i ≫ R.target at h
  rw [h, Category.assoc]
  rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories
