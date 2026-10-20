module
public import SerrePositivity.InfinityCategories.Derived.DGActualRoofFiberReduction

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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (P : Set D) (x y : D) {L K : SSet.{max u v}}
variable {i : L ⟶ K} {a : L ⟶ dgRoofCorrespondence A D P x y}
variable {g : K ⟶ dgQuotientRoofCorrespondence A D P x y}
variable (R : DGActualRoofFiberReduction A D P x y i a g)

/-- 還元後の元境界の実 pinched Hom 係数。 -/
def dgActualRoofSourceCoefficient : L ⟶
    DGNerve.pinchedHom A D (dgOverVertexSource A D x R.cone.vertex.val) y :=
  R.boundary ≫ (dgRoofCorrespondenceFiberIso A D P x y R.cone.vertex).hom

/-- 還元後の商図式の実 pinched Hom 係数。 -/
def dgActualRoofTargetCoefficient : K ⟶
    DGNerve.pinchedHom A (DGQuotient.QuotientObject D P)
      ((DGQuotient.inclusion A D P).obj (dgOverVertexSource A D x R.cone.vertex.val))
      ((DGQuotient.inclusion A D P).obj y) :=
  R.target ≫ (dgQuotientRoofCorrespondenceFiberIso A D P x y R.cone.vertex).hom

/-- 還元後の元・商の実係数は、元の Hom 鎖写像上で厳密な相対問題をなす。 -/
lemma dgActualRoofCoefficient_square :
    dgActualRoofSourceCoefficient A D P x y R ≫
      pinchedHomChainMap ((DGQuotient.inclusion A D P).map
        (dgOverVertexSource A D x R.cone.vertex.val) y) =
      i ≫ dgActualRoofTargetCoefficient A D P x y R := by
  change (R.boundary ≫ (dgRoofCorrespondenceFiberIso A D P x y R.cone.vertex).hom) ≫ _ = _
  rw [Category.assoc, ← dgRoofCorrespondenceFiberMap_comparison, ← Category.assoc]
  have h := R.square (dgRoofCorrespondenceMap_projection A D P x y)
  change R.boundary ≫ dgRoofCorrespondenceFiberMap A D P x y R.cone.vertex = i ≫ R.target at h
  rw [h, Category.assoc]
  rfl

end SerrePositivity.InfinityCategories
