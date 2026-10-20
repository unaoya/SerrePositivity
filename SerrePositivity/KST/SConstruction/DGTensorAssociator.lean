module
public import SerrePositivity.KST.SConstruction.DGTensorFunctor
public import SerrePositivity.KST.SConstruction.DGTensorAssociatorLaws

/-! # 元の三重 tensor dg 圏の結合関手
概要：元の三つの Hom の結合写像により、三重 tensor dg 圏の間の厳密 dg 関手を作る。
方針：tensorμ の結合則と元の monoidal 結合写像の自然性で単位・合成を照合する。
規約：対象は組の括弧替え、Hom は元の結合写像。使われ方：二回の tensor dg 作用。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (C : Type v) (D : Type w) (E : Type z)
  [DGCategory A C] [DGCategory A D] [DGCategory A E]

/-- 元の三重 tensor dg 圏の括弧を、元の Hom の結合写像で右へ移す。 -/
def dgTensorAssociator :
    DGFunctor A (DGTensorCategory A (DGTensorCategory A C D) E)
      (DGTensorCategory A C (DGTensorCategory A D E)) where
  obj x := (x.1.1, (x.1.2, x.2))
  map x y := (α_ (homObject A C x.1.1 y.1.1) (homObject A D x.1.2 y.1.2)
    (homObject A E x.2 y.2)).hom
  map_id x := by
    simp only [dgTensor_identity]
    exact dgTensorAssociator_unit (eId (Complex A) x.1.1)
      (eId (Complex A) x.1.2) (eId (Complex A) x.2)
  map_comp x y z := by
    simp only [dgTensor_composition, dgTensor_hom, Category.assoc]
    erw [dgTensorAssociator_composition]

/-- 結合 dg 関手の全 Hom は、元の三つの Hom 複体の結合写像そのもの。 -/
lemma dgTensorAssociator_map
    (x y : DGTensorCategory A (DGTensorCategory A C D) E) :
    (dgTensorAssociator A C D E).map x y =
      (α_ (homObject A C x.1.1 y.1.1) (homObject A D x.1.2 y.1.2)
        (homObject A E x.2 y.2)).hom := rfl

end SerrePositivity.KST.SConstruction
