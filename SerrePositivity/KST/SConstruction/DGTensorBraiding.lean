module
public import SerrePositivity.KST.SConstruction.DGTensorBraidingLaws
public import SerrePositivity.DifferentialGraded.Category.Tensor

/-! # 元の tensor dg 圏の符号つき交換関手
概要：二つの tensor 因子を交換し、元の Hom の signed braiding で厳密 dg 関手を作る。
方針：対称 monoidal 基底で交換と合成の式を証明し、複体へ適用する。
規約：Koszul 符号を保ち、小ささは要求しない。使われ方：二回の tensor dg 作用の順序。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory HomologicalComplex SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (C : Type v) (D : Type w)
  [DGCategory A C] [DGCategory A D]

/-- 元の二つの Hom 複体の signed braiding を、交換した対象間の Hom として読む。 -/
def dgTensorBraidingHom (x y : DGTensorCategory A C D) :
    homObject A C x.1 y.1 ⊗ homObject A D x.2 y.2 ⟶
      homObject A D x.2 y.2 ⊗ homObject A C x.1 y.1 :=
  (β_ (homObject A C x.1 y.1) (homObject A D x.2 y.2)).hom

/-- 元の交換 Hom の純斉次成分は、同じ二次数の Koszul 符号を保持する。 -/
lemma dgTensorBraidingHom_apply {x y : DGTensorCategory A C D} {p q n : ℤ}
    (a : GradedHom A x.1 y.1 p) (b : GradedHom A x.2 y.2 q) (hn : p + q = n) :
    (dgTensorBraidingHom A C D x y).f n (dgTensorElement A a b hn) =
      (p * q).negOnePow • dgTensorElement A
        (x := ((x.2, x.1) : DGTensorCategory A D C))
        (y := ((y.2, y.1) : DGTensorCategory A D C)) b a (by omega) :=
  signedSwap_apply _ _ p q n hn a b

/-- 元の二つの閉単位の交換は、交換後の同じ閉単位。 -/
lemma dgTensorBraidingHom_identity (x : DGTensorCategory A C D) :
    eId (Complex A) x ≫ dgTensorBraidingHom A C D x x =
      eId (C := DGTensorCategory A D C) (Complex A) (x.2, x.1) := by
  dsimp only [dgTensorBraidingHom]
  simp only [dgTensor_identity]
  exact dgTensorBraiding_unit (eId (Complex A) x.1) (eId (Complex A) x.2)

/-- 元の signed braiding は tensor dg 圏の全次数合成を保持する。 -/
lemma dgTensorBraidingHom_composition (x y z : DGTensorCategory A C D) :
    eComp (Complex A) x y z ≫ dgTensorBraidingHom A C D x z =
      (dgTensorBraidingHom A C D x y ⊗ₘ dgTensorBraidingHom A C D y z) ≫
        eComp (C := DGTensorCategory A D C) (Complex A) (x.2, x.1) (y.2, y.1) (z.2, z.1) := by
  dsimp only [dgTensorBraidingHom]
  simp only [dgTensor_composition, dgTensor_hom, homObject, Category.assoc]
  erw [dgTensorBraiding_composition]

/-- 元の対象の組と全 Hom の signed braiding による、厳密 dg 交換関手。 -/
def dgTensorBraiding : DGFunctor A (DGTensorCategory A C D) (DGTensorCategory A D C) where
  obj x := (x.2, x.1)
  map := dgTensorBraidingHom A C D
  map_id := dgTensorBraidingHom_identity A C D
  map_comp := dgTensorBraidingHom_composition A C D

/-- dg 交換関手は元の signed Hom 作用を厳密に回収する。 -/
lemma dgTensorBraiding_map (x y : DGTensorCategory A C D) :
    (dgTensorBraiding A C D).map x y = dgTensorBraidingHom A C D x y := rfl

end SerrePositivity.KST.SConstruction
