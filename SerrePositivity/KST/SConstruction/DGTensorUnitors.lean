module
public import SerrePositivity.KST.SConstruction.DGTensorUnitorLaws
public import SerrePositivity.DifferentialGraded.Category.Tensor
public import SerrePositivity.DifferentialGraded.Category.Basic
public import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence

/-! # 一対象 A との実 dg tensor の左右単位関手
概要：元の単位複体との左右単位写像を、元の dg 圏への実 dg 関手へ束ねる。
方針：対象は元の第二・第一成分、Hom は元の左右単位とし単位・合成保存を照合する。
規約：既存の一対象 A と実 dg tensor を使う。使われ方：Λ の oplax 単位則。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (C : Type v) [DGCategory A C]

/-- 元の左単位写像を、元の実 dg tensor の Hom を source に持つ射として固定する。 -/
def dgTensorLeftUnitorHom (x y : DGTensorCategory A PUnit.{1} C) :
    (x ⟶[Complex A] y) ⟶ homObject A C x.2 y.2 :=
  (λ_ (homObject A C x.2 y.2)).hom

/-- 元の右単位写像を、元の実 dg tensor の Hom を source に持つ射として固定する。 -/
def dgTensorRightUnitorHom (x y : DGTensorCategory A C PUnit.{1}) :
    (x ⟶[Complex A] y) ⟶ homObject A C x.1 y.1 :=
  (ρ_ (homObject A C x.1 y.1)).hom

/-- 元の左単位写像は、元の実 dg tensor の単位を保持する。 -/
lemma dgTensorLeftUnitor_identity (x : DGTensorCategory A PUnit.{1} C) :
    eId (Complex A) x ≫ dgTensorLeftUnitorHom A C x x =
      eId (Complex A) (C := C) x.2 :=
  dgTensorUnitor_left_unit (eId (Complex A) (C := C) x.2)

/-- 元の左単位写像は、元の実 dg tensor の合成を保持する。 -/
lemma dgTensorLeftUnitor_composition (x y z : DGTensorCategory A PUnit.{1} C) :
    eComp (Complex A) x y z ≫ dgTensorLeftUnitorHom A C x z =
      (dgTensorLeftUnitorHom A C x y ⊗ₘ dgTensorLeftUnitorHom A C y z) ≫
        eComp (Complex A) (C := C) x.2 y.2 z.2 := by
  rw [dgTensor_composition A PUnit.{1} C x y z]
  exact dgTensorUnitor_left_composition
    (X := homObject A C x.2 y.2) (Y := homObject A C y.2 z.2)
    (Z := homObject A C x.2 z.2) (eComp (Complex A) (C := C) x.2 y.2 z.2)

/-- 元の右単位写像は、元の実 dg tensor の単位を保持する。 -/
lemma dgTensorRightUnitor_identity (x : DGTensorCategory A C PUnit.{1}) :
    eId (Complex A) x ≫ dgTensorRightUnitorHom A C x x =
      eId (Complex A) (C := C) x.1 :=
  dgTensorUnitor_right_unit (eId (Complex A) (C := C) x.1)

/-- 元の右単位写像は、元の実 dg tensor の合成を保持する。 -/
lemma dgTensorRightUnitor_composition (x y z : DGTensorCategory A C PUnit.{1}) :
    eComp (Complex A) x y z ≫ dgTensorRightUnitorHom A C x z =
      (dgTensorRightUnitorHom A C x y ⊗ₘ dgTensorRightUnitorHom A C y z) ≫
        eComp (Complex A) (C := C) x.1 y.1 z.1 := by
  rw [dgTensor_composition A C PUnit.{1} x y z]
  exact dgTensorUnitor_right_composition
    (X := homObject A C x.1 y.1) (Y := homObject A C y.1 z.1)
    (Z := homObject A C x.1 z.1) (eComp (Complex A) (C := C) x.1 y.1 z.1)

/-- 元の一対象 A と dg 圏の実 tensor から、元の Hom の左単位で戻す dg 関手。 -/
def dgTensorLeftUnitor : DGFunctor A (DGTensorCategory A PUnit.{1} C) C where
  obj x := x.2
  map := dgTensorLeftUnitorHom A C
  map_id x := dgTensorLeftUnitor_identity A C x
  map_comp x y z := dgTensorLeftUnitor_composition A C x y z

/-- 元の dg 圏と一対象 A の実 tensor から、元の Hom の右単位で戻す dg 関手。 -/
def dgTensorRightUnitor : DGFunctor A (DGTensorCategory A C PUnit.{1}) C where
  obj x := x.1
  map := dgTensorRightUnitorHom A C
  map_id x := dgTensorRightUnitor_identity A C x
  map_comp x y z := dgTensorRightUnitor_composition A C x y z

/-- 元の左単位 dg 関手の対象作用は元の第二射影。 -/
lemma dgTensorLeftUnitor_obj (x : DGTensorCategory A PUnit.{1} C) :
    (dgTensorLeftUnitor A C).obj x = x.2 := rfl

/-- 元の右単位 dg 関手の対象作用は元の第一射影。 -/
lemma dgTensorRightUnitor_obj (x : DGTensorCategory A C PUnit.{1}) :
    (dgTensorRightUnitor A C).obj x = x.1 := rfl

/-- 元の左単位 dg 関手の Hom 作用は元の Hom の左単位そのもの。 -/
lemma dgTensorLeftUnitor_map (x y : DGTensorCategory A PUnit.{1} C) :
    (dgTensorLeftUnitor A C).map x y = (λ_ (homObject A C x.2 y.2)).hom := rfl

/-- 元の右単位 dg 関手の Hom 作用は元の Hom の右単位そのもの。 -/
lemma dgTensorRightUnitor_map (x y : DGTensorCategory A C PUnit.{1}) :
    (dgTensorRightUnitor A C).map x y = (ρ_ (homObject A C x.1 y.1)).hom := rfl

end SerrePositivity.KST.SConstruction
