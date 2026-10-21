module
public import SerrePositivity.KST.SConstruction.DGFunctorHorizontalDG
public import SerrePositivity.KST.SConstruction.DGFunctorHorizontalAssociativity
public import SerrePositivity.KST.SConstruction.DGTensorAssociator

/-! # 元の tensor dg 横合成関手の結合等号
概要：三つの関手圏からの実 tensor dg 横合成の二経路を、同じ dg 関手として比較する。
方針：対象は元の厳密 dg 合成の結合等号、全 Hom は元の等号移送付き横合成則を使う。
規約：同じ対象等号と全次数 Hom を保持。使われ方：native 直積横合成の結合則。
-/
@[expose] public section
noncomputable section
universe u v w z t
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) (E : Type w) (B : Type z) (T : Type t)
  [DGCategory A D] [DGCategory A E] [DGCategory A B] [DGCategory A T]
  [Small.{u} D] [Small.{u} E] [Small.{u} B]

/-- 元の横合成を左の二因子から適用する実 dg 関手。 -/
def dgFunctorHorizontalLeftDG :
    DGFunctor A (DGTensorCategory A (DGTensorCategory A (DGFunctor A D E) (DGFunctor A E B))
      (DGFunctor A B T)) (DGFunctor A D T) :=
    DGFunctor.comp
        (dgTensorFunctor A (dgFunctorHorizontalDG A D E B) (DGFunctor.id (DGFunctor A B T)))
        (dgFunctorHorizontalDG A D B T)

/-- 右の二因子から横合成する、右括弧を源に持つ実 dg 関手。 -/
def dgFunctorHorizontalRightInnerDG :
    DGFunctor A (DGTensorCategory A (DGFunctor A D E)
      (DGTensorCategory A (DGFunctor A E B) (DGFunctor A B T))) (DGFunctor A D T) :=
  DGFunctor.comp
    (dgTensorFunctor A (DGFunctor.id (DGFunctor A D E)) (dgFunctorHorizontalDG A E B T))
    (dgFunctorHorizontalDG A D E T)

/-- 元の実 dg tensor の結合関手の後、右の二因子から横合成する実 dg 関手。 -/
def dgFunctorHorizontalRightDG :
    DGFunctor A (DGTensorCategory A (DGTensorCategory A (DGFunctor A D E) (DGFunctor A E B))
      (DGFunctor A B T)) (DGFunctor A D T) :=
  DGFunctor.comp
    (dgTensorAssociator A (DGFunctor A D E) (DGFunctor A E B) (DGFunctor A B T))
    (dgFunctorHorizontalRightInnerDG A D E B T)

/-- 右括弧からの経路の全 Hom は、元の二回の横合成 chain map。 -/
lemma dgFunctorHorizontalRightInnerDG_map
    (x y : DGTensorCategory A (DGFunctor A D E)
      (DGTensorCategory A (DGFunctor A E B) (DGFunctor A B T))) :
    (dgFunctorHorizontalRightInnerDG A D E B T).map x y =
      (𝟙 (dgFunctorHom A D E x.1 y.1) ⊗ₘ
        dgFunctorHorizontal A E B T x.2.1 y.2.1 x.2.2 y.2.2) ≫
        dgFunctorHorizontal A D E T x.1 y.1 (x.2.1.comp x.2.2) (y.2.1.comp y.2.2) := rfl

/-- 左からの実横合成経路の全 Hom は、元の二回の横合成 chain map。 -/
lemma dgFunctorHorizontalLeftDG_map
    (x y : DGTensorCategory A
      (DGTensorCategory A (DGFunctor A D E) (DGFunctor A E B)) (DGFunctor A B T)) :
    (dgFunctorHorizontalLeftDG A D E B T).map x y =
      (dgFunctorHorizontal A D E B x.1.1 y.1.1 x.1.2 y.1.2 ⊗ₘ
        𝟙 (dgFunctorHom A B T x.2 y.2)) ≫
        dgFunctorHorizontal A D B T (x.1.1.comp x.1.2) (y.1.1.comp y.1.2) x.2 y.2 := rfl

/-- 右からの実横合成経路の全 Hom は、元の結合射に続く二回の横合成。 -/
lemma dgFunctorHorizontalRightDG_map
    (x y : DGTensorCategory A
      (DGTensorCategory A (DGFunctor A D E) (DGFunctor A E B)) (DGFunctor A B T)) :
    (dgFunctorHorizontalRightDG A D E B T).map x y =
      (α_ (dgFunctorHom A D E x.1.1 y.1.1) (dgFunctorHom A E B x.1.2 y.1.2)
        (dgFunctorHom A B T x.2 y.2)).hom ≫
        ((𝟙 (dgFunctorHom A D E x.1.1 y.1.1) ⊗ₘ
          dgFunctorHorizontal A E B T x.1.2 y.1.2 x.2 y.2) ≫
          dgFunctorHorizontal A D E T x.1.1 y.1.1 (x.1.2.comp x.2) (y.1.2.comp y.2)) := by
  change (dgTensorAssociator A (DGFunctor A D E) (DGFunctor A E B)
    (DGFunctor A B T)).map x y ≫
    (dgFunctorHorizontalRightInnerDG A D E B T).map
      (x.1.1, (x.1.2, x.2)) (y.1.1, (y.1.2, y.2)) = _
  erw [dgFunctorHorizontalRightInnerDG_map]
  rfl

/-- 実 tensor dg 横合成の二回適用は、元の実 dg tensor 結合関手を介して一致する。 -/
lemma dgFunctorHorizontalDG_associativity :
    dgFunctorHorizontalLeftDG A D E B T = dgFunctorHorizontalRightDG A D E B T := by
  refine EnrichedFunctor.ext (Complex A)
    (F := dgFunctorHorizontalLeftDG A D E B T)
    (G := dgFunctorHorizontalRightDG A D E B T)
    (fun x => strictDGFunctor_comp_assoc x.1.1 x.1.2 x.2) ?_
  intro x y
  rw [dgFunctorHorizontalLeftDG_map, dgFunctorHorizontalRightDG_map]
  change ((dgFunctorHorizontal A D E B x.1.1 y.1.1 x.1.2 y.1.2 ⊗ₘ
      𝟙 (dgFunctorHom A B T x.2 y.2)) ≫
      dgFunctorHorizontal A D B T (x.1.1.comp x.1.2) (y.1.1.comp y.1.2) x.2 y.2) ≫
      dgFunctorHomTransport A D T (strictDGFunctor_comp_assoc x.1.1 x.1.2 x.2)
        (strictDGFunctor_comp_assoc y.1.1 y.1.2 y.2) =
    (α_ (dgFunctorHom A D E x.1.1 y.1.1) (dgFunctorHom A E B x.1.2 y.1.2)
      (dgFunctorHom A B T x.2 y.2)).hom ≫
      ((𝟙 (dgFunctorHom A D E x.1.1 y.1.1) ⊗ₘ
        dgFunctorHorizontal A E B T x.1.2 y.1.2 x.2 y.2) ≫
        dgFunctorHorizontal A D E T x.1.1 y.1.1 (x.1.2.comp x.2) (y.1.2.comp y.2))
  simpa only [tensorHom_id, id_tensorHom, Category.assoc] using
    dgFunctorHorizontal_assoc A D E B T x.1.1 y.1.1 x.1.2 y.1.2 x.2 y.2

end SerrePositivity.KST.SConstruction
