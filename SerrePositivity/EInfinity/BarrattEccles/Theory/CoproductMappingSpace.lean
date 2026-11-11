module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.CoproductFrameHom
public import SerrePositivity.EInfinity.BarrattEccles.MappingSpaceTargetComparison
public import SerrePositivity.EInfinity.BarrattEccles.Theory.AnodyneBinaryProducts

/-!
# 導来写像空間の二包含による積比較

概要：HA 3.2.4.7 の余積の全 Hom の積比較を、実際の Map^h について示す。
方針：指定した余積 frame の比較と、両変数に自然な終域置換の比較を消去する。
規約：単体集合のモデル構造を要求せず、同じ二包含による前合成を使う。
使われ方：native な二項余積錐の余極限性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Limits HomotopicalAlgebra Opposite MonoidalCategory
open SerrePositivity.Reedy SerrePositivity.HomotopyFunctionComplex SerrePositivity.SimplicialModel
variable (A : Type u) [CommRing A]

/-- 二変数の単体集合の積は anodyne 局所化の同型を保つ。 -/
lemma binaryProduct_map_anodyneQ_isIso {B B' D D' : SSet.{u}}
    (f : B ⟶ B') (g : D ⟶ D')
    (hf : IsIso (AnodyneHomotopy.anodyneQ.map f))
    (hg : IsIso (AnodyneHomotopy.anodyneQ.map g)) :
    IsIso (AnodyneHomotopy.anodyneQ.map (prod.map f g)) := by
  let Q := AnodyneHomotopy.anodyneQ
  have := hf
  have := hg
  have he := Limits.prodComparison_natural Q f g
  have h : IsIso (Q.map (prod.map f g) ≫ prodComparison Q B' D') := by
    rw [he]
    infer_instance
  exact (isIso_comp_right_iff _ _).mp h

/-- 同じ分解の始域射による二項の制限。 -/
def sourceFrameCoprodRestriction (X Y Z : (operad A).Algebra) :
    ((sourceFrameHom A).obj (op (X ⨿ Y))).obj Z ⟶
      ((sourceFrameHom A).obj (op X)).obj Z ⨯ ((sourceFrameHom A).obj (op Y)).obj Z :=
  prod.lift (((sourceFrameHom A).map coprod.inl.op).app Z)
    (((sourceFrameHom A).map coprod.inr.op).app Z)

/-- 実際の指定包含による frame Hom の積比較は局所化で同型。 -/
lemma sourceFrameCoprodRestriction_isIso (X Y Z : (operad A).Algebra)
    (hX : let := modelCategory A; IsCofibrant X)
    (hY : let := modelCategory A; IsCofibrant Y) :
    IsIso (AnodyneHomotopy.anodyneQ.map (sourceFrameCoprodRestriction A X Y Z)) := by
  let := modelCategory A
  let q := cosimplicialResolutionFamily (mappingCofibrantFactorization A)
  have : IsCofibrant X := hX
  have : IsCofibrant Y := hY
  have := isFibrant A Z
  have := coproductFrameComparison_hom_isIso q AnodyneHomotopy.anodyneQ
    SSet.anodyneExtensions.Q_inverts X Y Z
  have he : (cosimplicialHomMap (coproductFrameComparison q X Y)).app Z ≫
      coproductFrameHomRestriction (q.obj.obj X) (q.obj.obj Y) Z =
    sourceFrameCoprodRestriction A X Y Z := by
    apply prod.hom_ext
    · calc
        _ = (cosimplicialHomMap (coproductFrameComparison q X Y)).app Z ≫
            (cosimplicialHomMap (coprod.inl : q.obj.obj X ⟶ q.obj.obj X ⨿ q.obj.obj Y)).app Z :=
          (Category.assoc _ _ _).trans (congrArg (fun k =>
            (cosimplicialHomMap (coproductFrameComparison q X Y)).app Z ≫ k)
              (prod.lift_fst
                ((cosimplicialHomMap
                  (coprod.inl : q.obj.obj X ⟶ q.obj.obj X ⨿ q.obj.obj Y)).app Z)
                ((cosimplicialHomMap
                  (coprod.inr : q.obj.obj Y ⟶ q.obj.obj X ⨿ q.obj.obj Y)).app Z)))
        _ = ((sourceFrameHom A).map (coprod.inl : X ⟶ X ⨿ Y).op).app Z := by
          ext n f
          change ((coprod.inl : q.obj.obj X ⟶ q.obj.obj X ⨿ q.obj.obj Y).app n.unop ≫
            (coproductFrameComparison q X Y).app n.unop) ≫ f = _
          rw [← NatTrans.comp_app, coproductFrameComparison_inl]
          rfl
        _ = _ := (prod.lift_fst
          (((sourceFrameHom A).map (coprod.inl : X ⟶ X ⨿ Y).op).app Z)
          (((sourceFrameHom A).map (coprod.inr : Y ⟶ X ⨿ Y).op).app Z)).symm
    · calc
        _ = (cosimplicialHomMap (coproductFrameComparison q X Y)).app Z ≫
            (cosimplicialHomMap (coprod.inr : q.obj.obj Y ⟶ q.obj.obj X ⨿ q.obj.obj Y)).app Z :=
          (Category.assoc _ _ _).trans (congrArg (fun k =>
            (cosimplicialHomMap (coproductFrameComparison q X Y)).app Z ≫ k)
              (prod.lift_snd
                ((cosimplicialHomMap
                  (coprod.inl : q.obj.obj X ⟶ q.obj.obj X ⨿ q.obj.obj Y)).app Z)
                ((cosimplicialHomMap
                  (coprod.inr : q.obj.obj Y ⟶ q.obj.obj X ⨿ q.obj.obj Y)).app Z)))
        _ = ((sourceFrameHom A).map (coprod.inr : Y ⟶ X ⨿ Y).op).app Z := by
          ext n f
          change ((coprod.inr : q.obj.obj Y ⟶ q.obj.obj X ⨿ q.obj.obj Y).app n.unop ≫
            (coproductFrameComparison q X Y).app n.unop) ≫ f = _
          rw [← NatTrans.comp_app, coproductFrameComparison_inr]
          rfl
        _ = _ := (prod.lift_snd
          (((sourceFrameHom A).map (coprod.inl : X ⟶ X ⨿ Y).op).app Z)
          (((sourceFrameHom A).map (coprod.inr : Y ⟶ X ⨿ Y).op).app Z)).symm
  rw [← he, Functor.map_comp]
  infer_instance

/-- 選んだ Map^h の同じ二包含による制限射。 -/
def mappingSpaceCoprodRestriction (X Y Z : (operad A).Algebra) :
    ((mappingSpace A).obj (op (X ⨿ Y))).obj Z ⟶
      ((mappingSpace A).obj (op X)).obj Z ⨯ ((mappingSpace A).obj (op Y)).obj Z :=
  prod.lift (((mappingSpace A).map coprod.inl.op).app Z)
    (((mappingSpace A).map coprod.inr.op).app Z)

/-- Cofibrant な余積の Map^h の指定積比較は局所化で同型。 -/
lemma mappingSpaceCoprodRestriction_isIso (X Y Z : (operad A).Algebra)
    (hX : let := modelCategory A; IsCofibrant X)
    (hY : let := modelCategory A; IsCofibrant Y) :
    IsIso (AnodyneHomotopy.anodyneQ.map (mappingSpaceCoprodRestriction A X Y Z)) := by
  let Q := AnodyneHomotopy.anodyneQ
  let c := sourceFrameHomComparison A
  have hX' := sourceFrameHomComparison_isIso A Q SSet.anodyneExtensions.Q_inverts (op X) Z
  have hY' := sourceFrameHomComparison_isIso A Q SSet.anodyneExtensions.Q_inverts (op Y) Z
  have := sourceFrameHomComparison_isIso A Q SSet.anodyneExtensions.Q_inverts (op (X ⨿ Y)) Z
  have := binaryProduct_map_anodyneQ_isIso ((c.app (op X)).app Z) ((c.app (op Y)).app Z) hX' hY'
  have := sourceFrameCoprodRestriction_isIso A X Y Z hX hY
  have he : (c.app (op (X ⨿ Y))).app Z ≫ mappingSpaceCoprodRestriction A X Y Z =
      sourceFrameCoprodRestriction A X Y Z ≫
        prod.map ((c.app (op X)).app Z) ((c.app (op Y)).app Z) := by
    apply prod.hom_ext
    · simpa only [mappingSpaceCoprodRestriction, sourceFrameCoprodRestriction,
        NatTrans.comp_app, Category.assoc, prod.lift_fst, prod.map_fst, prod.lift_fst_assoc] using
        (NatTrans.congr_app (c.naturality (coprod.inl : X ⟶ X ⨿ Y).op) Z).symm
    · simpa only [mappingSpaceCoprodRestriction, sourceFrameCoprodRestriction,
        NatTrans.comp_app, Category.assoc, prod.lift_snd, prod.map_snd, prod.lift_snd_assoc] using
        (NatTrans.congr_app (c.naturality (coprod.inr : Y ⟶ X ⨿ Y).op) Z).symm
  have he' := congrArg Q.map he
  simp only [Functor.map_comp] at he'
  have hh : IsIso (Q.map ((c.app (op (X ⨿ Y))).app Z) ≫
      Q.map (mappingSpaceCoprodRestriction A X Y Z)) := by
    rw [he']
    infer_instance
  exact (isIso_comp_left_iff _ _).mp hh

end SerrePositivity.EInfinity.BarrattEccles
