module

public import SerrePositivity.EInfinity.BarrattEccles.CofibrantSourceFrameHom
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic

/-!
# 元の sourceFrameHom の反対要素圏と DK frame の固定終域の矢

概要：元の全単体・全作用素を AsSmall Δ と Hom ULift の同じ表示へ移す。
方針：次数の上げ下げと全部分圏の homMk・hom を厳密に逆にする。
規約：元の frame・元の代数射・指定終域を保持する。
使われ方：既存の source frame 弱比較と実屋根比較の始域の一致。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Opposite

variable (A : Type u) [CommRing A] (X Y : CofibrantAlgebra A)

abbrev sourceFrameElementCategory :=
  ULiftHom.{u + 1} (((((sourceFrameHom A).obj (op X.obj)).obj Y.obj).Elements)ᵒᵖ)

def sourceFrameElementsToDK : sourceFrameElementCategory A X Y ⥤
    CostructuredArrow (cofibrantDKSourceFrame A X)
      (show (cofibrantAlgebraRelativeCategory A).category from Y) where
  obj s := by
    let t : (((sourceFrameHom A).obj (op X.obj)).obj Y.obj).Elementsᵒᵖ :=
      ULiftHom.objDown s
    exact
      { left := ⟨t.unop.obj.unop⟩
        right := ⟨⟨⟩⟩
        hom := ⟨ObjectProperty.homMk t.unop.val⟩ }
  map f := by
    let a := ULift.down f
    exact CostructuredArrow.homMk ⟨a.unop.hom.unop⟩ (by
      apply ULift.ext
      apply ObjectProperty.hom_ext
      exact a.unop.map_val)

def sourceFrameDKToElements :
    CostructuredArrow (cofibrantDKSourceFrame A X)
      (show (cofibrantAlgebraRelativeCategory A).category from Y) ⥤
        sourceFrameElementCategory A X Y where
  obj s := ULiftHom.objUp (op (Functor.elementsMk _ (op (ULift.down s.left))
    (ULift.down s.hom).hom))
  map {s t} f := ⟨Quiver.Hom.op
    { hom := (ULift.down f.left).op
      map_val := by
        exact congrArg (fun g : (cofibrantDKSourceFrame A X).obj s.left ⟶
          (show (cofibrantAlgebraRelativeCategory A).category from Y) =>
            (ULift.down g).hom) (CostructuredArrow.w f) }⟩

def sourceFrameElementsDKEquivalence : sourceFrameElementCategory A X Y ≌
    CostructuredArrow (cofibrantDKSourceFrame A X)
      (show (cofibrantAlgebraRelativeCategory A).category from Y) where
  functor := sourceFrameElementsToDK A X Y
  inverse := sourceFrameDKToElements A X Y
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)
  counitIso := NatIso.ofComponents (fun _ => CostructuredArrow.isoMk (Iso.refl _))

lemma sourceFrameElementsToDK_degree (s : sourceFrameElementCategory A X Y) :
    ULift.down ((sourceFrameElementsToDK A X Y).obj s).left =
      (show (((sourceFrameHom A).obj (op X.obj)).obj Y.obj).Elementsᵒᵖ from
        ULiftHom.objDown s).unop.obj.unop := rfl

lemma sourceFrameElementsToDK_arrow (s : sourceFrameElementCategory A X Y) :
    (ULift.down ((sourceFrameElementsToDK A X Y).obj s).hom).hom =
      (show (((sourceFrameHom A).obj (op X.obj)).obj Y.obj).Elementsᵒᵖ from
        ULiftHom.objDown s).unop.val := rfl

lemma sourceFrameElementsToDK_inverse : sourceFrameElementsToDK A X Y ⋙
    sourceFrameDKToElements A X Y = 𝟭 (sourceFrameElementCategory A X Y) := rfl

lemma sourceFrameDKToElements_inverse : sourceFrameDKToElements A X Y ⋙
    sourceFrameElementsToDK A X Y = 𝟭 _ := rfl

def sourceFrameElementDegree : sourceFrameElementCategory A X Y ⥤
    AsSmall.{u + 1} SimplexCategory where
  obj s := ⟨(ULiftHom.objDown s).unop.obj.unop⟩
  map f := ⟨(ULift.down f).unop.hom.unop⟩

def sourceFrameElementsDKNerveIso : nerve (sourceFrameElementCategory A X Y) ≅
    nerve (CostructuredArrow (cofibrantDKSourceFrame A X)
      (show (cofibrantAlgebraRelativeCategory A).category from Y)) where
  hom := { app _ := ↾fun σ => σ ⋙ sourceFrameElementsToDK A X Y
           naturality _ _ _ := rfl }
  inv := { app _ := ↾fun σ => σ ⋙ sourceFrameDKToElements A X Y
           naturality _ _ _ := rfl }
  hom_inv_id := rfl
  inv_hom_id := rfl

def sourceFrameElementDegreeNerve : nerve (sourceFrameElementCategory A X Y) ⟶
    nerve (AsSmall.{u + 1} SimplexCategory) where
  app _ := ↾fun σ => σ ⋙ sourceFrameElementDegree A X Y
  naturality _ _ _ := rfl

end SerrePositivity.EInfinity.BarrattEccles
