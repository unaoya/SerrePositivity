module
public import SerrePositivity.KST.SConstruction.MultiFixedSInterchangeIndex

/-! # 独立な全方向を動かす S の内外交換
概要：先頭添字の S を最内側に置く図式と最外側に置く図式を自然同型で比較する。
方針：残りの全多次数の自然性と先頭の次数変更の自然性を合成する。
規約：全多次数で元の交換成分を使う。使われ方：巡回交換の各零方向の制御。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
attribute [local instance] CategoryTheory.endofunctorMonoidalCategory

/-- 全多次数の先頭の S の自己関手。 -/
def multiHeadSEndofunctor (r : ℕ) :
    (Fin (r + 1) → SimplexCategoryᵒᵖ) ⥤ (StableModel.{u} ⥤ StableModel.{u}) :=
  Pi.eval (fun _ : Fin (r + 1) => SimplexCategoryᵒᵖ) 0 ⋙ simplicialStableEndofunctor

/-- 全多次数の先頭を除いた反復 S の自己関手。 -/
def multiTailSEndofunctor (r : ℕ) :
    (Fin (r + 1) → SimplexCategoryᵒᵖ) ⥤ (StableModel.{u} ⥤ StableModel.{u}) :=
  Pi.comap (fun _ : Fin (r + 1) => SimplexCategoryᵒᵖ) Fin.succ ⋙ multiSEndofunctor r

/-- 先頭添字の S を最内側に置く全多単体的な自己関手。 -/
def multiInnerSEndofunctor (r : ℕ) :
    (Fin (r + 1) → SimplexCategoryᵒᵖ) ⥤ (StableModel.{u} ⥤ StableModel.{u}) :=
  multiHeadSEndofunctor r ⊗ multiTailSEndofunctor r

/-- 全方向を独立に動かす、最内側の S と最外側の S の交換同型。 -/
def multiMovingSInterchangeNatIso (r : ℕ) :
    multiInnerSEndofunctor.{u} r ≅ multiTailSEndofunctor r ⊗ multiHeadSEndofunctor r :=
  NatIso.ofComponents (fun d => multiFixedSEndofunctorIso (d 0).unop.len r
    (fun i => d i.succ)) (by
      intro d e f
      apply NatTrans.ext
      funext X
      let D := (multiSEndofunctor r).obj (fun i => d i.succ)
      let E := (multiSEndofunctor r).obj (fun i => e i.succ)
      let t := (multiSEndofunctor r).map (fun i => f i.succ)
      let a := simplicialStableEndofunctor.map (f 0)
      let b := (multiFixedSEndofunctorIso (d 0).unop.len r (fun i => d i.succ)).hom.app X
      let c := (multiFixedSEndofunctorIso (d 0).unop.len r (fun i => e i.succ)).hom.app X
      let c' := (multiFixedSEndofunctorIso (e 0).unop.len r (fun i => e i.succ)).hom.app X
      have ht : t.app ((sEndofunctor (d 0).unop.len).obj X) ≫ c =
          b ≫ (sEndofunctor (d 0).unop.len).map (t.app X) :=
        multiFixedSEndofunctorIso_naturality (d 0).unop.len r (fun i => f i.succ) X
      have hi : E.map (a.app X) ≫ c' = c ≫ a.app (E.obj X) :=
        multiFixedSEndofunctorIso_index r (fun i => e i.succ) X (f 0).unop.toOrderHom
      have ha : (sEndofunctor (d 0).unop.len).map (t.app X) ≫ a.app (E.obj X) =
          a.app (D.obj X) ≫ (sEndofunctor (e 0).unop.len).map (t.app X) := a.naturality _
      change (((multiHeadSEndofunctor r).map f ⊗ₘ (multiTailSEndofunctor r).map f) ≫
        (multiFixedSEndofunctorIso (e 0).unop.len r (fun i => e i.succ)).hom).app X =
        ((multiFixedSEndofunctorIso (d 0).unop.len r (fun i => d i.succ)).hom ≫
          ((multiTailSEndofunctor r).map f ⊗ₘ (multiHeadSEndofunctor r).map f)).app X
      simp only [NatTrans.comp_app, endofunctorMonoidalCategory_tensorMap_app]
      change (t.app ((sEndofunctor (d 0).unop.len).obj X) ≫ E.map (a.app X)) ≫ c' =
        b ≫ (a.app (D.obj X) ≫ (sEndofunctor (e 0).unop.len).map (t.app X))
      rw [Category.assoc, hi, ← Category.assoc, ht, Category.assoc, ha])

end SerrePositivity.KST.SConstruction
