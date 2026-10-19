module
public import SerrePositivity.KST.SConstruction.InnerVariablePermutationMap
public import SerrePositivity.KST.SConstruction.MultiMovingSInterchange

/-! # 元の最内側の座標比較の全多単体的な自然性
概要：結合子による元の内側 S の比較を、巡回置換した全多単体図式への自然同型に束ねる。
方針：内側・外側それぞれの自然性と、元の添字作用の巡回置換との等号を合成する。
規約：S の転置とは別の元の結合子の比較。使われ方：旧座標比較下の全零境界の同定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
attribute [local instance] CategoryTheory.endofunctorMonoidalCategory

/-- 全多次数での、元の最内側 S と巡回置換した標準反復の座標同型。 -/
def multiInnerSCoordinateAt (r : ℕ) (d : Fin (r + 1) → SimplexCategoryᵒᵖ) :
    (multiInnerSEndofunctor.{u} r).obj d ≅
      (multiSEndofunctor (r + 1)).obj
        ((Pi.comap (fun _ : Fin (r + 1) => SimplexCategoryᵒᵖ) (finRotate (r + 1))).obj d) :=
  innerVariableSComparisonIso r (fun i => d i.succ) (d 0) ≪≫
    (multiSEndofunctor (r + 1)).mapIso (eqToIso (innerVariableIndex_obj_permutation r d))

/-- 元の座標同型は、内側と外側の全ての独立な作用素について自然。 -/
lemma multiInnerSCoordinateAt_naturality (r : ℕ)
    {d e : Fin (r + 1) → SimplexCategoryᵒᵖ} (f : d ⟶ e) (X : StableModel.{u}) :
    ((multiInnerSEndofunctor r).map f).app X ≫ (multiInnerSCoordinateAt r e).hom.app X =
      (multiInnerSCoordinateAt r d).hom.app X ≫
        ((multiSEndofunctor (r + 1)).map
          ((Pi.comap (fun _ : Fin (r + 1) => SimplexCategoryᵒᵖ)
            (finRotate (r + 1))).map f)).app X := by
  let T := multiSEndofunctor.{u} (r + 1)
  let E := (multiSEndofunctor r).obj (fun i => e i.succ)
  let a := simplicialStableEndofunctor.map (f 0)
  let t := (multiSEndofunctor r).map (fun i => f i.succ)
  let b := (innerVariableSComparisonIso r (fun i => d i.succ) (d 0)).hom.app X
  let c := (innerVariableSComparisonIso r (fun i => e i.succ) (d 0)).hom.app X
  let c' := (innerVariableSComparisonIso r (fun i => e i.succ) (e 0)).hom.app X
  let u := innerVariableOuterMap r (fun i => f i.succ) (d 0)
  let v := (innerVariableIndex r (fun i => e i.succ)).map (f 0)
  have ho : t.app (sStableModel (d 0).unop.len X) ≫ c = b ≫ (T.map u).app X :=
    innerVariableSComparisonIso_outer_naturality r (fun i => f i.succ) (d 0) X
  have hi : E.map (a.app X) ≫ c' = c ≫ (T.map v).app X :=
    NatTrans.congr_app (innerVariableSComparisonIso_naturality r
      (fun i => e i.succ) (f 0)) X
  have h := innerVariableIndex_map_permutation r f
  have hs : ((multiInnerSEndofunctor r).map f).app X =
      t.app (sStableModel (d 0).unop.len X) ≫ E.map (a.app X) := by
    change (((multiHeadSEndofunctor r).map f ⊗ₘ (multiTailSEndofunctor r).map f).app X) = _
    rw [endofunctorMonoidalCategory_tensorMap_app]
    rfl
  rw [hs]
  simp only [multiInnerSCoordinateAt, Iso.trans_hom, Functor.mapIso_hom, eqToIso.hom,
    NatTrans.comp_app]
  change ((t.app (sStableModel (d 0).unop.len X) ≫ E.map (a.app X)) ≫
    (c' ≫ (T.map (eqToHom (innerVariableIndex_obj_permutation r e))).app X)) =
    (b ≫ (T.map (eqToHom (innerVariableIndex_obj_permutation r d))).app X) ≫ _
  rw [Category.assoc, ← Category.assoc (E.map (a.app X)), hi,
    ← Category.assoc, ← Category.assoc (t.app (sStableModel (d 0).unop.len X)) c, ho]
  simpa only [CategoryTheory.Functor.map_comp, NatTrans.comp_app, Category.assoc] using
    congrArg (fun z => b ≫ (T.map z).app X) h

/-- 元の結合子の座標比較を全多単体的な自然同型として束ねる。 -/
def multiInnerSCoordinateNatIso (r : ℕ) :
    multiInnerSEndofunctor.{u} r ≅
      Pi.comap (fun _ : Fin (r + 1) => SimplexCategoryᵒᵖ) (finRotate (r + 1)) ⋙
        multiSEndofunctor (r + 1) :=
  NatIso.ofComponents (multiInnerSCoordinateAt r) (by
    intro d e f
    apply NatTrans.ext
    funext X
    exact multiInnerSCoordinateAt_naturality r f X)

end SerrePositivity.KST.SConstruction
