module
public import SerrePositivity.InfinityCategories.Stable.ExactFunctorConnecting
public import SerrePositivity.InfinityCategories.Stable.ExactFunctorShift
public import SerrePositivity.InfinityCategories.Stable.PretriangulatedInstance
public import Mathlib.CategoryTheory.Triangulated.Functor

/-! # 完全関手が誘導する三角関手

概要：安定 ∞ 圏間の完全関手の h の関手は distinguished triangle を保つ。
方針：接続射と一回シフト比較の式から cofiber 三角形の像を同定し、同型に沿って移す。
規約：既存の整数シフトと前三角構造を使う。使われ方：S6 の三角関手の公開。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Functor Pretriangulated MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：cofiber 三角形の第三射は完全関手の一回シフト比較を介して保存される。
方針：シフトと懸垂の比較の逆・順を消し、接続射の保存を適用する。
規約：Mathlib の mapTriangle の第三射。使われ方：cofiber 三角形の像の同型。 -/
lemma exactFunctor_map_cofiberTriangle_mor₃ {X Y : SSet.{u}}
    [Quasicategory X] [IsStable X] [Quasicategory Y] [IsStable Y]
    (F : X ⟶ Y) [IsExactFunctor F] (t : ZeroTriangle X) (ht : IsCofiberSequence t) :
    (hoFunctor.map F).toFunctor.map (cofiberTriangle t ht).mor₃ ≫
        ((hoFunctor.map F).toFunctor.commShiftIso (1 : ℤ)).hom.app (cofiberTriangle t ht).obj₁ =
      (cofiberTriangle (t.map F (IsExactFunctor.preservesZero (F := F)))
        (IsExactFunctor.preservesCofiber (F := F) t ht)).mor₃ := by
  rw [exactFunctorCommShift_one]
  change (hoFunctor.map F).toFunctor.map
      (cofiberConnecting t ht ≫ (shiftOneSuspensionIso X).inv.app t.hoShortComplex.X₁) ≫
      (exactFunctorShiftOneIso F).hom.app t.hoShortComplex.X₁ = _
  simp only [exactFunctorShiftOneIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    isoWhiskerRight_hom, isoWhiskerLeft_hom, whiskerRight_app, whiskerLeft_app]
  rw [CategoryTheory.Functor.map_comp]
  simp only [Category.assoc, ← CategoryTheory.Functor.map_comp_assoc,
    Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  rw [← Category.assoc, cofiberConnecting_postcomp]
  rfl

/-- 概要：cofiber 三角形の像は写した cofiber 列の三角形と同型。
方針：三つの対象の恒等同型を使い、第三射には接続射の保存を適用する。
規約：Mathlib の mapTriangle を使う。使われ方：distinguished triangle の保存。 -/
def exactFunctorCofiberTriangleIso {X Y : SSet.{u}}
    [Quasicategory X] [IsStable X] [Quasicategory Y] [IsStable Y]
    (F : X ⟶ Y) [IsExactFunctor F] (t : ZeroTriangle X) (ht : IsCofiberSequence t) :
    (hoFunctor.map F).toFunctor.mapTriangle.obj (cofiberTriangle t ht) ≅
      cofiberTriangle (t.map F (IsExactFunctor.preservesZero (F := F)))
        (IsExactFunctor.preservesCofiber (F := F) t ht) :=
  Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]; rfl)
    (by simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]; rfl)
    (by
      simp only [Iso.refl_hom, CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]
      exact exactFunctor_map_cofiberTriangle_mor₃ F t ht)

/-- 概要：安定 ∞ 圏間の完全関手は h の三角関手を誘導する。
方針：cofiber 三角形の保存を、distinguished triangle の同型による表示へ拡張する。
規約：仮定は両側の安定性と完全性のみ。使われ方：S6 と D7 の比較関手。 -/
instance exactFunctor_isTriangulated {X Y : SSet.{u}}
    [Quasicategory X] [IsStable X] [Quasicategory Y] [IsStable Y]
    (F : X ⟶ Y) [IsExactFunctor F] : (hoFunctor.map F).toFunctor.IsTriangulated where
  map_distinguished T hT := by
    change T ∈ cofiberDistinguishedTriangles X at hT
    obtain ⟨t, ht, ⟨e⟩⟩ := hT
    change (hoFunctor.map F).toFunctor.mapTriangle.obj T ∈ cofiberDistinguishedTriangles Y
    exact ⟨t.map F (IsExactFunctor.preservesZero (F := F)),
      IsExactFunctor.preservesCofiber (F := F) t ht,
      ⟨(hoFunctor.map F).toFunctor.mapTriangle.mapIso e ≪≫ exactFunctorCofiberTriangleIso F t ht⟩⟩

/-- 概要：完全関手が誘導する h の関手は加法的。
方針：Mathlib の三角関手の加法性を適用する。
規約：加法性を完全性の追加仮定にはしない。使われ方：Hom の準同型と長完全列。 -/
lemma exactFunctor_additive {X Y : SSet.{u}}
    [Quasicategory X] [IsStable X] [Quasicategory Y] [IsStable Y]
    (F : X ⟶ Y) [IsExactFunctor F] : (hoFunctor.map F).toFunctor.Additive := inferInstance

end SerrePositivity.InfinityCategories
