module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExactFunctorConnecting
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExactFunctorShift
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PretriangulatedInstance
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
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：cofiber 三角形の第三射は完全関手の一回シフト比較を介して保存される。
方針：シフトと懸垂の比較の逆・順を消し、接続射の保存を適用する。
規約：Mathlib の mapTriangle の第三射。使われ方：cofiber 三角形の像の同型。 -/
lemma exactFunctor_map_cofiberTriangle_mor₃ {X Y : SSet.{u}}
    [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] [Quasicategory Y] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable Y]
    (F : X ⟶ Y) [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor F] (t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X) (ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsCofiberSequence t) :
    (hoFunctor.map F).toFunctor.map (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberTriangle t ht).mor₃ ≫
        ((hoFunctor.map F).toFunctor.commShiftIso (1 : ℤ)).hom.app (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberTriangle t ht).obj₁ =
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberTriangle (t.map F (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesZero (F := F)))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesCofiber (F := F) t ht)).mor₃ := by
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.exactFunctorCommShift_one]
  change (hoFunctor.map F).toFunctor.map
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberConnecting t ht ≫ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.shiftOneSuspensionIso X).inv.app t.hoShortComplex.X₁) ≫
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.exactFunctorShiftOneIso F).hom.app t.hoShortComplex.X₁ = _
  simp only [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.exactFunctorShiftOneIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    isoWhiskerRight_hom, isoWhiskerLeft_hom, whiskerRight_app, whiskerLeft_app]
  rw [CategoryTheory.Functor.map_comp]
  simp only [Category.assoc, ← CategoryTheory.Functor.map_comp_assoc,
    Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberConnecting_postcomp]
  rfl

/-- 概要：cofiber 三角形の像は写した cofiber 列の三角形と同型。
方針：三つの対象の恒等同型を使い、第三射には接続射の保存を適用する。
規約：Mathlib の mapTriangle を使う。使われ方：distinguished triangle の保存。 -/
def exactFunctorCofiberTriangleIso {X Y : SSet.{u}}
    [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] [Quasicategory Y] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable Y]
    (F : X ⟶ Y) [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor F] (t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X) (ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsCofiberSequence t) :
    (hoFunctor.map F).toFunctor.mapTriangle.obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberTriangle t ht) ≅
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberTriangle (t.map F (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesZero (F := F)))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesCofiber (F := F) t ht) :=
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
    [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] [Quasicategory Y] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable Y]
    (F : X ⟶ Y) [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor F] : (hoFunctor.map F).toFunctor.IsTriangulated where
  map_distinguished T hT := by
    change T ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberDistinguishedTriangles X at hT
    obtain ⟨t, ht, ⟨e⟩⟩ := hT
    change (hoFunctor.map F).toFunctor.mapTriangle.obj T ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberDistinguishedTriangles Y
    exact ⟨t.map F (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesZero (F := F)),
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesCofiber (F := F) t ht,
      ⟨(hoFunctor.map F).toFunctor.mapTriangle.mapIso e ≪≫ exactFunctorCofiberTriangleIso F t ht⟩⟩

/-- 概要：完全関手が誘導する h の関手は加法的。
方針：Mathlib の三角関手の加法性を適用する。
規約：加法性を完全性の追加仮定にはしない。使われ方：Hom の準同型と長完全列。 -/
lemma exactFunctor_additive {X Y : SSet.{u}}
    [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] [Quasicategory Y] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable Y]
    (F : X ⟶ Y) [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor F] : (hoFunctor.map F).toFunctor.Additive := inferInstance

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
