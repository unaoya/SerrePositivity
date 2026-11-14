module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.HomTensorStrength
public import Mathlib.CategoryTheory.Monoidal.Closed.InternalCurrying

/-!
概要：閉 braided 圏における二つの内部 Hom の順序交換。
方針：二重の内部 curry とテンソルの交換の同型を合成する。
規約：対象の同型と二重評価での計算を扱う。
使われ方：BF 1978 §2、HA §1.4.2。Kan 列の内部 Hom の Ω 条件。
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory MonoidalClosed

namespace SerrePositivity.KST.Spectra.InternalHomExchange
end SerrePositivity.KST.Spectra.InternalHomExchange
namespace SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange
open _root_.SerrePositivity.KST.Spectra.InternalHomExchange

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [MonoidalClosed C]

/-- 概要：源の同型による内部 Hom の制限同型。
方針：同型とその逆による pre を両方向に使う。
規約：源の向きは反変。
使われ方：HA §1.4.2。内部 Hom の二重 curry の間のテンソル交換。 -/
def preIso {A B : C} (e : A ≅ B) (Y : C) : (ihom B).obj Y ≅ (ihom A).obj Y where
  hom := (MonoidalClosed.pre e.hom).app Y
  inv := (MonoidalClosed.pre e.inv).app Y
  hom_inv_id := by
    rw [← NatTrans.comp_app, ← MonoidalClosed.pre_map, e.inv_hom_id,
      MonoidalClosed.pre_id]
    rfl
  inv_hom_id := by
    rw [← NatTrans.comp_app, ← MonoidalClosed.pre_map, e.hom_inv_id,
      MonoidalClosed.pre_id]
    rfl

/-- 概要：内部 Hom の二つの源を交換する同型。
方針：uncurry、源の braiding、curry を合成する。
規約：Hom(A,Hom(K,Y)) から Hom(K,Hom(A,Y)) への向き。
使われ方：BF 1978 §2、HA §1.4.2。loop と内部 Hom の交換。 -/
def iso (A K Y : C) : (ihom A).obj ((ihom K).obj Y) ≅ (ihom K).obj ((ihom A).obj Y) :=
  (MonoidalClosed.ihomCurryIso K A Y).symm ≪≫ _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.preIso (β_ A K) Y ≪≫
    MonoidalClosed.ihomCurryIso A K Y

/-- 概要：内部 Hom の交換同型を二重に評価した式。
方針：二重 curry をほどき、源の制限の評価式と結合子の自然性を使う。
規約：テンソル交換は既存の HomTensorStrength.exchange。
使われ方：BF 1978 §2、HA §1.4.2。内部 Hom の列の随伴構造射の計算。 -/
theorem uncurry_uncurry_hom (A K Y : C) :
    MonoidalClosed.uncurry (MonoidalClosed.uncurry (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso A K Y).hom) =
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.exchange A K ((ihom A).obj ((ihom K).obj Y))).hom ≫
        K ◁ (ihom.ev A).app ((ihom K).obj Y) ≫ (ihom.ev K).app Y := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso, Iso.trans_hom, Iso.symm_hom, _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.preIso,
    MonoidalClosed.ihomCurryIso_hom, MonoidalClosed.ihomCurryIso_inv]
  simp only [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_uncurry_ihomCurry]
  rw [associator_inv_naturality_right_assoc, associator_inv_naturality_right_assoc,
    MonoidalClosed.id_tensor_pre_app_comp_ev, whisker_exchange_assoc]
  rw [← MonoidalClosed.uncurry_eq, MonoidalClosed.uncurry_ihomUncurry]
  simp only [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.exchange, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, tensorRight, Functor.flip, curriedTensor, Category.assoc]

/-- 概要：テンソル交換による内部 Hom の構造射の随伴は、元の随伴を Hom へ移した射。
方針：二重に uncurry して交換同型の評価式と評価の自然性を使う。
規約：σ は任意の K⊗X から Y への射。
使われ方：BF 1978 §2、HA §1.4.2。Kan 列の内部 Hom の Ω 条件の厳密な比較。 -/
theorem curry_strength (K A X Y : C) (σ : K ⊗ X ⟶ Y) :
    MonoidalClosed.curry (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.map K A X ≫ (ihom A).map σ) =
      (ihom A).map (MonoidalClosed.curry σ) ≫ (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso A K Y).hom := by
  apply MonoidalClosed.uncurry_injective
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_curry, MonoidalClosed.uncurry_natural_left,
    MonoidalClosed.uncurry_ihom_map, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.evaluation]
  rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_natural_left,
    _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.uncurry_uncurry_hom, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.exchange_natural_right_assoc]
  have hev : A ◁ (ihom A).map (MonoidalClosed.curry σ) ≫ (ihom.ev A).app ((ihom K).obj Y) =
      (ihom.ev A).app X ≫ MonoidalClosed.curry σ := (ihom.ev A).naturality _
  rw [← whiskerLeft_comp_assoc, hev, whiskerLeft_comp]
  simp only [Category.assoc, MonoidalClosed.whiskerLeft_curry_ihom_ev_app]

end

end SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.InternalHomExchange.curry_strength := _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.curry_strength

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.InternalHomExchange.iso := _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.preIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.InternalHomExchange.preIso := _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.preIso

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.InternalHomExchange.uncurry_uncurry_hom := _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.uncurry_uncurry_hom

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.InternalHomExchange.iso.eq_1 := _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso.eq_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.InternalHomExchange.preIso._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.preIso._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.InternalHomExchange.preIso._proof_2 := _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.preIso._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.InternalHomExchange.preIso.eq_1 := _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.preIso.eq_1
