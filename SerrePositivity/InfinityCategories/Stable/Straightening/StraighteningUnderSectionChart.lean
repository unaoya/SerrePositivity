module
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Iso
public import SerrePositivity.InfinityCategories.F1B.IsoEndpointNormalization

/-!
分割で生成：docstring を書き直すこと
 # 元の初頂点 under 比較を、同じ切断比較と元の under 制限成分に分解する
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w v' w'
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
variable {B : SSet.{u}}

private lemma normalizeComposition {C : Type v} [Category.{w} C]
    {a b c b' c' : C} (l : a ≅ b) (e : b ≅ c) (hb : b = b') (hc : c = c') :
    F2.isoNormalizeEndpoints (l ≪≫ e) rfl hc =
      F2.isoNormalizeEndpoints l rfl hb ≪≫ F2.isoNormalizeEndpoints e hb hc := by
  subst b' c'
  simp only [F2.isoNormalizeEndpoints, eqToIso_refl, Iso.refl_symm, Iso.refl_trans,
    Iso.trans_refl]

private lemma mapNormalizeComposition {C : Type v} [Category.{w} C]
    {Z : Type v'} [Category.{w'} Z] (F : C ⥤ Z) {a b c : C} {b' c' : Z}
    (l : a ≅ b) (e : b ≅ c) (d : a ≅ c) (hd : d = l ≪≫ e)
    (hb : F.obj b = b') (hc : F.obj c = c') :
    F2.isoNormalizeEndpoints (F.mapIso d) rfl hc =
      F2.isoNormalizeEndpoints (F.mapIso l) rfl hb ≪≫
        F2.isoNormalizeEndpoints (F.mapIso e) hb hc := by
  subst d
  rw [Functor.mapIso_trans]
  exact normalizeComposition _ _ hb hc

end SerrePositivity.KST.Fibration
