module

public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Whiskering

/-! # パラメータの積の比較を作用の反復比較へ送る -/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

noncomputable section

namespace SerrePositivity.ActionProductComparison

open CategoryTheory CategoryTheory.MonoidalCategory

variable {W : Type u₁} {V : Type u₂} {C : Type u₃}
  [Category.{v₁} W] [Category.{v₂} V] [Category.{v₃} C]
  [MonoidalCategory W] [MonoidalCategory V]
  (P : W ⥤ V) (H : V ⥤ C ⥤ C)
  (a : ∀ X Y, H.obj (X ⊗ Y) ≅ H.obj Y ⋙ H.obj X)
  (m : ∀ K L, P.obj K ⊗ P.obj L ≅ P.obj (K ⊗ L))

/-- パラメータの積を作用の結同比較に接続した自然同型。 -/
def productNatIso (K L : W) : H.obj (P.obj (K ⊗ L)) ≅ H.obj (P.obj L) ⋙ H.obj (P.obj K) :=
  H.mapIso (m K L).symm ≪≫ a (P.obj K) (P.obj L)

/-- 反復比較のパラメータの両変数の自然性の等式。 -/
def parameterLaw {K K' L L' : W} (f : K ⟶ K') (g : L ⟶ L') (E : C) : Prop :=
  (H.map (P.map (f ⊗ₘ g))).app E ≫ (productNatIso P H a m K' L').hom.app E =
    (productNatIso P H a m K L).hom.app E ≫
      (H.map (P.map f)).app ((H.obj (P.obj L)).obj E) ≫
        (H.obj (P.obj K')).map ((H.map (P.map g)).app E)

/-- 積の比較と作用の結同比較の自然性から、反復比較の両変数の自然性を得る。 -/
lemma parameter {K K' L L' : W} (f : K ⟶ K') (g : L ⟶ L') (E : C)
    (hm : P.map (f ⊗ₘ g) ≫ (m K' L').inv =
      (m K L).inv ≫ (P.map f ⊗ₘ P.map g))
    (ha : (H.map (P.map f ⊗ₘ P.map g)).app E ≫ (a (P.obj K') (P.obj L')).hom.app E =
      (a (P.obj K) (P.obj L)).hom.app E ≫
        (H.map (P.map f)).app ((H.obj (P.obj L)).obj E) ≫
          (H.obj (P.obj K')).map ((H.map (P.map g)).app E)) :
    parameterLaw P H a m f g E := by
  unfold parameterLaw productNatIso
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, NatTrans.comp_app]
  rw [← Category.assoc, ← NatTrans.comp_app, ← H.map_comp, hm, H.map_comp,
    NatTrans.comp_app, Category.assoc, ha]
  simp only [Category.assoc]

end SerrePositivity.ActionProductComparison
