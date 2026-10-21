module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovLayerBase

/-!
概要：底の層双加群を隣接遷移で制限すると、元の層双加群と同型になる。
方針：検証済みの左右作用の回収式で、層複体の恒等射を双加群同型にする。
規約：underlying map は恒等。使われ方：shift した係数の元の層との比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (B : Mon (Complex R)) [B.X.IsStrictlyLE 0] (n : ℤ)

def postnikovLayerBaseRestrictionIso (hn : 0 ≤ n) :
    postnikovLayerBimodule R B n ≅
      bimoduleRestrict (postnikovTransition R B (n + 1) n (by omega))
        (postnikovLayerBaseBimodule R B n hn) := by
  refine Bimod.isoOfIso (Iso.refl (postnikovLayer R B n)) ?_ ?_
  · change postnikovLayerActLeft R B n ≫ 𝟙 _ =
      ((postnikov R B (n + 1)).X ◁ 𝟙 (postnikovLayer R B n)) ≫
        ((postnikovTransition R B (n + 1) n (by omega)).hom ▷ postnikovLayer R B n) ≫
          (postnikovLayerBaseBimodule R B n hn).actLeft
    simp only [Category.comp_id, whiskerLeft_id, Category.id_comp]
    exact (postnikovLayerBase_left_transition R B n hn).symm
  · change postnikovLayerActRight R B n ≫ 𝟙 _ =
      (𝟙 (postnikovLayer R B n) ▷ (postnikov R B (n + 1)).X) ≫
        (postnikovLayer R B n ◁ (postnikovTransition R B (n + 1) n (by omega)).hom) ≫
          (postnikovLayerBaseBimodule R B n hn).actRight
    simp only [Category.comp_id, id_whiskerRight, Category.id_comp]
    exact (postnikovLayerBase_right_transition R B n hn).symm

lemma postnikovLayerBaseRestrictionIso_hom (hn : 0 ≤ n) :
    (postnikovLayerBaseRestrictionIso R B n hn).hom.hom = 𝟙 (postnikovLayer R B n) := rfl

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
