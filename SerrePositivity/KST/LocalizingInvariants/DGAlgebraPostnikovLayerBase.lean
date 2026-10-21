module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovLayerActions
public import SerrePositivity.KST.LocalizingInvariants.DGBimodulePostnikov
public import SerrePositivity.KST.LocalizingInvariants.BimoduleRestriction

/-!
概要：Postnikov 層を元の底の切断代数上の実 dg 双加群として構成する。
方針：一度元の代数へ制限し、内部 Hom による降下と全射性で元の隣接遷移へ戻す。
規約：実際の τ≥−n(B) 上の作用。使われ方：Postnikov 拡大を分類する係数。
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

def postnikovLayerOriginalBimodule : Bimod B B :=
  bimoduleRestrict (postnikovQuotient R B (n + 1)) (postnikovLayerBimodule R B n)

local instance layerOriginal_upperBound :
    (postnikovLayerOriginalBimodule R B n).X.IsStrictlyLE (-(n + 1)) :=
  postnikovLayer_upperBound R B n

local instance layerOriginal_lowerBound :
    (postnikovLayerOriginalBimodule R B n).X.IsStrictlyGE (-(n + 1)) :=
  postnikovLayer_lowerBound R B n

def postnikovLayerBaseBimodule (hn : 0 ≤ n) : Bimod (postnikov R B n) (postnikov R B n) :=
  postnikovBimodule R B (postnikovLayerOriginalBimodule R B n) (-(n + 1)) n hn

lemma postnikovLayerBase_left_projection (hn : 0 ≤ n) :
    ((postnikovQuotient R B n).hom ▷ postnikovLayer R B n) ≫
      (postnikovLayerBaseBimodule R B n hn).actLeft =
    ((postnikovQuotient R B (n + 1)).hom ▷ postnikovLayer R B n) ≫
      postnikovLayerActLeft R B n :=
  postnikovBimodule_left_projection R B (postnikovLayerOriginalBimodule R B n)
    (-(n + 1)) n hn

lemma postnikovLayerBase_right_projection (hn : 0 ≤ n) :
    (postnikovLayer R B n ◁ (postnikovQuotient R B n).hom) ≫
      (postnikovLayerBaseBimodule R B n hn).actRight =
    (postnikovLayer R B n ◁ (postnikovQuotient R B (n + 1)).hom) ≫
      postnikovLayerActRight R B n :=
  postnikovBimodule_right_projection R B (postnikovLayerOriginalBimodule R B n)
    (-(n + 1)) n hn

lemma postnikovLayerBase_left_transition (hn : 0 ≤ n) :
    ((postnikovTransition R B (n + 1) n (by omega)).hom ▷ postnikovLayer R B n) ≫
      (postnikovLayerBaseBimodule R B n hn).actLeft = postnikovLayerActLeft R B n := by
  have : Epi ((postnikovQuotient R B (n + 1)).hom ▷ postnikovLayer R B n) := by
    rw [← tensorHom_id]
    exact TruncationDesc.tensor_epi _ _
  apply (cancel_epi ((postnikovQuotient R B (n + 1)).hom ▷ postnikovLayer R B n)).1
  rw [← comp_whiskerRight_assoc]
  have ht := congrArg Mon.Hom.hom (postnikovQuotient_transition R B (n + 1) n (by omega))
  change (postnikovQuotient R B (n + 1)).hom ≫
    (postnikovTransition R B (n + 1) n (by omega)).hom = (postnikovQuotient R B n).hom at ht
  rw [ht]
  exact postnikovLayerBase_left_projection R B n hn

lemma postnikovLayerBase_right_transition (hn : 0 ≤ n) :
    (postnikovLayer R B n ◁ (postnikovTransition R B (n + 1) n (by omega)).hom) ≫
      (postnikovLayerBaseBimodule R B n hn).actRight = postnikovLayerActRight R B n := by
  have : Epi (postnikovLayer R B n ◁ (postnikovQuotient R B (n + 1)).hom) := by
    rw [← id_tensorHom]
    exact TruncationDesc.tensor_epi _ _
  apply (cancel_epi (postnikovLayer R B n ◁ (postnikovQuotient R B (n + 1)).hom)).1
  rw [← whiskerLeft_comp_assoc]
  have ht := congrArg Mon.Hom.hom (postnikovQuotient_transition R B (n + 1) n (by omega))
  change (postnikovQuotient R B (n + 1)).hom ≫
    (postnikovTransition R B (n + 1) n (by omega)).hom = (postnikovQuotient R B n).hom at ht
  rw [ht]
  exact postnikovLayerBase_right_projection R B n hn

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
