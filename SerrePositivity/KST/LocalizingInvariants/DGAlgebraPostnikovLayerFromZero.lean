module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovLayerZeroRestrictionIso
public import SerrePositivity.KST.LocalizingInvariants.BimoduleRestrictionOver
public import SerrePositivity.KST.LocalizingInvariants.BimoduleComposition

/-!
概要：任意の二つの底変更層について、零切断上の実射を元の共通底上へ移す。
方針：恒等 underlying の二つの制限同型と制限射を、一般の三射合成で組み合わせる。
規約：roof や選択した段の定義を展開しない。使われ方：元の共通底の係数双加群逆。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (B C P : Mon (Complex R))
  [B.X.IsStrictlyLE 0] [C.X.IsStrictlyLE 0] [P.X.IsStrictlyLE 0]
  (n : ℤ) (hn : 0 ≤ n) (b : P ⟶ postnikov R B n) (c : P ⟶ postnikov R C n)

local instance layerFromZero_source_lowerBound : (postnikov R B 0).X.IsStrictlyGE 0 := by
  simpa only [neg_zero] using postnikov_lowerBound R B 0
local instance layerFromZero_target_lowerBound : (postnikov R C 0).X.IsStrictlyGE 0 := by
  simpa only [neg_zero] using postnikov_lowerBound R C 0

variable (u : bimoduleRestrict (postnikovDesc R 0 (b ≫ postnikovTransition R B n 0 hn))
    (postnikovLayerZeroBimodule R B n) ⟶
  bimoduleRestrict (postnikovDesc R 0 (c ≫ postnikovTransition R C n 0 hn))
    (postnikovLayerZeroBimodule R C n))

def postnikovLayerFromZero : bimoduleRestrict b (postnikovLayerBaseBimodule R B n hn) ⟶
    bimoduleRestrict c (postnikovLayerBaseBimodule R C n hn) :=
  bimoduleComposition (postnikovLayerBaseZeroRestrictionIso R B P n hn b).hom
    (bimoduleRestrictionMap (postnikovQuotient R P 0) u)
    (postnikovLayerBaseZeroRestrictionIso R C P n hn c).inv

lemma postnikovLayerFromZero_hom : (postnikovLayerFromZero R B C P n hn b c u).hom = u.hom := by
  unfold postnikovLayerFromZero
  rw [bimoduleComposition_hom, postnikovLayerBaseZeroRestrictionIso_hom,
    bimoduleRestrictionMap_hom, postnikovLayerBaseZeroRestrictionIso_inv]
  change 𝟙 _ ≫ u.hom ≫ 𝟙 _ = u.hom
  rw [Category.id_comp, Category.comp_id]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
