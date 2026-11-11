module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.NormalizedEndRebase

/-!
概要：実正規化 bar の自己 Hom 微分を、内部微分と左右の theta 合成で記述する。
方針：同じ評価成分を持つ MC 移送の cochain 微分を展開する。
規約：始域と標的の双方に同じ正規化 theta を使う。
使われ方：末尾付加の局所縮約の二つの境界項。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory Limits DifferentialGraded SSet
open HomologicalComplex CochainComplex HomComplex
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {J : Type u} [PartialOrder J] (F : J ⥤ _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D)

local notation "B" => ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R)
  (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedGraded R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictDiagram R D F))
local notation "P" => _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictNormalizedModule R D F
local notation "T" => _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedTheta R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictDiagram R D F)

def dgStrictNormalizedEndDifferential (q : ℤ) (z : (_root_.SerrePositivity.DifferentialGraded.moduleHom R D B B).X q) :
    (_root_.SerrePositivity.DifferentialGraded.moduleHom R D B B).X (q + 1) :=
  (_root_.SerrePositivity.DifferentialGraded.moduleHom R D B B).d q (q + 1) z +
    _root_.SerrePositivity.DifferentialGraded.compose R (x := B) (y := B) (z := B) T z rfl +
    (q + 1).negOnePow • _root_.SerrePositivity.DifferentialGraded.compose R (x := B) (y := B) (z := B) z T (by omega)

lemma dgStrictNormalizedEndRebase_d (q : ℤ) (z : (_root_.SerrePositivity.DifferentialGraded.moduleHom R D B B).X q) :
    (moduleHom R D P P).d q (q + 1) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgStrictNormalizedEndRebase R D F q z) =
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgStrictNormalizedEndRebase R D F (q + 1) (dgStrictNormalizedEndDifferential R D F q z) := by
  apply _root_.SerrePositivity.DifferentialGraded.moduleHomElement_ext R D (M := P) (N := P)
  intro x
  let θx := (_root_.SerrePositivity.DifferentialGraded.moduleHomπ R D B B x).f 1 T
  let hT := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedTheta_maurerCartan R D
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictDiagram R D F)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarMaurerCartan_unconditional R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictDiagram R D F))
  let hx := _root_.SerrePositivity.DifferentialGraded.moduleMaurerCartan_evaluation R D B T hT x
  have hrebase (r : ℤ) (w : (_root_.SerrePositivity.DifferentialGraded.moduleHom R D B B).X r) :
      (moduleHomπ R D P P x).f r (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgStrictNormalizedEndRebase R D F r w) =
        _root_.SerrePositivity.DifferentialGraded.maurerCartanRebaseCochain θx θx hx hx ((_root_.SerrePositivity.DifferentialGraded.moduleHomπ R D B B x).f r w) := by
    apply Cochain.ext
    intro i j hij
    simpa only [_root_.SerrePositivity.DifferentialGraded.maurerCartanRebaseCochain, Cochain.mk_v] using!
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgStrictNormalizedEndRebase_π R D F r w x i j hij
  rw [_root_.SerrePositivity.DifferentialGraded.moduleHomElement_d_π, hrebase q z,
    hrebase (q + 1) (dgStrictNormalizedEndDifferential R D F q z)]
  apply (_root_.SerrePositivity.DifferentialGraded.maurerCartanCochainEquiv θx θx hx hx (q + 1)).symm.injective
  change _root_.SerrePositivity.DifferentialGraded.maurerCartanForgetCochain θx θx hx hx
      (δ q (q + 1) (_root_.SerrePositivity.DifferentialGraded.maurerCartanRebaseCochain θx θx hx hx
        ((_root_.SerrePositivity.DifferentialGraded.moduleHomπ R D B B x).f q z))) = (_root_.SerrePositivity.DifferentialGraded.moduleHomπ R D B B x).f (q + 1)
          (dgStrictNormalizedEndDifferential R D F q z)
  rw [_root_.SerrePositivity.DifferentialGraded.maurerCartanHom_δ]
  unfold dgStrictNormalizedEndDifferential
  simp only [map_add, Units.smul_def, map_zsmul, _root_.SerrePositivity.DifferentialGraded.moduleHomElement_d_π, _root_.SerrePositivity.DifferentialGraded.moduleHomCompose_π]
  rfl

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
