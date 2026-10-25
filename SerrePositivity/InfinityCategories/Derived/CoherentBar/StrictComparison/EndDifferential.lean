module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.NormalizedEndRebase

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
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open HomologicalComplex CochainComplex HomComplex
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {J : Type u} [PartialOrder J] (F : J ⥤ ModuleCategory R D)

local notation "B" => ForgetEnrichment.to (Complex R)
  (dgCoherentBarNormalizedGraded R D (dgCoherentBarStrictDiagram R D F))
local notation "P" => dgCoherentBarStrictNormalizedModule R D F
local notation "T" => dgCoherentBarNormalizedTheta R D (dgCoherentBarStrictDiagram R D F)

def dgStrictNormalizedEndDifferential (q : ℤ) (z : (moduleHom R D B B).X q) :
    (moduleHom R D B B).X (q + 1) :=
  (moduleHom R D B B).d q (q + 1) z +
    compose R (x := B) (y := B) (z := B) T z rfl +
    (q + 1).negOnePow • compose R (x := B) (y := B) (z := B) z T (by omega)

lemma dgStrictNormalizedEndRebase_d (q : ℤ) (z : (moduleHom R D B B).X q) :
    (moduleHom R D P P).d q (q + 1) (dgStrictNormalizedEndRebase R D F q z) =
      dgStrictNormalizedEndRebase R D F (q + 1) (dgStrictNormalizedEndDifferential R D F q z) := by
  apply moduleHomElement_ext R D (M := P) (N := P)
  intro x
  let θx := (moduleHomπ R D B B x).f 1 T
  let hT := dgCoherentBarNormalizedTheta_maurerCartan R D
    (dgCoherentBarStrictDiagram R D F)
    (dgCoherentBarMaurerCartan_unconditional R D (dgCoherentBarStrictDiagram R D F))
  let hx := moduleMaurerCartan_evaluation R D B T hT x
  have hrebase (r : ℤ) (w : (moduleHom R D B B).X r) :
      (moduleHomπ R D P P x).f r (dgStrictNormalizedEndRebase R D F r w) =
        maurerCartanRebaseCochain θx θx hx hx ((moduleHomπ R D B B x).f r w) := by
    apply Cochain.ext
    intro i j hij
    simpa only [maurerCartanRebaseCochain, Cochain.mk_v] using!
      dgStrictNormalizedEndRebase_π R D F r w x i j hij
  rw [moduleHomElement_d_π, hrebase q z,
    hrebase (q + 1) (dgStrictNormalizedEndDifferential R D F q z)]
  apply (maurerCartanCochainEquiv θx θx hx hx (q + 1)).symm.injective
  change maurerCartanForgetCochain θx θx hx hx
      (δ q (q + 1) (maurerCartanRebaseCochain θx θx hx hx
        ((moduleHomπ R D B B x).f q z))) = (moduleHomπ R D B B x).f (q + 1)
          (dgStrictNormalizedEndDifferential R D F q z)
  rw [maurerCartanHom_δ]
  unfold dgStrictNormalizedEndDifferential
  simp only [map_add, Units.smul_def, map_zsmul, moduleHomElement_d_π, moduleHomCompose_π]
  rfl

end SerrePositivity.InfinityCategories
