module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovPerturbedProjection
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroConeClassMap

/-!
概要：Postnikov の微分変更後の実代数から、元の平方零標的への class を構成する。
方針：底変更した shift 係数の同型と、その負号を実双加群射として移送する。
規約：係数は標準 cone 境界の負符号。使われ方：非分裂拡大と cell 上の derivation。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (B : Mon (Complex R)) [B.X.IsStrictlyLE 0]
  (n : ℤ) (hn : 0 ≤ n)

local instance classLayerLower : (postnikovLayerBimodule R B n).X.IsStrictlyGE (-(n + 1)) :=
  postnikovLayer_lowerBound R B n

local instance classLayerUpper : (postnikovLayerBimodule R B n).X.IsStrictlyLE (-(n + 1)) :=
  postnikovLayer_upperBound R B n

lemma postnikovShiftedLayerRestrictionIso_hom :
    (postnikovShiftedLayerRestrictionIso R B n hn 1).hom.hom =
      𝟙 ((postnikovLayerBimodule R B n).X⟦(1 : ℤ)⟧) := by
  change (𝟙 (postnikovLayer R B n))⟦(1 : ℤ)⟧' ≫ 𝟙 _ = 𝟙 _
  exact (congrArg (fun t => t ≫ 𝟙 _) ((CategoryTheory.shiftFunctor (Complex R) (1 : ℤ)).map_id
    (postnikovLayer R B n))).trans (Category.id_comp _)

def postnikovClassCoefficient : DGBimoduleShift.obj (postnikovLayerBimodule R B n) 1 ⟶
    bimoduleRestrict (postnikovTransition R B (n + 1) n (by omega))
      (postnikovShiftedLayerBimodule R B n hn 1) :=
  SquareZero.negateCoefficient (postnikovTransition R B (n + 1) n (by omega)) _ _
    (postnikovShiftedLayerRestrictionIso R B n hn 1).hom

lemma postnikovClassCoefficient_hom : (postnikovClassCoefficient R B n hn).hom =
    -(𝟙 ((postnikovLayerBimodule R B n).X⟦(1 : ℤ)⟧)) := by
  change -(postnikovShiftedLayerRestrictionIso R B n hn 1).hom.hom = _
  rw [postnikovShiftedLayerRestrictionIso_hom]

def postnikovPerturbedClass : postnikovPerturbedExtension R B n hn ⟶
    postnikovDerivationTarget R B n hn :=
  SquareZeroCone.classMap (postnikov R B (n + 1)) (postnikovLayerBimodule R B n)
    (postnikovLayerInclusionBimodule R B n) (-(n + 1)) (by omega)
    (postnikovTransition R B (n + 1) n (by omega)) (postnikovShiftedLayerBimodule R B n hn 1)
    (postnikovClassCoefficient R B n hn) (postnikovLayerInclusion_transition_zero R B n)

lemma postnikovPerturbedClass_f (p : ℤ) : (postnikovPerturbedClass R B n hn).hom.f p =
    (Limits.biprod.map (postnikovTransition R B (n + 1) n (by omega)).hom
      (-(𝟙 ((postnikovLayerBimodule R B n).X⟦(1 : ℤ)⟧)))).f p := by
  have hc := SquareZeroCone.classMap_f (postnikov R B (n + 1)) (postnikovLayerBimodule R B n)
    (postnikovLayerInclusionBimodule R B n) (-(n + 1)) (by omega)
    (postnikovTransition R B (n + 1) n (by omega)) (postnikovShiftedLayerBimodule R B n hn 1)
    (postnikovClassCoefficient R B n hn) (postnikovLayerInclusion_transition_zero R B n) p
  rw [postnikovClassCoefficient_hom] at hc
  exact hc

lemma postnikovPerturbedClass_projection : postnikovPerturbedClass R B n hn ≫
    SquareZero.projection (postnikov R B n) (postnikovShiftedLayerBimodule R B n hn 1) =
      postnikovPerturbedProjection R B n hn := SquareZeroCone.classMap_projection _ _ _ _ _ _ _ _ _

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
