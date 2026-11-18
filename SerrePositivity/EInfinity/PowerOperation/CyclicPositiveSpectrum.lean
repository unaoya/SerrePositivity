module

public import SerrePositivity.EInfinity.PowerOperation.CyclicPeriodicRestriction
public import SerrePositivity.EInfinity.PowerOperation.BoundedCyclicSpectrum
public import SerrePositivity.EInfinity.PowerOperation.RelativeComplexSpectrum

/-!
# 同じ周期解像度の正の部分の有界係数スペクトル図式

DAG XIII Construction 2.2.6 の境界の係数模型に使う前段。
正の部分の各項の射影性を供給し、有界係数の指定準同型を保つことを証明する。
元の正の部分の Hom 図式を native Sp へ運ぶ。orbit との同定はまだ含めない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory
open SerrePositivity.DifferentialGraded
open _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
variable (p : ℕ) [NeZero p] (k : Type u) [CommRing k]

/-- 同じ周期解像度の正の部分も、各項は射影的。 -/
lemma cyclicPositiveResolution_projective (i : ℤ) :
    Projective ((cyclicPositiveResolution p k).X i) := by
  by_cases hi : 0 ≤ i
  · exact Projective.of_iso
      (StupidTruncation.aboveXIso (powerOperationCompleteResolution p k) 0 i hi).symm
      (cyclicTateComplex_leftRegular_projective k (powerOperationCyclicGenerator p) i)
  · exact (StupidTruncation.above_isZero_X
      (powerOperationCompleteResolution p k) 0 i (by omega)).projective

/-- 正の部分の同じ Hom を上有界係数へ制限した全関手。 -/
def cyclicPositiveBoundedHomFunctor : BoundedCyclicCoefficient p k ⥤ Complex k :=
  boundedCyclicCoefficientInclusion p k ⋙ cyclicPositiveResolutionHomFunctor p k

lemma cyclicPositiveBoundedHomFunctor_map_quasiIso
    {M N : BoundedCyclicCoefficient p k} (f : M ⟶ N) [QuasiIso f.hom] :
    QuasiIso ((cyclicPositiveBoundedHomFunctor p k).map f) := by
  obtain ⟨a, ha⟩ := M.property
  obtain ⟨b, hb⟩ := N.property
  have : M.obj.IsStrictlyLE a := ha
  have : N.obj.IsStrictlyLE b := hb
  have : M.obj.IsStrictlyLE (max a b) := M.obj.isStrictlyLE_of_le a _ (le_max_left _ _)
  have : N.obj.IsStrictlyLE (max a b) := N.obj.isStrictlyLE_of_le b _ (le_max_right _ _)
  have (i : ℤ) : Projective ((cyclicPositiveResolution p k).X i) :=
    cyclicPositiveResolution_projective p k i
  exact linearHomComplexPostcompose_quasiIso_boundedAbove k
    (cyclicPositiveResolution p k) f.hom (max a b)

/-- 正の部分の Hom の同じ実相対関手。 -/
def cyclicPositiveBoundedHomLocalizer : LocalizerMorphism (boundedCyclicCoefficientWeak p k)
    (HomologicalComplex.quasiIso (ModuleCat.{u} k) (.up ℤ)) where
  functor := cyclicPositiveBoundedHomFunctor p k
  map _ _ f hf := by
    have : QuasiIso f.hom := (HomologicalComplex.mem_quasiIso_iff _).mp hf
    exact (HomologicalComplex.mem_quasiIso_iff _).mpr
      (cyclicPositiveBoundedHomFunctor_map_quasiIso p k f)

/-- 正の部分の同じ Hom を全複体の相対圏へ送る。 -/
def cyclicPositiveRelativeHomMorphism : LocalizerMorphism
    (boundedCyclicRelativeCategory p k).weakEquivalences
    (complexRelativeCategory k).weakEquivalences where
  functor := boundedCyclicRelativeDown p k ⋙ cyclicPositiveBoundedHomFunctor p k ⋙
    complexRelativeUp k
  map _ _ f hf := by
    let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory k
    exact (HomologicalComplex.mem_quasiIso_iff _).mp
      ((cyclicPositiveBoundedHomLocalizer p k).map ((boundedCyclicRelativeDown p k).map f) hf)

/-- 同じ正の部分の係数図式から native Sp への実関手。 -/
def cyclicPositiveSpectrum := relativeComplexSpectrum k (cyclicPositiveRelativeHomMorphism p k)

/-- 同じ厳密な正の部分の全図式へ戻る指定 sourceIso。 -/
def cyclicPositiveSpectrum_sourceIso :=
  relativeComplexSpectrum_sourceIso k (cyclicPositiveRelativeHomMorphism p k)

end SerrePositivity.EInfinity.PowerOperation
