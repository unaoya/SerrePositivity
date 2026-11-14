module

public import SerrePositivity.EInfinity.PowerOperation.BoundedCyclicCoefficients
public import SerrePositivity.EInfinity.PowerOperation.ComplexRelativeElementColumn
public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneHammockFunctor
public import SerrePositivity.EInfinity.SimplicialLocalization.RelativeHammockSourceComparison

/-!
# 同じ上有界周期係数模型から native Sp への実関手

DAG XIII Construction 2.2.6 の完全入力の係数模型の前段。
証明済みの同じ相対 Hom 関手を hammock へ移し、実 Eilenberg–Mac Lane 関手へ合成する。
同じ厳密な係数図式へ戻る全 sourceIso を保持する。
これはまだ native Tate 関手との同定でも、T_p の一般入力への延長でもない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded
open SerrePositivity.EInfinity.SimplicialLocalization
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
variable (p : ℕ) [NeZero p] (k : Type u) [CommRing k]

/-- 上有界係数の同じ準同型を持つ相対圏。 -/
def boundedCyclicRelativeCategory : RelativeCategory.{u + 1} where
  category := Cat.of (AsSmall.{u + 1} (BoundedCyclicCoefficient p k))
  weakEquivalences := (boundedCyclicCoefficientWeak p k).inverseImage AsSmall.down
  isMultiplicative := inferInstance

/-- 宇宙の表示だけを忘れる指定係数関手。 -/
abbrev boundedCyclicRelativeDown :
    (boundedCyclicRelativeCategory p k).category ⥤ BoundedCyclicCoefficient p k :=
  AsSmall.down

/-- 同じ周期 Hom を全複体の実相対圏へ送る相対関手。 -/
def boundedCyclicRelativeHomMorphism : LocalizerMorphism
    (boundedCyclicRelativeCategory p k).weakEquivalences
    (complexRelativeCategory k).weakEquivalences where
  functor := boundedCyclicRelativeDown p k ⋙ boundedCyclicHomFunctor p k ⋙ complexRelativeUp k
  map _ _ f hf := by
    let := projectiveModelCategory k
    have h := (boundedCyclicHomLocalizer p k).map
      ((boundedCyclicRelativeDown p k).map f) hf
    exact (HomologicalComplex.mem_quasiIso_iff _).mp h

/-- 同じ上有界係数の hammock から native Sp への実関手。 -/
def boundedCyclicSpectrum :
    kanHammockNerve (boundedCyclicRelativeCategory p k) ⟶ KST.Spectra.Sp.{u} :=
  relativeKanHammockNerve (boundedCyclicRelativeHomMorphism p k) ≫
    eilenbergMacLaneHammockFunctor k

/-- 同じ厳密な周期 Hom の図式へ戻る、全関手の指定同型。 -/
def boundedCyclicSpectrum_sourceIso :
    FunctorIso (hammockLocalizationNerveMap (boundedCyclicRelativeCategory p k) ≫
      boundedCyclicSpectrum p k)
      (nerveMap (boundedCyclicRelativeHomMorphism p k).functor ≫
        complexRelativeSpectrumSource k) := by
  change FunctorIso (hammockLocalizationNerveMap (boundedCyclicRelativeCategory p k) ≫
    (relativeKanHammockNerve (boundedCyclicRelativeHomMorphism p k) ≫
      eilenbergMacLaneHammockFunctor k)) _
  rw [← Category.assoc, relativeKanHammockNerve_source]
  simpa only [Category.assoc, complexHammockSource] using
    FunctorIso.precomp (eilenbergMacLaneHammockFunctor_sourceIso k)
      (nerveMap (boundedCyclicRelativeHomMorphism p k).functor)

end SerrePositivity.EInfinity.PowerOperation
