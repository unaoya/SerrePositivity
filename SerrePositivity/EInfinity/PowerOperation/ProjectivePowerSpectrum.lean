module

public import SerrePositivity.EInfinity.PowerOperation.BoundedProjectiveTensorInput
public import SerrePositivity.EInfinity.PowerOperation.BoundedCyclicSpectrum

/-!
# 射影入力の同じ p 重テンソルと周期 Hom の native スペクトル図式

DAG XIII Construction 2.2.6 の完全入力の係数模型の前段。
同じ p 入力・周期解像度・Hom・スペクトル化を実相対関手として合成する。
採用した周期のままの未シフト Hom であり、native Tate[-1] との比較は別に必要。
T_p の一般入力への延長も、このファイルの完成範囲には含めない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory SSet
open _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
variable (p : ℕ) [NeZero p] (k : Type u) [CommRing k]

/-- 元の上有界射影入力と同じ指定準同型を持つ相対圏。 -/
def boundedProjectiveRelativeCategory : RelativeCategory.{u + 1} where
  category := Cat.of (AsSmall.{u + 1} (BoundedProjectiveInput k))
  weakEquivalences := (boundedProjectiveInputWeak k).inverseImage AsSmall.down
  isMultiplicative := inferInstance

/-- 同じ p 入力を上有界巡回係数の実相対圏へ送る。 -/
def boundedProjectiveRelativeTensorMorphism : LocalizerMorphism
    (boundedProjectiveRelativeCategory k).weakEquivalences
    (boundedCyclicRelativeCategory p k).weakEquivalences where
  functor := AsSmall.down ⋙ boundedProjectiveTensorInputFunctor p k ⋙ AsSmall.up
  map _ _ f hf := (boundedProjectiveTensorInputLocalizer p k).map (AsSmall.down.map f) hf

/-- 同じ p 入力と完全周期 Hom の合成を全複体の相対圏へ送る。 -/
def boundedProjectivePowerHomMorphism : LocalizerMorphism
    (boundedProjectiveRelativeCategory k).weakEquivalences
    (complexRelativeCategory k).weakEquivalences :=
  (boundedProjectiveRelativeTensorMorphism p k).comp (boundedCyclicRelativeHomMorphism p k)

/-- 射影入力の同じ指定係数構成から native Sp への実関手。 -/
def projectivePowerSpectrum :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockNerve (boundedProjectiveRelativeCategory k) ⟶ KST.Spectra.Sp.{u} :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.relativeKanHammockNerve (boundedProjectivePowerHomMorphism p k) ≫
    eilenbergMacLaneHammockFunctor k

/-- 同じ厳密な p 入力・周期 Hom・スペクトル化との全 sourceIso。 -/
def projectivePowerSpectrum_sourceIso :
    FunctorIso (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockLocalizationNerveMap (boundedProjectiveRelativeCategory k) ≫
      projectivePowerSpectrum p k)
      (nerveMap (boundedProjectivePowerHomMorphism p k).functor ≫
        complexRelativeSpectrumSource k) := by
  change FunctorIso (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockLocalizationNerveMap (boundedProjectiveRelativeCategory k) ≫
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.relativeKanHammockNerve (boundedProjectivePowerHomMorphism p k) ≫
      eilenbergMacLaneHammockFunctor k)) _
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.relativeKanHammockNerve_source]
  simpa only [Category.assoc, complexHammockSource] using
    FunctorIso.precomp (eilenbergMacLaneHammockFunctor_sourceIso k)
      (nerveMap (boundedProjectivePowerHomMorphism p k).functor)

end SerrePositivity.EInfinity.PowerOperation
