module

public import SerrePositivity.EInfinity.PowerOperation.ComplexRelativeElementColumn
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.FramedLimitProbeFunctor
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.RelativeHammockNerveEquivalence
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.RelativeNaturalWeakComparison
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.RelativeFunctorLaws

/-!
# 同じ cofibrant probe による全複体 hammock の自己同値

DAG XIII §2.2 の native な降下の補助。構成済みの probe と元の全 augmentation の
弱同値性を使う。［一般∞］移動候補。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock
open SerrePositivity.DifferentialGraded _root_.SerrePositivity.ComplexLimits
open _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
variable (A : Type u) [CommRing A]

def complexRelativeProbeMorphism : LocalizerMorphism
    (complexRelativeCategory A).weakEquivalences (complexRelativeCategory A).weakEquivalences where
  functor := complexRelativeDown A ⋙ _root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A ⋙ complexRelativeUp A
  map _ _ f hf := _root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor_map_quasiIso A ((complexRelativeDown A).map f) hf

def complexRelativeProbeAugmentation :
    (complexRelativeProbeMorphism A).functor ⟶ 𝟭 (complexRelativeCategory A).category where
  app Z := (complexRelativeUp A).map
    (_root_.SerrePositivity.ComplexLimits.framedLimitProbeComparison A ((complexRelativeDown A).obj Z))
  naturality X Y f := by
    apply ULift.ext
    exact (_root_.SerrePositivity.ComplexLimits.framedLimitProbeComparisonNatTrans A).naturality ((complexRelativeDown A).map f)

lemma complexRelativeProbeAugmentation_weak (Z : (complexRelativeCategory A).category) :
    (complexRelativeCategory A).weakEquivalences ((complexRelativeProbeAugmentation A).app Z) :=
  _root_.SerrePositivity.ComplexLimits.framedLimitProbeComparison_quasiIso A ((complexRelativeDown A).obj Z)

lemma complexRelativeProbeMorphism_hom_weak (X Y : (complexRelativeCategory A).category) :
    IsWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Relative.colimitMap (complexRelativeProbeMorphism A) X Y) := by
  apply (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.RelativeNatural.weak_iff (F := complexRelativeProbeMorphism A)
    (G := LocalizerMorphism.id (complexRelativeCategory A).weakEquivalences)
    (complexRelativeProbeAugmentation A)
    (complexRelativeProbeAugmentation_weak A) X Y).mpr
  rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Relative.colimitMap_id]
  exact isWeakHomotopyEquivalence_id _

lemma complexHammockProbe_isQCatEquivalence :
    IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.relativeKanHammockNerve (complexRelativeProbeMorphism A)) :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.relativeKanHammockNerve_isQCatEquivalence_of_counit (complexRelativeProbeMorphism A)
    (LocalizerMorphism.id (complexRelativeCategory A).weakEquivalences)
    (complexRelativeProbeAugmentation A) (complexRelativeProbeAugmentation_weak A)
    (complexRelativeProbeMorphism_hom_weak A)

end SerrePositivity.EInfinity.PowerOperation
