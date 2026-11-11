module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraNativeFrameUnits
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.PiZeroConstant
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.KanLimits

/-!
概要：元の代数射の全標的族を Kan 値として保持し、実 frame の単位を持ち上げる。
方針：元の ordinaryHomFamily を同じ Hom 集合の離散単体集合と比較する。
規約：局所化後の Hom と同一視せず、元の全代数射と標的作用を変えない。
使われ方：実 frame 比較における零単体の全標的 coherent な照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory Limits MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (A : Mon (Complex R))

def nativeCellOrdinaryHomDiscreteIso (B : Mon (Complex R)) :
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ordinaryHomFamily (cellResolution R A)).obj B ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.discrete (cellResolution R A ⟶ B) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro n m α
    apply ConcreteCategory.hom_ext
    intro f
    change f ≫ 𝟙 B = f
    exact Category.comp_id f)

lemma nativeCellOrdinaryHom_kanComplex (B : Mon (Complex R)) :
    SSet.KanComplex ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ordinaryHomFamily (cellResolution R A)).obj B) := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.discrete_kan (cellResolution R A ⟶ B)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.kanComplex_of_iso (nativeCellOrdinaryHomDiscreteIso R A B).symm

def nativeCellOrdinaryLargeKanFunctor : Mon (Complex R) ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u + 1} where
  obj B := ⟨SSet.uliftFunctor.{u + 1, u}.obj
    ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ordinaryHomFamily (cellResolution R A)).obj B), by
      have := nativeCellOrdinaryHom_kanComplex R A B
      infer_instance⟩
  map f := SSet.uliftFunctor.{u + 1, u}.map
    ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ordinaryHomFamily (cellResolution R A)).map f)
  map_id B := (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ordinaryHomFamily (cellResolution R A) ⋙
    SSet.uliftFunctor.{u + 1, u}).map_id B
  map_comp f g := (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ordinaryHomFamily (cellResolution R A) ⋙
    SSet.uliftFunctor.{u + 1, u}).map_comp f g

lemma nativeCellOrdinaryLargeKanFunctor_forget :
    nativeCellOrdinaryLargeKanFunctor R A ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget =
      _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ordinaryHomFamily (cellResolution R A) ⋙
        SSet.uliftFunctor.{u + 1, u} := rfl

def nativeCellOrdinaryInfinityKanFunctor : InfinityPresentation R ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u + 1} :=
  ULiftHom.down ⋙ nativeCellOrdinaryLargeKanFunctor R A

def nativeCellMappingUnitLarge :
    nativeCellOrdinaryLargeKanFunctor R A ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget ⟶
      multiplicativeCellMappingLargeKanFunctor R A ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget :=
  Functor.whiskerRight (nativeCellMappingUnit R A) SSet.uliftFunctor.{u + 1, u}

def nativeCellSourceFrameMappingUnitLarge :
    nativeCellOrdinaryLargeKanFunctor R A ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget ⟶
      nativeCellSourceFrameLargeKanFunctor R A ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget :=
  Functor.whiskerRight (nativeCellSourceFrameMappingUnit R A) SSet.uliftFunctor.{u + 1, u}

def nativeCellChosenRightMappingUnitLarge :
    nativeCellOrdinaryLargeKanFunctor R A ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget ⟶
      nativeCellChosenRightLargeKanFunctor R A ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget :=
  Functor.whiskerRight (nativeCellChosenRightMappingUnit R A) SSet.uliftFunctor.{u + 1, u}

lemma nativeCellMappingUnitLarge_mixed_triangle :
    nativeCellSourceFrameMappingUnitLarge R A ≫ nativeCellMixedLeftLarge R A =
      nativeCellMappingUnitLarge R A ≫ nativeCellMixedRightLarge R A := by
  change Functor.whiskerRight (nativeCellSourceFrameMappingUnit R A) _ ≫
      Functor.whiskerRight (nativeCellMixedLeftToKan R A) _ =
    Functor.whiskerRight (nativeCellMappingUnit R A) _ ≫
      Functor.whiskerRight (nativeCellMixedRightToKan R A) _
  rw [← Functor.whiskerRight_comp, ← Functor.whiskerRight_comp]
  congr 1

lemma nativeCellChosenRightMappingUnitLarge_mixed_triangle :
    nativeCellSourceFrameMappingUnitLarge R A ≫ nativeCellChosenMixedLeftLarge R A =
      nativeCellChosenRightMappingUnitLarge R A ≫ nativeCellChosenMixedRightLarge R A := by
  change Functor.whiskerRight (nativeCellSourceFrameMappingUnit R A) _ ≫
      Functor.whiskerRight (nativeCellChosenMixedLeftToKan R A) _ =
    Functor.whiskerRight (nativeCellChosenRightMappingUnit R A) _ ≫
      Functor.whiskerRight (nativeCellChosenMixedRightToKan R A) _
  rw [← Functor.whiskerRight_comp, ← Functor.whiskerRight_comp]
  congr 1

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
