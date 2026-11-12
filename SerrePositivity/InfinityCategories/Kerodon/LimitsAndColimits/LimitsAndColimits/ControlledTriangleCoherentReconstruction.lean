module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ControlledTriangleUniversalLongHom
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleSeparatedFamilyShortFaces
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleSeparatedFamilyDiagonal

/-!
概要：要求正本の実 L の全てをパラメーターにした、標準全対角を持つ実二胞体族。
方針：普遍長 Hom の対角を保つ Kan 延長を選び、全次数で組み立てる。
規約：元の二短辺と標準全対角を全 K・L で厳密に回収する。
使われ方：固定ホーン fiber への実 encode の構成。単射性と厳密切断は別途。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

variable (X Y Z : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) (K : SSet.{u + 1})
  (f : K ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom X Y))
  (g : K ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom Y Z))

def controlledTriangleSeparatedExtension :
    let L := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleLongHomSpace X Z K (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleCompositeFamily X Y Z K f g)
    (Δ[1] : SSet.{u + 1}) ⊗ ((K ⊗ K) ⊗ L) ⟶
      (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom X Z) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleUniversalSeparatedExtension_exists X Y Z K f g).choose

lemma controlledTriangleSeparatedExtension_comp :
    let L := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleLongHomSpace X Z K (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleCompositeFamily X Y Z K f g)
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 ((K ⊗ K) ⊗ L) ≫ controlledTriangleSeparatedExtension X Y Z K f g =
      lift (fst (K ⊗ K) L ≫ fst K K ≫ f) (fst (K ⊗ K) L ≫ snd K K ≫ g) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftTensorIso.{u, u + 1}
        (SimplicialCategory.sHom X Y) (SimplicialCategory.sHom Y Z)).inv ≫
        (SSet.uliftFunctor.{u + 1, u}).map (eComp SSet X Y Z) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleUniversalSeparatedExtension_exists X Y Z K f g).choose_spec.2

lemma controlledTriangleSeparatedExtension_diagonal :
    let c := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleCompositeFamily X Y Z K f g
    let L := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleLongHomSpace X Z K c
    (Δ[1] ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleParameterDiagonal K L) ≫ controlledTriangleSeparatedExtension X Y Z K f g =
      uncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleUniversalInterval X Z K c) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleUniversalSeparatedExtension_exists X Y Z K f g).choose_spec.1

/-- 同じ実 L 全体での再構成二胞体族。 -/
def controlledTriangleCoherentFamily :
    let L := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleLongHomSpace X Z K (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleCompositeFamily X Y Z K f g)
    (Δ[2] : SSet.{u + 1}) ⊗ (K ⊗ L) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleSeparatedFamily f g (controlledTriangleSeparatedExtension X Y Z K f g)
    (controlledTriangleSeparatedExtension_comp X Y Z K f g)

lemma controlledTriangleCoherentFamily_first :
    let L := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleLongHomSpace X Z K (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleCompositeFamily X Y Z K f g)
    (stdSimplex.δ (2 : Fin 3) ▷ (K ⊗ L)) ≫ controlledTriangleCoherentFamily X Y Z K f g =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (fst K L ≫ f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison X Y) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleSeparatedFamily_first f g _ (controlledTriangleSeparatedExtension_comp X Y Z K f g)

lemma controlledTriangleCoherentFamily_last :
    let L := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleLongHomSpace X Z K (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleCompositeFamily X Y Z K f g)
    (stdSimplex.δ (0 : Fin 3) ▷ (K ⊗ L)) ≫ controlledTriangleCoherentFamily X Y Z K f g =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (fst K L ≫ g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison Y Z) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleSeparatedFamily_last f g _ (controlledTriangleSeparatedExtension_comp X Y Z K f g)

/-- 実 L の同じ普遍長 Hom の直接評価を、全 K・L の標準 coherent 長辺として厳密回収。 -/
lemma controlledTriangleCoherentFamily_diagonal :
    let c := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleCompositeFamily X Y Z K f g
    let L := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleLongHomSpace X Z K c
    (stdSimplex.δ (1 : Fin 3) ▷ (K ⊗ L)) ≫ controlledTriangleCoherentFamily X Y Z K f g =
      (Δ[1] ◁ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (K ⊗ L) ≫ uncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleUniversalInterval X Z K c))) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison X Z) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleSeparatedFamily_diagonal f g _ (controlledTriangleSeparatedExtension_comp X Y Z K f g)
    _ (controlledTriangleSeparatedExtension_diagonal X Y Z K f g)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
