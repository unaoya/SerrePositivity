module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.ReflectiveMappingAdjunction

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.AdjunctionOfOpposite
public import SerrePositivity.KST.LocalizingInvariants.RelativeInitialAdjunction
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FunctorComparison.IntervalFunctorOpposite

/-!
概要：可逆な余単位候補と、その右随伴像への元の写像空間比較から実随伴を得る。
方針：反対圏の可逆な指定単位に F1B の局所随伴判定を適用して戻す。
規約：三角恒等式は結論で構成する。使われ方：Tamme Prop. 11 の差の実随伴。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

variable {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
  {F : X ⟶ Y} {G : Y ⟶ X}

lemma unitCondition_of_iso_localMapping (η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 X) (F ≫ G)) [IsIso η]
    (h : ∀ (x : X _⦋0⦌) (y : Y _⦋0⦌), _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap G (F.app (Opposite.op ⦋0⦌) x) y)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitMappingSpaceCondition η := by
  intro x y
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitPinchedMap_formula]
  have : IsIso (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatUnitComponent η x) := by
    change IsIso (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate η x)
    infer_instance
  exact ((h x y).isQCatEquivalence.comp
    (PinchedPrecompose.isQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatUnitComponent η x) _)
    ).isSimplicialHomotopyEquivalence

lemma reflectiveOppositeUnit_condition (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (G ≫ F) (𝟙 Y))
    (h : ∀ (x : X _⦋0⦌) (y : Y _⦋0⦌), _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap F x (G.app (Opposite.op ⦋0⦌) y))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitMappingSpaceCondition (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.reflectiveOppositeUnit e).hom := by
  apply unitCondition_of_iso_localMapping
  intro y x
  have hp := h (SSet.opObjEquiv x) (SSet.opObjEquiv y)
  have hi := hp.isQCatEquivalence.comp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace_isQCatEquivalence
    (F.app (Opposite.op ⦋0⦌) (SSet.opObjEquiv x))
    (F.app (Opposite.op ⦋0⦌) (G.app (Opposite.op ⦋0⦌) (SSet.opObjEquiv y))))
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.pinchedIntervalComparison_naturality] at hi
  have ho := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.intervalFunctorMap_op_isQCatEquivalence F _ _
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace_isQCatEquivalence _ _).cancel_left hi)
  exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pinchedHomMap_equivalence_of_intervalFunctorMap _ _ _ ho

/-- 元の局所比較と可逆余単位から、元の二関手の実随伴を構成する。 -/
def adjunctionOfReflectiveMapping (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (G ≫ F) (𝟙 Y))
    (h : ∀ (x : X _⦋0⦌) (y : Y _⦋0⦌), _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap F x (G.app (Opposite.op ⦋0⦌) y))) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction F G :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.adjunctionOfOpposite (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatAdjunctionOfUnitMappingSpaceCondition
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.reflectiveOppositeUnit e).hom (reflectiveOppositeUnit_condition e h))

end SerrePositivity.KST.LocalizingInvariants
