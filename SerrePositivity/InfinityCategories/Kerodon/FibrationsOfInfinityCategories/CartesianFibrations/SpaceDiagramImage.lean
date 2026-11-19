module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.SmallEnrichedNerve
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.InnerFibration
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.NerveFullyFaithful

/-! # 元の小さい底の空間値図式を含む、小さい全充満像の coherent nerve

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories

namespace SerrePositivity.KST.Fibration
end SerrePositivity.KST.Fibration
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
open _root_.SerrePositivity.KST.Fibration
variable {X : SSet.{u}} (F : (SSet.uliftFunctor.{u + 1, u}).obj X ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})

/-- 元の図式の全頂点の値そのものを許す。対象の同型類による置換はしない。 -/
def spaceDiagramImageObjects : ObjectProperty _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} :=
  fun K => ∃ x : X _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityObject (F.app (Opposite.op ⦋0⦌) (ULift.up x)) = K

/-- 元の値の全対象は、小さい底の頂点から全射で被覆される。 -/
instance spaceDiagramImageObjects_small :
    Small.{u} (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.spaceDiagramImageObjects F).FullSubcategory := by
  let g (x : X _⦋0⦌) : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.spaceDiagramImageObjects F).FullSubcategory :=
    ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityObject (F.app (Opposite.op ⦋0⦌) (ULift.up x)), ⟨x, rfl⟩⟩
  apply small_of_surjective (f := g)
  rintro ⟨K, x, hx⟩
  subst K
  exact ⟨x, rfl⟩

/-- 元の値とその間の全 Hom をそのまま保持する全充満像。 -/
def spaceDiagramImage : SSet.{u + 1} :=
  SimplicialNerve (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.spaceDiagramImageObjects F).FullSubcategory

instance spaceDiagramImage_obj_small (n : SimplexCategoryᵒᵖ) :
    Small.{u} ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.spaceDiagramImage F).obj n) := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.small_simplicialNerve_obj n

instance spaceDiagramImage_quasicategory : Quasicategory (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.spaceDiagramImage F) := by
  have (K L : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.spaceDiagramImageObjects F).FullSubcategory) :
      KanComplex (SimplicialCategory.sHom K L) :=
    inferInstanceAs (KanComplex ((ihom K.obj.obj).obj L.obj.obj))
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialNerve_quasicategory _

/-- 同じ元の空間の ∞ 圏への全充満像の実包含。 -/
def spaceDiagramImageInclusion : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.spaceDiagramImage F ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentFullSubcategoryInclusion (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.spaceDiagramImageObjects F)

/-- 包含の充満忠実性は、同じ元の豊穣 Hom の恒等写像から従う。 -/
theorem spaceDiagramImageInclusion_isFullyFaithful :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.spaceDiagramImageInclusion F) := by
  have (K L : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.spaceDiagramImageObjects F).FullSubcategory) :
      KanComplex (SimplicialCategory.sHom K L) :=
    inferInstanceAs (KanComplex ((ihom K.obj.obj).obj L.obj.obj))
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.coherentNerveMap_isFullyFaithful_iff
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.enrichedFullSubcategoryInclusion (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.spaceDiagramImageObjects F))).mpr
      (fun _ _ => (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence.refl _).isQCatEquivalence)

/-- 元の全図式を全充満像へ厳密に制限する。 -/
def spaceDiagramImageLift : (SSet.uliftFunctor.{u + 1, u}).obj X ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.spaceDiagramImage F :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentFullSubcategoryLift (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.spaceDiagramImageObjects F) F (by
    rintro ⟨x⟩
    exact ⟨x, rfl⟩)

/-- 制限後の包含との合成は、元の図式と全単体で厳密に一致する。 -/
theorem spaceDiagramImageLift_inclusion :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.spaceDiagramImageLift F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.spaceDiagramImageInclusion F = F :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentFullSubcategoryLift_inclusion _ _ _

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
