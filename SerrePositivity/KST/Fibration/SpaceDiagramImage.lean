module
public import SerrePositivity.KST.Fibration.SmallEnrichedNerve
public import SerrePositivity.InfinityCategories.F1.UniverseInnerFibration
public import SerrePositivity.InfinityCategories.F1.CoherentNerveFullyFaithful

/-! # 元の小さい底の空間値図式を含む、小さい全充満像の coherent nerve -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.InfinityCategories.HomotopyLimits
namespace SerrePositivity.KST.Fibration
variable {X : SSet.{u}} (F : (SSet.uliftFunctor.{u + 1, u}).obj X ⟶ SpaceInfinity.{u})

/-- 元の図式の全頂点の値そのものを許す。対象の同型類による置換はしない。 -/
def spaceDiagramImageObjects : ObjectProperty KanObject.{u} :=
  fun K => ∃ x : X _⦋0⦌, spaceInfinityObject (F.app (Opposite.op ⦋0⦌) (ULift.up x)) = K

/-- 元の値の全対象は、小さい底の頂点から全射で被覆される。 -/
instance spaceDiagramImageObjects_small :
    Small.{u} (spaceDiagramImageObjects F).FullSubcategory := by
  let g (x : X _⦋0⦌) : (spaceDiagramImageObjects F).FullSubcategory :=
    ⟨spaceInfinityObject (F.app (Opposite.op ⦋0⦌) (ULift.up x)), ⟨x, rfl⟩⟩
  apply small_of_surjective (f := g)
  rintro ⟨K, x, hx⟩
  subst K
  exact ⟨x, rfl⟩

/-- 元の値とその間の全 Hom をそのまま保持する全充満像。 -/
def spaceDiagramImage : SSet.{u + 1} :=
  SimplicialNerve (spaceDiagramImageObjects F).FullSubcategory

instance spaceDiagramImage_obj_small (n : SimplexCategoryᵒᵖ) :
    Small.{u} ((spaceDiagramImage F).obj n) := small_simplicialNerve_obj n

instance spaceDiagramImage_quasicategory : Quasicategory (spaceDiagramImage F) := by
  have (K L : (spaceDiagramImageObjects F).FullSubcategory) :
      KanComplex (SimplicialCategory.sHom K L) :=
    inferInstanceAs (KanComplex ((ihom K.obj.obj).obj L.obj.obj))
  exact Coherent.simplicialNerve_quasicategory _

/-- 同じ元の空間の ∞ 圏への全充満像の実包含。 -/
def spaceDiagramImageInclusion : spaceDiagramImage F ⟶ SpaceInfinity.{u} :=
  coherentFullSubcategoryInclusion (spaceDiagramImageObjects F)

/-- 包含の充満忠実性は、同じ元の豊穣 Hom の恒等写像から従う。 -/
theorem spaceDiagramImageInclusion_isFullyFaithful :
    IsFullyFaithful (spaceDiagramImageInclusion F) := by
  have (K L : (spaceDiagramImageObjects F).FullSubcategory) :
      KanComplex (SimplicialCategory.sHom K L) :=
    inferInstanceAs (KanComplex ((ihom K.obj.obj).obj L.obj.obj))
  exact (coherentNerveMap_isFullyFaithful_iff
    (enrichedFullSubcategoryInclusion (spaceDiagramImageObjects F))).mpr
      (fun _ _ => (QCatEquivalence.refl _).isQCatEquivalence)

/-- 元の全図式を全充満像へ厳密に制限する。 -/
def spaceDiagramImageLift : (SSet.uliftFunctor.{u + 1, u}).obj X ⟶ spaceDiagramImage F :=
  coherentFullSubcategoryLift (spaceDiagramImageObjects F) F (by
    rintro ⟨x⟩
    exact ⟨x, rfl⟩)

/-- 制限後の包含との合成は、元の図式と全単体で厳密に一致する。 -/
theorem spaceDiagramImageLift_inclusion :
    spaceDiagramImageLift F ≫ spaceDiagramImageInclusion F = F :=
  coherentFullSubcategoryLift_inclusion _ _ _

end SerrePositivity.KST.Fibration
