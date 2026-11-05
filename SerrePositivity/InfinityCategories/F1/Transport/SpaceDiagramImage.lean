module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
public import SerrePositivity.InfinityCategories.F1.Transport.SmallEnrichedNerve
public import SerrePositivity.InfinityCategories.F1.Universe.InnerFibration
public import SerrePositivity.InfinityCategories.F1.Coherent.NerveFullyFaithful

/-! # 元の小さい底の空間値図式を含む、小さい全充満像の coherent nerve -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.InfinityCategories.HomotopyLimits
namespace SerrePositivity.KST.Fibration
end SerrePositivity.KST.Fibration
namespace SerrePositivity.InfinityCategories.F1.Transport
open SerrePositivity.KST.Fibration
variable {X : SSet.{u}} (F : (SSet.uliftFunctor.{u + 1, u}).obj X ⟶ SpaceInfinity.{u})

/-- 元の図式の全頂点の値そのものを許す。対象の同型類による置換はしない。 -/
def spaceDiagramImageObjects : ObjectProperty KanObject.{u} :=
  fun K => ∃ x : X _⦋0⦌, spaceInfinityObject (F.app (Opposite.op ⦋0⦌) (ULift.up x)) = K

/-- 元の値の全対象は、小さい底の頂点から全射で被覆される。 -/
instance spaceDiagramImageObjects_small :
    Small.{u} (_root_.SerrePositivity.InfinityCategories.F1.Transport.spaceDiagramImageObjects F).FullSubcategory := by
  let g (x : X _⦋0⦌) : (_root_.SerrePositivity.InfinityCategories.F1.Transport.spaceDiagramImageObjects F).FullSubcategory :=
    ⟨spaceInfinityObject (F.app (Opposite.op ⦋0⦌) (ULift.up x)), ⟨x, rfl⟩⟩
  apply small_of_surjective (f := g)
  rintro ⟨K, x, hx⟩
  subst K
  exact ⟨x, rfl⟩

/-- 元の値とその間の全 Hom をそのまま保持する全充満像。 -/
def spaceDiagramImage : SSet.{u + 1} :=
  SimplicialNerve (_root_.SerrePositivity.InfinityCategories.F1.Transport.spaceDiagramImageObjects F).FullSubcategory

instance spaceDiagramImage_obj_small (n : SimplexCategoryᵒᵖ) :
    Small.{u} ((_root_.SerrePositivity.InfinityCategories.F1.Transport.spaceDiagramImage F).obj n) := _root_.SerrePositivity.InfinityCategories.F1.Transport.small_simplicialNerve_obj n

instance spaceDiagramImage_quasicategory : Quasicategory (_root_.SerrePositivity.InfinityCategories.F1.Transport.spaceDiagramImage F) := by
  have (K L : (_root_.SerrePositivity.InfinityCategories.F1.Transport.spaceDiagramImageObjects F).FullSubcategory) :
      KanComplex (SimplicialCategory.sHom K L) :=
    inferInstanceAs (KanComplex ((ihom K.obj.obj).obj L.obj.obj))
  exact Coherent.simplicialNerve_quasicategory _

/-- 同じ元の空間の ∞ 圏への全充満像の実包含。 -/
def spaceDiagramImageInclusion : _root_.SerrePositivity.InfinityCategories.F1.Transport.spaceDiagramImage F ⟶ SpaceInfinity.{u} :=
  coherentFullSubcategoryInclusion (_root_.SerrePositivity.InfinityCategories.F1.Transport.spaceDiagramImageObjects F)

/-- 包含の充満忠実性は、同じ元の豊穣 Hom の恒等写像から従う。 -/
theorem spaceDiagramImageInclusion_isFullyFaithful :
    IsFullyFaithful (_root_.SerrePositivity.InfinityCategories.F1.Transport.spaceDiagramImageInclusion F) := by
  have (K L : (_root_.SerrePositivity.InfinityCategories.F1.Transport.spaceDiagramImageObjects F).FullSubcategory) :
      KanComplex (SimplicialCategory.sHom K L) :=
    inferInstanceAs (KanComplex ((ihom K.obj.obj).obj L.obj.obj))
  exact (coherentNerveMap_isFullyFaithful_iff
    (enrichedFullSubcategoryInclusion (_root_.SerrePositivity.InfinityCategories.F1.Transport.spaceDiagramImageObjects F))).mpr
      (fun _ _ => (QCatEquivalence.refl _).isQCatEquivalence)

/-- 元の全図式を全充満像へ厳密に制限する。 -/
def spaceDiagramImageLift : (SSet.uliftFunctor.{u + 1, u}).obj X ⟶ _root_.SerrePositivity.InfinityCategories.F1.Transport.spaceDiagramImage F :=
  coherentFullSubcategoryLift (_root_.SerrePositivity.InfinityCategories.F1.Transport.spaceDiagramImageObjects F) F (by
    rintro ⟨x⟩
    exact ⟨x, rfl⟩)

/-- 制限後の包含との合成は、元の図式と全単体で厳密に一致する。 -/
theorem spaceDiagramImageLift_inclusion :
    _root_.SerrePositivity.InfinityCategories.F1.Transport.spaceDiagramImageLift F ≫ _root_.SerrePositivity.InfinityCategories.F1.Transport.spaceDiagramImageInclusion F = F :=
  coherentFullSubcategoryLift_inclusion _ _ _

end SerrePositivity.InfinityCategories.F1.Transport

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.F1.Transport.spaceDiagramImage (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.spaceDiagramImage := _root_.SerrePositivity.InfinityCategories.F1.Transport.spaceDiagramImage

@[deprecated _root_.SerrePositivity.InfinityCategories.F1.Transport.spaceDiagramImageInclusion (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.spaceDiagramImageInclusion := _root_.SerrePositivity.InfinityCategories.F1.Transport.spaceDiagramImageInclusion

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.spaceDiagramImageInclusion_isFullyFaithful := _root_.SerrePositivity.InfinityCategories.F1.Transport.spaceDiagramImageInclusion_isFullyFaithful

@[deprecated _root_.SerrePositivity.InfinityCategories.F1.Transport.spaceDiagramImageLift (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.spaceDiagramImageLift := _root_.SerrePositivity.InfinityCategories.F1.Transport.spaceDiagramImageLift

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.spaceDiagramImageLift_inclusion := _root_.SerrePositivity.InfinityCategories.F1.Transport.spaceDiagramImageLift_inclusion

@[deprecated _root_.SerrePositivity.InfinityCategories.F1.Transport.spaceDiagramImageObjects (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.spaceDiagramImageObjects := _root_.SerrePositivity.InfinityCategories.F1.Transport.spaceDiagramImageObjects

@[deprecated _root_.SerrePositivity.InfinityCategories.F1.Transport.spaceDiagramImageObjects_small (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.spaceDiagramImageObjects_small := _root_.SerrePositivity.InfinityCategories.F1.Transport.spaceDiagramImageObjects_small

@[deprecated _root_.SerrePositivity.InfinityCategories.F1.Transport.spaceDiagramImage_obj_small (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.spaceDiagramImage_obj_small := _root_.SerrePositivity.InfinityCategories.F1.Transport.spaceDiagramImage_obj_small

@[deprecated _root_.SerrePositivity.InfinityCategories.F1.Transport.spaceDiagramImage_quasicategory (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.spaceDiagramImage_quasicategory := _root_.SerrePositivity.InfinityCategories.F1.Transport.spaceDiagramImage_quasicategory

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.spaceDiagramImageLift._proof_1 := _root_.SerrePositivity.InfinityCategories.F1.Transport.spaceDiagramImageLift._proof_1
