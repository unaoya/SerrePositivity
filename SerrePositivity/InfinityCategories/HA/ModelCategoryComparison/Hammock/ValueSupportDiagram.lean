module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ValueSupportSubcomplex
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.Data.Finset.Lattice.Basic

/-!
# 元の有限個の値の部分複体の全図式

概要：有限集合で添字付けた元の部分複体の余極限は元の全体と同型。
方針：各単体を singleton へ持ち上げ、和集合で等式を回収する。
規約：元の全標準射と元の全体への包含を保持する。
使われ方：各値の fiber の弱可縮性を元の評価自身へ移す。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ValueSupport
open _root_.CategoryTheory _root_.CategoryTheory.Limits
attribute [local instance] Classical.propDecidable

variable {B : Type u} {X : SSet.{u}} (ℓ : X ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B)

def diagram : Finset B ⥤ SSet.{u} where
  obj S := (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ValueSupport.subcomplex ℓ (S : Set B)).toFunctor
  map h := SSet.Subcomplex.homOfLE (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ValueSupport.subcomplex_mono ℓ (leOfHom h))
  map_id _ := rfl
  map_comp _ _ := rfl

def cocone : Cocone (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ValueSupport.diagram ℓ) where
  pt := X
  ι :=
    { app S := (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ValueSupport.subcomplex ℓ (S : Set B)).ι
      naturality _ _ _ := rfl }

def degreeCocone (n : SimplexCategoryᵒᵖ) :
    Cocone (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ValueSupport.diagram ℓ ⋙ (evaluation _ (Type u)).obj n) :=
  ((evaluation _ (Type u)).obj n).mapCocone (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ValueSupport.cocone ℓ)

lemma degree_surjective (n : SimplexCategoryᵒᵖ) (x : X.obj n) :
    ∃ S y, x = (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ValueSupport.degreeCocone ℓ n).ι.app S y :=
  ⟨{ℓ.app n x}, ⟨x, Finset.mem_singleton_self _⟩, rfl⟩

lemma degree_equal (n : SimplexCategoryᵒᵖ) (S R : Finset B)
    (x : ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ValueSupport.diagram ℓ).obj S).obj n) (y : ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ValueSupport.diagram ℓ).obj R).obj n)
    (h : (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ValueSupport.degreeCocone ℓ n).ι.app S x = (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ValueSupport.degreeCocone ℓ n).ι.app R y) :
    ∃ (U : Finset B) (f : S ⟶ U) (g : R ⟶ U),
      ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ValueSupport.diagram ℓ).map f).app n x = ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ValueSupport.diagram ℓ).map g).app n y := by
  refine ⟨S ∪ R, homOfLE Finset.subset_union_left, homOfLE Finset.subset_union_right, ?_⟩
  exact Subtype.ext h

def degree_isColimit (n : SimplexCategoryᵒᵖ) : IsColimit (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ValueSupport.degreeCocone ℓ n) :=
  Types.FilteredColimit.isColimitOf _ _ (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ValueSupport.degree_surjective ℓ n) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ValueSupport.degree_equal ℓ n)

def cocone_isColimit : IsColimit (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ValueSupport.cocone ℓ) :=
  evaluationJointlyReflectsColimits _ (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ValueSupport.degree_isColimit ℓ)

def colimitIso : colimit (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ValueSupport.diagram ℓ) ≅ X :=
  (colimit.isColimit _).coconePointUniqueUpToIso (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ValueSupport.cocone_isColimit ℓ)

lemma colimitIso_fac (S : Finset B) :
    colimit.ι (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ValueSupport.diagram ℓ) S ≫ (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ValueSupport.colimitIso ℓ).hom = (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ValueSupport.subcomplex ℓ (S : Set B)).ι :=
  (colimit.isColimit _).comp_coconePointUniqueUpToIso_hom (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ValueSupport.cocone_isColimit ℓ) S

variable {Y : SSet.{u}} (μ : Y ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B)
  (f : X ⟶ Y) (h : f ≫ μ = ℓ)

def diagramMap : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ValueSupport.diagram ℓ ⟶ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ValueSupport.diagram μ where
  app S := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ValueSupport.restriction ℓ μ f h (S : Set B)
  naturality _ _ _ := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    rfl

lemma colimitIso_naturality :
    colim.map (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ValueSupport.diagramMap ℓ μ f h) ≫ (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ValueSupport.colimitIso μ).hom = (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ValueSupport.colimitIso ℓ).hom ≫ f := by
  apply colimit.hom_ext
  intro S
  rw [← Category.assoc, colimit.ι_map, Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ValueSupport.colimitIso_fac,
    ← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ValueSupport.colimitIso_fac]
  exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ValueSupport.restriction_inclusion ℓ μ f h (S : Set B)

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ValueSupport
