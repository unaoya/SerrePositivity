module

public import SerrePositivity.EInfinity.Hammock.ValueSupportSubcomplex
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
namespace SerrePositivity.EInfinity.Hammock.ValueSupport
open CategoryTheory Limits
attribute [local instance] Classical.propDecidable

variable {B : Type u} {X : SSet.{u}} (ℓ : X ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B)

def diagram : Finset B ⥤ SSet.{u} where
  obj S := (subcomplex ℓ (S : Set B)).toFunctor
  map h := SSet.Subcomplex.homOfLE (subcomplex_mono ℓ (leOfHom h))
  map_id _ := rfl
  map_comp _ _ := rfl

def cocone : Cocone (diagram ℓ) where
  pt := X
  ι :=
    { app S := (subcomplex ℓ (S : Set B)).ι
      naturality _ _ _ := rfl }

def degreeCocone (n : SimplexCategoryᵒᵖ) :
    Cocone (diagram ℓ ⋙ (evaluation _ (Type u)).obj n) :=
  ((evaluation _ (Type u)).obj n).mapCocone (cocone ℓ)

lemma degree_surjective (n : SimplexCategoryᵒᵖ) (x : X.obj n) :
    ∃ S y, x = (degreeCocone ℓ n).ι.app S y :=
  ⟨{ℓ.app n x}, ⟨x, Finset.mem_singleton_self _⟩, rfl⟩

lemma degree_equal (n : SimplexCategoryᵒᵖ) (S R : Finset B)
    (x : ((diagram ℓ).obj S).obj n) (y : ((diagram ℓ).obj R).obj n)
    (h : (degreeCocone ℓ n).ι.app S x = (degreeCocone ℓ n).ι.app R y) :
    ∃ (U : Finset B) (f : S ⟶ U) (g : R ⟶ U),
      ((diagram ℓ).map f).app n x = ((diagram ℓ).map g).app n y := by
  refine ⟨S ∪ R, homOfLE Finset.subset_union_left, homOfLE Finset.subset_union_right, ?_⟩
  exact Subtype.ext h

def degree_isColimit (n : SimplexCategoryᵒᵖ) : IsColimit (degreeCocone ℓ n) :=
  Types.FilteredColimit.isColimitOf _ _ (degree_surjective ℓ n) (degree_equal ℓ n)

def cocone_isColimit : IsColimit (cocone ℓ) :=
  evaluationJointlyReflectsColimits _ (degree_isColimit ℓ)

def colimitIso : colimit (diagram ℓ) ≅ X :=
  (colimit.isColimit _).coconePointUniqueUpToIso (cocone_isColimit ℓ)

lemma colimitIso_fac (S : Finset B) :
    colimit.ι (diagram ℓ) S ≫ (colimitIso ℓ).hom = (subcomplex ℓ (S : Set B)).ι :=
  (colimit.isColimit _).comp_coconePointUniqueUpToIso_hom (cocone_isColimit ℓ) S

variable {Y : SSet.{u}} (μ : Y ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B)
  (f : X ⟶ Y) (h : f ≫ μ = ℓ)

def diagramMap : diagram ℓ ⟶ diagram μ where
  app S := restriction ℓ μ f h (S : Set B)
  naturality _ _ _ := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    rfl

lemma colimitIso_naturality :
    colim.map (diagramMap ℓ μ f h) ≫ (colimitIso μ).hom = (colimitIso ℓ).hom ≫ f := by
  apply colimit.hom_ext
  intro S
  rw [← Category.assoc, colimit.ι_map, Category.assoc, colimitIso_fac,
    ← Category.assoc, colimitIso_fac]
  exact restriction_inclusion ℓ μ f h (S : Set B)

end SerrePositivity.EInfinity.Hammock.ValueSupport
