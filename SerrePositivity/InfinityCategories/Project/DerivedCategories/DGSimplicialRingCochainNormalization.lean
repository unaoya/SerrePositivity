module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGSimplicialRingNormalizedDegreeLaws
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.CategoryTheory.Whiskering
/-!
概要：単体環の実 Moore 正規化を非正次数の cochain 複体へ移す。
方針：次数反転の零延長関手とその成分・微分・準同型比較を使う。
規約：元の正規化鎖写像を保つ。使われ方：β5(g) の dg 代数化。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology
open AlgebraicTopology.DoldKan HomologicalComplex
open scoped _root_.Simplicial

def simplicialRingNormalizationFunctor :
    SimplicialObject RingCat.{u} ⥤ ChainComplex (ModuleCat.{u} ℤ) ℕ :=
  ((Functor.whiskeringRight SimplexCategoryᵒᵖ RingCat.{u} (ModuleCat.{u} ℤ)).obj
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ringIntegerModuleFunctor) ⋙ normalizedMooreComplex _
def simplicialRingCochainFunctor :
    SimplicialObject RingCat.{u} ⥤ CochainComplex (ModuleCat.{u} ℤ) ℤ :=
  simplicialRingNormalizationFunctor ⋙ ComplexShape.embeddingDownNat.extendFunctor _
abbrev simplicialRingNormalizedCochain (A : SimplicialObject RingCat.{u}) :=
  simplicialRingCochainFunctor.obj A
abbrev simplicialRingCochainMap {A B : SimplicialObject RingCat.{u}} (f : A ⟶ B) :=
  simplicialRingCochainFunctor.map f
def simplicialRingCochainDegreeIso (A : SimplicialObject RingCat.{u}) (n : ℕ) :
    (simplicialRingNormalizedCochain A).X (-(n : ℤ)) ≅ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedChains A).X n :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedChains A).extendXIso ComplexShape.embeddingDownNat (i := n) rfl
lemma simplicialRingCochain_positive_zero (A : SimplicialObject RingCat.{u})
    (k : ℤ) (hk : 0 < k) : IsZero ((simplicialRingNormalizedCochain A).X k) := by
  apply (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedChains A).isZero_extend_X ComplexShape.embeddingDownNat
  intro n
  change -(n : ℤ) ≠ k
  omega
lemma simplicialRingCochain_d (A : SimplicialObject RingCat.{u}) (n : ℕ) :
    (simplicialRingNormalizedCochain A).d (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) =
      (simplicialRingCochainDegreeIso A (n + 1)).hom ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedChains A).d (n + 1) n ≫
          (simplicialRingCochainDegreeIso A n).inv :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedChains A).extend_d_eq ComplexShape.embeddingDownNat
    (i := n + 1) (j := n) rfl rfl
lemma simplicialRingCochainMap_degree {A B : SimplicialObject RingCat.{u}} (f : A ⟶ B) (n : ℕ) :
    (simplicialRingCochainMap f).f (-(n : ℤ)) =
      (simplicialRingCochainDegreeIso A n).hom ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedMap f).f n ≫
        (simplicialRingCochainDegreeIso B n).inv :=
  HomologicalComplex.extendMap_f (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedMap f)
    ComplexShape.embeddingDownNat (i := n) rfl
lemma simplicialRingCochainMap_quasiIso_iff
    {A B : SimplicialObject RingCat.{u}} (f : A ⟶ B) :
    QuasiIso (simplicialRingCochainMap f) ↔ QuasiIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedMap f) :=
  HomologicalComplex.quasiIso_extendMap_iff (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedMap f)
    ComplexShape.embeddingDownNat
instance simplicialRingCochainMap_quasiIso
    {A B : SimplicialObject RingCat.{u}} (f : A ⟶ B)
    [QuasiIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedMap f)] : QuasiIso (simplicialRingCochainMap f) :=
  (simplicialRingCochainMap_quasiIso_iff f).mpr inferInstance
end SerrePositivity.InfinityCategories.Project.DerivedCategories
