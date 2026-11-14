module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.DGSimplicialRingCochainNormalization
public import SerrePositivity.DifferentialGraded.Complexes.HomComplex
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Ring.ULift
/-!
概要：単体環の実正規化 cochain 複体を同宇宙の整数係数の dg 複体へ移す。
方針：ULift 整数との実加群圏同値を複体へ適用する。
規約：元の対象宇宙と各成分の作用を保つ。使われ方：β5(g) の標準 dg 代数化。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology
open HomologicalComplex
abbrev simplicialRingCoefficient : Type u := ULift.{u} ℤ
def simplicialRingIntegerModuleEquivalence :
    ModuleCat.{u} ℤ ≌ ModuleCat.{u} simplicialRingCoefficient.{u} :=
  ModuleCat.restrictScalarsEquivalenceOfRingEquiv
    (ULift.ringEquiv : simplicialRingCoefficient.{u} ≃+* ℤ)
instance simplicialRingIntegerModuleEquivalence_additive :
    simplicialRingIntegerModuleEquivalence.{u}.functor.Additive := by
  change (ModuleCat.restrictScalars
    (ULift.ringEquiv : simplicialRingCoefficient.{u} ≃+* ℤ).toRingHom).Additive
  infer_instance
def simplicialRingDGCochainFunctor :
    SimplicialObject RingCat.{u} ⥤ DifferentialGraded.Complex simplicialRingCoefficient.{u} :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingCochainFunctor ⋙
    (simplicialRingIntegerModuleEquivalence.{u}.mapHomologicalComplex (.up ℤ)).functor
abbrev simplicialRingNormalizedDGComplex (A : SimplicialObject RingCat.{u}) :=
  simplicialRingDGCochainFunctor.obj A
abbrev simplicialRingDGCochainMap {A B : SimplicialObject RingCat.{u}} (f : A ⟶ B) :=
  simplicialRingDGCochainFunctor.map f
lemma simplicialRingDGCochainMap_component {A B : SimplicialObject RingCat.{u}}
    (f : A ⟶ B) (k : ℤ) :
    (simplicialRingDGCochainMap f).f k =
      simplicialRingIntegerModuleEquivalence.{u}.functor.map
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingCochainMap f).f k) := rfl
lemma simplicialRingNormalizedDGComplex_positive_zero (A : SimplicialObject RingCat.{u})
    (k : ℤ) (hk : 0 < k) : IsZero ((simplicialRingNormalizedDGComplex A).X k) :=
  Functor.map_isZero simplicialRingIntegerModuleEquivalence.{u}.functor
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingCochain_positive_zero A k hk)
lemma simplicialRingDGCochainMap_quasiIso_iff
    {A B : SimplicialObject RingCat.{u}} (f : A ⟶ B) :
    QuasiIso (simplicialRingDGCochainMap f) ↔ QuasiIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedMap f) :=
  (HomologicalComplex.quasiIso_map_iff_of_preservesHomology (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingCochainMap f)
    simplicialRingIntegerModuleEquivalence.{u}.functor).trans
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingCochainMap_quasiIso_iff f)
instance simplicialRingDGCochainMap_quasiIso
    {A B : SimplicialObject RingCat.{u}} (f : A ⟶ B)
    [QuasiIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedMap f)] : QuasiIso (simplicialRingDGCochainMap f) :=
  (simplicialRingDGCochainMap_quasiIso_iff f).mpr inferInstance
end SerrePositivity.InfinityCategories.Project.DerivedCategories
