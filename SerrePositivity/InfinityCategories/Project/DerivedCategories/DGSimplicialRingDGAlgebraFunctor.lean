module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGSimplicialRingDGAlgebraNaturality
/-!
概要：任意の非可換単体環から dg 代数への実関手。
方針：同じ正規化鎖写像の単位・乗法保存を使い、恒等と合成を保持する。
規約：可換性や平坦性を仮定しない。使われ方：β5(g) の正規化界面。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory HomologicalComplex
open AlgebraicTopology AlgebraicTopology.DoldKan
open scoped TensorProduct _root_.Simplicial
def simplicialRingNormalizedDGAlgebraMap {A B : SimplicialObject RingCat.{u}}
    (f : A ⟶ B) : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedDGAlgebra A ⟶
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedDGAlgebra B where
  hom := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainMap f
  isMonHom_hom :=
    { one_hom := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainUnit_naturality f
      mul_hom := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainMultiplication_naturality f).symm }
def simplicialRingNormalizedDGAlgebraFunctor :
    SimplicialObject RingCat.{u} ⥤
      Mon (DifferentialGraded.Complex _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingCoefficient.{u}) where
  obj := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedDGAlgebra
  map := simplicialRingNormalizedDGAlgebraMap
  map_id A := Mon.Hom.ext (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainFunctor.map_id A)
  map_comp f g := Mon.Hom.ext (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainFunctor.map_comp f g)
lemma simplicialRingNormalizedDGAlgebraMap_hom
    {A B : SimplicialObject RingCat.{u}} (f : A ⟶ B) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedDGAlgebraMap f).hom = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainMap f := rfl
lemma simplicialRingNormalizedDGAlgebraMap_quasiIso_iff
    {A B : SimplicialObject RingCat.{u}} (f : A ⟶ B) :
    QuasiIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedDGAlgebraMap f).hom ↔
      QuasiIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedMap f) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainMap_quasiIso_iff f
end SerrePositivity.InfinityCategories.Project.DerivedCategories
