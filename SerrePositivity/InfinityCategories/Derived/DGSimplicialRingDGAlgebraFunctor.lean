module
public import SerrePositivity.InfinityCategories.Derived.DGSimplicialRingDGAlgebraNaturality
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory HomologicalComplex KST.ProExcision
open AlgebraicTopology AlgebraicTopology.DoldKan
open scoped TensorProduct Simplicial
def simplicialRingNormalizedDGAlgebraMap {A B : SimplicialObject RingCat.{u}}
    (f : A ⟶ B) : simplicialRingNormalizedDGAlgebra A ⟶
      simplicialRingNormalizedDGAlgebra B where
  hom := simplicialRingDGCochainMap f
  isMonHom_hom :=
    { one_hom := simplicialRingDGCochainUnit_naturality f
      mul_hom := (simplicialRingDGCochainMultiplication_naturality f).symm }
def simplicialRingNormalizedDGAlgebraFunctor :
    SimplicialObject RingCat.{u} ⥤
      Mon (DifferentialGraded.Complex simplicialRingCoefficient.{u}) where
  obj := simplicialRingNormalizedDGAlgebra
  map := simplicialRingNormalizedDGAlgebraMap
  map_id A := Mon.Hom.ext (simplicialRingDGCochainFunctor.map_id A)
  map_comp f g := Mon.Hom.ext (simplicialRingDGCochainFunctor.map_comp f g)
lemma simplicialRingNormalizedDGAlgebraMap_hom
    {A B : SimplicialObject RingCat.{u}} (f : A ⟶ B) :
    (simplicialRingNormalizedDGAlgebraMap f).hom = simplicialRingDGCochainMap f := rfl
lemma simplicialRingNormalizedDGAlgebraMap_quasiIso_iff
    {A B : SimplicialObject RingCat.{u}} (f : A ⟶ B) :
    QuasiIso (simplicialRingNormalizedDGAlgebraMap f).hom ↔
      QuasiIso (simplicialRingNormalizedMap f) :=
  simplicialRingDGCochainMap_quasiIso_iff f
end SerrePositivity.InfinityCategories
