module

public import SerrePositivity.KST.Spectra.D3BiParameterFaces
public import SerrePositivity.KST.Spectra.D3PointedKanUnitIso

/-!
概要：実二方向端点図式の外側の三角を、元の恒等作用と通常 loop 作用へ接続する。
方針：同じ全パラメータ図式の角を回収し、パラメータ単位子と既証の全 Hom 同型を合成。
規約：二重 loop の交換や模型単位三角形の可換性は結論しない。
使われ方：二方向全図式を元の loop 模型と比較するときの、指定外側境界の正規化。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF

/-- 同じ二方向図式の厳密な最終角と、元の恒等 Kan 作用との全関手比較。 -/
def d3DoubleEndpointTargetIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (d3DoubleEndpointSquare.{u} ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt ((stdSimplex.obj₀Equiv.symm (1 : Fin 2), stdSimplex.obj₀Equiv.symm 1),
        (stdSimplex.obj₀Equiv.symm (1 : Fin 2), stdSimplex.obj₀Equiv.symm 1)))
      (𝟙 PointedKanInfinity) := by
  rw [d3DoubleEndpointSquare, d3PointedKanBiParameterSquare_corner]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap
    (d3PointedKanIhom ((𝟙_ PointedSimplicialSet.{u}) ⊗ 𝟙_ PointedSimplicialSet.{u}))) _
  exact d3PointedKanPreFunctorIso (λ_ (𝟙_ PointedSimplicialSet.{u})).inv ≪≫
    d3PointedKanUnitFunctorIso

/-- 第一方向の始点と第二方向の終点で、同じ元の通常 loop 作用を回収する。 -/
def d3DoubleEndpointLeftLoopIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (d3DoubleEndpointSquare.{u} ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt ((stdSimplex.obj₀Equiv.symm (0 : Fin 2), stdSimplex.obj₀Equiv.symm 0),
        (stdSimplex.obj₀Equiv.symm (1 : Fin 2), stdSimplex.obj₀Equiv.symm 1)))
      pointedKanLoopInfinity := by
  rw [d3DoubleEndpointSquare, d3PointedKanBiParameterSquare_corner]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap
    (d3PointedKanIhom (endpointCircle.{u} ⊗ 𝟙_ PointedSimplicialSet.{u}))) _
  exact d3PointedKanPreFunctorIso (ρ_ endpointCircle.{u}).inv ≪≫
    d3PointedKanEndpointLoopIso.symm

/-- 第二方向の始点と第一方向の終点も、同じ元の通常 loop 作用へ全 Hom 上で比較する。 -/
def d3DoubleEndpointRightLoopIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (d3DoubleEndpointSquare.{u} ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt ((stdSimplex.obj₀Equiv.symm (1 : Fin 2), stdSimplex.obj₀Equiv.symm 1),
        (stdSimplex.obj₀Equiv.symm (0 : Fin 2), stdSimplex.obj₀Equiv.symm 0)))
      pointedKanLoopInfinity := by
  rw [d3DoubleEndpointSquare, d3PointedKanBiParameterSquare_corner]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap
    (d3PointedKanIhom ((𝟙_ PointedSimplicialSet.{u}) ⊗ endpointCircle.{u}))) _
  exact d3PointedKanPreFunctorIso (λ_ endpointCircle.{u}).inv ≪≫
    d3PointedKanEndpointLoopIso.symm

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
