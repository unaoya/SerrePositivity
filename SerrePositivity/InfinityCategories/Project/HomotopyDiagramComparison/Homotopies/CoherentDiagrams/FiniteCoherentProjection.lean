module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.CoherentDiagrams.CoherentProjectionUnitComparison
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.CoherentDiagrams.FiniteCoherentProductTotalMap
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.VertexTransport.FunctorIsoTransport

/-!
概要：有限 coherent 積の元の反復射影変換と、その全空間作用・指定単位の比較。
方針：元の二項射影を指定三角形で合成し、同じ三角形の相対比較を反復する。
規約：元の各因子・全空間射影・単位を保持。底の quasicategory 性は不要。
使われ方：native な有限積の全脚の余錐作用の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

/-- 元の二項射影から指定三角形で合成した、各因子への coherent な反復射影。 -/
def finiteCoherentProjectionVertex {B : SSet.{u}} : (n : ℕ) →
    (F : Fin (n + 1) → ((SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})) →
    (i : Fin (n + 1)) →
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningTransformationSpace (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteCoherentSpaceProduct n F) (F i)) _⦋0⦌
  | 0, F, i => by
      have hi : i = 0 := Fin.eq_zero i
      subst i
      exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentIdentityTransformationVertex (F 0)
  | n + 1, F, i => Fin.cases
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentSpaceTensorProductFstVertex (F 0)
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteCoherentSpaceProduct n (fun j ↦ F j.succ)))
      (fun j ↦ (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentTransformationVertexTriangle _ _ _
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentSpaceTensorProductSndVertex (F 0)
          (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteCoherentSpaceProduct n (fun k ↦ F k.succ)))
        (finiteCoherentProjectionVertex n (fun k ↦ F k.succ) j)).diagonal) i

/-- 元の反復射影変換の作用は、元の単位の後で元の反復全空間射影と同型。 -/
def finiteCoherentProjectionUnitIso (n : ℕ) {B : SSet.{u}}
    (F : Fin (n + 1) → ((SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}))
    (i : Fin (n + 1)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentTransformationTotalMap (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteCoherentSpaceProduct n F) (F i)
      (finiteCoherentProjectionVertex n F i) ≫ _root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalUnit (F i))
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteCoherentSpaceProductTotalProjection n F i ≫ _root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalUnit (F i)) := by
  induction n with
  | zero =>
    have hi : i = 0 := Fin.eq_zero i
    subst i
    simpa only [finiteCoherentProjectionVertex, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteCoherentSpaceProduct,
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteCoherentSpaceProductTotalProjection, eqToHom_refl, Category.id_comp] using
        _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentIdentityTransformationUnitIso (F 0)
  | succ n ih =>
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · exact Iso.refl _
    · let G := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteCoherentSpaceProduct n (fun k ↦ F k.succ)
      let x := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentSpaceTensorProductSndVertex (F 0) G
      let y := finiteCoherentProjectionVertex n (fun k ↦ F k.succ) j
      let T := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentTransformationVertexTriangle (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteCoherentSpaceProduct (n + 1) F)
        G (F j.succ) x y
      have e := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransformationTriangleUnitIso _ G (F j.succ) x y T
      have d := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (ih (fun k ↦ F k.succ) j)
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentSpaceTensorProductTotalSnd (F 0) G)
      change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentTransformationTotalMap _ _ T.diagonal ≫
        _root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalUnit (F j.succ))
        ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentSpaceTensorProductTotalSnd (F 0) G ≫
          _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteCoherentSpaceProductTotalProjection n (fun k ↦ F k.succ) j) ≫
            _root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalUnit (F j.succ))
      exact _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (e ≪≫ d) rfl (Category.assoc _ _ _).symm

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
