module

public import SerrePositivity.InfinityCategories.HomotopyLimits.CoherentProjectionUnitComparison
public import SerrePositivity.InfinityCategories.HomotopyLimits.FiniteCoherentProductTotalMap
public import SerrePositivity.InfinityCategories.F2.FunctorIsoTransport

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
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 元の二項射影から指定三角形で合成した、各因子への coherent な反復射影。 -/
def finiteCoherentProjectionVertex {B : SSet.{u}} : (n : ℕ) →
    (F : Fin (n + 1) → ((SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})) →
    (i : Fin (n + 1)) →
      (leftUnstraighteningTransformationSpace (finiteCoherentSpaceProduct n F) (F i)) _⦋0⦌
  | 0, F, i => by
      have hi : i = 0 := Fin.eq_zero i
      subst i
      exact coherentIdentityTransformationVertex (F 0)
  | n + 1, F, i => Fin.cases
      (coherentSpaceTensorProductFstVertex (F 0)
        (finiteCoherentSpaceProduct n (fun j ↦ F j.succ)))
      (fun j ↦ (F2.coherentTransformationVertexTriangle _ _ _
        (coherentSpaceTensorProductSndVertex (F 0)
          (finiteCoherentSpaceProduct n (fun k ↦ F k.succ)))
        (finiteCoherentProjectionVertex n (fun k ↦ F k.succ) j)).diagonal) i

/-- 元の反復射影変換の作用は、元の単位の後で元の反復全空間射影と同型。 -/
def finiteCoherentProjectionUnitIso (n : ℕ) {B : SSet.{u}}
    (F : Fin (n + 1) → ((SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}))
    (i : Fin (n + 1)) :
    FunctorIso (F2.coherentTransformationTotalMap (finiteCoherentSpaceProduct n F) (F i)
      (finiteCoherentProjectionVertex n F i) ≫ F2.coherentDiagramTotalUnit (F i))
      (finiteCoherentSpaceProductTotalProjection n F i ≫ F2.coherentDiagramTotalUnit (F i)) := by
  induction n with
  | zero =>
    have hi : i = 0 := Fin.eq_zero i
    subst i
    simpa only [finiteCoherentProjectionVertex, finiteCoherentSpaceProduct,
      finiteCoherentSpaceProductTotalProjection, eqToHom_refl, Category.id_comp] using
        coherentIdentityTransformationUnitIso (F 0)
  | succ n ih =>
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · exact Iso.refl _
    · let G := finiteCoherentSpaceProduct n (fun k ↦ F k.succ)
      let x := coherentSpaceTensorProductSndVertex (F 0) G
      let y := finiteCoherentProjectionVertex n (fun k ↦ F k.succ) j
      let T := F2.coherentTransformationVertexTriangle (finiteCoherentSpaceProduct (n + 1) F)
        G (F j.succ) x y
      have e := coherentTransformationTriangleUnitIso _ G (F j.succ) x y T
      have d := FunctorIso.precomp (ih (fun k ↦ F k.succ) j)
        (coherentSpaceTensorProductTotalSnd (F 0) G)
      change FunctorIso (F2.coherentTransformationTotalMap _ _ T.diagonal ≫
        F2.coherentDiagramTotalUnit (F j.succ))
        ((coherentSpaceTensorProductTotalSnd (F 0) G ≫
          finiteCoherentSpaceProductTotalProjection n (fun k ↦ F k.succ) j) ≫
            F2.coherentDiagramTotalUnit (F j.succ))
      exact F2.functorIsoOfEq (e ≪≫ d) rfl (Category.assoc _ _ _).symm

end SerrePositivity.InfinityCategories.HomotopyLimits
