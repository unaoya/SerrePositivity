module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitLowerActionValue
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitLowerCompositeValue
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorIsoComponentPost
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoWhiskerComposition
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FunctorIsoTriangleEvaluation
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.VertexIsoCompositionTransport

/-!
概要：下面の fiber 比較を、元の下面比較と指定区間輸送比較の二因子へ分解する。
方針：後合成と一点成分の合成則を使い、元の各因子の指定値を保持する。
規約：下面・輸送を選び直さない。使われ方：上下面の指定共役因子の消去。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}} (H : SSet.Homotopy F G)
local notation "v" => stdSimplex.obj₀Equiv.symm (0 : Fin 1)
local notation "m" => CategoryTheory.Functor.map (ihom (leftUnstraightening F))
  (QCatEquivalence.hom (pointedSpaceFiberValueEquivalence (coherentDiagramTotalVertex G)))
local notation "q" => Iso.hom (constantUnstraighteningRelativeIso
  (leftUnstraighteningProjection F) (coherentDiagramTotalVertex G))
local notation "e" => coconeIntervalFiberHomIso (coherentDiagramTotalCocone F)
  (SSet.yonedaEquiv.symm (coherentColimitIntervalVertex B H))

/-- 元の下面作用の成分は、元の三角形比較と指定区間輸送比較の像の合成。 -/
lemma coherentColimitLowerFiberHomIso_app_heq_factors :
    HEq (((coherentColimitLowerFiberHomIso B H).postcomp m).app v)
      (VertexIso.map ((coherentColimitLowerCompositeIso B H).app v) (q ≫ m) ≪≫
        VertexIso.map (FunctorIso.app e v) m) := by
  unfold coherentColimitLowerFiberHomIso
  rw [functorIso_postcomp_trans, functorIso_postcomp_postcomp, FunctorIso.app_trans]
  exact vertexIso_trans_heq_of_heq _ _ _ _ rfl rfl rfl
    (functorIso_app_postcomp_heq _ _ v) (functorIso_app_postcomp_heq _ _ v)

/-- 既存の下面作用比較自体も、同じ三角形比較と指定区間輸送比較の二因子を保持する。 -/
lemma coherentColimitLowerActionIso_heq_factors :
    HEq (coherentColimitLowerActionIso B H)
      (VertexIso.map ((coherentColimitLowerCompositeIso B H).app v) (q ≫ m) ≪≫
        VertexIso.map (FunctorIso.app e v) m) :=
  (coherentColimitLowerActionIso_heq_component B H).trans
    (coherentColimitLowerFiberHomIso_app_heq_factors B H)

end SerrePositivity.InfinityCategories.F2
