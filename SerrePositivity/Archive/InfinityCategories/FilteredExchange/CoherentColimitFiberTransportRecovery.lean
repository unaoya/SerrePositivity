module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitFiberTransportComparison
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FullyFaithfulFunctorIsoCoherence
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoWhiskerAlgebra

/-!
概要：a6 への既存の fiber 輸送比較を元の余錐 fiber 写像で戻すと、元の作用比較を回収する。
方針：同じ充満忠実な前合成による逆像の像を計算し、端点表示の輸送を除く。
規約：既存の逆像を保持。使われ方：指定二面の整合式を元の fiber 比較へ反映する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F2
attribute [local instance] vertexFiber_kanComplex_of_leftFibration
variable (B : SSet.{u})
  {F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}} (H : SSet.Homotopy F G)

/-- 元の既存の fiber 比較を同じ余錐の fiber 写像で前合成すると、指定作用比較を値まで回収する。 -/
lemma coherentColimitFiberTransportComparisonIso_precomp_heq :
    HEq ((coherentColimitFiberTransportComparisonIso B H).precomp
      (coconeFiberMap (coherentDiagramTotalCocone F)))
      ((coherentColimitLowerActionIso B H).symm ≪≫ coherentColimitUpperActionIso B H) := by
  unfold coherentColimitFiberTransportComparisonIso
  rw [functorIso_precomp_eq_mapIso]
  change HEq (VertexIso.map _ _) _
  rw [IsFullyFaithful.preimageVertexIso_map]
  have hcast {α β : Sort _} (h : α = β) (e : α) : HEq (Eq.mp h e) e := by
    cases h
    rfl
  exact hcast _ _

end SerrePositivity.InfinityCategories.F2
