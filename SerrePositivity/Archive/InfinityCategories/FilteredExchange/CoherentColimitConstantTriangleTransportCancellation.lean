module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitConstantTriangleFiberIso
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorIsoTransportCancellation
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedIntervalComparisonComposition
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoWhiskerAlgebra
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitConstantTransportPointIso

/-!
概要：元の定値余極限三角形比較を逆合成して、同じ長辺輸送比較の先頭因子を消去する。
方針：元の実両端へ戻した指定比較の等式と、同じ二輸送の普遍比較の合成則を使う。
規約：元の三角形・実終点・指定輸送を保持。使われ方：下側輸送因子の整合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {c : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle a b c)
local notation "z₀" => JoinCocone.vertex (coherentDiagramTotalCocone F)
local notation "z₃" => JoinCocone.vertex (coherentDiagramTotalCocone J)
local notation "C₀" => SSet.yonedaEquiv.symm (coherentColimitRawIntervalVertex B c)
local notation "P" => constantUnstraighteningFiberProjection
  (CategoryTheory.Functor.obj SSet.uliftFunctor B) z₀
local notation "T₀" => constantDiagramTransportWitness
  (constantDiagramMappingFamilyWitness (CategoryTheory.Functor.obj SSet.uliftFunctor B) C₀)
local notation "U" => coherentColimitConstantTriangleLongTransport B T
local notation "l" => stdSimplex.obj₀Equiv.symm (0 : Fin 1)
local notation "s" => lift (𝟙 _) (SSet.const l)
local notation "hs" => coherentColimitConstantTransport_endpoint_point B l
local notation "ht" => coherentColimitConstantTriangleLongTransport_endpoint_point B T l

/-- 元の三角形比較の逆を合成すると、同じ指定長辺輸送の残りの普遍比較に等しい。 -/
lemma coherentColimitConstantTriangleTransport_cancel :
    (coherentColimitConstantTriangleFiberIso B T).symm ≪≫
      functorIsoOfEq ((pointedIntervalTransportComparison P C₀ T₀).precomp s) hs rfl =
        functorIsoOfEq ((pointedIntervalTransportComparison P C₀ U).precomp s) ht rfl := by
  have h := pointedIntervalTransportComparison_trans P C₀ T₀ U
  have hp := congrArg (fun e => FunctorIso.precomp e s) h
  have hpre := functorIso_precomp_trans
    (FiberTransportFamily.endpointIso pointedSpaceProjection P (intervalMappingUncurry C₀)
      (intervalMappingUncurry_one C₀) T₀ U)
    (pointedIntervalTransportComparison P C₀ U) s
  rw [coherentColimitConstantTriangleFiberIso_eq_transport]
  exact functorIsoOfEq_symm_cancel_prefix _ _ _ hs ht (hpre.symm.trans hp)

/-- 元の定値輸送比較そのものから、元の三角形比較を逆合成して先頭因子を消去する。 -/
lemma coherentColimitConstantTriangleTransport_cancel_original :
    (coherentColimitConstantTriangleFiberIso B T).symm ≪≫
      coherentColimitConstantTransportPointIso B c =
        functorIsoOfEq ((pointedIntervalTransportComparison P C₀ U).precomp s) ht rfl := by
  rw [coherentColimitConstantTransportPointIso_eq_witness]
  exact coherentColimitConstantTriangleTransport_cancel B T

/-- 同じ元の因子消去は、任意の始域制限と元の fiber の値への後合成でも保持される。 -/
lemma coherentColimitConstantTriangleTransport_cancel_original_precomp_postcomp
    {A X : SSet.{u + 1}}
    (f : A ⟶ leftUnstraightening
      (SSet.const z₀ : ((SSet.uliftFunctor.{u + 1, u}).obj B) ⟶ SpaceInfinity))
    (g : vertexFiber pointedSpaceProjection z₃ ⟶ X) :
    ((FunctorIso.precomp (coherentColimitConstantTriangleFiberIso B T).symm f).postcomp g) ≪≫
      (((coherentColimitConstantTransportPointIso B c).precomp f).postcomp g) =
        (((functorIsoOfEq ((pointedIntervalTransportComparison P C₀ U).precomp s)
          ht rfl).precomp f).postcomp g) := by
  have h := congrArg (fun e => (FunctorIso.precomp e f).postcomp g)
    (coherentColimitConstantTriangleTransport_cancel_original B T)
  rw [functorIso_precomp_trans, functorIso_postcomp_trans] at h
  exact h

end SerrePositivity.InfinityCategories.F2
