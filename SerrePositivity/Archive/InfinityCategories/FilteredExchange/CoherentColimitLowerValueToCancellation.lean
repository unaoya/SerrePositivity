module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitLowerPointValueToEndpoints
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitConstantTriangleValueTo
public import
  SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitConstantTriangleTransportCancellation
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.VertexIsoNormalizedInverseCancellation

/-!
概要：元の定値三角形を下側輸送因子の逆と合成し、同じ指定長辺輸送の残りへ消去する。
方針：元の一点比較を実両端で下側因子へ同定し、同じ指定消去式の逆を取る。
規約：単位・三角形・指定長辺輸送を保持。使われ方：a6 の模型五因子式の下側消去。
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
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle a b d)
local notation "c₀" => coherentDiagramTotalCocone F
local notation "z₃" => JoinCocone.vertex (coherentDiagramTotalCocone J)
local notation "C₀" => SSet.yonedaEquiv.symm (coherentColimitRawIntervalVertex B d)
local notation "P" => constantUnstraighteningFiberProjection
  (CategoryTheory.Functor.obj SSet.uliftFunctor B) (JoinCocone.vertex c₀)
local notation "U" => coherentColimitConstantTriangleLongTransport B T
local notation "l" => stdSimplex.obj₀Equiv.symm (0 : Fin 1)
local notation "s" => lift (𝟙 _) (SSet.const l)
local notation "u₀" => Subtype.val (leftUnstraighteningMappingVertexMap F
  (SSet.const (JoinCocone.vertex c₀)) (coconeTransformationVertex c₀))
local notation "V" => pointedFiberValueTo (coherentDiagramTotalCocone_vertex J)

/-- 元の三角形の指定長辺輸送において先頭因子を消去した、同じ残りの一点比較。 -/
def coherentColimitConstantTriangleRemainderIso :=
  functorIsoOfEq ((pointedIntervalTransportComparison P C₀ U).precomp s)
    (coherentColimitConstantTriangleLongTransport_endpoint_point B T l) rfl

/-- 同じ固定値の中で、下側因子の逆と元の定値三角形は元の残りの比較の逆へ消去される。 -/
lemma coherentColimitLowerValueTo_triangle_cancel :
    (coherentColimitLowerTransportFactorIso B d).symm ≪≫
      vertexIsoOfEq (((coherentColimitConstantTriangleFiberIso B T).precomp u₀).postcomp V)
        (coherentColimitLowerPoint_source_valueTo_vertex B d) rfl =
    vertexIsoOfEq
      ((((coherentColimitConstantTriangleRemainderIso B T).precomp u₀).postcomp V).symm)
      (coherentColimitLowerPoint_target_valueTo_vertex B d) rfl := by
  have h := coherentColimitConstantTriangleTransport_cancel_original_precomp_postcomp B T u₀ V
  rw [functorIso_precomp_symm, functorIso_postcomp_symm] at h
  have hc := vertexIsoOfEq_inverse_cancel
    (((coherentColimitConstantTriangleFiberIso B T).precomp u₀).postcomp V)
    (((coherentColimitConstantTransportPointIso B d).precomp u₀).postcomp V)
    (((coherentColimitConstantTriangleRemainderIso B T).precomp u₀).postcomp V)
    (coherentColimitLowerPoint_source_valueTo_vertex B d)
    (coherentColimitLowerPoint_target_valueTo_vertex B d) h
  rw [coherentColimitLowerPoint_valueTo_eq_lowerFactor] at hc
  exact hc

end SerrePositivity.InfinityCategories.F2
