module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeIntervalTransportUnit
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoconeIntervalFiberTransport
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorCurryPointVertex

/-!
概要：元の区間 Hom 比較の成分の両端を、同じ単位と同じ係数制限の実射の頂点へ戻す。
方針：全相対合成の座標式と全 curry の一点評価を使う。
規約：元の両実射を保持。使われ方：成分の値への像と因子消去の型付き照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B T : SSet.{u + 1}} {F : B ⟶ SpaceInfinity.{u}}
  (c : JoinCocone F) {z : SpaceInfinity.{u} _⦋0⦌}
  (a : T ⟶ intervalMappingSpace c.vertex z)
local notation "E" => leftUnstraightening F
local notation "S" => coconeIntervalTransportSource c T
local notation "P" => constantUnstraighteningFiberProjection B c.vertex
local notation "u₀" => Subtype.val (leftUnstraighteningMappingVertexMap F (SSet.const c.vertex)
  (coconeTransformationVertex c))
local notation "M" => uncurry ((constantDiagramTransformation B a ≫
  leftUnstraighteningMappingSpaceMap (SSet.const c.vertex : B ⟶ _) (SSet.const z)) ≫
  Iso.hom (constantUnstraighteningRelativeIso
    (leftUnstraighteningProjection (SSet.const c.vertex : B ⟶ _)) z))

/-- 元の Hom 比較の始点は、元の単位と同じ係数で制限した定値作用の実合成の頂点。 -/
lemma coconeIntervalFiberHomIso_source_point_vertex (l : T _⦋0⦌) :
    (coconeIntervalRelativeComposite c a ≫
      (constantUnstraighteningRelativeIso (leftUnstraighteningProjection F) z).hom).app
        (Opposite.op ⦋0⦌) l = functorVertex (u₀ ≫ lift (𝟙 _) (SSet.const l) ≫ M) := by
  have h := congrArg (fun f : E ⊗ T ⟶ vertexFiber pointedSpaceProjection z =>
    (curry f).app (Opposite.op ⦋0⦌) l)
    (coconeIntervalRelativeComposite_coordinates c a)
  simp only [curry_uncurry, functorCurry_point_vertex] at h
  have hp : lift (𝟙 E) (SSet.const l) ≫ S ≫ M =
      u₀ ≫ lift (𝟙 _) (SSet.const l) ≫ M :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫ M) (coconeIntervalTransportSource_point c l)).trans
        (Category.assoc _ _ _))
  exact h.trans (congrArg functorVertex hp)

/-- 元の Hom 比較の終点は、同じ単位と同じ係数の普遍輸送の実合成の頂点。 -/
lemma coconeIntervalFiberHomIso_target_point_vertex (l : T _⦋0⦌) :
    ((pointedIntervalTransport a).map ≫
      (pre (coconeFiberMap c)).app (vertexFiber pointedSpaceProjection z)).app
        (Opposite.op ⦋0⦌) l = functorVertex (u₀ ≫ lift (𝟙 _) (SSet.const l) ≫
          (P ▷ T) ≫ (pointedIntervalTransport a).endpoint) := by
  have ht : curry (lift (fst E T ≫ coconeFiberMap c) (snd E T) ≫
      (pointedIntervalTransport a).endpoint) =
      (pointedIntervalTransport a).map ≫
        (pre (coconeFiberMap c)).app (vertexFiber pointedSpaceProjection z) := by
    apply uncurry_injective
    rw [uncurry_curry, uncurry_pre_app]
    change _ = (coconeFiberMap c ▷ T) ≫ uncurry (curry (pointedIntervalTransport a).endpoint)
    rw [uncurry_curry]
    rfl
  rw [← ht, functorCurry_point_vertex]
  apply congrArg functorVertex
  rw [← coconeIntervalTransportSource_projection c T]
  simp only [← Category.assoc]
  rw [coconeIntervalTransportSource_point]

end SerrePositivity.InfinityCategories.F2
