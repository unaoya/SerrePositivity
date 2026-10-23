module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.TransportDiagramEvaluation
public import SerrePositivity.InfinityCategories.F1.StrictDiagramMappingNaturality
public import SerrePositivity.InfinityCategories.Core.VertexFiber
public import SerrePositivity.InfinityCategories.F1.Cocartesian.HomComponentPullback

/-!
概要：元の混合 Hom 作用を終点成分と前合成へ分解する。
方針：strict な自然性を core 関手へ移し、同じ成分の fiber に制限する。
規約：同じ作用の全高次に対する等式であり、独立な Hom 同値への置き換えはしない。
使われ方：一次元の source 比較の第一三角形を指定合成へ揃える。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable {C : Type u} [Category.{u} C] {c d : C} (f : c ⟶ d)
  (F G : CocartesianTransportDiagramCategory C)

/-- 元の混合 Hom 作用は、終点での成分評価の後に始域の輸送を前合成した作用。 -/
lemma cocartesianTransportDiagramMixedHom_naturality :
    cocartesianTransportDiagramMixedHom f F G =
      (cocartesianTransportDiagramEvaluationEnriched d).map F G ≫
        quasicategoryCoreMap ((pre (F.val.map f)).app (G.val.obj d)) := by
  change quasicategoryCoreFunctor.map (strictDiagramMixedHom f F.val G.val) =
    quasicategoryCoreFunctor.map _ ≫ quasicategoryCoreFunctor.map _
  rw [← Functor.map_comp]
  exact congrArg quasicategoryCoreFunctor.map
    (strictDiagramMappingComponent_naturality F.val G.val f)

/-- 終点成分を固定すると、混合 Hom の全高次も同じ前合成の頂点に固定される。 -/
lemma cocartesianTransportDiagramMixedHom_fiber
    (b : (SimplicialCategory.sHom (cocartesianTransportDiagramValue F d)
      (cocartesianTransportDiagramValue G d)) _⦋0⦌) :
    vertexFiberι ((cocartesianTransportDiagramEvaluationEnriched d).map F G) b ≫
        cocartesianTransportDiagramMixedHom f F G =
      SSet.const ((quasicategoryCoreMap ((pre (F.val.map f)).app (G.val.obj d))).app
        (Opposite.op ⦋0⦌) b) := by
  rw [cocartesianTransportDiagramMixedHom_naturality, ← Category.assoc,
    vertexFiberι_comp, SSet.const_comp]
  rfl

/-- 実際の source 比較と同じ宇宙・同じ成分 fiber 上でも混合作用は一定。 -/
lemma cocartesianHomSourceComponent_mixedHom_fiber
    (b : ((SSet.uliftFunctor.{u + 1, u}).obj
      (SimplicialCategory.sHom (cocartesianTransportDiagramValue F d)
        (cocartesianTransportDiagramValue G d))) _⦋0⦌) :
    vertexFiberι (cocartesianHomSourceComponent F G d) b ≫
        (SSet.uliftFunctor.{u + 1, u}).map
          (cocartesianTransportDiagramMixedHom f F G) =
      SSet.const (((SSet.uliftFunctor.{u + 1, u}).map
        (quasicategoryCoreMap ((pre (F.val.map f)).app (G.val.obj d)))).app
          (Opposite.op ⦋0⦌) b) := by
  rw [cocartesianTransportDiagramMixedHom_naturality, Functor.map_comp,
    ← Category.assoc]
  change (_ ≫ cocartesianHomSourceComponent F G d) ≫ _ = _
  rw [vertexFiberι_comp, SSet.const_comp]
  rfl

end SerrePositivity.InfinityCategories
