module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitUnitLeftPairProjectionTo
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitUnitValueActionCoherence

/-!
概要：元の五因子式を同じ固定値へ射影し、左辺二因子を native 指定合成へ厳密に移す。
方針：元の全式を一つの射で写し、実三頂点と二因子の指定値の一致を代入する。
規約：元の右辺三因子をそのまま保持。使われ方：a6 の模型三角形式への五因子式の代入。
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
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle a b d)
local notation "p" => leftUnstraighteningProjection F
local notation "x₀" => relativeFunctorVertex p p (𝟙 (leftUnstraightening F)) (Category.id_comp p)
local notation "uF" => coconeTransformationHomotopy (coherentDiagramTotalCocone F)
local notation "uJ" => coconeTransformationHomotopy (coherentDiagramTotalCocone J)
local notation "rc" => simplicialHomotopyOfFunctorEdge (coherentColimitConstantEdge B b)
local notation "e" => FunctorIso.app (functorTriangleSequentialPostComparison T p) x₀
local notation "Q" => constantTargetValueProjectionTo p (coherentDiagramTotalCocone_vertex J)

/-- 元の五因子式の右辺三因子を、同じ固定値への元の射影で写した指定合成。 -/
def coherentColimitUnitRightValueTo :=
  VertexIso.map
    ((functorTriangleSequentialPostComparison (coherentColimitConstantTriangle B T) p).app
      ((functorHomotopyRelativePost uF p).app (Opposite.op ⦋0⦌) x₀)) Q ≪≫
    VertexIso.map (VertexIso.map (coherentColimitUnitValueComparison B a p x₀)
      (functorHomotopyRelativePost rc p)) Q ≪≫
    coherentColimitUnitValueActionTo B b p
      ((functorHomotopyRelativePost a p).app (Opposite.op ⦋0⦌) x₀)

/-- 元の全五因子の整合式は、同じ固定値への一つの射影でそのまま保持される。 -/
lemma coherentColimitUnitValueActionTo_coherence :
    coherentColimitUnitValueActionTo B d p x₀ ≪≫
      VertexIso.map (VertexIso.map e (functorHomotopyRelativePost uJ p)) Q =
    coherentColimitUnitRightValueTo B T := by
  exact vertexIso_five_factor_relation_map Q (coherentColimitUnitValueComparison B d p x₀)
    (VertexIso.map e (functorHomotopyRelativePost uJ p))
    ((functorTriangleSequentialPostComparison (coherentColimitConstantTriangle B T) p).app
      ((functorHomotopyRelativePost uF p).app (Opposite.op ⦋0⦌) x₀))
    (VertexIso.map (coherentColimitUnitValueComparison B a p x₀) (functorHomotopyRelativePost rc p))
    (coherentColimitUnitValueComparison B b p ((functorHomotopyRelativePost a p).app
      (Opposite.op ⦋0⦌) x₀)) (coherentColimitUnitTriangleValue_coherence B T)

/-- 同じ native 左辺二因子は、実三頂点だけを揃えた元の右辺三因子に値まで等しい。 -/
lemma coherentColimitUnitNativePair_eq_rightValueTo :
    coherentColimitNativeTriangleActionComparison B d ≪≫
      functorIsoOfEq ((functorTriangleTotalActionIso T).postcomp (coherentNativeUnitValueAction J))
        rfl (coherentColimitUpperUnitTriangle_middle (B := B) (a := a) (b := b)) =
    vertexIsoOfEq (coherentColimitUnitRightValueTo B T)
      (coherentColimitValueProjection_lower_vertex B d)
      (coherentColimitValueProjection_composite_vertex B a b) := by
  have h := congrArg (fun k => vertexIsoOfEq k (coherentColimitValueProjection_lower_vertex B d)
    (coherentColimitValueProjection_composite_vertex B a b))
    (coherentColimitUnitValueActionTo_coherence B T)
  exact (coherentColimitUnitLeftPair_projectionTo_eq B T).symm.trans h

end SerrePositivity.InfinityCategories.F2
