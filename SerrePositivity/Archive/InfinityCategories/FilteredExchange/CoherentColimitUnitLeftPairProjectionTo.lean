module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitUnitValueActionTo
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitUnitTriangleProjectionTo
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitValueProjectionEndpoints
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitUpperUnitTriangle

/-!
概要：元の五因子の左辺二因子の合成を、同じ値空間の native 指定合成へ照合する。
方針：三実頂点の等式と二つの元の指定値を同時に移す。
規約：元の全三角形・二面を保持。使われ方：a6 の模型三角形交換式への五因子式の代入。
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
local notation "uJ" => coconeTransformationHomotopy (coherentDiagramTotalCocone J)
local notation "e" => FunctorIso.app (functorTriangleSequentialPostComparison T p) x₀
local notation "Q" => constantTargetValueProjectionTo p (coherentDiagramTotalCocone_vertex J)

/-- 三実頂点だけを表示変更した左辺二因子は、同じ native 中央比較と上側三角形項に等しい。 -/
lemma coherentColimitUnitLeftPair_projectionTo_eq :
    vertexIsoOfEq (coherentColimitUnitValueActionTo B d p x₀ ≪≫
      VertexIso.map (VertexIso.map e (functorHomotopyRelativePost uJ p)) Q)
      (coherentColimitValueProjection_lower_vertex B d)
      (coherentColimitValueProjection_composite_vertex B a b) =
    coherentColimitNativeTriangleActionComparison B d ≪≫
      functorIsoOfEq ((functorTriangleTotalActionIso T).postcomp (coherentNativeUnitValueAction J))
        rfl (coherentColimitUpperUnitTriangle_middle (B := B) (a := a) (b := b)) := by
  have hg := (coherentColimitUnitTriangle_projectionTo_heq_native B T).trans
    (functorIsoOfEq_heq ((functorTriangleTotalActionIso T).postcomp
      (coherentNativeUnitValueAction J)) rfl
      (coherentColimitUpperUnitTriangle_middle (B := B) (a := a) (b := b))).symm
  have h := vertexIso_trans_heq_of_heq (coherentColimitUnitValueActionTo B d p x₀)
    (VertexIso.map (VertexIso.map e (functorHomotopyRelativePost uJ p)) Q)
    (coherentColimitNativeTriangleActionComparison B d)
    (functorIsoOfEq ((functorTriangleTotalActionIso T).postcomp (coherentNativeUnitValueAction J))
      rfl (coherentColimitUpperUnitTriangle_middle (B := B) (a := a) (b := b)))
    (coherentColimitValueProjection_lower_vertex B d)
    (coherentColimitValueProjection_upper_vertex B d)
    (coherentColimitValueProjection_composite_vertex B a b)
    (coherentColimitUnitValueActionTo_total_heq_native B d) hg
  exact eq_of_heq ((vertexIsoOfEq_heq _ _ _).trans h)

end SerrePositivity.InfinityCategories.F2
