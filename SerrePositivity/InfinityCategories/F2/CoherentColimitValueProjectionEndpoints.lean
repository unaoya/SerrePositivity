module

public import SerrePositivity.InfinityCategories.F2.CoherentNativeUnitValuePost
public import SerrePositivity.InfinityCategories.F2.CoherentColimitLowerTransportVertices
public import SerrePositivity.InfinityCategories.F2.CoherentColimitUpperTriangleAction

/-!
概要：元の五因子の左辺の実三頂点を、同じ値空間内で native 作用の実頂点へ揃える。
方針：元の円柱の全値射影の等式を、元の恒等初期値で評価する。
規約：端点を HEq から抽出しない。使われ方：二指定因子の合成を値まで照合する。
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
local notation "p" => leftUnstraighteningProjection F
local notation "x₀" => relativeFunctorVertex p p (𝟙 (leftUnstraightening F)) (Category.id_comp p)
local notation "uF" => coconeTransformationHomotopy (coherentDiagramTotalCocone F)
local notation "uG" => coconeTransformationHomotopy (coherentDiagramTotalCocone G)
local notation "rc" => simplicialHomotopyOfFunctorEdge (coherentColimitConstantEdge B H)
local notation "Q" => constantTargetValueProjectionTo p (coherentDiagramTotalCocone_vertex G)

/-- 元の定値辺と元の余錐単位の合成の射影は、下面の実合成作用の同じ頂点。 -/
lemma coherentColimitValueProjection_lower_vertex :
    NatTrans.app Q (Opposite.op ⦋0⦌) ((functorHomotopyRelativePost rc p).app (Opposite.op ⦋0⦌)
      ((functorHomotopyRelativePost uF p).app (Opposite.op ⦋0⦌) x₀)) =
      functorVertex (coherentColimitLowerCompositeAction B H) := by
  have h := functorHomotopyConstantPost_value_retarget_action rc
    (coherentColimitIntervalConstantHomotopy B H) (coherentDiagramTotalCocone_vertex G) rfl p
  exact congrArg (fun k => k.app (Opposite.op ⦋0⦌)
    ((functorHomotopyRelativePost uF p).app (Opposite.op ⦋0⦌) x₀)) h

/-- 元の変換と元の標的余錐単位の合成の射影は、上面の実合成作用の同じ頂点。 -/
lemma coherentColimitValueProjection_upper_vertex :
    NatTrans.app Q (Opposite.op ⦋0⦌) ((functorHomotopyRelativePost uG p).app (Opposite.op ⦋0⦌)
      ((functorHomotopyRelativePost H p).app (Opposite.op ⦋0⦌) x₀)) =
      functorVertex (coherentColimitUpperCompositeAction B H) := by
  exact congrArg (fun k => k.app (Opposite.op ⦋0⦌)
    ((functorHomotopyRelativePost H p).app (Opposite.op ⦋0⦌) x₀)) (coherentNativeUnitValue_post G p)

/-- 元の実二辺と標的余錐単位の合成も、同じ最後辺の上面作用の前合成の頂点。 -/
lemma coherentColimitValueProjection_composite_vertex
    {J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}} (K : SSet.Homotopy G J) :
    (constantTargetValueProjectionTo p (coherentDiagramTotalCocone_vertex J)).app (Opposite.op ⦋0⦌)
      ((functorHomotopyRelativePost (coconeTransformationHomotopy (coherentDiagramTotalCocone J))
        p).app (Opposite.op ⦋0⦌) ((functorHomotopyRelativePost K p).app (Opposite.op ⦋0⦌)
          ((functorHomotopyRelativePost H p).app (Opposite.op ⦋0⦌) x₀))) =
    functorVertex ((leftUnstraighteningMappingVertexMap F G (coherentVertexOfHomotopy H)).val ≫
      coherentColimitUpperCompositeAction B K) := by
  exact congrArg (fun k => k.app (Opposite.op ⦋0⦌)
    ((functorHomotopyRelativePost K p).app (Opposite.op ⦋0⦌)
      ((functorHomotopyRelativePost H p).app (Opposite.op ⦋0⦌) x₀)))
    (coherentNativeUnitValue_post J p)

end SerrePositivity.InfinityCategories.F2
