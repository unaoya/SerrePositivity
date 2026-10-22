module

public import SerrePositivity.InfinityCategories.F2.CoherentColimitRawLastLongValueCancellation
public import SerrePositivity.InfinityCategories.F2.CoherentColimitIntervalModelFiberTransport

/-!
概要：残余消去の固定値への像の中間点と終点を、元の模型三角形式の同じ実射へ揃える。
方針：元の単位・第一作用の合成と最後辺の実輸送終点を使う。
規約：端点等式は実射から計算する。使われ方：元の模型残余と指定一点比較の消去。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  (a : SSet.Homotopy F G) (b : SSet.Homotopy G J)
local notation "ma" => Subtype.val (leftUnstraighteningMappingVertexMap _ _
  (coherentVertexOfHomotopy (simplicialHomotopyOfFunctorEdge (coherentColimitConstantEdge B a))))
local notation "mb" => Subtype.val (leftUnstraighteningMappingVertexMap _ _
  (coherentVertexOfHomotopy (simplicialHomotopyOfFunctorEdge (coherentColimitConstantEdge B b))))
local notation "u₀" => Subtype.val (leftUnstraighteningMappingVertexMap F
  (SSet.const (JoinCocone.vertex (coherentDiagramTotalCocone F)))
  (coconeTransformationVertex (coherentDiagramTotalCocone F)))
local notation "V" => pointedFiberValueTo (coherentDiagramTotalCocone_vertex J)
local notation "P" => coherentColimitRawConstantFiberProjection B G
local notation "PJ" => coherentColimitRawConstantFiberProjection B J
local notation "A" => SSet.yonedaEquiv.symm (coherentColimitRawIntervalVertex B b)
local notation "s" => lift (𝟙 _) (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1)))

/-- 元の固定値での中間点は、元の実下面作用後の同じ最後辺始点。 -/
lemma coherentColimitRawLastLongValue_middle_vertex :
    functorVertex ((u₀ ≫ ((ma ≫ mb) ≫ PJ)) ≫ V) =
      functorVertex (coherentColimitRawLowerCompositeAction B a ≫ (mb ≫ PJ ≫ V)) := by
  unfold coherentColimitRawLowerCompositeAction
  rw [coherentVertexOfHomotopy_cocone]
  simp only [Category.assoc]

/-- 元の固定値での終点は、元の実下面作用後の同じ最後辺の指定輸送終点。 -/
lemma coherentColimitRawLastLongValue_target_vertex :
    functorVertex ((u₀ ≫ ((ma ≫ P) ≫ coherentColimitRawFiberTransport B b)) ≫ V) =
      functorVertex (coherentColimitRawLowerCompositeAction B a ≫
        ((s ≫ (P ▷ Δ[0]) ≫ (pointedIntervalTransport A).endpoint) ≫ V)) := by
  rw [coherentColimitConstantTransport_raw_point_target]
  unfold coherentColimitRawLowerCompositeAction
  rw [coherentVertexOfHomotopy_cocone]
  simp only [Category.assoc]

end SerrePositivity.InfinityCategories.F2
