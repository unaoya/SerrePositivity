module

public import SerrePositivity.InfinityCategories.F1.SmallLeftUnstraighteningLift
public import SerrePositivity.InfinityCategories.F1.LeftCoherentTransportDirectComparison
public import SerrePositivity.InfinityCategories.F1.LeftFibrationInfinityEquivalence

/-!
概要：通常の nerve 上の left fibration の coherent な表現を元の宇宙で復元する。
方針：大きい全空間の直接比較を降ろし、底上の同値を LF∞ の頂点の同型にする。
規約：表現は値を反転した leftCoherentTransport を使う。
使われ方：Kerodon Corollary 5.6.0.6、分類の存在方向の小さい代表。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：元の全空間から coherent transport の小さい unstraightening への比較射。
方針：大きい直接比較の標的を縮小して宇宙を降ろす。
規約：定義域も終域も宇宙 u。
使われ方：Kerodon Corollary 5.6.0.6、小さい全空間による復元。 -/
noncomputable def smallLeftCoherentTransportComparison
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] :
    E ⟶ smallLeftUnstraightening (leftCoherentTransport p) :=
  smallLeftUnstraighteningLift (leftCoherentTransport p) (leftCoherentTransportDirectComparison p)

/-- 概要：小さい coherent transport の復元比較は元の底を厳密に保つ。
方針：大きい比較の底上の等式を縮小した射へ移す。
規約：底は持ち上げ前の nerve C。
使われ方：Kerodon Remark 5.6.2.5、復元比較を LF∞ の辺へ入れる条件。 -/
lemma smallLeftCoherentTransportComparison_projection
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] :
    smallLeftCoherentTransportComparison p ≫
      smallLeftUnstraighteningProjection (leftCoherentTransport p) = p :=
  smallLeftUnstraighteningLift_projection (leftCoherentTransport p) p
    (leftCoherentTransportDirectComparison p) (leftCoherentTransportDirectComparison_projection p)

/-- 概要：小さい coherent transport の実際の復元比較は前合成同値。
方針：大きい比較の同値性を各 Kan fiber で反映する。
規約：単なる別の同値の存在でなく構成した射の性質。
使われ方：Kerodon Corollary 5.6.0.6、小さい復元の同値性。 -/
lemma smallLeftCoherentTransportComparison_isPrecompositionEquivalence
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] :
    IsPrecompositionEquivalence (smallLeftCoherentTransportComparison p) :=
  smallLeftUnstraighteningLift_isPrecompositionEquivalence (leftCoherentTransport p) p
    (leftCoherentTransportDirectComparison p) (leftCoherentTransportDirectComparison_projection p)
    (leftCoherentTransportDirectComparison_isPrecompositionEquivalence p)

/-- 概要：元の left fibration と coherent transport の小さい復元は LF∞ 内で同型。
方針：底上の前合成同値から coherent nerve の可逆な辺を作る。
規約：これは各対象の比較であり、自然変換の存在は別の課題。
使われ方：Kerodon Corollary 5.6.0.6、分類の存在方向を ∞ 圏内で述べる。 -/
noncomputable def smallLeftCoherentTransportVertexIso
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] :
    VertexIso (leftFibrationInfinityVertex p)
      (leftFibrationInfinityVertex
        (smallLeftUnstraighteningProjection (leftCoherentTransport p))) :=
  leftFibrationInfinityVertexIsoOfPrecompositionEquivalence p
    (smallLeftUnstraighteningProjection (leftCoherentTransport p))
    (smallLeftCoherentTransportComparison p) (smallLeftCoherentTransportComparison_projection p)
    (smallLeftCoherentTransportComparison_isPrecompositionEquivalence p)

/-- 概要：通常の nerve 上の任意の小さい left fibration は小さい unstraightening と LF∞ 内で同型。
方針：反転した strict transport を表す coherent 図式と構成済みの比較を選ぶ。
規約：任意の coherent 図式の復元や写像空間の完全忠実性は結論に含めない。
使われ方：Kerodon Corollary 5.6.0.6、対象の表現の存在方向。 -/
lemma exists_smallLeftUnstraightening_representation
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] :
    ∃ F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve C) ⟶ SpaceInfinity.{u},
      Nonempty (VertexIso (leftFibrationInfinityVertex p)
        (leftFibrationInfinityVertex (smallLeftUnstraighteningProjection F))) :=
  ⟨leftCoherentTransport p, ⟨smallLeftCoherentTransportVertexIso p⟩⟩

end SerrePositivity.InfinityCategories
