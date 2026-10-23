module

public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorEnrichedEvaluation
public import SerrePositivity.InfinityCategories.F1.Coherent.NervePostcomposition
public import SerrePositivity.InfinityCategories.F1.Fibrations.LeftFibrationMappingSpaces
public import SerrePositivity.InfinityCategories.F1.Transport.LeftStrictTransport

/-!
概要：left fibrations の ∞ 圏から 𝒮 への相対関手の coherent な評価。
方針：相対 Hom の豊穣評価に coherent nerve を適用する。
規約：底の図式の全空間は u、得られる評価写像の単体集合は u+1。
使われ方：Kerodon Corollary 5.6.0.6、分類関手の strict transport の各対象での値。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：固定した底上の対象からの相対関手空間による coherent な空間値評価。
方針：Kan 複体への豊穣評価を coherent nerve の射に写す。
規約：定義域は left fibrations の ∞ 圏、値域は coherent nerve による 𝒮。
使われ方：Kerodon Corollary 5.6.0.6、fibration の高次の射も含めた相対 Hom の評価。 -/
noncomputable def leftFibrationCoherentEvaluation {B : SSet.{u}} (a : Over B) :
    LeftFibrationInfinity B ⟶ SpaceInfinity.{u} :=
  coherentNerveMap (relativeFunctorEnrichedEvaluation a)

/-- 概要：coherent な評価の頂点での値は指定した相対関手空間の Kan 複体を表す。
方針：coherent nerve の射の標準頂点の式を使う。
規約：相対関手空間の Kan 性は射影 p の left fibration 性による。
使われ方：Kerodon Corollary 5.6.0.6、coherent な評価の対象での値の照合。 -/
lemma leftFibrationCoherentEvaluation_vertex {E B : SSet.{u}} (a : Over B)
    (p : E ⟶ B) [LeftFibration p] :
    (leftFibrationCoherentEvaluation a).app (Opposite.op ⦋0⦌) (leftFibrationInfinityVertex p) =
      spaceInfinityVertex
        ((relativeFunctorEnrichedEvaluation a).obj (leftFibrationObjectOf p)) := by
  rw [spaceInfinityVertex_eq_coherent]
  exact coherentNerveMap_vertex (relativeFunctorEnrichedEvaluation a) (leftFibrationObjectOf p)

/-- 概要：通常の底の対象における strict transport の coherent な評価。
方針：undercategory の nerve からの相対 Hom の評価を取る。
規約：底の圏 C の対象 c を固定し、fibration 側の全ての高次単体を動かす。
使われ方：Kerodon Construction 5.3.1.5、Corollary 5.6.0.6、分類関手の対象 c での評価。 -/
noncomputable def leftStrictTransportCoherentEvaluation {C : Type u} [Category.{u} C] (c : C) :
    LeftFibrationInfinity (nerve C) ⟶ SpaceInfinity.{u} :=
  leftFibrationCoherentEvaluation (Over.mk (nerveMap (Under.forget c)))

/-- 概要：strict transport の coherent 評価は fibration p の頂点をその strict transport の空間へ写す。
方針：一般の coherent な相対 Hom の評価の頂点の式を使う。
規約：対象 c での値は既存の leftStrictTransportFunctor の値そのもの。
使われ方：Kerodon Construction 5.3.1.5、Corollary 5.6.0.6、既存の表現との整合性。 -/
lemma leftStrictTransportCoherentEvaluation_vertex
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] (c : C) :
    (leftStrictTransportCoherentEvaluation c).app (Opposite.op ⦋0⦌)
      (leftFibrationInfinityVertex p) =
      spaceInfinityVertex ((leftStrictTransportFunctor p).obj c) :=
  leftFibrationCoherentEvaluation_vertex (Over.mk (nerveMap (Under.forget c))) p

end SerrePositivity.InfinityCategories
