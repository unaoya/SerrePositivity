module
public import SerrePositivity.KST.SConstruction.BoundaryAssemblyCanonicalPaths

/-! # 選択した自然性の辺と具体的な因子辺列の照合
概要：任意の選択済みの自然性パラメーター辺を、指定した因子の三辺列と比較する。
方針：可縮な Kan パラメーター内の三角形を評価し、円筒の厳密な制限を使う。
規約：指定した三本の辺と選択した延長を保つ。
使われ方：因子の合成三角形から随伴構造射の二次整合性を得る準備。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open Spectra Spectra.PointedMapping Comparison
open scoped Simplicial

/-- 指定した延長側の辺の評価は元の延長側の合成族の同じ辺の評価。 -/
lemma boundaryAssemblyExtensionParameterEdge_evaluation (r : ℕ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (u : (boundaryAssemblyNaturalityFamilyChoices r f) _⦋0⦌)
    (v : (boundaryKanAssemblyChoices r X) _⦋0⦌)
    (w : (boundaryKanAssemblyChoices r Y) _⦋0⦌)
    (e : (kanAssemblyMixedChoices r f).Edge
      ((kanAssemblyMixedFromSource r f).app (Opposite.op ⦋0⦌) v.2)
      ((kanAssemblyMixedFromTarget r f).app (Opposite.op ⦋0⦌) w.2)) :
    ((boundaryAssemblyExtensionParameterEdge r f v w e).map
      (boundaryAssemblyNaturalityFamilyAt r f u)).edge =
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianEdgePair (K := oneDirectionKanInverseChoices r X)
        (L := kanAssemblyMixedChoices r f) (SSet.Edge.id v.1) e).map (boundaryAssemblyExtensionFamily r f)).edge := by
  have h : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder_left (boundaryAssemblyExtensionMiddle r f)
      (boundaryAssemblyInverseMiddle r f) ≫
        (boundaryAssemblyNaturalityParameterUnit r f ≫ boundaryAssemblyNaturalityFamilyAt r f u) =
      boundaryAssemblyExtensionFamily r f := by
    rw [boundaryAssemblyNaturalityFamilyAt_unit]
    exact boundaryAssemblyNaturalityCylinderFamily_left r f
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianLeftParameterEdge_evaluation
    (kanAssemblyMixedFromSource r f) (kanAssemblyMixedFromTarget r f)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder_left (boundaryAssemblyExtensionMiddle r f) (boundaryAssemblyInverseMiddle r f))
    (boundaryAssemblyNaturalityParameterUnit r f) (boundaryAssemblyNaturalityFamilyAt r f u)
    (boundaryAssemblyExtensionFamily r f) h v w.2 e

/-- 指定した逆射側の辺の評価は元の逆射側の合成族の同じ辺の評価。 -/
lemma boundaryAssemblyInverseParameterEdge_evaluation (r : ℕ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (u : (boundaryAssemblyNaturalityFamilyChoices r f) _⦋0⦌)
    (v : (boundaryKanAssemblyChoices r X) _⦋0⦌)
    (w : (boundaryKanAssemblyChoices r Y) _⦋0⦌)
    (e : (oneDirectionInverseMixedChoices r f).Edge
      ((oneDirectionInverseMixedFromSource r f).app (Opposite.op ⦋0⦌) v.1)
      ((oneDirectionInverseMixedFromTarget r f).app (Opposite.op ⦋0⦌) w.1)) :
    ((boundaryAssemblyInverseParameterEdge r f v w e).map
      (boundaryAssemblyNaturalityFamilyAt r f u)).edge =
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianEdgePair (K := oneDirectionInverseMixedChoices r f)
        (L := kanAssemblyAdjointChoices r Y) e (SSet.Edge.id w.2)).map (boundaryAssemblyInverseFamily r f)).edge := by
  have h : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder_right (boundaryAssemblyExtensionMiddle r f)
      (boundaryAssemblyInverseMiddle r f) ≫
        (boundaryAssemblyNaturalityParameterUnit r f ≫ boundaryAssemblyNaturalityFamilyAt r f u) =
      boundaryAssemblyInverseFamily r f := by
    rw [boundaryAssemblyNaturalityFamilyAt_unit]
    exact boundaryAssemblyNaturalityCylinderFamily_right r f
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianRightParameterEdge_evaluation
    (oneDirectionInverseMixedFromSource r f) (oneDirectionInverseMixedFromTarget r f)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder_right (boundaryAssemblyExtensionMiddle r f) (boundaryAssemblyInverseMiddle r f))
    (boundaryAssemblyNaturalityParameterUnit r f) (boundaryAssemblyNaturalityFamilyAt r f u)
    (boundaryAssemblyInverseFamily r f) h v.1 w e

/-- 任意の指定した自然性パラメーター辺は具体的な因子の三辺列と一致する。 -/
lemma boundaryAssemblyCanonicalPath_fac (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (v : (boundaryKanAssemblyChoices r X) _⦋0⦌)
    (w : (boundaryKanAssemblyChoices r Y) _⦋0⦌)
    (a : (kanAssemblyMixedChoices r f).Edge
      ((kanAssemblyMixedFromSource r f).app (Opposite.op ⦋0⦌) v.2) ((kanAssemblyMixedFromTarget r f).app (Opposite.op ⦋0⦌) w.2))
    (b : (oneDirectionInverseMixedChoices r f).Edge
      ((oneDirectionInverseMixedFromSource r f).app (Opposite.op ⦋0⦌) v.1)
      ((oneDirectionInverseMixedFromTarget r f).app (Opposite.op ⦋0⦌) w.1))
    (e : (boundaryAssemblyNaturalityParameters r f).Edge
      ((boundaryAssemblyNaturalitySource r f).app (Opposite.op ⦋0⦌) v) ((boundaryAssemblyNaturalityTarget r f).app (Opposite.op ⦋0⦌) w)) :
    (SSet.HomotopyCategory.homMk (boundaryAssemblyExtensionParameterEdge r f v w a) ≫
      SSet.HomotopyCategory.homMk (boundaryAssemblyMiddleParameterEdge r f v.1 w.2)) ≫
      SSet.HomotopyCategory.homMk (boundaryAssemblyInverseParameterEdge r f v w b) =
      SSet.HomotopyCategory.homMk e :=
  contractibleKan_three_edge_fac (boundaryAssemblyNaturalityParameters_isContractibleKan r f) _ _ _ _

/-- 任意の延長選択による評価後も、指定した自然性の辺と因子辺列の比較を保持する。 -/
lemma boundaryAssemblyCanonicalPath_evaluated_fac (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (u : (boundaryAssemblyNaturalityFamilyChoices r f) _⦋0⦌)
    (v : (boundaryKanAssemblyChoices r X) _⦋0⦌)
    (w : (boundaryKanAssemblyChoices r Y) _⦋0⦌)
    (a : (kanAssemblyMixedChoices r f).Edge
      ((kanAssemblyMixedFromSource r f).app (Opposite.op ⦋0⦌) v.2) ((kanAssemblyMixedFromTarget r f).app (Opposite.op ⦋0⦌) w.2))
    (b : (oneDirectionInverseMixedChoices r f).Edge
      ((oneDirectionInverseMixedFromSource r f).app (Opposite.op ⦋0⦌) v.1)
      ((oneDirectionInverseMixedFromTarget r f).app (Opposite.op ⦋0⦌) w.1))
    (e : (boundaryAssemblyNaturalityParameters r f).Edge
      ((boundaryAssemblyNaturalitySource r f).app (Opposite.op ⦋0⦌) v) ((boundaryAssemblyNaturalityTarget r f).app (Opposite.op ⦋0⦌) w)) :
    (SSet.HomotopyCategory.homMk ((boundaryAssemblyExtensionParameterEdge r f v w a).map
        (boundaryAssemblyNaturalityFamilyAt r f u)) ≫
      SSet.HomotopyCategory.homMk ((boundaryAssemblyMiddleParameterEdge r f v.1 w.2).map
        (boundaryAssemblyNaturalityFamilyAt r f u))) ≫
      SSet.HomotopyCategory.homMk ((boundaryAssemblyInverseParameterEdge r f v w b).map
        (boundaryAssemblyNaturalityFamilyAt r f u)) =
      SSet.HomotopyCategory.homMk (e.map (boundaryAssemblyNaturalityFamilyAt r f u)) := by
  have h := congrArg (SSet.mapHomotopyCategory (boundaryAssemblyNaturalityFamilyAt r f u)).map
    (boundaryAssemblyCanonicalPath_fac r f v w a b e)
  simpa only [CategoryTheory.Functor.map_comp, SSet.mapHomotopyCategory_map_homMk] using h

end SerrePositivity.KST.SConstruction
