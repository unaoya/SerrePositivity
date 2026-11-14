module
public import SerrePositivity.KST.SConstruction.BoundaryAssemblyParameterPaths
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.DoubleCylinderPaths

/-! # 自然性円筒内の具体的な三辺列
概要：延長側・円筒横断・逆射側の指定した辺を同じ Kan パラメーター内へ移す。
方針：直積の辺と二重円筒の厳密な端点の貼り合わせを使う。
規約：因子の自然性の辺は指定したものを保持する。
使われ方：選択した構造射の自然性を因子の合成三角形へ接続する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open Spectra Spectra.PointedMapping Comparison
open scoped Simplicial

/-- 共通の中間選択の左側の Kan パラメーター頂点。 -/
def boundaryAssemblyLeftMiddle (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (v : (oneDirectionKanInverseChoices r X) _⦋0⦌)
    (w : (kanAssemblyAdjointChoices r Y) _⦋0⦌) :
    (boundaryAssemblyNaturalityParameters r f) _⦋0⦌ :=
  (boundaryAssemblyExtensionMiddle r f ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder_left (boundaryAssemblyExtensionMiddle r f) (boundaryAssemblyInverseMiddle r f) ≫
      boundaryAssemblyNaturalityParameterUnit r f).app (Opposite.op ⦋0⦌) (v, w)

/-- 共通の中間選択の右側の Kan パラメーター頂点。 -/
def boundaryAssemblyRightMiddle (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (v : (oneDirectionKanInverseChoices r X) _⦋0⦌)
    (w : (kanAssemblyAdjointChoices r Y) _⦋0⦌) :
    (boundaryAssemblyNaturalityParameters r f) _⦋0⦌ :=
  (boundaryAssemblyInverseMiddle r f ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder_right (boundaryAssemblyExtensionMiddle r f) (boundaryAssemblyInverseMiddle r f) ≫
      boundaryAssemblyNaturalityParameterUnit r f).app (Opposite.op ⦋0⦌) (v, w)

/-- 指定した延長側の自然性の辺を同じ Kan パラメーターへ移す。 -/
def boundaryAssemblyExtensionParameterEdge (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (v : (boundaryKanAssemblyChoices r X) _⦋0⦌)
    (w : (boundaryKanAssemblyChoices r Y) _⦋0⦌)
    (e : (kanAssemblyMixedChoices r f).Edge
      ((kanAssemblyMixedFromSource r f).app (Opposite.op ⦋0⦌) v.2)
      ((kanAssemblyMixedFromTarget r f).app (Opposite.op ⦋0⦌) w.2)) :
    (boundaryAssemblyNaturalityParameters r f).Edge
      ((boundaryAssemblyNaturalitySource r f).app (Opposite.op ⦋0⦌) v) (boundaryAssemblyLeftMiddle r f v.1 w.2) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianLeftParameterEdge (kanAssemblyMixedFromSource r f) (kanAssemblyMixedFromTarget r f)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder_left (boundaryAssemblyExtensionMiddle r f) (boundaryAssemblyInverseMiddle r f))
    (boundaryAssemblyNaturalityParameterUnit r f) v w.2 e

/-- 指定した逆射側の自然性の辺を同じ Kan パラメーターへ移す。 -/
def boundaryAssemblyInverseParameterEdge (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (v : (boundaryKanAssemblyChoices r X) _⦋0⦌)
    (w : (boundaryKanAssemblyChoices r Y) _⦋0⦌)
    (e : (oneDirectionInverseMixedChoices r f).Edge
      ((oneDirectionInverseMixedFromSource r f).app (Opposite.op ⦋0⦌) v.1)
      ((oneDirectionInverseMixedFromTarget r f).app (Opposite.op ⦋0⦌) w.1)) :
    (boundaryAssemblyNaturalityParameters r f).Edge
      (boundaryAssemblyRightMiddle r f v.1 w.2) ((boundaryAssemblyNaturalityTarget r f).app (Opposite.op ⦋0⦌) w) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianRightParameterEdge (oneDirectionInverseMixedFromSource r f)
    (oneDirectionInverseMixedFromTarget r f)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder_right (boundaryAssemblyExtensionMiddle r f) (boundaryAssemblyInverseMiddle r f))
    (boundaryAssemblyNaturalityParameterUnit r f) v.1 w e

/-- 共通の中間選択を通る円筒の横断辺を同じ Kan パラメーターへ移す。 -/
def boundaryAssemblyMiddleParameterEdge (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (v : (oneDirectionKanInverseChoices r X) _⦋0⦌)
    (w : (kanAssemblyAdjointChoices r Y) _⦋0⦌) :
    (boundaryAssemblyNaturalityParameters r f).Edge
      (boundaryAssemblyLeftMiddle r f v w) (boundaryAssemblyRightMiddle r f v w) :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.doubleCylinderMiddleMappedEdge (boundaryAssemblyExtensionMiddle r f)
    (boundaryAssemblyInverseMiddle r f) (boundaryAssemblyNaturalityParameterUnit r f) (v, w)

/-- 円筒の中間部分では元の貼った族は時刻によらず同じ評価となる。 -/
lemma boundaryAssemblyNaturalityCylinderFamily_middle (r : ℕ)
    {X Y : StableModel.{u}} (f : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder_middle (boundaryAssemblyExtensionMiddle r f) (boundaryAssemblyInverseMiddle r f) ≫
      boundaryAssemblyNaturalityCylinderFamily r f =
    fst _ (Δ[1] : SSet.{u}) ≫ boundaryAssemblyExtensionMiddle r f ≫
      boundaryAssemblyExtensionFamily r f := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.doubleMappingCylinder_middle_desc ..

/-- 任意の延長選択でも円筒の横断辺の像は同じ中間評価頂点の恒等辺。 -/
lemma boundaryAssemblyMiddleParameterEdge_evaluation (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (u : (boundaryAssemblyNaturalityFamilyChoices r f) _⦋0⦌)
    (v : (oneDirectionKanInverseChoices r X) _⦋0⦌)
    (w : (kanAssemblyAdjointChoices r Y) _⦋0⦌) :
    ((boundaryAssemblyMiddleParameterEdge r f v w).map
      (boundaryAssemblyNaturalityFamilyAt r f u)).edge =
    (SSet.Edge.id ((boundaryAssemblyExtensionMiddle r f ≫ boundaryAssemblyExtensionFamily r f).app
      (Opposite.op ⦋0⦌) (v, w))).edge := by
  have h : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder_middle (boundaryAssemblyExtensionMiddle r f)
      (boundaryAssemblyInverseMiddle r f) ≫
        (boundaryAssemblyNaturalityParameterUnit r f ≫ boundaryAssemblyNaturalityFamilyAt r f u) =
      fst _ (Δ[1] : SSet.{u}) ≫
        (boundaryAssemblyExtensionMiddle r f ≫ boundaryAssemblyExtensionFamily r f) := by
    rw [boundaryAssemblyNaturalityFamilyAt_unit]
    exact boundaryAssemblyNaturalityCylinderFamily_middle r f
  exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.doubleCylinderMiddleMappedEdge_constant_evaluation
    (boundaryAssemblyExtensionMiddle r f) (boundaryAssemblyInverseMiddle r f)
    (boundaryAssemblyNaturalityParameterUnit r f) (boundaryAssemblyNaturalityFamilyAt r f u)
    (boundaryAssemblyExtensionMiddle r f ≫ boundaryAssemblyExtensionFamily r f) h (v, w)

end SerrePositivity.KST.SConstruction
