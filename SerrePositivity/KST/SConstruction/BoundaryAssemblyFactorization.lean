module
public import SerrePositivity.KST.SConstruction.BoundaryAssemblyCanonicalComparison
public import SerrePositivity.KST.SConstruction.MappedPathTriangles

/-! # 指定した自然性の辺の実三角形による因子分解
概要：任意の選択済み自然性の辺を、指定した延長側と逆射側の二辺へ分解する。
方針：円筒横断辺の恒等評価を使い、同じ一単体を保って端点を付け直す。
規約：延長選択と三本の指定パラメーター辺を保持する。
使われ方：入力二本の合成三角形を因子の三角形と交差族から貼り合わせる。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open Spectra Spectra.PointedMapping
open scoped Simplicial

/-- 二つの因子辺が共有する中間の評価頂点。 -/
def boundaryAssemblyIntermediateVertex (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (v : (boundaryKanAssemblyChoices r X) _⦋0⦌)
    (w : (boundaryKanAssemblyChoices r Y) _⦋0⦌) :
    (PointedObject.basedHom ((boundaryKanRealizationFunctor r).obj X)
      ((loopBoundaryKanFunctor (r + 1)).obj Y)).right _⦋0⦌ :=
  (boundaryAssemblyExtensionMiddle r f ≫ boundaryAssemblyExtensionFamily r f).app
    (Opposite.op ⦋0⦌) (v.1, w.2)

/-- 延長側の指定辺の評価を、元の源と共通の中間頂点の間の辺として表す。 -/
def boundaryAssemblyExtensionEdgeAt (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (u : (boundaryAssemblyNaturalityFamilyChoices r f) _⦋0⦌)
    (v : (boundaryKanAssemblyChoices r X) _⦋0⦌)
    (w : (boundaryKanAssemblyChoices r Y) _⦋0⦌)
    (a : (kanAssemblyMixedChoices r f).Edge
      ((kanAssemblyMixedFromSource r f).app (Opposite.op ⦋0⦌) v.2)
      ((kanAssemblyMixedFromTarget r f).app (Opposite.op ⦋0⦌) w.2)) :
    (PointedObject.basedHom ((boundaryKanRealizationFunctor r).obj X)
      ((loopBoundaryKanFunctor (r + 1)).obj Y)).right.Edge
      (familyVertex (boundaryKanAssemblyAdjointAt r X v ≫ (loopBoundaryKanFunctor (r + 1)).map f))
      (boundaryAssemblyIntermediateVertex r f v w) :=
  ((boundaryAssemblyExtensionParameterEdge r f v w a).map
    (boundaryAssemblyNaturalityFamilyAt r f u)).ofEq
    (boundaryAssemblyNaturalityFamilyAt_source_vertex r f u v)
    (edge_source_eq_of_edge_eq
      ((boundaryAssemblyMiddleParameterEdge r f v.1 w.2).map
        (boundaryAssemblyNaturalityFamilyAt r f u))
      (.id (boundaryAssemblyIntermediateVertex r f v w))
      (boundaryAssemblyMiddleParameterEdge_evaluation r f u v.1 w.2))

/-- 逆射側の指定辺の評価を、共通の中間頂点と元の標的の間の辺として表す。 -/
def boundaryAssemblyInverseEdgeAt (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (u : (boundaryAssemblyNaturalityFamilyChoices r f) _⦋0⦌)
    (v : (boundaryKanAssemblyChoices r X) _⦋0⦌)
    (w : (boundaryKanAssemblyChoices r Y) _⦋0⦌)
    (b : (oneDirectionInverseMixedChoices r f).Edge
      ((oneDirectionInverseMixedFromSource r f).app (Opposite.op ⦋0⦌) v.1)
      ((oneDirectionInverseMixedFromTarget r f).app (Opposite.op ⦋0⦌) w.1)) :
    (PointedObject.basedHom ((boundaryKanRealizationFunctor r).obj X)
      ((loopBoundaryKanFunctor (r + 1)).obj Y)).right.Edge
      (boundaryAssemblyIntermediateVertex r f v w)
      (familyVertex ((boundaryKanRealizationFunctor r).map f ≫ boundaryKanAssemblyAdjointAt r Y w)) :=
  ((boundaryAssemblyInverseParameterEdge r f v w b).map
    (boundaryAssemblyNaturalityFamilyAt r f u)).ofEq
    (edge_target_eq_of_edge_eq
      ((boundaryAssemblyMiddleParameterEdge r f v.1 w.2).map
        (boundaryAssemblyNaturalityFamilyAt r f u))
      (.id (boundaryAssemblyIntermediateVertex r f v w))
      (boundaryAssemblyMiddleParameterEdge_evaluation r f u v.1 w.2))
    (boundaryAssemblyNaturalityFamilyAt_target_vertex r f u w)

/-- 因子辺の一単体は元の合成族の評価を厳密に回収する。 -/
lemma boundaryAssemblyExtensionEdgeAt_evaluation (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (u : (boundaryAssemblyNaturalityFamilyChoices r f) _⦋0⦌)
    (v : (boundaryKanAssemblyChoices r X) _⦋0⦌)
    (w : (boundaryKanAssemblyChoices r Y) _⦋0⦌)
    (a : (kanAssemblyMixedChoices r f).Edge
      ((kanAssemblyMixedFromSource r f).app (Opposite.op ⦋0⦌) v.2)
      ((kanAssemblyMixedFromTarget r f).app (Opposite.op ⦋0⦌) w.2)) :
    (boundaryAssemblyExtensionEdgeAt r f u v w a).edge =
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianEdgePair (K := oneDirectionKanInverseChoices r X)
        (L := kanAssemblyMixedChoices r f) (SSet.Edge.id v.1) a).map (boundaryAssemblyExtensionFamily r f)).edge :=
  boundaryAssemblyExtensionParameterEdge_evaluation r f u v w a

/-- 因子辺の一単体は元の合成族の評価を厳密に回収する。 -/
lemma boundaryAssemblyInverseEdgeAt_evaluation (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (u : (boundaryAssemblyNaturalityFamilyChoices r f) _⦋0⦌)
    (v : (boundaryKanAssemblyChoices r X) _⦋0⦌)
    (w : (boundaryKanAssemblyChoices r Y) _⦋0⦌)
    (b : (oneDirectionInverseMixedChoices r f).Edge
      ((oneDirectionInverseMixedFromSource r f).app (Opposite.op ⦋0⦌) v.1)
      ((oneDirectionInverseMixedFromTarget r f).app (Opposite.op ⦋0⦌) w.1)) :
    (boundaryAssemblyInverseEdgeAt r f u v w b).edge =
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianEdgePair (K := oneDirectionInverseMixedChoices r f)
        (L := kanAssemblyAdjointChoices r Y) b (SSet.Edge.id w.2)).map (boundaryAssemblyInverseFamily r f)).edge :=
  boundaryAssemblyInverseParameterEdge_evaluation r f u v w b

/-- 任意の指定した自然性の辺は、指定した二つの因子辺と実三角形をなす。 -/
lemma boundaryAssemblyNaturalityFactorizationTriangle_nonempty (r : ℕ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (u : (boundaryAssemblyNaturalityFamilyChoices r f) _⦋0⦌)
    (v : (boundaryKanAssemblyChoices r X) _⦋0⦌)
    (w : (boundaryKanAssemblyChoices r Y) _⦋0⦌)
    (a : (kanAssemblyMixedChoices r f).Edge
      ((kanAssemblyMixedFromSource r f).app (Opposite.op ⦋0⦌) v.2)
      ((kanAssemblyMixedFromTarget r f).app (Opposite.op ⦋0⦌) w.2))
    (b : (oneDirectionInverseMixedChoices r f).Edge
      ((oneDirectionInverseMixedFromSource r f).app (Opposite.op ⦋0⦌) v.1)
      ((oneDirectionInverseMixedFromTarget r f).app (Opposite.op ⦋0⦌) w.1))
    (e : (boundaryAssemblyNaturalityParameters r f).Edge
      ((boundaryAssemblyNaturalitySource r f).app (Opposite.op ⦋0⦌) v)
      ((boundaryAssemblyNaturalityTarget r f).app (Opposite.op ⦋0⦌) w)) :
    Nonempty (SSet.Edge.CompStruct (boundaryAssemblyExtensionEdgeAt r f u v w a)
      (boundaryAssemblyInverseEdgeAt r f u v w b)
      (boundaryAssemblyNaturalityEdgeAt r f u v w e)) :=
  contractibleKan_mapped_three_edge_triangle
    (boundaryAssemblyNaturalityParameters_isContractibleKan r f)
    (boundaryAssemblyNaturalityFamilyAt r f u)
    (boundaryAssemblyExtensionParameterEdge r f v w a)
    (boundaryAssemblyMiddleParameterEdge r f v.1 w.2)
    (boundaryAssemblyInverseParameterEdge r f v w b) e
    (boundaryAssemblyExtensionEdgeAt r f u v w a)
    (boundaryAssemblyInverseEdgeAt r f u v w b)
    (boundaryAssemblyNaturalityEdgeAt r f u v w e) rfl
    (boundaryAssemblyMiddleParameterEdge_evaluation r f u v.1 w.2) rfl rfl

end SerrePositivity.KST.SConstruction
