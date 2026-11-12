module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.LeftFiberKan
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PointedSpaceFiberVertices

/-!
概要：left fibration の全ての頂点 fiber の Kan 性。
方針：左ホーン充填を反転して右ホーンによる Kan 判定に帰着し、fiber の普遍性で充填する。
規約：底の quasicategory 性を仮定しない。
使われ方：Kerodon Corollary 4.4.2.3（Tag 019E）、Construction 5.5.2.1（Tag 01ZW）、unstraightening の fiber 比較。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：pointed-space 射影の任意の頂点 fiber は Kan 複体。
方針：coslice 射影の left fibration 性に fiber の Kan 判定を適用する。
規約：頂点は任意の coherent な空間の頂点。
使われ方：Kerodon Construction 5.5.2.1（Tag 01ZW）、空間との高次比較の始域。 -/
instance pointedSpaceFiber_kanComplex (s : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌) :
    KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection s) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex_of_leftFibration _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection s

/-- 概要：left unstraightening の全ての頂点 fiber は Kan 複体。
方針：引き戻した射影の left fibration 性を使う。
規約：底 C の quasicategory 性は不要。
使われ方：Kerodon Example 5.6.2.9（Tag 026S）、図式の値との fiber 比較。 -/
instance leftUnstraighteningFiber_kanComplex {C : SSet.{u + 1}}
    (F : C ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) (c : C _⦋0⦌) :
    KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection F) c) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex_of_leftFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection F) c

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
