module

public import SerrePositivity.InfinityCategories.Core.LeftFiberKan
public import SerrePositivity.InfinityCategories.F1.PointedSpaceFiberVertices

/-!
概要：left fibration の全ての頂点 fiber の Kan 性。
方針：左ホーン充填を反転して右ホーンによる Kan 判定に帰着し、fiber の普遍性で充填する。
規約：底の quasicategory 性を仮定しない。
使われ方：Kerodon Corollary 4.4.2.3、Construction 5.5.2.1、unstraightening の fiber 比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：pointed-space 射影の任意の頂点 fiber は Kan 複体。
方針：coslice 射影の left fibration 性に fiber の Kan 判定を適用する。
規約：頂点は任意の coherent な空間の頂点。
使われ方：Kerodon Construction 5.5.2.1、空間との高次比較の始域。 -/
instance pointedSpaceFiber_kanComplex (s : SpaceInfinity.{u} _⦋0⦌) :
    KanComplex (vertexFiber pointedSpaceProjection s) :=
  vertexFiber_kanComplex_of_leftFibration pointedSpaceProjection s

/-- 概要：left unstraightening の全ての頂点 fiber は Kan 複体。
方針：引き戻した射影の left fibration 性を使う。
規約：底 C の quasicategory 性は不要。
使われ方：Kerodon Example 5.6.2.9、図式の値との fiber 比較。 -/
instance leftUnstraighteningFiber_kanComplex {C : SSet.{u + 1}}
    (F : C ⟶ SpaceInfinity.{u}) (c : C _⦋0⦌) :
    KanComplex (vertexFiber (leftUnstraighteningProjection F) c) :=
  vertexFiber_kanComplex_of_leftFibration (leftUnstraighteningProjection F) c

end SerrePositivity.InfinityCategories
