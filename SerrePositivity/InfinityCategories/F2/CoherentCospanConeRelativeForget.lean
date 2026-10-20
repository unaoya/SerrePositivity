module

public import SerrePositivity.InfinityCategories.F2.CoherentCospanConeRelativePath

/-!
概要：底固定の相対可換 path の指定同型を既存の全空間比較へ厳密に戻す。
方針：相対同型の合成と忘却の関手性、共通長辺の等式の消去を使う。
規約：指定同型の等式。使われ方：既存の native 値比較候補と底上の模型との照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：共通長辺の等式からの相対同型の忘却は元の全空間の標準同型。
方針：等式を消去。規約：指定値の等式。使われ方：相対可換 path の中央比較。 -/
lemma coherentTransformationRelativeVertex_eqIso_forget {B : SSet.{u}}
    (F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
    {x y : (leftUnstraighteningTransformationSpace F G) _⦋0⦌} (h : x = y) :
    VertexIso.map (eqToIso (congrArg SSet.HomotopyCategory.mk
      (congrArg (coherentTransformationRelativeVertex F G) h)))
      (vertexFiberι ((ihom (smallLeftUnstraightening F)).map (smallLeftUnstraighteningProjection G))
        (functorVertex (smallLeftUnstraighteningProjection F))) =
      functorEqIso (congrArg (coherentTransformationTotalMap F G) h) := by
  cases h
  rfl

/-- 概要：相対空間内の指定可換同型の忘却像は元の全空間の指定可換同型そのもの。
方針：左右三角形の同じ相対比較と共通長辺の標準同型を写す。
規約：元の指定値を変更しない。使われ方：以前の native 比較候補と同じ path の確認。 -/
lemma coherentCospanConeRelativePathIso_forget {B : SSet.{u}} [Quasicategory B]
    (F X Y Z : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
    (C : CoherentTransformationCospanCone F X Y Z) :
    (coherentCospanConeRelativePathIso F X Y Z C).map
      (vertexFiberι ((ihom (smallLeftUnstraightening F)).map (smallLeftUnstraighteningProjection Z))
        (functorVertex (smallLeftUnstraighteningProjection F))) =
      coherentCospanConeTotalPathIso F X Y Z C := by
  have hd := coherentTransformationRelativeVertex_eqIso_forget F Z C.diagonal_eq
  dsimp only [VertexIso.map] at hd
  simp only [coherentCospanConeRelativePathIso, coherentCospanConeTotalPathIso,
    coherentTransformationTriangleSmallIso, VertexIso.map, Functor.mapIso_trans,
    Functor.mapIso_symm, hd]

end SerrePositivity.InfinityCategories.F2
