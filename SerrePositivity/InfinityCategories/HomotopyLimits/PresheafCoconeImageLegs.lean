module

public import SerrePositivity.InfinityCategories.HomotopyLimits.PresheafCoconeImageCones
public import SerrePositivity.InfinityCategories.HomotopyLimits.CoconeWholeEdgeSquare
public import SerrePositivity.InfinityCategories.Core.CatInfinity.NativeConeLeg

/-!
概要：指定前層余錐の元の全評価余錐間の変換として、元の全錐の実際の脚を回収する。
方針：交換評価で写した同じ全錐の頂点と底図式を厳密に読み、全一単体を保持する。
規約：元の全錐・全脚・指定余錐を変更しない。
使われ方：元の評価脚と実際の余極限頂点の脚を、全余錐の可換正方形へ入力する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 元の全錐を写した native 脚は、元の同じ全一単体の像。 -/
lemma nativeConeLeg_mapJoinCone_edge {K X Y : SSet.{u}} {p : K ⟶ X}
    (f : X ⟶ Y) (c : JoinCone p) (k : K _⦋0⦌) :
    (F2.nativeConeLeg (mapJoinCone f c) k).edge =
      f.app (Opposite.op ⦋1⦌) (F2.nativeConeLeg c k).edge := rfl

variable {B C K : SSet.{u}}
  {r : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ PresheafInfinity C}
  (q : JoinCocone r) {p : K ⟶ C.op} (c : JoinCone p)

/-- 元の交換像全錐の頂点は、元の錐頂点で評価した同じ全余錐の関手頂点。 -/
lemma presheafCoconeImageCone_vertex :
    (presheafCoconeImageCone q c).vertex = functorVertex
      (F1B.kanPostcomposeCocone
        (evaluateFunctorAt (JoinCone.ulift.{u, u + 1} c).vertex) q).val := by
  rw [presheafCoconeImageCone, mapJoinCone_vertex, presheafCoconeFlip_vertex]

/-- 元の交換像の底図式の各頂点は、同じ元の全評価余錐の関手頂点。 -/
lemma presheafCoconeImageDiagram_vertex
    (k : ((SSet.uliftFunctor.{u + 1, u}).obj K) _⦋0⦌) :
    ((SSet.uliftFunctor.{u + 1, u}).map p ≫ presheafCoconeFlip q).app (Opposite.op ⦋0⦌) k =
      functorVertex (F1B.kanPostcomposeCocone
        (evaluateFunctorAt
          (((SSet.uliftFunctor.{u + 1, u}).map p).app (Opposite.op ⦋0⦌) k)) q).val :=
  presheafCoconeFlip_vertex q _

/-- 元の同じ全錐の実際の脚を、元の全評価余錐間の変換の代表辺として表示する。 -/
def presheafCoconeImageLeg
    (k : ((SSet.uliftFunctor.{u + 1, u}).obj K) _⦋0⦌) :
    SSet.Edge (functorVertex
      (F1B.kanPostcomposeCocone (evaluateFunctorAt (JoinCone.ulift.{u, u + 1} c).vertex) q).val)
      (functorVertex (F1B.kanPostcomposeCocone
        (evaluateFunctorAt
          (((SSet.uliftFunctor.{u + 1, u}).map p).app (Opposite.op ⦋0⦌) k)) q).val) :=
  (SSet.Edge.ofTruncated (F2.nativeConeLeg (presheafCoconeImageCone q c) k)).ofEq
    (presheafCoconeImageCone_vertex q c) (presheafCoconeImageDiagram_vertex q k)

end SerrePositivity.InfinityCategories.HomotopyLimits
