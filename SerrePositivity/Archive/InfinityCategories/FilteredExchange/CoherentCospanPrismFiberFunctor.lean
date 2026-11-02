module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PrismFiberHomotopyFunctor
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentCospanRestrictedPrismPath

/-!
概要：元の共通長辺空間の指定類を、同じ小さい fiber 間の関手の指定類へ写す。
方針：共通の終点条件で一つの終点・縮小・下降・fiber Hom 関手を構成する。
規約：同じ関手で局所側と native 側を写す。使われ方：実際の fiber 比較への接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}}
  (F X Y Z : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (C : CoherentTransformationCospanCone F X Y Z) (b : B _⦋0⦌)
local notation "a" => coherentNativeTriangleFiberParameters F b
local notation "m" => smallUnstraighteningSourceRestriction F
  (vertexFiberι (smallLeftUnstraighteningProjection F) b)
local notation "q" => coherentCospanNativeLongBase F X Y Z C b
local notation "hq" => coherentCospanNativeLongBase_initial F X Y Z C b

/-- 共通の長辺の終点は、元の標的図式の同じ fiber を被覆する。 -/
lemma coherentCospanPrismEndpoint_projection :
    prismEndpoint 1 a ≫ q = ((m).left ≫ leftUnstraighteningProjection F) ≫ Z :=
  coherentRestrictedPrismEndpoint_projection F X Z C.toLeft C.fromLeft C.leftTriangle b q
    (coherentCospanRestrictedPrismBase_left F X Y Z C b)

/-- 元の局所比較と native 比較の共通空間から、元の小さい fiber の関手への同じ関手。 -/
def coherentCospanPrismFiberFunctor :=
  coherentPrismFiberFunctor F Z b q hq (coherentCospanPrismEndpoint_projection F X Y Z C b)

/-- native 全錐の指定長辺同型の、終点・縮小・下降・fiber Hom による指定像。 -/
def coherentCospanNativePrismFiberPathIso :=
  (coherentCospanPrismFiberFunctor F X Y Z C b).mapIso
    (coherentCospanNativeCommonLongPathIso F X Y Z C b)

/-- 元の局所二 prism の指定合成を、同じ全経路で小さい fiber の関手へ写す。 -/
def coherentCospanRestrictedPrismFiberPathIso :=
  (coherentCospanPrismFiberFunctor F X Y Z C b).mapIso
    (coherentCospanRestrictedPrismPathIso F X Y Z C b)

/-- 元の局所指定合成と native 指定長辺は、小さい fiber の同じ指定同型へ写る。 -/
lemma coherentCospanRestrictedPrismFiberPathIso_eq_native :
    coherentCospanRestrictedPrismFiberPathIso F X Y Z C b =
      coherentCospanNativePrismFiberPathIso F X Y Z C b :=
  congrArg (fun e => (coherentCospanPrismFiberFunctor F X Y Z C b).mapIso e)
    (coherentCospanRestrictedPrismPathIso_eq_native F X Y Z C b)

end SerrePositivity.InfinityCategories.F2
