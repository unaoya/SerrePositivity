module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.KST.SConstruction.IteratedPathContractible

/-! # 反復した経路実現の境界図式
概要：経路を最内側にした反復の境界射を、入力の射について自然に構成する。
方針：安定な S 図式の先頭を忘れる面へ反復実現を適用する。
規約：homotopy fiber の計算は含まない。使われ方：反復の delooping の境界図式。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：経路の境界は単体的対象の写像について自然。
方針：後続頂点の包含に対する元の自然性を各次数で使う。
規約：任意の値の圏に適用。使われ方：反復後の境界図式の自然性。 -/
lemma simplicialPathBoundary_naturality {C : Type u} [Category.{v} C]
    {X Y : SimplicialObject C} (f : X ⟶ Y) :
    Functor.whiskerLeft SimplexPrefix.functor.op f ≫ simplicialPathBoundary Y =
      simplicialPathBoundary X ≫ f := by
  apply NatTrans.ext
  funext d
  exact (f.naturality (simplicialPathTail d.unop).op).symm

/-- 概要：入力で評価した安定な S の単体的図式。
方針：単体的自己関手の二変数を反転して入力で評価する。
規約：第 n 段は S_n X。使われ方：経路の境界の標的側の構成。 -/
def stableSConstructionDiagram (X : StableModel.{u}) : SimplicialObject StableModel.{u} :=
  simplicialStableEndofunctor.flip.obj X

/-- 概要：最内側の S の各段へ外側の r 重 S の core の実現を施した図式。
方針：安定な S 図式に反復実現を後合成する。
規約：最内側の次数は n、外側は実現の次数。使われ方：反復経路の境界の標的。 -/
def iteratedSRealizationDiagram (r : ℕ) (X : StableModel.{u}) : SimplicialObject SSet.{u} :=
  stableSConstructionDiagram X ⋙ multiRealizationFunctor r

/-- 概要：反復実現した経路から元の S 図式への境界の自然変換。
方針：追加した先頭を忘れる面を反復実現の関手で写す。
規約：経路方向は最内側。使われ方：全対角の境界射。 -/
def iteratedPathBoundary (r : ℕ) (X : StableModel.{u}) :
    iteratedPathRealizationDiagram r X ⟶ iteratedSRealizationDiagram r X :=
  Functor.whiskerRight (simplicialPathBoundary (stableSConstructionDiagram X))
    (multiRealizationFunctor r)

/-- 概要：全方向を対角にした最内側 S の反復実現。
方針：内側の S の次数も外側の反復実現の次数と対角にする。
規約：全 S 方向で同じ次数を取る。使われ方：境界射の標的の座標。 -/
def iteratedSRealization (r : ℕ) (X : StableModel.{u}) : SSet.{u} :=
  simplicialDiagonalFunctor.obj (iteratedSRealizationDiagram r X)

/-- 概要：反復した経路の全対角から元の全対角への実際の境界射。
方針：単体的な境界射を対角関手で写す。
規約：経路全空間の弱可縮性は証明済み。使われ方：homotopy fiber 比較の境界射。 -/
def iteratedPathRealizationBoundary (r : ℕ) (X : StableModel.{u}) :
    iteratedPathRealization r X ⟶ iteratedSRealization r X :=
  simplicialDiagonalFunctor.map (iteratedPathBoundary r X)

/-- 概要：入力の射が誘導する最内側 S の反復実現の図式の写像。
方針：S の自己関手の入力への作用を反復実現で写す。
規約：入力の射は StableModel の射。使われ方：境界図式の標的の自然性。 -/
def iteratedSRealizationDiagramMap (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    iteratedSRealizationDiagram r X ⟶ iteratedSRealizationDiagram r Y :=
  Functor.whiskerRight (simplicialStableEndofunctor.flip.map f) (multiRealizationFunctor r)

/-- 概要：入力の射が誘導する反復した経路図式の写像。
方針：元の S 図式の入力の作用を経路へ制限してから反復実現で写す。
規約：全経路次数について自然。使われ方：境界図式の源の自然性。 -/
def iteratedPathRealizationDiagramMap (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    iteratedPathRealizationDiagram r X ⟶ iteratedPathRealizationDiagram r Y :=
  Functor.whiskerRight
    (Functor.whiskerLeft SimplexPrefix.functor.op (simplicialStableEndofunctor.flip.map f))
    (multiRealizationFunctor r)

/-- 概要：反復した経路の境界は入力の射について自然。
方針：後続頂点への制限に関する自然性を反復実現の関手で写す。
規約：厳密な自然変換の等号。使われ方：境界の対角への自然性の移送。 -/
lemma iteratedPathBoundary_naturality (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    iteratedPathRealizationDiagramMap r f ≫ iteratedPathBoundary r Y =
      iteratedPathBoundary r X ≫ iteratedSRealizationDiagramMap r f := by
  apply NatTrans.ext
  funext d
  change (multiRealizationFunctor r).map
      ((simplicialStableEndofunctor.flip.map f).app (SimplexPrefix.functor.op.obj d)) ≫
        (multiRealizationFunctor r).map ((stableSConstructionDiagram Y).map
          (simplicialPathTail d.unop).op) =
    (multiRealizationFunctor r).map ((stableSConstructionDiagram X).map
      (simplicialPathTail d.unop).op) ≫
        (multiRealizationFunctor r).map ((simplicialStableEndofunctor.flip.map f).app d)
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  exact congrArg (multiRealizationFunctor r).map
    ((simplicialStableEndofunctor.flip.map f).naturality (simplicialPathTail d.unop).op).symm

/-- 概要：入力の射による最内側 S の全対角実現の写像。
方針：構成した単体的図式の写像を対角で写す。
規約：構造射の座標との同一視は別に行う。使われ方：境界射の自然性の標的。 -/
def iteratedSRealizationMap (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    iteratedSRealization r X ⟶ iteratedSRealization r Y :=
  simplicialDiagonalFunctor.map (iteratedSRealizationDiagramMap r f)

/-- 概要：入力の射による反復経路の全対角実現の写像。
方針：経路図式の入力の作用を対角で写す。
規約：追加の選択は不要。使われ方：境界射の自然性の源。 -/
def iteratedPathRealizationMap (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    iteratedPathRealization r X ⟶ iteratedPathRealization r Y :=
  simplicialDiagonalFunctor.map (iteratedPathRealizationDiagramMap r f)

/-- 概要：反復経路の全対角の境界射は入力の射について自然。
方針：図式の自然性を対角関手で写す。
規約：単体集合の射の厳密等号。使われ方：K の delooping の自然性の照合。 -/
lemma iteratedPathRealizationBoundary_naturality (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    iteratedPathRealizationMap r f ≫ iteratedPathRealizationBoundary r Y =
      iteratedPathRealizationBoundary r X ≫ iteratedSRealizationMap r f := by
  change simplicialDiagonalFunctor.map (iteratedPathRealizationDiagramMap r f) ≫
      simplicialDiagonalFunctor.map (iteratedPathBoundary r Y) =
    simplicialDiagonalFunctor.map (iteratedPathBoundary r X) ≫
      simplicialDiagonalFunctor.map (iteratedSRealizationDiagramMap r f)
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
    iteratedPathBoundary_naturality]

end SerrePositivity.KST.SConstruction

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite BGT "Rem 7.4" (partial := component) "仮定：安定準圏の模型（原典の安定な場合）。結論：各 Gap を段とする単体安定圏（原典の単体 ∞ 圏の成分）。"] _root_.SerrePositivity.KST.SConstruction.stableSConstructionDiagram
