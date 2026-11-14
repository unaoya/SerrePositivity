module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.Pullback
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.Terminal
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TerminalUniqueness
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PushoutShape

/-! # 零対象と pointed ∞ 圏

概要：零対象を同時に始対象・終対象となる実際の頂点として扱う。
方針：A2e の二つの境界充填条件を組み合わせる。
規約：零対象の選択とその存在を分ける。使われ方：HA §1.1 の fiber/cofiber 四角形。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects
open _root_.CategoryTheory MonoidalCategory _root_.SSet
open scoped _root_.Simplicial

/-- 概要：零対象となる頂点は始対象かつ終対象。
方針：二つの A2e の充填条件を同時に課す。
規約：任意の単体集合で定義する。使われ方：HA Definition 1.1.1.1 の零対象。 -/
def IsZeroVertex {X : SSet.{u}} (z : X _⦋0⦌) : Prop :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex z ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex z

/-- 概要：選ばれた零対象の頂点。
方針：頂点に始対象・終対象の二つの証明を付ける。
規約：h C の対象で置き換えない。使われ方：fiber/cofiber の零角の指定。 -/
structure ZeroVertex (X : SSet.{u}) where
  vertex : X _⦋0⦌
  isInitial : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex vertex
  isTerminal : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex vertex

/-- 概要：零対象の存在を pointed 条件として表す。
方針：選択を伴わない存在命題を型クラスにする。
規約：quasicategory 性は別の仮定とする。使われ方：安定性の前提。 -/
class HasZeroVertex (X : SSet.{u}) : Prop where
  exists_zero : ∃ z : X _⦋0⦌, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex z

/-- 概要：選ばれた零対象の両方の充填条件。
方針：構造の二つの証明を組にする。
規約：同じ頂点。使われ方：四角形の零角の判定。 -/
lemma _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroVertex.isZero {X : SSet.{u}} (z : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroVertex X) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex z.vertex :=
  ⟨z.isInitial, z.isTerminal⟩

/-- 概要：零対象の存在から一つを選べる。
方針：存在量化から頂点と二つの条件を選ぶ。
規約：古典的選択。使われ方：Σ・Ω を構成する際の零対象。 -/
def chosenZeroVertex (X : SSet.{u}) [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex X] : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroVertex X :=
  ⟨Classical.choose (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex.exists_zero (X := X)),
    (Classical.choose_spec (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex.exists_zero (X := X))).1,
    (Classical.choose_spec (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex.exists_zero (X := X))).2⟩

/-- 概要：二つの零対象はホモトピー圏で同型である。
方針：A2f の終対象の一意性を使う。
規約：頂点の命題的等号は主張しない。使われ方：零対象の選択の比較。 -/
def zeroVertexIso {X : SSet.{u}} [Quasicategory X] (z w : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroVertex X) :
    (SSet.HomotopyCategory.mk z.vertex : hoFunctor.obj X) ≅ SSet.HomotopyCategory.mk w.vertex :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.terminalVertexIso z.isTerminal w.isTerminal

/-- 概要：単体的四角形の指定された角の頂点。
方針：標準辺の二つの零単体の組を評価する。
規約：第一座標が横、第二座標が縦。使われ方：零角と fiber/cofiber 対象の指定。 -/
def squareVertex {X : SSet.{u}} (F : Δ[1] ⊗ Δ[1] ⟶ X) (i j : Fin 2) : X _⦋0⦌ :=
  F.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm i, stdSimplex.obj₀Equiv.symm j)

/-- 概要：HA の三角形は (0,1) の角が零対象となる四角形。
方針：四角形と零角の充填条件を保持する。
規約：三辺は X→Y→Z と X→0→Z。使われ方：HA Definition 1.1.1.4 の fiber/cofiber 列。 -/
structure ZeroTriangle (X : SSet.{u}) where
  square : Δ[1] ⊗ Δ[1] ⟶ X
  zero_corner : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex square 0 1)

/-- 概要：零角の四角形が fiber 列となること。
方針：A2g の引き戻し条件を使う。
規約：零角は三角形の構造に保持する。使われ方：HA 1.1.1.9 の安定性。 -/
def IsFiberSequence {X : SSet.{u}} (t : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle X) : Prop :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare t.square

/-- 概要：零角の四角形が cofiber 列となること。
方針：span の余極限による押し出し条件を使う。
規約：実際の coslice の始対象。使われ方：HA 1.1.1.9 の安定性。 -/
def IsCofiberSequence {X : SSet.{u}} (t : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle X) : Prop :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare t.square

/-- 概要：指定された射の fiber を与える零角の引き戻し四角形。
方針：射を右辺に固定し、残りの四角形と引き戻し性を保持する。
規約：零角の選択は構造の一部。使われ方：全ての射の fiber の存在。 -/
structure FiberSquare {X : SSet.{u}} {x y : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x y) extends _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle X where
  right_edge : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ square = SSet.yonedaEquiv.symm f.edge
  isPullback : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare square

/-- 概要：指定された射の cofiber を与える零角の押し出し四角形。
方針：射を下辺に固定し、残りの四角形と押し出し性を保持する。
規約：零角の選択は構造の一部。使われ方：全ての射の cofiber の存在。 -/
structure CofiberSquare {X : SSet.{u}} {x y : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x y) extends _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle X where
  bottom_edge : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ square = SSet.yonedaEquiv.symm f.edge
  isPushout : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare square

/-- 概要：fiber 四角形の fiber 対象の頂点。
方針：引き戻し頂点 (0,0) を評価する。
規約：元の射の始域は (1,0)。使われ方：Ω と fiber 列の第一項。 -/
def _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.FiberSquare.fiber {X : SSet.{u}} {x y : X _⦋0⦌}
    {f : SSet.Truncated.Edge (X := (truncation 2).obj X) x y} (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.FiberSquare f) : X _⦋0⦌ :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex s.square 0 0

/-- 概要：cofiber 四角形の cofiber 対象の頂点。
方針：余極限頂点 (1,1) を評価する。
規約：元の射の終域は (1,0)。使われ方：Σ と cofiber 列の第三項。 -/
def _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.CofiberSquare.cofiber {X : SSet.{u}} {x y : X _⦋0⦌}
    {f : SSet.Truncated.Edge (X := (truncation 2).obj X) x y} (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.CofiberSquare f) : X _⦋0⦌ :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex s.square 1 1

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "1.1.1.1"] _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex
attribute [cite HA "1.1.1.1"] _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex
attribute [cite HA "1.1.1.4"] _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsCofiberSequence
attribute [cite HA "1.1.1.4"] _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsFiberSequence
attribute [cite HA "1.1.1.4"] _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle
attribute [cite HA "1.1.1.5"] _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle
attribute [cite HA "1.1.1.6"] _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.CofiberSquare
attribute [cite HA "1.1.1.6"] _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.CofiberSquare.cofiber
attribute [cite HA "1.1.1.6"] _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.FiberSquare
attribute [cite HA "1.1.1.6"] _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.FiberSquare.fiber
attribute [cite HTT "7.2.2.7"] _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex
