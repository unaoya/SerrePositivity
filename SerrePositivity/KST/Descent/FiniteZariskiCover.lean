module

public import SerrePositivity.KST.Descent.FiniteTypeCoproducts
public import SerrePositivity.KST.Descent.FiniteTypeFreeCharts

/-!
# 元の有限型の圏内の有限 Zariski 被覆と局所自由 chart

## 概要
有限個の開埋め込みの実際の被覆を保持し、同じ有限型の圏内の非交和からの全射に束ねる。

## 方針
被覆は基礎点の実際の持ち上げで指定し、非交和の指定包含の公式から全射性を導く。
有限平坦射の構成済みの有限自由 chart を同じ型へ接続する。

## 規約
被覆射そのものが開埋め込みとは主張しない。Zariski Čech 降下の法則の検証とは別の幾何データ。

## 使われ方
論文 補題 3.2 の変動 rank の有限局所自明化と、公理 (1) の元の前層の定義域内の被覆。
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace SerrePositivity.KST.Descent

/-- 概要：同じ有限型の圏内の有限 Zariski 被覆の実際のデータ（補題 3.2、公理 (1)）。
方針：有限添字、開埋め込み、基礎点の持ち上げを保持する。
規約：空の基底では空の添字も許す。使われ方：局所自由 chart と実際の Čech 被覆射。 -/
structure FiniteTypeZariskiCover {S : Scheme.{u}} (Y : FiniteTypeSchemes S) where
  /-- 概要：被覆の有限添字。方針：元の universe に固定。
  規約：有限性は次の証拠で供給。使われ方：非交和と有限積。 -/
  Index : Type u
  /-- 概要：添字は有限。方針：型の証拠を保持。
  規約：空を許す。使われ方：有限型の非交和。 -/
  finite : Finite Index
  /-- 概要：元の基底上有限型の各被覆対象。方針：同じ充満部分圏内。
  規約：元の前層が評価する対象。使われ方：局所 rank。 -/
  obj : Index → FiniteTypeSchemes S
  /-- 概要：指定被覆射。方針：基底上の実際の射。
  規約：対象ごとの抽象同型に弱めない。使われ方：Čech の指定増強。 -/
  inclusion : ∀ i, obj i ⟶ Y
  /-- 概要：各被覆射は開埋め込み。方針：元のスキームの射で指定。
  規約：全体の非交和の射とは異なる。使われ方：Zariski 被覆の法則。 -/
  openImmersion : ∀ i, IsOpenImmersion (inclusion i).hom.left
  /-- 概要：全基礎点の実際の持ち上げ。方針：指定被覆射の点の等式で与える。
  規約：全基底を覆う。使われ方：非交和からの全射。 -/
  covers : ∀ y : Y.obj.left, ∃ i, ∃ x : (obj i).obj.left, (inclusion i).hom.left x = y

attribute [instance] FiniteTypeZariskiCover.finite FiniteTypeZariskiCover.openImmersion

namespace FiniteTypeZariskiCover

variable {S : Scheme.{u}} [IsNoetherian S] {Y : FiniteTypeSchemes S} (c : FiniteTypeZariskiCover Y)

/-- 概要：被覆の有限非交和から元の基底への指定射（補題 3.2）。
方針：元の有限型の圏の標準非交和の desc を取る。
規約：各成分との合成は指定 inclusion。使われ方：実際の元の Čech nerve。 -/
def morphism : (∐ c.obj) ⟶ Y := Sigma.desc c.inclusion

/-- 概要：有限 Zariski 被覆を束ねた指定射は実際に全射（補題 3.2）。
方針：各点の持ち上げを非交和の指定包含で写す。
規約：有限型の圏の標準非交和の射を使う。使われ方：有限平坦射の局所自明化の被覆。 -/
instance morphism_surjective : Surjective c.morphism.hom.left := by
  constructor
  intro y
  obtain ⟨i, x, hx⟩ := c.covers y
  refine ⟨(Sigma.ι c.obj i).hom.left x, ?_⟩
  change ((Sigma.ι c.obj i ≫ c.morphism).hom.left) x = y
  exact (congrArg (fun f ↦ f.hom.left x) (Sigma.ι_comp_desc c.inclusion i)).trans hx

end FiniteTypeZariskiCover

/-- 概要：有限平坦全射の有限自由 chart は元の有限型の圏内の有限 Zariski 被覆（補題 3.2）。
方針：構成済みの有限 chart の実際の対象・包含・点の持ち上げをそのまま使う。
規約：正の基底と Cartesian 四辺は元の chart に保持する。使われ方：局所 rank 作用の実際の被覆。 -/
def finiteFreeChartZariskiCover {S : Scheme.{u}} [IsNoetherian S]
    {X Y : FiniteTypeSchemes S} (f : X ⟶ Y) [IsFinite f.hom.left]
    [AlgebraicGeometry.Flat f.hom.left] [Surjective f.hom.left]
    [LocallyOfFinitePresentation f.hom.left] : FiniteTypeZariskiCover Y where
  Index := finiteFreeChartIndices f.hom.left
  finite := inferInstance
  obj i := (finiteFreeChartFamily f.hom.left i.val).toBaseObject f
  inclusion i := (finiteFreeChartFamily f.hom.left i.val).toBaseInclusion f
  openImmersion i := (finiteFreeChartFamily f.hom.left i.val).openImmersion
  covers := finiteFreeChartIndices_covers f.hom.left

end SerrePositivity.KST.Descent
