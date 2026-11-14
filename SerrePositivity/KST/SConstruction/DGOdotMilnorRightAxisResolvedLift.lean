module
public import SerrePositivity.KST.SConstruction.DGGluingCellRightAxisQuotientLift
public import SerrePositivity.KST.SConstruction.DGOdotMilnorResolvedInput
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingCellProjectiveInput

/-!
概要：元 Milnor gluing の中央 dg 射を同じ resolved 商包含へ特殊化する。
方針：保存済み実逆回転へ同じ商・元の零対象・二つの射影性証拠を渡す。
規約：D の同じ二射影性を代入。native 全比較と長方形認証は別工程。
使われ方：K-10 d④ の固定 S 中央辺。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories LocalizingInvariants
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "A" => _root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R d.source
local notation "C" => DGSmallPerfectArrowTarget R (A) (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R d.left)
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.top)
local notation "D" => DGSmallPerfectArrowTarget R (A) (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R d.right)
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.side)
local notation "V" => DGOdotCorner R d
local notation "p" => dgSmallPerfectSquareLeftMap R (A) (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R d.left)
  (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R d.right) (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R d.corner)
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.top) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.side) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.lower) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.upper)
local notation "q" => dgSmallPerfectSquareRightMap R (A) (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R d.left)
  (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R d.right) (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R d.corner)
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.top) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.side) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.lower) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.upper)
local notation "M" => dgHomGluingBimodule R (C) (D) (V) (p) (q)
local notation "z" => dgSmallPerfectEnvelopeZero R (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R d.left) _ _
local notation "hz" => dgSmallPerfectEnvelopeZero_isZero R (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R d.left) _ _
local notation "B" => DGOdotGluing R d
local notation "P" => DGCategoryCellResolution.Source R (B)
local notation "N" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGNullObjects R (B)
  (dgQuotientImage R (DGLaxQuotientEndInput.diagonal (dgOdotQuotientInput R d)))
local notation "Q" => DGQuotient.QuotientObject (P) (N)

/-- 概要：元 Milnor gluing の同じ右軸射影と包含の合成。
方針：保存済み右軸関手を元零対象で特殊化する。規約：全 Hom を保持。
使われ方：同じ graph と native 増大比較の共通入力。 -/
abbrev dgOdotMilnorRightAxisEndofunctor : DGFunctor R (B) (B) :=
  dgGluingCellRightAxisEndofunctor R (C) (D) (M) (z) (hz)

/-- 概要：元 Milnor gluing の右軸から恒等への同じ全 dg 比較。
方針：元の閉零対象を保って既存比較を特殊化する。規約：全次数を保持。
使われ方：同じ実中央射と native square の共通比較。 -/
abbrev dgOdotMilnorRightAxisComparison :=
  dgGluingAxisRightComparison R (C) (D) (M) (z) (hz)

/-- 概要：元 Milnor gluing で必要な二つの graph 右制限の射影性。
方針：元右軸と恒等の供給口を特殊化する。規約：D の同じ型を保持。
使われ方：D からの二証拠を受け取る型。 -/
abbrev DGOdotMilnorRightAxisProjectiveInput :=
  DGGluingCellRightAxisProjectiveInput R (C) (D) (M) (z) (hz)

/-- 概要：同じ resolved 商包含の厳密 dg 表示。
方針：元の null 対象集合をそのまま用いる。規約：商を選び直さない。
使われ方：中央射と固定 S 商辺の共通指定射。 -/
def dgOdotMilnorResolvedInclusion : DGFunctor R (P) (Q) :=
  DGQuotient.inclusion R (P) (N)

/-- 概要：指定包含は保存済み固定 S 商辺と同じ射である。
方針：元宇宙持ち上げの定義を展開する。規約：全 Hom の等号。
使われ方：二つの経路の商の照合。 -/
lemma dgOdotMilnorResolvedInclusion_input :
    (dgOdotMilnorCellProjectionInputMap R d).down =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftFunctor.{u, u + 1, u + 1, u + 1, u + 1}
        (dgOdotMilnorResolvedInclusion R d) := rfl

/-- 概要：同じ右軸・恒等 graph の二つの射影性証拠。
方針：D の無条件な同じ固定解像度の定理を特殊化する。
規約：解像度を変更しない。使われ方：中央 dg 射の追加射影性入力を除去。 -/
def dgOdotMilnorRightAxisProjective : DGOdotMilnorRightAxisProjectiveInput R d :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGluingCellRightAxisProjectiveInput R (C) (D) (M) (z) (hz)

local notation "h" => dgOdotMilnorRightAxisProjective R d

/-- 概要：同じ resolved 商へ延長した元右軸 graph の実 Perf 関手。
方針：元の指定包含で実延長する。規約：全 Hom を保持。
使われ方：中央比較の二成分。 -/
abbrev dgOdotMilnorRightAxisQuotientSource :=
  dgGluingCellRightAxisQuotientSource R (C) (D) (M) (z) (hz) h (Q)
    (dgOdotMilnorResolvedInclusion R d)

/-- 概要：同じ resolved 商へ延長した元恒等 graph の実 Perf 関手。
方針：元の指定包含で実延長する。規約：全 Hom を保持。
使われ方：中央比較の二成分。 -/
abbrev dgOdotMilnorRightAxisQuotientTarget :=
  dgGluingCellRightAxisQuotientTarget R (C) (D) (M) (z) (hz) h (Q)
    (dgOdotMilnorResolvedInclusion R d)

/-- 概要：同じ resolved 商上の右軸から恒等への全 dg 比較。
方針：保存済み全比較を同じ指定包含で延長する。規約：元の比較を保持。
使われ方：実逆回転の指定比較。 -/
abbrev dgOdotMilnorRightAxisQuotientComparison :=
  dgGluingCellRightAxisQuotientComparison R (C) (D) (M) (z) (hz) h (Q)
    (dgOdotMilnorResolvedInclusion R d)

/-- 概要：同じ実二像と cone 像を含む中央射の小基底。
方針：同じ resolved 包含へ既存の構成を特殊化する。規約：元実像を保持。
使われ方：固定 S 中央辺の終域。 -/
abbrev DGOdotMilnorRightAxisBase :=
  DGGluingCellRightAxisQuotientLiftBase R (C) (D) (M) (z) (hz) h (Q)
    (dgOdotMilnorResolvedInclusion R d)

/-- 概要：同じ小基底の恒等二脚 Hom gluing。
方針：同じ resolved 包含へ既存の構成を特殊化する。規約：元実像を保持。
使われ方：固定 S 中央辺の終域。 -/
abbrev DGOdotMilnorRightAxisTarget :=
  DGGluingCellRightAxisQuotientLiftTarget R (C) (D) (M) (z) (hz) h (Q)
    (dgOdotMilnorResolvedInclusion R d)

/-- 概要：元 cell 始域から同じ resolved 商上の実逆回転への中央 dg 射。
方針：元右軸比較を同じ包含で延長する。規約：D の二射影性を充足済み。
使われ方：d④ の実中央辺。 -/
def dgOdotMilnorRightAxisLift : DGFunctor R (P) (DGOdotMilnorRightAxisTarget R d) :=
  dgGluingCellRightAxisQuotientLift R (C) (D) (M) (z) (hz) h (Q)
    (dgOdotMilnorResolvedInclusion R d)

/-- 概要：同じ実中央射の終域を固定 S に置く。
方針：元対象と全 Hom を宇宙持ち上げする。規約：同じ二像小模型を保持。
使われ方：共通 S 長方形の中央下頂点候補。 -/
def dgOdotMilnorRightAxisInput : PerfDGInput.{u, u + 1} R :=
  dgKUniverseInput.{u, u + 1, u + 1} R (DGOdotMilnorRightAxisTarget R d)

/-- 概要：同じ実中央 dg 射を固定 S の実辺にする。
方針：元厳密関手を持ち上げる。規約：始域は保存済み cell 入力。
使われ方：三認証へ接続する中央辺。 -/
def dgOdotMilnorRightAxisInputMap :
    dgOdotMilnorCellInput R d ⟶ dgOdotMilnorRightAxisInput R d :=
  ULift.up (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftFunctor.{u, u + 1, u + 1, u + 1, u + 1}
    (dgOdotMilnorRightAxisLift R d))

/-- 概要：固定 S の同じ中央辺の完全な ν 像。
方針：固定界面に実辺を渡す。規約：native 全比較は別に構成する。
使われ方：中央辺の ν 比較の始点。 -/
abbrev dgOdotMilnorRightAxisExactMap : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap
    (dgKInputStableValue R (dgOdotMilnorCellInput R d))
    (dgKInputStableValue R (dgOdotMilnorRightAxisInput R d)) :=
  dgKInputNuMap R (dgOdotMilnorRightAxisInputMap R d)

end SerrePositivity.KST.SConstruction
