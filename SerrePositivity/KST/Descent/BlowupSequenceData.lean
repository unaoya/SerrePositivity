module

public import SerrePositivity.KST.Descent.BlowupGeometry
public import SerrePositivity.KST.Descent.SquareMapSequence
public import SerrePositivity.KST.Descent.SquareSequenceAction

/-!
# 抽象 blowup の自然な全次数の列の接続界面

## 概要
実降下から供給すべき長完全列と、その境界の幾何正方形の射に関する自然性を記述する。
この自然性から境界の同変性と、有理不変部分の全次数完全列を構成する。

## 方針
境界を任意に選ばず、抽象 blowup ごとに指定された列と、全ての正方形の射の可換式を保持する。
群元による自己射に自然性を適用する。

## 規約
これは公理 (2) の実降下から導く π_* 側の接続データ。
このデータの存在をホモトピー引き戻し性の定義としたり、実降下の構成済みと数えたりしない。
L9 の実際の fiber と長完全列、実降下の比較から供給する責務が残る。

## 使われ方
論文 補題 3.3・定理 3.1 の軌道正方形の長完全列への接続。
-/

@[expose] public section

universe u w t

open CategoryTheory AlgebraicGeometry Representation

namespace SerrePositivity.KST.Descent

/-- 概要：抽象 blowup の指定長完全列と境界の自然性（論文 §3）。
方針：実降下から得るべき列を、幾何正方形の射全体に対して自然に指定する。
規約：主定理の結論を仮定せず、実降下と L9 の列から供給する接続データ。
使われ方：境界の同変性と全次数の不変部分の列。 -/
structure NaturalBlowupSequences {S : Scheme.{u}} {Coefficient : Type w}
    (L : GradedPresheaf.{u + 1, u, w, t} (FiniteTypeSchemes S) Coefficient) where
  /-- 概要：各係数に対する指定された全次数の列（論文 §3）。
  方針：前層の指定制限を持つ実際の長完全列を保持する。
  規約：境界と三箇所の完全性を含む。
  使われ方：閉和・軌道正方形の貼り合わせ。 -/
  sequence : ∀ (b : AbstractBlowupSquare S) (H : Coefficient), SquareMayerVietoris L H b.square
  /-- 概要：境界は幾何正方形の射に関して自然（論文 §3）。
  方針：四頂点の引き戻しによる可換式を記録する。
  規約：正方形の自己射も含む。
  使われ方：境界の同変性と比較の五項補題。 -/
  boundary_naturality : ∀ (b c : AbstractBlowupSquare S) (f : b.square ⟶ c.square)
    (H : Coefficient) (n : ℤ),
    ((sequence b H).boundary n).comp (L.pullback H (n + 1) f.τ₁) =
      (L.pullback H n f.τ₄).comp ((sequence c H).boundary n)

namespace NaturalBlowupSequences

variable {S : Scheme.{u}} {Coefficient : Type w}
variable {L : GradedPresheaf.{u + 1, u, w, t} (FiniteTypeSchemes S) Coefficient}
variable (data : NaturalBlowupSequences L)

/-- 概要：自然な blowup 列の幾何的な引き戻し比較（論文 補題 3.3）。
方針：四頂点の指定引き戻しと境界の自然性を列の射にまとめる。
規約：反変の向きで列を比較する。
使われ方：実際の二つの抽象 blowup の比較。 -/
def comparison (b c : AbstractBlowupSquare S) (f : b.square ⟶ c.square) (H : Coefficient) :
    GradedMayerVietoris.Hom (data.sequence c H).toGraded (data.sequence b H).toGraded :=
  SquareMayerVietoris.pullbackComparison L H (data.sequence b H) (data.sequence c H) f
    (data.boundary_naturality b c f H)

/-- 概要：自然な blowup 列の境界は同変な正方形の作用と可換（論文 定理 3.1）。
方針：逆元が定める正方形の自己射へ境界の自然性を適用する。
規約：同変性を独立の追加仮定にせず、自然性から導く。
使われ方：全次数の列へ有理不変部分を適用する。 -/
theorem boundary_equivariant (b : AbstractBlowupSquare S) (H : Coefficient)
    {G : Type*} [Group G] (a : SquareAction b.square G) (n : ℤ) :
    IsIntertwiningMap (L.pullbackRepresentation H (n + 1) a.on1)
      (L.pullbackRepresentation H n a.on4) ((data.sequence b H).boundary n) := by
  constructor
  intro g x
  exact LinearMap.congr_fun (data.boundary_naturality b b (a.endomorphism g⁻¹) H n) x

/-- 概要：自然な blowup 列に幾何正方形の G 作用を入れる（論文 定理 3.1）。
方針：制限と差の同変性、および自然性から導いた境界の同変性を用いる。
規約：各次数の境界の同変性を別に入力する必要はない。
使われ方：不変部分の全次数の完全列。 -/
noncomputable def action (b : AbstractBlowupSquare S) (H : Coefficient)
    {G : Type*} [Group G] (a : SquareAction b.square G) :
    GradedMayerVietoris.Action (data.sequence b H).toGraded G :=
  SquareMayerVietoris.withSquareAction L H a (data.sequence b H)
    (data.boundary_equivariant b H a)

/-- 概要：自然な blowup 列の有理不変部分の全次数の完全列（論文 定理 3.1）。
方針：構成した列の作用に、有限群の有理不変部分の完全性を適用する。
規約：hG の構成や実降下の存在はこの補題では供給しない。
使われ方：実際の同変軌道正方形の全次数の貼り合わせ。 -/
noncomputable def fixedSequence (b : AbstractBlowupSquare S) (H : Coefficient)
    {G : Type*} [Group G] [Finite G] (a : SquareAction b.square G) :
    GradedMayerVietoris.{t} :=
  (data.action b H a).fixedSequence

end NaturalBlowupSequences

end SerrePositivity.KST.Descent
