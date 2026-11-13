module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.KST.SConstruction.DGOdotMilnorCompletion
public import SerrePositivity.KST.SConstruction.DGOdotMilnorLandTamme
public import SerrePositivity.KST.SConstruction.DGOdotMilnorProjectionRectangle

/-!
概要：Milnor 条件だけから、同じ resolved 商の完備化を持つ実 Cat^perf 列と LT 結論を得る。
方針：D-21 の具体的 c・hc を既存の Tamme・Verdier 接続へ代入する。
規約：元代数の二脚全体との比較と固定 S の全長方形は別工程として保持する。
使われ方：e② の実完備化入力を取り除いた具体的な引き戻し・極限錐。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet DifferentialGraded InfinityCategories LocalizingInvariants
  Spectra
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R) (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d)
local notation "κ" => dgOdotMilnorCompletion R d
local notation "hκ" => dgOdotMilnorCompletion_isIdempotentCompletion R d
local instance : SimplicialCategory OmegaSpectrum.{u + 1} := OmegaSpectrum.simplicialCategory

/-- 概要：実 resolved 商とその実完備化を持つ Cat^perf 列。
方針：D-21 の c・hc を代入する。規約：Milnor 条件以外の商証拠を要求しない。
使われ方：元対角・元 gluing の実 fiber 列。 -/
def dgOdotMilnorCompletedPerfectSequence : PerfectVerdierSequence.{u + 1} :=
  dgOdotMilnorPerfectSequence R d h (κ) (hκ)

/-- 概要：同じ具体的な実列の全 Cat^perf 提示四角形。
方針：既存の全単体を保持する提示を使用する。規約：c を追加入力にしない。
使われ方：全局所化不変量への適用。 -/
def dgOdotMilnorCompletedPerfectDiagram : PerfectVerdierDiagram.{u + 1} :=
  (dgOdotMilnorCompletedPerfectSequence R d h).presentation

/-- 概要：元の実 lax 模型と同じ resolved 商の具体的完備化を持つ商入力。
方針：証明済みの核・局所化と c・hc を束ねる。
規約：追加の商・完備化仮定なし。使われ方：Tamme 分裂と実 LT 四角形。 -/
def dgOdotMilnorCompletedLaxQuotient : PerfectLaxQuotient
    (dgOdotMilnorLaxYoneda R d) (dgOdotMilnorLaxCoefficient R d) :=
  dgOdotMilnorLaxPerfectQuotient R d h (κ) (hκ)

/-- 概要：商側の実比較長方形は同じ具体的な c と上下の指定三角形を保持する。
方針：構成済みの全貼合せを実完備化に特殊化する。
規約：零角を含む S 内の全図式とは区別する。使われ方：d④ の商側境界。 -/
def dgOdotMilnorCompletedProjectionRectangle := dgOdotMilnorProjectionRectangle R d (κ)

variable {F : perfectStableInfinity.{u + 1} ⟶ Sp.{u + 1}} (hF : IsPerfectLocalizingInvariant F)

/-- 概要：元の三対象と同じ実包含・完備化後の商を持つ列の fiber 性。
方針：具体的提示に局所化不変量を適用する。規約：K の局所化性は仮定しない。
使われ方：実 Cat^perf 版の結論。 -/
theorem dgOdotMilnorCompletedPerfect_isFiber :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsFiberSequence (hF.fiberTriangle (dgOdotMilnorCompletedPerfectDiagram R d h)) :=
  hF.fiberTriangle_isFiber _

/-- 概要：同じ resolved 商の実完備化を終点とする実 LT 四角形。
方針：Tamme 分裂と元 Milnor 列を使用する。規約：実 c・hc を追加入力にしない。
使われ方：具体的 Cat^perf 不変量の引き戻し。 -/
def dgOdotMilnorCompletedLandTammeSquare :
    (Δ[1] ⊗ Δ[1] : SSet.{u + 2}) ⟶ Sp.{u + 1} :=
  dgOdotMilnorLandTammeSquare R d h (κ) (hκ) hF

/-- 概要：Milnor 条件だけから、同じ実 LT 四角形の引き戻し性。
方針：具体的完備化で既存の定理を充足する。
規約：元代数二脚との全比較は別に行う。使われ方：e② の実商入力の充足。 -/
theorem dgOdotMilnorCompletedLandTamme_isPullback :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (dgOdotMilnorCompletedLandTammeSquare R d h hF) :=
  dgOdotMilnorLandTamme_isPullback R d h (κ) (hκ) hF

/-- 概要：同じ二脚を持つ実 LT cospan。
方針：四辺固定の同じ四角形から回収する。規約：脚を選び直さない。
使われ方：実極限錐の底。 -/
def dgOdotMilnorCompletedLandTammeCospan : (horn 2 2 : SSet.{u + 2}) ⟶ Sp.{u + 1} :=
  dgOdotMilnorLandTammeCospan R d h (κ) (hκ) hF

/-- 概要：元小 Perf 対角始域の値を頂点に持つ同じ錐。
方針：具体的な c・hc を既存の実錐へ代入する。規約：頂点を置換しない。
使われ方：LT の実極限表示。 -/
def dgOdotMilnorCompletedLandTammeCone :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (dgOdotMilnorCompletedLandTammeCospan R d h hF) :=
  dgOdotMilnorLandTammeCone R d h (κ) (hκ) hF

/-- 概要：同じ元頂点・二脚を持つ錐は ∞ 極限。
方針：具体化した LT 引き戻しの実錐を使用する。規約：群ごとの主張に弱めない。
使われ方：実 Cat^perf LT 結論。 -/
theorem dgOdotMilnorCompletedLandTammeCone_isLimit :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (dgOdotMilnorCompletedLandTammeCone R d h hF) :=
  dgOdotMilnorLandTammeCone_isLimit R d h (κ) (hκ) hF

/-- 概要：極限錐の頂点は元の同じ小 Perf 始域値。
方針：元の頂点回収を保持する。規約：同型類だけではない。
使われ方：元代数の固定 ν 値との比較。 -/
lemma dgOdotMilnorCompletedLandTammeCone_source :
    (dgOdotMilnorCompletedLandTammeCone R d h hF).vertex =
      F.app (Opposite.op ⦋0⦌) (perfectStableVertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorNativeDiagonalSource R d)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorDiagonalSource_isIdempotentComplete R d)) :=
  dgOdotMilnorLandTammeCone_source R d h (κ) (hκ) hF

end SerrePositivity.KST.SConstruction

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite KST "Thm 4.11" (partial := component) "仮定：非正 dg 塔の Tor 模型と IsKConnective、また別に dg Milnor の単一正方形（Lean が強い）。結論：実不変量の一本のプロ同値と単一の ⊙ 引き戻し。c(μ)πᵢ と K のプロ四角形を組み立てていない（Lean が弱い）。"] _root_.SerrePositivity.KST.SConstruction.dgOdotMilnorCompletedLandTamme_isPullback
attribute [cite LT "Eq (10)" (partial := component) "仮定：指定された dg Milnor 正方形（Lean が強い）。結論：実 lax gluing と resolved 商の Verdier 列をその冪等完備化まで構成。任意の E₁ 環の主定理の列より狭い（Lean が弱い）。"] _root_.SerrePositivity.KST.SConstruction.dgOdotMilnorCompletedPerfectSequence
attribute [cite LT "Eq (11)" (partial := component) "仮定：指定 dg Milnor 四角形と Sp 値の完全局所化不変量（Lean が強い）。結論：実商のファイバー列と、その分裂を通じた同じ四頂点の引き戻し。一般環スペクトルと任意の安定標的は範囲外（Lean が弱い）。"] _root_.SerrePositivity.KST.SConstruction.dgOdotMilnorCompletedLandTamme_isPullback
attribute [cite LT "Eq (11)" (partial := component) "仮定：指定 dg Milnor 四角形と Sp 値の完全局所化不変量（Lean が強い）。結論：実商のファイバー列と、その分裂を通じた同じ四頂点の引き戻し。一般環スペクトルと任意の安定標的は範囲外（Lean が弱い）。"] _root_.SerrePositivity.KST.SConstruction.dgOdotMilnorCompletedPerfect_isFiber
attribute [cite LT "Eq (12)" (partial := component) "仮定：指定 dg Milnor 四角形と Sp 値の完全局所化不変量（Lean が強い）。結論：実商のファイバー列と、その分裂を通じた同じ四頂点の引き戻し。一般環スペクトルと任意の安定標的は範囲外（Lean が弱い）。"] _root_.SerrePositivity.KST.SConstruction.dgOdotMilnorCompletedLandTamme_isPullback
attribute [cite LT "Eq (12)" (partial := component) "仮定：指定 dg Milnor 四角形と Sp 値の完全局所化不変量（Lean が強い）。結論：実商のファイバー列と、その分裂を通じた同じ四頂点の引き戻し。一般環スペクトルと任意の安定標的は範囲外（Lean が弱い）。"] _root_.SerrePositivity.KST.SConstruction.dgOdotMilnorCompletedPerfect_isFiber
attribute [cite LT "Eq (17)" (partial := component) "仮定：前者は単一の dg Milnor 正方形と局所化不変量、後者は非正 dg 代数の塔と IsKConnective（Lean が強い）。結論：実 ⊙ 側の値の引き戻しと、別に塔の一本の射の連結度比較。元のプロ四角形が弱 n-引き戻しとの合成および K の適用はない（Lean が弱い）。"] _root_.SerrePositivity.KST.SConstruction.dgOdotMilnorCompletedLandTamme_isPullback
attribute [cite LT "Eq (3)" (partial := component) "仮定：可換基礎環上の指定 dg Milnor 正方形（Lean が強い）。結論：対角と resolved 商の完備化を与える。一般の E₁ 環の引き戻しを指定するものではない（Lean が弱い）。"] _root_.SerrePositivity.KST.SConstruction.dgOdotMilnorCompletedPerfectSequence
attribute [cite LT "Eq (4)" (partial := component) "仮定：可換基礎環上の指定 dg gluing の Milnor 正方形、Sp 値かつ filtered 余極限保存の局所化不変量（Lean が強い）。結論：実 resolved 商の冪等完備化を第 4 頂点とする Sp 引き戻しと、dg End の Morita 比較。任意の E₁ 環スペクトルについての自然な環の四辺と下部スペクトル A′⊗_A B の同定は含まない（Lean が弱い）。"] _root_.SerrePositivity.KST.SConstruction.dgOdotMilnorCompletedLandTamme_isPullback
attribute [cite LT "Thm 1.3" (partial := component) "仮定：可換基礎環上の指定 dg gluing の Milnor 正方形、Sp 値かつ filtered 余極限保存の局所化不変量（Lean が強い）。結論：実 resolved 商の冪等完備化を第 4 頂点とする Sp 引き戻しと、dg End の Morita 比較。任意の E₁ 環スペクトルについての自然な環の四辺と下部スペクトル A′⊗_A B の同定は含まない（Lean が弱い）。"] _root_.SerrePositivity.KST.SConstruction.dgOdotMilnorCompletedLandTamme_isPullback
attribute [cite LT "Thm 2.32" (partial := component) "仮定：前者は単一の dg Milnor 正方形と局所化不変量、後者は非正 dg 代数の塔と IsKConnective（Lean が強い）。結論：実 ⊙ 側の値の引き戻しと、別に塔の一本の射の連結度比較。元のプロ四角形が弱 n-引き戻しとの合成および K の適用はない（Lean が弱い）。"] _root_.SerrePositivity.KST.SConstruction.dgOdotMilnorCompletedLandTamme_isPullback
