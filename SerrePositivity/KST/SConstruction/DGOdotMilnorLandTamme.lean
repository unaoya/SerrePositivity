module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorLaxVerdier
public import SerrePositivity.KST.SConstruction.PerfectLaxQuotientValuePullback

/-!
概要：Milnor 条件と同じ resolved 商の指定完備化から Cat^perf の LT 出力を導く。
方針：元二因子・二射影を持つ実 lax 模型と証明済み Verdier 列へ Tamme 分裂を適用する。
規約：残る実完備化の供給と、元代数の固定 ν 模型との比較を完成扱いしない。
使われ方：e② の未供給入力を実商の完備化一つへ絞った主定理接続。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet Spectra DifferentialGraded InfinityCategories
  LocalizingInvariants

open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local instance : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R (DGOdotGluing R d) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnor_isDGPretriangulated R d
local instance : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgOdotQuotientInput R d).diagonal) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorNativeDiagonal_isExactFunctor R d
local instance : SimplicialCategory OmegaSpectrum.{u + 1} := OmegaSpectrum.simplicialCategory
variable (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d)
  (c : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorNativeResolvedQuotient R d)
    (dgKInputStableValue R (dgOdotMilnorResolvedInput R d)))
  (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion c.hom)

/-- 概要：元 Milnor 対角・resolved 商・指定完備化を持つ実 lax 商入力。
方針：元二因子の完備性と Milnor の実列を既存の入力に代入する。
規約：任意の比較同値・核・局所化証人は要求しない。使われ方：LT の実入力。 -/
def dgOdotMilnorLaxPerfectQuotient : PerfectLaxQuotient
    (dgOdotMilnorLaxYoneda R d) (dgOdotMilnorLaxCoefficient R d) where
  left := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorNativeDiagonalSource R d
  rawQuotient := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorNativeResolvedQuotient R d
  right := dgKInputStableValue R (dgOdotMilnorResolvedInput R d)
  inclusion := dgOdotMilnorLaxInclusion R d
  rawProjection := dgOdotMilnorLaxProjection R d
  isVerdier := dgOdotMilnorLax_isVerdier R d h
  left_complete := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorDiagonalSource_isIdempotentComplete R d
  c_complete := dgOdotMilnorLaxLeft_complete R d
  d_complete := dgOdotMilnorLaxRight_complete R d
  completion := c
  isCompletion := hc

local notation "Q" => dgOdotMilnorLaxPerfectQuotient R d h c hc

/-- 概要：完備化後の射は同じ実比較の逆・resolved 射影・指定完備化の合成。
方針：構成した射を回収する。規約：完備化後の射を strict 商とはしない。
使われ方：元商と e の射の照合。 -/
lemma dgOdotMilnorLaxPerfectProjection : (Q).sequence.projection.hom =
    ((dgOdotMilnorNativeLaxEquivalence R d).inv ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorResolvedProjection R d).hom) ≫ c.hom := rfl

variable {F : perfectStableInfinity.{u + 1} ⟶ Sp.{u + 1}} (hF : IsPerfectLocalizingInvariant F)

/-- 概要：元二因子・元対角・同じ resolved 商の完備化による実 BF 正方形。
方針：既存の四辺固定 LT 構成を具体的 Milnor 入力へ適用する。
規約：実完備化証人だけは明示入力。使われ方：Cat^perf の LT 結論。 -/
def dgOdotMilnorLandTammeSquare : (Δ[1] ⊗ Δ[1] : SSet.{u + 2}) ⟶ Sp.{u + 1} :=
  (Q).valuePullbackSquare hF

/-- 概要：同じ実 Milnor 正方形を全局所化不変量が引き戻しへ送る。
方針：元 Tamme 分裂と証明済み resolved Verdier 列を使う。
規約：未供給の実完備化を証明済みとしない。使われ方：e② の形式的な主定理。 -/
theorem dgOdotMilnorLandTamme_isPullback :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (dgOdotMilnorLandTammeSquare R d h c hc hF) :=
  (Q).valuePullbackSquare_isPullback hF

/-- 概要：同じ下辺は元の第一因子へ向かう包含・射影の値。
方針：四辺固定の既存構成を回収する。規約：射の類だけではない。
使われ方：元の左射影への比較。 -/
lemma dgOdotMilnorLandTamme_bottom :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ dgOdotMilnorLandTammeSquare R d h c hc hF =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge ((Q).valueCSource F)).edge :=
  (Q).valuePullbackSquare_bottom hF

/-- 概要：同じ左辺は元の第二因子へ向かう包含・射影の値。
方針：四辺固定の既存構成を回収する。規約：元二因子の順序を保つ。
使われ方：元の右射影への比較。 -/
lemma dgOdotMilnorLandTamme_left :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ dgOdotMilnorLandTammeSquare R d h c hc hF =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge ((Q).valueDSource F)).edge :=
  (Q).valuePullbackSquare_left hF

/-- 概要：同じ右辺は第一因子から resolved 商の完備化への脚の値。
方針：元の二脚の構成を回収する。規約：指定完備化を保持する。
使われ方：LT の実 cospan の第一脚。 -/
lemma dgOdotMilnorLandTamme_right :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ dgOdotMilnorLandTammeSquare R d h c hc hF =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge ((Q).valueCLeg F)).edge :=
  (Q).valuePullbackSquare_right hF

/-- 概要：同じ上辺は第二因子から resolved 商の完備化への脚の値。
方針：元の二脚の構成を回収する。規約：指定完備化を保持する。
使われ方：LT の実 cospan の第二脚。 -/
lemma dgOdotMilnorLandTamme_top :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ dgOdotMilnorLandTammeSquare R d h c hc hF =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge ((Q).valueDLeg F)).edge :=
  (Q).valuePullbackSquare_top hF

/-- 概要：同じ resolved 商の完備化への二脚を持つ実 cospan。
方針：四辺を固定した同じ正方形から取り出す。
規約：脚を選び直さない。使われ方：実 LT 極限錐の底。 -/
def dgOdotMilnorLandTammeCospan : (horn 2 2 : SSet.{u + 2}) ⟶ Sp.{u + 1} :=
  (Q).valuePullbackCospan hF

/-- 概要：元小 Perf 対角始域の値を頂点とする同じ実錐。
方針：既存の四辺固定錐を特殊化する。規約：同値な別頂点で代用しない。
使われ方：LT の極限表示。 -/
def dgOdotMilnorLandTammeCone : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (dgOdotMilnorLandTammeCospan R d h c hc hF) :=
  (Q).valuePullbackCone hF

/-- 概要：同じ二脚と元対角始域値を持つ錐は ∞ 極限。
方針：Tamme と Milnor の具体的商列からの引き戻し性を使う。
規約：π 群の比較に弱めない。使われ方：e② の実錐の結論。 -/
theorem dgOdotMilnorLandTammeCone_isLimit :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (dgOdotMilnorLandTammeCone R d h c hc hF) :=
  (Q).valuePullbackCone_isLimit hF

/-- 概要：極限錐の頂点は元の同じ小 Perf 対角始域への不変量値。
方針：既存の頂点回収式を使う。規約：対象の同型類だけではない。
使われ方：元代数の Perf 表示との照合。 -/
lemma dgOdotMilnorLandTammeCone_source :
    (dgOdotMilnorLandTammeCone R d h c hc hF).vertex =
      F.app (Opposite.op ⦋0⦌) (perfectStableVertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorNativeDiagonalSource R d)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorDiagonalSource_isIdempotentComplete R d)) :=
  (Q).valuePullbackCone_vertex_value hF

end SerrePositivity.KST.SConstruction
