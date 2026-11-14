module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorResolvedInput
public import SerrePositivity.KST.SConstruction.DGKInputIdempotentComplete
public import SerrePositivity.KST.SConstruction.PerfectLaxIdempotent
public import SerrePositivity.KST.SConstruction.PerfectVerdierPresentation
public import SerrePositivity.KST.SConstruction.PerfectLocalizingInvariant
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Comparison.LaxComparisonEquivalence

/-!
概要：Milnor の native Verdier 列の左端・中央の完備性を証明し Cat^perf へ接続する。
方針：実小 Perf の完備性と D2 の元の lax 比較を使い、実商の完備化だけを分離する。
規約：未完備な native 商を固定 ν の Perf 値と同一視しない。
使われ方：resolved 商の実完備化が供給された際の同じ Cat^perf fiber 列。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet DifferentialGraded InfinityCategories LocalizingInvariants Spectra
variable (R : Type u) [CommRing R] (d : DGOdotInput R)

local notation "A" => _root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R (DGOdotInput.source d)
local notation "C" => DGSmallPerfectArrowTarget R (A) (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R d.left)
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.top)
local notation "D" => DGSmallPerfectArrowTarget R (A) (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R d.right)
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.side)
local notation "V" => DGSmallPerfectSquareCorner R (A) (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R d.left)
  (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R d.right) (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R d.corner)
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.top) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.side) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.lower) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.upper)
local notation "p" => dgSmallPerfectSquareLeftMap R (A) (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R d.left)
  (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R d.right) (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R d.corner)
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.top) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.side) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.lower) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.upper)
local notation "q" => dgSmallPerfectSquareRightMap R (A) (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R d.left)
  (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R d.right) (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R d.corner)
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.top) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.side) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.lower) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.upper)
local notation "M" => dgHomGluingBimodule R (C) (D) (V) (p) (q)

/-- 概要：元の左小 Perf 模型の coherent 完備性。
方針：D の実 Perf 完備性を同じ小模型評価の逆で移す。
規約：四角形の追加仮定なし。使われ方：D2 の lax 完備性の第一入力。 -/
lemma dgOdotMilnorNativeLeft_complete : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (C)) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectModuleNerve_isIdempotentComplete R (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R d.left)).of_equivalence
    (dgSmallPerfectEnvelopeNerveEquivalence R (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R d.left)
      (DGSmallPerfectBase R (A))
      (dgSmallPerfectEnvelopeExtensionFamily R (A) (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R d.left) Empty
        (dgSmallPerfectBaseFamily R (A)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.top))).symm

/-- 概要：元の右小 Perf 模型の coherent 完備性。
方針：D の実 Perf 完備性を同じ小模型評価の逆で移す。
規約：四角形の追加仮定なし。使われ方：D2 の lax 完備性の第二入力。 -/
lemma dgOdotMilnorNativeRight_complete : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (D)) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectModuleNerve_isIdempotentComplete R (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R d.right)).of_equivalence
    (dgSmallPerfectEnvelopeNerveEquivalence R (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R d.right)
      (DGSmallPerfectBase R (A))
      (dgSmallPerfectEnvelopeExtensionFamily R (A) (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R d.right) Empty
        (dgSmallPerfectBaseFamily R (A)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.side))).symm

/-- 概要：元 gluing 自身の native nerve は coherent 冪等完備。
方針：元小 Perf 二因子の完備性から D2 の同じ lax pullback の完備性を戻す。
規約：Perf(gluing) への置換で代用しない。使われ方：実 Verdier 列の中央完備性。 -/
lemma dgOdotMilnorNativeMiddle_complete : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (DGOdotGluing R d)) := by
  have hC := (dgOdotMilnorNativeLeft_complete R d).ulift.{u + 1}
  have hD := (dgOdotMilnorNativeRight_complete R d).ulift.{u + 1}
  have hL := perfectLaxPullback_isIdempotentComplete
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedYoneda.{u, u + 1, u + 1} R (C))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedCoefficient R (C) (D) (M)) hC hD
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.isIdempotentComplete_of_ulift
    (hL.of_equivalence (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedNerveLaxEquivalence R (C) (D) (M)).symm)

local instance : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R (DGOdotGluing R d) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnor_isDGPretriangulated R d

variable (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d)
  (c : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorNativeResolvedQuotient R d)
    (dgKInputStableValue R (dgOdotMilnorResolvedInput R d)))
  (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion c.hom)

/-- 概要：Milnor の実列を resolved 商の指定完備化で Cat^perf に提示する。
方針：左・中央の既証明の完備性を使う。規約：完備化射の実証拠だけは入力。
使われ方：実商の strict 局所化と完備化後の列を区別した接続。 -/
def dgOdotMilnorPerfectSequence : PerfectVerdierSequence.{u + 1} where
  verdier := dgOdotMilnorNativeSequence R d h
  left_complete := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorDiagonalSource_isIdempotentComplete R d
  middle_complete := dgOdotMilnorNativeMiddle_complete R d
  right := dgKInputStableValue R (dgOdotMilnorResolvedInput R d)
  completion := c
  isCompletion := hc

/-- 概要：同じ実包含・resolved 商・指定完備化を持つ Cat^perf の全四角形。
方針：既存の全単体を保つ提示を適用する。規約：完備化の存在は入力のまま。
使われ方：全 Cat^perf 局所化不変量での実 fiber 列。 -/
def dgOdotMilnorPerfectDiagram : PerfectVerdierDiagram.{u + 1} :=
  (dgOdotMilnorPerfectSequence R d h c hc).presentation

/-- 概要：同じ Cat^perf 図式は局所化不変量で fiber 列になる。
方針：Milnor の実列を既存の局所化条件へ接続する。
規約：K の局所化性や未供給の完備化を結論しない。使われ方：e② の形式的接続。 -/
theorem dgOdotMilnorPerfect_isFiber
    {F : perfectStableInfinity.{u + 1} ⟶ Sp.{u + 1}} (hF : IsPerfectLocalizingInvariant F) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsFiberSequence (hF.fiberTriangle (dgOdotMilnorPerfectDiagram R d h c hc)) :=
  hF.fiberTriangle_isFiber _

end SerrePositivity.KST.SConstruction
