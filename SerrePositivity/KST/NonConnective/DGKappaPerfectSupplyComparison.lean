module
public import SerrePositivity.KST.NonConnective.DGKappaPerfectSupply
public import SerrePositivity.KST.NonConnective.DGKappaResolvedEvaluationInclusion
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FullyFaithfulIsoRecovery

/-!
概要：同じ I に対する既存 P と D の実供給 P を、元の全導来包含を通して照合する。
方針：同じ完全充満包含から全関手同型を戻し、実評価 Perf 比較の入力依存を検証する。
規約：同じ I を固定し、異なる dg 入力間の自然性はここから推論しない。
使われ方：K-7 c5・d4 の P の実供給への差し替えと元の全 native Perf 比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] (D : PerfDGInput.{u, max (u + 1) v} R)
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)

/-- 概要：同じ I の perfect 安定閉包を元の実導来模型へ含める全関手。
方針：元の安定閉包包含と I の指定導来比較を合成する。
規約：P の比較射を使わず、元の実包含を固定する。
使われ方：既存 P と標準 P の比較を反映する同じ実射。 -/
abbrev dgKappaPerfectDerivedInclusion :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableClosureInclusion R (DGKappaCone R D I) (dgKappaConePerfectObjects R D I) ≫
    dgKappaConeDerivedComparison R D I

/-- 概要：同じ実 perfect 閉包の導来包含は全写像空間で充満忠実。
方針：正本の安定閉包包含と元の I の充満忠実性を合成する。
規約：新たな包含や充満忠実性の仮定を加えない。
使われ方：元の P の全関手比較を実供給へ戻す。 -/
theorem dgKappaPerfectDerivedInclusion_isFullyFaithful :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (dgKappaPerfectDerivedInclusion R D I) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableClosureInclusion_isFullyFaithful R (DGKappaCone R D I)
    (dgKappaConePerfectObjects R D I)).comp I.derivedFullyFaithful

/-- 概要：元の実包含後で、既存 P と実供給 P を同じ二つの包含同型で比較する。
方針：元の指定 Perf 包含への同型を、標準 P の同型の逆と合成する。
規約：同じ包含の全関手同型を使い、点別の同型を選ばない。
使われ方：同じ完全充満包含で反映する元の比較そのもの。 -/
def dgKappaPerfectSupplyDerivedIso (P : DGKappaPerfectInput R D I) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (P.comparison ≫ dgKappaPerfectDerivedInclusion R D I)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaPerfect.dgKappaPerfectInput R D I).comparison ≫ dgKappaPerfectDerivedInclusion R D I) := by
  simpa only [dgKappaPerfectDerivedInclusion, Category.assoc] using!
    P.inclusion ≪≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaPerfect.dgKappaPerfectInput R D I).inclusion.symm

/-- 概要：同じ I の任意の既存 P は、D の実供給 P と全 native Perf 関手として同型。
方針：元の実導来包含の充満忠実性で同じ指定比較を戻す。
規約：元の包含比較を保持し、D の入力族全体での自然性を主張しない。
使われ方：K-7 c5・d4 の実供給 P と既存 P の選択比較。 -/
def dgKappaPerfectSupplyComparison (P : DGKappaPerfectInput R D I) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso P.comparison (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaPerfect.dgKappaPerfectInput R D I).comparison :=
  (dgKappaPerfectDerivedInclusion_isFullyFaithful R D I).preimageFunctorIso
    (dgKappaPerfectSupplyDerivedIso R D I P)

/-- 概要：同じ実小核への元の P 比較も、標準 P の全関手比較と同型。
方針：同じ実核増大の指定逆を、構成済みの P 比較へ後合成する。
規約：核同値の逆射を選び直さない。
使われ方：既存の実評価・実構造射の元の Perf 始点との照合。 -/
def dgKappaPerfectResolvedSupplyComparison (P : DGKappaPerfectInput R D I) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (dgKappaPerfectResolvedComparison R D I P)
      (dgKappaPerfectResolvedComparison R D I (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaPerfect.dgKappaPerfectInput R D I)) :=
  (dgKappaPerfectSupplyComparison R D I P).postcomp
    (dgKappaResolvedKernelNerveEquivalence R D I).inv

/-- 概要：同じ実評価 Morita 核の固定 ν の Perf 同値は、P の選択を変更しても同じ実値。
方針：P は同じ実評価核の Morita 性の証明だけに使われることを定義的に確認する。
規約：元の同じ I・核・評価・ラベル同値を保持する。
使われ方：K-7 c5 の標準 P への差し替えで実評価 Perf 同値を選び直さない。 -/
theorem dgKappaResolvedKernelPerfEquivalence_perfect_input_irrel
    (P Q : DGKappaPerfectInput R D I) :
    dgKappaResolvedKernelPerfEquivalence R D I P = dgKappaResolvedKernelPerfEquivalence R D I Q :=
  rfl

/-- 概要：戻した P 選択比較の包含後は、元の二つの指定包含同型による比較そのもの。
方針：正本の充満忠実な後合成の回収則を同じ実包含へ適用する。
規約：比較の存在だけでなく、指定された元の同型を保持する。
使われ方：実供給への差し替えで元の包含二胞体を選び直さないことの確認。 -/
theorem dgKappaPerfectSupplyComparison_derived (P : DGKappaPerfectInput R D I) :
    (dgKappaPerfectSupplyComparison R D I P).postcomp (dgKappaPerfectDerivedInclusion R D I) =
      dgKappaPerfectSupplyDerivedIso R D I P :=
  (dgKappaPerfectDerivedInclusion_isFullyFaithful R D I).preimageFunctorIso_postcomp _

/-- 概要：同じ実小核の厳密評価 dg 関手も、P の選択を変更しても同じ実射。
方針：P は同じ列の perfect 所属の証明にだけ使われることを確認する。
規約：元の実評価の全対象・全 dg Hom 作用を保持する。
使われ方：実供給 P と既存 P の比較における実評価の固定。 -/
theorem dgKappaResolvedPerfectEvaluation_perfect_input_irrel
    (P Q : DGKappaPerfectInput R D I) :
    dgKappaResolvedPerfectEvaluation R D I P = dgKappaResolvedPerfectEvaluation R D I Q := rfl

/-- 概要：同じ実核から作る元の構造射は、同じ I・零所属のもとで P の選択に依存しない。
方針：同じ実評価 Perf 同値の入力独立性を元の構造射へ適用する。
規約：各入力での同じ実射の等号であり、異なる dg 入力間の β 自然性は別工程。
使われ方：K-7 c5・d の標準 P への差し替えで構造射を選び直さないことの照合。 -/
theorem dgKappaResolvedConnectiveStructureMap_perfect_input_irrel
    (P Q : DGKappaPerfectInput R D I) (Z : DGKappaZeroInput R D I) :
    dgKappaResolvedConnectiveStructureMap R D I (dgKappaResolvedKernelPerfEquivalence R D I P)
        Z (dgKappaResolvedNullPerf_isZero R D I) =
      dgKappaResolvedConnectiveStructureMap R D I (dgKappaResolvedKernelPerfEquivalence R D I Q)
        Z (dgKappaResolvedNullPerf_isZero R D I) :=
  congrArg (fun e => dgKappaResolvedConnectiveStructureMap R D I e Z
    (dgKappaResolvedNullPerf_isZero R D I))
      (dgKappaResolvedKernelPerfEquivalence_perfect_input_irrel R D I P Q)

/-- 概要：同じ I の任意の二つの P を、同じ実供給 P を介する全関手同型で比較する。
方針：元の二つの標準 P 比較を一方の逆と合成する。
規約：元の Perf 全 Hom 上の比較であり、入力 D 自体は固定する。
使われ方：K-7 d4 の P 選択比較を同じ標準供給で正規化する。 -/
def dgKappaPerfectChoiceIso (P Q : DGKappaPerfectInput R D I) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso P.comparison Q.comparison :=
  dgKappaPerfectSupplyComparison R D I P ≪≫ (dgKappaPerfectSupplyComparison R D I Q).symm

/-- 概要：同じ P への選択比較は元の全関手の恒等同型。
方針：同じ標準比較とその逆を相殺する。
規約：各点の恒等性だけへ弱めない。
使われ方：同じ標準供給を通す P 選択比較の単位則。 -/
theorem dgKappaPerfectChoiceIso_self (P : DGKappaPerfectInput R D I) :
    dgKappaPerfectChoiceIso R D I P P = Iso.refl _ := by
  exact Iso.self_symm_id _

/-- 概要：三つの P の選択比較は、同じ標準供給を介して厳密な合成則を満たす。
方針：中間の同じ標準比較の逆と順を相殺する。
規約：全関手同型自体の等式であり、異なる dg 入力間の自然性は別工程。
使われ方：K-7 d4 の P 選択比較の整合性。 -/
theorem dgKappaPerfectChoiceIso_trans (P Q U : DGKappaPerfectInput R D I) :
    dgKappaPerfectChoiceIso R D I P Q ≪≫ dgKappaPerfectChoiceIso R D I Q U =
      dgKappaPerfectChoiceIso R D I P U := by
  apply Iso.ext
  simp only [dgKappaPerfectChoiceIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id_assoc]

end SerrePositivity.KST.NonConnective
