module

public import SerrePositivity.KST.DerivedBlowup.DiagramGaugeModuleHomIso
public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapTwistDGComparison
public import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence

/-!
概要：KST v4 §3.1（pp.11–14）の整数捻りは既存 dg 模型の準同値。
方針：gauge 制限の全 Hom 複体同型と、指定導来比較による H⁰ の同値を組み合わせる。
規約：原典とは異なる図式加群模型での証明。層の降下・dg 商との比較は別工程。
使われ方：捻りが導来 mapping 複体を保つことの保証。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory DifferentialGraded

variable (R : Type u) [CommRing R] {I : Type} [DecidableEq I] (a : I → R)

/-- 概要：全図式加群の dg 捻りの全 Hom 写像は複体同型。
方針：一般 gauge の指定 Hom 同型を具体的な推移単元の整数冪へ適用する。
規約：KST §3.1。使われ方：射影的部分模型への制限。 -/
theorem finiteOverlapDGTwistAction_map_isIso (m : ℤ)
    (M N : RightModule R (BlowupDiagramCoefficientObject R a)ᵒᵖ) :
    IsIso ((finiteOverlapDGTwistAction R a m).map M N) :=
  (diagramGaugeModuleHomIso (finiteOverlapDGAlgebraDiagram R a)
    (finiteOverlapTwistGauge R a m) M N).isIso_hom

/-- 概要：射影的図式 dg 模型の整数捻りは全 Hom 複体を保つ。
方針：充満 dg 部分圏への制限は Hom 写像を変えない。
規約：KST §3.1。使われ方：cartesian perfect 条件を加えた模型の Hom 比較。 -/
theorem projectiveDiagramTwistDGFunctor_map_isIso (m : ℤ)
    (M N : ProjectiveDiagramModules (finiteOverlapDGAlgebraDiagram R a)) :
    IsIso ((projectiveDiagramTwistDGFunctor R a m).map M N) :=
  finiteOverlapDGTwistAction_map_isIso R a m M.val N.val

/-- 概要：既存 cartesian perfect 射影的 dg 模型の整数捻りは全 Hom で同型。
方針：二段の充満 dg 制限を忘れ、元の gauge Hom 同型を使う。
規約：KST §3.1。使われ方：dg 準同値の Hom 条件。 -/
theorem blowupTwistDGFunctor_map_isIso (m : ℤ)
    (M N : CartesianPerfectDiagramDGModel R a) :
    IsIso ((blowupTwistDGFunctor R a m).map M N) :=
  projectiveDiagramTwistDGFunctor_map_isIso R a m M.val N.val

/-- 概要：dg 模型上の捻り前後の mapping 複体の指定同型。
方針：実際の dg 関手の Hom 写像を順射とする。
規約：KST §3.1。使われ方：半直交性の Hom 消滅を捻りで移す。 -/
def blowupTwistHomIso (m : ℤ) (M N : CartesianPerfectDiagramDGModel R a) :
    homObject R (CartesianPerfectDiagramDGModel R a) M N ≅
      homObject R (CartesianPerfectDiagramDGModel R a)
        ((blowupTwistDGFunctor R a m).obj M) ((blowupTwistDGFunctor R a m).obj N) := by
  letI := blowupTwistDGFunctor_map_isIso R a m M N
  exact asIso ((blowupTwistDGFunctor R a m).map M N)

/-- 概要：整数捻りは既存 cartesian perfect dg 模型の準同値。
方針：全 Hom 複体の同型性と、指定導来比較で証明した H⁰ の本質的全射性を使う。
規約：KST §3.1、層の Perf や coherent な極限との比較は独立した義務。
使われ方：生成系・半直交分解での dg 捻りの可逆性。 -/
theorem blowupTwistDGFunctor_quasiEquivalence (m : ℤ) :
    QuasiEquivalence (blowupTwistDGFunctor R a m) := by
  refine ⟨?_, inferInstance⟩
  intro M N
  let := blowupTwistDGFunctor_map_isIso R a m M N
  infer_instance

end SerrePositivity.KST.DerivedBlowup
