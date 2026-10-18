module

public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapTwistProjective
public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapTwistCartesianAction

/-!
概要：KST v4 §3.1（pp.11–14）の捻りを既存の射影的 cartesian perfect dg 模型へ制限する。
方針：全次数の制限関手を、ホモトピー射影性と指定導来対象条件の保存で制限する。
規約：原典とは異なる図式加群模型の構成。層・高次降下との比較は別に残す。
使われ方：導来 blowup の実際の dg 模型上の整数捻り。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory DifferentialGraded

variable (R : Type u) [CommRing R] {I : Type} [DecidableEq I] (a : I → R)

/-- 概要：整数捻りは既存の射影的図式 dg 模型に作用する。
方針：対象には射影性の保存を付け、全 Hom 写像と法則は元の制限から継承する。
規約：KST §3.1。使われ方：cartesian perfect 模型への更なる制限。 -/
def projectiveDiagramTwistDGFunctor (m : ℤ) :
    DGFunctor R (ProjectiveDiagramModules (finiteOverlapDGAlgebraDiagram R a))
      (ProjectiveDiagramModules (finiteOverlapDGAlgebraDiagram R a)) where
  obj M := ⟨(finiteOverlapDGTwistAction R a m).obj M.val,
    finiteOverlapTwistAction_homotopicallyProjective R a m M.property⟩
  map M N := (finiteOverlapDGTwistAction R a m).map M.val N.val
  map_id M := (finiteOverlapDGTwistAction R a m).map_id M.val
  map_comp M N P := (finiteOverlapDGTwistAction R a m).map_comp M.val N.val P.val

/-- 概要：通常捻りの主導来像と指定導来捻りは同じ対象。
方針：既存の導来制限の標準因子分解を対象で評価する。
規約：KST §3.1。使われ方：dg 模型の対象条件の保存を確認する。 -/
theorem finiteOverlapTwistAction_derived_obj (m : ℤ)
    (M : AllDiagramModules (finiteOverlapDGAlgebraDiagram R a)) :
    (finiteOverlapDerivedTwistAction R a m).obj
        ((moduleToDerived R (BlowupDiagramCoefficientObject R a)ᵒᵖ).obj M) =
      (moduleToDerived R (BlowupDiagramCoefficientObject R a)ᵒᵖ).obj
        ((finiteOverlapTwistAction R a m).obj M) :=
  congrArg (fun G => G.obj M) (dgDerivedRestriction_fac R _ _
    (finiteOverlapTwistDGFunctor R a m).op)

/-- 概要：射影的捻りは元の模型の cartesian perfect 条件を保つ。
方針：因子分解等式を使い、全導来対象で証明済みの保存へ帰着する。
規約：KST §3.1。使われ方：実際の dg 候補への対象の持ち上げ。 -/
theorem projectiveDiagramTwist_cartesianPerfect (m : ℤ)
    (M : ProjectiveDiagramModules (finiteOverlapDGAlgebraDiagram R a))
    (hM : projectiveDiagramCartesianPerfect R a M) :
    projectiveDiagramCartesianPerfect R a ((projectiveDiagramTwistDGFunctor R a m).obj M) := by
  change diagramCartesianPerfect R a ((moduleToDerived R _).obj
    ((finiteOverlapTwistAction R a m).obj (ForgetEnrichment.of (Complex R) M.val)))
  rw [← finiteOverlapTwistAction_derived_obj]
  exact (finiteOverlapDerivedTwistAction_cartesianPerfect_iff R a m _).mpr hM

/-- 概要：既存 cartesian perfect 射影的 dg 模型上の整数捻り。
方針：対象を保存する射影的 dg 捻りの全 Hom と法則をそのまま制限する。
規約：KST §3.1、dg 商の普遍性・層の降下の比較とは区別する。
使われ方：生成系と半直交分解で必要になる dg レベルの捻り。 -/
def blowupTwistDGFunctor (m : ℤ) :
    DGFunctor R (CartesianPerfectDiagramDGModel R a) (CartesianPerfectDiagramDGModel R a) where
  obj M := ⟨(projectiveDiagramTwistDGFunctor R a m).obj M.val,
    projectiveDiagramTwist_cartesianPerfect R a m M.val M.property⟩
  map M N := (projectiveDiagramTwistDGFunctor R a m).map M.val N.val
  map_id M := (projectiveDiagramTwistDGFunctor R a m).map_id M.val
  map_comp M N P := (projectiveDiagramTwistDGFunctor R a m).map_comp M.val N.val P.val

end SerrePositivity.KST.DerivedBlowup
