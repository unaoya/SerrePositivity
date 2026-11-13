module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapExceptionalCartesianConditions

/-!
概要：KST v4 §3.1・Lemma 3.6（pp.11–14）の cartesian・局所 perfect な射影的図式模型の H⁰ 比較。
方針：全図式の H⁰ 比較を充満部分圏へ制限し、標準分解へ条件を同型で移す。
規約：dg 商の普遍性や層の降下との比較はこの通常圏の同値とは区別する。
使われ方：指定 cartesian 条件を持つ実際の dg 模型の H⁰ の確認。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory
open DifferentialGraded

variable (R : Type u) [CommRing R] {I : Type} [DecidableEq I]

/-- 概要：cartesian・局所 perfect な主導来図式加群の充満部分圏。
方針：二つの指定済み条件で主導来圏の対象を制限する。
規約：KST v4 §3.1・Lemma 3.6（pp.11–14）。使われ方：射影的候補模型の H⁰ 比較の行先。 -/
abbrev ExceptionalCartesianPerfectDerivedDiagramModules (a : I → R) :=
  (exceptionalDiagramCartesianPerfect R a).FullSubcategory

/-- 概要：cartesian perfect 射影的図式模型から全射影的図式模型への包含。
方針：Hom 複体を変えない充満 dg 包含を用いる。
規約：KST v4 §3.1・Lemma 3.6（pp.11–14）。使われ方：全図式の H⁰ 比較を制限する。 -/
def exceptionalCartesianPerfectDiagramInclusion (a : I → R) :
    DGFunctor R (ExceptionalCartesianPerfectDiagramDGModel R a)
      (ProjectiveDiagramModules (finiteOverlapExceptionalDGAlgebraDiagram R a)) :=
  dgFullSubcategoryInclusion R _ (projectiveExceptionalDiagramCartesianPerfect R a)

/-- 概要：指定 cartesian perfect dg 模型の H⁰ から主導来部分圏への比較。
方針：全図式比較を合成し、定義通りの対象条件で行先を制限する。
規約：KST v4 §3.1・Lemma 3.6（pp.11–14）。使われ方：実際の Hom 複体を備えた候補模型の検証。 -/
def exceptionalCartesianPerfectDiagramToDerived (a : I → R) :
    HomotopyCategory R (ExceptionalCartesianPerfectDiagramDGModel R a) ⥤
      ExceptionalCartesianPerfectDerivedDiagramModules R a :=
  (exceptionalDiagramCartesianPerfect R a).lift
    ((exceptionalCartesianPerfectDiagramInclusion R a).onHomotopy ⋙
      projectiveDiagramModuleToDerived (finiteOverlapExceptionalDGAlgebraDiagram R a))
    (fun X => (exceptionalDiagramCartesianPerfect R a).prop_of_iso
      ((moduleToHomotopyDerivedIso R (DiagramModuleCoefficientObject
        (finiteOverlapExceptionalDGAlgebraDiagram R a))ᵒᵖ).app
        (ForgetEnrichment.of (Complex R)
          (ForgetEnrichment.to (Complex R) X.as).val.val)).symm
      (ForgetEnrichment.to (Complex R) X.as).property)

/-- 概要：指定条件への H⁰ 比較は充満。
方針：充満 dg 包含と全図式の充満比較の合成を使う。
規約：KST v4 §3.1・Lemma 3.6（pp.11–14）。使われ方：候補模型の完全忠実性。 -/
instance exceptionalCartesianPerfectDiagramToDerivedFull (a : I → R) :
    (exceptionalCartesianPerfectDiagramToDerived R a).Full := by
  unfold exceptionalCartesianPerfectDiagramToDerived exceptionalCartesianPerfectDiagramInclusion
  infer_instance

/-- 概要：指定条件への H⁰ 比較は忠実。
方針：充満 dg 包含と全図式の忠実比較の合成を使う。
規約：KST v4 §3.1・Lemma 3.6（pp.11–14）。使われ方：候補模型の完全忠実性。 -/
instance exceptionalCartesianPerfectDiagramToDerivedFaithful (a : I → R) :
    (exceptionalCartesianPerfectDiagramToDerived R a).Faithful := by
  unfold exceptionalCartesianPerfectDiagramToDerived exceptionalCartesianPerfectDiagramInclusion
  infer_instance

/-- 概要：全ての cartesian perfect 導来対象は射影的候補模型で表せる。
方針：標準半自由分解の擬同型に沿って同型不変な条件を移す。
規約：KST v4 §3.1・Lemma 3.6（pp.11–14）。使われ方：候補模型の H⁰ 比較の本質的全射性。 -/
instance exceptionalCartesianPerfectDiagramToDerivedEssSurj (a : I → R) :
    (exceptionalCartesianPerfectDiagramToDerived R a).EssSurj where
  mem_essImage X := by
    let F := finiteOverlapExceptionalDGAlgebraDiagram R a
    let P := diagramModuleProjectiveResolution F X.obj.as.obj
    let e : (moduleToDerived R (DiagramModuleCoefficientObject
      (finiteOverlapExceptionalDGAlgebraDiagram R a))ᵒᵖ).obj P.obj ≅ X.obj :=
      moduleDerivedIso R (DiagramModuleCoefficientObject
        (finiteOverlapExceptionalDGAlgebraDiagram R a))ᵒᵖ P.π P.quasiIso
    let M := projectiveDiagramModuleRepresentative F X.obj.as.obj
    have hM : projectiveExceptionalDiagramCartesianPerfect R a M :=
      (exceptionalDiagramCartesianPerfect R a).prop_of_iso e.symm X.property
    let N : ExceptionalCartesianPerfectDiagramDGModel R a := ⟨M, hM⟩
    refine ⟨(toHomotopy R (ExceptionalCartesianPerfectDiagramDGModel R a)).obj
      (ForgetEnrichment.of (Complex R) N), ⟨?_⟩⟩
    exact (exceptionalDiagramCartesianPerfect R a).ι.preimageIso
      ((moduleToHomotopyDerivedIso R (DiagramModuleCoefficientObject
        (finiteOverlapExceptionalDGAlgebraDiagram R a))ᵒᵖ).app P.obj ≪≫ e)

/-- 概要：指定 cartesian perfect 模型の H⁰ 比較は圏同値。
方針：完全忠実性と標準分解による本質的全射性を束ねる。
規約：KST v4 §3.1・Lemma 3.6（pp.11–14）。使われ方：射影的候補模型の H⁰ の同定。 -/
instance exceptionalCartesianPerfectDiagramToDerivedIsEquivalence (a : I → R) :
    (exceptionalCartesianPerfectDiagramToDerived R a).IsEquivalence where

/-- 概要：指定 cartesian perfect dg 模型の H⁰ と主導来部分圏の同値。
方針：実際の構成済み比較関手を同値として読む。
規約：KST v4 §3.1・Lemma 3.6（pp.11–14）、層・dg 商・高次降下との比較は別に残す。
使われ方：全図式の導来 Hom を保つ候補模型の通常圏レベルの保証。 -/
def exceptionalCartesianPerfectDiagramHomotopyEquivalence (a : I → R) :
    HomotopyCategory R (ExceptionalCartesianPerfectDiagramDGModel R a) ≌
      ExceptionalCartesianPerfectDerivedDiagramModules R a :=
  (exceptionalCartesianPerfectDiagramToDerived R a).asEquivalence

end SerrePositivity.KST.DerivedBlowup

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite KST "Construction §3.1 thickenings" (partial := component) "仮定：明示的な例外因子のチャート dg 模型と有限重なり（Lean が強い）。結論：例外因子のチャート比較と完全加群の比較。D(n) と E(n) を含む導来スキーム全体の厚化・立方体は含まない（Lean が弱い）。"] _root_.SerrePositivity.KST.DerivedBlowup.exceptionalCartesianPerfectDiagramToDerivedIsEquivalence
attribute [cite KST "Eq (3.3)" (partial := component) "仮定：明示的な例外因子のチャート dg 模型と有限重なり（Lean が強い）。結論：例外因子のチャート比較と完全加群の比較。D(n) と E(n) を含む導来スキーム全体の厚化・立方体は含まない（Lean が弱い）。"] _root_.SerrePositivity.KST.DerivedBlowup.exceptionalCartesianPerfectDiagramToDerivedIsEquivalence
attribute [cite KST "Rem 3.2" (partial := component) "仮定：明示的な例外因子のチャート dg 模型と有限重なり（Lean が強い）。結論：例外因子のチャート比較と完全加群の比較。D(n) と E(n) を含む導来スキーム全体の厚化・立方体は含まない（Lean が弱い）。"] _root_.SerrePositivity.KST.DerivedBlowup.exceptionalCartesianPerfectDiagramToDerivedIsEquivalence
