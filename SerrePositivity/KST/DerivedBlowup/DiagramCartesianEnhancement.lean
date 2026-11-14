module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.KST.DerivedBlowup.DiagramCartesianIsomorphism

/-!
概要：KST §3.1 の cartesian・局所 perfect な射影的図式模型の H⁰ 比較。
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
規約：KST §3.1。使われ方：射影的候補模型の H⁰ 比較の行先。 -/
abbrev CartesianPerfectDerivedDiagramModules (a : I → R) :=
  (diagramCartesianPerfect R a).FullSubcategory

/-- 概要：cartesian perfect 射影的図式模型から全射影的図式模型への包含。
方針：Hom 複体を変えない充満 dg 包含を用いる。
規約：KST §3.1。使われ方：全図式の H⁰ 比較を制限する。 -/
def cartesianPerfectDiagramInclusion (a : I → R) :
    DGFunctor R (CartesianPerfectDiagramDGModel R a)
      (ProjectiveDiagramModules (finiteOverlapDGAlgebraDiagram R a)) :=
  dgFullSubcategoryInclusion R _ (projectiveDiagramCartesianPerfect R a)

/-- 概要：指定 cartesian perfect dg 模型の H⁰ から主導来部分圏への比較。
方針：全図式比較を合成し、定義通りの対象条件で行先を制限する。
規約：KST §3.1。使われ方：実際の Hom 複体を備えた候補模型の検証。 -/
def cartesianPerfectDiagramToDerived (a : I → R) :
    HomotopyCategory R (CartesianPerfectDiagramDGModel R a) ⥤
      CartesianPerfectDerivedDiagramModules R a :=
  (diagramCartesianPerfect R a).lift
    ((cartesianPerfectDiagramInclusion R a).onHomotopy ⋙
      projectiveDiagramModuleToDerived (finiteOverlapDGAlgebraDiagram R a))
    (fun X => (diagramCartesianPerfect R a).prop_of_iso
      ((moduleToHomotopyDerivedIso R (BlowupDiagramCoefficientObject R a)ᵒᵖ).app
        (ForgetEnrichment.of (Complex R)
          (ForgetEnrichment.to (Complex R) X.as).val.val)).symm
      (ForgetEnrichment.to (Complex R) X.as).property)

/-- 概要：指定条件への H⁰ 比較は充満。
方針：充満 dg 包含と全図式の充満比較の合成を使う。
規約：KST §3.1。使われ方：候補模型の完全忠実性。 -/
instance cartesianPerfectDiagramToDerivedFull (a : I → R) :
    (cartesianPerfectDiagramToDerived R a).Full := by
  unfold cartesianPerfectDiagramToDerived cartesianPerfectDiagramInclusion
  infer_instance

/-- 概要：指定条件への H⁰ 比較は忠実。
方針：充満 dg 包含と全図式の忠実比較の合成を使う。
規約：KST §3.1。使われ方：候補模型の完全忠実性。 -/
instance cartesianPerfectDiagramToDerivedFaithful (a : I → R) :
    (cartesianPerfectDiagramToDerived R a).Faithful := by
  unfold cartesianPerfectDiagramToDerived cartesianPerfectDiagramInclusion
  infer_instance

/-- 概要：全ての cartesian perfect 導来対象は射影的候補模型で表せる。
方針：標準半自由分解の擬同型に沿って同型不変な条件を移す。
規約：KST §3.1。使われ方：候補模型の H⁰ 比較の本質的全射性。 -/
instance cartesianPerfectDiagramToDerivedEssSurj (a : I → R) :
    (cartesianPerfectDiagramToDerived R a).EssSurj where
  mem_essImage X := by
    let F := finiteOverlapDGAlgebraDiagram R a
    let P := diagramModuleProjectiveResolution F X.obj.as.obj
    let e : (moduleToDerived R (BlowupDiagramCoefficientObject R a)ᵒᵖ).obj P.obj ≅ X.obj :=
      moduleDerivedIso R (BlowupDiagramCoefficientObject R a)ᵒᵖ P.π P.quasiIso
    let M := projectiveDiagramModuleRepresentative F X.obj.as.obj
    have hM : projectiveDiagramCartesianPerfect R a M :=
      (diagramCartesianPerfect R a).prop_of_iso e.symm X.property
    let N : CartesianPerfectDiagramDGModel R a := ⟨M, hM⟩
    refine ⟨(toHomotopy R (CartesianPerfectDiagramDGModel R a)).obj
      (ForgetEnrichment.of (Complex R) N), ⟨?_⟩⟩
    exact (diagramCartesianPerfect R a).ι.preimageIso
      ((moduleToHomotopyDerivedIso R (BlowupDiagramCoefficientObject R a)ᵒᵖ).app P.obj ≪≫ e)

/-- 概要：指定 cartesian perfect 模型の H⁰ 比較は圏同値。
方針：完全忠実性と標準分解による本質的全射性を束ねる。
規約：KST §3.1。使われ方：射影的候補模型の H⁰ の同定。 -/
instance cartesianPerfectDiagramToDerivedIsEquivalence (a : I → R) :
    (cartesianPerfectDiagramToDerived R a).IsEquivalence where

/-- 概要：指定 cartesian perfect dg 模型の H⁰ と主導来部分圏の同値。
方針：実際の構成済み比較関手を同値として読む。
規約：KST §3.1、層・dg 商・高次降下との比較は別に残す。
使われ方：全図式の導来 Hom を保つ候補模型の通常圏レベルの保証。 -/
def cartesianPerfectDiagramHomotopyEquivalence (a : I → R) :
    HomotopyCategory R (CartesianPerfectDiagramDGModel R a) ≌
      CartesianPerfectDerivedDiagramModules R a :=
  (cartesianPerfectDiagramToDerived R a).asEquivalence

end SerrePositivity.KST.DerivedBlowup

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite KST "Rem 2.5" (partial := component) "仮定：指定有限アフィンチャートの導来係数図式（Lean が強い）。結論：Cartesian な完全加群の局所 dg 図式と導来側の比較。全準連接加群の局所記述は範囲外（Lean が弱い）。"] _root_.SerrePositivity.KST.DerivedBlowup.cartesianPerfectDiagramToDerivedIsEquivalence
