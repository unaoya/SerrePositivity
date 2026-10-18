module

public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapTwistCartesian
public import SerrePositivity.KST.DerivedBlowup.DiagramCartesianEnhancement

/-!
概要：KST Def3.1・Lemma3.6 の全整数捻りを既存の cartesian perfect dg 候補内で実現する。
方針：実際の O(m) の標準射影分解に、証明した cartesian perfect 性を移す。
規約：全次数 Hom を持つ既存の大域模型の対象。層との比較は別工程。
使われ方：捻り対象の生成系と半直交分解。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory DifferentialGraded

variable (R : Type u) [CommRing R] {I : Type} [DecidableEq I]

/-- 概要：全整数 O(m) の既存の cartesian perfect dg 模型内での指定対象。
方針：標準射影分解の増大擬同型に沿って同型不変な対象条件を移す。
規約：KST Def3.1・Lemma3.6。使われ方：大域の捻りの実際の dg 代表。 -/
def blowupTwistDGObject (a : I → R) (m : ℤ) : CartesianPerfectDiagramDGModel R a := by
  let F := finiteOverlapDGAlgebraDiagram R a
  let P := diagramModuleProjectiveResolution F (finiteOverlapTwistModule R a m)
  let M := projectiveDiagramModuleRepresentative F (finiteOverlapTwistModule R a m)
  have e : (moduleToDerived R (BlowupDiagramCoefficientObject R a)ᵒᵖ).obj P.obj ≅
      derivedFiniteOverlapTwistModule R a m :=
    moduleDerivedIso R (BlowupDiagramCoefficientObject R a)ᵒᵖ P.π P.quasiIso
  have hM : projectiveDiagramCartesianPerfect R a M :=
    (diagramCartesianPerfect R a).prop_of_iso e.symm
      (derivedFiniteOverlapTwistModule_cartesianPerfect R a m)
  exact ⟨M, hM⟩

/-- 概要：指定 dg 捻り対象の H⁰ 比較像は実際の O(m) の主導来像と同型。
方針：標準射影分解の H⁰ 計算同型と増大射を接続する。
規約：KST Def3.1・Lemma3.6。使われ方：dg 模型と主導来計算の接続。 -/
def blowupTwistDGObjectDerivedIso (a : I → R) (m : ℤ) :
    (cartesianPerfectDiagramToDerived R a).obj
        ((toHomotopy R (CartesianPerfectDiagramDGModel R a)).obj
          (ForgetEnrichment.of (Complex R) (blowupTwistDGObject R a m))) ≅
      (⟨derivedFiniteOverlapTwistModule R a m,
        derivedFiniteOverlapTwistModule_cartesianPerfect R a m⟩ :
        CartesianPerfectDerivedDiagramModules R a) := by
  let F := finiteOverlapDGAlgebraDiagram R a
  let P := diagramModuleProjectiveResolution F (finiteOverlapTwistModule R a m)
  exact (diagramCartesianPerfect R a).ι.preimageIso
    ((moduleToHomotopyDerivedIso R (BlowupDiagramCoefficientObject R a)ᵒᵖ).app P.obj ≪≫
      moduleDerivedIso R (BlowupDiagramCoefficientObject R a)ᵒᵖ P.π P.quasiIso)

end SerrePositivity.KST.DerivedBlowup
