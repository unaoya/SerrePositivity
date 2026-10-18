module

public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapStructureModule
public import SerrePositivity.KST.DerivedBlowup.DiagramCartesianEnhancement

/-!
概要：KST Def3.1・Lemma3.6 の構造加群を既存の cartesian perfect dg 候補内で実現する。
方針：構成済み構造図式加群の標準射影分解に同型不変な対象条件を移す。
規約：大域 dg 模型を変更せず、実際の全次数 Hom を持つ対象を作る。
使われ方：構造加群と捻りによる生成系・半直交分解の入力。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory
open DifferentialGraded

variable (R : Type u) [CommRing R] {I : Type} [DecidableEq I]

/-- 概要：構造図式加群を表す既存の cartesian perfect dg 模型内の指定対象。
方針：標準射影分解を選び、その増大擬同型に沿って cartesian perfect 性を移す。
規約：KST Def3.1・Lemma3.6。使われ方：構造加群の実際の dg 代表。 -/
def blowupStructureDGObject (a : I → R) : CartesianPerfectDiagramDGModel R a := by
  let F := finiteOverlapDGAlgebraDiagram R a
  let P := diagramModuleProjectiveResolution F (blowupStructureModule R a)
  let M := projectiveDiagramModuleRepresentative F (blowupStructureModule R a)
  have e : (moduleToDerived R (BlowupDiagramCoefficientObject R a)ᵒᵖ).obj P.obj ≅
      derivedBlowupStructureModule R a :=
    moduleDerivedIso R (BlowupDiagramCoefficientObject R a)ᵒᵖ P.π P.quasiIso
  have hM : projectiveDiagramCartesianPerfect R a M :=
    (diagramCartesianPerfect R a).prop_of_iso e.symm
      (derivedBlowupStructureModule_cartesianPerfect R a)
  exact ⟨M, hM⟩

/-- 概要：指定 dg 構造対象の H⁰ 比較像は構成済み構造図式加群の導来像と同型。
方針：射影的模型の H⁰ 比較の標準計算同型と分解の増大を接続する。
規約：KST Def3.1・Lemma3.6。使われ方：dg 模型内の構造加群と主導来計算の接続。 -/
def blowupStructureDGObjectDerivedIso (a : I → R) :
    (cartesianPerfectDiagramToDerived R a).obj
        ((toHomotopy R (CartesianPerfectDiagramDGModel R a)).obj
          (ForgetEnrichment.of (Complex R) (blowupStructureDGObject R a))) ≅
      (⟨derivedBlowupStructureModule R a, derivedBlowupStructureModule_cartesianPerfect R a⟩ :
        CartesianPerfectDerivedDiagramModules R a) := by
  let F := finiteOverlapDGAlgebraDiagram R a
  let P := diagramModuleProjectiveResolution F (blowupStructureModule R a)
  exact (diagramCartesianPerfect R a).ι.preimageIso
    ((moduleToHomotopyDerivedIso R (BlowupDiagramCoefficientObject R a)ᵒᵖ).app P.obj ≪≫
      moduleDerivedIso R (BlowupDiagramCoefficientObject R a)ᵒᵖ P.π P.quasiIso)

end SerrePositivity.KST.DerivedBlowup
