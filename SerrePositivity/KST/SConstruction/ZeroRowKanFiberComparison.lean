module
public import SerrePositivity.KST.SConstruction.ZeroRowPointedFiberComparison
public import SerrePositivity.KST.SConstruction.PointedKanStrictExtension

/-! # 元の零行の Kan 模型から既存の fiber への全基点比較
概要：零段の任意の基点を用いた零行の Kan 模型は既存の path homotopy fiber と全基点 π_* 同型。
方針：元の零行の点つき射を Kan 単位に沿って厳密に延長し、局所化同型性を移す。
規約：既存の fiber を別の Kan 模型へ置換しない。使われ方：前段と fiber の共通 Kan 比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open Spectra
open scoped Simplicial

/-- 元の点つき零行の Kan 模型から既存の path homotopy fiber への厳密な延長。 -/
def zeroRowKanFiberComparison (r : ℕ) (X : StableModel.{u})
    (b : ((iteratedSRealizationDiagram r X).obj (Opposite.op ⦋0⦌)) _⦋0⦌) :
    PointedKanReplacement.obj (zeroRowPointedModel r X b) ⟶ iteratedPathHomotopyFiber r X :=
  pointedKanStrictExtension (zeroRowPointedFiberComparison r X b)

/-- Kan 比較は元の零行の fiber 射を厳密に回収する。 -/
lemma zeroRowKanFiberComparison_fac (r : ℕ) (X : StableModel.{u})
    (b : ((iteratedSRealizationDiagram r X).obj (Opposite.op ⦋0⦌)) _⦋0⦌) :
    PointedKanReplacement.unit.app (zeroRowPointedModel r X b) ≫
      zeroRowKanFiberComparison r X b = zeroRowPointedFiberComparison r X b :=
  pointedKanStrictExtension_fac _

/-- 元の零行の Kan 模型と既存の path homotopy fiber の比較は正の全反復で全基点 π_* 同型。 -/
lemma zeroRowKanFiberComparison_piIsomorphism (r : ℕ) (X : StableModel.{u})
    (b : ((iteratedSRealizationDiagram (r + 1) X).obj (Opposite.op ⦋0⦌)) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (zeroRowKanFiberComparison (r + 1) X b).right :=
  pointedKanStrictExtension_piIsomorphism (zeroRowPointedFiberComparison (r + 1) X b)
    (zeroRowPointedFiberComparison_localized_isIso r X b)

end SerrePositivity.KST.SConstruction
