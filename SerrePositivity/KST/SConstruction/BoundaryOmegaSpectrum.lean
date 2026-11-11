module
public import SerrePositivity.KST.SConstruction.KanAssemblyEquivalence
public import SerrePositivity.KST.Spectra.CofibrantOmegaSequence

/-! # 元の反復境界商の BF Ω スペクトル
概要：r+1 重 S の元の境界商を段とする列は Ω 条件を満たし、単射置換後に BF 模型になる。
方針：元の構造射の随伴の π 同型と L9 の列の単射置換を使う。
規約：段は r+1 重 S のまま。K の次数を戻す loop と負次数消滅は後続工程。
使われ方：連結 K スペクトルの構成への入力。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open Spectra

/-- 元の境界商の列の全ての構造射は全基点の Ω 条件を満たす。 -/
lemma boundaryKanSequence_omegaCondition (X : StableModel.{u}) :
    (boundaryKanSequence X).OmegaCondition := by
  intro r
  change _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism
    ((_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv _ _) (boundaryKanAssemblySigma r X)).right
  rw [boundaryKanAssemblySigma_adjoint]
  exact boundaryKanAssemblyAdjoint_piIsomorphism r X

/-- 既存の単射置換した境界商の列も同じ全基点 Ω 条件を満たす。 -/
lemma monicBoundaryKanSequence_omegaCondition (X : StableModel.{u}) :
    (monicBoundaryKanSequence X).OmegaCondition :=
  KanSequence.cofibrantReplacement_omegaCondition _ (boundaryKanSequence_omegaCondition X)

/-- 元の境界商の列の単射置換をそのまま BF Ω スペクトルに束ねる。 -/
def boundaryOmegaSpectrum (X : StableModel.{u}) : OmegaSpectrum.{u} :=
  (monicBoundaryKanSequence X).toOmegaSpectrum (fun _ => inferInstance)
    (monicBoundaryKanSequence_omegaCondition X)

end SerrePositivity.KST.SConstruction
