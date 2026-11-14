module

public import SerrePositivity.KST.Spectra.RawSpectrumMappingLaws
public import SerrePositivity.KST.Spectra.RawSpectrumMappingFamily
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.DiagramComparisons.RelativePointedHomLifting
public import SerrePositivity.KST.Spectra.PushoutProductMonomorphism

/-!
概要：段ごとの全単射 RLP に沿って持ち上がるスペクトル写像の整合族。
方針：任意の Kan 列への相対充填を特殊化し、BF の後合成との厳密な一致で移す。
規約：L9 の実際の各段評価と厳密な構造条件を保持する。
使われ方：BF 1978 §2、HTT A.3.3、Sp の豊穣 Hom 写像の fibration 性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.Spectra.SpectrumMappingAcyclic

noncomputable section
local instance simplicialCategory :
    SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory

/-- 概要：段ごとの全単射 RLP に沿う Hom の単射パラメータは各段で整合する族へ持ち上がる。
方針：後合成の初段の持ち上げから始め、構造射の単射性による相対持ち上げを反復する。
規約：単射パラメータ上と底への合成の等式、構造射の整合条件を全て保持する。
使われ方：L9 の実際の Hom 空間の fibration の対角射を構成する。 -/
lemma monoFamily (X : OmegaSpectrum.{u}) {Y Z : OmegaSpectrum.{u}}
    (p : Y ⟶ Z) (hp : ∀ n, (MorphismProperty.monomorphisms SSet.{u}).rlp (p.app n).right)
    {T U : SSet.{u}} (j : T ⟶ U) [Mono j]
    (a : T ⟶ OmegaSpectrum.mappingSpace X Y) (b : U ⟶ OmegaSpectrum.mappingSpace X Z)
    (h : a ≫ ((SimplicialCategory.sHomFunctor OmegaSpectrum.{u}).obj (Opposite.op X)).map p =
      j ≫ b) :
    ∃ l : ∀ n, U ⟶ (PointedObject.basedHom (X.level n).space (Y.level n).space).right,
      (∀ n, j ≫ l n = a ≫ OmegaSpectrum.evaluation X Y n) ∧
      (∀ n, l n ≫ (PointedObject.basedHomMap (X.level n).space (p.app n)).right =
        b ≫ OmegaSpectrum.evaluation X Z n) ∧
      (∀ n, l (n + 1) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (X.sigma n) (Y.level (n + 1)).space =
        l n ≫ OmegaSpectrum.mappingStep X Y n) := by
  let q : KanSequence.Hom Y.toKanSequence Z.toKanSequence := ⟨p.app, p.comm⟩
  have hq : a ≫ RawSpectrumMapping.post X q = j ≫ b := by
    rw [RawSpectrumMapping.post_spectrum]
    exact h
  exact RawSpectrumMapping.monoFamily X q hp j a b hq

end
end SerrePositivity.KST.Spectra.SpectrumMappingAcyclic
