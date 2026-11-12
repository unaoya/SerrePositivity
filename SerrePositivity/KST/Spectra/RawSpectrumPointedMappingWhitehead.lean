module

public import SerrePositivity.KST.Spectra.SpectrumLevelwiseInversePostInterval
public import SerrePositivity.KST.Spectra.KanEquivalenceBridge

/-!
概要：BF 射の段ごとの π 同型を、元の点つき整合 Hom の後合成へ移す。
方針：同じ選択済み逆射の左右の全 Hom 区間を実ホモトピー逆として使う。
規約：豊穣 Hom との定義上の一致を仮定しない。使われ方：元の全 Hom 比較の同型性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping

/-- 段ごとの π 同型の後合成は、元の点つき全 Hom の実ホモトピー同値。 -/
lemma pointedPost_homotopyEquivalence_of_levelwise (A : OmegaSpectrum.{u})
    {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) (hf : ∀ n, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (f.app n).right) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (pointedPost A (OmegaSpectrum.sequenceHom f)).right := by
  refine ⟨(pointedPost A (OmegaSpectrum.sequenceHom
    (OmegaSpectrum.levelwiseInverse f hf))).right, ?_, ?_⟩
  · exact ⟨(OmegaSpectrum.levelwiseInverse_post_left_interval A f hf).homotopy⟩
  · exact ⟨(OmegaSpectrum.levelwiseInverse_post_right_interval A f hf).homotopy⟩

/-- 同じ後合成の元の点つき全 Hom 上の全基点 π 同型性。 -/
lemma pointedPost_piIsomorphism_of_levelwise (A : OmegaSpectrum.{u})
    {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) (hf : ∀ n, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (f.app n).right) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (pointedPost A (OmegaSpectrum.sequenceHom f)).right :=
  kanPiIsomorphism_of_qCatEquivalence _
    (pointedPost_homotopyEquivalence_of_levelwise A f hf).isQCatEquivalence

end SerrePositivity.KST.Spectra.RawSpectrumMapping
