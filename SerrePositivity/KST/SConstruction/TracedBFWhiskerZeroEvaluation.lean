module
public import SerrePositivity.KST.SConstruction.TracedBFCompositionZeroEvaluation
public import SerrePositivity.KST.SConstruction.SpectrumWhiskerEvaluationConstants

/-! # 元の両 BF whisker の零段は全区間で定数
概要：元の後二射・前二射の BF 比較の零段定数性を、固定因子との合成へ移す。
方針：全 Hom の固定因子合成の評価式と、元の BF 比較辺の全零段固定式を使う。
規約：実辺全体の定数性を証明し、成分だけの主張にはしない。
使われ方：元の二三角形の三つの零段境界を定数辺として回収する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet Spectra
open scoped Simplicial
local instance tracedWhiskerZeroSpectrumSimplicialCategory :
    SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory
variable {I : Type u} [SmallCategory I] (F : I ⥤ StableModel.{u})
  {w x y z : I} (f : w ⟶ x) (g : x ⟶ y) (h : y ⟶ z)

/-- 元の第一 BF whisker の全零段は、固定第一因子との同じ合成頂点で定数。 -/
lemma monicKTracedNativeFirstWhisker_zero_constant :
    ∃ v, SSet.yonedaEquiv.symm (monicKTracedNativeFirstWhisker F f g h).edge ≫
        OmegaSpectrum.evaluation (kOmegaSpectrum (F.obj w)) (kOmegaSpectrum (F.obj z)) 0 =
      SSet.const v := by
  exact spectrumComparisonLeftWhisker_constant
    (monicKTracedSpectrumMap F f) (monicKTracedSpectrumMap F g) (monicKTracedSpectrumMap F h)
    (monicKTracedSpectrumMap F (g ≫ h)) (monicKTracedSpectrumCompositionEdge F g h) 0
    ⟨_, monicKTracedSpectrumCompositionEdge_zero F g h⟩

/-- 元の第二 BF whisker の全零段も、固定最終因子との同じ合成頂点で定数。 -/
lemma monicKTracedNativeSecondWhisker_zero_constant :
    ∃ v, SSet.yonedaEquiv.symm (monicKTracedNativeSecondWhisker F f g h).edge ≫
        OmegaSpectrum.evaluation (kOmegaSpectrum (F.obj w)) (kOmegaSpectrum (F.obj z)) 0 =
      SSet.const v := by
  exact spectrumComparisonRightWhisker_constant
    (monicKTracedSpectrumMap F f) (monicKTracedSpectrumMap F g) (monicKTracedSpectrumMap F h)
    (monicKTracedSpectrumMap F (f ≫ g)) (monicKTracedSpectrumCompositionEdge F f g) 0
    ⟨_, monicKTracedSpectrumCompositionEdge_zero F f g⟩

/-- 元の指定左 BF 比較辺の全零段は、合成入力の元の同じ定数区間。 -/
lemma monicKTracedNativeTriplePrescribedEdge_zero_constant :
    ∃ v, SSet.yonedaEquiv.symm (monicKTracedNativeTriplePrescribedEdge F f g h).edge ≫
        OmegaSpectrum.evaluation (kOmegaSpectrum (F.obj w)) (kOmegaSpectrum (F.obj z)) 0 =
      SSet.const v := by
  rw [monicKTracedNativeTriplePrescribedEdge_edge, monicKTracedSpectrumCompositionEdge_zero]
  exact ⟨_, rfl⟩

end SerrePositivity.KST.SConstruction
