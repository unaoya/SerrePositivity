module

public import SerrePositivity.KST.Spectra.Limits.SpectrumHomHornFamilies
public import SerrePositivity.KST.Spectra.Limits.SpectrumPullbackCones

/-!
概要：段ごとの fibration は実際のスペクトル Hom の fibration を与え、Sp の引き戻しを検証する。
方針：各段の相対充填による整合族を L9 の全切断写像空間へ束ねる。
規約：段ごとの fibration 以外の条件や比較同値を追加しない。
使われ方：BF 1978 §2、HTT A.3.3、HTT 4.2.4.1 の Sp の実際の ∞ 引き戻し。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open SerrePositivity.KST.Spectra
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
local instance spectrumHomFibrations_simplicialCategory :
    SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory
local instance spectrumHomFibrations_locallyKan (X Y : OmegaSpectrum.{u}) :
    KanComplex (SimplicialCategory.sHom X Y) := OmegaSpectrum.mappingSpace_kanComplex X Y

/-- 概要：段ごとの fibration による実際のスペクトル Hom の後合成はホーンを持ち上げる。
方針：各段で整合した持ち上げの族を全切断写像空間の普遍性へ渡す。
規約：ホーン上の元の射と底への合成を厳密に保つ。
使われ方：Sp の写像単体集合の fibration の対角射の構成。 -/
lemma spectrumHom_hornLift (X : OmegaSpectrum.{u}) {Y Z : OmegaSpectrum.{u}}
    (p : Y ⟶ Z) [∀ n, Fibration (p.app n).right]
    {T U : SSet.{u}} (j : T ⟶ U) (hj : J j)
    (a : T ⟶ OmegaSpectrum.mappingSpace X Y) (b : U ⟶ OmegaSpectrum.mappingSpace X Z)
    (h : a ≫ ((SimplicialCategory.sHomFunctor OmegaSpectrum.{u}).obj (Opposite.op X)).map p =
      j ≫ b) :
    ∃ l : U ⟶ OmegaSpectrum.mappingSpace X Y, j ≫ l = a ∧
      l ≫ ((SimplicialCategory.sHomFunctor OmegaSpectrum.{u}).obj (Opposite.op X)).map p = b := by
  obtain ⟨f, ha, hb, hf⟩ := spectrumHom_hornFamily X p j hj a b h
  let l := TruncatedMapping.familyLift (fun n ↦ (X.level n).space)
    (fun n ↦ (Y.level n).space) (fun n ↦ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)
    X.sigma (OmegaSpectrum.mappingStep X Y) f hf
  have hl (n : ℕ) : l ≫ OmegaSpectrum.evaluation X Y n = f n :=
    TruncatedMapping.familyLift_evaluation _ _ _ _ _ f hf n
  refine ⟨l, ?_, ?_⟩
  · apply OmegaSpectrum.mapping_hom_ext (X := X) (Y := Y)
    intro n
    rw [Category.assoc, hl]
    exact ha n
  · apply OmegaSpectrum.mapping_hom_ext (X := X) (Y := Z)
    intro n
    rw [Category.assoc, spectrumHomMap_evaluation X (Y := Y) (Z := Z) p n,
      ← Category.assoc, hl]
    exact hb n

/-- 概要：各段が Kan fibration のスペクトル射は全ての実際の豊穣 Hom で Kan fibration を与える。
方針：ホーンの RLP を各段の相対充填と全切断の普遍性で直接検証する。
規約：Ω 条件を追加で使わず、源の単射な構造射は L9 の対象の定義から得る。
使われ方：HTT 4.2.4.1 の Sp の引き戻しと塔の Hom の fibration 条件。 -/
instance spectrumHomMap_fibration (X : OmegaSpectrum.{u}) {Y Z : OmegaSpectrum.{u}}
    (p : Y ⟶ Z) [∀ n, Fibration (p.app n).right] :
    Fibration (((SimplicialCategory.sHomFunctor OmegaSpectrum.{u}).obj (Opposite.op X)).map p) := by
  rw [SSet.modelCategoryQuillen.fibration_iff]
  intro T U j hj
  constructor
  intro a b sq
  obtain ⟨l, hl, hp⟩ := spectrumHom_hornLift X p j hj a b sq.w
  exact ⟨⟨{ l := l, fac_left := hl, fac_right := hp }⟩⟩

/-- 概要：L9 の一脚が各段で fibration のスペクトルの引き戻しは Sp の実際の極限錐。
方針：実際の豊穣 Hom の極限性と左脚の fibration 性を cospan の比較定理へ渡す。
規約：左脚 f だけに段ごとの fibration 性を要求し、右脚 g は任意。
使われ方：HTT 4.2.4.1 の双対、BF 1978 §2、HA §1.4.2、γ3c の Sp の引き戻し。 -/
lemma spectrumPullbackInfinityCone_isLimit {E X B : OmegaSpectrum.{u}}
    (f : E ⟶ B) (g : X ⟶ B) [∀ n, Fibration (f.app n).right] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (spectrumPullbackInfinityCone f g) := by
  have : ∀ Z : OmegaSpectrum.{u}, Fibration
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram (spectrumPullbackDiagram f g) Z).map
        (AsSmall.up.map WalkingCospan.Hom.inl)) := fun Z ↦ by
    change Fibration
      (((SimplicialCategory.sHomFunctor OmegaSpectrum.{u}).obj (Opposite.op Z)).map f)
    exact spectrumHomMap_fibration Z f
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.strictCoherentCone_isLimit_of_cospan_homLimit (spectrumPullbackCone f g)
    (spectrumPullbackCone_hom_isLimit f g)

end
end SerrePositivity.InfinityCategories.HomotopyLimits
