module

public import SerrePositivity.KST.Spectra.SpectrumMappingAcyclicFamily
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.MonoRightHomotopyEquivalence

/-!
概要：段ごとの全単射 RLP は、実際のスペクトル写像空間への後合成でも保存される。
方針：単射パラメータでの整合充填の族を全切断の普遍性で束ねる。
規約：実際の豊穣 Hom の射についての主張。段ごとの成分の等式に弱めない。
使われ方：BF 1978 §2、HTT A.3.3。BF 弱同値と Sp の同値の比較。
-/

@[expose] public section
universe u
open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra.SpectrumMappingAcyclic
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
local instance : SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory
local instance (X Y : OmegaSpectrum.{u}) : KanComplex (SimplicialCategory.sHom X Y) :=
  OmegaSpectrum.mappingSpace_kanComplex X Y

/-- 実際の豊穣 Hom の後合成の射。 -/
abbrev post (A : OmegaSpectrum.{u}) {Y Z : OmegaSpectrum.{u}} (p : Y ⟶ Z) :
    OmegaSpectrum.mappingSpace A Y ⟶ OmegaSpectrum.mappingSpace A Z :=
  ((SimplicialCategory.sHomFunctor OmegaSpectrum.{u}).obj (Opposite.op A)).map p

/-- 段ごとに全単射 RLP を持つ射は豊穣 Hom でも全単射 RLP を持つ。 -/
lemma post_rlp (A : OmegaSpectrum.{u}) {Y Z : OmegaSpectrum.{u}} (p : Y ⟶ Z)
    (hp : ∀ n, (MorphismProperty.monomorphisms SSet.{u}).rlp (p.app n).right) :
    (MorphismProperty.monomorphisms SSet.{u}).rlp (post A p) := by
  intro T U j hj
  let : Mono j := hj
  constructor
  intro a b sq
  obtain ⟨f, ha, hb, hf⟩ := monoFamily A p hp j a b sq.w
  let l := TruncatedMapping.familyLift (fun n ↦ (A.level n).space)
    (fun n ↦ (Y.level n).space) (fun n ↦ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (A.level n).space)
    A.sigma (OmegaSpectrum.mappingStep A Y) f hf
  have hl (n : ℕ) : l ≫ OmegaSpectrum.evaluation A Y n = f n :=
    TruncatedMapping.familyLift_evaluation _ _ _ _ _ f hf n
  refine ⟨⟨{ l := l, fac_left := ?_, fac_right := ?_ }⟩⟩
  · apply OmegaSpectrum.mapping_hom_ext
    intro n
    rw [Category.assoc, hl]
    exact ha n
  · apply OmegaSpectrum.mapping_hom_ext
    intro n
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumHomMap_evaluation A p n, ← Category.assoc, hl]
    exact hb n

/-- 全単射 RLP を持つ後合成は全基点・全次数で π 同型。 -/
lemma post_piIsomorphism (A : OmegaSpectrum.{u}) {Y Z : OmegaSpectrum.{u}} (p : Y ⟶ Z)
    (hp : ∀ n, (MorphismProperty.monomorphisms SSet.{u}).rlp (p.app n).right) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (post A p) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.kanPiIsomorphism_of_monoRight _ (post_rlp A p hp)

end
end SerrePositivity.KST.Spectra.SpectrumMappingAcyclic
