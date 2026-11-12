module

public import SerrePositivity.KST.Spectra.SpectrumMappingAcyclic
public import SerrePositivity.KST.Spectra.SpectrumFibrationReplacement
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.PointedKanWhitehead

/-!
概要：BF 射の段ごとの全基点 π 同型は、全ての実際の豊穣 Hom への後合成でも π 同型。
方針：mapping path の BF 置換からの二つの全単射 RLP 射影と、源への厳密切断を使う。
規約：Hom 全体の単体写像について証明する。各段のホモトピー類の一致ではない。
使われ方：BF 1978 §2、HTT A.3.3。Sp の同値の検出と置換不変性。
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
open OmegaSpectrum

/-- mapping path の BF 置換から元の源への射影は各段で全単射 RLP。 -/
lemma retraction_rlp {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) (n : ℕ) :
    (MorphismProperty.monomorphisms SSet.{u}).rlp
      ((fibrationReplacementRetraction f).app n).right :=
  (MorphismProperty.monomorphisms SSet.{u}).rlp.comp_mem _ _
    (KanSequence.replacementStage (fibrationPath f) n).projection_rlp
    (KanSequence.mappingPathSource_rlp (sequenceHom f) n)

/-- 元の射が段ごとの π 同型なら、置換から標的への射影も各段で全単射 RLP。 -/
lemma projection_rlp {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y)
    (hf : ∀ n, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (f.app n).right) (n : ℕ) :
    (MorphismProperty.monomorphisms SSet.{u}).rlp
      ((fibrationReplacementProjection f).app n).right :=
  (MorphismProperty.monomorphisms SSet.{u}).rlp.comp_mem _ _
    (KanSequence.replacementStage (fibrationPath f) n).projection_rlp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mappingPathProjection_rlp_of_piIsomorphism (f.app n) (hf n))

/-- BF の段ごとの π 同型は実際のスペクトル Hom 全体でも全基点 π 同型。 -/
lemma post_piIsomorphism_of_levelwise (A : OmegaSpectrum.{u}) {X Y : OmegaSpectrum.{u}}
    (f : X ⟶ Y) (hf : ∀ n, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (f.app n).right) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (post A f) := by
  have hr := post_piIsomorphism A (fibrationReplacementRetraction f) (retraction_rlp f)
  have hu : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (post A (fibrationReplacementUnit f)) := by
    apply _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism.of_comp (g := post A (fibrationReplacementRetraction f)) _ hr
    have he : post A (fibrationReplacementUnit f) ≫
        post A (fibrationReplacementRetraction f) = 𝟙 _ := by
      exact (Functor.map_comp _ _ _).symm.trans
        (by
          rw [fibrationReplacementUnit_retraction]
          exact ((SimplicialCategory.sHomFunctor OmegaSpectrum.{u}).obj
            (Opposite.op A)).map_id X)
    rw [he]
    exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism.id _
  have hq := post_piIsomorphism A (fibrationReplacementProjection f) (projection_rlp f hf)
  have h := hu.comp hq
  have he : post A (fibrationReplacementUnit f) ≫
      post A (fibrationReplacementProjection f) = post A f := by
    exact (Functor.map_comp _ _ _).symm.trans (by rw [fibrationReplacement_fac])
  rw [he] at h
  exact h

end
end SerrePositivity.KST.Spectra.SpectrumMappingAcyclic
