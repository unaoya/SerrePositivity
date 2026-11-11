module

public import SerrePositivity.KST.LocalizingInvariants.CotensorMultiplication
public import SerrePositivity.KST.Spectra.TailCotensorComparison
public import SerrePositivity.KST.Spectra.OriginalLoopModelMap

/-!
概要：任意の元の BF スペクトルに、両軸で単位となる積の射を構成する。
方針：既存の対象ごとの loop 比較と、その実写像空間での逆を使って演算を戻す。
規約：loop の関手同型や Sp の安定性を仮定しない。使われ方：切断付き列の積比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open SerrePositivity.KST.Spectra SerrePositivity.KST.Spectra.OmegaSpectrum
open SpectrumMappingAcyclic
namespace SerrePositivity.KST.LocalizingInvariants.Multiplication

variable (X : OmegaSpectrum.{u})

/-- 元の対象から一段先の Kan 円 cotensor への実際の比較。 -/
def comparison : X ⟶ CotensorClasses.target (tail X) :=
  originalLoopModelMap X ≫ tailCotensorComparison CirclePower.space X

lemma comparison_levelwise (n : ℕ) : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism ((comparison X).app n).right :=
  (originalLoopModelMap_levelwise X n).comp
    (tailCotensorComparison_levelwise CirclePower.space X n)

def inverse : CotensorClasses.target (tail X) ⟶ X :=
  Classical.choose (exists_componentInverse (comparison X) (comparison_levelwise X))

lemma comparison_inverse : component (comparison X ≫ inverse X) = component (𝟙 X) :=
  (Classical.choose_spec (exists_componentInverse (comparison X) (comparison_levelwise X))).1

/-- 任意の BF 対象の二項積から元の対象への、両軸に単位を持つ実射。 -/
def map : Binary.obj X X ⟶ X :=
  CotensorClasses.add (Z := tail X) (Binary.fst X X ≫ comparison X)
    (Binary.snd X X ≫ comparison X) ≫ inverse X

lemma left_component : component (Binary.inl X X ≫ map X) = component (𝟙 X) := by
  have h := CotensorClasses.component_pre_add (Binary.inl X X)
    (Binary.fst X X ≫ comparison X) (Binary.snd X X ≫ comparison X)
  have hc : component (Binary.inl X X ≫ CotensorClasses.add
      (Binary.fst X X ≫ comparison X) (Binary.snd X X ≫ comparison X)) =
      component (comparison X) := by
    simpa only [Binary.inl_fst_assoc, Binary.inl_snd_assoc, Category.id_comp, zero_comp,
      CotensorClasses.component_add_zero] using h
  have hp := congrArg (mapπ₀ (post X (inverse X))) hc
  simp only [post_component] at hp
  simpa only [map, Category.assoc] using hp.trans (comparison_inverse X)

lemma right_component : component (Binary.inr X X ≫ map X) = component (𝟙 X) := by
  have h := CotensorClasses.component_pre_add (Binary.inr X X)
    (Binary.fst X X ≫ comparison X) (Binary.snd X X ≫ comparison X)
  have hc : component (Binary.inr X X ≫ CotensorClasses.add
      (Binary.fst X X ≫ comparison X) (Binary.snd X X ≫ comparison X)) =
      component (comparison X) := by
    simpa only [Binary.inr_fst_assoc, Binary.inr_snd_assoc, Category.id_comp, zero_comp,
      CotensorClasses.component_zero_add] using h
  have hp := congrArg (mapπ₀ (post X (inverse X))) hc
  simp only [post_component] at hp
  simpa only [map, Category.assoc] using hp.trans (comparison_inverse X)

lemma left_hom : SpectrumHo.hom (Binary.inl X X) ≫ SpectrumHo.hom (map X) =
    𝟙 (SpectrumHo.obj X) := by
  rw [← SpectrumHo.hom_comp]
  exact (SpectrumHo.hom_eq_of_component_eq _ _ (left_component X)).trans (SpectrumHo.hom_id X)

lemma right_hom : SpectrumHo.hom (Binary.inr X X) ≫ SpectrumHo.hom (map X) =
    𝟙 (SpectrumHo.obj X) := by
  rw [← SpectrumHo.hom_comp]
  exact (SpectrumHo.hom_eq_of_component_eq _ _ (right_component X)).trans (SpectrumHo.hom_id X)

end SerrePositivity.KST.LocalizingInvariants.Multiplication
