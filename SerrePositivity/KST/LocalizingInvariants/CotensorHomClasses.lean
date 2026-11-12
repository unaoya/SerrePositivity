module

public import SerrePositivity.KST.Spectra.SpectrumCotensorMappingEquivalence
public import SerrePositivity.KST.Spectra.RawSpectrumCotensorSourceNaturality
public import SerrePositivity.KST.Spectra.CircleMappingComponents

/-!
概要：Kan 円 cotensor への BF Hom の成分を、元の写像空間の基本群と比較する。
方針：cotensor 射影と源交換の実比較を使い、BF 源の前合成との自然性を保つ。
規約：固定標的の主張であり、loop 関手の完全忠実性は使わない。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.Spectra SerrePositivity.KST.Spectra.OmegaSpectrum
namespace SerrePositivity.KST.LocalizingInvariants.CotensorClasses

abbrev target (Z : OmegaSpectrum.{u}) := cotensor CirclePower.space.{u} Z
abbrev classes (A Z : OmegaSpectrum.{u}) := π₀ (mappingSpace A (target Z))
abbrev fundamental (A Z : OmegaSpectrum.{u}) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (RawSpectrumMapping.pointedSpace A Z.toKanSequence).right 0
    (RawSpectrumMapping.pointedSpace A Z.toKanSequence).basepoint

/-- 元の点つき cotensor 比較。 -/
def comparison (A Z : OmegaSpectrum.{u}) :
    RawSpectrumMapping.pointedSpace A (target Z).toKanSequence ⟶
      (ihom CirclePower.space.{u}).obj (RawSpectrumMapping.pointedSpace A Z.toKanSequence) :=
  RawSpectrumMapping.pointedPost A (cotensorProjection CirclePower.space Z) ≫
    RawSpectrumMapping.cotensorComparison A Z.toKanSequence CirclePower.space

lemma comparison_hom (A Z : OmegaSpectrum.{u}) :
    (comparison A Z).right = (cotensorMappingEquivalence A Z CirclePower.space.{u}).hom := rfl

/-- 実 Hom の成分と元の全 Hom の基本群の同値。 -/
def equiv (A Z : OmegaSpectrum.{u}) : classes A Z ≃ fundamental A Z :=
  (Equiv.ofBijective (mapπ₀ (comparison A Z).right) (by
    rw [comparison_hom]
    have h := cotensorMappingComparison_homotopyEquivalence A Z CirclePower.space
    exact h.mapPiZero_bijective)).trans
    (CirclePower.componentEquiv (RawSpectrumMapping.pointedSpace A Z.toKanSequence))

/-- 源の BF 射の前合成との厳密な可換性。 -/
lemma comparison_pre {A B : OmegaSpectrum.{u}} (f : A ⟶ B) (Z : OmegaSpectrum.{u}) :
    RawSpectrumMapping.pointedPre f (target Z).toKanSequence ≫ comparison A Z =
      comparison B Z ≫ (ihom CirclePower.space.{u}).map
        (RawSpectrumMapping.pointedPre f Z.toKanSequence) := by
  unfold comparison
  rw [← Category.assoc, ← RawSpectrumMapping.pointedPre_post, Category.assoc,
    RawSpectrumMapping.cotensorComparison_pre_source, Category.assoc]

def pre {A B : OmegaSpectrum.{u}} (f : A ⟶ B) (Z : OmegaSpectrum.{u}) :
    classes B Z → classes A Z :=
  mapπ₀ (RawSpectrumMapping.pointedPre f (target Z).toKanSequence).right

def fundamentalPre {A B : OmegaSpectrum.{u}} (f : A ⟶ B) (Z : OmegaSpectrum.{u}) :
    fundamental B Z →* fundamental A Z :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (RawSpectrumMapping.pointedPre f Z.toKanSequence).right
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint _)

/-- 成分比較は前合成を基本群の準同型へ移す。 -/
lemma equiv_pre {A B : OmegaSpectrum.{u}} (f : A ⟶ B) (Z : OmegaSpectrum.{u})
    (a : classes B Z) : equiv A Z (pre f Z a) = fundamentalPre f Z (equiv B Z a) := by
  change CirclePower.componentEquiv (RawSpectrumMapping.pointedSpace A Z.toKanSequence)
    (mapπ₀ (comparison A Z).right (pre f Z a)) = _
  have h := congrArg Under.Hom.right (comparison_pre f Z)
  change (RawSpectrumMapping.pointedPre f (target Z).toKanSequence).right ≫
    (comparison A Z).right = (comparison B Z).right ≫
      ((ihom CirclePower.space.{u}).map
        (RawSpectrumMapping.pointedPre f Z.toKanSequence)).right at h
  rw [pre, ← mapπ₀_comp_apply, h, mapπ₀_comp_apply]
  exact CirclePower.componentEquiv_natural (RawSpectrumMapping.pointedPre f Z.toKanSequence) _

def unit (A Z : OmegaSpectrum.{u}) : classes A Z := (equiv A Z).symm 1

def sum (A Z : OmegaSpectrum.{u}) (a b : classes A Z) : classes A Z :=
  (equiv A Z).symm (equiv A Z a * equiv A Z b)

lemma sum_unit (A Z : OmegaSpectrum.{u}) (a : classes A Z) : sum A Z a (unit A Z) = a := by
  simp only [sum, unit, Equiv.apply_symm_apply, mul_one, Equiv.symm_apply_apply]

lemma unit_sum (A Z : OmegaSpectrum.{u}) (a : classes A Z) : sum A Z (unit A Z) a = a := by
  simp only [sum, unit, Equiv.apply_symm_apply, one_mul, Equiv.symm_apply_apply]

lemma pre_sum {A B : OmegaSpectrum.{u}} (f : A ⟶ B) (Z : OmegaSpectrum.{u})
    (a b : classes B Z) : pre f Z (sum B Z a b) = sum A Z (pre f Z a) (pre f Z b) := by
  apply (equiv A Z).injective
  simp only [equiv_pre, sum, Equiv.apply_symm_apply, map_mul]

end SerrePositivity.KST.LocalizingInvariants.CotensorClasses
