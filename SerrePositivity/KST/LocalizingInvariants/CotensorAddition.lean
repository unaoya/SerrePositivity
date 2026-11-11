module

public import SerrePositivity.KST.LocalizingInvariants.CotensorHomClasses
public import SerrePositivity.KST.Spectra.SpectrumMappingComponents
public import SerrePositivity.KST.Spectra.SpectrumZeroMaps
public import SerrePositivity.KST.Spectra.LoopMappingOperations

/-!
概要：Kan 円 cotensor を標的とする二つの BF 射の和の代表。
方針：源に自然な基本群の演算を実 Hom の成分へ戻し、BF 射の代表を選ぶ。
規約：演算の法則は実写像空間の成分で述べる。使われ方：Sp の積分解の比較射。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.KST.Spectra SerrePositivity.KST.Spectra.OmegaSpectrum
open SpectrumMappingAcyclic
namespace SerrePositivity.KST.LocalizingInvariants.CotensorClasses

local instance additionSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

lemma pre_component {A B Z : OmegaSpectrum.{u}} (f : A ⟶ B) (g : B ⟶ target Z) :
    pre f Z (component g) = component (f ≫ g) := by
  change mapπ₀ (RawSpectrumMapping.pre f (target Z).toKanSequence) (component g) = _
  rw [RawSpectrumMapping.pre_spectrum]
  exact SpectrumMappingAcyclic.pre_component f g

/-- 元の BF 零射の頂点は、点つき全写像空間の基点。 -/
lemma zero_vertex (A B : OmegaSpectrum.{u}) :
    vertexOfHom (0 : A ⟶ B) = (RawSpectrumMapping.pointedSpace A B.toKanSequence).basepoint := by
  apply vertex_ext
  intro n
  rw [vertexOfHom_evaluation, zero_app, ← PointedMapping.familyVertex_eq_pointedHomVertex,
    PointedMapping.familyVertex_zero]
  exact (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (RawSpectrumMapping.pointedEvaluation A B.toKanSequence n)).symm

lemma circle_basepoint (M : PointedSimplicialSet.{u}) [KanComplex M.right] :
    CirclePower.componentEquiv M
      (π₀.mk (PointedSimplicialSet.basepoint
        (PointedObject.basedHom CirclePower.space.{u} M))) = 1 := by
  rw [← PointedMapping.familyVertex_zero CirclePower.space M,
    CirclePower.componentEquiv_familyVertex]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (0 : CirclePower.space.{u} ⟶ M).right
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint _) CirclePower.generator = 1
  simp only [PointedObject.zero_right, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedConstant_eq_const]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.map_const 1 _ CirclePower.generator

lemma equiv_zero (A Z : OmegaSpectrum.{u}) : equiv A Z (component (0 : A ⟶ target Z)) = 1 := by
  change CirclePower.componentEquiv (RawSpectrumMapping.pointedSpace A Z.toKanSequence)
    (mapπ₀ (comparison A Z).right (π₀.mk (vertexOfHom (0 : A ⟶ target Z)))) = 1
  rw [mapπ₀_mk, zero_vertex]
  have hb := _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (comparison A Z)
  exact (congrArg (fun v ↦ CirclePower.componentEquiv
    (RawSpectrumMapping.pointedSpace A Z.toKanSequence) (π₀.mk v)) hb).trans (circle_basepoint _)

lemma unit_eq_zero (A Z : OmegaSpectrum.{u}) : unit A Z = component (0 : A ⟶ target Z) := by
  apply (equiv A Z).injective
  rw [unit, Equiv.apply_symm_apply, equiv_zero]

lemma exists_representative {A Z : OmegaSpectrum.{u}} (a : classes A Z) :
    ∃ f : A ⟶ target Z, component f = a := by
  obtain ⟨v, rfl⟩ := π₀.mk_surjective a
  exact ⟨homOfVertex v, congrArg π₀.mk (vertexOfHom_homOfVertex v)⟩

/-- 二射の成分の和を表す元の BF 射。 -/
def add {A Z : OmegaSpectrum.{u}} (f g : A ⟶ target Z) : A ⟶ target Z :=
  Classical.choose (exists_representative (sum A Z (component f) (component g)))

lemma component_add {A Z : OmegaSpectrum.{u}} (f g : A ⟶ target Z) :
    component (add f g) = sum A Z (component f) (component g) :=
  Classical.choose_spec (exists_representative _)

lemma component_add_zero {A Z : OmegaSpectrum.{u}} (f : A ⟶ target Z) :
    component (add f 0) = component f := by
  rw [component_add, ← unit_eq_zero, sum_unit]

lemma component_zero_add {A Z : OmegaSpectrum.{u}} (f : A ⟶ target Z) :
    component (add 0 f) = component f := by
  rw [component_add, ← unit_eq_zero, unit_sum]

lemma component_pre_add {A B Z : OmegaSpectrum.{u}} (f : A ⟶ B) (g h : B ⟶ target Z) :
    component (f ≫ add g h) = component (add (f ≫ g) (f ≫ h)) := by
  rw [← pre_component, component_add, pre_sum, pre_component, pre_component, component_add]

end SerrePositivity.KST.LocalizingInvariants.CotensorClasses
