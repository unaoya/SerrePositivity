module

public import SerrePositivity.KST.Spectra.SpectrumMappingWhitehead
public import SerrePositivity.KST.Spectra.SpectrumLevelwiseInverse
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.HomotopyComponents

/-!
概要：BF 射の段ごとの π 同型から、実際のスペクトル写像空間での両側の逆条件を構成する。
方針：標的の恒等射を後合成の π₀ 全射性で戻し、もう一方の逆条件を単射性で検査する。
規約：写像空間全体の連結成分について述べる。段ごとの成分に弱めない。
使われ方：BF 1978 §2、HTT A.3.3。coherent nerve の同値の検出。
-/

@[expose] public section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial

namespace SerrePositivity.KST.Spectra.SpectrumMappingAcyclic
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
local instance : SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory
local instance (X Y : OmegaSpectrum.{u}) : KanComplex (SimplicialCategory.sHom X Y) :=
  OmegaSpectrum.mappingSpace_kanComplex X Y
open OmegaSpectrum

/-- 実際のスペクトル写像空間における厳密射の連結成分。 -/
def component {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) : π₀ (mappingSpace X Y) :=
  π₀.mk (vertexOfHom f)

/-- 豊穣後合成の頂点は実際の厳密射の合成を表す。 -/
lemma post_vertex {A X Y : OmegaSpectrum.{u}} (f : A ⟶ X) (p : X ⟶ Y) :
    (post A p).app _ (vertexOfHom f) = vertexOfHom (f ≫ p) := by
  apply vertex_ext
  intro n
  have h := congrArg (fun q : mappingSpace A X ⟶
      (PointedObject.basedHom (A.level n).space (Y.level n).space).right ↦
        q.app _ (vertexOfHom f)) (_root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumHomMap_evaluation A p n)
  change (evaluation A Y n).app _ ((post A p).app _ (vertexOfHom f)) = _ at h
  change (evaluation A Y n).app _ ((post A p).app _ (vertexOfHom f)) =
    (PointedObject.basedHomMap (A.level n).space (p.app n)).right.app _
      ((evaluation A X n).app _ (vertexOfHom f)) at h
  rw [h, vertexOfHom_evaluation, pointedHomVertexEquiv_post, vertexOfHom_evaluation]
  rfl

@[simp]
lemma post_component {A X Y : OmegaSpectrum.{u}} (f : A ⟶ X) (p : X ⟶ Y) :
    mapπ₀ (post A p) (component f) = component (f ≫ p) :=
  congrArg π₀.mk (post_vertex f p)

/-- 豊穣 Hom の実際の前合成。 -/
abbrev pre {A X : OmegaSpectrum.{u}} (f : A ⟶ X) (Z : OmegaSpectrum.{u}) :
    mappingSpace X Z ⟶ mappingSpace A Z := eHomWhiskerRight SSet f Z

/-- 豊穣前合成も頂点で実際の厳密射の合成を表す。 -/
lemma pre_vertex {A X Z : OmegaSpectrum.{u}} (f : A ⟶ X) (g : X ⟶ Z) :
    (pre f Z).app _ (vertexOfHom g) = vertexOfHom (f ≫ g) := by
  have he : eHomEquiv SSet g ≫ eHomWhiskerRight SSet f Z = eHomEquiv SSet (f ≫ g) := by
    rw [eHomEquiv_comp, eHomWhiskerRight, leftUnitor_inv_comp_tensorHom_assoc]
  change (SSet.unitHomEquiv _).symm (vertexOfHom g) ≫ pre f Z =
    (SSet.unitHomEquiv _).symm (vertexOfHom (f ≫ g)) at he
  have h := congrArg (SSet.unitHomEquiv _) he
  simpa only [unitHomEquiv_comp, Equiv.apply_symm_apply] using h

@[simp]
lemma pre_component {A X Z : OmegaSpectrum.{u}} (f : A ⟶ X) (g : X ⟶ Z) :
    mapπ₀ (pre f Z) (component g) = component (f ≫ g) :=
  congrArg π₀.mk (pre_vertex f g)

/-- 元の源への参照射があれば、π 同型の後合成は全連結成分で全単射。 -/
lemma post_piZero_bijective (A : OmegaSpectrum.{u}) {X Y : OmegaSpectrum.{u}}
    (p : X ⟶ Y) (hp : ∀ n, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (p.app n).right) (a : A ⟶ X) :
    Function.Bijective (mapπ₀ (post A p)) :=
  (post_piIsomorphism_of_levelwise A p hp).piZero_bijective_at (vertexOfHom a)

/-- 段ごとの π 同型は実際の豊穣 Hom の π₀ で両側の逆を持つ。 -/
theorem exists_componentInverse {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y)
    (hf : ∀ n, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (f.app n).right) :
    ∃ g : Y ⟶ X, component (f ≫ g) = component (𝟙 X) ∧
      component (g ≫ f) = component (𝟙 Y) := by
  obtain ⟨a, ha⟩ := (post_piZero_bijective Y f hf (levelwiseInverse f hf)).surjective
    (component (𝟙 Y))
  obtain ⟨v, rfl⟩ := π₀.mk_surjective a
  let g : Y ⟶ X := homOfVertex v
  have hg : component (g ≫ f) = component (𝟙 Y) := by
    rw [← post_component]
    simpa only [component, g, vertexOfHom_homOfVertex] using ha
  refine ⟨g, ?_, hg⟩
  apply (post_piZero_bijective X f hf (𝟙 X)).injective
  rw [post_component, post_component, Category.assoc, Category.id_comp]
  have h := congrArg (fun a ↦ mapπ₀ (pre f Y) a) hg
  simpa only [pre_component, Category.comp_id] using h

end
end SerrePositivity.KST.Spectra.SpectrumMappingAcyclic
