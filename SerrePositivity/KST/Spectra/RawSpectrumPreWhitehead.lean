module

public import SerrePositivity.KST.Spectra.RawSpectrumMappingPrecomposition
public import SerrePositivity.KST.Spectra.SpectrumMappingComponents
public import SerrePositivity.KST.Spectra.ExponentialHomotopyEdges
public import SerrePositivity.KST.Spectra.KanEquivalenceBridge

/-!
概要：BF 源の段ごとの π 同型による前合成は、元の全 Hom のホモトピー同値。
方針：全スペクトル Hom 内の両側逆の辺を、合成の全パラメータ作用へ写す。
規約：標的は一般の Kan 列。段ごとのホモトピー類から全 Hom の一致を推論しない。
使われ方：元の評価写像の源比較の打ち消し。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping

/-- 元の合成を curry した、全 Hom 上の前合成のパラメータ作用。 -/
def preAction (X Y : OmegaSpectrum.{u}) (Z : KanSequence.{u}) :
    OmegaSpectrum.mappingSpace X Y ⟶ (ihom (space Y Z)).obj (space X Z) :=
  curry ((β_ (space Y Z) (OmegaSpectrum.mappingSpace X Y)).hom ≫ composition X Y Z)

lemma preAction_vertex {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) (Z : KanSequence.{u}) :
    (preAction X Y Z).app _ (OmegaSpectrum.vertexOfHom f) =
      ExponentialPaths.vertex (pre f Z) := by
  rw [OmegaSpectrum.vertexOfHom, ← OmegaSpectrum.unitHomEquiv_comp]
  change SSet.unitHomEquiv _ (OmegaSpectrum.vertexOfHomMap f ≫ preAction X Y Z) = _
  rw [preAction, ← curry_natural_left]
  have h : (space Y Z ◁ OmegaSpectrum.vertexOfHomMap f) ≫
      (β_ (space Y Z) (OmegaSpectrum.mappingSpace X Y)).hom =
      (β_ (space Y Z) (𝟙_ SSet.{u})).hom ≫
        OmegaSpectrum.vertexOfHomMap f ▷ space Y Z := by
    exact BraidedCategory.braiding_naturality_right _ _
  rw [← Category.assoc, h, Category.assoc]
  change SSet.unitHomEquiv _ (curry (_ ≫ _ ≫ composition X Y Z)) = _
  unfold ExponentialPaths.vertex pre
  rfl

/-- 全スペクトル Hom の同じ成分に属する二射は、前合成の実ホモトピーを与える。 -/
lemma pre_homotopy_of_component_eq {X Y : OmegaSpectrum.{u}} {f g : X ⟶ Y}
    (h : SpectrumMappingAcyclic.component f = SpectrumMappingAcyclic.component g)
    (Z : KanSequence.{u}) : Nonempty (SSet.Homotopy (pre f Z) (pre g Z)) := by
  obtain ⟨e⟩ := nonempty_edge_of_piZero_eq h
  let e' := e.map (preAction X Y Z)
  rw [preAction_vertex, preAction_vertex] at e'
  exact ⟨ExponentialPaths.homotopyOfEdge e'⟩

local instance preWhiteheadPointedSimplicialCategory :
    SimplicialCategory PointedSimplicialSet.{u} := PointedEnrichment.simplicialCategory

/-- 元の全 Hom の前合成は厳密に反変な合成則を満たす。 -/
lemma pre_comp {X Y W : OmegaSpectrum.{u}} (f : X ⟶ Y) (g : Y ⟶ W)
    (Z : KanSequence.{u}) : pre (f ≫ g) Z = pre g Z ≫ pre f Z := by
  apply hom_ext X Z
  intro n
  rw [pre_evaluation, Category.assoc, pre_evaluation, ← Category.assoc, pre_evaluation,
    Category.assoc]
  simp only [← PointedEnrichment.whiskerRight_eq]
  exact congrArg (evaluation W Z n ≫ ·)
    (eHomWhiskerRight_comp SSet (f.app n) (g.app n) (Z.level n).space)

/-- 元の全 Hom の恒等射による前合成は恒等射。 -/
lemma pre_id (X : OmegaSpectrum.{u}) (Z : KanSequence.{u}) : pre (𝟙 X) Z = 𝟙 _ := by
  apply hom_ext X Z
  intro n
  rw [pre_evaluation, Category.id_comp]
  simp only [← PointedEnrichment.whiskerRight_eq]
  change evaluation X Z n ≫ eHomWhiskerRight SSet (𝟙 (X.level n).space)
    (Z.level n).space = _
  rw [eHomWhiskerRight_id]
  exact Category.comp_id (evaluation X Z n)

/-- BF の段ごとの π 同型は、任意の Kan 列への元の全 Hom の前合成でホモトピー同値。 -/
lemma pre_homotopyEquivalence_of_levelwise {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y)
    (hf : ∀ n, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (f.app n).right) (Z : KanSequence.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (pre f Z) := by
  obtain ⟨g, hg, hh⟩ := SpectrumMappingAcyclic.exists_componentInverse f hf
  refine ⟨pre g Z, ?_, ?_⟩
  · rw [← pre_comp, ← pre_id Y Z]
    exact pre_homotopy_of_component_eq hh Z
  · rw [← pre_comp, ← pre_id X Z]
    exact pre_homotopy_of_component_eq hg Z

/-- 同じ元の点つき全 Hom の前合成の、全基点 π 同型性。 -/
lemma pointedPre_piIsomorphism_of_levelwise {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y)
    (hf : ∀ n, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (f.app n).right) (Z : KanSequence.{u}) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (pointedPre f Z).right :=
  kanPiIsomorphism_of_qCatEquivalence _
    (pre_homotopyEquivalence_of_levelwise f hf Z).isQCatEquivalence

end SerrePositivity.KST.Spectra.RawSpectrumMapping
