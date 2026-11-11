module

public import SerrePositivity.KST.Spectra.RawSpectrumMappingCompositionLaws
public import SerrePositivity.KST.Spectra.RawSpectrumMappingPointed

/-!
概要：一般の Kan 列への元の整合写像空間で、BF 源の厳密射の前合成を構成する。
方針：元の豊穣合成を射の頂点で評価し、段ごとの前合成と基点保存を照合する。
規約：別の写像空間へ取り替えない。使われ方：Hom-end 交換の源変数の自然性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping
local instance rawPrePointedSimplicialCategory :
    SimplicialCategory PointedSimplicialSet.{u} := PointedEnrichment.simplicialCategory
local instance rawPreSpectrumSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

/-- 元の BF 射の頂点で、実際の豊穣合成の源パラメータを評価する。 -/
def pre {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) (Z : KanSequence.{u}) :
    space Y Z ⟶ space X Z :=
  (λ_ (space Y Z)).inv ≫ OmegaSpectrum.vertexOfHomMap f ▷ space Y Z ≫ composition X Y Z

@[reassoc (attr := simp)]
lemma pre_evaluation {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) (Z : KanSequence.{u}) (n : ℕ) :
    pre f Z ≫ evaluation X Z n =
      evaluation Y Z n ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (f.app n) (Z.level n).space := by
  rw [pre, Category.assoc, Category.assoc, composition_evaluation]
  dsimp only [compositionFamily]
  rw [whiskerRight_comp_tensorHom_assoc, OmegaSpectrum.vertexOfHomMap_evaluation,
    leftUnitor_inv_comp_tensorHom_assoc]
  change evaluation Y Z n ≫ eHomWhiskerRight SSet (f.app n) (Z.level n).space = _
  rw [PointedEnrichment.whiskerRight_eq]

/-- 一般の Kan 列への前合成も、元の零写像の基点を保つ。 -/
def pointedPre {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) (Z : KanSequence.{u}) :
    pointedSpace Y Z ⟶ pointedSpace X Z :=
  Under.homMk (pre f Z) (by
    apply hom_ext X Z
    intro n
    rw [Category.assoc, pre_evaluation, ← Category.assoc]
    have he := Under.w (pointedEvaluation Y Z n)
    change (pointedSpace Y Z).hom ≫ evaluation Y Z n = _ at he
    rw [he]
    exact (Under.w (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (f.app n) (Z.level n).space)).trans
      (Under.w (pointedEvaluation X Z n)).symm)

@[reassoc (attr := simp)]
lemma pointedPre_evaluation {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y)
    (Z : KanSequence.{u}) (n : ℕ) :
    pointedPre f Z ≫ pointedEvaluation X Z n = pointedEvaluation Y Z n ≫
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (f.app n) (Z.level n).space := by
  apply Under.UnderMorphism.ext
  exact pre_evaluation f Z n

/-- BF 標的の場合、前合成は元の単体的圏の豊穣前合成そのもの。 -/
lemma pre_spectrum {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) (Z : OmegaSpectrum.{u}) :
    pre f Z.toKanSequence = eHomWhiskerRight SSet f Z := by
  have hf : eHomEquiv SSet f = OmegaSpectrum.vertexOfHomMap f := by
    change (SSet.unitHomEquiv (OmegaSpectrum.mappingSpace X Y)).symm
      ((SSet.unitHomEquiv _) (OmegaSpectrum.vertexOfHomMap f)) = _
    exact Equiv.symm_apply_apply _ _
  unfold eHomWhiskerRight
  rw [hf]
  rfl

end SerrePositivity.KST.Spectra.RawSpectrumMapping
