module
public import SerrePositivity.KST.SConstruction.PointedFixedVertexComposition
public import SerrePositivity.KST.Spectra.SpectrumWhiteheadEquivalence

/-! # 元の BF 段頂点の合成写像を通常の点つき前合成へ照合する
概要：元の BF 射の段頂点と合成する全 Hom 写像を、同じ実段射の前合成として回収する。
方針：既存の豊穣頂点評価と点つき通常射の頂点表示を使う。
規約：元の BF 射と段射を選び直さず、全 Hom の実写像を同定する。
使われ方：三本の補正辺路の結合律と raw 後合成の交換を厳密に計算する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet Spectra Spectra.PointedMapping
open scoped Simplicial
local instance stageFixedPointedSimplicialCategory :
    SimplicialCategory PointedSimplicialSet.{u} := PointedEnrichment.simplicialCategory
local instance stageFixedSpectrumSimplicialCategory :
    SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory

/-- 元の BF 射の豊穣段頂点は、元の同じ点つき段射の頂点表示。 -/
lemma spectrumStageVertex_familyVertex {A B : OmegaSpectrum.{u}} (f : A ⟶ B) (n : ℕ) :
    (OmegaSpectrum.evaluation A B n).app (Opposite.op ⦋0⦌)
        (SimplicialCategory.homEquiv' _ _ f) = familyVertex (f.app n) := by
  rw [SpectrumMappingAcyclic.homEquiv'_eq_vertex, OmegaSpectrum.vertexOfHom_evaluation,
    familyVertex_eq_pointedHomVertex]

/-- 固定 BF 段頂点との全合成は、同じ点つき段射による前合成そのもの。 -/
lemma spectrumStageFixedLeftComposition_pre {A B : OmegaSpectrum.{u}} (f : A ⟶ B)
    (C : PointedSimplicialSet.{u}) (n : ℕ) :
    lift (SSet.const ((OmegaSpectrum.evaluation A B n).app (Opposite.op ⦋0⦌)
        (SimplicialCategory.homEquiv' _ _ f)))
      (𝟙 (PointedObject.basedHom (B.level n).space C).right) ≫
      eComp SSet (A.level n).space (B.level n).space C = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (f.app n) C := by
  rw [spectrumStageVertex_familyVertex, pointedFamilyComposition_const_left, Category.id_comp]

end SerrePositivity.KST.SConstruction
