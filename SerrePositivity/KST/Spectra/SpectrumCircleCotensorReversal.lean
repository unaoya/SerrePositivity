module

public import SerrePositivity.KST.Spectra.SpectrumCircleCotensorComponents
public import SerrePositivity.KST.Spectra.SpectrumWhiteheadEquivalence

/-!
概要：元の円 cotensor の頂点に、評価の基本群の符号を反転する BF 自己射を構成する。
方針：元の Hom の成分表示で逆元を選び、前合成の群準同型性から二乗を計算する。
規約：安定性や loop の完全忠実性を仮定しない。使われ方：元の評価錐の頂点の符号比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum
local instance circleCotensorReversalSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
local instance circleCotensorReversalHomKan (X Y : OmegaSpectrum.{u}) :
    KanComplex (SimplicialCategory.sHom X Y) := mappingSpace_kanComplex X Y

/-- 元の恒等射の評価の逆元を表す BF 自己射と、その元の成分の式。 -/
def circleCotensorReversalData (Y : OmegaSpectrum.{u}) :
    {f : cotensor PointedSimplicialSet.circle Y ⟶ cotensor PointedSimplicialSet.circle Y //
      circleCotensorComponentClass (cotensor PointedSimplicialSet.circle Y) Y
        (SpectrumMappingAcyclic.component f) =
      (circleCotensorComponentClass (cotensor PointedSimplicialSet.circle Y) Y
        (SpectrumMappingAcyclic.component (𝟙 (cotensor PointedSimplicialSet.circle Y))))⁻¹} :=
  Classical.choice (by
    obtain ⟨a, ha⟩ := (circleCotensorComponentClass_bijective
      (cotensor PointedSimplicialSet.circle Y) Y).surjective
        ((circleCotensorComponentClass (cotensor PointedSimplicialSet.circle Y) Y
          (SpectrumMappingAcyclic.component (𝟙 (cotensor PointedSimplicialSet.circle Y))))⁻¹)
    obtain ⟨v, rfl⟩ := π₀.mk_surjective a
    refine ⟨⟨homOfVertex v, ?_⟩⟩
    simpa only [SpectrumMappingAcyclic.component, vertexOfHom_homOfVertex] using ha)
/-- 元の円 cotensor の評価の符号を反転する、実際の BF 自己射。 -/
def circleCotensorReversal (Y : OmegaSpectrum.{u}) :
    cotensor PointedSimplicialSet.circle Y ⟶ cotensor PointedSimplicialSet.circle Y :=
  (circleCotensorReversalData Y).val

/-- この自己射の成分は、元の恒等射の評価の逆元を表す。 -/
lemma circleCotensorReversal_class (Y : OmegaSpectrum.{u}) :
    circleCotensorComponentClass (cotensor PointedSimplicialSet.circle Y) Y
      (SpectrumMappingAcyclic.component (circleCotensorReversal Y)) =
    (circleCotensorComponentClass (cotensor PointedSimplicialSet.circle Y) Y
      (SpectrumMappingAcyclic.component (𝟙 (cotensor PointedSimplicialSet.circle Y))))⁻¹ :=
  (circleCotensorReversalData Y).property

/-- 元の符号反転自己射の二乗は、元の全 Hom 内で恒等射と同じ成分にある。 -/
lemma circleCotensorReversal_square_component (Y : OmegaSpectrum.{u}) :
    SpectrumMappingAcyclic.component (circleCotensorReversal Y ≫ circleCotensorReversal Y) =
      SpectrumMappingAcyclic.component (𝟙 (cotensor PointedSimplicialSet.circle Y)) := by
  apply (circleCotensorComponentClass_bijective
    (cotensor PointedSimplicialSet.circle Y) Y).injective
  have hf := circleCotensorComponentClass_pre (circleCotensorReversal Y) Y
    (SpectrumMappingAcyclic.component (circleCotensorReversal Y))
  have hi := circleCotensorComponentClass_pre (circleCotensorReversal Y) Y
    (SpectrumMappingAcyclic.component (𝟙 (cotensor PointedSimplicialSet.circle Y)))
  rw [SpectrumMappingAcyclic.pre_component] at hf hi
  simp only [Category.comp_id] at hi
  rw [hf, circleCotensorReversal_class, map_inv, ← hi, circleCotensorReversal_class, inv_inv]

/-- 元の符号反転 BF 自己射そのものが、Sp 内の可逆な辺を与える。 -/
lemma circleCotensorReversal_isInvertible (Y : OmegaSpectrum.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (circleCotensorReversal Y)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentNerveEdge_isInvertible_of_enrichedInverse (circleCotensorReversal Y)
    (circleCotensorReversal Y)
    (SpectrumMappingAcyclic.vertexIsoOfComponentEq (circleCotensorReversal_square_component Y))
    (SpectrumMappingAcyclic.vertexIsoOfComponentEq (circleCotensorReversal_square_component Y))

end SerrePositivity.KST.Spectra.OmegaSpectrum
