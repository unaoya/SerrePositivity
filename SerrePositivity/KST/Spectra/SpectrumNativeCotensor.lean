module

public import SerrePositivity.KST.Spectra.SpectrumCotensorCompatibleFunctors
public import SerrePositivity.InfinityCategories.F1.Coherent.NerveFullyFaithful
public import SerrePositivity.InfinityCategories.Core.FullyFaithfulEquivalence
public import SerrePositivity.InfinityCategories.Coherent.Quasicategory

/-!
概要：BF cotensor の、元の Sp 上の実際の coherent な関手化。
方針：整合写像の圏の源射影の同値の逆と cotensor 射影を合成する。
規約：豊穣射影の全 Hom 同値から構成する。対象ごとの同型だけを関手同型と扱わない。
使われ方：円の cotensor と native loop の高次自然な比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum
local instance nativeCotensorSpectrumSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
local instance nativeCotensorSpectrumHomKan (X Y : OmegaSpectrum.{u}) :
    KanComplex (SimplicialCategory.sHom X Y) := mappingSpace_kanComplex X Y
namespace CotensorCompatible

/-- 整合写像の coherent nerve から元の Sp への射影。 -/
def sourceInfinityMap (A : PointedSimplicialSet.{u}) :
    SimplicialNerve (Object A) ⟶ Sp.{u} := coherentNerveMap (sourceEnriched A)

/-- 整合写像の coherent nerve から cotensor の値への射影。 -/
def cotensorInfinityMap (A : PointedSimplicialSet.{u}) :
    SimplicialNerve (Object A) ⟶ Sp.{u} := coherentNerveMap (cotensorEnriched A)

/-- 元の Sp への射影は、全写像空間の意味で完全忠実。 -/
lemma sourceInfinityMap_isFullyFaithful (A : PointedSimplicialSet.{u}) :
    IsFullyFaithful (sourceInfinityMap A) := by
  apply (coherentNerveMap_isFullyFaithful_iff (sourceEnriched A)).mpr
  intro X Y
  exact (sourceEquivalence A X.val Y.val).isQCatEquivalence

/-- 源射影は元の全ての BF 対象を表す。 -/
lemma sourceInfinityMap_isEssentiallySurjective (A : PointedSimplicialSet.{u}) :
    IsEssentiallySurjective (sourceInfinityMap A) := by
  intro y
  refine ⟨coherentNerveVertex (⟨coherentNerveObject y⟩ : Object A), ?_⟩
  change Nonempty (VertexIso
    ((coherentNerveMap (sourceEnriched A)).app _ (coherentNerveVertex _)) y)
  rw [coherentNerveMap_vertex]
  exact ⟨eqToIso (congrArg SSet.HomotopyCategory.mk (coherentNerveVertex_object y))⟩

/-- 源射影そのものを順方向とする実際の ∞ 圏同値。 -/
def sourceInfinityEquivalence (A : PointedSimplicialSet.{u}) :
    QCatEquivalence (SimplicialNerve (Object A)) Sp.{u} :=
  qCatEquivalenceOfFullyFaithfulEssentiallySurjective (sourceInfinityMap A)
    (sourceInfinityMap_isFullyFaithful A) (sourceInfinityMap_isEssentiallySurjective A)

/-- 同値の順方向は元の源射影。 -/
lemma sourceInfinityEquivalence_hom (A : PointedSimplicialSet.{u}) :
    (sourceInfinityEquivalence A).hom = sourceInfinityMap A := rfl

end CotensorCompatible

/-- 元の Sp 上の全単体で定義された cotensor 関手。 -/
def nativeCotensor (A : PointedSimplicialSet.{u}) : Sp.{u} ⟶ Sp.{u} :=
  (CotensorCompatible.sourceInfinityEquivalence A).inv ≫
    CotensorCompatible.cotensorInfinityMap A

/-- 整合写像の共通解像上での、元の cotensor 射影との高次自然な比較。 -/
def nativeCotensor_sourceIso (A : PointedSimplicialSet.{u}) :
    FunctorIso (CotensorCompatible.sourceInfinityMap A ≫ nativeCotensor A)
      (CotensorCompatible.cotensorInfinityMap A) := by
  have h := FunctorIso.postcomp (CotensorCompatible.sourceInfinityEquivalence A).homInvIso
    (CotensorCompatible.cotensorInfinityMap A)
  simpa only [CotensorCompatible.sourceInfinityEquivalence_hom, Category.assoc,
    Category.id_comp, nativeCotensor] using h

/-- 関手の値は、元の実際の BF cotensor と Sp で同型。 -/
def nativeCotensorVertexIso (A : PointedSimplicialSet.{u}) (X : OmegaSpectrum.{u}) :
    VertexIso ((nativeCotensor A).app _ (coherentNerveVertex X))
      (coherentNerveVertex (cotensor A X)) := by
  have h := FunctorIso.app (nativeCotensor_sourceIso A)
    (coherentNerveVertex (⟨X⟩ : CotensorCompatible.Object A))
  change VertexIso
    ((nativeCotensor A).app _
      ((coherentNerveMap (CotensorCompatible.sourceEnriched A)).app _ (coherentNerveVertex _)))
    ((coherentNerveMap (CotensorCompatible.cotensorEnriched A)).app _ (coherentNerveVertex _)) at h
  rw [coherentNerveMap_vertex, coherentNerveMap_vertex] at h
  exact h

end SerrePositivity.KST.Spectra.OmegaSpectrum
