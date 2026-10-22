module

public import SerrePositivity.InfinityCategories.F2.Presentable.SmallFullSubcomplex
public import SerrePositivity.InfinityCategories.Stable.UniverseHorns
public import SerrePositivity.InfinityCategories.F1B.FullSubcomplexMapping

/-!
概要：小さい頂点族上の全部分圏を宇宙 u の ∞ 圏で厳密に模型化する。
方針：全次数の縮小同型を使い、持ち上げたホーン充填から quasicategory 性を反映する。
規約：元の大きい標的への包含を保持し、その充満忠実性を実証する。
使われ方：Ind 内の共通の小さい μ-compact 族から小さい生成圏を得る。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits

/-- 全 inner horn の持ち上げと降下により、元の宇宙の quasicategory 性を反映する。 -/
lemma quasicategory_of_ulift (X : SSet.{u})
    [Quasicategory ((SSet.uliftFunctor.{v, u}).obj X)] : Quasicategory X := by
  constructor
  intro n i f h0 hn
  obtain ⟨g, hg⟩ := Quasicategory.hornFilling h0 hn
    ((uliftHornIso.{u, v} (n + 2) i).inv ≫ (SSet.uliftFunctor.{v, u}).map f)
  refine ⟨uliftMorphismDown ((uliftStdSimplexIso.{u, v} (n + 2)).hom ≫ g), ?_⟩
  apply (SSet.uliftFunctor.{v, u}).map_injective
  rw [Functor.map_comp, uliftMorphismDown_lift, ← Category.assoc,
    ← uliftHornIso_ι, Category.assoc, ← hg, Iso.hom_inv_id_assoc]

variable {X : SSet.{u + 1}} (hX : Ind.HasSmallFixedVertexMaps X)
  {T : Type u} (v : T → X _⦋0⦌)

/-- 共通の小さい族の値上の全部分圏を、元の小さい宇宙で縮小する。 -/
def smallFullModel : SSet.{u} := by
  have (n : SimplexCategoryᵒᵖ) := small_fullSubcomplexOnRange hX v n
  exact smallSimplicialSet.{u, u + 1}
    (fullSubcomplexOnVertices X (fun x ↦ x ∈ Set.range v)).toSSet

/-- 縮小模型の持ち上げと、元の全部分圏の全単体の同型。 -/
def smallFullModelIso : (SSet.uliftFunctor.{u + 1, u}).obj (smallFullModel hX v) ≅
    (fullSubcomplexOnVertices X (fun x ↦ x ∈ Set.range v)).toSSet :=
  by
    have (n : SimplexCategoryᵒᵖ) := small_fullSubcomplexOnRange hX v n
    exact smallSimplicialSetIso.{u, u + 1} _

instance smallFullModel_quasicategory [Quasicategory X] : Quasicategory (smallFullModel hX v) := by
  have : InnerFibration (smallFullModelIso hX v).hom :=
    ⟨MorphismProperty.of_isIso innerFibrations _⟩
  have := quasicategory_of_innerFibration (smallFullModelIso hX v).hom
  exact quasicategory_of_ulift.{u, u + 1} (smallFullModel hX v)

/-- 小さい模型から元の大きい標的への、同じ全部分包含。 -/
def smallFullModelInclusion : (SSet.uliftFunctor.{u + 1, u}).obj (smallFullModel hX v) ⟶ X :=
  (smallFullModelIso hX v).hom ≫ (fullSubcomplexOnVertices X (fun x ↦ x ∈ Set.range v)).ι

/-- 元の全部分包含と縮小同型の合成は、全写像空間で充満忠実。 -/
lemma smallFullModelInclusion_isFullyFaithful [Quasicategory X] :
    IsFullyFaithful (smallFullModelInclusion hX v) :=
  (qCatEquivalenceOfIso (smallFullModelIso hX v)).isFullyFaithful.comp
    (isFullyFaithful_fullSubcomplexOnVertices_ι _ _)

end SerrePositivity.InfinityCategories.F2.Presentable
