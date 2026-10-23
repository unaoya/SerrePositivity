module

public import SerrePositivity.InfinityCategories.F2.Presentable.SmallFullModel
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FullSubcomplexRestrictionEquivalence

/-!
概要：小さい頂点族上の全部分圏と、その同型飽和上の全部分圏との全同値を構成する。
方針：元の全部分包含で充満忠実性を検出し、各頂点の指定同型で本質的全射性を得る。
規約：同型飽和自体の単体が小さいとは仮定しない。小さい模型からの同値を提供する。
使われ方：部分余極限族の全表示を、同型を通じて小さい生成圏へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
variable {X : SSet.{u + 1}} [Quasicategory X] {T : Type u} (v : T → X _⦋0⦌)

/-- 共通の小さい族の一つと、元の標的内で頂点同型を持つこと。 -/
def FamilySaturation (x : X _⦋0⦌) : Prop := ∃ t, Nonempty (VertexIso x (v t))

/-- 同型で飽和した同じ族の、元の標的内の全部分 ∞ 圏。 -/
def familySaturationCategory : SSet.{u + 1} :=
  (fullSubcomplexOnVertices X (FamilySaturation v)).toSSet

instance familySaturationCategory_quasicategory : Quasicategory (familySaturationCategory v) :=
  inferInstanceAs (Quasicategory (fullSubcomplexOnVertices X (FamilySaturation v)).toSSet)

/-- 同じ同型飽和の全部分包含。 -/
def familySaturationInclusion : familySaturationCategory v ⟶ X :=
  (fullSubcomplexOnVertices X (FamilySaturation v)).ι

/-- 小さい縮小模型から同型飽和への、元の全部分包含の持ち上げ。 -/
def smallFamilySaturationComparison (hX : Ind.HasSmallFixedVertexMaps X) :
    (SSet.uliftFunctor.{u + 1, u}).obj (smallFullModel hX v) ⟶ familySaturationCategory v :=
  fullSubcomplexLift (FamilySaturation v) (smallFullModelInclusion hX v) (by
    intro s
    have hs := fullSubcomplexOnVertices_vertex ((smallFullModelIso hX v).hom.app _ s)
    obtain ⟨t, ht⟩ := hs
    exact ⟨t, ⟨eqToIso (congrArg HomotopyCategory.mk ht.symm)⟩⟩)

omit [Quasicategory X] in
/-- 同型飽和への比較も、元の大きい標的への包含そのものを保つ。 -/
lemma smallFamilySaturationComparison_inclusion (hX : Ind.HasSmallFixedVertexMaps X) :
    smallFamilySaturationComparison v hX ≫ familySaturationInclusion v =
      smallFullModelInclusion hX v := rfl

/-- 小さい模型から同型飽和への比較は、全 ∞ 圏の同値。 -/
lemma smallFamilySaturationComparison_isEquivalence (hX : Ind.HasSmallFixedVertexMaps X) :
    IsQCatEquivalence (smallFamilySaturationComparison v hX) := by
  apply isQCatEquivalence_of_isFullyFaithful_of_isEssentiallySurjective
  · apply (isFullyFaithful_fullSubcomplexOnVertices_ι X (FamilySaturation v)).cancel_right
    change IsFullyFaithful (smallFullModelInclusion hX v)
    exact smallFullModelInclusion_isFullyFaithful hX v
  · intro z
    obtain ⟨t, ⟨e⟩⟩ := fullSubcomplexOnVertices_vertex z
    let y : (fullSubcomplexOnVertices X (fun x ↦ x ∈ Set.range v)).toSSet _⦋0⦌ :=
      ⟨v t, by
        intro α
        have hα : α = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
        subst α
        simpa only [op_id, CategoryTheory.Functor.map_id_apply] using Set.mem_range_self t⟩
    let s := (smallFullModelIso hX v).inv.app (Opposite.op ⦋0⦌) y
    refine ⟨s, ⟨(isFullyFaithful_fullSubcomplexOnVertices_ι X
      (FamilySaturation v)).preimageVertexIso ?_⟩⟩
    have hs : (smallFullModelInclusion hX v).app (Opposite.op ⦋0⦌) s = v t := by
      change ((smallFullModelIso hX v).hom.app _
        ((smallFullModelIso hX v).inv.app _ y)).val = v t
      have hi := ConcreteCategory.congr_hom
        (NatTrans.congr_app (smallFullModelIso hX v).inv_hom_id (Opposite.op ⦋0⦌)) y
      exact congrArg Subtype.val hi
    change VertexIso ((smallFullModelInclusion hX v).app _ s) z.val
    rw [hs]
    exact e.symm

/-- 元の比較関手そのものを順方向に持つ、小さい模型と同型飽和の全同値。 -/
def smallFamilySaturationEquivalence (hX : Ind.HasSmallFixedVertexMaps X) :
    QCatEquivalence ((SSet.uliftFunctor.{u + 1, u}).obj (smallFullModel hX v))
      (familySaturationCategory v) :=
  (smallFamilySaturationComparison_isEquivalence v hX).choose

end SerrePositivity.InfinityCategories.F2.Presentable
