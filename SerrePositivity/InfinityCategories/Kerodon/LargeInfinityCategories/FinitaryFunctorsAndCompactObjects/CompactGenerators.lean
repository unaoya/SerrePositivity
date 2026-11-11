module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.Accessible
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.FilteredRetraction
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.RepresentableRetractions

/-!
概要：κ-compact 生成圏があれば、全 κ-compact 対象は生成対象の retract である。
方針：指定対象を頂点とする同じ filtered 表示へ N の恒等点因子化を適用する。
規約：Ind 表現との同値を仮定しない。元の生成関手と対象を保持する。
使われ方：HTT 5.4.2、accessible 圏の compact 部分の同定。

対応節は Kerodon 9.2（Tag 0639）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects
variable {κ : Cardinal.{u}} {A : SSet.{u}} [Quasicategory A]
  {C : SSet.{u + 1}} [Quasicategory C]
  {i : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ C}

/-- 元の任意の κ-compact 対象は、小さい生成圏の一つの対象の像の retract。 -/
lemma IsKappaCompactGenerating.retract_generator (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaCompactGenerating κ i)
    {x : C _⦋0⦌} (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} κ x) :
    ∃ a : A _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsVertexRetractOf x
      (i.app (Opposite.op ⦋0⦌) (ULift.up a)) := by
  obtain ⟨I, hI, hκ, a, c, hc, hcol⟩ := h.presentation x
  have := hI
  have := hκ
  have hx' : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} κ c.vertex := hc.symm ▸ hx
  obtain ⟨j, hj⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IsKappaCompact.retract_of_colimit
    ((SSet.uliftFunctor.{u + 1, u}).map a ≫ i) c hcol hx'
  refine ⟨a.app (Opposite.op ⦋0⦌) j, ?_⟩
  have hv : ((SSet.uliftFunctor.{u + 1, u}).map a).app (Opposite.op ⦋0⦌) (ULift.up j) =
      ULift.up (a.app (Opposite.op ⦋0⦌) j) := rfl
  simp only [SSet.comp_app, types_comp_apply] at hj
  rw [hv, hc] at hj
  exact hj

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaCompactGenerating export _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompactGenerating (retract_generator)


/-- κ-compact 部分は、指定された小さい生成圏の像の retract 閉包そのもの。 -/
lemma IsKappaCompactGenerating.compact_iff_retract (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaCompactGenerating κ i)
    (x : C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} κ x ↔
      ∃ a : A _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsVertexRetractOf x
        (i.app (Opposite.op ⦋0⦌) (ULift.up a)) := by
  constructor
  · exact h.retract_generator
  · rintro ⟨a, ha⟩
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.of_retract ha (h.compact a)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaCompactGenerating export _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompactGenerating (compact_iff_retract)


end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects
