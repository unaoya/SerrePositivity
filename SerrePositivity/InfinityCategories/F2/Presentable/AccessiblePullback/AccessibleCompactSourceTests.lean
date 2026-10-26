module

public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.CompactCommaFiltered

/-!
概要：accessible 圏の compact 始域 slice に全小試験余錐を構成する。
方針：元の入力付き compact 表示の一頂点を選び、全 slice 余錐に戻す。
規約：全小余極限は要求せず、元の accessible 性だけから構成する。
使われ方：一般 accessible 成分の標準密度余錐の filtered 局所存在。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback
open HomotopyLimits

/-- 概要：accessible 圏の compact 始域 slice の任意の小さい試験図式は内部余錐を持つ。
方針：quasicategory 試験に対して実際の正規化 compact 表示から先端を取り、全試験へ戻す。
規約：元の入力図式を保持し、全小余極限の存在を仮定しない。
使われ方：標準密度添字の小さい filtered 模型。 -/
lemma nonempty_compactSourceSlice_cocone_of_isKappaAccessible
    {μ : Cardinal.{u}} [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    {C : SSet.{u + 1}} [Quasicategory C] (hC : IsKappaAccessible μ C)
    (x : (Δ[0] : SSet.{u + 1}) ⟶ C)
    (K : SSet.{u}) (hK : IsKappaSmall μ K)
    (r : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ compactSourceSlice μ x) :
    Nonempty (JoinCocone r) := by
  apply nonempty_cocone_of_smallQuasicategory_tests hμ ?_ K hK r
  intro L hL hsmall j
  let P := fun v : (sliceOver x) _⦋0⦌ ↦
    Compact.IsKappaCompact.{u, u + 1} μ ((sliceOverProjection x).app (Opposite.op ⦋0⦌) v)
  let i := (fullSubcomplexOnVertices (sliceOver x) P).ι
  let U := j ≫ i
  let a := U ≫ sliceOverProjection x
  have ha : ∀ v, Compact.IsKappaCompact.{u, u + 1} μ (a.app (Opposite.op ⦋0⦌) v) := by
    intro v
    exact fullSubcomplexOnVertices_vertex (j.app (Opposite.op ⦋0⦌) v)
  obtain ⟨N⟩ := nonempty_compactInputPresentation_of_isKappaAccessible hμ hC hsmall a ha
    (sliceDiagramCocone U)
  letI := isFilteredInfinity_of_isKappaFiltered hμ.le N.index
  obtain ⟨v⟩ := nonempty_vertices_of_isFilteredInfinity N.index
  let w := N.diagram.app (Opposite.op ⦋0⦌) (ULift.up v)
  obtain ⟨c, hc⟩ := exists_sliceCocone_of_inputVertex U w
  have htip : P c.vertex := by
    change Compact.IsKappaCompact.{u, u + 1} μ
      ((sliceOverProjection x).app (Opposite.op ⦋0⦌) c.vertex)
    rw [hc]
    exact N.compact v
  exact ⟨fullSubcomplexCoconeLift P j c htip⟩

/-- 概要：compact 始域 slice の任意の指定小模型は同じ濃度で filtered。
方針：実際の accessible 入力余錐を小さい全同値模型へ移す。
規約：元の濃度を保ち、小模型の存在をこの補題には隠さない。
使われ方：標準左 Kan 添字の filtered 局所余極限。 -/
lemma compactSourceSlice_model_isKappaFiltered_of_isKappaAccessible
    {μ : Cardinal.{u}} [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    {C : SSet.{u + 1}} [Quasicategory C] (hC : IsKappaAccessible μ C)
    (x : (Δ[0] : SSet.{u + 1}) ⟶ C)
    {M : SSet.{u}} [Quasicategory M]
    (e : QCatEquivalence ((SSet.uliftFunctor.{u + 1, u}).obj M) (compactSourceSlice μ x)) :
    IsKappaFiltered μ M :=
  isKappaFiltered_of_small_tests_equivalence e (fun K hK r ↦
    nonempty_compactSourceSlice_cocone_of_isKappaAccessible hμ hC x K hK r)

end SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback
