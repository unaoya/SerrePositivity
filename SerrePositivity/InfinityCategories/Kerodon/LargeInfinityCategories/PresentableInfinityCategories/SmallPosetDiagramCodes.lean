module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallPartialColimits
public import Mathlib.Logic.Equiv.Set

/-!
概要：小さい生成圏への μ-small κ-filtered poset 図式を、一つの宇宙 u の族で符号化する。
方針：μ.out 内の部分集合へ台集合を全単射で移し、順序と全単体の図式を輸送する。
規約：図式の値や射を忘れず、元の nerve との厳密な同型と因子化等式を提供する。
使われ方：対象に依存しない小さい μ-compact 生成族の添字。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 同じ順序同型を全単体へ作用させた nerve の同型。 -/
def nerveOrderIso {I J : Type u} [Preorder I] [Preorder J] (e : I ≃o J) :
    nerve I ≅ nerve J where
  hom := nerveMap e.monotone.functor
  inv := nerveMap e.symm.monotone.functor
  hom_inv_id := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    exact ComposableArrows.ext (fun _ ↦ e.symm_apply_apply _) (fun _ _ ↦ Subsingleton.elim _ _)
  inv_hom_id := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    exact ComposableArrows.ext (fun _ ↦ e.apply_symm_apply _) (fun _ _ ↦ Subsingleton.elim _ _)

/-- 全ての小さい filtered poset 図式を表現する、元の小さい宇宙内の符号型。 -/
structure SmallPosetDiagramCode (κ μ : Cardinal.{u}) [Fact κ.IsRegular]
    (A : SSet.{u}) where
  carrier : Set μ.out
  order : PartialOrder carrier
  small : HasCardinalLT carrier μ
  filtered : letI := order; IsCardinalFiltered carrier κ
  diagram : letI := order; nerve carrier ⟶ A

namespace SmallPosetDiagramCode
variable {κ μ : Cardinal.{u}} [Fact κ.IsRegular] {A : SSet.{u}}

/-- 符号化された元の小さい poset。 -/
abbrev Index (q : SmallPosetDiagramCode κ μ A) := q.carrier

instance (q : SmallPosetDiagramCode κ μ A) : PartialOrder q.Index := q.order

/-- 元の全図式を保持する、符号化された nerve 図式。 -/
def map (q : SmallPosetDiagramCode κ μ A) : nerve q.Index ⟶ A := q.diagram

/-- 全 coherent な試験図式について、符号の添字は κ-filtered。 -/
lemma nerve_isKappaFiltered (q : SmallPosetDiagramCode κ μ A) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered κ (nerve q.Index) := by
  have := q.filtered
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.isKappaFiltered_nerve_of_cardinalFiltered _

end SmallPosetDiagramCode

/-- 任意の元の μ-small κ-filtered poset 図式を、同じ全単体を保つ小さい符号へ戻す。 -/
lemma exists_smallPosetDiagramCode {κ μ : Cardinal.{u}} [Fact κ.IsRegular]
    {A : SSet.{u}} (I : Type u) [PartialOrder I] [IsCardinalFiltered I κ]
    (hI : HasCardinalLT I μ) (D : nerve I ⟶ A) :
    ∃ q : SmallPosetDiagramCode κ μ A, ∃ e : nerve I ≅ nerve q.Index,
      e.hom ≫ q.map = D := by
  obtain ⟨f⟩ : Nonempty (I ↪ μ.out) := by
    apply (Cardinal.le_def I μ.out).mp
    rw [Cardinal.mk_out]
    exact le_of_lt ((hasCardinalLT_iff_cardinal_mk_lt I μ).mp hI)
  let t := Equiv.ofInjective f f.injective
  let o : PartialOrder (Set.range f) := PartialOrder.lift t.symm t.symm.injective
  let := o
  let e : I ≃o Set.range f :=
    { t with map_rel_iff' := by intro i j; change t.symm (t i) ≤ t.symm (t j) ↔ i ≤ j; simp }
  let n := nerveOrderIso e
  have hs : HasCardinalLT (Set.range f) μ :=
    (hasCardinalLT_iff_of_equiv t μ).mp hI
  have hf : IsCardinalFiltered (Set.range f) κ :=
    IsCardinalFiltered.of_equivalence κ e.equivalence
  refine ⟨⟨Set.range f, o, hs, hf, n.inv ≫ D⟩, n, ?_⟩
  exact Iso.hom_inv_id_assoc n D

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
