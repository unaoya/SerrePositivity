module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.TerminalCarrierBoundary

/-!
概要：一つの鎖の上にある単体は、その鎖の最後の部分複体に収まる。
方針：各制限の最後の添字を全体の最後の添字で上から押さえる。
規約：元の射影の等式を用い、像の部分複体を別のものへ置き換えない。
使われ方：境界を最後の部分複体内で充填する準備。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
variable {I : Type u} [Preorder I] {X : SSet.{u}}

/-- 全制限の条件は、同じ元の単体の最後の部分複体への所属を含む。 -/
lemma terminalCarrierCondition_mem_last {A : I → X.Subcomplex} {z : I → X _⦋0⦌}
    {n : SimplexCategory} {x : X.obj (Opposite.op n)} {s : (nerve I).obj (Opposite.op n)}
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.terminalCarrierCondition A z x s) :
    x ∈ (A (s.obj (Fin.last n.len))).obj (Opposite.op n) := by
  have hh := h.1 n (𝟙 n)
  change X.map (𝟙 _) x ∈ (A (s.obj (Fin.last n.len))).obj _ at hh
  simpa only [CategoryTheory.Functor.map_id_apply] using hh

/-- 標準単体からの同じ鎖の全ての値は、元の最後の添字以下。 -/
lemma nerveHom_value_le_last {n : ℕ} (q : (Δ[n] : SSet.{u}) ⟶ nerve I)
    {m : SimplexCategory} (t : (Δ[n] : SSet.{u}).obj (Opposite.op m)) :
    (q.app _ t).obj (Fin.last m.len) ≤ (SSet.yonedaEquiv q).obj (Fin.last n) := by
  have hq : SSet.yonedaEquiv.symm (SSet.yonedaEquiv q) = q :=
    SSet.yonedaEquiv.symm_apply_apply q
  conv_lhs => rw [← hq, SSet.yonedaEquiv_symm_app]
  change (SSet.yonedaEquiv q).obj ((stdSimplex.objEquiv t).toOrderHom (Fin.last m.len)) ≤ _
  exact leOfHom ((SSet.yonedaEquiv q).map (homOfLE (Fin.le_last _)))

/-- 同じ鎖の上の図式の値は、最後の部分複体に因子分解する。 -/
lemma terminalCarrierValue_range_le {A : I → X.Subcomplex} {z : I → X _⦋0⦌}
    (hA : Monotone A) {K : SSet.{u}} {n : ℕ}
    (b : K ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.terminalCarrier A z).toSSet) (r : K ⟶ Δ[n])
    (q : (Δ[n] : SSet.{u}) ⟶ nerve I)
    (h : b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.terminalCarrierProjection A z = r ≫ q) :
    Subcomplex.range (b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.terminalCarrierValue A z) ≤
      A ((SSet.yonedaEquiv q).obj (Fin.last n)) := by
  intro m x hx
  obtain ⟨y, rfl⟩ := hx
  let e := b.app m y
  have he : e.val.2 = q.app m (r.app m y) :=
    congrArg (fun a : K ⟶ nerve I => a.app m y) h
  have hindex : e.val.2.obj (Fin.last m.unop.len) ≤
      (SSet.yonedaEquiv q).obj (Fin.last n) := by
    rw [he]
    exact nerveHom_value_le_last q _
  exact (hA hindex) _ (terminalCarrierCondition_mem_last e.property)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
