module

public import SerrePositivity.InfinityCategories.F2.Ind.CodiscreteConeLabels

/-!
概要：未使用の頂点ラベルは、同じ錐の各単体の左右の切断を決定する。
方針：各頂点の新しいラベルへの所属を、join の切断の逆像の公式で判定する。
規約：元の全単体で成り立つ。頂点の新しさだけで単射性を仮定しない。
使われ方：元の部分複体への単射な包含から、同じ錐の写像の単射性を示す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {K : SSet.{u}} {T : Type u}

/-- 同じ錐の単体の指定された頂点。 -/
def coneSimplexVertex {n : ℕ} (s : (join K (Δ[0] : SSet.{u})) _⦋n⦌)
    (i : Fin (n + 1)) : (join K (Δ[0] : SSet.{u})) _⦋0⦌ :=
  (join K Δ[0]).map (SimplexCategory.const ⦋0⦌ ⦋n⦌ i).op s

/-- 指定した頂点が右側に属するのは、元の切断以降の頂点であるときに限る。 -/
lemma coneSimplexVertex_cut {n : ℕ} (s : (join K (Δ[0] : SSet.{u})) _⦋n⦌)
    (i : Fin (n + 1)) : (coneSimplexVertex s i).1.val = 0 ↔ s.1.val ≤ i.val := by
  let α := (SimplexCategory.const ⦋0⦌ ⦋n⦌ i).toOrderHom
  change Join.pullCut α s.1.val = 0 ↔ _
  have h := Join.lt_pullCut_iff α s.1.val (0 : Fin 1)
  have hb := Join.pullCut_le α s.1.val
  change 0 < Join.pullCut α s.1.val ↔ i.val < s.1.val at h
  omega

/-- 未使用ラベルを持つのは、同じ錐の右頂点に限る。 -/
lemma coneVertexLabels_eq_apex_iff (f : K _⦋0⦌ → T) (a : T)
    (ha : ∀ x, f x ≠ a) (s : (join K (Δ[0] : SSet.{u})) _⦋0⦌) :
    coneVertexLabels f a s = a ↔ s.1.val = 0 := by
  unfold coneVertexLabels
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => rfl⟩
  · exact ⟨fun he => False.elim (ha _ he), fun hz => False.elim (h hz)⟩

/-- 同じラベル付き錐写像の像が等しい二つの単体は、同じ切断を持つ。 -/
lemma codiscreteConeLabelMap_cut {n : ℕ} (f : K ⟶ nerve (Codiscrete T)) (a : T)
    (ha : ∀ x : K _⦋0⦌, (nerveEquiv (f.app _ x)).as ≠ a)
    {s t : (join K (Δ[0] : SSet.{u})) _⦋n⦌}
    (h : (codiscreteConeLabelMap f a).app _ s = (codiscreteConeLabelMap f a).app _ t) :
    s.1 = t.1 := by
  apply Fin.ext
  apply Join.cut_ext (Nat.le_of_lt_succ s.1.isLt) (Nat.le_of_lt_succ t.1.isLt)
  intro i
  have hv := congrArg (fun q : (nerve (Codiscrete T)) _⦋n⦌ => (q.obj i).as) h
  let b : K _⦋0⦌ → T := fun x => (nerveEquiv (f.app _ x)).as
  change coneVertexLabels b a (coneSimplexVertex s i) =
    coneVertexLabels b a (coneSimplexVertex t i) at hv
  have hi : coneVertexLabels b a (coneSimplexVertex s i) = a ↔
      coneVertexLabels b a (coneSimplexVertex t i) = a := by rw [hv]
  rw [coneVertexLabels_eq_apex_iff _ _ ha, coneSimplexVertex_cut,
    coneVertexLabels_eq_apex_iff _ _ ha, coneSimplexVertex_cut] at hi
  omega

end SerrePositivity.InfinityCategories.F2.Ind
