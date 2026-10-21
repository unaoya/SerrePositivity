module
public import SerrePositivity.InfinityCategories.Derived.DGNerveSelectedCutRhsSum
public import SerrePositivity.InfinityCategories.Derived.DGTensorFiniteSums
public import SerrePositivity.InfinityCategories.Derived.DGNerveCutRhsBoundarySum
/-!
概要：各 tensor 切断項の実微分を、選択点と未選択点の二つの有限和へ展開する。
方針：元の HA 項、選択点の有限和、第二切断合成の実微分の同定を使う。
規約：同じ実 cochain を使う。使われ方：tensor 候補の全 HA の有限和の相殺。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
open scoped BigOperators
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D]
/-- 元の実成分の微分と有限和の照合。 -/
lemma dgNerveTensorCutTerm_differential_normal (B : Type v) (C : Type w)
    [DGCategory R B] [DGCategory R C] {n : ℕ} (s : Simplex R B n) (t : Simplex R C n)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (S : Finset (Fin (n + 1)))
    (k : ℤ) (hk : k = 2 - (I.card : ℤ)) (hI : 2 ≤ I.card)
    (ha : IsLeast (I : Set (Fin (n + 1))) a) (hb : IsGreatest (I : Set (Fin (n + 1))) b)
    (hc : ∀ j ∈ S, j ∈ I ∧ a < j ∧ j < b) (hab : a < b) :
    differential R (dgNerveTensorCutTerm R B C s.toSimplexData t.toSimplexData
      I a b S k hk hI ha hb hc) =
    (dgNerveTensorCutSign I a b S).negOnePow •
      ((∑ j : S, dgTensorElement R
        (x := ((s.obj a, t.obj a) : DGTensorCategory R B C))
        (y := ((s.obj b, t.obj b) : DGTensorCategory R B C))
        (dgNerveSelectedCutTerm R B s.toSimplexData a b S hab
          (fun x hx => (hc x hx).2) j.val j.property)
        (dgNerveCutProduct R C t.toSimplexData I a b S hI ha hb hc) (by omega)) +
      (-(S.card : ℤ)).negOnePow • ∑ j : I, dgTensorElement R
        (x := ((s.obj a, t.obj a) : DGTensorCategory R B C))
        (y := ((s.obj b, t.obj b) : DGTensorCategory R B C))
        (dgNerveSelectedCutHom R B s.toSimplexData a b S hab (fun x hx => (hc x hx).2))
        (if h : a < j.val ∧ j.val < b ∧ j.val ∉ S then
          dgNerveCutBoundaryTerm R C t.toSimplexData I a b S j.val
            (2 - (I.card : ℤ) + (S.card : ℤ)) rfl ha hb hc j.property h.1 h.2.1 h.2.2
          else 0) (by omega)) := by
  rw [dgNerveTensorCutTerm_differential R B C s t I a b S k hk hI ha hb hc hab,
    dgNerveSelectedCutRhs_eq_sum, dgNerveCutRhs_eq_boundarySum]
  unfold dgNerveCutBoundarySum
  rw [dgTensorElement_sum_left R B C, dgTensorElement_sum_right R B C]
end SerrePositivity.InfinityCategories
