module
public import SerrePositivity.HomotopicalAlgebra.Diagram.BousfieldKanSimplex
public import Mathlib.AlgebraicTopology.SimplicialSet.Degenerate

/-!
概要：BK単体の退化性は、最後の射を除いた元の射列の退化性そのもの。
方針：忘却は退化を保ち、逆向きは同じ退化と面によって最後の構造射を固定して復元。
規約：IS-W2 R03aの自由境界細胞の証明分割。圏の射が単射とは仮定しない。
使われ方：非退化な射列で添字付けた自由図式の細胞。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DiagramModel.BousfieldKanCells
open CategoryTheory Limits SSet
open scoped Simplicial
variable (I : Type u) [SmallCategory I]

/-- 台の射列が一つの退化の像なら、同じ面と退化でover射列自体を復元できる。 -/
theorem sigma_delta_eq_of_base {n : ℕ} {i : I}
    (s : ComposableArrows (Over i) (n+1)) (k : Fin (n+1))
    (t : ComposableArrows I n)
    (ht : (nerve I).σ k t = s ⋙ Over.forget i) :
    (nerve (Over i)).σ k ((nerve (Over i)).δ k.castSucc s) = s := by
  apply (simplexEquiv I (n+1) i).injective
  refine Sigma.ext ?_ ?_
  · change (nerve I).σ k ((nerve I).δ k.castSucc (s ⋙ Over.forget i)) = _
    rw [← ht]
    have hd : (nerve I).δ k.castSucc ((nerve I).σ k t) = t := by
      simpa only [← ConcreteCategory.comp_apply, SimplicialObject.δ_comp_σ_self,
        ConcreteCategory.id_apply]
    rw [hd]
    exact ht
  · change HEq
      (((nerve (Over i)).σ k ((nerve (Over i)).δ k.castSucc s)).obj
        (Fin.last (n+1))).hom (s.obj (Fin.last (n+1))).hom
    have hl : k.castSucc.succAbove (k.predAbove (Fin.last (n+1))) = Fin.last (n+1) := by
      rw [Fin.predAbove_right_last,
        Fin.succAbove_ne_last_last (Fin.castSucc_ne_last k)]
    simp only [nerve.σ_obj, nerve.δ_obj]
    rw [hl]

/-- BK重みの単体は、台の元の射列が退化のときに限り退化。 -/
theorem degenerate_iff_base {n : ℕ} {i : I}
    (s : ComposableArrows (Over i) n) :
    s ∈ (nerve (Over i)).degenerate n ↔
      (s ⋙ Over.forget i) ∈ (nerve I).degenerate n := by
  constructor
  · intro hs
    exact SSet.degenerate_app_apply hs (nerveMap (Over.forget i))
  · intro hs
    cases n with
    | zero => simpa only [SSet.degenerate_zero, Set.mem_empty_iff_false] using hs
    | succ n =>
      rw [SSet.degenerate_eq_iUnion_range_σ] at hs ⊢
      obtain ⟨k, t, ht⟩ := Set.mem_iUnion.mp hs
      exact Set.mem_iUnion.mpr ⟨k, ⟨(nerve (Over i)).δ k.castSucc s,
        sigma_delta_eq_of_base I s k t ht⟩⟩

/-- 非退化なBK単体の自由細胞の添字は、同じ非退化な台の射列。 -/
theorem nondegenerate_iff_base {n : ℕ} {i : I}
    (s : ComposableArrows (Over i) n) :
    s ∈ (nerve (Over i)).nonDegenerate n ↔
      (s ⋙ Over.forget i) ∈ (nerve I).nonDegenerate n :=
  not_congr (degenerate_iff_base I s)

end SerrePositivity.DiagramModel.BousfieldKanCells
