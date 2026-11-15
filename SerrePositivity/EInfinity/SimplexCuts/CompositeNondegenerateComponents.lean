module

public import SerrePositivity.EInfinity.SimplexCuts.CompositeFaceComparison

/-!
# 元の合成切断の非退化性の二段の面による検査

Berger–Fresse §2.2.6、M14 L12a のC453の証明分割。
同じ指定面のSigmaの等式に沿って、面の単射性を移す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory

/-- 二段の元の切断が非退化なら、同じ合成切断も非退化（BF §2.2.6）。 -/
lemma positiveCompositeCut_nondegenerate_of_nested {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q)
    (hOuter : Nondegenerate (positiveCompositeOuterCut u v k c) (positiveWord u).val)
    (hInner : Nondegenerate (positiveCompositeInnerCut u v k c) (positiveWord v).val) :
    Nondegenerate c.2 (positiveCompositeCutWord u v k c.1).val := by
  apply (faces_mono_iff _ _).mp
  intro a
  apply SimplexCategory.mono_iff_injective.mpr
  obtain ⟨s, hs⟩ := (operadInsertionEquiv m (n + 1) k).symm.surjective a
  rw [← hs]
  cases s with
  | inl b =>
    have he := positiveComposite_remaining_face u v k c b
    have hp := congrArg (fun f : Σ t : ℕ, Fin (t + 1) →o Fin (q + 1) =>
      Function.Injective f.2) he
    exact hp.mp (vertices_strictMono hOuter b.val).injective
  | inr b =>
    have he := positiveComposite_inserted_face u v k c b
    have hp := congrArg (fun f : Σ t : ℕ, Fin (t + 1) →o Fin (q + 1) =>
      Function.Injective f.2) he
    exact hp.mpr ((vertices_strictMono hOuter k).injective.comp
      (vertices_strictMono hInner b).injective)

/-- 元の合成切断が非退化なら、同じ内側切断は非退化（BF §2.2.6）。 -/
lemma positiveCompositeCut_inner_nondegenerate {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q)
    (h : Nondegenerate c.2 (positiveCompositeCutWord u v k c.1).val) :
    Nondegenerate (positiveCompositeInnerCut u v k c) (positiveWord v).val := by
  apply (faces_mono_iff _ _).mp
  intro b
  apply SimplexCategory.mono_iff_injective.mpr
  have he := positiveComposite_inserted_face u v k c b
  have hp := congrArg (fun f : Σ t : ℕ, Fin (t + 1) →o Fin (q + 1) =>
    Function.Injective f.2) he
  have hc := hp.mp (vertices_strictMono h (BarrattEccles.insertedPosition m (n + 1) k b)).injective
  intro i j hij
  apply hc
  exact congrArg (vertices (positiveCompositeOuterCut u v k c) (positiveWord u) k) hij

end SerrePositivity.EInfinity.SimplexCuts
