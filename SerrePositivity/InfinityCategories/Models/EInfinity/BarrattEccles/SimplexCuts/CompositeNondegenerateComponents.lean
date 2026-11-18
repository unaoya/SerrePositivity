module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.CompositeFaceComparison

/-!
模型。文献の定義との比較は後で
# 元の合成切断の非退化性の二段の面による検査

Berger–Fresse §2.2.6、M14 L12a のC453の証明分割。
同じ指定面のSigmaの等式に沿って、面の単射性を移す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
open _root_.CategoryTheory

/-- 二段の元の切断が非退化なら、同じ合成切断も非退化（BF §2.2.6）。 -/
lemma positiveCompositeCut_nondegenerate_of_nested {m n d e q : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.PositiveCompositeCutIndex u v k q)
    (hOuter : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Nondegenerate (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeOuterCut u v k c) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord u).val)
    (hInner : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Nondegenerate (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeInnerCut u v k c) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord v).val) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Nondegenerate c.2 (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeCutWord u v k c.1).val := by
  apply (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.faces_mono_iff _ _).mp
  intro a
  apply SimplexCategory.mono_iff_injective.mpr
  obtain ⟨s, hs⟩ := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInsertionEquiv m (n + 1) k).symm.surjective a
  rw [← hs]
  cases s with
  | inl b =>
    have he := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveComposite_remaining_face u v k c b
    have hp := congrArg (fun f : Σ t : ℕ, Fin (t + 1) →o Fin (q + 1) =>
      Function.Injective f.2) he
    exact hp.mp (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vertices_strictMono hOuter b.val).injective
  | inr b =>
    have he := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveComposite_inserted_face u v k c b
    have hp := congrArg (fun f : Σ t : ℕ, Fin (t + 1) →o Fin (q + 1) =>
      Function.Injective f.2) he
    exact hp.mpr ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vertices_strictMono hOuter k).injective.comp
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vertices_strictMono hInner b).injective)

/-- 元の合成切断が非退化なら、同じ内側切断は非退化（BF §2.2.6）。 -/
lemma positiveCompositeCut_inner_nondegenerate {m n d e q : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.PositiveCompositeCutIndex u v k q)
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Nondegenerate c.2 (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeCutWord u v k c.1).val) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Nondegenerate (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeInnerCut u v k c) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord v).val := by
  apply (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.faces_mono_iff _ _).mp
  intro b
  apply SimplexCategory.mono_iff_injective.mpr
  have he := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveComposite_inserted_face u v k c b
  have hp := congrArg (fun f : Σ t : ℕ, Fin (t + 1) →o Fin (q + 1) =>
    Function.Injective f.2) he
  have hc := hp.mp (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vertices_strictMono h (_root_.SerrePositivity.EInfinity.BarrattEccles.insertedPosition m (n + 1) k b)).injective
  intro i j hij
  apply hc
  exact congrArg (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vertices (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeOuterCut u v k c) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord u) k) hij

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
