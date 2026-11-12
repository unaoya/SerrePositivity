module
public import SerrePositivity.KST.Fibration.WeakStringInitialPullback
public import SerrePositivity.KST.Fibration.SimplicialInitialPullback
public import SerrePositivity.KST.Fibration.WeakStringRelativeMultiPostcomp

/-! # 先頭を保つ全再添字と Verdier 包含の元のホモトピー引き戻し -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.Comparison
namespace SerrePositivity.KST.Fibration

/-- 初期頂点を保つ全単体作用素の元の自然性四角形は、全正反復で homotopy pullback。 -/
theorem weakStringMultiPostcomp_headPreserving_homotopyPullback
    {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
    (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) (r : ℕ) {m n : ℕ}
    (θ : ⦋m⦌ ⟶ ⦋n⦌) (hθ : θ.toOrderHom 0 = 0) :
    IsHomotopyPullback (CommSq.mk
      ((weakStringMultiPostcomp i q (r + 1)).naturality θ.op)) := by
  apply simplicialInitialComparison_head_homotopyPullback (weakStringMultiPostcomp i q (r + 1))
    ((multiRealizationFunctor (r + 1)).map (topPostExact i))
    (fun n => (multiRealizationFunctor (r + 1)).map
      (weakStringVertexTopExact (i ≫ q : A ⟶ C) n 0))
    (fun n => (multiRealizationFunctor (r + 1)).map (weakStringVertexTopExact q n 0))
    (fun n => weakStringInitialPostSquare i q n.len (r + 1))
    (fun n => weakStringInitialPostSquare_homotopyPullback h n.len r) θ
  · change (multiRealizationFunctor (r + 1)).map
      (weakStringExactMap (i ≫ q : A ⟶ C) θ) ≫
        (multiRealizationFunctor (r + 1)).map
          (weakStringVertexTopExact (i ≫ q : A ⟶ C) ⦋m⦌ 0) = _
    rw [← Functor.map_comp, weakStringVertexTopExact_reindex, hθ]
  · change (multiRealizationFunctor (r + 1)).map (weakStringExactMap q θ) ≫
      (multiRealizationFunctor (r + 1)).map (weakStringVertexTopExact q ⦋m⦌ 0) = _
    rw [← Functor.map_comp, weakStringVertexTopExact_reindex, hθ]

end SerrePositivity.KST.Fibration
