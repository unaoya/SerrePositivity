module
public import SerrePositivity.KST.Fibration.WeakStringInitialPullback
public import SerrePositivity.KST.Fibration.PullbackCancellation
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
    {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}
    (h : IsVerdierSequence i q) (r : ℕ) {m n : ℕ}
    (θ : ⦋m⦌ ⟶ ⦋n⦌) (hθ : θ.toOrderHom 0 = 0) :
    IsHomotopyPullback (CommSq.mk
      ((weakStringMultiPostcomp i q (r + 1)).naturality θ.op)) := by
  let s : CommSq
      ((multiRealizationFunctor (r + 1)).map (weakStringExactMap (i ≫ q : A ⟶ C) θ))
      ((multiRealizationFunctor (r + 1)).map (weakStringPostExact i q ⦋n⦌))
      ((multiRealizationFunctor (r + 1)).map (weakStringPostExact i q ⦋m⦌))
      ((multiRealizationFunctor (r + 1)).map (weakStringExactMap q θ)) := by
    constructor
    rw [← Functor.map_comp, ← Functor.map_comp, weakStringPostExact_reindex]
  let t := weakStringInitialPostSquare i q m (r + 1)
  have ha : (multiRealizationFunctor (r + 1)).map
      (weakStringExactMap (i ≫ q : A ⟶ C) θ) ≫
        (multiRealizationFunctor (r + 1)).map
          (weakStringVertexTopExact (i ≫ q : A ⟶ C) ⦋m⦌ 0) =
      (multiRealizationFunctor (r + 1)).map
        (weakStringVertexTopExact (i ≫ q : A ⟶ C) ⦋n⦌ 0) := by
    rw [← Functor.map_comp, weakStringVertexTopExact_reindex, hθ]
  have hb : (multiRealizationFunctor (r + 1)).map (weakStringExactMap q θ) ≫
        (multiRealizationFunctor (r + 1)).map (weakStringVertexTopExact q ⦋m⦌ 0) =
      (multiRealizationFunctor (r + 1)).map (weakStringVertexTopExact q ⦋n⦌ 0) := by
    rw [← Functor.map_comp, weakStringVertexTopExact_reindex, hθ]
  have hout : IsHomotopyPullback (s.horiz_comp t) := by
    apply (isHomotopyPullback_iff_of_localized_isIso (s.horiz_comp t)
      (weakStringInitialPostSquare i q n (r + 1)) (𝟙 _) (𝟙 _) (𝟙 _) (𝟙 _)
      ?_ ?_ ?_ ?_ (by infer_instance) (by infer_instance)
      (by infer_instance) (by infer_instance)).mpr
    · exact weakStringInitialPostSquare_homotopyPullback h n r
    · simpa only [Category.comp_id, Category.id_comp] using ha
    · simp only [Category.comp_id, Category.id_comp]
    · simp only [Category.comp_id, Category.id_comp]
    · simpa only [Category.comp_id, Category.id_comp] using hb
  exact isHomotopyPullback_left_of_horiz s t hout
    (weakStringInitialPostSquare_homotopyPullback h m r)

end SerrePositivity.KST.Fibration
