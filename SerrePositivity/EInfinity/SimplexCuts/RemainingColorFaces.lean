module

public import SerrePositivity.EInfinity.SimplexCuts.ColorPathTransport
public import SerrePositivity.EInfinity.SimplexCuts.RemainingWordPositions
public import SerrePositivity.EInfinity.SimplexCuts.CompositeOuterEndpoints

/-!
# 元の残り色の指定面は同じ合成切断で一致する

Berger–Fresse §2.2.6、M14 L12a のC451の残り色の成分。
区間内の全頂点の順序を保ち、同じSigma型の中で指定面を比較する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 元の残り色の面と、同じ合成語での面は厳密に一致（BF §2.2.6）。 -/
lemma positiveComposite_remaining_face {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q)
    (a : {a : Fin (m + 1) // a ≠ k}) :
    (⟨outputDegree (positiveCompositeOuterCut u v k c) (positiveWord u) a.val,
       vertices (positiveCompositeOuterCut u v k c) (positiveWord u) a.val⟩ :
        Σ t : ℕ, Fin (t + 1) →o Fin (q + 1)) =
      ⟨outputDegree c.2 (positiveCompositeCutWord u v k c.1)
          (BarrattEccles.remainingPosition m (n + 1) k a),
       vertices c.2 (positiveCompositeCutWord u v k c.1)
          (BarrattEccles.remainingPosition m (n + 1) k a)⟩ := by
  let epos := remainingWordPositionOrderIso u v k c.1 a
  have hl : ∀ p, lo (positiveCompositeOuterCut u v k c) p.val = lo c.2 (epos p).val := by
    intro p
    exact (positiveCompositeOuterCut_endpoints u v k c p.val).1
  have hr : ∀ p, hi (positiveCompositeOuterCut u v k c) p.val = hi c.2 (epos p).val := by
    intro p
    have hp : (positiveWord u).val p.val ≠ k := by
      have he : (positiveWord u).val p.val = a.val := (Finset.mem_filter.mp p.property).2
      exact fun h => a.property (he.symm.trans h)
    have heq := compositeFirstPosition_eq_last_of_non_slot u v k c.1 p.val hp
    exact (positiveCompositeOuterCut_endpoints u v k c p.val).2.trans
      (congrArg (hi c.2) heq.symm)
  exact faceData_eq_of_colorOrderIso _ _ _ _ _ _
    (colorPathOrderIso _ _ _ _ _ _ epos hl hr)
    (fun x => (colorPathOrderIso_vertical _ _ _ _ _ _ epos hl hr x).symm)

end SerrePositivity.EInfinity.SimplexCuts
