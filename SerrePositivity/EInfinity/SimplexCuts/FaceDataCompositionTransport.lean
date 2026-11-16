module

public import SerrePositivity.EInfinity.SimplexCuts.FaceDataOrderTransport

/-!
# 外側の指定面を通した同じ頂点列の移送

Berger–Fresse §2.2.6、M14 L12a のC451hの挿入色への証明分割。
元の全頂点の順序同値に沿い、同じ外側の面を合成する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 同じ順序列挙と指定頂点の合成は、元の指定面を保つ（BF §2.2.6）。 -/
lemma faceData_comp_eq_of_colorOrderIso {m m' q q' r r' : ℕ} (s : Cut m q) (t : Cut m' q')
    (u : Surjection.Word r (m + 1)) (v : Surjection.Word r' (m' + 1)) (a : Fin r) (b : Fin r')
    (ρ : Fin (q' + 1) →o Fin (q + 1))
    (e : ↥(colorPositions s u.val a) ≃o ↥(colorPositions t v.val b))
    (hv : ∀ x, s.vertical x.val = ρ (t.vertical (e x).val)) :
    (⟨outputDegree s u a, vertices s u a⟩ : Σ d : ℕ, Fin (d + 1) →o Fin (q + 1)) =
      ⟨outputDegree t v b, ρ.comp (vertices t v b)⟩ := by
  have hc : (colorPositions s u.val a).card = (colorPositions t v.val b).card := by
    simpa only [Fintype.card_coe] using Fintype.card_congr e.toEquiv
  have hd : outputDegree s u a = outputDegree t v b := congrArg (fun n : ℕ => n - 1) hc
  apply Sigma.ext hd
  apply orderHom_heq_of_values _ _ (congrArg (fun n : ℕ => n + 1) hd)
  intro i j hij
  let first := (colorPositions s u.val a).orderIsoOfFin (colorPositions_card_eq s u a)
  let last := (colorPositions t v.val b).orderIsoOfFin (colorPositions_card_eq t v b)
  let f := first.trans (e.trans last.symm)
  have he : f i = j := Fin.ext ((finiteOrderIso_val f i).trans hij)
  have hep : e (first i) = last j := by
    have h := congrArg last he
    change last (last.symm (e (first i))) = last j at h
    simpa only [OrderIso.apply_symm_apply] using h
  have hvertex := hv (first i)
  rw [hep] at hvertex
  exact hvertex


end SerrePositivity.EInfinity.SimplexCuts
