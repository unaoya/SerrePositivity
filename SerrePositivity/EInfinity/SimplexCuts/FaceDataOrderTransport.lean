module

public import SerrePositivity.EInfinity.SimplexCuts.Faces
public import Mathlib.Data.Fintype.EquivFin

/-!
# 同じ色別順序列挙による元の指定面の移送

Berger–Fresse §2.2.6、M14 L12a の指定面の照合の補助。
元の順序列挙と頂点を保ち、等しい出力次数の添字だけを合わせる。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 同じ有限順序の同値は元の番号を保つ（BF §2.2.6 の列挙の補助）。 -/
lemma finiteOrderIso_val {N M : ℕ} (e : Fin N ≃o Fin M) (i : Fin N) : (e i).val = i.val := by
  have h : N = M := by simpa only [Fintype.card_fin] using Fintype.card_congr e.toEquiv
  subst M
  exact congrArg Fin.val (congrFun e.strictMono.eq_id i)

/-- 等しい有限次数の順序写像を、同じ番号の値で照合する（BF §2.2.6 の移送の補助）。 -/
lemma orderHom_heq_of_values {N M Q : ℕ} (f : Fin N →o Fin Q) (g : Fin M →o Fin Q)
    (h : N = M) (hv : ∀ i j, i.val = j.val → f i = g j) : HEq f g := by
  subst M
  apply heq_of_eq
  apply OrderHom.ext
  funext i
  exact hv i i rfl

/-- C451h：同じ色別位置の順序同値が元の頂点を保てば、次数と指定面も一致（BF §2.2.6）。 -/
lemma faceData_eq_of_colorOrderIso {m m' q r r' : ℕ} (s : Cut m q) (t : Cut m' q)
    (u : Surjection.Word r (m + 1)) (v : Surjection.Word r' (m' + 1)) (a : Fin r) (b : Fin r')
    (e : ↥(colorPositions s u.val a) ≃o ↥(colorPositions t v.val b))
    (hv : ∀ x, s.vertical x.val = t.vertical (e x).val) :
    (⟨outputDegree s u a, vertices s u a⟩ : Σ d : ℕ, Fin (d + 1) →o Fin (q + 1)) =
      ⟨outputDegree t v b, vertices t v b⟩ := by
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
