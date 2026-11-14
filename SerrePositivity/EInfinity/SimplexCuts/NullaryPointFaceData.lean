module

public import SerrePositivity.EInfinity.SimplexCuts.NullaryPointRelabel
public import SerrePositivity.EInfinity.SimplexCuts.FaceVertexLists

/-!
# 一点削除の前後の同じ出力次数と指定面

Berger–Fresse §2.2.6、M14 L12a、報告 §349。
残る全頂点列の一致を同じSigma型での次数・順序写像の厳密な一致へ戻す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 元の順序写像の全頂点列は、始域次数と写像を厳密に決める（BF §2.2.6）。 -/
lemma faceData_eq_of_vertexList {q : ℕ}
    (F G : Σ t : ℕ, Fin (t + 1) →o Fin (q + 1))
    (h : List.ofFn F.2 = List.ofFn G.2) : F = G := by
  rcases F with ⟨d, f⟩
  rcases G with ⟨e, g⟩
  have hdeg : d = e := Nat.add_right_cancel (by
    simpa only [List.length_ofFn] using congrArg List.length h)
  subst e
  apply congrArg (fun f : Fin (d + 1) →o Fin (q + 1) =>
    (⟨d, f⟩ : Σ t : ℕ, Fin (t + 1) →o Fin (q + 1)))
  apply OrderHom.ext
  funext i
  have he := congrArg (fun l : List (Fin (q + 1)) => l[i.val]?) h
  simpa only [List.getElem?_ofFn, i.isLt, dite_eq_left, Option.some.injEq] using he

/-- 一点削除の残り色の次数と同じ指定面は元のSigma型で一致（BF §2.2.6）。 -/
lemma nullaryPointEraseCut_faceData_relabel {m q r : ℕ} (s : Cut (m + 1) q)
    (v : Surjection.Word (r + 1) (m + 2)) (w : Surjection.Word r (m + 1))
    (p : Fin (m + 2)) (k : Fin (r + 1)) (hp : v.val p = k)
    (hpoint : hi s p = lo s p)
    (hv : ∀ i, k.succAbove (w.val i) = v.val (p.succAbove i)) (c : Fin r) :
    (⟨outputDegree (nullaryPointEraseCut s p) w c,
      vertices (nullaryPointEraseCut s p) w c⟩ : Σ t : ℕ, Fin (t + 1) →o Fin (q + 1)) =
      ⟨outputDegree s v (k.succAbove c), vertices s v (k.succAbove c)⟩ := by
  apply faceData_eq_of_vertexList
  change simplexVertexList (face (nullaryPointEraseCut s p) w c) =
    simplexVertexList (face s v (k.succAbove c))
  rw [simplexVertexList_face, simplexVertexList_face]
  exact nullaryPointEraseCut_verticesList_relabel s v.val w.val p k hp hpoint hv c

end SerrePositivity.EInfinity.SimplexCuts
