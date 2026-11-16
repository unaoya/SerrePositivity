module

public import SerrePositivity.EInfinity.SimplexCuts.FaceDataOrderTransport
public import SerrePositivity.EInfinity.SimplexCuts.CutGeneratorFamilies
public import SerrePositivity.EInfinity.SimplexCuts.NullaryPointCaesuras
public import SerrePositivity.EInfinity.SimplexCuts.SignedTerms

/-!
# 一文字単位の一般次元の指定面と符号

Berger–Fresse §2.2.6、M14 L13、報告 §384。
元の一色の順序列挙を全単体の恒等写像と比較する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory
open scoped Simplicial

/-- 同じ一色のCutの指定面は全単体の恒等（BF §2.2.6）。 -/
lemma unaryCut_faceData {q : ℕ} (s : Cut 0 q) (u : Surjection.Word 1 1) :
    (⟨outputDegree s u 0, vertices s u 0⟩ : Σ d : ℕ, Fin (d + 1) →o Fin (q + 1)) =
      ⟨q, OrderHom.id⟩ := by
  have hd : outputDegree s u 0 = q := by
    have H := outputDegree_sum s u
    change (∑ a : Fin 1, outputDegree s u a) = 0 + q + 1 - 1 at H
    simpa only [Fin.sum_univ_one, Nat.zero_add, Nat.add_sub_cancel] using H
  have hn : Nondegenerate s u.val := by
    intro i j hij
    apply s.vertex_injective
    apply Prod.ext
    · apply Fin.ext
      have hi := (s.horizontal i).isLt
      have hj := (s.horizontal j).isLt
      omega
    · have hv : (pair s u.val i).2 = (pair s u.val j).2 := congrArg Prod.snd hij
      exact hv
  have hc : (colorPositions s u.val 0).card = q + 1 :=
    (colorPositions_card_eq s u 0).trans (congrArg (fun n => n + 1) hd)
  apply Sigma.ext hd
  apply orderHom_heq_of_values _ _ (congrArg (fun n => n + 1) hd)
  intro i j hij
  have he : (colorPositions s u.val 0).orderEmbOfFin (colorPositions_card_eq s u 0) i =
      (colorPositions s u.val 0).orderEmbOfFin hc j :=
    Finset.orderEmbOfFin_eq_orderEmbOfFin_iff.mpr hij
  change s.vertical _ = j
  rw [he]
  exact congrFun (fullColorVertices_eq_id hn 0 hc) j

/-- 一文字のCutには逆転もcaesuraもなく元の符号は正（BF §2.2.6）。 -/
lemma unaryCut_sign {q : ℕ} (s : Cut 0 q) (u : Surjection.Word 1 1) : cutSign s u.val = 1 := by
  have hcae : ¬Surjection.Caesura u.val (0 : Fin 1) :=
    not_caesura_of_unique _ _ (fun (j : Fin 1) _ => by
      apply Fin.ext
      have hj := j.isLt
      omega)
  change (-1 : ℤ) ^
    ((∑ i : Fin 1, ∑ j : Fin 1, if i < j ∧ u.val j < u.val i
      then intervalLength s u.val i * intervalLength s u.val j else 0) +
      ∑ i : Fin 1, if Surjection.Caesura u.val i then hi s i else 0) = 1
  simp only [Fin.sum_univ_one, lt_self_iff_false, false_and, ite_false, hcae, zero_add, pow_zero]

/-- 同じ指定面の生成元は元の全単体の生成元（BF §2.2.6）。 -/
lemma unaryCut_generatorFamily (A : Type u) [CommRing A] (S : SSet.{0}) {q : ℕ}
    (s : Cut 0 q) (u : Surjection.Word 1 1) (x : S _⦋q⦌) :
    cutGeneratorFamily A S s u x = fun _ => ⟨q, gen A S q x⟩ := by
  funext a
  have ha : a = 0 := by apply Fin.ext; have h := a.isLt; omega
  subst a
  let F (f : Σ d : ℕ, Fin (d + 1) →o Fin (q + 1)) :
      Σ d : ℕ, (chains A S).X (-(d : ℤ)) :=
    ⟨f.1, gen A S f.1 (S.map (SimplexCategory.mkHom f.2).op x)⟩
  have H := congrArg F (unaryCut_faceData s u)
  change F ⟨outputDegree s u 0, vertices s u 0⟩ = ⟨q, gen A S q x⟩
  have hid : SimplexCategory.mkHom (OrderHom.id : Fin (q + 1) →o Fin (q + 1)) =
      𝟙 (⦋q⦌ : SimplexCategory) := rfl
  exact H.trans (by dsimp only [F]; rw [hid, op_id, S.map_id]; rfl)

end SerrePositivity.EInfinity.SimplexCuts
