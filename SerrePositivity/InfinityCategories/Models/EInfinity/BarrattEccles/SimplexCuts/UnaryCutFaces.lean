module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.FaceDataOrderTransport
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.CutGeneratorFamilies
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.NullaryPointCaesuras
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.SignedTerms

/-!
模型。文献の定義との比較は後で
# 一文字単位の一般次元の指定面と符号

Berger–Fresse §2.2.6、M14 L13、報告 §384。
元の一色の順序列挙を全単体の恒等写像と比較する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
open _root_.CategoryTheory
open scoped _root_.Simplicial

/-- 同じ一色のCutの指定面は全単体の恒等（BF §2.2.6）。 -/
lemma unaryCut_faceData {q : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut 0 q) (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word 1 1) :
    (⟨_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s u 0, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vertices s u 0⟩ : Σ d : ℕ, Fin (d + 1) →o Fin (q + 1)) =
      ⟨q, OrderHom.id⟩ := by
  have hd : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s u 0 = q := by
    have H := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree_sum s u
    change (∑ a : Fin 1, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s u a) = 0 + q + 1 - 1 at H
    simpa only [Fin.sum_univ_one, Nat.zero_add, Nat.add_sub_cancel] using H
  have hn : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Nondegenerate s u.val := by
    intro i j hij
    apply s.vertex_injective
    apply Prod.ext
    · apply Fin.ext
      have hi := (s.horizontal i).isLt
      have hj := (s.horizontal j).isLt
      omega
    · have hv : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.pair s u.val i).2 = (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.pair s u.val j).2 := congrArg Prod.snd hij
      exact hv
  have hc : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositions s u.val 0).card = q + 1 :=
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositions_card_eq s u 0).trans (congrArg (fun n => n + 1) hd)
  apply Sigma.ext hd
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.orderHom_heq_of_values _ _ (congrArg (fun n => n + 1) hd)
  intro i j hij
  have he : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositions s u.val 0).orderEmbOfFin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositions_card_eq s u 0) i =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositions s u.val 0).orderEmbOfFin hc j :=
    Finset.orderEmbOfFin_eq_orderEmbOfFin_iff.mpr hij
  change s.vertical _ = j
  rw [he]
  exact congrFun (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.fullColorVertices_eq_id hn 0 hc) j

/-- 一文字のCutには逆転もcaesuraもなく元の符号は正（BF §2.2.6）。 -/
lemma unaryCut_sign {q : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut 0 q) (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word 1 1) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutSign s u.val = 1 := by
  have hcae : ¬_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura u.val (0 : Fin 1) :=
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.not_caesura_of_unique _ _ (fun (j : Fin 1) _ => by
      apply Fin.ext
      have hj := j.isLt
      omega)
  change (-1 : ℤ) ^
    ((∑ i : Fin 1, ∑ j : Fin 1, if i < j ∧ u.val j < u.val i
      then _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.intervalLength s u.val i * _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.intervalLength s u.val j else 0) +
      ∑ i : Fin 1, if _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura u.val i then _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi s i else 0) = 1
  simp only [Fin.sum_univ_one, lt_self_iff_false, false_and, ite_false, hcae, zero_add, pow_zero]

/-- 同じ指定面の生成元は元の全単体の生成元（BF §2.2.6）。 -/
lemma unaryCut_generatorFamily (A : Type u) [CommRing A] (S : SSet.{0}) {q : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut 0 q) (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word 1 1) (x : S _⦋q⦌) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutGeneratorFamily A S s u x = fun _ => ⟨q, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.gen A S q x⟩ := by
  funext a
  have ha : a = 0 := by apply Fin.ext; have h := a.isLt; omega
  subst a
  let F (f : Σ d : ℕ, Fin (d + 1) →o Fin (q + 1)) :
      Σ d : ℕ, (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S).X (-(d : ℤ)) :=
    ⟨f.1, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.gen A S f.1 (S.map (SimplexCategory.mkHom f.2).op x)⟩
  have H := congrArg F (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.unaryCut_faceData s u)
  change F ⟨_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s u 0, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vertices s u 0⟩ = ⟨q, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.gen A S q x⟩
  have hid : SimplexCategory.mkHom (OrderHom.id : Fin (q + 1) →o Fin (q + 1)) =
      𝟙 (⦋q⦌ : SimplexCategory) := rfl
  exact H.trans (by dsimp only [F]; rw [hid, op_id, S.map_id]; rfl)

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
