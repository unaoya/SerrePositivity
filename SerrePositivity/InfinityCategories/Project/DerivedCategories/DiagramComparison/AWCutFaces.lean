module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StandardTopBoundary
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AWAssocTerms
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AlexanderWhitney

/-!
概要：AWの前面・後面の最上位成分を同じ切断集合の成分へ同定する。
方針：指定順序写像の全域像と単射な引き戻しの既存評価則を使う。
規約：全切断点と次数を保持する既存構成の評価則。
使われ方：HA 1.2.4、IS-W2 B02の自由鎖AWと実標準AWの各切断の照合。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
open CategoryTheory
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open scoped Simplicial

/-- 指定前面の順序写像は単射。 -/
theorem awFront_injective (n : ℕ) (c : Fin (n + 1)) :
    Function.Injective (awFront n c).toOrderHom := by
  intro a b h
  apply Fin.ext
  have h' := congrArg (fun a : Fin (n + 1) => a.val) h
  exact h'

/-- 指定後面の順序写像は単射。 -/
theorem awBack_injective (n : ℕ) (c : Fin (n + 1)) :
    Function.Injective (awBack n c).toOrderHom := by
  intro a b h
  apply Fin.ext
  have h' := congrArg Fin.val h
  change c.val + a.val = c.val + b.val at h'
  omega

/-- 指定前面の全頂点の像は切断点までの接頭集合。 -/
theorem awFront_univ_image (n : ℕ) (c : Fin (n + 1)) :
    (Finset.univ : Finset (Fin (c.val + 1))).image (awFront n c).toOrderHom =
      Finset.univ.filter (· ≤ c) := by
  ext a
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
  constructor
  · rintro ⟨b, rfl⟩
    change b.val ≤ c.val
    omega
  · intro ha
    refine ⟨⟨a.val, by change a.val ≤ c.val at ha; omega⟩, ?_⟩
    apply Fin.ext
    rfl

/-- 指定後面の全頂点の像は切断点以降の接尾集合。 -/
theorem awBack_univ_image (n : ℕ) (c : Fin (n + 1)) :
    (Finset.univ : Finset (Fin (n - c.val + 1))).image (awBack n c).toOrderHom =
      Finset.univ.filter (c ≤ ·) := by
  ext a
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
  constructor
  · rintro ⟨b, rfl⟩
    change c.val ≤ c.val + b.val
    omega
  · intro ha
    have ha' : c.val ≤ a.val := ha
    refine ⟨⟨a.val - c.val, by have := a.isLt; omega⟩, ?_⟩
    apply Fin.ext
    change c.val + (a.val - c.val) = a.val
    omega

/-- 接頭集合の濃度。 -/
theorem awFront_filter_card (n : ℕ) (c : Fin (n + 1)) :
    (Finset.univ.filter (· ≤ c)).card = c.val + 1 := by
  rw [← awFront_univ_image n c, Finset.card_image_of_injective _ (awFront_injective n c)]
  simp only [Finset.card_univ, Fintype.card_fin]

/-- 接尾集合の濃度。 -/
theorem awBack_filter_card (n : ℕ) (c : Fin (n + 1)) :
    (Finset.univ.filter (c ≤ ·)).card = n - c.val + 1 := by
  rw [← awBack_univ_image n c, Finset.card_image_of_injective _ (awBack_injective n c)]
  simp only [Finset.card_univ, Fintype.card_fin]

variable {R : Type u} [CommRing R] {D : Type v} [DGCategory R D] {x y : D}

/-- 元の前面の最上位評価は同じ接頭集合の成分。 -/
theorem standardTopEval_awFront {n : ℕ} (f : StandardSimplex R x y n)
    (c : Fin (n + 1)) :
    standardTopEval (R := R) x y c.val (standardPullback (awFront n c).toOrderHom f) =
      f.val.component (Finset.univ.filter (· ≤ c)) (-(c.val : ℤ))
        (AWIndex.left_nonempty (Finset.mem_univ c))
        (by rw [awFront_filter_card]; simp) := by
  change (standardPullback (awFront n c).toOrderHom f).val.component
    Finset.univ (-(c.val : ℤ)) Finset.univ_nonempty (by simp) = _
  rw [standardPullback_val, pullback_component_of_inj _ _ _ _ _ _
    (awFront_injective n c).injOn]
  exact eq_of_heq (component_heq_of_eq f.val _ _ (awFront_univ_image n c) _ _ _ _ _ _)

/-- 元の後面の最上位評価は同じ接尾集合の成分。 -/
theorem standardTopEval_awBack {n : ℕ} (f : StandardSimplex R x y n)
    (c : Fin (n + 1)) :
    standardTopEval (R := R) x y (n - c.val) (standardPullback (awBack n c).toOrderHom f) =
      f.val.component (Finset.univ.filter (c ≤ ·)) (-((n - c.val : ℕ) : ℤ))
        (AWIndex.right_nonempty (Finset.mem_univ c))
        (by rw [awBack_filter_card]; simp) := by
  change (standardPullback (awBack n c).toOrderHom f).val.component
    Finset.univ (-((n - c.val : ℕ) : ℤ)) Finset.univ_nonempty (by simp) = _
  rw [standardPullback_val, pullback_component_of_inj _ _ _ _ _ _
    (awBack_injective n c).injOn]
  exact eq_of_heq (component_heq_of_eq f.val _ _ (awBack_univ_image n c) _ _ _ _ _ _)

/-- 実AWの各切断成分は、同じ前面・後面の最上位成分の通常順合成。 -/
theorem awTerm_univ_top_faces {x y z : D} {n : ℕ}
    (g : StandardSimplex R y z n) (f : StandardSimplex R x y n) (c : Fin (n + 1)) :
    awTerm g.val f.val Finset.univ ⟨c, Finset.mem_univ c⟩ (-(n : ℤ)) (by simp) =
      compose R (p := -((n - c.val : ℕ) : ℤ)) (q := -(c.val : ℤ)) (n := -(n : ℤ))
        (standardTopEval (R := R) y z c.val (standardPullback (awFront n c).toOrderHom g))
        (standardTopEval (R := R) x y (n - c.val)
          (standardPullback (awBack n c).toOrderHom f))
        (by have := c.isLt; omega) := by
  let L := (Finset.univ : Finset (Fin (n + 1))).filter (· ≤ c)
  let K := (Finset.univ : Finset (Fin (n + 1))).filter (c ≤ ·)
  have hp : 1 - (K.card : ℤ) = -((n - c.val : ℕ) : ℤ) := by
    dsimp only [K]
    rw [awBack_filter_card]
    simp
  have hq : 1 - (L.card : ℤ) = -(c.val : ℤ) := by
    dsimp only [L]
    rw [awFront_filter_card]
    simp
  have hg : HEq (g.val.component L (1 - (L.card : ℤ))
      (AWIndex.left_nonempty (Finset.mem_univ c)) rfl)
      (standardTopEval (R := R) y z c.val (standardPullback (awFront n c).toOrderHom g)) := by
    have h := component_heq_of_eq g.val L L rfl
      (1 - (L.card : ℤ)) (-(c.val : ℤ))
      (AWIndex.left_nonempty (Finset.mem_univ c))
      (AWIndex.left_nonempty (Finset.mem_univ c)) rfl hq.symm
    exact h.trans (heq_of_eq (standardTopEval_awFront g c).symm)
  have hf : HEq (f.val.component K (1 - (K.card : ℤ))
      (AWIndex.right_nonempty (Finset.mem_univ c)) rfl)
      (standardTopEval (R := R) x y (n - c.val)
        (standardPullback (awBack n c).toOrderHom f)) := by
    have h := component_heq_of_eq f.val K K rfl
      (1 - (K.card : ℤ)) (-((n - c.val : ℕ) : ℤ))
      (AWIndex.right_nonempty (Finset.mem_univ c))
      (AWIndex.right_nonempty (Finset.mem_univ c)) rfl hp.symm
    exact h.trans (heq_of_eq (standardTopEval_awBack f c).symm)
  exact AWAssocTerms.compose_eq_of_heq _ _ _ _ hg hf hp hq
    (by have := c.isLt; omega)
    (by have := c.isLt; omega)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
