module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AWDegenerate
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CubeRestriction

/-!
# 座標の順序に適合しない AW の旗の消滅

概要：後の射の座標より先に前の射の座標が現れる旗では、AW の最上位評価は零である。
方針：各切断点で、接頭側または接尾側に忘れた座標の隣接頂点が含まれることを示す。
規約：P が後の射の座標、その補集合が前の射の座標。
使われ方：HA 1.3.1.16、Kerodon 2.5.8（Tag 00S0） の AW と shuffle の合成の不要項の消去。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial
variable {R : Type u} [CommRing R] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] {x y z : D}

/-- 概要：接頭の途中で忘れた座標が加わると、その AW 項は零である。
方針：加わる前後の頂点が接頭集合に属し、制限した旗で一致することを使う。
規約：座標番号 r が切断点 j より小さい場合。
使われ方：Kerodon 2.5.8（Tag 00S0） の後の射の接頭成分の消滅。 -/
lemma awTerm_cubeRestriction_zero_left {T : Type u} {n : ℕ} (P : T → Prop)
    (e : Fin (n + 1) ≃ T) (r : Fin (n + 1)) (hr : ¬ P (e r))
    (ψ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube {t // P t} ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := R) y z)
    (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R x y (n + 1)) (j : Fin (n + 2)) (hj : r.val < j.val)
    (k : ℤ) (hk : k = 1 - ((Finset.univ : Finset (Fin (n + 2))).card : ℤ)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awTerm (ψ.app _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeRestrictionMap P).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag e))).val f
      Finset.univ ⟨j, Finset.mem_univ j⟩ k hk = 0 := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awTerm_nerve_zero_left
  intro hinj
  have h₀ : r.castSucc ∈ (Finset.univ : Finset (Fin (n + 2))).filter (· ≤ j) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, by change r.val ≤ j.val; omega⟩
  have h₁ : r.succ ∈ (Finset.univ : Finset (Fin (n + 2))).filter (· ≤ j) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, by change r.val + 1 ≤ j.val; omega⟩
  exact (ne_of_lt r.castSucc_lt_succ) (hinj h₀ h₁ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeRestrictionMap_flag_repeat P e r hr))

/-- 概要：接尾の途中で忘れた座標が加わると、その AW 項は零である。
方針：加わる前後の頂点が接尾集合に属し、制限した旗で一致することを使う。
規約：切断点 j が座標番号 r 以下の場合。
使われ方：Kerodon 2.5.8（Tag 00S0） の前の射の接尾成分の消滅。 -/
lemma awTerm_cubeRestriction_zero_right {T : Type u} {n : ℕ} (P : T → Prop)
    (e : Fin (n + 1) ≃ T) (r : Fin (n + 1)) (hr : ¬ P (e r))
    (φ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube {t // P t} ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := R) x y)
    (g : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R y z (n + 1)) (j : Fin (n + 2)) (hj : j.val ≤ r.val)
    (k : ℤ) (hk : k = 1 - ((Finset.univ : Finset (Fin (n + 2))).card : ℤ)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awTerm g (φ.app _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeRestrictionMap P).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag e))).val
      Finset.univ ⟨j, Finset.mem_univ j⟩ k hk = 0 := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awTerm_nerve_zero_right
  intro hinj
  have h₀ : r.castSucc ∈ (Finset.univ : Finset (Fin (n + 2))).filter (j ≤ ·) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, by change j.val ≤ r.val; exact hj⟩
  have h₁ : r.succ ∈ (Finset.univ : Finset (Fin (n + 2))).filter (j ≤ ·) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, by change j.val ≤ r.val + 1; omega⟩
  exact (ne_of_lt r.castSucc_lt_succ) (hinj h₀ h₁ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeRestrictionMap_flag_repeat P e r hr))

/-- 概要：前の射の座標が後の射の座標より先に現れる旗の各 AW 項は零である。
方針：切断点より前に誤った座標がある場合と、切断点以後にある場合に分ける。
規約：P が後の射、¬P が前の射の座標集合。
使われ方：HA 1.3.1.16 の AW と shuffle の合成で逆転した旗を消去する。 -/
lemma awTerm_cubeRestriction_zero_of_inversion {T : Type u} {n : ℕ} (P : T → Prop)
    (e : Fin (n + 1) ≃ T) (r s : Fin (n + 1)) (hrs : r < s)
    (hr : ¬ P (e r)) (hs : P (e s))
    (ψ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube {t // P t} ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := R) y z)
    (φ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube {t // ¬ P t} ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := R) x y)
    (j : Fin (n + 2)) (k : ℤ)
    (hk : k = 1 - ((Finset.univ : Finset (Fin (n + 2))).card : ℤ)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awTerm (ψ.app _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeRestrictionMap P).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag e))).val
      (φ.app _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeRestrictionMap (fun t ↦ ¬ P t)).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag e))).val
      Finset.univ ⟨j, Finset.mem_univ j⟩ k hk = 0 := by
  by_cases hj : r.val < j.val
  · exact awTerm_cubeRestriction_zero_left P e r hr ψ _ j hj k hk
  · exact awTerm_cubeRestriction_zero_right (fun t ↦ ¬ P t) e s (not_not.mpr hs) φ _ j
      (by have h : r.val < s.val := hrs; omega) k hk

/-- 概要：座標の前後が逆転した旗の AW 合成の最上位評価は零である。
方針：全切断点の AW 項を逆転の消滅補題で零にする。
規約：旗の次元は n+1、評価の次数は −(n+1)。
使われ方：Kerodon 2.5.8（Tag 00S0） の AW∘shuffle の計算で順序に適合した旗だけを残す。 -/
lemma standardTopEval_AW_restriction_zero_of_inversion {T : Type u} {n : ℕ}
    (P : T → Prop) (e : Fin (n + 1) ≃ T) (r s : Fin (n + 1)) (hrs : r < s)
    (hr : ¬ P (e r)) (hs : P (e s))
    (ψ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube {t // P t} ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := R) y z)
    (φ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube {t // ¬ P t} ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := R) x y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardTopEval (R := R) x z (n + 1)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardAW (ψ.app _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeRestrictionMap P).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag e)))
        (φ.app _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeRestrictionMap (fun t ↦ ¬ P t)).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag e)))) = 0 := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awData (n := n + 1) _ _).component Finset.univ (-((n + 1 : ℕ) : ℤ))
    Finset.univ_nonempty (by simp) = 0
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awData_component]
  apply Finset.sum_eq_zero
  intro j _
  exact awTerm_cubeRestriction_zero_of_inversion P e r s hrs hr hs ψ φ j.val _ _

/-- 概要：二つの座標集合が境目 c で分かれた旗では、他の切断点の AW 項は零である。
方針：境目より前の切断では接尾、後の切断では接頭に忘れた座標が現れる。
規約：P の座標が先頭 c 個、補集合の座標がその後に並ぶ。
使われ方：Kerodon 2.5.8（Tag 00S0） の AW∘shuffle の唯一の切断点の選択。 -/
lemma awTerm_cubeRestriction_zero_of_bad_cut {T : Type u} {n : ℕ} (P : T → Prop)
    (e : Fin (n + 1) ≃ T) (c : Fin (n + 2))
    (hc : ∀ r : Fin (n + 1), P (e r) ↔ r.val < c.val)
    (ψ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube {t // P t} ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := R) y z)
    (φ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube {t // ¬ P t} ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := R) x y)
    (j : Fin (n + 2)) (hj : j ≠ c) (k : ℤ)
    (hk : k = 1 - ((Finset.univ : Finset (Fin (n + 2))).card : ℤ)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awTerm (ψ.app _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeRestrictionMap P).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag e))).val
      (φ.app _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeRestrictionMap (fun t ↦ ¬ P t)).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag e))).val
      Finset.univ ⟨j, Finset.mem_univ j⟩ k hk = 0 := by
  rcases lt_or_gt_of_ne hj with hj | hj
  · let r : Fin (n + 1) := ⟨j.val, by have h := c.isLt; change j.val < c.val at hj; omega⟩
    have hr : ¬ ¬ P (e r) := not_not.mpr ((hc r).mpr hj)
    exact awTerm_cubeRestriction_zero_right (fun t ↦ ¬ P t) e r hr φ _ j (le_refl _) k hk
  · let r : Fin (n + 1) := ⟨c.val, by have h := j.isLt; change c.val < j.val at hj; omega⟩
    have hr : ¬ P (e r) := fun h ↦ (Nat.lt_irrefl c.val) ((hc r).mp h)
    exact awTerm_cubeRestriction_zero_left P e r hr ψ _ j hj k hk

/-- 概要：境目で分かれた旗の AW の最上位評価は境目の一項に等しい。
方針：全切断点の和から、境目以外の退化項を除く。
規約：境目が最初または最後の場合も含める。
使われ方：HA 1.3.1.16 の基本鎖の AW 評価を左右の評価の合成へ移す準備。 -/
lemma standardTopEval_AW_restriction_eq_term {T : Type u} {n : ℕ}
    (P : T → Prop) (e : Fin (n + 1) ≃ T) (c : Fin (n + 2))
    (hc : ∀ r : Fin (n + 1), P (e r) ↔ r.val < c.val)
    (ψ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube {t // P t} ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := R) y z)
    (φ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube {t // ¬ P t} ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := R) x y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardTopEval (R := R) x z (n + 1)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardAW (ψ.app _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeRestrictionMap P).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag e)))
        (φ.app _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeRestrictionMap (fun t ↦ ¬ P t)).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag e)))) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awTerm (ψ.app _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeRestrictionMap P).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag e))).val
        (φ.app _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeRestrictionMap (fun t ↦ ¬ P t)).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag e))).val
        Finset.univ ⟨c, Finset.mem_univ c⟩ (-((n + 1 : ℕ) : ℤ)) (by simp) := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awData (n := n + 1) _ _).component Finset.univ (-((n + 1 : ℕ) : ℤ))
    Finset.univ_nonempty (by simp) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awData_component]
  apply Finset.sum_eq_single
    (⟨c, Finset.mem_univ c⟩ : (Finset.univ : Finset (Fin (n + 2))))
  · intro j _ hj
    exact awTerm_cubeRestriction_zero_of_bad_cut P e c hc ψ φ j.val
      (fun h ↦ hj (Subtype.ext h)) _ _
  · simp

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
