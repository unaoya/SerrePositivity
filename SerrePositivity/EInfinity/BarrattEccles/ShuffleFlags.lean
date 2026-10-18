module

public import SerrePositivity.EInfinity.BarrattEccles.OrderedSubset

/-!
# 三入力の shuffle の辺集合の旗

概要：Berger–Fresse §1.1.3 の二段の shuffle の添字を三種類の辺の包含の旗で表す。
方針：最初の色の辺集合を最初の二色の辺集合の昇順部分集合として表す。
規約：全辺数 N と最初の二色の辺数 p,q を独立に指定する。
使われ方：二つの括弧付けの shuffle の添字の全単射を作る。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.BarrattEccles

/-- 概要：最初の色の辺集合が最初の二色の辺集合に含まれる旗（Berger–Fresse §1.1.3）。
方針：二つの有限辺集合に包含と濃度の条件を課す。
規約：小さい集合の濃度は p、大きい集合の濃度は p+q である。
使われ方：三入力の shuffle の括弧に依存しない添字となる。 -/
abbrev ShuffleFlagIn (N p q : ℕ) :=
  {t : Finset (Fin N) × Finset (Fin N) //
    t.1 ⊆ t.2 ∧ t.1.card = p ∧ t.2.card = p + q}

/-- 概要：全辺数の等式による旗の移送（Berger–Fresse §1.1.3）。
方針：全辺数の等式を消去して恒等同値を使う。
規約：二つの色の辺数は変えない。
使われ方：p+q+r と p+(q+r) の二つの括弧付けを同定する。 -/
def shuffleFlagCast {N M : ℕ} (h : N = M) (p q : ℕ) :
    ShuffleFlagIn N p q ≃ ShuffleFlagIn M p q := by
  subst M
  exact Equiv.refl _

/-- 概要：左の二入力を先に shuffle する添字と辺集合の旗の全単射（Berger–Fresse §1.1.3）。
方針：外側の水平辺集合を大きい集合とし、内側の水平辺集合を昇順列挙で埋め込む。
規約：外側の経路は (p+q,r)、内側の経路は (p,q) である。
使われ方：左括弧の二重 shuffle 和を旗の有限和へ添字替えする。 -/
def leftShuffleFlagEquiv (p q r : ℕ) :
    ShufflePath (p + q) r × ShufflePath p q ≃ ShuffleFlagIn (p + q + r) p q where
  toFun v := by
    let t := orderedSubsetEquiv v.1.val v.1.property v.2.val
    exact ⟨(t.val, v.1.val), t.property,
      (orderedSubsetEquiv_card v.1.val v.1.property v.2.val).trans v.2.property, v.1.property⟩
  invFun t := by
    let a := (orderedSubsetEquiv t.val.2 t.property.2.2).symm ⟨t.val.1, t.property.1⟩
    exact (⟨t.val.2, t.property.2.2⟩,
      ⟨a, (orderedSubsetEquiv_symm_card t.val.2 t.property.2.2
        ⟨t.val.1, t.property.1⟩).trans t.property.2.1⟩)
  left_inv v := by
    apply Prod.ext
    · apply Subtype.ext; rfl
    · apply Subtype.ext
      exact (orderedSubsetEquiv v.1.val v.1.property).symm_apply_apply v.2.val
  right_inv t := by
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg Subtype.val
        ((orderedSubsetEquiv t.val.2 t.property.2.2).apply_symm_apply ⟨t.val.1, t.property.1⟩)
    · rfl

/-- 概要：右の二入力を先に shuffle する添字と辺集合の旗の全単射（Berger–Fresse §1.1.3）。
方針：外側の最初の色の補集合へ内側の二番目の色を埋め込み、和集合を大きい集合とする。
規約：外側の経路は (p,q+r)、内側の経路は (q,r) である。
使われ方：右括弧の二重 shuffle 和を旗の有限和へ添字替えする。 -/
def rightShuffleFlagEquiv (p q r : ℕ) :
    ShufflePath p (q + r) × ShufflePath q r ≃ ShuffleFlagIn (p + (q + r)) p q where
  toFun v := by
    let D := orderedSubsetEquiv v.1.valᶜ v.1.compl_card v.2.val
    have hd : Disjoint v.1.val D.val := Finset.disjoint_left.mpr (by
      intro x hx hxD
      exact (Finset.mem_compl.mp (D.property hxD)) hx)
    refine ⟨(v.1.val, v.1.val ∪ D.val), Finset.subset_union_left, v.1.property, ?_⟩
    rw [Finset.card_union_of_disjoint hd, v.1.property, orderedSubsetEquiv_card, v.2.property]
  invFun t := by
    let U : ShufflePath p (q + r) := ⟨t.val.1, t.property.2.1⟩
    let T : {T : Finset (Fin (p + (q + r))) // T ⊆ U.valᶜ} :=
      ⟨t.val.2 \ t.val.1, fun x hx => Finset.mem_compl.mpr (Finset.mem_sdiff.mp hx).2⟩
    have hT : T.val.card = q := by
      change (t.val.2 \ t.val.1).card = q
      rw [Finset.card_sdiff_of_subset t.property.1, t.property.2.2, t.property.2.1]
      omega
    exact (U, ⟨(orderedSubsetEquiv U.valᶜ U.compl_card).symm T,
      (orderedSubsetEquiv_symm_card U.valᶜ U.compl_card T).trans hT⟩)
  left_inv v := by
    apply Prod.ext
    · apply Subtype.ext; rfl
    · apply Subtype.ext
      let D := orderedSubsetEquiv v.1.valᶜ v.1.compl_card v.2.val
      let T : {T : Finset (Fin (p + (q + r))) // T ⊆ v.1.valᶜ} :=
        ⟨(v.1.val ∪ D.val) \ v.1.val,
          fun x hx => Finset.mem_compl.mpr (Finset.mem_sdiff.mp hx).2⟩
      have hd : Disjoint v.1.val D.val := Finset.disjoint_left.mpr (by
        intro x hx hxD
        exact (Finset.mem_compl.mp (D.property hxD)) hx)
      have ht : T = D := Subtype.ext (Finset.union_sdiff_cancel_left hd)
      change (orderedSubsetEquiv v.1.valᶜ v.1.compl_card).symm T = v.2.val
      rw [ht]
      exact (orderedSubsetEquiv v.1.valᶜ v.1.compl_card).symm_apply_apply v.2.val
  right_inv t := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · let U : ShufflePath p (q + r) := ⟨t.val.1, t.property.2.1⟩
      let T : {T : Finset (Fin (p + (q + r))) // T ⊆ U.valᶜ} :=
        ⟨t.val.2 \ t.val.1, fun x hx => Finset.mem_compl.mpr (Finset.mem_sdiff.mp hx).2⟩
      change U.val ∪ ((orderedSubsetEquiv U.valᶜ U.compl_card)
        ((orderedSubsetEquiv U.valᶜ U.compl_card).symm T)).val = t.val.2
      rw [(orderedSubsetEquiv U.valᶜ U.compl_card).apply_symm_apply]
      exact Finset.union_sdiff_of_subset t.property.1

/-- 概要：三入力の二つの括弧付けの shuffle の添字の全単射（Berger–Fresse §1.1.3）。
方針：両方の添字を同じ辺集合の旗へ移し、全辺数の加法の結合則で同定する。
規約：左は ((p,q),r)、右は (p,(q,r)) の経路の組である。
使われ方：三入力の shuffle の二重和を添字替えして結合則を証明する。 -/
def tripleShuffleEquiv (p q r : ℕ) :
    ShufflePath (p + q) r × ShufflePath p q ≃ ShufflePath p (q + r) × ShufflePath q r :=
  (leftShuffleFlagEquiv p q r).trans
    ((shuffleFlagCast (Nat.add_assoc p q r) p q).trans (rightShuffleFlagEquiv p q r).symm)

/-- 概要：全辺数の移送は旗の小さい辺集合を標準の有限全単射で移す（Berger–Fresse §1.1.3）。
方針：全辺数の等式を消去する。
規約：有限全単射は Fin の値を変えない。
使われ方：三入力の添字替えの最初の色の辺集合を比較する。 -/
lemma shuffleFlagCast_small {N M : ℕ} (h : N = M) (p q : ℕ) (t : ShuffleFlagIn N p q) :
    ((shuffleFlagCast h p q) t).val.1 = t.val.1.map (finCongr h).toEmbedding := by
  cases h
  simp [shuffleFlagCast]

/-- 概要：全辺数の移送は旗の大きい辺集合を標準の有限全単射で移す（Berger–Fresse §1.1.3）。
方針：全辺数の等式を消去する。
規約：有限全単射は Fin の値を変えない。
使われ方：三入力の添字替えの最初の二色の辺集合を比較する。 -/
lemma shuffleFlagCast_large {N M : ℕ} (h : N = M) (p q : ℕ) (t : ShuffleFlagIn N p q) :
    ((shuffleFlagCast h p q) t).val.2 = t.val.2.map (finCongr h).toEmbedding := by
  cases h
  simp [shuffleFlagCast]

/-- 概要：三入力の shuffle の添字替えは同じ辺集合の旗を表す（Berger–Fresse §1.1.3）。
方針：右括弧の旗の全単射と逆同値を相殺する。
規約：左括弧の全辺数は加法の結合則で移送する。
使われ方：添字替え後の各色の辺集合の具体的な等式を得る。 -/
lemma rightFlag_tripleShuffleEquiv (p q r : ℕ)
    (v : ShufflePath (p + q) r × ShufflePath p q) :
    rightShuffleFlagEquiv p q r (tripleShuffleEquiv p q r v) =
      shuffleFlagCast (Nat.add_assoc p q r) p q (leftShuffleFlagEquiv p q r v) :=
  (rightShuffleFlagEquiv p q r).apply_symm_apply _

/-- 概要：三入力の添字替え後の最初の色の辺集合を計算する（Berger–Fresse §1.1.3）。
方針：旗の等式の小さい辺集合を取り出し、全辺数の移送を map に直す。
規約：左括弧の最初の色は二段の水平辺の昇順の合成である。
使われ方：二つの括弧付けの最初の座標を比較する。 -/
lemma tripleShuffle_firstEdges (p q r : ℕ)
    (v : ShufflePath (p + q) r × ShufflePath p q) :
    (tripleShuffleEquiv p q r v).1.val =
      ((orderedSubsetEquiv v.1.val v.1.property) v.2.val).val.map
        (finCongr (Nat.add_assoc p q r)).toEmbedding := by
  have h := congrArg (fun t : ShuffleFlagIn (p + (q + r)) p q => t.val.1)
    (rightFlag_tripleShuffleEquiv p q r v)
  rw [shuffleFlagCast_small] at h
  exact h

/-- 概要：三入力の添字替え後の最初の二色の辺集合を計算する（Berger–Fresse §1.1.3）。
方針：旗の等式の大きい辺集合を取り出して、右括弧の二色の和集合として表す。
規約：右括弧の二番目の色は最初の色の補集合の昇順の部分集合である。
使われ方：二つの括弧付けの二番目・三番目の座標を比較する。 -/
lemma tripleShuffle_firstTwoEdges (p q r : ℕ)
    (v : ShufflePath (p + q) r × ShufflePath p q) :
    (tripleShuffleEquiv p q r v).1.val ∪
        ((orderedSubsetEquiv (tripleShuffleEquiv p q r v).1.valᶜ
          (tripleShuffleEquiv p q r v).1.compl_card) (tripleShuffleEquiv p q r v).2.val).val =
      v.1.val.map (finCongr (Nat.add_assoc p q r)).toEmbedding := by
  have h := congrArg (fun t : ShuffleFlagIn (p + (q + r)) p q => t.val.2)
    (rightFlag_tripleShuffleEquiv p q r v)
  rw [shuffleFlagCast_large] at h
  exact h

end SerrePositivity.EInfinity.BarrattEccles
