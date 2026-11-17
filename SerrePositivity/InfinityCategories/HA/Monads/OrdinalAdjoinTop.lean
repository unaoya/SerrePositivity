module

public import SerrePositivity.InfinityCategories.HA.Monads.OrdinalAdjoints

/-!
概要：空を含む有限順序集合の射への最大元の付加と、その制限の逆変換。
方針：Fin.lastCasesで付加し、最大元を反映する射から最後の元を取り除く。
規約：Fin 0も含む。端点保存と端点反映を区別する。
使われ方：HA Proposition 4.7.3.3 のwalking adjunctionの区間表示、
Riehl–Verity Remark 3.3.8、Kerodon Remark 6.2.1.4（Tag 02EN）。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.HA.Monads

variable {m n k : ℕ}

/-- 概要：有限単調射に新しい最大元を付け足す。
方針：元の点ではcastSucc、新しい最後の点ではlastを取る。
規約：始域・値域が空でも定義する。使われ方：Riehl–Verity Remark 3.3.8 の区間表示。 -/
def ordinalAdjoinTop (f : Fin m →o Fin n) : Fin (m + 1) →o Fin (n + 1) where
  toFun := Fin.lastCases (Fin.last n) (fun i => (f i).castSucc)
  monotone' := by
    intro i j hij
    cases i using Fin.lastCases with
    | last =>
      have h : j = Fin.last m := le_antisymm (Fin.le_last _) hij
      subst j
      exact le_rfl
    | cast i =>
      cases j using Fin.lastCases with
      | last =>
          simpa only [Fin.lastCases_castSucc, Fin.lastCases_last] using
            Fin.le_last ((f i).castSucc)
      | cast j =>
        simpa only [Fin.lastCases_castSucc, Fin.castSucc_le_castSucc_iff] using
          f.monotone (Fin.castSucc_le_castSucc_iff.mp hij)

/-- 概要：最大元付加の元の点での値。
方針：lastCasesの定義。規約：元の有限順序集合の点を指定する。
使われ方：Riehl–Verity Remark 3.3.8 の区間表示の回収。 -/
@[simp] lemma ordinalAdjoinTop_castSucc (f : Fin m →o Fin n) (i : Fin m) :
    ordinalAdjoinTop f i.castSucc = (f i).castSucc := by
  simp [ordinalAdjoinTop]

/-- 概要：最大元付加は指定の最後の元を保つ。
方針：lastCasesの最後の枝。規約：元の射の端点保存は不要。
使われ方：Riehl–Verity Remark 3.3.8 の左随伴の入力。 -/
@[simp] lemma ordinalAdjoinTop_last (f : Fin m →o Fin n) :
    ordinalAdjoinTop f (Fin.last m) = Fin.last n := by
  simp [ordinalAdjoinTop]

/-- 概要：付加した最大元以外は最大元に写らない。
方針：最後の点か元の点かで分ける。規約：最大元を反映する同値。
使われ方：Riehl–Verity Remark 3.3.8 の両端点保存の検収。 -/
lemma ordinalAdjoinTop_reflectsLast (f : Fin m →o Fin n) (i : Fin (m + 1)) :
    ordinalAdjoinTop f i = Fin.last n ↔ i = Fin.last m := by
  cases i using Fin.lastCases <;> simp

/-- 概要：最大元付加は元の単調射の等式を反映する。
方針：元の点で評価しcastSuccの単射性を使う。規約：空の場合も同じ型で量化する。
使われ方：Riehl–Verity Remark 3.3.8 の区間表示の忠実性。 -/
lemma ordinalAdjoinTop_injective : Function.Injective
    (ordinalAdjoinTop : (Fin m →o Fin n) → _) := by
  intro f g h
  apply OrderHom.ext
  funext i
  apply Fin.castSucc_injective
  have hi := congrArg (fun p : Fin (m + 1) →o Fin (n + 1) => p i.castSucc) h
  simpa only [ordinalAdjoinTop_castSucc] using hi

/-- 概要：恒等単調射への最大元付加は恒等射。
方針：最後の点と元の点で計算する。規約：元の有限順序集合が空でもよい。
使われ方：Riehl–Verity Remark 3.3.8 の区間表示の関手性。 -/
lemma ordinalAdjoinTop_id (m : ℕ) :
    ordinalAdjoinTop (OrderHom.id : Fin m →o Fin m) = OrderHom.id := by
  apply OrderHom.ext
  funext i
  cases i using Fin.lastCases <;> simp

/-- 概要：最大元付加は有限単調射の合成を保つ。
方針：両種類の点で定義を計算する。規約：元の射の向きのまま合成する。
使われ方：Riehl–Verity Remark 3.3.8 の区間表示の反変関手。 -/
lemma ordinalAdjoinTop_comp (f : Fin m →o Fin n) (g : Fin n →o Fin k) :
    ordinalAdjoinTop (g.comp f) = (ordinalAdjoinTop g).comp (ordinalAdjoinTop f) := by
  apply OrderHom.ext
  funext i
  cases i using Fin.lastCases <;> simp [OrderHom.comp_coe]

/-- 概要：最大元を反映する射は、元の点を元の点へ送る。
方針：最後の点との等式を反映して排除する。
規約：始域の元の点iを指定する。使われ方：Riehl–Verity Remark 3.3.8 の制限。 -/
lemma ordinalRemoveTop_bound (g : Fin (m + 1) →o Fin (n + 1))
    (hg : ∀ i, g i = Fin.last n ↔ i = Fin.last m) (i : Fin m) :
    (g i.castSucc).val < n := by
  have hne : (g i.castSucc).val ≠ n := by
    intro h
    exact Fin.castSucc_ne_last i ((hg _).mp (Fin.ext h))
  have hlt := (g i.castSucc).isLt
  omega

/-- 概要：最大元を反映する有限単調射から付加した最大元を除く。
方針：元の点に制限し、値の厳密な上界を使う。
規約：最大元の反映を要求する。使われ方：Riehl–Verity Remark 3.3.8 の逆変換。 -/
def ordinalRemoveTop (g : Fin (m + 1) →o Fin (n + 1))
    (hg : ∀ i, g i = Fin.last n ↔ i = Fin.last m) : Fin m →o Fin n where
  toFun i := ⟨(g i.castSucc).val, ordinalRemoveTop_bound g hg i⟩
  monotone' := by
    intro i j hij
    exact g.monotone (Fin.castSucc_le_castSucc_iff.mpr hij)

/-- 概要：制限を再びcastSuccすると元の射の値になる。
方針：値の自然数は変えていないことを使う。規約：元の点での等式。
使われ方：Riehl–Verity Remark 3.3.8 の往復の検収。 -/
lemma ordinalRemoveTop_castSucc (g : Fin (m + 1) →o Fin (n + 1))
    (hg : ∀ i, g i = Fin.last n ↔ i = Fin.last m) (i : Fin m) :
    (ordinalRemoveTop g hg i).castSucc = g i.castSucc := by
  apply Fin.ext
  rfl

/-- 概要：元の有限単調射への付加・制限の往復は恒等。
方針：castSuccの単射性で各点を比較する。規約：元の射の等式。
使われ方：Riehl–Verity Remark 3.3.8 の区間表示の忠実性。 -/
lemma ordinalRemoveTop_adjoin (f : Fin m →o Fin n) :
    ordinalRemoveTop (ordinalAdjoinTop f) (ordinalAdjoinTop_reflectsLast f) = f := by
  apply OrderHom.ext
  funext i
  apply Fin.castSucc_injective
  rw [ordinalRemoveTop_castSucc, ordinalAdjoinTop_castSucc]

/-- 概要：最大元を保ち反映する射の制限・付加の往復は元の射。
方針：最後の点と元の点で比較する。規約：両方の最大元の条件を明示する。
使われ方：Riehl–Verity Remark 3.3.8 の逆変換の検収。 -/
lemma ordinalAdjoinTop_remove (g : Fin (m + 1) →o Fin (n + 1))
    (hg : ∀ i, g i = Fin.last n ↔ i = Fin.last m)
    (ht : g (Fin.last m) = Fin.last n) :
    ordinalAdjoinTop (ordinalRemoveTop g hg) = g := by
  apply OrderHom.ext
  funext i
  cases i using Fin.lastCases with
  | last => simpa only [ordinalAdjoinTop_last] using ht.symm
  | cast i => rw [ordinalAdjoinTop_castSucc, ordinalRemoveTop_castSucc]

end SerrePositivity.InfinityCategories.HA.Monads
