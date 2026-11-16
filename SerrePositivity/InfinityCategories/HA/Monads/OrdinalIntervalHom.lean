module

public import SerrePositivity.InfinityCategories.HA.Monads.OrdinalAdjoinTop

/-!
概要：有限順序射と、両端点を保つ逆向きの区間の射の相互変換。
方針：最大元を付加した射の実左随伴を取り、逆には右随伴の元の点への制限を使う。
規約：空の順序集合も含む。全て実際の有限単調射の等式として比較する。
使われ方：HA Proposition 4.7.3.3 のwalking adjunctionの残る水平合成の区間表示、
Riehl–Verity Remark 3.3.8、Kerodon Remark 6.2.1.4（Tag 02EN）。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.InfinityCategories.HA.Monads

variable {m n k : ℕ}

/-- 概要：有限順序射を逆向きの区間の単調射にする。
方針：最大元付加の実左随伴を使う。規約：長さm,nは0でもよい。
使われ方：Riehl–Verity Remark 3.3.8 のirの射の構成。 -/
def ordinalIntervalMap (f : Fin m →o Fin n) : Fin (n + 1) →o Fin (m + 1) :=
  ordinalLeftAdjoint (ordinalAdjoinTop f) (ordinalAdjoinTop_last f)

/-- 概要：区間の射は最大元付加の実左随伴。
方針：左随伴の構成の条件を使う。規約：元の射とその付加を固定する。
使われ方：Riehl–Verity Remark 3.3.8 の端点・往復の計算。 -/
lemma ordinalIntervalMap_gc (f : Fin m →o Fin n) :
    GaloisConnection (ordinalIntervalMap f) (ordinalAdjoinTop f) :=
  ordinalLeftAdjoint_gc _ _

/-- 概要：構成した区間の射は最小元を保つ。
方針：実左随伴の最小元保存。規約：両区間の指定された0。
使われ方：Riehl–Verity Remark 3.3.8 の両端点条件。 -/
lemma ordinalIntervalMap_zero (f : Fin m →o Fin n) : ordinalIntervalMap f 0 = 0 :=
  ordinalLeftAdjoint_zero _ _

/-- 概要：構成した区間の射は最大元も保つ。
方針：Galois単位と、最大元付加が最大元を反映することを使う。
規約：両区間の最後の元。使われ方：Riehl–Verity Remark 3.3.8 の両端点条件。 -/
lemma ordinalIntervalMap_last (f : Fin m →o Fin n) :
    ordinalIntervalMap f (Fin.last n) = Fin.last m := by
  have h := (ordinalIntervalMap_gc f).le_u_l (Fin.last n)
  have ht : ordinalAdjoinTop f (ordinalIntervalMap f (Fin.last n)) = Fin.last n :=
    le_antisymm (Fin.le_last _) h
  exact (ordinalAdjoinTop_reflectsLast f _).mp ht

/-- 概要：両端点を保つ射の右随伴は最大元を反映する。
方針：元の射の最大元保存とGalois余単位を使う。
規約：最小元保存から実右随伴を作る。使われ方：Riehl–Verity Remark 3.3.8 の逆変換。 -/
lemma intervalRightAdjoint_reflectsLast (l : Fin (n + 1) →o Fin (m + 1))
    (h₀ : l 0 = 0) (h₁ : l (Fin.last n) = Fin.last m) (i : Fin (m + 1)) :
    ordinalRightAdjoint l h₀ i = Fin.last n ↔ i = Fin.last m := by
  constructor
  · intro h
    apply le_antisymm (Fin.le_last _)
    have hi := (ordinalRightAdjoint_gc l h₀).l_u_le i
    rw [h, h₁] at hi
    exact hi
  · rintro rfl
    exact ordinalRightAdjoint_last l h₀

/-- 概要：両端点を保つ区間の射から元の有限順序射を回収する。
方針：実右随伴から付加した最大元を除く。規約：元の両端点の条件を明示する。
使われ方：Riehl–Verity Remark 3.3.8 の区間表示の逆。 -/
def ordinalRecoverMap (l : Fin (n + 1) →o Fin (m + 1))
    (h₀ : l 0 = 0) (h₁ : l (Fin.last n) = Fin.last m) : Fin m →o Fin n :=
  ordinalRemoveTop (ordinalRightAdjoint l h₀) (intervalRightAdjoint_reflectsLast l h₀ h₁)

/-- 概要：回収した射の最大元付加は元の区間射の右随伴。
方針：最大元の付加・制限の往復を使う。
規約：同じ右随伴との等式。使われ方：Riehl–Verity Remark 3.3.8 の相互逆性。 -/
lemma ordinalRecoverMap_adjoin (l : Fin (n + 1) →o Fin (m + 1))
    (h₀ : l 0 = 0) (h₁ : l (Fin.last n) = Fin.last m) :
    ordinalAdjoinTop (ordinalRecoverMap l h₀ h₁) = ordinalRightAdjoint l h₀ :=
  ordinalAdjoinTop_remove _ _ (ordinalRightAdjoint_last l h₀)

/-- 概要：有限順序射の区間表示・回収の往復は元の射。
方針：最大元付加の単射性と有限Galois随伴の相互逆性を使う。
規約：射の等式として戻す。使われ方：Riehl–Verity Remark 3.3.8 の忠実性。 -/
lemma ordinalRecoverMap_interval (f : Fin m →o Fin n) :
    ordinalRecoverMap (ordinalIntervalMap f) (ordinalIntervalMap_zero f)
      (ordinalIntervalMap_last f) = f := by
  apply ordinalAdjoinTop_injective
  exact (ordinalRecoverMap_adjoin _ _ _).trans
    (ordinal_right_left (ordinalAdjoinTop f) (ordinalAdjoinTop_last f))

/-- 概要：両端点を保つ区間射の回収・区間表示の往復は元の区間射。
方針：同じ右随伴を持つ二つの左随伴の一意性を使う。
規約：高次の同値でなく実際の有限順序射の等式。使われ方：Riehl–Verity Remark 3.3.8。 -/
lemma ordinalIntervalMap_recover (l : Fin (n + 1) →o Fin (m + 1))
    (h₀ : l 0 = 0) (h₁ : l (Fin.last n) = Fin.last m) :
    ordinalIntervalMap (ordinalRecoverMap l h₀ h₁) = l := by
  have h := ordinalIntervalMap_gc (ordinalRecoverMap l h₀ h₁)
  rw [ordinalRecoverMap_adjoin] at h
  apply OrderHom.ext
  funext i
  exact h.l_unique (ordinalRightAdjoint_gc l h₀) (fun _ => rfl)

/-- 概要：有限順序射と両端点を保つ逆向きの区間射の実全単射。
方針：実際のGalois随伴と二つの往復をまとめる。
規約：長さ0の有限順序集合も含める。
使われ方：HA Proposition 4.7.3.3、Riehl–Verity Remark 3.3.8 のirの充満忠実性。 -/
def ordinalIntervalHomEquiv (m n : ℕ) :
    (Fin m →o Fin n) ≃
      {l : Fin (n + 1) →o Fin (m + 1) // l 0 = 0 ∧ l (Fin.last n) = Fin.last m} where
  toFun f := ⟨ordinalIntervalMap f, ordinalIntervalMap_zero f, ordinalIntervalMap_last f⟩
  invFun l := ordinalRecoverMap l.val l.property.1 l.property.2
  left_inv := ordinalRecoverMap_interval
  right_inv l := Subtype.ext (ordinalIntervalMap_recover l.val l.property.1 l.property.2)

/-- 概要：区間表示は恒等射を保つ。
方針：最大元付加の恒等則と左随伴の一意性。
規約：元の有限順序集合が空でもよい。使われ方：Riehl–Verity Remark 3.3.8 の関手性。 -/
lemma ordinalIntervalMap_id (m : ℕ) :
    ordinalIntervalMap (OrderHom.id : Fin m →o Fin m) = OrderHom.id := by
  have h := ordinalIntervalMap_gc (OrderHom.id : Fin m →o Fin m)
  rw [ordinalAdjoinTop_id] at h
  apply OrderHom.ext
  funext i
  exact h.l_unique GaloisConnection.id (fun _ => rfl)

/-- 概要：区間表示は有限順序射の合成の順序を反転する。
方針：最大元付加の合成則とGalois随伴の合成・一意性を使う。
規約：同じ三つの有限順序集合。使われ方：Riehl–Verity Remark 3.3.8 の反変関手。 -/
lemma ordinalIntervalMap_comp (f : Fin m →o Fin n) (g : Fin n →o Fin k) :
    ordinalIntervalMap (g.comp f) = (ordinalIntervalMap f).comp (ordinalIntervalMap g) := by
  have h : GaloisConnection ((ordinalIntervalMap f).comp (ordinalIntervalMap g))
      (ordinalAdjoinTop (g.comp f)) := by
    rw [ordinalAdjoinTop_comp]
    exact (ordinalIntervalMap_gc g).compose (ordinalIntervalMap_gc f)
  apply OrderHom.ext
  funext i
  exact (ordinalIntervalMap_gc (g.comp f)).l_unique h (fun _ => rfl)

end SerrePositivity.InfinityCategories.HA.Monads
