module

public import Mathlib.Data.Fintype.Fin
public import Mathlib.Data.Finset.Max
public import Mathlib.Order.GaloisConnection.Defs
public import Mathlib.Order.Fin.Basic

/-!
概要：端点を保つ有限順序集合の射のGalois随伴を実際に構成する。
方針：有限下方fiberの最大と上方fiberの最小を取り、両側の随伴条件から相互逆を示す。
規約：ここでの随伴は有限順序集合の間の随伴。∞随伴の全拡張の存在を代用しない。
使われ方：HA Proposition 4.7.3.3 の全拡張の添字となるwalking adjunctionの混合Hom。
Riehl–Verity Observation 3.3.6・Remark 3.3.8、Kerodon Remark 6.2.1.4（Tag 02EN）。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.InfinityCategories.HA.Monads

variable {m n k : ℕ}

/-- 概要：有限単調射の、指定値以下に写る元の有限集合。
方針：有限全体を不等式でfilterする。規約：非空性は最小元の保存から別に示す。
使われ方：Riehl–Verity Observation 3.3.6 の右随伴の実構成。 -/
def ordinalLowerFiber (f : Fin (m + 1) →o Fin (n + 1)) (j : Fin (n + 1)) :
    Finset (Fin (m + 1)) := Finset.univ.filter (fun i => f i ≤ j)

/-- 概要：最小元を保つ射の下方fiberは非空。
方針：元0を入れる。規約：任意の指定値jに対して成り立つ。
使われ方：Riehl–Verity Observation 3.3.6 の最大元の選択。 -/
lemma ordinalLowerFiber_nonempty (f : Fin (m + 1) →o Fin (n + 1))
    (hf : f 0 = 0) (j : Fin (n + 1)) : (ordinalLowerFiber f j).Nonempty := by
  refine ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
  rw [hf]
  exact Fin.zero_le j

/-- 概要：右随伴の値を下方fiberの最大元で定める。
方針：証明済みの非空性を使う。規約：有限集合の実際の元。
使われ方：Riehl–Verity Observation 3.3.6 の右随伴。 -/
def ordinalRightAdjointValue (f : Fin (m + 1) →o Fin (n + 1))
    (hf : f 0 = 0) (j : Fin (n + 1)) : Fin (m + 1) :=
  (ordinalLowerFiber f j).max' (ordinalLowerFiber_nonempty f hf j)

/-- 概要：最大元による右随伴の値はGaloisの同値を満たす。
方針：filterの所属条件と最大元の性質、fの単調性を使う。
規約：元の有限単調射を変えない。使われ方：Riehl–Verity Observation 3.3.6。 -/
lemma ordinalRightAdjointValue_gc (f : Fin (m + 1) →o Fin (n + 1))
    (hf : f 0 = 0) (i : Fin (m + 1)) (j : Fin (n + 1)) :
    f i ≤ j ↔ i ≤ ordinalRightAdjointValue f hf j := by
  constructor
  · intro h
    exact Finset.le_max' (ordinalLowerFiber f j) i
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
  · intro h
    exact (f.monotone h).trans
      (Finset.mem_filter.mp (Finset.max'_mem _ (ordinalLowerFiber_nonempty f hf j))).2

/-- 概要：最小元を保つ有限単調射の実右随伴。
方針：値のGaloisの同値から単調性を示す。規約：随伴の存在を引数に仮定しない。
使われ方：HA Proposition 4.7.3.3 のwalking adjunctionの混合Homの表示。 -/
def ordinalRightAdjoint (f : Fin (m + 1) →o Fin (n + 1)) (hf : f 0 = 0) :
    Fin (n + 1) →o Fin (m + 1) where
  toFun := ordinalRightAdjointValue f hf
  monotone' := by
    intro i j hij
    apply (ordinalRightAdjointValue_gc f hf _ j).mp
    exact ((ordinalRightAdjointValue_gc f hf _ i).mpr le_rfl).trans hij

/-- 概要：構成した右随伴と元の射のGalois随伴条件。
方針：各値について証明した同値を使う。規約：同じ射f。
使われ方：Riehl–Verity Observation 3.3.6 の反変対応。 -/
lemma ordinalRightAdjoint_gc (f : Fin (m + 1) →o Fin (n + 1)) (hf : f 0 = 0) :
    GaloisConnection f (ordinalRightAdjoint f hf) := ordinalRightAdjointValue_gc f hf

/-- 概要：構成した右随伴は最大元を保つ。
方針：Galoisの同値を最大元に適用する。規約：Finの指定された最後の元。
使われ方：Riehl–Verity Observation 3.3.6 のΔ∞への値域。 -/
lemma ordinalRightAdjoint_last (f : Fin (m + 1) →o Fin (n + 1)) (hf : f 0 = 0) :
    ordinalRightAdjoint f hf (Fin.last n) = Fin.last m := by
  apply le_antisymm (Fin.le_last _)
  exact (ordinalRightAdjoint_gc f hf _ _).mp (Fin.le_last _)

/-- 概要：有限単調射の、指定値以上を与える元の有限集合。
方針：有限全体を不等式でfilterする。規約：左随伴の値の候補の集合。
使われ方：Riehl–Verity Observation 3.3.6 の左随伴の実構成。 -/
def ordinalUpperFiber (g : Fin (n + 1) →o Fin (m + 1)) (i : Fin (m + 1)) :
    Finset (Fin (n + 1)) := Finset.univ.filter (fun j => i ≤ g j)

/-- 概要：最大元を保つ射の上方fiberは非空。
方針：最後の元を入れる。規約：任意の指定値i。
使われ方：Riehl–Verity Observation 3.3.6 の最小元の選択。 -/
lemma ordinalUpperFiber_nonempty (g : Fin (n + 1) →o Fin (m + 1))
    (hg : g (Fin.last n) = Fin.last m) (i : Fin (m + 1)) :
    (ordinalUpperFiber g i).Nonempty := by
  refine ⟨Fin.last n, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
  rw [hg]
  exact Fin.le_last i

/-- 概要：左随伴の値を上方fiberの最小元で定める。
方針：証明済みの非空性を使う。規約：元の有限順序集合の元。
使われ方：Riehl–Verity Observation 3.3.6 の左随伴。 -/
def ordinalLeftAdjointValue (g : Fin (n + 1) →o Fin (m + 1))
    (hg : g (Fin.last n) = Fin.last m) (i : Fin (m + 1)) : Fin (n + 1) :=
  (ordinalUpperFiber g i).min' (ordinalUpperFiber_nonempty g hg i)

/-- 概要：最小元による左随伴の値はGaloisの同値を満たす。
方針：最小元の所属条件とgの単調性、最小元以下の性質を使う。
規約：同じgのまま比較する。使われ方：Riehl–Verity Observation 3.3.6。 -/
lemma ordinalLeftAdjointValue_gc (g : Fin (n + 1) →o Fin (m + 1))
    (hg : g (Fin.last n) = Fin.last m) (i : Fin (m + 1)) (j : Fin (n + 1)) :
    ordinalLeftAdjointValue g hg i ≤ j ↔ i ≤ g j := by
  constructor
  · intro h
    exact (Finset.mem_filter.mp
      (Finset.min'_mem _ (ordinalUpperFiber_nonempty g hg i))).2 |>.trans (g.monotone h)
  · intro h
    exact Finset.min'_le (ordinalUpperFiber g i) j
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)

/-- 概要：最大元を保つ有限単調射の実左随伴。
方針：値の随伴条件から単調性を示す。規約：存在を仮定せず実際に構成する。
使われ方：HA Proposition 4.7.3.3 のwalking adjunctionの混合Hom。 -/
def ordinalLeftAdjoint (g : Fin (n + 1) →o Fin (m + 1))
    (hg : g (Fin.last n) = Fin.last m) : Fin (m + 1) →o Fin (n + 1) where
  toFun := ordinalLeftAdjointValue g hg
  monotone' := by
    intro i j hij
    apply (ordinalLeftAdjointValue_gc g hg i _).mpr
    exact hij.trans ((ordinalLeftAdjointValue_gc g hg j _).mp le_rfl)

/-- 概要：構成した左随伴と元の射のGalois随伴条件。
方針：各値での同値を使う。規約：同じg。
使われ方：Riehl–Verity Observation 3.3.6 の反変対応。 -/
lemma ordinalLeftAdjoint_gc (g : Fin (n + 1) →o Fin (m + 1))
    (hg : g (Fin.last n) = Fin.last m) :
    GaloisConnection (ordinalLeftAdjoint g hg) g := ordinalLeftAdjointValue_gc g hg

/-- 概要：構成した左随伴は最小元を保つ。
方針：随伴条件を0に適用し、最小性で挟む。規約：Finの指定された0。
使われ方：Riehl–Verity Observation 3.3.6 のΔ−∞への値域。 -/
lemma ordinalLeftAdjoint_zero (g : Fin (n + 1) →o Fin (m + 1))
    (hg : g (Fin.last n) = Fin.last m) : ordinalLeftAdjoint g hg 0 = 0 := by
  apply le_antisymm _ (Fin.zero_le _)
  exact (ordinalLeftAdjoint_gc g hg _ _).mpr (Fin.zero_le _)

/-- 概要：右随伴を持つ有限単調射は最小元を保つ。
方針：随伴条件を0に適用する。規約：構成した右随伴に限定しない。
使われ方：Riehl–Verity Observation 3.3.6 の必要性。 -/
lemma ordinal_zero_of_gc {f : Fin (m + 1) →o Fin (n + 1)}
    {g : Fin (n + 1) →o Fin (m + 1)} (h : GaloisConnection f g) : f 0 = 0 :=
  le_antisymm ((h _ _).mpr (Fin.zero_le _)) (Fin.zero_le _)

/-- 概要：左随伴を持つ有限単調射は最大元を保つ。
方針：随伴条件を最後の元に適用する。規約：任意の実随伴を量化する。
使われ方：Riehl–Verity Observation 3.3.6 の必要性。 -/
lemma ordinal_last_of_gc {f : Fin (m + 1) →o Fin (n + 1)}
    {g : Fin (n + 1) →o Fin (m + 1)} (h : GaloisConnection f g) :
    g (Fin.last n) = Fin.last m :=
  le_antisymm (Fin.le_last _) ((h _ _).mp (Fin.le_last _))

/-- 概要：有限単調射の最小元保存と右随伴の存在は同値。
方針：実構成と必要性を合わせる。規約：両側とも元の有限順序集合上の主張。
使われ方：Riehl–Verity Observation 3.3.6、walking adjunctionのHomの検収。 -/
lemma ordinal_rightAdjoint_exists_iff (f : Fin (m + 1) →o Fin (n + 1)) :
    (∃ g : Fin (n + 1) →o Fin (m + 1), GaloisConnection f g) ↔ f 0 = 0 :=
  ⟨fun ⟨_, h⟩ => ordinal_zero_of_gc h,
    fun hf => ⟨ordinalRightAdjoint f hf, ordinalRightAdjoint_gc f hf⟩⟩

/-- 概要：有限単調射の最大元保存と左随伴の存在は同値。
方針：実構成と必要性を合わせる。規約：指定された同じ有限単調射。
使われ方：Riehl–Verity Observation 3.3.6 のΔ∞の特徴づけ。 -/
lemma ordinal_leftAdjoint_exists_iff (g : Fin (n + 1) →o Fin (m + 1)) :
    (∃ f : Fin (m + 1) →o Fin (n + 1), GaloisConnection f g) ↔
      g (Fin.last n) = Fin.last m :=
  ⟨fun ⟨_, h⟩ => ordinal_last_of_gc h,
    fun hg => ⟨ordinalLeftAdjoint g hg, ordinalLeftAdjoint_gc g hg⟩⟩

/-- 概要：最小元を保つ射を右随伴・左随伴で往復すると元に戻る。
方針：二つの随伴条件の単位で両向きの不等式を示す。
規約：射の等式として比較。使われ方：Riehl–Verity Observation 3.3.6 の相互逆性。 -/
lemma ordinal_left_right (f : Fin (m + 1) →o Fin (n + 1)) (hf : f 0 = 0) :
    ordinalLeftAdjoint (ordinalRightAdjoint f hf) (ordinalRightAdjoint_last f hf) = f := by
  apply OrderHom.ext
  funext i
  have h₁ := ordinalLeftAdjoint_gc (ordinalRightAdjoint f hf) (ordinalRightAdjoint_last f hf)
  have h₂ := ordinalRightAdjoint_gc f hf
  exact le_antisymm ((h₁ _ _).mpr (h₂.le_u_l _)) ((h₂ _ _).mpr (h₁.le_u_l _))

/-- 概要：最大元を保つ射を左随伴・右随伴で往復すると元に戻る。
方針：二つの随伴条件の余単位で挟む。規約：元の射と実際に等しい。
使われ方：Riehl–Verity Observation 3.3.6 の相互逆性。 -/
lemma ordinal_right_left (g : Fin (n + 1) →o Fin (m + 1))
    (hg : g (Fin.last n) = Fin.last m) :
    ordinalRightAdjoint (ordinalLeftAdjoint g hg) (ordinalLeftAdjoint_zero g hg) = g := by
  apply OrderHom.ext
  funext j
  have h₁ := ordinalRightAdjoint_gc (ordinalLeftAdjoint g hg) (ordinalLeftAdjoint_zero g hg)
  have h₂ := ordinalLeftAdjoint_gc g hg
  exact le_antisymm ((h₂ _ _).mp (h₁.l_u_le _)) ((h₁ _ _).mp (h₂.l_u_le _))

/-- 概要：恒等射の右随伴は同じ恒等射。
方針：Galois右随伴の一意性。規約：全ての有限順序集合。
使われ方：Riehl–Verity Observation 3.3.6 の反変関手の恒等射保存。 -/
lemma ordinalRightAdjoint_id (m : ℕ) :
    ordinalRightAdjoint (OrderHom.id : Fin (m + 1) →o Fin (m + 1)) rfl = OrderHom.id := by
  apply OrderHom.ext
  funext j
  exact (ordinalRightAdjoint_gc OrderHom.id rfl).u_unique GaloisConnection.id (fun _ => rfl)

/-- 概要：右随伴は有限単調射の合成の順序を反転する。
方針：Galois随伴の合成と右随伴の一意性。規約：指定された端点保存の証明に依らない。
使われ方：Riehl–Verity Observation 3.3.6 の混合Homの反変対応。 -/
lemma ordinalRightAdjoint_comp (f : Fin (m + 1) →o Fin (n + 1))
    (g : Fin (n + 1) →o Fin (k + 1)) (hf : f 0 = 0) (hg : g 0 = 0) :
    ordinalRightAdjoint (g.comp f) (by change g (f 0) = 0; rw [hf, hg]) =
      (ordinalRightAdjoint f hf).comp (ordinalRightAdjoint g hg) := by
  apply OrderHom.ext
  funext j
  exact (ordinalRightAdjoint_gc (g.comp f) _).u_unique
    ((ordinalRightAdjoint_gc f hf).compose (ordinalRightAdjoint_gc g hg)) (fun _ => rfl)

/-- 概要：恒等射の左随伴は同じ恒等射。
方針：Galois左随伴の一意性。規約：同じ有限順序集合上。
使われ方：Riehl–Verity Observation 3.3.6 の逆方向の反変関手。 -/
lemma ordinalLeftAdjoint_id (m : ℕ) :
    ordinalLeftAdjoint (OrderHom.id : Fin (m + 1) →o Fin (m + 1)) rfl = OrderHom.id := by
  apply OrderHom.ext
  funext i
  exact (ordinalLeftAdjoint_gc OrderHom.id rfl).l_unique GaloisConnection.id (fun _ => rfl)

/-- 概要：左随伴は有限単調射の合成の順序を反転する。
方針：Galois随伴の合成と左随伴の一意性。規約：元の射を変えない。
使われ方：Riehl–Verity Observation 3.3.6 の混合Homの逆の対応。 -/
lemma ordinalLeftAdjoint_comp (f : Fin (n + 1) →o Fin (m + 1))
    (g : Fin (k + 1) →o Fin (n + 1))
    (hf : f (Fin.last n) = Fin.last m) (hg : g (Fin.last k) = Fin.last n) :
    ordinalLeftAdjoint (f.comp g) (by change f (g (Fin.last k)) = Fin.last m; rw [hg, hf]) =
      (ordinalLeftAdjoint g hg).comp (ordinalLeftAdjoint f hf) := by
  apply OrderHom.ext
  funext i
  exact (ordinalLeftAdjoint_gc (f.comp g) _).l_unique
    ((ordinalLeftAdjoint_gc f hf).compose (ordinalLeftAdjoint_gc g hg)) (fun _ => rfl)

end SerrePositivity.InfinityCategories.HA.Monads
