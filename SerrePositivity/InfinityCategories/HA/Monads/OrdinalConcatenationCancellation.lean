module

public import SerrePositivity.InfinityCategories.HA.Monads.OrdinalConcatenationLaws

/-!
概要：有限単調射の順序和と端点共有の表示から、二つの因子の射を回収する。
方針：左の包含と右の包含で評価し、共有する最小元の値を明示する。
規約：因子の個数を固定した等式の反映である。
使われ方：HA Proposition 4.7.3.3、Riehl–Verity Proposition 3.1.10・Remark 3.3.8、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の原子的な分解の一意性。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：順序和の射の等式は二つの因子の射の等式を反映する。
方針：二つの包含上で評価する。規約：空の因子も含む。
使われ方：Riehl–Verity Proposition 3.1.10 の水平分解の照合。 -/
lemma ordinalAppend_inj {m n p q : ℕ}
    {f f' : Fin m →o Fin n} {g g' : Fin p →o Fin q}
    (h : ordinalAppend f g = ordinalAppend f' g') : f = f' ∧ g = g' := by
  constructor
  · apply OrderHom.ext
    funext i
    apply Fin.castAdd_injective n q
    have hi := congrArg (fun k : Fin (m + p) →o Fin (n + q) => k (i.castAdd p)) h
    simpa only [ordinalAppend_castAdd] using hi
  · apply OrderHom.ext
    funext i
    apply Fin.natAdd_injective q n
    have hi := congrArg (fun k : Fin (m + p) →o Fin (n + q) => k (i.natAdd m)) h
    simpa only [ordinalAppend_natAdd] using hi

/-- 概要：端点共有の射の等式は左の因子の全射を反映する。
方針：共有点までの包含上で評価する。規約：共有点を落とさない。
使われ方：Riehl–Verity Proposition 3.1.10 の左の射の回収。 -/
lemma ordinalGlue_left_inj {m n p q : ℕ}
    {f f' : Fin (m + 1) →o Fin (n + 1)} {g g' : Fin (p + 1) →o Fin (q + 1)}
    (h : ordinalGlue f g = ordinalGlue f' g') : f = f' := by
  apply OrderHom.ext
  funext i
  apply Fin.ext
  have hi := congrArg
    (fun k : Fin (m + p + 1) →o Fin (n + q + 1) =>
      (k ⟨i.val, by have := i.isLt; omega⟩).val) h
  simpa only [ordinalGlue_val_left] using hi

/-- 概要：端点共有の右因子の射は、最小元の保存と合成の射から回収できる。
方針：最小元を別に照合し、他の点は共有点の後で評価する。
規約：元の最小元の条件を仮定として明示する。
使われ方：Riehl–Verity Proposition 3.1.10 の右の射の回収。 -/
lemma ordinalGlue_right_inj {m n p q : ℕ}
    {f f' : Fin (m + 1) →o Fin (n + 1)} {g g' : Fin (p + 1) →o Fin (q + 1)}
    (hg : g 0 = 0) (hg' : g' 0 = 0)
    (h : ordinalGlue f g = ordinalGlue f' g') : g = g' := by
  apply OrderHom.ext
  funext i
  by_cases hi : i = 0
  · subst i
    exact hg.trans hg'.symm
  · apply Fin.ext
    have hipos : 0 < i.val := by
      have hne : i.val ≠ 0 := fun h => hi (Fin.ext h)
      omega
    have he := congrArg
      (fun k : Fin (m + p + 1) →o Fin (n + q + 1) =>
        (k ⟨m + i.val, by have := i.isLt; omega⟩).val) h
    rw [ordinalGlue_val_of_lt _ _ _ (by change m < m + i.val; omega),
      ordinalGlue_val_of_lt _ _ _ (by change m < m + i.val; omega)] at he
    dsimp only at he
    have hk : (⟨m + i.val - m, by omega⟩ : Fin (p + 1)) = i :=
      Fin.ext (by change m + i.val - m = i.val; omega)
    change n + (g ⟨m + i.val - m, by omega⟩).val =
      n + (g' ⟨m + i.val - m, by omega⟩).val at he
    rw [hk] at he
    omega

/-- 概要：端点共有は最小元を保つ右因子との組の等式を反映する。
方針：左と右の回収を合わせる。規約：因子の個数は固定。
使われ方：Riehl–Verity Proposition 3.1.10 の水平分解の照合。 -/
lemma ordinalGlue_inj {m n p q : ℕ}
    {f f' : Fin (m + 1) →o Fin (n + 1)} {g g' : Fin (p + 1) →o Fin (q + 1)}
    (hg : g 0 = 0) (hg' : g' 0 = 0)
    (h : ordinalGlue f g = ordinalGlue f' g') : f = f' ∧ g = g' :=
  ⟨ordinalGlue_left_inj h, ordinalGlue_right_inj hg hg' h⟩

end SerrePositivity.InfinityCategories.HA.Monads
