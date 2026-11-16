module

public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionVertices

/-!
概要：零次元の実walking adjunctionの射は二つの生成射の道と一対一に対応する。
方針：同じ長さの交互の道の一意性と、偶数・奇数の標準語で検収する。
規約：全頂点の射を覆う。使われ方：HA Proposition 4.7.3.3、
Riehl–Verity Proposition 3.1.10・Theorem 4.3.9、Kerodon Remark 6.2.1.4（Tag 02EN）。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：異なる二点を結ぶ生成quiverの射。
方針：他方の点への唯一の射を指定する。規約：自己生成射を加えない。
使われ方：Riehl–Verity Example 3.1.11 のf・u。 -/
def walkingAdjunctionGeneratingArrow (X : WalkingAdjunctionPoint) :
    X ⟶ walkingAdjunctionOther X := ⟨by cases X <;> decide⟩

/-- 概要：偶数長の標準の交互の道。
方針：生成射と戻る生成射を一組ずつ後置する。
規約：同じ始点に戻る。使われ方：Riehl–Verity Proposition 3.1.10 の自己Homの全頂点。 -/
def walkingAdjunctionEvenPath (X : WalkingAdjunctionPoint) : ℕ → Quiver.Path X X
  | 0 => .nil
  | n + 1 => ((walkingAdjunctionEvenPath X n).cons
      (walkingAdjunctionGeneratingArrow X)).cons
        (show walkingAdjunctionOther X ⟶ X from ⟨by cases X <;> decide⟩)

/-- 概要：奇数長の標準の交互の道。
方針：偶数語の後にもう一つの生成射を置く。
規約：他方の点に到着する。使われ方：Riehl–Verity Proposition 3.1.10 の混合Homの全頂点。 -/
def walkingAdjunctionOddPath (X : WalkingAdjunctionPoint) (n : ℕ) :
    Quiver.Path X (walkingAdjunctionOther X) :=
  (walkingAdjunctionEvenPath X n).cons (walkingAdjunctionGeneratingArrow X)

/-- 概要：標準の偶数語の道としての長さ。
方針：語の帰納法を使う。規約：二つの生成射で一組。
使われ方：Riehl–Verity Proposition 3.1.10 の全射性。 -/
lemma walkingAdjunctionEvenPath_length (X : WalkingAdjunctionPoint) (n : ℕ) :
    (walkingAdjunctionEvenPath X n).length = 2 * n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [walkingAdjunctionEvenPath, Quiver.Path.length] at *
    omega

/-- 概要：標準の奇数語の道としての長さ。
方針：偶数語の長さに1を加える。規約：同じ道の表示。
使われ方：Riehl–Verity Proposition 3.1.10 の混合Homの全射性。 -/
lemma walkingAdjunctionOddPath_length (X : WalkingAdjunctionPoint) (n : ℕ) :
    (walkingAdjunctionOddPath X n).length = 2 * n + 1 := by
  change (walkingAdjunctionEvenPath X n).length + 1 = _
  rw [walkingAdjunctionEvenPath_length]

/-- 概要：異なる二点の終点は他方の点に決まる。
方針：二点を場合分けする。規約：同じ生成quiver。
使われ方：Riehl–Verity Proposition 3.1.10 の語の一意性。 -/
lemma walkingAdjunctionOther_of_ne {X Y : WalkingAdjunctionPoint} (h : X ≠ Y) :
    Y = walkingAdjunctionOther X := by
  cases X <;> cases Y <;> simp_all [walkingAdjunctionOther]

/-- 概要：同じ始点と長さを持つ二つの生成語は終点を含めて一致する。
方針：道の帰納法と、各点から出る生成射が一つであることを使う。
規約：終点の異種等式を保持する。使われ方：Riehl–Verity Proposition 3.1.10 の自由性。 -/
lemma walkingAdjunctionGeneratingPath_hext {X Y Z : WalkingAdjunctionPoint}
    (p : Quiver.Path X Y) (q : Quiver.Path X Z) (h : p.length = q.length) :
    Y = Z ∧ HEq p q := by
  induction p generalizing Z with
  | nil =>
    cases q with
    | nil => exact ⟨rfl, HEq.rfl⟩
    | cons q e => simp only [Quiver.Path.length] at h; omega
  | @cons Y Y' p e ih =>
    cases q with
    | nil => simp only [Quiver.Path.length] at h; omega
    | @cons Z Z' q f =>
      obtain ⟨hYZ, hpq⟩ := ih q (Nat.succ.inj h)
      cases hYZ
      have hlast := (walkingAdjunctionOther_of_ne e.down).trans
        (walkingAdjunctionOther_of_ne f.down).symm
      cases hlast
      have hpq' : p = q := eq_of_heq hpq
      cases hpq'
      have hef : e = f := by cases e; cases f; rfl
      cases hef
      exact ⟨rfl, HEq.rfl⟩

/-- 概要：自由な生成語から実頂点への合成は単射。
方針：実像の長さから道の長さを戻す。
規約：対象の同一視だけにしない。使われ方：Riehl–Verity Proposition 3.1.10 の自由性。 -/
instance walkingAdjunctionPathFunctor_faithful : walkingAdjunctionPathFunctor.Faithful where
  map_injective {X Y} p q h := by
    apply eq_of_heq (walkingAdjunctionGeneratingPath_hext p q ?_).2
    have hp := walkingAdjunctionPathFunctor_length p
    have hq := walkingAdjunctionPathFunctor_length q
    rw [h] at hp
    exact hp.symm.trans hq

/-- 概要：全ての実頂点の射は生成語の像。
方針：四Homの各頂点に偶数または奇数の標準語を与える。
規約：空の自己Homも含む。使われ方：Riehl–Verity Proposition 3.1.10 の零次元の全射性。 -/
instance walkingAdjunctionPathFunctor_full : walkingAdjunctionPathFunctor.Full where
  map_surjective {X Y} A := by
    change ∃ p : Quiver.Path (V := WalkingAdjunctionPoint) X Y,
      walkingAdjunctionPathFunctor.map p = A
    cases X <;> cases Y
    · refine ⟨walkingAdjunctionEvenPath .plus (augmentedOrdinalCard A), ?_⟩
      apply walkingAdjunctionVertexLength_injective .plus .plus
      rw [walkingAdjunctionPathFunctor_length, walkingAdjunctionEvenPath_length]
      rfl
    · refine ⟨walkingAdjunctionOddPath .plus A.obj.len, ?_⟩
      apply walkingAdjunctionVertexLength_injective .plus .minus
      rw [walkingAdjunctionPathFunctor_length, walkingAdjunctionOddPath_length]
      rfl
    · refine ⟨walkingAdjunctionOddPath .minus A.obj.len, ?_⟩
      apply walkingAdjunctionVertexLength_injective .minus .plus
      rw [walkingAdjunctionPathFunctor_length, walkingAdjunctionOddPath_length]
      rfl
    · refine ⟨walkingAdjunctionEvenPath .minus (augmentedOrdinalCard (Opposite.unop A)), ?_⟩
      apply walkingAdjunctionVertexLength_injective .minus .minus
      rw [walkingAdjunctionPathFunctor_length, walkingAdjunctionEvenPath_length]
      rfl

end SerrePositivity.InfinityCategories.HA.Monads
