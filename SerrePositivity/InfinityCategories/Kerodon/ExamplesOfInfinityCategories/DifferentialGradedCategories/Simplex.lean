module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.DifferentialGraded.Category.Basic
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index

/-! # dg nerve の単体

概要：有限部分集合で添字付けた斉次射と HA の方程式を持つ単体を定義する。
方針：端点と次数を射の引数に取り、削除・切断の等式を証明引数で吸収する。
規約：HA Construction 1.3.1.6、微分は +1、成分の次数は `2-|I|`。
使われ方：単体的構造とホーン充填のデータの型となる。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open DifferentialGraded
open scoped BigOperators

variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

/-- 概要：固定した頂点族の間の全斉次成分の型。
方針：端点・次数の等式を引数として cast を避ける。
規約：HA 1.3.1.6、各 I の濃度は二以上。使われ方：単体の `hom` フィールド。 -/
abbrev HomFamily {n : ℕ} (obj : Fin (n + 1) → D) :=
  ∀ (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ)
    (hI : 2 ≤ I.card),
    a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI) → b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI) →
    k = 2 - (I.card : ℤ) → GradedHom A (obj a) (obj b) k

/-- 概要：方程式を課す前の単体データ。
方針：頂点と斉次成分を分離して、方程式の右辺を先に定義する。
規約：HA 1.3.1.6 の有限部分集合表示。使われ方：`Simplex` のデータ部分。 -/
structure SimplexData (n : ℕ) where
  /-- 頂点番号ごとの dg 圏の対象。 -/
  obj : Fin (n + 1) → D
  /-- 二点以上の部分集合ごとの、指定した端点と次数を持つ射。 -/
  hom : HomFamily A D obj

variable {A D}

namespace SimplexData

variable {n : ℕ} (s : SimplexData A D n)

/-- 概要：単体の方程式の一つの内部点の寄与。
方針：削除成分と左右切断の合成の差に符号を掛ける。
規約：HA 1.3.1.6 の通常順合成。使われ方：`rhs` の有限和の項。 -/
def term (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ)
    (hI : 2 ≤ I.card) (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hk : k = 2 - (I.card : ℤ))
    (j : Fin (n + 1)) (hj : j ∈ I) (haj : a < j) (hjb : j < b) :
    GradedHom A (s.obj a) (s.obj b) (k + 1) := by
  have hamin : IsLeast (I : Set (Fin (n + 1))) a := by
    rw [ha]; exact I.isLeast_min' _
  have hbmax : IsGreatest (I : Set (Fin (n + 1))) b := by
    rw [hb]; exact I.isGreatest_max' _
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.erase_two hamin.1 hbmax.1 haj hjb
  have hl := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.left_two hamin.1 hj haj
  have hr := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.right_two hj hbmax.1 hjb
  let fe := s.hom (I.erase j) a b (k + 1) he
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.erase_min hamin haj _) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.erase_max hbmax hjb _) (by
      have := Finset.card_erase_add_one hj
      omega)
  let fl := s.hom (I.filter (· ≤ j)) a j (2 - ((I.filter (· ≤ j)).card : ℤ)) hl
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.left_min hamin haj.le _) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.left_max hj _) rfl
  let fr := s.hom (I.filter (j ≤ ·)) j b (2 - ((I.filter (j ≤ ·)).card : ℤ)) hr
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.right_min hj _) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.right_max hbmax hjb.le _) rfl
  exact ((I.filter (j < ·)).card : ℤ).negOnePow •
    (fe - compose A fr fl (by have := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.split_card hj; omega))

/-- 概要：単体の方程式の右辺は内部点にわたる有限和。
方針：所属証明を持つ有限型 I で和を取り、端点では寄与を零とする。
規約：HA 1.3.1.6、符号の指数は j より大きい点の数。使われ方：`Simplex.equation`。 -/
def rhs (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ)
    (hI : 2 ≤ I.card) (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hk : k = 2 - (I.card : ℤ)) :
    GradedHom A (s.obj a) (s.obj b) (k + 1) :=
  ∑ j : I, if h : a < j.val ∧ j.val < b then
    s.term I a b k hI ha hb hk j.val j.property h.1 h.2 else 0

end SimplexData

variable (A D)

/-- 概要：dg nerve の n 単体は頂点と HA の方程式を満たす斉次射の族。
方針：`SimplexData` に微分の式を課す。
規約：HA Construction 1.3.1.6、cochain 次数 `2-|I|`。
使われ方：後続の `dgNerve` の各次数の型。単体的構造の存在はこの定義に含めない。 -/
structure Simplex (n : ℕ) extends SimplexData A D n where
  /-- 全ての二点以上の部分集合で HA の微分方程式が成り立つ。 -/
  equation : ∀ (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ)
    (hI : 2 ≤ I.card) (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hk : k = 2 - (I.card : ℤ)),
    differential A (hom I a b k hI ha hb hk) = toSimplexData.rhs I a b k hI ha hb hk

variable {A D}

namespace SimplexData

/-- 概要：頂点と斉次成分が一致するデータは等しい。
方針：構造体の成分の等式を使う。規約：HA 1.3.1.6。
使われ方：頂点を取り替えた際の従属する射族の比較。 -/
lemma ext {n : ℕ} {s t : SimplexData A D n} (hobj : s.obj = t.obj)
    (hhom : HEq s.hom t.hom) : s = t := by
  cases s
  cases t
  cases hobj
  cases hhom
  rfl

end SimplexData

/-- 概要：零単体の射族は頂点族にかかわらず一意。
方針：濃度二以上の部分集合が存在しないことから従属関数の外延性を使う。
規約：HA Example 1.3.1.8。使われ方：零単体の同値の逆写像の確認。 -/
lemma zero_hom_heq {obj obj' : Fin 1 → D}
    (f : HomFamily A D obj) (g : HomFamily A D obj') : HEq f g := by
  apply Function.hfunext rfl
  intro I I' h
  cases h
  apply Function.hfunext rfl
  intro a a' h
  cases h
  apply Function.hfunext rfl
  intro b b' h
  cases h
  apply Function.hfunext rfl
  intro k k' h
  cases h
  apply Function.hfunext rfl
  intro hI _ _
  have h := Finset.card_le_univ I
  simp only [Fintype.card_fin] at h
  omega

namespace Simplex

/-- 概要：単体は頂点と斉次成分のデータで決まる。
方針：方程式は命題なので証明の一意性を使う。
規約：HA 1.3.1.6。使われ方：単体的恒等式の検証。 -/
lemma ext {n : ℕ} {s t : Simplex A D n} (h : s.toSimplexData = t.toSimplexData) :
    s = t := by
  cases s
  cases t
  cases h
  rfl

/-- 概要：一点の対象は零単体を定める。
方針：`Fin 1` の部分集合に二点以上のものはなく、射族と方程式は空条件。
規約：HA Example 1.3.1.8。使われ方：零単体と対象の同値の逆写像。 -/
def vertex (x : D) : Simplex A D 0 where
  obj _ := x
  hom I _ _ _ hI _ _ _ := by
    have h := Finset.card_le_univ I
    simp only [Fintype.card_fin] at h
    omega
  equation I _ _ _ hI _ _ _ := by
    have h := Finset.card_le_univ I
    simp only [Fintype.card_fin] at h
    omega

/-- 概要：dg nerve の零単体は対象と同値。
方針：唯一の頂点を評価し、射族が空条件であることから逆を確認する。
規約：HA Example 1.3.1.8。使われ方：辺の両端と H⁰ の対象の同定。 -/
def vertexEquiv : Simplex A D 0 ≃ D where
  toFun s := s.obj 0
  invFun := vertex
  left_inv s := by
    apply ext
    apply SimplexData.ext
    · funext i
      exact congrArg s.obj (Fin.ext (by omega))
    · exact zero_hom_heq _ _
  right_inv _ := rfl

/-- 概要：単体の任意の二頂点は次数零の射を定める。
方針：二点集合の成分を評価する。
規約：HA Example 1.3.1.8。使われ方：単体の辺と閉次数零射の比較。 -/
def edgeHom {n : ℕ} (s : Simplex A D n) (a b : Fin (n + 1)) (hab : a < b) :
    GradedHom A (s.obj a) (s.obj b) 0 :=
  s.hom {a, b} a b 0 (by simp [ne_of_lt hab])
    (by symm; exact (Finset.min'_eq_iff _ _ _).2 (by simp [hab.le]))
    (by symm; exact (Finset.max'_eq_iff _ _ _).2 (by simp [hab.le]))
    (by simp [ne_of_lt hab])

/-- 概要：単体の各辺は閉次数零射である。
方針：二点集合の内部点がないので方程式の右辺が零になる。
規約：HA Example 1.3.1.8。使われ方：閉零圏および H⁰ 圏への比較。 -/
lemma differential_edgeHom {n : ℕ} (s : Simplex A D n)
    (a b : Fin (n + 1)) (hab : a < b) : differential A (s.edgeHom a b hab) = 0 := by
  unfold edgeHom
  rw [s.equation]
  apply Finset.sum_eq_zero
  intro j _
  have hj := j.property
  simp only [Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with h | h
  · simp [h]
  · simp [h]

/-- 概要：単体の辺を Hom 複体の閉次数零元として読む。
方針：辺の閉性を零 cycle の条件に用いる。
規約：HA Example 1.3.1.8。使われ方：`closedHomEquiv` と接続する。 -/
def edgeCycle {n : ℕ} (s : Simplex A D n) (a b : Fin (n + 1)) (hab : a < b) :
    zeroCycles (homObject A D (s.obj a) (s.obj b)) :=
  ⟨s.edgeHom a b hab, s.differential_edgeHom a b hab⟩

end Simplex

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "1.3.1.6"] _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex
