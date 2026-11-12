module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NestedCut

/-! # 厳密 dg 自然変換と二相の斉次写像

概要：閉零成分と全斉次射に対する厳密自然性を持つ dg 自然変換を定義する。
方針：二相の対象を F と G で写し、相をまたぐ射には自然変換の成分を合成する。
規約：HA Construction 1.3.1.6。使われ方：dg nerve 上の単体的ホモトピーの各成分。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v w

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open CategoryTheory DifferentialGraded

variable {A : Type u} [CommRing A] {D : Type v} {E : Type w}
  [DGCategory A D] [DGCategory A E]

/-- 概要：厳密 dg 自然変換は閉次数零成分と全斉次射に対する自然性からなる。
方針：既存の dg 関手の間に、通常順合成による自然性を直接課す。
規約：HA Construction 1.3.1.6、成分の次数は零で追加の符号はない。
使われ方：dg nerve の二つの写像を結ぶ単体的ホモトピー。 -/
structure StrictNatTrans (F G : DGFunctor A D E) where
  /-- 各対象の閉次数零の成分。 -/
  app : ∀ x, zeroCycles (homObject A E (F.obj x) (G.obj x))
  /-- 全ての斉次射に対する厳密自然性。 -/
  naturality : ∀ {x y : D} {k : ℤ} (f : GradedHom A x y k),
    compose A (app y).val ((F.map x y).f k f) (add_zero k) =
      compose A ((G.map x y).f k f) (app x).val (zero_add k)

namespace StrictNatTrans

variable {F G : DGFunctor A D E} (η : StrictNatTrans F G)

/-- 概要：相零では F、相一では G による対象を選ぶ。
方針：有限二点型の分岐を使う。
規約：HA Construction 1.3.1.6。使われ方：切れ目で対象を F と G に分ける。 -/
@[reducible]
def phaseObj (F G : DGFunctor A D E) (p : Fin 2) (x : D) : E :=
  Fin.cases (F.obj x) (fun _ => G.obj x) p

/-- 概要：昇順の二相の間の射は F、G、または自然変換と F の合成で定まる。
方針：零から一へだけ相をまたげることを用い、逆向きの相を除く。
規約：HA Construction 1.3.1.6。使われ方：ホモトピー単体の各有限部分集合の射。 -/
def transition (η : StrictNatTrans F G) {x y : D} {k : ℤ}
    (p q : Fin 2) (hpq : p ≤ q) (f : GradedHom A x y k) :
    GradedHom A (phaseObj F G p x) (phaseObj F G q y) k := by
  rcases p with ⟨p, hp⟩
  rcases q with ⟨q, hq⟩
  cases p with
  | zero =>
    cases q with
    | zero => exact (F.map x y).f k f
    | succ q =>
      have hq0 : q = 0 := by omega
      subst q
      exact compose A (η.app y).val ((F.map x y).f k f) (add_zero k)
  | succ p =>
    have hp0 : p = 0 := by omega
    subst p
    cases q with
    | zero => exact False.elim (by simp at hpq)
    | succ q =>
      have hq0 : q = 0 := by omega
      subst q
      exact (G.map x y).f k f

/-- 概要：相零同士の写像は F の斉次写像。
方針：有限二相の定義の最初の分岐を評価する。
規約：HA Construction 1.3.1.6。使われ方：ホモトピーの始端の計算。 -/
lemma transition_00 {x y : D} {k : ℤ} (h : (0 : Fin 2) ≤ 0) (f : GradedHom A x y k) :
    η.transition 0 0 h f = (F.map x y).f k f := rfl

/-- 概要：相をまたぐ写像は自然変換成分と F の像の通常順合成。
方針：有限二相の定義の混合分岐を評価する。
規約：HA Construction 1.3.1.6。使われ方：切れ目をまたぐ単体成分の計算。 -/
lemma transition_01 {x y : D} {k : ℤ} (h : (0 : Fin 2) ≤ 1) (f : GradedHom A x y k) :
    η.transition 0 1 h f = compose A (η.app y).val ((F.map x y).f k f) (add_zero k) := rfl

/-- 概要：相一同士の写像は G の斉次写像。
方針：有限二相の定義の最後の分岐を評価する。
規約：HA Construction 1.3.1.6。使われ方：ホモトピーの終端の計算。 -/
lemma transition_11 {x y : D} {k : ℤ} (h : (1 : Fin 2) ≤ 1) (f : GradedHom A x y k) :
    η.transition 1 1 h f = (G.map x y).f k f := rfl

/-- 概要：二相の斉次写像は零を保つ。
方針：三つの有効な相の組を分け、線形写像と合成の零の保存を使う。
規約：HA Construction 1.3.1.6。使われ方：高次の退化した零成分の保存。 -/
lemma transition_zero {x y : D} {k : ℤ} (p q : Fin 2) (hpq : p ≤ q) :
    η.transition p q hpq (0 : GradedHom A x y k) = 0 := by
  fin_cases p <;> fin_cases q <;> simp at hpq
  all_goals simp [transition_00, transition_01, transition_11, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_zero]

/-- 概要：二相の斉次写像は差を保つ。
方針：三つの有効な相の組を分け、線形性と合成の加法性を使う。
規約：HA Construction 1.3.1.6。使われ方：単体方程式の差の移送。 -/
lemma transition_sub {x y : D} {k : ℤ} (p q : Fin 2) (hpq : p ≤ q)
    (f g : GradedHom A x y k) : η.transition p q hpq (f - g) =
      η.transition p q hpq f - η.transition p q hpq g := by
  fin_cases p <;> fin_cases q <;> simp at hpq
  all_goals simp [transition_00, transition_01, transition_11, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_sub_right]

/-- 概要：二相の斉次写像は整数の符号スカラーを保つ。
方針：三つの有効な相の組を分け、線形性と合成のスカラー保存を使う。
規約：HA Construction 1.3.1.6。使われ方：単体方程式の符号付き和の移送。 -/
lemma transition_smul {x y : D} {k : ℤ} (p q : Fin 2) (hpq : p ≤ q)
    (c : ℤˣ) (f : GradedHom A x y k) :
    η.transition p q hpq (c • f) = c • η.transition p q hpq f := by
  fin_cases p <;> fin_cases q <;> simp at hpq
  · change (F.map x y).f k (c • f) = c • (F.map x y).f k f
    simp [Units.smul_def]
  · change compose A (η.app y).val ((F.map x y).f k (c • f)) (add_zero k) =
      c • compose A (η.app y).val ((F.map x y).f k f) (add_zero k)
    have hs : (F.map x y).f k (c • f) = c • (F.map x y).f k f := by
      simp [Units.smul_def]
    rw [hs]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_units_smul_right c _ _ (add_zero k)
  · change (G.map x y).f k (c • f) = c • (G.map x y).f k f
    simp [Units.smul_def]

/-- 概要：二相の斉次写像は微分と可換。
方針：相をまたぐ場合には自然変換の成分の閉性と Leibniz 則を使う。
規約：HA Construction 1.3.1.6。使われ方：ホモトピー単体の方程式の左辺の移送。 -/
lemma transition_differential {x y : D} {k : ℤ} (p q : Fin 2) (hpq : p ≤ q)
    (f : GradedHom A x y k) :
    η.transition p q hpq (differential A f) = differential A (η.transition p q hpq f) := by
  fin_cases p <;> fin_cases q <;> simp at hpq
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.map_differential F f
  · change compose A (η.app y).val ((F.map x y).f (k + 1) (differential A f))
        (add_zero (k + 1)) =
      differential A (compose A (η.app y).val ((F.map x y).f k f) (add_zero k))
    have hη : differential A (η.app y).val = 0 := (η.app y).property
    rw [differential_compose]
    simp only [hη, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.zero_compose, Int.negOnePow_zero, one_smul, zero_add]
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.map_differential]
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.map_differential G f

/-- 概要：三つの昇順の相に沿う写像は通常順の斉次合成を保つ。
方針：四つの有効な相の並びを分け、dg 関手の合成保存、結合律、厳密自然性を使う。
規約：HA Construction 1.3.1.6。使われ方：ホモトピー単体の切断合成の保存。 -/
lemma transition_compose {x y z : D} {i j k : ℤ} (p q r : Fin 2)
    (hpq : p ≤ q) (hqr : q ≤ r) (g : GradedHom A y z j) (f : GradedHom A x y i)
    (hk : i + j = k) :
    η.transition p r (hpq.trans hqr) (compose A g f hk) =
      compose A (η.transition q r hqr g) (η.transition p q hpq f) hk := by
  fin_cases p <;> fin_cases q <;> fin_cases r <;> simp at hpq hqr
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.map_compose F g f hk
  · change compose A (η.app z).val ((F.map x z).f k (compose A g f hk)) (add_zero k) =
      compose A (compose A (η.app z).val ((F.map y z).f j g) (add_zero j))
        ((F.map x y).f i f) hk
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.map_compose]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NestedCut.compose_assoc_of_sum _ _ _ hk (add_zero j) (add_zero k)
  · change compose A (η.app z).val ((F.map x z).f k (compose A g f hk)) (add_zero k) =
      compose A ((G.map y z).f j g)
        (compose A (η.app y).val ((F.map x y).f i f) (add_zero i)) hk
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.map_compose, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NestedCut.compose_assoc_of_sum _ _ _ hk (add_zero j) (add_zero k), η.naturality]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NestedCut.compose_assoc_of_sum _ _ _ (add_zero i) (zero_add j) hk).symm
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.map_compose G g f hk

/-- 概要：同じ相の間では単位を対応する対象の単位へ送る。
方針：相零と相一を分け、既存の dg 関手の単位保存を使う。
規約：HA Construction 1.3.1.6。使われ方：退化した辺の単位の保存。 -/
lemma transition_unit (p : Fin 2) (x : D) :
    η.transition p p le_rfl (unitElement A x).val = (unitElement A (phaseObj F G p x)).val := by
  fin_cases p
  · exact DGFunctor.map_unitElement A F x
  · exact DGFunctor.map_unitElement A G x

/-- 概要：二相の斉次写像は有限和を保つ。
方針：三つの相の組を分け、線形写像と合成の有限和への分配を使う。
規約：HA Construction 1.3.1.6。使われ方：単体方程式の右辺の移送。 -/
lemma transition_sum {ι : Type*} {x y : D} {k : ℤ} (p q : Fin 2) (hpq : p ≤ q)
    (S : Finset ι) (f : ι → GradedHom A x y k) :
    η.transition p q hpq (∑ t ∈ S, f t) = ∑ t ∈ S, η.transition p q hpq (f t) := by
  fin_cases p <;> fin_cases q <;> simp at hpq
  all_goals simp [transition_00, transition_01, transition_11, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_sum_right]

/-- 概要：等しい対象と相の間の単位の像を異種等号で同定する。
方針：対象・相・元の等式を消去し、単位保存へ帰着する。
規約：HA Construction 1.3.1.6。使われ方：潰れた辺の引き戻しとの比較。 -/
lemma transition_unit_of_heq {x y : D} (p q : Fin 2) (hpq : p ≤ q)
    (f : GradedHom A x y 0) (hxy : x = y) (hp : p = q)
    (hf : HEq f (unitElement A y).val) :
    HEq (η.transition p q hpq f) (unitElement A (phaseObj F G q y)).val := by
  subst y
  subst q
  have he : f = (unitElement A x).val := eq_of_heq hf
  subst f
  exact heq_of_eq (η.transition_unit p x)

end StrictNatTrans

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
