module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.DGNerveBasic
public import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence

/-! # dg 関手による単体データの像

概要：dg 関手は dg nerve の単体の微分方程式を保つ。
方針：各 Hom 複体の chain map を斉次成分に適用し、線形性・合成・単位の保存を使う。
規約：HA Construction 1.3.1.6。使われ方：dg nerve の関手性の構成。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v w t

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open CategoryTheory DifferentialGraded

variable {A : Type u} [CommRing A] {D : Type v} {E : Type w} {T : Type t}
  [DGCategory A D] [DGCategory A E] [DGCategory A T]

/-- 概要：dg 関手の斉次写像は微分を保つ。
方針：Hom 複体の chain map の可換性を元で評価する。
規約：HA Construction 1.3.1.6。使われ方：単体の方程式の左辺の移送。 -/
lemma map_differential (F : DGFunctor A D E) {x y : D} {k : ℤ} (f : GradedHom A x y k) :
    (F.map x y).f (k + 1) (differential A f) = differential A ((F.map x y).f k f) :=
  (ConcreteCategory.congr_hom ((F.map x y).comm k (k + 1)) f).symm

/-- 概要：dg 関手の斉次写像は通常順合成を保つ。
方針：既存の豊穣順合成の保存と整数符号の線形性を使う。
規約：HA Construction 1.3.1.6。使われ方：単体の方程式の切断合成の移送。 -/
lemma map_compose (F : DGFunctor A D E) {x y z : D} {p q k : ℤ}
    (g : GradedHom A y z q) (f : GradedHom A x y p) (hk : p + q = k) :
    (F.map x z).f k (compose A g f hk) =
      compose A ((F.map y z).f q g) ((F.map x y).f p f) hk := by
  simp only [compose, Units.smul_def, map_zsmul, DGFunctor.map_forward]

/-- 概要：対象の等式で移送した単位の像は、像の対象の単位と異種等号で一致する。
方針：対象の等式と元の単位の同定を消去し、dg 関手の単位保存を使う。
規約：HA Construction 1.3.1.6。使われ方：潰れた辺の退化の像。 -/
lemma map_unit_of_heq (F : DGFunctor A D E) {x y : D} (f : GradedHom A x y 0)
    (hxy : x = y) (hf : HEq f (unitElement A y).val) :
    HEq ((F.map x y).f 0 f) (unitElement A (F.obj y)).val := by
  subst y
  have he : f = (unitElement A x).val := eq_of_heq hf
  subst f
  exact heq_of_eq (DGFunctor.map_unitElement A F x)

namespace SimplexData

/-- 概要：dg 関手で単体の全対象と斉次成分を写したデータ。
方針：Hom 複体の chain map の各次数の線形写像を適用する。
規約：HA Construction 1.3.1.6。使われ方：単体と単体的写像の像の構成。 -/
def map {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n) (F : DGFunctor A D E) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A E n where
  obj a := F.obj (s.obj a)
  hom I a b k hI ha hb hk := (F.map (s.obj a) (s.obj b)).f k (s.hom I a b k hI ha hb hk)

/-- 概要：dg 関手は内部点の一項を対応する像の項に送る。
方針：符号・差・合成の保存を使う。
規約：HA Construction 1.3.1.6。使われ方：単体の方程式の右辺の移送。 -/
lemma map_term {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n) (F : DGFunctor A D E)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (j : Fin (n + 1)) (hj : j ∈ I) (haj : a < j) (hjb : j < b) :
    (F.map (s.obj a) (s.obj b)).f (k + 1) (s.term I a b k hI ha hb hk j hj haj hjb) =
      (s.map F).term I a b k hI ha hb hk j hj haj hjb := by
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.term, map, Units.smul_def, map_zsmul, map_sub, map_compose]

/-- 概要：dg 関手は単体の方程式の右辺を対応する像の右辺に送る。
方針：有限和への分配と内部点の項の保存を使う。
規約：HA Construction 1.3.1.6。使われ方：方程式の保存の証明。 -/
lemma map_rhs {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n) (F : DGFunctor A D E)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) :
    (F.map (s.obj a) (s.obj b)).f (k + 1) (s.rhs I a b k hI ha hb hk) =
      (s.map F).rhs I a b k hI ha hb hk := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.rhs
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hint : a < j.val ∧ j.val < b
  · simp only [dite_eq_left hint, map_term]
  · simp only [dite_eq_right hint, map_zero]

end SimplexData

namespace Simplex

/-- 概要：dg 関手は dg nerve の単体を単体に送る。
方針：微分と単体方程式の右辺の保存を組み合わせる。
規約：HA Construction 1.3.1.6。使われ方：dg nerve の写像の各次数。 -/
def map {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D n) (F : DGFunctor A D E) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A E n where
  toSimplexData := s.toSimplexData.map F
  equation I a b k hI ha hb hk := by
    change differential A ((F.map (s.obj a) (s.obj b)).f k (s.hom I a b k hI ha hb hk)) = _
    rw [← map_differential, s.equation, SimplexData.map_rhs]

end Simplex

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
