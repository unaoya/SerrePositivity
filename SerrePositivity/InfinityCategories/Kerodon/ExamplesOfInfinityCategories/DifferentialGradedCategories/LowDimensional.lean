module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex
public import SerrePositivity.DifferentialGraded.Category.Basic

/-! # dg nerve の低次の単体

概要：閉次数零射から一単体を構成し、そのデータを復元する。
方針：`Fin 2` の二点以上の部分集合は全体集合であることを使う。
規約：HA Example 1.3.1.8。使われ方：辺と閉零圏の射の比較。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open DifferentialGraded

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：`Fin 2` の二点以上の部分集合は全体集合。
方針：全体集合との濃度比較。規約：HA 1.3.1.6。
使われ方：一単体の成分の評価。 -/
lemma two_eq_univ (I : Finset (Fin 2)) (hI : 2 ≤ I.card) : I = Finset.univ :=
  Finset.eq_of_subset_of_card_le (Finset.subset_univ _) (by simpa using hI)

namespace SimplexData

/-- 概要：二頂点と閉次数零元は一単体のデータを定める。
方針：部分集合の濃度条件から端点と次数がそれぞれ 0,1,0 と決まる。
規約：HA Example 1.3.1.8。使われ方：`Simplex.ofEdge` のデータ。 -/
def ofEdge (obj : Fin 2 → D) (f : zeroCycles (homObject A D (obj 0) (obj 1))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D 1 where
  obj := obj
  hom I a b k hI ha hb hk := by
    have h := two_eq_univ I hI
    subst I
    have ha' : a = 0 :=
      ha.trans ((Finset.min'_eq_iff _ _ 0).2 ⟨by simp, fun x _ => Fin.zero_le x⟩)
    have hb' : b = 1 :=
      hb.trans ((Finset.max'_eq_iff _ _ 1).2 ⟨by simp, fun x _ => Fin.le_last x⟩)
    have hk' : k = 0 := by simpa using hk
    subst ha' hb' hk'
    exact f.val

end SimplexData

namespace Simplex

/-- 概要：二頂点と閉次数零元は一単体を定める。
方針：唯一の成分の微分は閉性により零で、内部点がないので右辺も零。
規約：HA Example 1.3.1.8。使われ方：一単体と閉零射の同値の逆写像。 -/
def ofEdge (obj : Fin 2 → D) (f : zeroCycles (homObject A D (obj 0) (obj 1))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D 1 where
  toSimplexData := SimplexData.ofEdge obj f
  equation I a b k hI ha hb hk := by
    have h := two_eq_univ I hI
    subst I
    have ha' : a = 0 :=
      ha.trans ((Finset.min'_eq_iff _ _ 0).2 ⟨by simp, fun x _ => Fin.zero_le x⟩)
    have hb' : b = 1 :=
      hb.trans ((Finset.max'_eq_iff _ _ 1).2 ⟨by simp, fun x _ => Fin.le_last x⟩)
    have hk' : k = 0 := by simpa using hk
    subst ha' hb' hk'
    change differential A f.val = _
    rw [show differential A f.val = 0 from f.property]
    symm
    apply Finset.sum_eq_zero
    intro j _
    have hj : ¬ ((0 : Fin 2) < j.val ∧ j.val < 1) := by
      intro h
      have := h.1
      have := h.2
      omega
    exact dite_eq_right hj

/-- 概要：閉零元から構成した一単体の辺は元の元である。
方針：定義の評価と証明の一意性。規約：HA Example 1.3.1.8。
使われ方：辺の同値の右逆の確認。 -/
lemma edgeCycle_ofEdge (obj : Fin 2 → D)
    (f : zeroCycles (homObject A D (obj 0) (obj 1))) :
    (ofEdge obj f).edgeCycle 0 1 (by decide) = f := by
  apply Subtype.ext
  rfl

/-- 概要：一単体をその頂点と辺から再構成すると元に戻る。
方針：二点以上の部分集合は全体集合だけなので全成分が元の辺に一致する。
規約：HA Example 1.3.1.8。使われ方：辺の同値の左逆の確認。 -/
lemma ofEdge_edgeCycle (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D 1) :
    ofEdge s.obj (s.edgeCycle 0 1 (by decide)) = s := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  refine _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.ext (s := (ofEdge s.obj (s.edgeCycle 0 1 (by decide))).toSimplexData)
    (t := s.toSimplexData) rfl ?_
  apply heq_of_eq
  funext I a b k hI ha hb hk
  have h := two_eq_univ I hI
  subst I
  have ha' : a = 0 :=
      ha.trans ((Finset.min'_eq_iff _ _ 0).2 ⟨by simp, fun x _ => Fin.zero_le x⟩)
  have hb' : b = 1 :=
      hb.trans ((Finset.max'_eq_iff _ _ 1).2 ⟨by simp, fun x _ => Fin.le_last x⟩)
  have hk' : k = 0 := by simpa using hk
  subst ha' hb' hk'
  rfl

/-- 概要：一単体は二頂点とその間の閉次数零射に等しい情報を持つ。
方針：辺の評価と `ofEdge` が互いに逆であることを使う。
規約：HA Example 1.3.1.8。使われ方：ホモトピー圏の射の比較。 -/
def edgeEquiv : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D 1 ≃
    Σ obj : Fin 2 → D, zeroCycles (homObject A D (obj 0) (obj 1)) where
  toFun s := ⟨s.obj, s.edgeCycle 0 1 (by decide)⟩
  invFun f := ofEdge f.1 f.2
  left_inv := ofEdge_edgeCycle
  right_inv f := by
    rcases f with ⟨obj, f⟩
    exact congrArg (Sigma.mk obj) (edgeCycle_ofEdge obj f)

/-- 概要：単体の辺は既存の閉零圏の射を定める。
方針：`closedHomEquiv` の逆を閉次数零元に適用する。
規約：HA Example 1.3.1.8。使われ方：N3 の H⁰ 圏への比較。 -/
def edgeClosed {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D n) (a b : Fin (n + 1)) (hab : a < b) :
    CategoryTheory.ForgetEnrichment.of (Complex A) (s.obj a) ⟶
      CategoryTheory.ForgetEnrichment.of (Complex A) (s.obj b) :=
  (closedHomEquiv A D _ _).symm (s.edgeCycle a b hab)

/-- 概要：二単体の高次成分は次数 −1 の射である。
方針：全体集合の端点と濃度を評価する。
規約：HA Example 1.3.1.8。使われ方：三角形のホモトピー成分。 -/
def triangleHom (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D 2) : GradedHom A (s.obj 0) (s.obj 2) (-1) :=
  s.hom Finset.univ 0 2 (-1) (by decide) (by decide) (by decide) (by decide)

/-- 概要：二単体の微分は二辺の合成と第三辺の差に等しい。
方針：全体集合の方程式の内部点は 1 のみであることを計算する。
規約：HA Example 1.3.1.8。使われ方：N3 の合成・ホモトピーの判定。 -/
lemma differential_triangleHom (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D 2) :
    differential A s.triangleHom =
      compose A (s.edgeHom 1 2 (by decide)) (s.edgeHom 0 1 (by decide)) (by decide) -
        s.edgeHom 0 2 (by decide) := by
  unfold triangleHom
  rw [s.equation]
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.rhs
  rw [Finset.sum_coe_sort_eq_attach, Finset.sum_attach_univ]
  have he : (Finset.univ : Finset (Fin 3)).erase 1 = {0, 2} := by decide
  have hl : (Finset.univ : Finset (Fin 3)).filter (· ≤ 1) = {0, 1} := by decide
  have hr : (Finset.univ : Finset (Fin 3)).filter (1 ≤ ·) = {1, 2} := by decide
  have hs : ((Finset.univ : Finset (Fin 3)).filter (1 < ·)).card = 1 := by decide
  norm_num [Fin.sum_univ_succ]
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.term, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.edgeHom, he, hl, hr, hs]
  norm_num
  congr 2

end Simplex

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
