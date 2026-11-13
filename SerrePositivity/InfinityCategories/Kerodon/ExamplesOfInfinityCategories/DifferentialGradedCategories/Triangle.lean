module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LowDimensional
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.PullbackEquation
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.DGNerveBasic

/-! # 二単体と三角形のデータ

概要：三つの閉零射とその合成の差を埋める次数 −1 の射から二単体を構成する。
方針：`Fin 3` の二点集合と全体集合に場合分けして全成分を与える。
規約：HA Example 1.3.1.8。使われ方：ホモトピー圏での合成とホモトピーの判定。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open DifferentialGraded

variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

/-- 概要：二単体のデータは三頂点、三つの閉零射、および合成の差の原始元。
方針：HA の二単体の方程式を一つの構造体に記録する。
規約：HA Example 1.3.1.8、`δh = f₁₂ ∘ f₀₁ - f₀₂`。
使われ方：実際の二単体との同値の比較先。 -/
structure TriangleData where
  /-- 三頂点。 -/
  obj : Fin 3 → D
  /-- 辺 0→1 の閉零射。 -/
  f01 : zeroCycles (homObject A D (obj 0) (obj 1))
  /-- 辺 1→2 の閉零射。 -/
  f12 : zeroCycles (homObject A D (obj 1) (obj 2))
  /-- 辺 0→2 の閉零射。 -/
  f02 : zeroCycles (homObject A D (obj 0) (obj 2))
  /-- 三角形を埋める次数 −1 の射。 -/
  homotopy : GradedHom A (obj 0) (obj 2) (-1)
  /-- 三角形の微分方程式。 -/
  differential_homotopy : differential A homotopy = compose A f12.val f01.val (by decide) - f02.val

variable {A D}

/-- 概要：`Fin 3` の三点集合は全体集合。
方針：全体集合との濃度比較。規約：HA Example 1.3.1.8。
使われ方：二単体の唯一の高次成分の構成。 -/
lemma three_eq_univ (I : Finset (Fin 3)) (hI : I.card = 3) : I = Finset.univ :=
  Finset.eq_of_subset_of_card_le (Finset.subset_univ _) (by simp [hI])

namespace SimplexData

/-- 概要：単体データの二点成分は次数零の射。
方針：二点集合の端点と濃度で評価する。
規約：HA Example 1.3.1.8。使われ方：二単体の方程式の右辺の計算。 -/
def edgeHom {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n) (a b : Fin (n + 1)) (hab : a < b) :
    GradedHom A (s.obj a) (s.obj b) 0 :=
  s.hom {a, b} a b 0 (by simp [ne_of_lt hab])
    (by symm; exact (Finset.min'_eq_iff _ _ _).2 (by simp [hab.le]))
    (by symm; exact (Finset.max'_eq_iff _ _ _).2 (by simp [hab.le]))
    (by simp [ne_of_lt hab])

/-- 概要：二単体の全体集合における右辺は二辺の合成と第三辺の差。
方針：内部点 1 の唯一の項を計算する。
規約：HA Example 1.3.1.8。使われ方：三角形から単体を作る際の方程式の検証。 -/
lemma rhs_triangle (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D 2) :
    s.rhs Finset.univ 0 2 (-1) (by decide) (by decide) (by decide) (by decide) =
      compose A (s.edgeHom 1 2 (by decide)) (s.edgeHom 0 1 (by decide)) (by decide) -
        s.edgeHom 0 2 (by decide) := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.rhs
  rw [Finset.sum_coe_sort_eq_attach, Finset.sum_attach_univ]
  have he : (Finset.univ : Finset (Fin 3)).erase 1 = {0, 2} := by decide
  have hl : (Finset.univ : Finset (Fin 3)).filter (· ≤ 1) = {0, 1} := by decide
  have hr : (Finset.univ : Finset (Fin 3)).filter (1 ≤ ·) = {1, 2} := by decide
  have hs : ((Finset.univ : Finset (Fin 3)).filter (1 < ·)).card = 1 := by decide
  norm_num [Fin.sum_univ_succ]
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.term, edgeHom, he, hl, hr, hs]
  norm_num
  congr 2

/-- 概要：三角形の三辺と高次成分から二単体のデータを定める。
方針：濃度三では全体集合の高次成分、濃度二では端点に応じた辺を選ぶ。
規約：HA Example 1.3.1.8。使われ方：`Simplex.ofTriangle` のデータ部分。 -/
def ofTriangle (t : TriangleData A D) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D 2 where
  obj := t.obj
  hom I a b k hI ha hb hk := by
    by_cases hc : I.card = 3
    · have h := three_eq_univ I hc
      subst I
      have ha' : a = 0 :=
        ha.trans ((Finset.min'_eq_iff _ _ 0).2 ⟨by simp, fun x _ => Fin.zero_le x⟩)
      have hb' : b = 2 :=
        hb.trans ((Finset.max'_eq_iff _ _ 2).2 ⟨by simp, fun x _ => Fin.le_last x⟩)
      have hk' : k = -1 := by simpa using hk
      subst ha' hb' hk'
      exact t.homotopy
    · have hle := Finset.card_le_univ I
      simp only [Fintype.card_fin] at hle
      have hc2 : I.card = 2 := by omega
      have hab : a < b := by
        have h := I.min'_lt_max'_of_card (by omega)
        simpa only [← ha, ← hb] using h
      have hk' : k = 0 := by omega
      subst hk'
      rcases a with ⟨aa, haa⟩
      rcases b with ⟨bb, hbb⟩
      have habv : aa < bb := hab
      cases aa with
      | zero =>
        cases bb with
        | zero => exact False.elim (by omega)
        | succ bb =>
          cases bb with
          | zero => exact t.f01.val
          | succ bb =>
            cases bb with
            | zero => exact t.f02.val
            | succ bb => exact False.elim (by omega)
      | succ aa =>
        cases aa with
        | zero =>
          cases bb with
          | zero => exact False.elim (by omega)
          | succ bb =>
            cases bb with
            | zero => exact False.elim (by omega)
            | succ bb =>
              cases bb with
              | zero => exact t.f12.val
              | succ bb => exact False.elim (by omega)
        | succ aa => exact False.elim (by omega)

end SimplexData

namespace Simplex

/-- 概要：三角形のデータは実際の二単体を定める。
方針：二点集合の式には辺の閉性を、全体集合の式には三角形の微分条件を使う。
規約：HA Example 1.3.1.8。使われ方：二単体の特徴づけの逆写像。 -/
def ofTriangle (t : TriangleData A D) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D 2 where
  toSimplexData := SimplexData.ofTriangle t
  equation I a b k hI ha hb hk := by
    by_cases hc : I.card = 3
    · have h := three_eq_univ I hc
      subst I
      have ha' : a = 0 :=
        ha.trans ((Finset.min'_eq_iff _ _ 0).2 ⟨by simp, fun x _ => Fin.zero_le x⟩)
      have hb' : b = 2 :=
        hb.trans ((Finset.max'_eq_iff _ _ 2).2 ⟨by simp, fun x _ => Fin.le_last x⟩)
      have hk' : k = -1 := by simpa using hk
      subst ha' hb' hk'
      rw [SimplexData.rhs_triangle]
      exact t.differential_homotopy
    · have hle := Finset.card_le_univ I
      simp only [Fintype.card_fin] at hle
      have hc2 : I.card = 2 := by omega
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.rhs_of_card_two _ _ _ _ _ _ _ _ _ hc2]
      have hab : a < b := by
        have h := I.min'_lt_max'_of_card (by omega)
        simpa only [← ha, ← hb] using h
      have hk' : k = 0 := by omega
      subst hk'
      fin_cases a <;> fin_cases b <;> norm_num at hab
      all_goals simp only [SimplexData.ofTriangle, dite_eq_right hc]
      · exact t.f01.property
      · exact t.f02.property
      · exact t.f12.property

/-- 概要：二単体から三辺と高次成分の三角形データを取り出す。
方針：辺の閉性と既存の二単体の微分公式を使う。
規約：HA Example 1.3.1.8。使われ方：二単体の特徴づけの順写像。 -/
def toTriangle (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D 2) : TriangleData A D where
  obj := s.obj
  f01 := s.edgeCycle 0 1 (by decide)
  f12 := s.edgeCycle 1 2 (by decide)
  f02 := s.edgeCycle 0 2 (by decide)
  homotopy := s.triangleHom
  differential_homotopy := s.differential_triangleHom

/-- 概要：三角形のデータから二単体を作って成分を取り出すと元に戻る。
方針：三辺と全体集合の成分の定義の評価、閉性と方程式の証明の一意性。
規約：HA Example 1.3.1.8。使われ方：二単体の同値の右逆。 -/
lemma toTriangle_ofTriangle (t : TriangleData A D) : (ofTriangle t).toTriangle = t := by
  cases t
  rfl

/-- 概要：二単体をその三角形のデータから再構成すると元に戻る。
方針：濃度三の集合は全体集合、濃度二の集合は両端の対なので全成分が一致する。
規約：HA Example 1.3.1.8。使われ方：二単体の同値の左逆。 -/
lemma ofTriangle_toTriangle (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D 2) : ofTriangle s.toTriangle = s := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  refine _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.ext (s := (ofTriangle s.toTriangle).toSimplexData)
    (t := s.toSimplexData) rfl ?_
  apply heq_of_eq
  funext I a b k hI ha hb hk
  by_cases hc : I.card = 3
  · have h := three_eq_univ I hc
    subst I
    have ha' : a = 0 :=
      ha.trans ((Finset.min'_eq_iff _ _ 0).2 ⟨by simp, fun x _ => Fin.zero_le x⟩)
    have hb' : b = 2 :=
      hb.trans ((Finset.max'_eq_iff _ _ 2).2 ⟨by simp, fun x _ => Fin.le_last x⟩)
    have hk' : k = -1 := by simpa using hk
    subst ha' hb' hk'
    rfl
  · have hle := Finset.card_le_univ I
    simp only [Fintype.card_fin] at hle
    have hc2 : I.card = 2 := by omega
    have hab : a < b := by
      have h := I.min'_lt_max'_of_card (by omega)
      simpa only [← ha, ← hb] using h
    have hpair : I = {a, b} := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.eq_pair hc2
      (by rw [ha]; exact I.isLeast_min' _) (by rw [hb]; exact I.isGreatest_max' _)
    have hk' : k = 0 := by omega
    subst hk'
    fin_cases a <;> fin_cases b <;> norm_num at hab
    all_goals subst I; rfl

/-- 概要：二単体は三頂点、三つの閉零射、合成の差を埋める次数 −1 の射と同値。
方針：成分の評価と二点・三点集合による逆構成が互いに逆であることを使う。
規約：HA Example 1.3.1.8、微分は `δh = f₁₂ ∘ f₀₁ - f₀₂`。
使われ方：ホモトピー圏の合成と辺のホモトピーの明示的な特徴づけ。 -/
def triangleEquiv : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D 2 ≃ TriangleData A D where
  toFun := toTriangle
  invFun := ofTriangle
  left_inv := ofTriangle_toTriangle
  right_inv := toTriangle_ofTriangle

end Simplex

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open DifferentialGraded
open scoped _root_.Simplicial

/-- 概要：dg nerve の二単体は三辺と合成の差の原始元を持つ三角形と同値。
方針：単体の型の三角形の同値を、単体的集合の二次の型に読み替える。
規約：HA Example 1.3.1.8。使われ方：H⁰ 比較の三角形の特徴づけ。 -/
def triangleEquiv (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) _⦋2⦌ ≃ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.TriangleData A D := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.triangleEquiv

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve export _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories (triangleEquiv)


end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "1.3.1.8"] _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.triangleEquiv
