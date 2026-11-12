module

public import Mathlib.AlgebraicTopology.SimplicialNerve

/-!
# 有限順序の閉区間への射影

概要：既知面からの回収の選択独立性と真部分区間での合成の整合性を準備する。
方針：閉区間への射影、ホーンの自然性、豊穣関手の構造則を使う。
規約：追加の充填仮定や局所 Kan 性を用いない。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR）–2.4.5.9（Tag 00LS）。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section

universe v

open CategoryTheory MonoidalCategory
open scoped Simplicial

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

variable {J : Type v} [LinearOrder J]
/-- 概要：線形順序の閉区間への射影の順序写像を定義する。
方針：max と min で単調な切り詰めを作る。
規約：Mathlib の native な Path と共通の頂点対象を使う。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR）–2.4.5.9（Tag 00LS） の合成面の整合性。 -/
def intervalClamp (a b : J) : J →o J where
  toFun t := max a (min b t)
  monotone' _ _ h := max_le_max le_rfl (min_le_min le_rfl h)
/-- 概要：両端の順序が正しければ射影の値は閉区間に入る。
方針：max と min の不等式を用いる。
規約：Mathlib の native な Path と共通の頂点対象を使う。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR）–2.4.5.9（Tag 00LS） の合成面の整合性。 -/
lemma intervalClamp_mem (a b : J) (hab : a ≤ b) (t : J) :
    a ≤ intervalClamp a b t ∧ intervalClamp a b t ≤ b :=
  ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩
/-- 概要：閉区間内の点は射影で固定される。
方針：区間の二つの不等式で max と min を消去する。
規約：Mathlib の native な Path と共通の頂点対象を使う。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR）–2.4.5.9（Tag 00LS） の合成面の整合性。 -/
lemma intervalClamp_fixed (a b t : J) (h : a ≤ t ∧ t ≤ b) : intervalClamp a b t = t := by
  change max a (min b t) = t
  rw [min_eq_right h.2, max_eq_right h.1]
/-- 概要：区間の包含後の射影は包含自体に等しい。
方針：全ての区間内の点で固定点の式を使う。
規約：Mathlib の native な Path と共通の頂点対象を使う。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR）–2.4.5.9（Tag 00LS） の合成面の整合性。 -/
lemma intervalClamp_comp_inclusion (a b : J) :
    (intervalClamp a b).comp (⟨Subtype.val, fun _ _ h ↦ h⟩ : Set.Icc a b →o J) =
      (⟨Subtype.val, fun _ _ h ↦ h⟩ : Set.Icc a b →o J) := by
  apply OrderHom.ext
  funext x
  exact intervalClamp_fixed a b x.val x.property

/-- 概要：有限順序の閉区間への射影を単体圏の射として読む。
方針：射影の順序写像を Hom.mk で包む。
規約：Mathlib の native な Path と共通の頂点対象を使う。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR）–2.4.5.9（Tag 00LS） の合成面の整合性。 -/
def intervalClampSimplex {n : ℕ} (a b : Fin (n + 1)) : ⦋n⦌ ⟶ ⦋n⦌ :=
  SimplexCategory.Hom.mk (intervalClamp a b)
/-- 概要：区間外の頂点は射影の像に入らない。
方針：射影の値の区間への所属と区間外の不等式を使う。
規約：Mathlib の native な Path と共通の頂点対象を使う。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR）–2.4.5.9（Tag 00LS） の合成面の整合性。 -/
lemma intervalClampSimplex_avoids {n : ℕ} (j a b : Fin (n + 1))
    (hab : a ≤ b) (hout : j < a ∨ b < j) (t : Fin (n + 1)) :
    (intervalClampSimplex a b).toOrderHom t ≠ j := by
  have h := intervalClamp_mem a b hab t
  rcases hout with hja | hbj
  · exact ne_of_gt (lt_of_lt_of_le hja h.1)
  · exact ne_of_lt (lt_of_le_of_lt h.2 hbj)
/-- 概要：ULift した単体の射影は区間の包含上で恒等になる。
方針：down で射影の固定点の式を確認する。
規約：Mathlib の native な Path と共通の頂点対象を使う。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR）–2.4.5.9（Tag 00LS） の合成面の整合性。 -/
lemma intervalClampSimplex_ulift_inclusion {n : ℕ} (a b : Fin (n + 1)) :
    (intervalClampSimplex a b).toOrderHom.uliftMap.comp
      (⟨Subtype.val, fun _ _ h ↦ h⟩ : Set.Icc (ULift.up.{v} a) (ULift.up.{v} b) →o _) =
        (⟨Subtype.val, fun _ _ h ↦ h⟩ : Set.Icc (ULift.up.{v} a) (ULift.up.{v} b) →o _) := by
  apply OrderHom.ext
  funext x
  apply ULift.ext
  exact intervalClamp_fixed a b x.val.down x.property

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
