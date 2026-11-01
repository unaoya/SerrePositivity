module

public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.RelativeHornFillingOperation

/-!
# 中断した任意モデル源への一般化：DegenerateHornInput

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Degenerate horn inputs embed and admit a normalized filling operation。

## 方針（定義・証明）
全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0377][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0377
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Degenerate horn inputs embed and admit a normalized filling operation

For every horn and degeneracy, at least one of the two section faces is
present. It recovers the whole lower-dimensional input, so the family of
degenerate horn inputs is a split monomorphism. One uniform horn filling
operation can therefore preserve this entire family strictly.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed

namespace SerrePositivity.SimplicialModel.DegenerateHornInput
variable {n : ℕ} (i : Fin (n + 2)) (d : Fin (n + 1))

def visibleFace : Fin (n + 2) := if d.castSucc ≠ i then d.castSucc else d.succ

lemma visibleFace_ne : visibleFace i d ≠ i := by
  by_cases h : d.castSucc ≠ i
  · simpa only [visibleFace, ite_eq_left h] using h
  · simp only [visibleFace, ite_eq_right h]
    have hi : d.castSucc = i := not_not.mp h
    intro he
    have hv := congrArg Fin.val (he.trans hi.symm)
    simp only [Fin.val_succ, Fin.val_castSucc] at hv
    omega

lemma visibleFace_section : SSet.stdSimplex.δ.{v} (visibleFace i d) ≫ SSet.stdSimplex.σ d =
    𝟙 _ := by
  by_cases h : d.castSucc ≠ i
  · simp only [visibleFace, ite_eq_left h]
    exact SSet.stdSimplex.δ_comp_σ_self
  · simp only [visibleFace, ite_eq_right h]
    exact SSet.stdSimplex.δ_comp_σ_succ

variable (K : SSet.{v})

abbrev degeneracy : (ihom (SSet.stdSimplex.obj (SimplexCategory.mk n))).obj K ⟶
    (ihom (SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)))).obj K :=
  (pre (SSet.stdSimplex.σ d)).app K

abbrev boundary : (ihom (SSet.stdSimplex.obj (SimplexCategory.mk n))).obj K ⟶
    (ihom (SSet.horn (n + 1) i).toSSet).obj K :=
  degeneracy d K ≫ KanHornFamilyLifting.restriction K i

abbrev recover : (ihom (SSet.horn (n + 1) i).toSSet).obj K ⟶
    (ihom (SSet.stdSimplex.obj (SimplexCategory.mk n))).obj K :=
  (pre (SSet.horn.ι i (visibleFace i d) (visibleFace_ne i d))).app K

lemma boundary_recover : boundary i d K ≫ recover i d K = 𝟙 _ := by
  let s := SSet.horn.ι i (visibleFace i d) (visibleFace_ne i d)
  have h₁ : (pre (SSet.stdSimplex.σ d)).app K ≫ (pre (SSet.horn (n + 1) i).ι).app K =
      (pre ((SSet.horn (n + 1) i).ι ≫ SSet.stdSimplex.σ d)).app K :=
    RelativeChoiceSpace.restriction_comp _ _
  have h₂ : (pre ((SSet.horn (n + 1) i).ι ≫ SSet.stdSimplex.σ d)).app K ≫ (pre s).app K =
      (pre (s ≫ (SSet.horn (n + 1) i).ι ≫ SSet.stdSimplex.σ d)).app K :=
    RelativeChoiceSpace.restriction_comp _ _
  change ((pre (SSet.stdSimplex.σ d)).app K ≫
    (pre (SSet.horn (n + 1) i).ι).app K) ≫ (pre s).app K = _
  rw [h₁, h₂]
  have hs : s ≫ (SSet.horn (n + 1) i).ι ≫ SSet.stdSimplex.σ d = 𝟙 _ := by
    rw [← Category.assoc, SSet.horn.ι_ι, visibleFace_section]
  rw [hs, pre_id, NatTrans.id_app]

instance boundary_mono : Mono (boundary i d K) := mono_of_mono_fac (boundary_recover i d K)

variable (hK : SSet.modelCategoryQuillen.J.rlp (CategoryTheory.Limits.terminal.from K))

abbrev section_ := RelativeHornFillingOperation.section_ K i hK
  (boundary i d K) (degeneracy d K) rfl

lemma section_restriction : section_ i d K hK ≫ KanHornFamilyLifting.restriction K i = 𝟙 _ :=
  RelativeHornFillingOperation.section_restriction _ _ _ _ _ _

lemma section_degeneracy : boundary i d K ≫ section_ i d K hK = degeneracy d K :=
  RelativeHornFillingOperation.section_prescribed _ _ _ _ _ _

variable {L : SSet.{v}} (a : L ⟶ (ihom (SSet.stdSimplex.obj (SimplexCategory.mk n))).obj K)

lemma family_degeneracy : uncurry (a ≫ boundary i d K ≫ section_ i d K hK) =
    SSet.stdSimplex.σ d ▷ L ≫ uncurry a := by
  rw [section_degeneracy]
  exact uncurry_pre_app K a (SSet.stdSimplex.σ d)

end SerrePositivity.SimplicialModel.DegenerateHornInput
