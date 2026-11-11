module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanFibrationEndpointExtension
public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanActualHomotopy

/-!
# 強変形レトラクトをKan fibrationに沿って引き戻した実際のレトラクションを構成する

## 概要
強変形レトラクトをKan fibrationに沿って引き戻した実際のレトラクションを構成する。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
構成に現れる射と比較写像を明示し、各成分の等式を照合する。
既存の普遍性と自然性、必要な帰納を用いて全体の主張へ接続する。

## 規約と注意
Kan条件・右持ち上げ性・単射性は各宣言で指定された範囲で用いる。
ここでのKan条件は外側も含む全hornの充填であり、内側hornだけの条件ではない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。
[棚卸し m0428][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0428
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Pull back a strong deformation retract along an arbitrary Kan fibration

The given square is an actual pullback. The lifted interval fixes the
whole pullback subobject. Neither base nor total space need be Kan.
-/

@[expose] public section
universe v uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory

namespace SerrePositivity.SimplicialModel.KanPullbackDeformation
variable {A B E P : SSet.{v}} (i : A ⟶ B) (r : B ⟶ A) (hi : i ≫ r = 𝟙 A)
  (H : SSet.Homotopy (𝟙 B) (r ≫ i))
  (hfix : i ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫ H.h =
    fst A (SSet.stdSimplex.obj (SimplexCategory.mk 1)) ≫ i)
  (q : E ⟶ B) (hq : SSet.modelCategoryQuillen.J.rlp q)
  (j : P ⟶ E) (k : P ⟶ A) (sq : IsPullback j k q i)

include hi H hfix hq sq in
/-- 強変形レトラクトをKan fibrationに沿って引き戻した実際のレトラクションを構成する。

Kan条件・右持ち上げ性・単射性は各宣言で指定された範囲で用いる。
構成に現れる射と比較写像を明示し、各成分の等式を照合する。
既存の普遍性と自然性、必要な帰納を用いて全体の主張へ接続する。
-/
lemma exists_retraction : ∃ s : E ⟶ P, j ≫ s = 𝟙 P ∧
    ∃ V : SSet.Homotopy (𝟙 E) (s ≫ j),
      j ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫ V.h =
        fst P (SSet.stdSimplex.obj (SimplexCategory.mk 1)) ≫ j ∧
      V.h ≫ q = q ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫ H.h := by
  have : Mono i := mono_of_mono_fac hi
  have : Mono j := sq.mono_fst_of_mono
  let HA := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.changeEndpoints (KanActualHomotopy.refl j)
    (Category.comp_id j).symm rfl
  let base := q ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫ H.h
  have hb : (𝟙 E) ≫ q = SSet.ι₀ ≫ base := by
    dsimp only [base]
    rw [← Category.assoc, SSet.ι₀_comp, Category.assoc, H.h₀, Category.comp_id,
      Category.id_comp]
  have hA : HA.h ≫ q = j ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫ base := by
    dsimp only [HA, base]
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.changeEndpoints_h]
    change (fst P (SSet.stdSimplex.obj (SimplexCategory.mk 1)) ≫ j) ≫ q = _
    rw [← Category.assoc (j ▷ _) (q ▷ _) H.h, ← comp_whiskerRight, sq.w,
      comp_whiskerRight, Category.assoc (k ▷ _) (i ▷ _) H.h, hfix,
      whiskerRight_fst_assoc]
    rw [Category.assoc, sq.w]
  obtain ⟨t, hjt, V, hV, hVp⟩ :=
    KanFibrationEndpointExtension.exists_from_zero q hq j (𝟙 E) j HA base hb hA
  have htq : t ≫ q = (q ≫ r) ≫ i := by
    calc
      t ≫ q = (SSet.ι₁ ≫ V.h) ≫ q := by rw [V.h₁]
      _ = SSet.ι₁ ≫ base := by rw [Category.assoc, hVp]
      _ = (q ≫ r) ≫ i := by
        dsimp only [base]
        rw [← Category.assoc, SSet.ι₁_comp, Category.assoc, H.h₁, ← Category.assoc]
  let s := sq.lift t (q ≫ r) htq
  have hs : j ≫ s = 𝟙 P := by
    apply sq.hom_ext
    · rw [Category.assoc, sq.lift_fst, hjt, Category.id_comp]
    · rw [Category.assoc, sq.lift_snd, ← Category.assoc, sq.w,
        Category.assoc, hi, Category.comp_id, Category.id_comp]
  have he : t = s ≫ j := (sq.lift_fst _ _ _).symm
  refine ⟨s, hs, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.changeEndpoints V rfl he, ?_, ?_⟩
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.changeEndpoints_h, hV]
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.changeEndpoints_h]
    rfl
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.changeEndpoints_h]
    exact hVp

include hi H hfix hq sq in
lemma image_isIso {D : Type uD} [Category.{vD} D] (L : SSet.{v} ⥤ D)
    (hL : SSet.anodyneExtensions.IsInvertedBy L) : IsIso (L.map j) := by
  obtain ⟨s, hs, V, _⟩ := exists_retraction i r hi H hfix q hq j k sq
  have : IsIso (L.map s) := (AnodyneHomotopy.mapRetractionIso L hL s j hs V).isIso_hom
  have hc : IsIso (L.map j ≫ L.map s) := by
    rw [← L.map_comp, hs, L.map_id]
    infer_instance
  exact (isIso_comp_right_iff _ _).mp hc

include hi H hfix hq sq in
/-- Kan fibrationに沿って引き戻した強変形レトラクトは局所化で可逆となる。

Kan条件・右持ち上げ性・単射性は各宣言で指定された範囲で用いる。
構成に現れる射と比較写像を明示し、各成分の等式を照合する。
既存の普遍性と自然性、必要な帰納を用いて全体の主張へ接続する。
-/
lemma localized_isIso : IsIso (AnodyneHomotopy.anodyneQ.map j) :=
  image_isIso i r hi H hfix q hq j k sq AnodyneHomotopy.anodyneQ
    (Localization.inverts AnodyneHomotopy.anodyneQ SSet.anodyneExtensions)

end SerrePositivity.SimplicialModel.KanPullbackDeformation
