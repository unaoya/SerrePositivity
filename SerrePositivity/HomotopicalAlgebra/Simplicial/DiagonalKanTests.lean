module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.DiagonalAnodyne
public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanLocalizedMonoLifting
public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanTestLiftingClass

/-!
# Reedy局所化単射の対角がanodyne局所化で可逆となることをKan値テストから導く

## 概要
Reedy局所化単射の対角がanodyne局所化で可逆となることをKan値テストから導く。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
対角の右随伴と境界内部Homの比較を使い、相対matching射を計算する。
必要な持ち上げ条件またはBrownの補題を、この実際の比較へ適用する。

## 規約と注意
Kan条件・右持ち上げ性・単射性は各宣言で指定された範囲で用いる。
ここでのKan条件は外側も含む全hornの充填であり、内側hornだけの条件ではない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はWaldhausenのS-構成の二重単体図式や分解の比較・加法性の準備に利用できる。
[棚卸し m0384][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/k-theory-generalization-inventory.md#m0384
[plan]: ../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The diagonal inverts Reedy localized mono equivalences by actual Kan tests
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Reedy SerrePositivity.SimplicialModel
open scoped SSet.modelCategoryQuillen

namespace SerrePositivity.BisimplicialModel

lemma relativeMatching_target_kan {E B : SSet.{v}} (p : E ⟶ B)
    (hp : SSet.modelCategoryQuillen.J.rlp p)
    (hB : SSet.modelCategoryQuillen.J.rlp (terminal.from B)) (n : ℕ) :
    SSet.modelCategoryQuillen.J.rlp (terminal.from
      (pullback (reedyRestriction B n) (reedyTargetMap p n))) := by
  have : Fibration p := (SSet.modelCategoryQuillen.fibration_iff _).mpr hp
  have : Fibration (terminal.from B) := (SSet.modelCategoryQuillen.fibration_iff _).mpr hB
  have : SSet.KanComplex B := (isFibrant_iff B).mpr inferInstance
  have ht : Fibration (boundaryTargetMap p n) :=
    inferInstanceAs (Fibration ((ihom (SSet.boundary n).toSSet).map p))
  have hpb := (SSet.modelCategoryQuillen.J.rlp).pullback_snd
    (boundaryTargetMap p n) (boundaryRestriction B n)
    ((SSet.modelCategoryQuillen.fibration_iff _).mp ht)
  have : Fibration (pullback.snd (boundaryTargetMap p n) (boundaryRestriction B n)) :=
    (SSet.modelCategoryQuillen.fibration_iff _).mpr hpb
  have hKan : IsFibrant ((ihom (SSet.stdSimplex.obj (SimplexCategory.mk n))).obj B) :=
    inferInstance
  have : IsFibrant (boundaryPullbackHom p n).pt :=
    isFibrant_of_fibration (pullback.snd (boundaryTargetMap p n) (boundaryRestriction B n))
      (hY := hKan)
  have : IsFibrant (relativeTarget p n) := isFibrant_of_fibration (relativeTargetIso p n).hom
  exact (SSet.modelCategoryQuillen.fibration_iff _).mp this

lemma rightTest_kan {E B : SSet.{v}} (p : E ⟶ B) (hp : KanTestLiftingClass.rightTests p) :
    SSet.modelCategoryQuillen.J.rlp p ∧
      SSet.modelCategoryQuillen.J.rlp (terminal.from B) := by
  cases hp with
  | terminal K hK =>
    refine ⟨hK, ?_⟩
    have h : terminal.from (⊤_ SSet.{v}) = 𝟙 _ := terminal.hom_ext _ _
    rw [h]
    exact (SSet.modelCategoryQuillen.J.rlp).of_isIso _
  | paths K hK =>
    have : Fibration (terminal.from K) := (SSet.modelCategoryQuillen.fibration_iff _).mpr hK
    have : SSet.KanComplex K := (isFibrant_iff K).mpr inferInstance
    have h : Fibration (KanTestLiftingClass.pathRestriction K).π := SSet.fibration_pullbackObjObjπ _
    have hKan : IsFibrant ((ihom (SSet.boundary 1).toSSet).obj K) := inferInstance
    exact ⟨(SSet.modelCategoryQuillen.fibration_iff _).mp h,
      (SSet.modelCategoryQuillen.fibration_iff _).mp hKan⟩

lemma diagonal_lifting_of_reedy_localizedMonos {A T : SimplexCategoryᵒᵖ ⥤ SSet.{v}}
    (i : A ⟶ T) (hi : reedyLeft simplexOp KanTestLiftingClass.localizedMonos i)
    {E B : SSet.{v}} (p : E ⟶ B) (hp : SSet.modelCategoryQuillen.J.rlp p)
    (hB : SSet.modelCategoryQuillen.J.rlp (terminal.from B)) :
    HasLiftingProperty (diagonal.map i) p := by
  have : ∀ j : SimplexCategoryᵒᵖ,
      HasLiftingProperty (relativeLatchingMap simplexOp j i)
        (relativeMatchingMap simplexOp j (internalHomRight.map p)) := by
    intro j
    have : Mono (relativeLatchingMap simplexOp j i) := (hi j).1
    induction j using Opposite.rec with | _ j =>
      induction j using SimplexCategory.rec with | _ n =>
        exact KanLocalizedMonoLifting.hasLiftingProperty _ (hi _).2 _
          (relativeMatching_horn_rlp p hp n) (relativeMatching_target_kan p hp hB n)
  have h : HasLiftingProperty i (internalHomRight.map p) := Lifting.hasLiftingProperty simplexOp
  exact (Adjunction.hasLiftingProperty_iff diagonalInternalHomAdjunction i p).mpr h

/-- Reedy局所化単射の対角がanodyne局所化で可逆となることをKan値テストから導く。

Kan条件・右持ち上げ性・単射性は各宣言で指定された範囲で用いる。
対角の右随伴と境界内部Homの比較を使い、相対matching射を計算する。
必要な持ち上げ条件またはBrownの補題を、この実際の比較へ適用する。
-/
lemma localized_diagonal_map_of_reedy_localizedMonos {A T : SimplexCategoryᵒᵖ ⥤ SSet.{v}}
    (i : A ⟶ T) (hi : reedyLeft simplexOp KanTestLiftingClass.localizedMonos i) :
    IsIso (AnodyneHomotopy.anodyneQ.map (diagonal.map i)) := by
  apply KanTestLiftingClass.localized_isIso_of_llp
  intro E B p hp
  obtain ⟨h, hB⟩ := rightTest_kan p hp
  exact diagonal_lifting_of_reedy_localizedMonos i hi p h hB

end SerrePositivity.BisimplicialModel
