module

public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.DegenerateTriangleOverlap
public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.CompatibleHornFillingOperation

/-!
# 中断した任意モデル源への一般化：NormalizedTriangleHorn

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：One triangle horn filling operation preserves both degeneracies simultaneously。

## 方針（定義・証明）
全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0505][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0505
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# One triangle horn filling operation preserves both degeneracies simultaneously

Overlap compatibility is proved from the horn itself. It is not an
extra condition on the target, which is only assumed Kan. The same
chosen simplicial section preserves all families of both degeneracies
and is natural under every change of parameter.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed

namespace SerrePositivity.SimplicialModel.NormalizedTriangleHorn
variable (K : SSet.{v}) (i : Fin 3)

private lemma mixed_components (m : SimplexCategoryᵒᵖ)
    (x y : ((ihom DegenerateTriangleOverlap.interval).obj K).obj m)
    (h : (DegenerateHornInput.boundary i 0 K).app m x =
      (DegenerateHornInput.boundary i 1 K).app m y) :
    (DegenerateHornInput.degeneracy 0 K).app m x =
      (DegenerateHornInput.degeneracy 1 K).app m y := by
  have he : SSet.yonedaEquiv.symm x ≫ DegenerateHornInput.boundary i 0 K =
      SSet.yonedaEquiv.symm y ≫ DegenerateHornInput.boundary i 1 K := by
    apply SSet.yonedaEquiv.injective
    simpa only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] using h
  have hd := DegenerateTriangleOverlap.eq_of_same_horn K i
    (SSet.yonedaEquiv.symm x) (SSet.yonedaEquiv.symm y) he
  have hf := congrArg SSet.yonedaEquiv hd
  simpa only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] using hf

lemma compatible : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompatibleInputUnion.Compatible
    (fun _ : Fin 2 => (ihom DegenerateTriangleOverlap.interval).obj K)
    (fun d => DegenerateHornInput.boundary i d K)
    (fun d => DegenerateHornInput.degeneracy d K) := by
  intro d e m x y h
  fin_cases d <;> fin_cases e
  · have hx : x = y :=
      ((CategoryTheory.mono_iff_injective ((DegenerateHornInput.boundary i 0 K).app m)).mp
        inferInstance) h
    exact congrArg ((DegenerateHornInput.degeneracy 0 K).app m) hx
  · exact mixed_components K i m x y h
  · exact (mixed_components K i m y x h.symm).symm
  · have hx : x = y :=
      ((CategoryTheory.mono_iff_injective ((DegenerateHornInput.boundary i 1 K).app m)).mp
        inferInstance) h
    exact congrArg ((DegenerateHornInput.degeneracy 1 K).app m) hx

variable (hK : SSet.modelCategoryQuillen.J.rlp (CategoryTheory.Limits.terminal.from K))

abbrev section_ := CompatibleHornFillingOperation.section_ K i hK
  (fun _ : Fin 2 => (ihom DegenerateTriangleOverlap.interval).obj K)
  (fun d => DegenerateHornInput.boundary i d K)
  (fun d => DegenerateHornInput.degeneracy d K) (compatible K i) (fun _ => rfl)

lemma section_restriction : section_ K i hK ≫ KanHornFamilyLifting.restriction K i = 𝟙 _ :=
  CompatibleHornFillingOperation.section_restriction _ _ _ _ _ _ _ _

lemma section_degeneracy (d : Fin 2) :
    DegenerateHornInput.boundary i d K ≫ section_ K i hK = DegenerateHornInput.degeneracy d K :=
  CompatibleHornFillingOperation.section_prescribed _ _ _ _ _ _ _ _ d

variable {L : SSet.{v}} (b : L ⟶ (ihom (SSet.horn 2 i).toSSet).obj K)

abbrev fill : L ⟶ (ihom (SSet.stdSimplex.obj (SimplexCategory.mk 2))).obj K := b ≫ section_ K i hK

lemma fill_naturality {U : SSet.{v}} (j : U ⟶ L) :
    fill K i hK (j ≫ b) = j ≫ fill K i hK b := Category.assoc _ _ _

lemma fill_restriction : fill K i hK b ≫ KanHornFamilyLifting.restriction K i = b := by
  rw [fill, Category.assoc, section_restriction, Category.comp_id]

lemma family_degeneracy (d : Fin 2)
    (a : L ⟶ (ihom DegenerateTriangleOverlap.interval).obj K) :
    uncurry (fill K i hK (a ≫ DegenerateHornInput.boundary i d K)) =
      SSet.stdSimplex.σ d ▷ L ≫ uncurry a := by
  change uncurry ((a ≫ DegenerateHornInput.boundary i d K) ≫ section_ K i hK) = _
  rw [Category.assoc, section_degeneracy]
  exact uncurry_pre_app K a (SSet.stdSimplex.σ d)

end SerrePositivity.SimplicialModel.NormalizedTriangleHorn
