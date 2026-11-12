module

public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.NormalizedHornFilling
public import SerrePositivity.HomotopicalAlgebra.Simplicial.MonoRightLiftingRelativeHomotopy

/-!
# 中断した任意モデル源への一般化：NormalizedHornTargetComparison

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Target comparison of normalized horn filling operations。

## 方針（定義・証明）
全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0501][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0501
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Target comparison of normalized horn filling operations

One comparison is chosen on the entire horn input space. It projects to
the constant original horn and is constant on every degenerate input.
Restriction of this same comparison is strictly natural in parameters.
No simplicial model structure, or naturality of the chosen sections in
the target, is assumed.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed CategoryTheory.CartesianMonoidalCategory

namespace SerrePositivity.SimplicialModel.NormalizedHornTargetComparison
variable {K L : SSet.{v}} {n : ℕ} (i : Fin (n + 2))
  (hK : SSet.modelCategoryQuillen.J.rlp (terminal.from K))
  (hL : SSet.modelCategoryQuillen.J.rlp (terminal.from L)) (q : K ⟶ L)

abbrev sourceThenMap := NormalizedHornFilling.section_ K i hK ≫
  (ihom (SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)))).map q

abbrev mapThenTarget := (ihom (SSet.horn (n + 1) i).toSSet).map q ≫
  NormalizedHornFilling.section_ L i hL

abbrev inputs : ((ihom (SSet.horn (n + 1) i).toSSet).obj K).Subcomplex :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompatibleInputUnion.inputs
    (fun _ : Fin (n + 1) => (ihom (SSet.stdSimplex.obj (SimplexCategory.mk n))).obj K)
    (fun d => DegenerateHornInput.boundary i d K)

lemma same_horn : sourceThenMap i hK q ≫ KanHornFamilyLifting.restriction L i =
    mapThenTarget i hL q ≫ KanHornFamilyLifting.restriction L i := by
  dsimp only [sourceThenMap, mapThenTarget, KanHornFamilyLifting.restriction]
  rw [Category.assoc, (pre (SSet.horn (n + 1) i).ι).naturality q,
    ← Category.assoc, NormalizedHornFilling.section_restriction,
    Category.id_comp, Category.assoc, NormalizedHornFilling.section_restriction,
    Category.comp_id]

lemma same_degeneracy (d : Fin (n + 1)) :
    DegenerateHornInput.boundary i d K ≫ sourceThenMap i hK q =
      DegenerateHornInput.boundary i d K ≫ mapThenTarget i hL q := by
  dsimp only [sourceThenMap, mapThenTarget]
  rw [← Category.assoc, NormalizedHornFilling.section_degeneracy]
  have hb : DegenerateHornInput.boundary i d K ≫
      (ihom (SSet.horn (n + 1) i).toSSet).map q =
      (ihom (SSet.stdSimplex.obj (SimplexCategory.mk n))).map q ≫
        DegenerateHornInput.boundary i d L := by
    dsimp only [DegenerateHornInput.boundary, DegenerateHornInput.degeneracy,
      KanHornFamilyLifting.restriction]
    rw [Category.assoc, ← (pre (SSet.horn (n + 1) i).ι).naturality q,
      ← Category.assoc, ← (pre (SSet.stdSimplex.σ d)).naturality q, Category.assoc]
  rw [← Category.assoc, hb, Category.assoc, NormalizedHornFilling.section_degeneracy]
  exact (pre (SSet.stdSimplex.σ d)).naturality q |>.symm

lemma same_inputs : (inputs (K := K) i).ι ≫ sourceThenMap i hK q =
    (inputs (K := K) i).ι ≫ mapThenTarget i hL q := by
  apply _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompatibleInputUnion.hom_ext
  intro d
  rw [← Category.assoc, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompatibleInputUnion.toInputs_inclusion]
  exact same_degeneracy i hK hL q d

include hK hL in
lemma exists_comparison :
    ∃ H : SSet.Homotopy (sourceThenMap i hK q) (mapThenTarget i hL q),
      H.h ≫ KanHornFamilyLifting.restriction L i =
        fst _ (SSet.stdSimplex.obj (SimplexCategory.mk 1)) ≫
          sourceThenMap i hK q ≫ KanHornFamilyLifting.restriction L i ∧
      (inputs (K := K) i).ι ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫ H.h =
        fst _ (SSet.stdSimplex.obj (SimplexCategory.mk 1)) ≫
          (inputs (K := K) i).ι ≫ sourceThenMap i hK q :=
  MonoRightLiftingRelativeHomotopy.exists_relative_vertical_homotopy
    (KanHornFamilyLifting.restriction L i) (KanHornFamilyLifting.all_mono_rlp L i hL)
    (inputs (K := K) i).ι _ _ (same_horn i hK hL q) (same_inputs i hK hL q)

def comparison : SSet.Homotopy (sourceThenMap i hK q) (mapThenTarget i hL q) :=
  (exists_comparison i hK hL q).choose

lemma comparison_horn : (comparison i hK hL q).h ≫ KanHornFamilyLifting.restriction L i =
    fst _ (SSet.stdSimplex.obj (SimplexCategory.mk 1)) ≫
      sourceThenMap i hK q ≫ KanHornFamilyLifting.restriction L i :=
  (exists_comparison i hK hL q).choose_spec.1

lemma comparison_inputs : (inputs (K := K) i).ι ▷
    SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫ (comparison i hK hL q).h =
    fst _ (SSet.stdSimplex.obj (SimplexCategory.mk 1)) ≫
      (inputs (K := K) i).ι ≫ sourceThenMap i hK q :=
  (exists_comparison i hK hL q).choose_spec.2

lemma comparison_degeneracy (d : Fin (n + 1)) :
    DegenerateHornInput.boundary i d K ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫
        (comparison i hK hL q).h =
      fst _ (SSet.stdSimplex.obj (SimplexCategory.mk 1)) ≫
        DegenerateHornInput.degeneracy d K ≫
          (ihom (SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)))).map q := by
  let t := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompatibleInputUnion.toInputs
    (fun _ : Fin (n + 1) => (ihom (SSet.stdSimplex.obj (SimplexCategory.mk n))).obj K)
    (fun d => DegenerateHornInput.boundary i d K) d
  have ht : t ≫ (inputs (K := K) i).ι = DegenerateHornInput.boundary i d K := rfl
  rw [← ht, comp_whiskerRight, Category.assoc, comparison_inputs,
    whiskerRight_fst_assoc, ← Category.assoc t, ht]
  dsimp only [sourceThenMap]
  rw [← Category.assoc (DegenerateHornInput.boundary i d K),
    NormalizedHornFilling.section_degeneracy]

variable {T : SSet.{v}} (b : T ⟶ (ihom (SSet.horn (n + 1) i).toSSet).obj K)

def family : SSet.Homotopy (b ≫ sourceThenMap i hK q) (b ≫ mapThenTarget i hL q) :=
  HomotopyClasses.preHomotopy b (comparison i hK hL q)

lemma family_horn : (family i hK hL q b).h ≫ KanHornFamilyLifting.restriction L i =
    fst T (SSet.stdSimplex.obj (SimplexCategory.mk 1)) ≫ b ≫
      (ihom (SSet.horn (n + 1) i).toSSet).map q := by
  change (b ▷ _ ≫ (comparison i hK hL q).h) ≫ _ = _
  rw [Category.assoc, comparison_horn, whiskerRight_fst_assoc]
  have hs : sourceThenMap i hK q ≫ KanHornFamilyLifting.restriction L i =
      (ihom (SSet.horn (n + 1) i).toSSet).map q := by
    rw [same_horn i hK hL q]
    dsimp only [mapThenTarget]
    rw [Category.assoc, NormalizedHornFilling.section_restriction, Category.comp_id]
  rw [hs]

lemma family_reindex {U : SSet.{v}} (j : U ⟶ T) :
    (family i hK hL q (j ≫ b)).h =
      j ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫ (family i hK hL q b).h := by
  change (j ≫ b) ▷ _ ≫ _ = j ▷ _ ≫ (b ▷ _ ≫ _)
  rw [comp_whiskerRight, Category.assoc]

abbrev evaluation := uncurry (family i hK hL q b).h

lemma evaluation_reindex {U : SSet.{v}} (j : U ⟶ T) :
    evaluation i hK hL q (j ≫ b) =
      SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)) ◁
        (j ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1)) ≫ evaluation i hK hL q b := by
  dsimp only [evaluation]
  rw [family_reindex, uncurry_natural_left]

lemma family_degenerate (d : Fin (n + 1))
    (e : T ⟶ (ihom (SSet.stdSimplex.obj (SimplexCategory.mk n))).obj K) :
    (family i hK hL q (e ≫ DegenerateHornInput.boundary i d K)).h =
      fst T (SSet.stdSimplex.obj (SimplexCategory.mk 1)) ≫ e ≫
        DegenerateHornInput.degeneracy d K ≫
          (ihom (SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)))).map q := by
  change (e ≫ DegenerateHornInput.boundary i d K) ▷ _ ≫ _ = _
  rw [comp_whiskerRight, Category.assoc, comparison_degeneracy, whiskerRight_fst_assoc]

end SerrePositivity.SimplicialModel.NormalizedHornTargetComparison
