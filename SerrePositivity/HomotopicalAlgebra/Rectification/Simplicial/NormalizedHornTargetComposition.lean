module

public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.NormalizedHornInputMap
public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.RelativeComparisonTriangle

/-!
# 中断した任意モデル源への一般化：NormalizedHornTargetComposition

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：A composition triangle retains all three selected target comparisons。

## 方針（定義・証明）
全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0502][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0502
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# A composition triangle retains all three selected target comparisons

For K → L → M the two whiskered original comparisons and the original
comparison for the composite are faces of one actual triangle. The whole
horn is fixed, and the triangle is constant on all degenerate inputs.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed CategoryTheory.CartesianMonoidalCategory

namespace SerrePositivity.SimplicialModel.NormalizedHornTargetComposition
open NormalizedHornTargetComparison
variable {K L M : SSet.{v}} {n : ℕ} (i : Fin (n + 2))
  (hK : SSet.modelCategoryQuillen.J.rlp (terminal.from K))
  (hL : SSet.modelCategoryQuillen.J.rlp (terminal.from L))
  (hM : SSet.modelCategoryQuillen.J.rlp (terminal.from M)) (q : K ⟶ L) (r : L ⟶ M)

abbrev middle := mapThenTarget i hL q ≫
  (ihom (SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)))).map r

def first : SSet.Homotopy (sourceThenMap i hK (q ≫ r)) (middle i hL q r) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.changeEndpoints
    (HomotopyClasses.postHomotopy
      ((ihom (SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)))).map r)
      (comparison i hK hL q))
    (by dsimp only [sourceThenMap]; rw [CategoryTheory.Functor.map_comp, Category.assoc]) rfl

def second : SSet.Homotopy (middle i hL q r) (mapThenTarget i hM (q ≫ r)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.changeEndpoints
    (HomotopyClasses.preHomotopy ((ihom (SSet.horn (n + 1) i).toSSet).map q)
      (comparison i hL hM r))
    (Category.assoc _ _ _).symm
    (by dsimp only [mapThenTarget]; rw [CategoryTheory.Functor.map_comp, Category.assoc])

lemma first_h : (first i hK hL q r).h = (comparison i hK hL q).h ≫
    (ihom (SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)))).map r :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.changeEndpoints_h _ _ _

lemma second_h : (second i hL hM q r).h =
    ((ihom (SSet.horn (n + 1) i).toSSet).map q) ▷
      SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫ (comparison i hL hM r).h :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.changeEndpoints_h _ _ _

abbrev base := (ihom (SSet.horn (n + 1) i).toSSet).map (q ≫ r)
abbrev prescribed := (inputs (K := K) i).ι ≫ sourceThenMap i hK (q ≫ r)

include hM in
lemma source_base : sourceThenMap i hK (q ≫ r) ≫
    KanHornFamilyLifting.restriction M i = base i q r := by
  rw [same_horn i hK hM (q ≫ r)]
  dsimp only [mapThenTarget, base]
  rw [Category.assoc, NormalizedHornFilling.section_restriction, Category.comp_id]

include hM in
lemma prescribed_base : prescribed i hK q r ≫ KanHornFamilyLifting.restriction M i =
    (inputs (K := K) i).ι ≫ base i q r := by
  dsimp only [prescribed]
  rw [Category.assoc, source_base i hK hM q r]

lemma first_base : (first i hK hL q r).h ≫ KanHornFamilyLifting.restriction M i =
    fst _ (SSet.stdSimplex.obj (SimplexCategory.mk 1)) ≫ base i q r := by
  rw [first_h, Category.assoc]
  dsimp only [KanHornFamilyLifting.restriction]
  rw [(pre (SSet.horn (n + 1) i).ι).naturality r, ← Category.assoc, comparison_horn]
  have hs := source_base i hK hL q (𝟙 L)
  simp only [base, Category.comp_id] at hs
  rw [Category.assoc, hs]
  dsimp only [base]
  rw [CategoryTheory.Functor.map_comp]

lemma second_base : (second i hL hM q r).h ≫ KanHornFamilyLifting.restriction M i =
    fst _ (SSet.stdSimplex.obj (SimplexCategory.mk 1)) ≫ base i q r := by
  rw [second_h, Category.assoc, comparison_horn, whiskerRight_fst_assoc]
  have hs := source_base i hL hM r (𝟙 M)
  simp only [base, Category.comp_id] at hs
  rw [hs]
  dsimp only [base]
  rw [CategoryTheory.Functor.map_comp]

lemma first_relative : (inputs (K := K) i).ι ▷
    SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫ (first i hK hL q r).h =
    fst _ (SSet.stdSimplex.obj (SimplexCategory.mk 1)) ≫ prescribed i hK q r := by
  rw [first_h, ← Category.assoc, comparison_inputs]
  dsimp only [prescribed, sourceThenMap]
  rw [CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]

lemma middle_prescribed : (inputs (K := K) i).ι ≫ middle i hL q r =
    prescribed i hK q r := by
  dsimp only [middle, prescribed]
  rw [← Category.assoc, ← same_inputs i hK hL q]
  dsimp only [sourceThenMap]
  rw [CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]

lemma second_relative : (inputs (K := K) i).ι ▷
    SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫ (second i hL hM q r).h =
    fst _ (SSet.stdSimplex.obj (SimplexCategory.mk 1)) ≫ prescribed i hK q r := by
  rw [second_h, ← Category.assoc, ← comp_whiskerRight,
    ← NormalizedHornInputMap.map_inclusion, comp_whiskerRight,
    Category.assoc, comparison_inputs, whiskerRight_fst_assoc]
  rw [← Category.assoc (NormalizedHornInputMap.map i q),
    NormalizedHornInputMap.map_inclusion]
  change fst _ _ ≫ (inputs (K := K) i).ι ≫
    (ihom (SSet.horn (n + 1) i).toSSet).map q ≫ sourceThenMap i hL r = _
  have hm := middle_prescribed i hK hL q r
  dsimp only [middle, mapThenTarget] at hm
  rw [Category.assoc] at hm
  exact congrArg (fun f => fst _ _ ≫ f) hm

def triangle : (ihom (SSet.horn (n + 1) i).toSSet).obj K ⊗
    SSet.stdSimplex.obj (SimplexCategory.mk 2) ⟶
      (ihom (SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)))).obj M :=
  RelativeComparisonTriangle.triangle (first i hK hL q r) (second i hL hM q r)
    (comparison i hK hM (q ≫ r)) (KanHornFamilyLifting.restriction M i)
    (KanHornFamilyLifting.all_mono_rlp M i hM) (inputs (K := K) i).ι
    (prescribed i hK q r) (base i q r) (prescribed_base i hK hM q r)
    (first_base i hK hL q r) (second_base i hL hM q r)
    (by
      rw [comparison_horn]
      exact congrArg (fun f => fst _ _ ≫ f) (source_base i hK hM q r))
    (first_relative i hK hL q r) (second_relative i hK hL hM q r)
    (comparison_inputs i hK hM (q ≫ r))

lemma triangle_face (k : Fin 3) : _ ◁ SSet.stdSimplex.δ k ≫ triangle i hK hL hM q r =
    ![(second i hL hM q r).h, (comparison i hK hM (q ≫ r)).h,
      (first i hK hL q r).h] k :=
  RelativeComparisonTriangle.triangle_face _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ k

lemma triangle_base : triangle i hK hL hM q r ≫ KanHornFamilyLifting.restriction M i =
    fst _ (SSet.stdSimplex.obj (SimplexCategory.mk 2)) ≫ base i q r :=
  RelativeComparisonTriangle.triangle_base _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

lemma triangle_relative : (inputs (K := K) i).ι ▷
    SSet.stdSimplex.obj (SimplexCategory.mk 2) ≫ triangle i hK hL hM q r =
    fst _ (SSet.stdSimplex.obj (SimplexCategory.mk 2)) ≫ prescribed i hK q r :=
  RelativeComparisonTriangle.triangle_relative _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

variable {T : SSet.{v}} (t : T ⟶ (ihom (SSet.horn (n + 1) i).toSSet).obj K)

abbrev family := t ▷ SSet.stdSimplex.obj (SimplexCategory.mk 2) ≫ triangle i hK hL hM q r

lemma family_reindex {U : SSet.{v}} (j : U ⟶ T) :
    family i hK hL hM q r (j ≫ t) =
      j ▷ SSet.stdSimplex.obj (SimplexCategory.mk 2) ≫ family i hK hL hM q r t := by
  dsimp only [family]
  rw [comp_whiskerRight, Category.assoc]

abbrev evaluation := uncurry (family i hK hL hM q r t)

lemma evaluation_reindex {U : SSet.{v}} (j : U ⟶ T) :
    evaluation i hK hL hM q r (j ≫ t) =
      SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)) ◁
        (j ▷ SSet.stdSimplex.obj (SimplexCategory.mk 2)) ≫ evaluation i hK hL hM q r t := by
  dsimp only [evaluation]
  rw [family_reindex, uncurry_natural_left]

lemma family_face (k : Fin 3) : T ◁ SSet.stdSimplex.δ k ≫ family i hK hL hM q r t =
    t ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫
      ![(second i hL hM q r).h, (comparison i hK hM (q ≫ r)).h,
        (first i hK hL q r).h] k := by
  dsimp only [family]
  rw [whisker_exchange_assoc, triangle_face]

lemma family_degenerate (d : Fin (n + 1))
    (e : T ⟶ (ihom (SSet.stdSimplex.obj (SimplexCategory.mk n))).obj K) :
    family i hK hL hM q r (e ≫ DegenerateHornInput.boundary i d K) =
      fst T (SSet.stdSimplex.obj (SimplexCategory.mk 2)) ≫ e ≫
        DegenerateHornInput.degeneracy d K ≫
          (ihom (SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)))).map (q ≫ r) := by
  let u := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompatibleInputUnion.toInputs
    (fun _ : Fin (n + 1) => (ihom (SSet.stdSimplex.obj (SimplexCategory.mk n))).obj K)
    (fun d => DegenerateHornInput.boundary i d K) d
  have hu : u ≫ (inputs (K := K) i).ι = DegenerateHornInput.boundary i d K := rfl
  dsimp only [family]
  rw [← hu, ← Category.assoc e, comp_whiskerRight, Category.assoc,
    triangle_relative, whiskerRight_fst_assoc]
  dsimp only [prescribed]
  rw [← Category.assoc (e ≫ u), Category.assoc e, hu]
  dsimp only [sourceThenMap]
  rw [Category.assoc, ← Category.assoc (DegenerateHornInput.boundary i d K),
    NormalizedHornFilling.section_degeneracy]

end SerrePositivity.SimplicialModel.NormalizedHornTargetComposition
