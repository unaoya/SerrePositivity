module

public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.NormalizedHornTargetFaces

/-!
# 中断した任意モデル源への一般化：NormalizedHornTargetAssociativity

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Three target maps give a whole compatible tetrahedral boundary。

## 方針（定義・証明）
全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0500][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0500
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Three target maps give a whole compatible tetrahedral boundary

All four faces are the previously selected composition triangles, with
the actual required precomposition and postcomposition. Their six shared
edges agree as whole parameter families.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed CategoryTheory.CartesianMonoidalCategory

namespace SerrePositivity.SimplicialModel.NormalizedHornTargetAssociativity
open NormalizedHornTargetComparison
variable {K L M N : SSet.{v}} {n : ℕ} (i : Fin (n + 2))
  (hK : SSet.modelCategoryQuillen.J.rlp (terminal.from K))
  (hL : SSet.modelCategoryQuillen.J.rlp (terminal.from L))
  (hM : SSet.modelCategoryQuillen.J.rlp (terminal.from M))
  (hN : SSet.modelCategoryQuillen.J.rlp (terminal.from N))
  (q : K ⟶ L) (r : L ⟶ M) (s : M ⟶ N)

def faces : Fin 4 → ((ihom (SSet.horn (n + 1) i).toSSet).obj K ⊗
    SSet.stdSimplex.obj (SimplexCategory.mk 2) ⟶
      (ihom (SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)))).obj N) :=
  ![((ihom (SSet.horn (n + 1) i).toSSet).map q) ▷
      SSet.stdSimplex.obj (SimplexCategory.mk 2) ≫
        NormalizedHornTargetComposition.triangle i hL hM hN r s,
    NormalizedHornTargetComposition.triangle i hK hM hN (q ≫ r) s,
    NormalizedHornTargetComposition.triangle i hK hL hN q (r ≫ s),
    NormalizedHornTargetComposition.triangle i hK hL hM q r ≫
      (ihom (SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)))).map s]

lemma compatible : BoundaryTensorGluing.Compatible (faces i hK hL hM hN q r s) := by
  intro j k hjk
  fin_cases j <;> fin_cases k <;> simp at hjk
  · change _ ◁ SSet.stdSimplex.δ (0 : Fin 3) ≫
        (((ihom (SSet.horn (n + 1) i).toSSet).map q) ▷ _ ≫
          NormalizedHornTargetComposition.triangle i hL hM hN r s) =
      _ ◁ SSet.stdSimplex.δ (0 : Fin 3) ≫
        NormalizedHornTargetComposition.triangle i hK hM hN (q ≫ r) s
    rw [whisker_exchange_assoc, NormalizedHornTargetFaces.zero,
      NormalizedHornTargetFaces.zero, ← comp_whiskerRight_assoc,
      ← CategoryTheory.Functor.map_comp]
  · change _ ◁ SSet.stdSimplex.δ (1 : Fin 3) ≫
        (((ihom (SSet.horn (n + 1) i).toSSet).map q) ▷ _ ≫
          NormalizedHornTargetComposition.triangle i hL hM hN r s) =
      _ ◁ SSet.stdSimplex.δ (0 : Fin 3) ≫
        NormalizedHornTargetComposition.triangle i hK hL hN q (r ≫ s)
    rw [whisker_exchange_assoc, NormalizedHornTargetFaces.one, NormalizedHornTargetFaces.zero]
  · change _ ◁ SSet.stdSimplex.δ (2 : Fin 3) ≫
        (((ihom (SSet.horn (n + 1) i).toSSet).map q) ▷ _ ≫
          NormalizedHornTargetComposition.triangle i hL hM hN r s) =
      _ ◁ SSet.stdSimplex.δ (0 : Fin 3) ≫
        (NormalizedHornTargetComposition.triangle i hK hL hM q r ≫
          (ihom (SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)))).map s)
    rw [whisker_exchange_assoc, NormalizedHornTargetFaces.two]
    have hz := congrArg
      (fun f => f ≫ (ihom (SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)))).map s)
      (NormalizedHornTargetFaces.zero i hK hL hM q r)
    simpa only [Category.assoc] using hz.symm
  · change _ ◁ SSet.stdSimplex.δ (1 : Fin 3) ≫
        NormalizedHornTargetComposition.triangle i hK hM hN (q ≫ r) s =
      _ ◁ SSet.stdSimplex.δ (1 : Fin 3) ≫
        NormalizedHornTargetComposition.triangle i hK hL hN q (r ≫ s)
    rw [NormalizedHornTargetFaces.one, NormalizedHornTargetFaces.one, Category.assoc]
  · change _ ◁ SSet.stdSimplex.δ (2 : Fin 3) ≫
        NormalizedHornTargetComposition.triangle i hK hM hN (q ≫ r) s =
      _ ◁ SSet.stdSimplex.δ (1 : Fin 3) ≫
        (NormalizedHornTargetComposition.triangle i hK hL hM q r ≫
          (ihom (SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)))).map s)
    rw [NormalizedHornTargetFaces.two, ← Category.assoc, NormalizedHornTargetFaces.one]
  · change _ ◁ SSet.stdSimplex.δ (2 : Fin 3) ≫
        NormalizedHornTargetComposition.triangle i hK hL hN q (r ≫ s) =
      _ ◁ SSet.stdSimplex.δ (2 : Fin 3) ≫
        (NormalizedHornTargetComposition.triangle i hK hL hM q r ≫
          (ihom (SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)))).map s)
    rw [NormalizedHornTargetFaces.two, ← Category.assoc, NormalizedHornTargetFaces.two,
      CategoryTheory.Functor.map_comp, Category.assoc]

abbrev base := (ihom (SSet.horn (n + 1) i).toSSet).map (q ≫ r ≫ s)
abbrev prescribed := (NormalizedHornTargetComparison.inputs (K := K) i).ι ≫
  NormalizedHornTargetComparison.sourceThenMap i hK (q ≫ r ≫ s)

lemma faces_base (k : Fin 4) : faces i hK hL hM hN q r s k ≫
    KanHornFamilyLifting.restriction N i =
    fst _ (SSet.stdSimplex.obj (SimplexCategory.mk 2)) ≫ base i q r s := by
  fin_cases k
  · change (((ihom (SSet.horn (n + 1) i).toSSet).map q) ▷ _ ≫
        NormalizedHornTargetComposition.triangle i hL hM hN r s) ≫ _ = _
    rw [Category.assoc, NormalizedHornTargetComposition.triangle_base,
      whiskerRight_fst_assoc]
    dsimp only [NormalizedHornTargetComposition.base, base]
    simp only [CategoryTheory.Functor.map_comp]
  · change NormalizedHornTargetComposition.triangle i hK hM hN (q ≫ r) s ≫ _ = _
    rw [NormalizedHornTargetComposition.triangle_base]
    simp only [NormalizedHornTargetComposition.base, base, Category.assoc]
  · exact NormalizedHornTargetComposition.triangle_base i hK hL hN q (r ≫ s)
  · change (NormalizedHornTargetComposition.triangle i hK hL hM q r ≫
        (ihom (SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)))).map s) ≫ _ = _
    dsimp only [KanHornFamilyLifting.restriction]
    rw [Category.assoc, (pre (SSet.horn (n + 1) i).ι).naturality s,
      ← Category.assoc, NormalizedHornTargetComposition.triangle_base]
    simp only [NormalizedHornTargetComposition.base, base,
      CategoryTheory.Functor.map_comp, Category.assoc]

lemma faces_relative (k : Fin 4) : (NormalizedHornTargetComparison.inputs (K := K) i).ι ▷
    SSet.stdSimplex.obj (SimplexCategory.mk 2) ≫ faces i hK hL hM hN q r s k =
    fst _ (SSet.stdSimplex.obj (SimplexCategory.mk 2)) ≫ prescribed i hK q r s := by
  fin_cases k
  · change _ ≫ (((ihom (SSet.horn (n + 1) i).toSSet).map q) ▷ _ ≫
        NormalizedHornTargetComposition.triangle i hL hM hN r s) = _
    rw [← Category.assoc, ← comp_whiskerRight, ← NormalizedHornInputMap.map_inclusion,
      comp_whiskerRight, Category.assoc, NormalizedHornTargetComposition.triangle_relative,
      whiskerRight_fst_assoc]
    dsimp only [NormalizedHornTargetComposition.prescribed]
    rw [← Category.assoc (NormalizedHornInputMap.map i q),
      NormalizedHornInputMap.map_inclusion]
    have hm := NormalizedHornTargetComposition.middle_prescribed i hK hL q (r ≫ s)
    simpa only [NormalizedHornTargetComposition.middle,
      NormalizedHornTargetComposition.prescribed, prescribed,
      NormalizedHornTargetComparison.sourceThenMap, NormalizedHornTargetComparison.mapThenTarget,
      Category.assoc] using congrArg (fun f => fst _ _ ≫ f) hm
  · change _ ≫ NormalizedHornTargetComposition.triangle i hK hM hN (q ≫ r) s = _
    rw [NormalizedHornTargetComposition.triangle_relative]
    simp only [NormalizedHornTargetComposition.prescribed, prescribed, Category.assoc]
  · exact NormalizedHornTargetComposition.triangle_relative i hK hL hN q (r ≫ s)
  · change _ ≫ (NormalizedHornTargetComposition.triangle i hK hL hM q r ≫
        (ihom (SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)))).map s) = _
    rw [← Category.assoc, NormalizedHornTargetComposition.triangle_relative]
    simp only [NormalizedHornTargetComposition.prescribed, prescribed,
      NormalizedHornTargetComparison.sourceThenMap, CategoryTheory.Functor.map_comp,
      Category.assoc]

def tetrahedron : (ihom (SSet.horn (n + 1) i).toSSet).obj K ⊗
    SSet.stdSimplex.obj (SimplexCategory.mk 3) ⟶
      (ihom (SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)))).obj N :=
  RelativeBoundaryFilling.filler (KanHornFamilyLifting.restriction N i)
    (KanHornFamilyLifting.all_mono_rlp N i hN)
    (NormalizedHornTargetComparison.inputs (K := K) i).ι
    (prescribed i hK q r s) (base i q r s)
    (NormalizedHornTargetComposition.prescribed_base i hK hN q (r ≫ s))
    (faces i hK hL hM hN q r s) (compatible i hK hL hM hN q r s)
    (faces_base i hK hL hM hN q r s) (faces_relative i hK hL hM hN q r s)

lemma tetrahedron_face (k : Fin 4) : _ ◁ SSet.stdSimplex.δ k ≫
    tetrahedron i hK hL hM hN q r s = faces i hK hL hM hN q r s k :=
  RelativeBoundaryFilling.filler_face _ _ _ _ _ _ _ _ _ _ k

lemma tetrahedron_base : tetrahedron i hK hL hM hN q r s ≫
    KanHornFamilyLifting.restriction N i =
    fst _ (SSet.stdSimplex.obj (SimplexCategory.mk 3)) ≫ base i q r s :=
  RelativeBoundaryFilling.filler_base _ _ _ _ _ _ _ _ _ _

lemma tetrahedron_relative : (NormalizedHornTargetComparison.inputs (K := K) i).ι ▷
    SSet.stdSimplex.obj (SimplexCategory.mk 3) ≫ tetrahedron i hK hL hM hN q r s =
    fst _ (SSet.stdSimplex.obj (SimplexCategory.mk 3)) ≫ prescribed i hK q r s :=
  RelativeBoundaryFilling.filler_relative _ _ _ _ _ _ _ _ _ _

variable {T : SSet.{v}} (t : T ⟶ (ihom (SSet.horn (n + 1) i).toSSet).obj K)

abbrev family := t ▷ SSet.stdSimplex.obj (SimplexCategory.mk 3) ≫ tetrahedron i hK hL hM hN q r s

lemma family_reindex {U : SSet.{v}} (j : U ⟶ T) :
    family i hK hL hM hN q r s (j ≫ t) =
      j ▷ SSet.stdSimplex.obj (SimplexCategory.mk 3) ≫ family i hK hL hM hN q r s t := by
  dsimp only [family]
  rw [comp_whiskerRight, Category.assoc]

abbrev evaluation := uncurry (family i hK hL hM hN q r s t)

lemma evaluation_reindex {U : SSet.{v}} (j : U ⟶ T) :
    evaluation i hK hL hM hN q r s (j ≫ t) =
      SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)) ◁
        (j ▷ SSet.stdSimplex.obj (SimplexCategory.mk 3)) ≫ evaluation i hK hL hM hN q r s t := by
  dsimp only [evaluation]
  rw [family_reindex, uncurry_natural_left]

lemma family_face (k : Fin 4) : T ◁ SSet.stdSimplex.δ k ≫
    family i hK hL hM hN q r s t =
    t ▷ SSet.stdSimplex.obj (SimplexCategory.mk 2) ≫ faces i hK hL hM hN q r s k := by
  dsimp only [family]
  rw [whisker_exchange_assoc, tetrahedron_face]

lemma family_degenerate (d : Fin (n + 1))
    (e : T ⟶ (ihom (SSet.stdSimplex.obj (SimplexCategory.mk n))).obj K) :
    family i hK hL hM hN q r s (e ≫ DegenerateHornInput.boundary i d K) =
      fst T (SSet.stdSimplex.obj (SimplexCategory.mk 3)) ≫ e ≫
        DegenerateHornInput.degeneracy d K ≫
          (ihom (SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)))).map (q ≫ r ≫ s) := by
  let u := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompatibleInputUnion.toInputs
    (fun _ : Fin (n + 1) => (ihom (SSet.stdSimplex.obj (SimplexCategory.mk n))).obj K)
    (fun d => DegenerateHornInput.boundary i d K) d
  have hu : u ≫ (inputs (K := K) i).ι = DegenerateHornInput.boundary i d K := rfl
  dsimp only [family]
  rw [← hu, ← Category.assoc e, comp_whiskerRight, Category.assoc,
    tetrahedron_relative, whiskerRight_fst_assoc]
  dsimp only [prescribed]
  rw [← Category.assoc (e ≫ u), Category.assoc e, hu]
  dsimp only [sourceThenMap]
  rw [Category.assoc, ← Category.assoc (DegenerateHornInput.boundary i d K),
    NormalizedHornFilling.section_degeneracy]

end SerrePositivity.SimplicialModel.NormalizedHornTargetAssociativity
