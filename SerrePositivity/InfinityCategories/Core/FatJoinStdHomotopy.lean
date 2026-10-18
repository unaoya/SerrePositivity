module

public import SerrePositivity.InfinityCategories.Core.FatJoinStdNormalize
public import SerrePositivity.InfinityCategories.Core.FatJoinTransformFamily
public import SerrePositivity.InfinityCategories.Core.FatJoinHomotopyFixed

/-!
概要：標準単体の fat join の二つの正規化への可逆な変形。
方針：有限順序集合の単調写像の族をパラメーター付きの普遍性で貼る。
規約：左右の因子を全時間で固定する。
使われ方：Kerodon Theorem 4.6.2.8 の標準単体の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：左の変形の族は元の区間の零端を固定する。
方針：各頂点で有限順序集合の固定条件を使う。
規約：変形の時間は第二の標準区間。
使われ方：Kerodon §4.6.2 の左因子の固定。 -/
lemma stdSimplexTripleProductMap_leftClampHom_fixed (n : ℕ) :
    (SSet.ι₀ (X := (Δ[n] : SSet.{u})) ▷ (Δ[1] : SSet.{u})) ≫
        stdSimplexTripleProductMap (FatJoinStd.leftClampHom n) = fst Δ[n] Δ[1] := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨a, s⟩
  apply stdSimplex.ext
  intro i
  exact FatJoinStd.leftClampHom_fixed_zero n (a i) (s i)

/-- 概要：右の変形の族は元の区間の一端を固定する。
方針：各頂点で有限順序集合の固定条件を使う。
規約：変形の時間は第二の標準区間。
使われ方：Kerodon §4.6.2 の右因子の固定。 -/
lemma stdSimplexTripleProductMap_rightClampHom_fixed (n : ℕ) :
    (SSet.ι₁ (X := (Δ[n] : SSet.{u})) ▷ (Δ[1] : SSet.{u})) ≫
        stdSimplexTripleProductMap (FatJoinStd.rightClampHom n) = fst Δ[n] Δ[1] := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨a, s⟩
  apply stdSimplex.ext
  intro i
  exact FatJoinStd.rightClampHom_fixed_one n (a i) (s i)

/-- 概要：恒等射から左の正規化への時間付きの変形の射。
方針：左の単調な変形の族と右成分の恒等を貼り合わせる。
規約：両因子を全ての時間で固定する。
使われ方：Kerodon §4.6.2 の第一の変形。 -/
noncomputable def fatJoinStdLeftFamily (n m : ℕ) :
    fatJoin (Δ[n] : SSet.{u}) Δ[m] ⊗ Δ[1] ⟶ fatJoin (Δ[n] : SSet.{u}) Δ[m] :=
  fatJoinTransformFamily (stdSimplexTripleProductMap (FatJoinStd.leftClampHom n))
    (fst (Δ[m] ⊗ Δ[1]) Δ[1] ≫ fst Δ[m] Δ[1])
    (stdSimplexTripleProductMap_leftClampHom_fixed n) (by
      apply SSet.hom_ext
      intro d
      apply ConcreteCategory.hom_ext
      intro a
      rfl)

/-- 概要：左右の正規化から左の正規化への時間付きの変形の射。
方針：左の正規化を保ち、右の単調な変形の族を貼り合わせる。
規約：両因子を全ての時間で固定する。
使われ方：Kerodon §4.6.2 の第二の変形。 -/
noncomputable def fatJoinStdRightFamily (n m : ℕ) :
    fatJoin (Δ[n] : SSet.{u}) Δ[m] ⊗ Δ[1] ⟶ fatJoin (Δ[n] : SSet.{u}) Δ[m] :=
  fatJoinTransformFamily
    (fst (Δ[n] ⊗ Δ[1]) Δ[1] ≫ stdSimplexProductMap (FatJoinStd.leftClamp n))
    (stdSimplexTripleProductMap (FatJoinStd.rightClampHom m)) (by
      apply SSet.hom_ext
      rintro ⟨⟨d⟩⟩
      apply ConcreteCategory.hom_ext
      rintro ⟨a, s⟩
      apply stdSimplex.ext
      intro i
      exact FatJoinStd.leftClamp_zero n (a i))
    (stdSimplexTripleProductMap_rightClampHom_fixed m)

/-- 概要：第一の変形の時間零は恒等射。
方針：円柱と左右の因子上で比較し、単調写像の時間零を計算する。
規約：fat join の全単体での厳密な等式。
使われ方：Kerodon §4.6.2 の第一の変形の始点。 -/
lemma fatJoinStdLeftFamily_zero (n m : ℕ) :
    SSet.ι₀ ≫ fatJoinStdLeftFamily.{u} n m = 𝟙 (fatJoin (Δ[n] : SSet.{u}) Δ[m]) := by
  have hc : SSet.ι₀ ≫ fatJoinTransformFamilyCylinder
      (stdSimplexTripleProductMap.{u} (FatJoinStd.leftClampHom n))
      (fst (Δ[m] ⊗ Δ[1]) Δ[1] ≫ fst Δ[m] Δ[1]) =
        𝟙 (((Δ[n] : SSet.{u}) ⊗ Δ[1]) ⊗ Δ[m]) := by
    apply SSet.hom_ext
    rintro ⟨⟨d⟩⟩
    apply ConcreteCategory.hom_ext
    rintro ⟨⟨a, t⟩, b⟩
    apply Prod.ext
    · apply Prod.ext
      · apply stdSimplex.ext
        intro i
        exact FatJoinStd.leftClampHom_zero n (a i) (t i)
      · rfl
    · rfl
  unfold fatJoinStdLeftFamily
  apply fatJoin_hom_ext
  · rw [← SSet.ι₀_comp_assoc, fatJoinCylinder_transformFamily,
      ← Category.assoc, hc, Category.id_comp, Category.comp_id]
  · rw [← SSet.ι₀_comp_assoc, fatJoinInl_transformFamily,
      ← Category.assoc, SSet.ι₀_fst, Category.id_comp, Category.comp_id]
  · rw [← SSet.ι₀_comp_assoc, fatJoinInr_transformFamily,
      ← Category.assoc, SSet.ι₀_fst, Category.id_comp, Category.comp_id]

/-- 概要：第一の変形の時間一は左の正規化。
方針：円柱上で左の単調写像の時間一を計算する。
規約：左右の因子は固定する。
使われ方：Kerodon §4.6.2 の第一の変形の終点。 -/
lemma fatJoinStdLeftFamily_one (n m : ℕ) :
    SSet.ι₁ ≫ fatJoinStdLeftFamily.{u} n m = fatJoinStdLeftNormalize n m := by
  have hc : SSet.ι₁ ≫ fatJoinTransformFamilyCylinder
      (stdSimplexTripleProductMap.{u} (FatJoinStd.leftClampHom n))
      (fst (Δ[m] ⊗ Δ[1]) Δ[1] ≫ fst Δ[m] Δ[1]) =
        fatJoinTransformCylinder (stdSimplexProductMap (FatJoinStd.leftClamp n))
          (fst Δ[m] Δ[1]) := by
    apply SSet.hom_ext
    rintro ⟨⟨d⟩⟩
    apply ConcreteCategory.hom_ext
    rintro ⟨⟨a, t⟩, b⟩
    apply Prod.ext
    · apply Prod.ext
      · apply stdSimplex.ext
        intro i
        exact FatJoinStd.leftClampHom_one n (a i) (t i)
      · rfl
    · rfl
  unfold fatJoinStdLeftFamily fatJoinStdLeftNormalize
  apply fatJoin_hom_ext
  · rw [← SSet.ι₁_comp_assoc, fatJoinCylinder_transformFamily,
      fatJoinCylinder_transform, ← Category.assoc, hc]
  · rw [← SSet.ι₁_comp_assoc, fatJoinInl_transformFamily, fatJoinInl_transform,
      ← Category.assoc, SSet.ι₁_fst, Category.id_comp]
  · rw [← SSet.ι₁_comp_assoc, fatJoinInr_transformFamily, fatJoinInr_transform,
      ← Category.assoc, SSet.ι₁_fst, Category.id_comp]

/-- 概要：第二の変形の時間零は左右の正規化。
方針：右の単調写像の時間零を円柱上で計算する。
規約：左の正規化は全時間で保つ。
使われ方：Kerodon §4.6.2 の第二の変形の始点。 -/
lemma fatJoinStdRightFamily_zero (n m : ℕ) :
    SSet.ι₀ ≫ fatJoinStdRightFamily.{u} n m = fatJoinStdNormalize n m := by
  have hc : SSet.ι₀ ≫ fatJoinTransformFamilyCylinder
      (fst (Δ[n] ⊗ Δ[1]) Δ[1] ≫ stdSimplexProductMap.{u} (FatJoinStd.leftClamp n))
      (stdSimplexTripleProductMap (FatJoinStd.rightClampHom m)) =
        fatJoinTransformCylinder (stdSimplexProductMap (FatJoinStd.leftClamp n))
          (stdSimplexProductMap (FatJoinStd.rightClamp m)) := by
    apply SSet.hom_ext
    rintro ⟨⟨d⟩⟩
    apply ConcreteCategory.hom_ext
    rintro ⟨⟨a, t⟩, b⟩
    apply Prod.ext
    · rfl
    · apply stdSimplex.ext
      intro i
      exact FatJoinStd.rightClampHom_zero m (b i) (t i)
  unfold fatJoinStdRightFamily fatJoinStdNormalize
  apply fatJoin_hom_ext
  · rw [← SSet.ι₀_comp_assoc, fatJoinCylinder_transformFamily,
      fatJoinCylinder_transform, ← Category.assoc, hc]
  · rw [← SSet.ι₀_comp_assoc, fatJoinInl_transformFamily, fatJoinInl_transform,
      ← Category.assoc, SSet.ι₀_fst, Category.id_comp]
  · rw [← SSet.ι₀_comp_assoc, fatJoinInr_transformFamily, fatJoinInr_transform,
      ← Category.assoc, SSet.ι₀_fst, Category.id_comp]

/-- 概要：第二の変形の時間一は左の正規化。
方針：右の単調写像の時間一が恒等となることを円柱上で計算する。
規約：左右の因子は全時間で固定する。
使われ方：Kerodon §4.6.2 の第二の変形の終点。 -/
lemma fatJoinStdRightFamily_one (n m : ℕ) :
    SSet.ι₁ ≫ fatJoinStdRightFamily.{u} n m = fatJoinStdLeftNormalize n m := by
  have hc : SSet.ι₁ ≫ fatJoinTransformFamilyCylinder
      (fst (Δ[n] ⊗ Δ[1]) Δ[1] ≫ stdSimplexProductMap.{u} (FatJoinStd.leftClamp n))
      (stdSimplexTripleProductMap (FatJoinStd.rightClampHom m)) =
        fatJoinTransformCylinder (stdSimplexProductMap (FatJoinStd.leftClamp n))
          (fst Δ[m] Δ[1]) := by
    apply SSet.hom_ext
    rintro ⟨⟨d⟩⟩
    apply ConcreteCategory.hom_ext
    rintro ⟨⟨a, t⟩, b⟩
    apply Prod.ext
    · rfl
    · apply stdSimplex.ext
      intro i
      exact FatJoinStd.rightClampHom_one m (b i) (t i)
  unfold fatJoinStdRightFamily fatJoinStdLeftNormalize
  apply fatJoin_hom_ext
  · rw [← SSet.ι₁_comp_assoc, fatJoinCylinder_transformFamily,
      fatJoinCylinder_transform, ← Category.assoc, hc]
  · rw [← SSet.ι₁_comp_assoc, fatJoinInl_transformFamily, fatJoinInl_transform,
      ← Category.assoc, SSet.ι₁_fst, Category.id_comp]
  · rw [← SSet.ι₁_comp_assoc, fatJoinInr_transformFamily, fatJoinInr_transform,
      ← Category.assoc, SSet.ι₁_fst, Category.id_comp]

/-- 概要：標準単体の fat join の恒等射から左の正規化へのホモトピー。
方針：構成済みの変形の族と両端の等式を束ねる。
規約：左右の因子は全時間で固定する。
使われ方：Kerodon Theorem 4.6.2.8 の第一の変形。 -/
noncomputable def fatJoinStdLeftHomotopy (n m : ℕ) :
    SSet.Homotopy (𝟙 (fatJoin (Δ[n] : SSet.{u}) Δ[m])) (fatJoinStdLeftNormalize n m) where
  h := fatJoinStdLeftFamily n m
  h₀ := fatJoinStdLeftFamily_zero n m
  h₁ := fatJoinStdLeftFamily_one n m
  rel := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro s
    exact False.elim s.1.property

/-- 概要：左右の正規化から左の正規化へのホモトピー。
方針：構成済みの右成分の変形の族と両端の等式を束ねる。
規約：第一のホモトピーと同じ標的の自己射に向かう。
使われ方：Kerodon Theorem 4.6.2.8 の第二の変形。 -/
noncomputable def fatJoinStdRightHomotopy (n m : ℕ) :
    SSet.Homotopy (fatJoinStdNormalize.{u} n m) (fatJoinStdLeftNormalize n m) where
  h := fatJoinStdRightFamily n m
  h₀ := fatJoinStdRightFamily_zero n m
  h₁ := fatJoinStdRightFamily_one n m
  rel := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro s
    exact False.elim s.1.property

/-- 概要：左成分の正規化のホモトピーの各頂点の辺は可逆。
方針：両因子を全時間で固定することから頂点の辺が退化していると検出する。
規約：fat join 自身の quasicategory 性は不要。
使われ方：Kerodon §4.6.2 の前合成の同値条件の検出。 -/
lemma fatJoinStdLeftHomotopy_isInvertible (n m : ℕ) :
    ∀ x : (fatJoin (Δ[n] : SSet.{u}) Δ[m]) _⦋0⦌,
      IsInvertibleEdge (simplicialHomotopyVertexEdge (fatJoinStdLeftHomotopy n m) x).toTruncated := by
  apply fatJoinHomotopy_isInvertible_of_fixed_factors
  · change (fatJoinInl Δ[n] Δ[m] ▷ Δ[1]) ≫ fatJoinStdLeftFamily n m = _
    unfold fatJoinStdLeftFamily
    exact fatJoinInl_transformFamily _ _ _ _
  · change (fatJoinInr Δ[n] Δ[m] ▷ Δ[1]) ≫ fatJoinStdLeftFamily n m = _
    unfold fatJoinStdLeftFamily
    exact fatJoinInr_transformFamily _ _ _ _

/-- 概要：右成分の正規化のホモトピーの各頂点の辺は可逆。
方針：両因子を全時間で固定する条件を使う。
規約：fat join 自身の quasicategory 性は不要。
使われ方：Kerodon §4.6.2 の二つの可逆な変形による検出。 -/
lemma fatJoinStdRightHomotopy_isInvertible (n m : ℕ) :
    ∀ x : (fatJoin (Δ[n] : SSet.{u}) Δ[m]) _⦋0⦌,
      IsInvertibleEdge (simplicialHomotopyVertexEdge (fatJoinStdRightHomotopy n m) x).toTruncated := by
  apply fatJoinHomotopy_isInvertible_of_fixed_factors
  · change (fatJoinInl Δ[n] Δ[m] ▷ Δ[1]) ≫ fatJoinStdRightFamily n m = _
    unfold fatJoinStdRightFamily
    exact fatJoinInl_transformFamily _ _ _ _
  · change (fatJoinInr Δ[n] Δ[m] ▷ Δ[1]) ≫ fatJoinStdRightFamily n m = _
    unfold fatJoinStdRightFamily
    exact fatJoinInr_transformFamily _ _ _ _

/-- 概要：標準単体の fat join の左の正規化は前合成の同値条件を満たす。
方針：恒等射からの点ごとに可逆なホモトピーを使う。
規約：任意の自然数 n、m。比較射自体の同値性はまだ結論しない。
使われ方：Kerodon §4.6.2 の正規化による比較。 -/
lemma isPrecompositionEquivalence_fatJoinStdLeftNormalize (n m : ℕ) :
    IsPrecompositionEquivalence (fatJoinStdLeftNormalize.{u} n m) :=
  (isPrecompositionEquivalence_iff_of_homotopy (fatJoinStdLeftHomotopy n m)
    (fatJoinStdLeftHomotopy_isInvertible n m)).mp (isPrecompositionEquivalence_id _)

/-- 概要：標準単体の fat join の左右の正規化は前合成の同値条件を満たす。
方針：左の正規化への点ごとに可逆なホモトピーを使う。
規約：任意の自然数 n、m。比較射と切断の合成との同一視は別に必要。
使われ方：Kerodon Theorem 4.6.2.8 の正規化による比較。 -/
lemma isPrecompositionEquivalence_fatJoinStdNormalize (n m : ℕ) :
    IsPrecompositionEquivalence (fatJoinStdNormalize.{u} n m) :=
  (isPrecompositionEquivalence_iff_of_homotopy (fatJoinStdRightHomotopy n m)
    (fatJoinStdRightHomotopy_isInvertible n m)).mpr
      (isPrecompositionEquivalence_fatJoinStdLeftNormalize n m)

end SerrePositivity.InfinityCategories
