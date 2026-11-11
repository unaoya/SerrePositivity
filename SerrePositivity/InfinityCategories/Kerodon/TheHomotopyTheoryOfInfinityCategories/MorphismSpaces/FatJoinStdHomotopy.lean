module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FatJoinStdNormalize
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FatJoinTransformFamily
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FatJoinHomotopyFixed

/-!
概要：標準単体の fat join の二つの正規化への可逆な変形。
方針：有限順序集合の単調写像の族をパラメーター付きの普遍性で貼る。
規約：左右の因子を全時間で固定する。
使われ方：Kerodon Theorem 4.6.2.8（Tag 01HV） の標準単体の比較。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：左の変形の族は元の区間の零端を固定する。
方針：各頂点で有限順序集合の固定条件を使う。
規約：変形の時間は第二の標準区間。
使われ方：Kerodon §4.6.2（Tag 01HM） の左因子の固定。 -/
lemma stdSimplexTripleProductMap_leftClampHom_fixed (n : ℕ) :
    (SSet.ι₀ (X := (Δ[n] : SSet.{u})) ▷ (Δ[1] : SSet.{u})) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.stdSimplexTripleProductMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftClampHom n) = fst Δ[n] Δ[1] := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨a, s⟩
  apply stdSimplex.ext
  intro i
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftClampHom_fixed_zero n (a i) (s i)

/-- 概要：右の変形の族は元の区間の一端を固定する。
方針：各頂点で有限順序集合の固定条件を使う。
規約：変形の時間は第二の標準区間。
使われ方：Kerodon §4.6.2（Tag 01HM） の右因子の固定。 -/
lemma stdSimplexTripleProductMap_rightClampHom_fixed (n : ℕ) :
    (SSet.ι₁ (X := (Δ[n] : SSet.{u})) ▷ (Δ[1] : SSet.{u})) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.stdSimplexTripleProductMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightClampHom n) = fst Δ[n] Δ[1] := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨a, s⟩
  apply stdSimplex.ext
  intro i
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightClampHom_fixed_one n (a i) (s i)

/-- 概要：恒等射から左の正規化への時間付きの変形の射。
方針：左の単調な変形の族と右成分の恒等を貼り合わせる。
規約：両因子を全ての時間で固定する。
使われ方：Kerodon §4.6.2（Tag 01HM） の第一の変形。 -/
noncomputable def fatJoinStdLeftFamily (n m : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin (Δ[n] : SSet.{u}) Δ[m] ⊗ Δ[1] ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin (Δ[n] : SSet.{u}) Δ[m] :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinTransformFamily (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.stdSimplexTripleProductMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftClampHom n))
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
使われ方：Kerodon §4.6.2（Tag 01HM） の第二の変形。 -/
noncomputable def fatJoinStdRightFamily (n m : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin (Δ[n] : SSet.{u}) Δ[m] ⊗ Δ[1] ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin (Δ[n] : SSet.{u}) Δ[m] :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinTransformFamily
    (fst (Δ[n] ⊗ Δ[1]) Δ[1] ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.stdSimplexProductMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftClamp n))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.stdSimplexTripleProductMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightClampHom m)) (by
      apply SSet.hom_ext
      rintro ⟨⟨d⟩⟩
      apply ConcreteCategory.hom_ext
      rintro ⟨a, s⟩
      apply stdSimplex.ext
      intro i
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftClamp_zero n (a i))
    (stdSimplexTripleProductMap_rightClampHom_fixed m)

/-- 概要：第一の変形の時間零は恒等射。
方針：円柱と左右の因子上で比較し、単調写像の時間零を計算する。
規約：fat join の全単体での厳密な等式。
使われ方：Kerodon §4.6.2（Tag 01HM） の第一の変形の始点。 -/
lemma fatJoinStdLeftFamily_zero (n m : ℕ) :
    SSet.ι₀ ≫ fatJoinStdLeftFamily.{u} n m = 𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin (Δ[n] : SSet.{u}) Δ[m]) := by
  have hc : SSet.ι₀ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinTransformFamilyCylinder
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.stdSimplexTripleProductMap.{u} (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftClampHom n))
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
        exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftClampHom_zero n (a i) (t i)
      · rfl
    · rfl
  unfold fatJoinStdLeftFamily
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin_hom_ext
  · rw [← SSet.ι₀_comp_assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder_transformFamily,
      ← Category.assoc, hc, Category.id_comp, Category.comp_id]
  · rw [← SSet.ι₀_comp_assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl_transformFamily,
      ← Category.assoc, SSet.ι₀_fst, Category.id_comp, Category.comp_id]
  · rw [← SSet.ι₀_comp_assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr_transformFamily,
      ← Category.assoc, SSet.ι₀_fst, Category.id_comp, Category.comp_id]

/-- 概要：第一の変形の時間一は左の正規化。
方針：円柱上で左の単調写像の時間一を計算する。
規約：左右の因子は固定する。
使われ方：Kerodon §4.6.2（Tag 01HM） の第一の変形の終点。 -/
lemma fatJoinStdLeftFamily_one (n m : ℕ) :
    SSet.ι₁ ≫ fatJoinStdLeftFamily.{u} n m = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinStdLeftNormalize n m := by
  have hc : SSet.ι₁ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinTransformFamilyCylinder
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.stdSimplexTripleProductMap.{u} (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftClampHom n))
      (fst (Δ[m] ⊗ Δ[1]) Δ[1] ≫ fst Δ[m] Δ[1]) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinTransformCylinder (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.stdSimplexProductMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftClamp n))
          (fst Δ[m] Δ[1]) := by
    apply SSet.hom_ext
    rintro ⟨⟨d⟩⟩
    apply ConcreteCategory.hom_ext
    rintro ⟨⟨a, t⟩, b⟩
    apply Prod.ext
    · apply Prod.ext
      · apply stdSimplex.ext
        intro i
        exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftClampHom_one n (a i) (t i)
      · rfl
    · rfl
  unfold fatJoinStdLeftFamily _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinStdLeftNormalize
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin_hom_ext
  · rw [← SSet.ι₁_comp_assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder_transformFamily,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder_transform, ← Category.assoc, hc]
  · rw [← SSet.ι₁_comp_assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl_transformFamily, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl_transform,
      ← Category.assoc, SSet.ι₁_fst, Category.id_comp]
  · rw [← SSet.ι₁_comp_assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr_transformFamily, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr_transform,
      ← Category.assoc, SSet.ι₁_fst, Category.id_comp]

/-- 概要：第二の変形の時間零は左右の正規化。
方針：右の単調写像の時間零を円柱上で計算する。
規約：左の正規化は全時間で保つ。
使われ方：Kerodon §4.6.2（Tag 01HM） の第二の変形の始点。 -/
lemma fatJoinStdRightFamily_zero (n m : ℕ) :
    SSet.ι₀ ≫ fatJoinStdRightFamily.{u} n m = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinStdNormalize n m := by
  have hc : SSet.ι₀ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinTransformFamilyCylinder
      (fst (Δ[n] ⊗ Δ[1]) Δ[1] ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.stdSimplexProductMap.{u} (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftClamp n))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.stdSimplexTripleProductMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightClampHom m)) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinTransformCylinder (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.stdSimplexProductMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftClamp n))
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.stdSimplexProductMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightClamp m)) := by
    apply SSet.hom_ext
    rintro ⟨⟨d⟩⟩
    apply ConcreteCategory.hom_ext
    rintro ⟨⟨a, t⟩, b⟩
    apply Prod.ext
    · rfl
    · apply stdSimplex.ext
      intro i
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightClampHom_zero m (b i) (t i)
  unfold fatJoinStdRightFamily _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinStdNormalize
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin_hom_ext
  · rw [← SSet.ι₀_comp_assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder_transformFamily,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder_transform, ← Category.assoc, hc]
  · rw [← SSet.ι₀_comp_assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl_transformFamily, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl_transform,
      ← Category.assoc, SSet.ι₀_fst, Category.id_comp]
  · rw [← SSet.ι₀_comp_assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr_transformFamily, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr_transform,
      ← Category.assoc, SSet.ι₀_fst, Category.id_comp]

/-- 概要：第二の変形の時間一は左の正規化。
方針：右の単調写像の時間一が恒等となることを円柱上で計算する。
規約：左右の因子は全時間で固定する。
使われ方：Kerodon §4.6.2（Tag 01HM） の第二の変形の終点。 -/
lemma fatJoinStdRightFamily_one (n m : ℕ) :
    SSet.ι₁ ≫ fatJoinStdRightFamily.{u} n m = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinStdLeftNormalize n m := by
  have hc : SSet.ι₁ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinTransformFamilyCylinder
      (fst (Δ[n] ⊗ Δ[1]) Δ[1] ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.stdSimplexProductMap.{u} (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftClamp n))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.stdSimplexTripleProductMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightClampHom m)) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinTransformCylinder (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.stdSimplexProductMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftClamp n))
          (fst Δ[m] Δ[1]) := by
    apply SSet.hom_ext
    rintro ⟨⟨d⟩⟩
    apply ConcreteCategory.hom_ext
    rintro ⟨⟨a, t⟩, b⟩
    apply Prod.ext
    · rfl
    · apply stdSimplex.ext
      intro i
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightClampHom_one m (b i) (t i)
  unfold fatJoinStdRightFamily _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinStdLeftNormalize
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin_hom_ext
  · rw [← SSet.ι₁_comp_assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder_transformFamily,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder_transform, ← Category.assoc, hc]
  · rw [← SSet.ι₁_comp_assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl_transformFamily, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl_transform,
      ← Category.assoc, SSet.ι₁_fst, Category.id_comp]
  · rw [← SSet.ι₁_comp_assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr_transformFamily, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr_transform,
      ← Category.assoc, SSet.ι₁_fst, Category.id_comp]

/-- 概要：標準単体の fat join の恒等射から左の正規化へのホモトピー。
方針：構成済みの変形の族と両端の等式を束ねる。
規約：左右の因子は全時間で固定する。
使われ方：Kerodon Theorem 4.6.2.8（Tag 01HV） の第一の変形。 -/
noncomputable def fatJoinStdLeftHomotopy (n m : ℕ) :
    SSet.Homotopy (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin (Δ[n] : SSet.{u}) Δ[m])) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinStdLeftNormalize n m) where
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
使われ方：Kerodon Theorem 4.6.2.8（Tag 01HV） の第二の変形。 -/
noncomputable def fatJoinStdRightHomotopy (n m : ℕ) :
    SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinStdNormalize.{u} n m) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinStdLeftNormalize n m) where
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
使われ方：Kerodon §4.6.2（Tag 01HM） の前合成の同値条件の検出。 -/
lemma fatJoinStdLeftHomotopy_isInvertible (n m : ℕ) :
    ∀ x : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin (Δ[n] : SSet.{u}) Δ[m]) _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (fatJoinStdLeftHomotopy n m) x).toTruncated := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinHomotopy_isInvertible_of_fixed_factors
  · change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl Δ[n] Δ[m] ▷ Δ[1]) ≫ fatJoinStdLeftFamily n m = _
    unfold fatJoinStdLeftFamily
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl_transformFamily _ _ _ _
  · change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr Δ[n] Δ[m] ▷ Δ[1]) ≫ fatJoinStdLeftFamily n m = _
    unfold fatJoinStdLeftFamily
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr_transformFamily _ _ _ _

/-- 概要：右成分の正規化のホモトピーの各頂点の辺は可逆。
方針：両因子を全時間で固定する条件を使う。
規約：fat join 自身の quasicategory 性は不要。
使われ方：Kerodon §4.6.2（Tag 01HM） の二つの可逆な変形による検出。 -/
lemma fatJoinStdRightHomotopy_isInvertible (n m : ℕ) :
    ∀ x : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin (Δ[n] : SSet.{u}) Δ[m]) _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (fatJoinStdRightHomotopy n m) x).toTruncated := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinHomotopy_isInvertible_of_fixed_factors
  · change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl Δ[n] Δ[m] ▷ Δ[1]) ≫ fatJoinStdRightFamily n m = _
    unfold fatJoinStdRightFamily
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl_transformFamily _ _ _ _
  · change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr Δ[n] Δ[m] ▷ Δ[1]) ≫ fatJoinStdRightFamily n m = _
    unfold fatJoinStdRightFamily
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr_transformFamily _ _ _ _

/-- 概要：標準単体の fat join の左の正規化は前合成の同値条件を満たす。
方針：恒等射からの点ごとに可逆なホモトピーを使う。
規約：任意の自然数 n、m。比較射自体の同値性はまだ結論しない。
使われ方：Kerodon §4.6.2（Tag 01HM） の正規化による比較。 -/
lemma isPrecompositionEquivalence_fatJoinStdLeftNormalize (n m : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinStdLeftNormalize.{u} n m) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isPrecompositionEquivalence_iff_of_homotopy (fatJoinStdLeftHomotopy n m)
    (fatJoinStdLeftHomotopy_isInvertible n m)).mp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isPrecompositionEquivalence_id _)

/-- 概要：標準単体の fat join の左右の正規化は前合成の同値条件を満たす。
方針：左の正規化への点ごとに可逆なホモトピーを使う。
規約：任意の自然数 n、m。比較射と切断の合成との同一視は別に必要。
使われ方：Kerodon Theorem 4.6.2.8（Tag 01HV） の正規化による比較。 -/
lemma isPrecompositionEquivalence_fatJoinStdNormalize (n m : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinStdNormalize.{u} n m) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isPrecompositionEquivalence_iff_of_homotopy (fatJoinStdRightHomotopy n m)
    (fatJoinStdRightHomotopy_isInvertible n m)).mpr
      (isPrecompositionEquivalence_fatJoinStdLeftNormalize n m)

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
