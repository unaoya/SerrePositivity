module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialReplacementFunctor
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
概要：定値図式の simplicial replacement と、始対象の係数値からの組み立て射。
方針：定値図式を底の nerve と係数値の直積に同定し、始対象からの係数輸送を後合成する。
規約：単体集合の直積のみを使い、空間の ∞ 余極限の存在は主張しない。
使われ方：Kerodon Examples 5.3.2.2（Tag 035W）、5.3.2.12（Tag 0252）、有限順序上の scaffold 比較の分解。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- 概要：定値図式の simplicial replacement は底の nerve と係数値の直積に同型。
方針：各次数で係数単体の Yoneda 表示と単体そのものを往復させる。
規約：係数値の Kan 性は不要。
使われ方：Kerodon Example 5.3.2.2（Tag 035W）、始対象の係数値を含む部分の表示。 -/
def simplicialReplacementConstantIso (C : Type u) [Category.{u} C] (K : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacement ((CategoryTheory.Functor.const C).obj K) ≅ nerve C ⊗ K where
  hom :=
    { app := fun _ ↦ ↾fun s ↦ (s.1, SSet.yonedaEquiv s.2)
      naturality := by
        intro d e α
        apply ConcreteCategory.hom_ext
        rintro ⟨σ, τ⟩
        change (Δ[d.unop.len] : SSet.{u}) ⟶ K at τ
        refine Prod.ext (by rfl) ?_
        change SSet.yonedaEquiv (stdSimplex.map α.unop ≫ τ ≫ 𝟙 K) =
          K.map α (SSet.yonedaEquiv τ)
        rw [Category.comp_id]
        exact (SSet.yonedaEquiv_naturality α.unop τ).symm }
  inv :=
    { app := fun _ ↦ ↾fun s ↦ ⟨s.1, SSet.yonedaEquiv.symm s.2⟩
      naturality := by
        intro d e α
        apply ConcreteCategory.hom_ext
        rintro ⟨σ, τ⟩
        refine Sigma.ext (by rfl) ?_
        apply heq_of_eq
        change SSet.yonedaEquiv.symm (K.map α τ) =
          stdSimplex.map α.unop ≫ SSet.yonedaEquiv.symm τ ≫ 𝟙 K
        rw [Category.comp_id]
        exact (SSet.yonedaEquiv_symm_naturality_left (X := K) α.unop τ).symm }
  hom_inv_id := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    rintro ⟨σ, τ⟩
    refine Sigma.ext (by rfl) ?_
    exact heq_of_eq (SSet.yonedaEquiv.symm_apply_apply τ)
  inv_hom_id := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    rintro ⟨σ, τ⟩
    exact Prod.ext rfl (SSet.yonedaEquiv.apply_symm_apply τ)

/-- 概要：定値図式の直積同型は底の射影を保つ。
方針：各次数の対の第一成分を計算する。
規約：直積の射影は CartesianMonoidalCategory.fst。
使われ方：Kerodon Example 5.3.2.2（Tag 035W）、底上での直積表示。 -/
lemma simplicialReplacementConstantIso_projection (C : Type u) [Category.{u} C]
    (K : SSet.{u}) :
    (simplicialReplacementConstantIso C K).hom ≫ fst (nerve C) K =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection ((CategoryTheory.Functor.const C).obj K) := rfl

/-- 概要：始対象における係数値の定値図式から元の係数図式への自然変換。
方針：始対象から各対象への一意な射を F で写す。
規約：底の始対象は通常の圏の始対象。
使われ方：Kerodon Remark 5.3.2.12（Tag 0252）、最初の係数値を全射列上へ展開する。 -/
def simplicialReplacementInitialCoefficient {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {t : C} (ht : IsInitial t) :
    (CategoryTheory.Functor.const C).obj (F.obj t) ⟶ F where
  app c := F.map (ht.to c)
  naturality c d f := by
    change 𝟙 _ ≫ F.map (ht.to d) = F.map (ht.to c) ≫ F.map f
    rw [Category.id_comp, ← F.map_comp]
    exact congrArg F.map (ht.hom_ext _ _)

/-- 概要：底の nerve と始対象の係数値の直積から simplicial replacement への標準射。
方針：定値係数の直積表示の逆に始対象からの係数輸送を後合成する。
規約：有限順序への特殊化で分解の最初の部分を与える。
使われ方：Kerodon Remark 5.3.2.12（Tag 0252）、有限順序上の scaffold 比較の帰納段階。 -/
def simplicialReplacementInitialAssembly {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {t : C} (ht : IsInitial t) :
    nerve C ⊗ F.obj t ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacement F :=
  (simplicialReplacementConstantIso C (F.obj t)).inv ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementMap (simplicialReplacementInitialCoefficient F ht)

/-- 概要：始対象の係数値からの組み立て射は底の第一射影を被覆する。
方針：係数の自然変換は底の射列を変えないことを計算する。
規約：直積の第二成分は始対象における係数値。
使われ方：Kerodon Remark 5.3.2.12（Tag 0252）、分解の各部分の底上の整合性。 -/
lemma simplicialReplacementInitialAssembly_projection {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {t : C} (ht : IsInitial t) :
    simplicialReplacementInitialAssembly F ht ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection F =
      fst (nerve C) (F.obj t) := rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
