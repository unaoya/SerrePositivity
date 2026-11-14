module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.EnrichedFunctors.ConeSimplexFunctor
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FiberCofiber.TruncatedJoinConeData
public import Mathlib.AlgebraicTopology.SimplexCategory.MorphismProperty

/-! # 切断錐の全順序写像への自然性

概要：面・退化の整合条件から、指定次数内の全順序写像への自然性を得る。
方針：自然性を満たす射の乗法的性質を切断単体圏の生成元で検証する。
規約：全単体族の apex は固定されている。使われ方：実 coslice 写像への組み立て。
-/
@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet Opposite
open scoped _root_.Simplicial
variable {K X : SSet.{u}} {f : K ⟶ X} {N : ℕ}

/-- 各図式単体に apex を前置する、切断単体圏上の自然変換。 -/
def TruncatedJoinConeData.naturalTransformation (C : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.TruncatedJoinConeData f N) :
    (SimplexCategory.Truncated.inclusion N).op ⋙ K ⟶
      (SimplexCategory.Truncated.inclusion N ⋙ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.coneSimplexFunctor).op ⋙ X := by
  let app (a : (SimplexCategory.Truncated N)ᵒᵖ) :
      ((SimplexCategory.Truncated.inclusion N).op ⋙ K).obj a ⟶
        ((SimplexCategory.Truncated.inclusion N ⋙ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.coneSimplexFunctor).op ⋙ X).obj a :=
    ↾fun σ => C.simplex a.unop.obj.len a.unop.property σ
  let W := (MorphismProperty.naturalityProperty app).unop
  have hW : W = ⊤ := by
    apply SimplexCategory.Truncated.morphismProperty_eq_top
    · intro n hn i
      apply ConcreteCategory.hom_ext
      intro σ
      change C.simplex n _ (K.δ i σ) =
        X.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.coneSimplexFunctor.map (SimplexCategory.δ i)).op (C.simplex (n + 1) _ σ)
      rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.coneSimplexFunctor_map_δ]
      exact (C.face_positive n (by omega) σ i).symm
    · intro n hn i
      apply ConcreteCategory.hom_ext
      intro σ
      change C.simplex (n + 1) _ (K.σ i σ) =
        X.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.coneSimplexFunctor.map (SimplexCategory.σ i)).op (C.simplex n _ σ)
      rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.coneSimplexFunctor_map_σ]
      exact (C.degeneracy_positive n (by omega) σ i).symm
  exact {
    app := app
    naturality := fun a b α => by
      have h : W α.unop := by rw [hW]; trivial
      exact h }

/-- 指定次数内の全順序写像に沿う錐単体の厳密な自然性。 -/
lemma TruncatedJoinConeData.naturality (C : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.TruncatedJoinConeData f N)
    {m n : ℕ} (hm : m ≤ N) (hn : n ≤ N) (α : ⦋m⦌ ⟶ ⦋n⦌) (σ : K _⦋n⦌) :
    X.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.coneSimplexFunctor.map α).op (C.simplex n hn σ) =
      C.simplex m hm (K.map α.op σ) := by
  have h := ConcreteCategory.congr_hom (C.naturalTransformation.naturality
    (SimplexCategory.Truncated.Hom.tr α (ha := hm) (hb := hn)).op) σ
  exact h.symm

end SerrePositivity.InfinityCategories.Project.DerivedCategories
