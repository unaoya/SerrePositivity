module

public import SerrePositivity.KST.LocalizingInvariants.CochainMappingCoconeMapQuasiIso
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-!
概要：元の cocone 射を実三角形の射へ束ね、接続ホモロジー射の自然性を保持する。
方針：同じ cone 射の shift と相殺同型の自然性から第三辺を検証する。
規約：元の比較 cochain を持つ cocone 射を使う。使われ方：対角模型の実完全列。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits HomologicalComplex CochainComplex Pretriangulated
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
variable {R : Type u} [CommRing R] {K L K' L' : Complex R}
  (f : K ⟶ L) (g : K' ⟶ L') (a : K ⟶ K') (b : L ⟶ L')
  (h : f ≫ b = a ≫ g)

def cochainCoconeTriangleMap : mappingCocone.triangle f ⟶ mappingCocone.triangle g where
  hom₁ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap f g a b h
  hom₂ := a
  hom₃ := b
  comm₁ := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap_fst f g a b h).symm
  comm₂ := h
  comm₃ := by
    symm
    change b ≫ (mappingCone.inr g ≫
      (shiftFunctorCompIsoId (Complex R) (-1 : ℤ) 1 (by omega)).inv.app _) =
      (mappingCone.inr f ≫
      (shiftFunctorCompIsoId (Complex R) (-1 : ℤ) 1 (by omega)).inv.app _) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap f g a b h)⟦(1 : ℤ)⟧'
    rw [cochainMappingCoconeMap_eq_shift]
    have hc := (mappingCone.triangleMap f g a b h).comm₂
    change mappingCone.inr f ≫ mappingCone.map f g a b h = b ≫ mappingCone.inr g at hc
    rw [← Category.assoc, ← hc, Category.assoc]
    simp only [Category.assoc]
    exact congrArg (fun t => mappingCone.inr f ≫ t)
      ((shiftFunctorCompIsoId (Complex R) (-1 : ℤ) 1 (by omega)).inv.naturality
        (mappingCone.map f g a b h))

lemma cochainTriangleHomologyConnecting_naturality {T S : Triangle (Complex R)}
    (φ : T ⟶ S) (n₀ n₁ : ℤ) (hn : n₀ + 1 = n₁) :
    homologyMap φ.hom₃ n₀ ≫ homologyδOfTriangle S n₀ n₁ hn =
      homologyδOfTriangle T n₀ n₁ hn ≫ homologyMap φ.hom₁ n₁ := by
  unfold homologyδOfTriangle
  rw [← Category.assoc, ← homologyMap_comp, ← φ.comm₃, homologyMap_comp, Category.assoc]
  exact congrArg (fun t => homologyMap T.mor₃ n₀ ≫ t)
    (((homologyFunctor (ModuleCat R) (.up ℤ) 0).shiftIso 1 n₀ n₁
      (by omega)).hom.naturality φ.hom₁)

end SerrePositivity.KST.LocalizingInvariants
