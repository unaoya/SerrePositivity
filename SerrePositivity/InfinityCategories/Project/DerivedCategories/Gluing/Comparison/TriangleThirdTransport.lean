module
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-! 同じ最初の二射影を保持した、distinguished 三角形の第三対象の同型移送。 -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Pretriangulated
variable {H : Type u} [Category.{v} H] [Limits.HasZeroObject H] [HasShift H ℤ]
  [Preadditive H] [∀ n : ℤ, (shiftFunctor H n).Additive] [Pretriangulated H]

def dgGluingTriangleThirdTransport (T : Triangle H) {Z : H} (e : T.obj₃ ≅ Z) : Triangle H :=
  Triangle.mk T.mor₁ (T.mor₂ ≫ e.hom) (e.inv ≫ T.mor₃)

lemma dgGluingTriangleThirdTransport_distinguished (T : Triangle H) (hT : T ∈ distTriang H)
    {Z : H} (e : T.obj₃ ≅ Z) : dgGluingTriangleThirdTransport T e ∈ distTriang H := by
  refine isomorphic_distinguished T hT (dgGluingTriangleThirdTransport T e) ?_
  exact Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) e.symm
    (by simp [dgGluingTriangleThirdTransport])
    (by simp [dgGluingTriangleThirdTransport, Category.assoc])
    (by simp [dgGluingTriangleThirdTransport])

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
