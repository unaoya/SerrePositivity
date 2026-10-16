module
public import SerrePositivity.DifferentialGraded.Quotient.CompositionDifferential

/-! # 最終合成の成分と元のHom包含との比較 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 微分を変えても最終合成の各次数の射は内部合成の射そのものである。 -/
lemma quotientComposition_f (S : Set D) (x y z : D) (n : ℤ) :
    (quotientComposition A D S x y z).f n = (internalComposition A D S x y z).f n := by
  apply mapBifunctor.hom_ext
  intro i j hij
  exact quotientComposition_ι A D S x y z i j n hij

/-- 最終合成は元のdg圏の豊穣合成と包含を通じて一致する。 -/
lemma quotientComposition_original (S : Set D) (x y z : D) :
    (originalHomInclusion A D S x y ⊗ₘ originalHomInclusion A D S y z) ≫
      quotientComposition A D S x y z =
    eComp (Complex A) x y z ≫ originalHomInclusion A D S x z := by
  apply HomologicalComplex.Hom.ext
  funext n
  rw [HomologicalComplex.comp_f, quotientComposition_f,
    HomologicalComplex.comp_f, originalHomInclusion_f]
  have h := congrArg (fun f => f.f n) (internalComposition_original_original A D S x y z)
  simp only [HomologicalComplex.comp_f] at h
  exact h

end SerrePositivity.DifferentialGraded.DGQuotient
