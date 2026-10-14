module
public import SerrePositivity.DifferentialGraded.Complexes.ClosedMaps
public import Mathlib.Algebra.Homology.HomologicalComplexLimits

/-! # 全次数 Hom の余極限包含による判定 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w w'
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits MonoidalCategory
variable {A : Type u} [CommRing A] {J : Type w} [Category.{w'} J]

/-- 指定複体余極限からの全次数 Hom は包含前の成分で判定できる。 -/
lemma homComplex_colimit_ext (F : J ⥤ Complex A) [HasColimit F] {P K : Complex A}
    {f g : K ⟶ homComplex A (colimit F) P}
    (h : ∀ j, f ≫ homPrecompose (colimit.ι F j) P =
      g ≫ homPrecompose (colimit.ι F j) P) : f = g := by
  apply (tensorRightHomEquiv (colimit F) K P).symm.injective
  change uncurryRight f = uncurryRight g
  apply (isColimitOfPreserves (tensorLeft K) (colimit.isColimit F)).hom_ext
  intro j
  change (K ◁ colimit.ι F j) ≫ uncurryRight f = (K ◁ colimit.ι F j) ≫ uncurryRight g
  rw [← id_tensorHom]
  apply (tensorRightHomEquiv (F.obj j) K P).injective
  change curryRight ((𝟙 K ⊗ₘ colimit.ι F j) ≫ uncurryRight f) =
    curryRight ((𝟙 K ⊗ₘ colimit.ι F j) ≫ uncurryRight g)
  rw [curryRight_naturality_domain, curryRight_naturality_domain,
    curryRight_uncurryRight, curryRight_uncurryRight]
  exact h j
end SerrePositivity.DifferentialGraded
