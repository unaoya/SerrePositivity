module
public import SerrePositivity.DifferentialGraded.Functor.Components
public import SerrePositivity.DifferentialGraded.Category.Examples

/-! # 複体に値を持つdg関手のcochain合成計算 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGFunctor
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

lemma map_forward_cochain (F : DGFunctor A D (Complex A)) {x y z : D} {p q n : ℤ}
    (f : GradedHom A x y p) (g : GradedHom A y z q) (hn : p + q = n) :
    (F.map x z).f n (forward A f g hn) =
      (p * q).negOnePow • ((F.map x y).f p f).comp ((F.map y z).f q g) hn := by
  have h := map_forward A F f g hn
  change (F.map x z).f n (forward A f g hn) =
    (enrichedComposition _ _ _).f n
      (ιTensorObj (homComplex A (F.obj x) (F.obj y)) (homComplex A (F.obj y) (F.obj z))
        p q n hn ((F.map x y).f p f ⊗ₜ[A] (F.map y z).f q g)) at h
  exact h.trans (enrichedComposition_apply _ _ _ p q n hn _ _)

end SerrePositivity.DifferentialGraded.DGFunctor
