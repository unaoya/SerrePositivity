module
public import SerrePositivity.InfinityCategories.Derived.Gluing.PinchedPullbackData

/-! 引き戻した全成分は、同じ線形微分方程式を満たす単体を一意に定める。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve.PinchedHom
variable {R : Type u} [CommRing R] {D₀ D₁ D₂ D₃ : Type v}
  [DGCategory R D₀] [DGCategory R D₁] [DGCategory R D₂] [DGCategory R D₃]
  {x₀ y₀ : D₀} {x₁ y₁ : D₁} {x₂ y₂ : D₂} {x₃ y₃ : D₃}
  {a : homObject R D₀ x₀ y₀ ⟶ homObject R D₁ x₁ y₁}
  {b : homObject R D₀ x₀ y₀ ⟶ homObject R D₂ x₂ y₂}
  {f : homObject R D₁ x₁ y₁ ⟶ homObject R D₃ x₃ y₃}
  {g : homObject R D₂ x₂ y₂ ⟶ homObject R D₃ x₃ y₃} {n : ℕ}

lemma dgGluingPinchedData_equation_image (z : LinearData R x₀ y₀ n)
    (s : LinearSimplex R x₁ y₁ n) (hz : pinchedLinearDataMap a z = s.val)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    a.f (k + 1) ((homObject R D₀ x₀ y₀).d k (k + 1) (z.component J k hJ hk)) =
      a.f (k + 1) (z.rhs J k hk) := by
  have hc := (ConcreteCategory.congr_hom (a.comm k (k + 1)) (z.component J k hJ hk)).symm
  change a.f (k + 1) ((homObject R D₀ x₀ y₀).d k (k + 1) (z.component J k hJ hk)) =
    (homObject R D₁ x₁ y₁).d k (k + 1)
      ((pinchedLinearDataMap a z).component J k hJ hk) at hc
  rw [hc, pinchedLinearDataMap_rhs]
  rw [hz]
  exact s.equation J k hJ hk

lemma dgGluingPinchedPullbackData_equation (h : IsPullback a b f g)
    (s : LinearSimplex R x₁ y₁ n) (t : LinearSimplex R x₂ y₂ n)
    (e : pinchedLinearSimplexMap f s = pinchedLinearSimplexMap g t)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    (homObject R D₀ x₀ y₀).d k (k + 1)
        ((dgGluingPinchedPullbackData h s t e).component J k hJ hk) =
      (dgGluingPinchedPullbackData h s t e).rhs J k hk := by
  apply dgGluingComplexPullback_ext h (k + 1)
  · exact dgGluingPinchedData_equation_image _ s
      (dgGluingPinchedPullbackData_fst h s t e) J k hJ hk
  · exact dgGluingPinchedData_equation_image _ t
      (dgGluingPinchedPullbackData_snd h s t e) J k hJ hk

def dgGluingPinchedPullbackSimplex (h : IsPullback a b f g)
    (s : LinearSimplex R x₁ y₁ n) (t : LinearSimplex R x₂ y₂ n)
    (e : pinchedLinearSimplexMap f s = pinchedLinearSimplexMap g t) :
    LinearSimplex R x₀ y₀ n :=
  ⟨dgGluingPinchedPullbackData h s t e,
    dgGluingPinchedPullbackData_equation h s t e⟩

lemma dgGluingPinchedPullbackSimplex_fst (h : IsPullback a b f g)
    (s : LinearSimplex R x₁ y₁ n) (t : LinearSimplex R x₂ y₂ n)
    (e : pinchedLinearSimplexMap f s = pinchedLinearSimplexMap g t) :
    pinchedLinearSimplexMap a (dgGluingPinchedPullbackSimplex h s t e) = s :=
  Subtype.ext (dgGluingPinchedPullbackData_fst h s t e)

lemma dgGluingPinchedPullbackSimplex_snd (h : IsPullback a b f g)
    (s : LinearSimplex R x₁ y₁ n) (t : LinearSimplex R x₂ y₂ n)
    (e : pinchedLinearSimplexMap f s = pinchedLinearSimplexMap g t) :
    pinchedLinearSimplexMap b (dgGluingPinchedPullbackSimplex h s t e) = t :=
  Subtype.ext (dgGluingPinchedPullbackData_snd h s t e)

lemma dgGluingPinchedPullbackSimplex_ext (h : IsPullback a b f g)
    (s t : LinearSimplex R x₀ y₀ n)
    (ha : pinchedLinearSimplexMap a s = pinchedLinearSimplexMap a t)
    (hb : pinchedLinearSimplexMap b s = pinchedLinearSimplexMap b t) : s = t := by
  apply Subtype.ext
  funext i
  apply dgGluingComplexPullback_ext h i.val.2
  · exact congrArg (fun z : LinearSimplex R x₁ y₁ n => z.val i) ha
  · exact congrArg (fun z : LinearSimplex R x₂ y₂ n => z.val i) hb

end SerrePositivity.InfinityCategories
