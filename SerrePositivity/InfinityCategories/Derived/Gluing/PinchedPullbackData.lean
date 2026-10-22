module
public import SerrePositivity.InfinityCategories.Derived.Gluing.ComplexPullbackDegrees
public import SerrePositivity.InfinityCategories.Derived.PinchedLinearChainMap

/-! 複体の引き戻しに沿い、同じ有限集合ごとの線形成分を一意に持ち上げる。 -/
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
  {g : homObject R D₂ x₂ y₂ ⟶ homObject R D₃ x₃ y₃}
  {n : ℕ}

def dgGluingPinchedPullbackData (h : IsPullback a b f g)
    (s : LinearSimplex R x₁ y₁ n) (t : LinearSimplex R x₂ y₂ n)
    (e : pinchedLinearSimplexMap f s = pinchedLinearSimplexMap g t) :
    LinearData R x₀ y₀ n := fun i =>
  Classical.choose (dgGluingComplexPullback_exists h i.val.2 (s.val i) (t.val i) (by
    have he := congrArg (fun z : LinearSimplex R x₃ y₃ n => z.val i) e
    exact he))

lemma dgGluingPinchedPullbackData_fst (h : IsPullback a b f g)
    (s : LinearSimplex R x₁ y₁ n) (t : LinearSimplex R x₂ y₂ n)
    (e : pinchedLinearSimplexMap f s = pinchedLinearSimplexMap g t) :
    pinchedLinearDataMap a (dgGluingPinchedPullbackData h s t e) = s.val := by
  funext i
  exact (Classical.choose_spec (dgGluingComplexPullback_exists h i.val.2 (s.val i) (t.val i)
    (congrArg (fun z : LinearSimplex R x₃ y₃ n => z.val i) e))).1

lemma dgGluingPinchedPullbackData_snd (h : IsPullback a b f g)
    (s : LinearSimplex R x₁ y₁ n) (t : LinearSimplex R x₂ y₂ n)
    (e : pinchedLinearSimplexMap f s = pinchedLinearSimplexMap g t) :
    pinchedLinearDataMap b (dgGluingPinchedPullbackData h s t e) = t.val := by
  funext i
  exact (Classical.choose_spec (dgGluingComplexPullback_exists h i.val.2 (s.val i) (t.val i)
    (congrArg (fun z : LinearSimplex R x₃ y₃ n => z.val i) e))).2

end SerrePositivity.InfinityCategories
