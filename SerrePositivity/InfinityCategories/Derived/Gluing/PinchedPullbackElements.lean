module
public import SerrePositivity.InfinityCategories.Derived.Gluing.PinchedPullbackSimplex
public import SerrePositivity.InfinityCategories.Derived.PinchedChainMapComposition

/-! 線形持ち上げを実際の pinched 単体へ戻し、全次数の存在と共同単射性を得る。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve.PinchedHom
open scoped Simplicial
variable {R : Type u} [CommRing R] {D₀ D₁ D₂ D₃ : Type v}
  [DGCategory R D₀] [DGCategory R D₁] [DGCategory R D₂] [DGCategory R D₃]
  {x₀ y₀ : D₀} {x₁ y₁ : D₁} {x₂ y₂ : D₂} {x₃ y₃ : D₃}
  {a : homObject R D₀ x₀ y₀ ⟶ homObject R D₁ x₁ y₁}
  {b : homObject R D₀ x₀ y₀ ⟶ homObject R D₂ x₂ y₂}
  {f : homObject R D₁ x₁ y₁ ⟶ homObject R D₃ x₃ y₃}
  {g : homObject R D₂ x₂ y₂ ⟶ homObject R D₃ x₃ y₃}

lemma dgGluingPinchedPullbackElement_ext (h : IsPullback a b f g) (n : SimplexCategoryᵒᵖ)
    (s t : (DGNerve.pinchedHom R D₀ x₀ y₀).obj n)
    (ha : (pinchedHomChainMap a).app n s = (pinchedHomChainMap a).app n t)
    (hb : (pinchedHomChainMap b).app n s = (pinchedHomChainMap b).app n t) : s = t := by
  apply (linearEquiv x₀ y₀ n.unop.len).injective
  change toLinearSimplex s = toLinearSimplex t
  change pinchedHomChainMapSimplex a s = pinchedHomChainMapSimplex a t at ha
  change pinchedHomChainMapSimplex b s = pinchedHomChainMapSimplex b t at hb
  apply dgGluingPinchedPullbackSimplex_ext h
  · have hh := congrArg (toLinearSimplex (A := R) (x := x₁) (y := y₁)) ha
    simpa only [pinchedHomChainMapSimplex_linear] using hh
  · have hh := congrArg (toLinearSimplex (A := R) (x := x₂) (y := y₂)) hb
    simpa only [pinchedHomChainMapSimplex_linear] using hh

lemma dgGluingPinchedPullbackElement_exists (h : IsPullback a b f g) (n : SimplexCategoryᵒᵖ)
    (s : (DGNerve.pinchedHom R D₁ x₁ y₁).obj n)
    (t : (DGNerve.pinchedHom R D₂ x₂ y₂).obj n)
    (he : (pinchedHomChainMap f).app n s = (pinchedHomChainMap g).app n t) :
    ∃ z : (DGNerve.pinchedHom R D₀ x₀ y₀).obj n,
      (pinchedHomChainMap a).app n z = s ∧ (pinchedHomChainMap b).app n z = t := by
  change pinchedHomChainMapSimplex f s = pinchedHomChainMapSimplex g t at he
  have e : pinchedLinearSimplexMap f (toLinearSimplex s) =
      pinchedLinearSimplexMap g (toLinearSimplex t) := by
    simpa only [pinchedHomChainMapSimplex_linear] using
      congrArg (toLinearSimplex (A := R) (x := x₃) (y := y₃)) he
  refine ⟨(dgGluingPinchedPullbackSimplex h (toLinearSimplex s) (toLinearSimplex t) e).toPinched,
    ?_, ?_⟩
  · apply (linearEquiv x₁ y₁ n.unop.len).injective
    change toLinearSimplex (pinchedHomChainMapSimplex a _) = toLinearSimplex s
    rw [pinchedHomChainMapSimplex_linear, LinearSimplex.toLinearSimplex_toPinched]
    exact dgGluingPinchedPullbackSimplex_fst h _ _ e
  · apply (linearEquiv x₂ y₂ n.unop.len).injective
    change toLinearSimplex (pinchedHomChainMapSimplex b _) = toLinearSimplex t
    rw [pinchedHomChainMapSimplex_linear, LinearSimplex.toLinearSimplex_toPinched]
    exact dgGluingPinchedPullbackSimplex_snd h _ _ e

end SerrePositivity.InfinityCategories
