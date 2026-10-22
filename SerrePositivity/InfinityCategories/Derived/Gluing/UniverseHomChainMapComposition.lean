module
public import SerrePositivity.InfinityCategories.Derived.Gluing.UniverseHomChainMap
public import SerrePositivity.InfinityCategories.Derived.PinchedHomChainMap

/-! 一般宇宙間の Hom 鎖写像の作用は、同じ対象宇宙内での前後合成を保存する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w r
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerve.PinchedHom
variable {R : Type u} [CommRing R] {C : Type v} {D E : Type w}
  [DGCategory R C] [DGCategory R D] [DGCategory R E]
  {x y : C} {x' y' : D} {x'' y'' : E}

lemma dgGluingUniverseHomChainMap_post
    (φ : homObject R C x y ⟶ homObject R D x' y')
    (ψ : homObject R D x' y' ⟶ homObject R E x'' y'') :
    dgGluingUniverseHomChainMap.{u, v, w, r} φ ≫
      (SSet.uliftFunctor.{max v r, max u w}).map (pinchedHomChainMap ψ) =
      dgGluingUniverseHomChainMap.{u, v, w, r} (φ ≫ ψ) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  apply ULift.ext
  apply (linearEquiv x'' y'' n.unop.len).injective
  change toLinearSimplex (pinchedHomChainMapSimplex ψ
    ((dgGluingUniverseHomChainMap.{u, v, w, r} φ).app n s).down) = _
  change toLinearSimplex (pinchedHomChainMapSimplex ψ
    ((dgGluingUniverseHomChainMap.{u, v, w, r} φ).app n s).down) =
      toLinearSimplex ((pinchedLinearSimplexMap (φ ≫ ψ) (toLinearSimplex s.down)).toPinched)
  rw [pinchedHomChainMapSimplex_linear, dgGluingUniverseHomChainMap_linear,
    LinearSimplex.toLinearSimplex_toPinched]
  apply Subtype.ext
  rfl

variable {T : Type v} [DGCategory R T] {a b : T}

lemma dgGluingUniverseHomChainMap_pre
    (φ : homObject R C x y ⟶ homObject R T a b)
    (ψ : homObject R T a b ⟶ homObject R D x' y') :
    (SSet.uliftFunctor.{max w r, max u v}).map (pinchedHomChainMap φ) ≫
      dgGluingUniverseHomChainMap.{u, v, w, r} ψ =
      dgGluingUniverseHomChainMap.{u, v, w, r} (φ ≫ ψ) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  apply ULift.ext
  apply (linearEquiv x' y' n.unop.len).injective
  change toLinearSimplex ((pinchedLinearSimplexMap ψ
      (toLinearSimplex (pinchedHomChainMapSimplex φ s.down))).toPinched) =
    toLinearSimplex ((pinchedLinearSimplexMap (φ ≫ ψ) (toLinearSimplex s.down)).toPinched)
  rw [LinearSimplex.toLinearSimplex_toPinched, LinearSimplex.toLinearSimplex_toPinched,
    pinchedHomChainMapSimplex_linear]
  apply Subtype.ext
  rfl

end SerrePositivity.InfinityCategories
