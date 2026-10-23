module
public import SerrePositivity.InfinityCategories.Derived.PinchedLinearChainMap
public import SerrePositivity.InfinityCategories.F1.Universe.PinchedHom

/-! 対象宇宙の異なる二つの実 Hom 空間に、同じ Hom 鎖写像を作用させる。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w r
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerve.PinchedHom
open scoped Simplicial
variable {R : Type u} [CommRing R] {C : Type v} {D : Type w}
  [DGCategory R C] [DGCategory R D] {x y : C} {x' y' : D}

def dgGluingUniverseHomChainMap
    (φ : homObject R C x y ⟶ homObject R D x' y') :
    (SSet.uliftFunctor.{max w r, max u v}).obj (DGNerve.pinchedHom R C x y) ⟶
      (SSet.uliftFunctor.{max v r, max u w}).obj (DGNerve.pinchedHom R D x' y') where
  app _ := ↾fun s => ULift.up ((pinchedLinearSimplexMap φ (toLinearSimplex s.down)).toPinched)
  naturality {m n} α := by
    apply ConcreteCategory.hom_ext
    intro s
    apply ULift.ext
    apply (linearEquiv x' y' n.unop.len).injective
    change toLinearSimplex ((pinchedLinearSimplexMap φ
        (toLinearSimplex (s.down.pullback α.unop))).toPinched) =
      toLinearSimplex (((pinchedLinearSimplexMap φ
        (toLinearSimplex s.down)).toPinched).pullback α.unop)
    simp only [LinearSimplex.toLinearSimplex_toPinched, toLinearSimplex_pullback,
      pinchedLinearSimplexMap_pullback]

lemma dgGluingUniverseHomChainMap_linear
    (φ : homObject R C x y ⟶ homObject R D x' y') {n : ℕ}
    (s : ((SSet.uliftFunctor.{max w r, max u v}).obj
      (DGNerve.pinchedHom R C x y)) _⦋n⦌) :
    toLinearSimplex ((dgGluingUniverseHomChainMap.{u, v, w, r} φ).app
      (Opposite.op ⦋n⦌) s).down = pinchedLinearSimplexMap φ (toLinearSimplex s.down) :=
  LinearSimplex.toLinearSimplex_toPinched _

end SerrePositivity.InfinityCategories
