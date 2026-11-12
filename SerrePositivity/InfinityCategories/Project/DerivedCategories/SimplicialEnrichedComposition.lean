module
public import Mathlib.AlgebraicTopology.Quasicategory.StrictBicategory
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes
/-!
概要：単体集合の enrichment の合成を内部 Hom の実合成へ同定する。
方針：実辺と全次数の成分を使って同じ作用を照合する。
規約：元の指定関手と射を保持する。使われ方：一般 cell 合成の単位 coherence。
-/
@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet MonoidalClosed
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
lemma simplicialEnrichedComp_eq_internalComp (X Y Z : SSet.{u}) :
    eComp SSet X Y Z = MonoidalClosed.comp X Y Z := by
  ext n a
  rcases a with ⟨f, g⟩
  apply CategoryTheory.Functor.functorHom_ext
  intro m φ
  ext x
  change (g.app m φ) (f.app m φ x) = _
  dsimp +instances [eComp, Functor.HomObj.comp, MonoidalClosed.comp,
    MonoidalClosed.compTranspose, MonoidalClosed.curry,
    ihom, FunctorToTypes.rightAdj, Adjunction.homEquiv, ihom.adjunction, ihom.ev,
    FunctorToTypes.closed, FunctorToTypes.adj,
    FunctorToTypes.functorHomEquiv, Functor.functorHomEquiv, Functor.homObjEquiv]
  change (g.app m φ) (f.app m φ x) =
    (g.app m (φ ≫ 𝟙 m)) (f.app m (φ ≫ 𝟙 m) x)
  simp only [Category.comp_id]

end
end SerrePositivity.InfinityCategories.Project.DerivedCategories
