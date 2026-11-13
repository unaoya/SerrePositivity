module
public import SerrePositivity.HomologicalAlgebra.UncurriedDiagramHomotopy
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.NormalizedIntervalHomEndpoints
/-!
概要：二重図式の指定ホモトピーを余単体方向にも自然な区間評価へ送る。
方針：積添字のA06を適用し、同じ成分を二重図式へ戻す。
規約：A07の証明分割。次数ごとにホモトピーを選び直さない。
使われ方：HA 1.2.4、指定余作用から単体的ホモトピーへの接続。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.HomologicalAlgebra
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable {A : Type (max u v)} [CommRing A] {J : Type v} [SmallCategory J]
local notation "D" => J ⥤ Complex A
local notation "I" => Functor.obj
  (liftedStandardSimplexParameter J ⋙ freeNegativeChainsDiagramFunctor A J) (SimplexCategory.mk 1)
local notation "EE" =>
  (Functor.obj (Functor.whiskeringRight SimplexCategory (J ⥤ Complex A)
    (CochainComplex (J ⥤ ModuleCat A) ℤ))
      (functorToComplexOfFunctors J (ModuleCat A) (ComplexShape.up ℤ)) ⋙
    functorToComplexOfFunctors SimplexCategory (J ⥤ ModuleCat A) (ComplexShape.up ℤ))
/-- 同じ全余単体ホモトピーを指定区間で評価した二重図式の射。 -/
def frameIntervalHom {F G : SimplexCategory ⥤ D} (f g : F ⟶ G)
    (h : Homotopy ((EE).map f) ((EE).map g)) :
    F ⊗ (Functor.const SimplexCategory).obj I ⟶ G := by
  let k := normalizedIntervalHom (Functor.uncurry.map f) (Functor.uncurry.map g)
    (uncurriedDiagramHomotopy (ComplexShape.up ℤ) f g h)
  have hm (W : SimplicialObject (ModuleCat A)) :
      AlgebraicTopology.NormalizedMooreComplex.map (𝟙 W) = 𝟙 _ :=
    (AlgebraicTopology.normalizedMooreComplex (ModuleCat A)).map_id W
  exact {
    app n := {
      app j := k.app (n, j)
      naturality := by
        intro i j t
        have hk := k.naturality ((𝟙 n, t) : (n, i) ⟶ (n, j))
        simpa [Functor.uncurry, freeNegativeChainsDiagram, freeNegativeChainsMap,
          freeNegativeChainsDiagramFunctor, liftedStandardSimplexParameter, SSet.uliftFunctor] using hk }
    naturality := by
      intro n m t
      apply NatTrans.ext
      funext j
      have hk := k.naturality ((t, 𝟙 j) : (n, j) ⟶ (m, j))
      simp [Functor.uncurry, freeNegativeChainsDiagram, freeNegativeChainsMap,
        freeNegativeChainsDiagramFunctor, liftedStandardSimplexParameter, SSet.uliftFunctor] at hk
      erw [hm, extendMap_id, tensorHom_id] at hk
      exact hk }
/-- 元の余単体ホモトピー区間評価の端点は元の二射。 -/
theorem frameIntervalHom_endpoints {F G : SimplexCategory ⥤ D} (f g : F ⟶ G)
    (h : Homotopy ((EE).map f) ((EE).map g)) :
    (ρ_ F).inv ≫ (𝟙 F ⊗ₘ (Functor.const SimplexCategory).map
      (normalizedIntervalEndpoint A J 0)) ≫ frameIntervalHom f g h = f ∧
    (ρ_ F).inv ≫ (𝟙 F ⊗ₘ (Functor.const SimplexCategory).map
      (normalizedIntervalEndpoint A J 1)) ≫ frameIntervalHom f g h = g := by
  have hk := normalizedIntervalHom_endpoints (Functor.uncurry.map f) (Functor.uncurry.map g)
    (uncurriedDiagramHomotopy (ComplexShape.up ℤ) f g h)
  constructor
  · apply NatTrans.ext
    funext n
    apply NatTrans.ext
    funext j
    simpa [frameIntervalHom, normalizedIntervalEndpoint, Functor.uncurry] using NatTrans.congr_app hk.1 (n, j)
  · apply NatTrans.ext
    funext n
    apply NatTrans.ext
    funext j
    simpa [frameIntervalHom, normalizedIntervalEndpoint, Functor.uncurry] using NatTrans.congr_app hk.2 (n, j)
end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
