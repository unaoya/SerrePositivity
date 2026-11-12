module
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.EdgeRepresentativeLift
public import SerrePositivity.KST.SConstruction.SpecifiedTwoTrianglePrism

/-!
概要：元二単体比較の同じ類を保ち、共有対角を指定した全比較へ合わせる。
方針：対角制限の内ファイブレーションに既存の辺代表修正を使う。
規約：元二単体・全比較の類を保持。使われ方：実右面の上下比較の接合。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet InfinityCategories
open scoped Simplicial
private lemma specifiedTriangleEdgeYoneda {A X : SSet.{u}} (p : A ⟶ X)
    (s : A _⦋1⦌) (t : X _⦋1⦌) (h : p.app (Opposite.op ⦋1⦌) s = t) :
    SSet.yonedaEquiv.symm s ≫ p = SSet.yonedaEquiv.symm t := by
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact h
/-- 概要：元全三角形比較の類を保ちながら、同じ類の指定対角を厳密に回収する。
方針：既存の内ファイブレーションの辺代表修正を適用する。
規約：元両二単体を保持。使われ方：上下二胞体の全比較の貼り合わせ。 -/
lemma exists_specifiedTriangleDiagonalRepresentative {X : SSet.{u}} [Quasicategory X]
    {f g : (Δ[2] : SSet.{u}) ⟶ X} (H₀ : SSet.Homotopy f g)
    (T : SSet.Homotopy (stdSimplex.δ (1 : Fin 3) ≫ f)
      (stdSimplex.δ (1 : Fin 3) ≫ g))
    (hc₀ : SSet.Truncated.HomotopyCategory.homMk
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H₀).map
          ((truncation 2).map ((pre (stdSimplex.δ (1 : Fin 3))).app X))) =
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy T)) :
    ∃ H : SSet.Homotopy f g,
      (stdSimplex.δ (1 : Fin 3) ▷ (Δ[1] : SSet.{u})) ≫ H.h = T.h ∧
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H) =
        SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H₀) := by
  let p := (pre (stdSimplex.δ (1 : Fin 3))).app X
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H₀
  let t := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy T
  obtain ⟨e', he', hc⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.exists_kanEdgeRepresentative_lift p e t hc₀
  let H := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge e'
  have hH : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H = e' := by
    apply SSet.Truncated.Edge.ext
    change SSet.yonedaEquiv (curry (uncurry (SSet.yonedaEquiv.symm e'.edge))) = e'.edge
    rw [curry_uncurry]
    exact Equiv.apply_symm_apply SSet.yonedaEquiv _
  have hp : SSet.yonedaEquiv.symm e'.edge ≫ p = SSet.yonedaEquiv.symm t.edge :=
    specifiedTriangleEdgeYoneda p
      (show ((ihom (Δ[2] : SSet.{u})).obj X) _⦋1⦌ from e'.edge)
      (show ((ihom (Δ[1] : SSet.{u})).obj X) _⦋1⦌ from t.edge) he'
  refine ⟨H, ?_, ?_⟩
  · apply curry_injective
    calc
      curry ((stdSimplex.δ (1 : Fin 3) ▷ (Δ[1] : SSet.{u})) ≫ H.h) =
          curry H.h ≫ p := (curry_pre_app _ _).symm
      _ = SSet.yonedaEquiv.symm e'.edge ≫ p := by
        change curry (uncurry (SSet.yonedaEquiv.symm e'.edge)) ≫ p = _
        rw [curry_uncurry]
      _ = SSet.yonedaEquiv.symm t.edge := hp
      _ = curry T.h := Equiv.symm_apply_apply SSet.yonedaEquiv _
  · rw [hH]
    exact hc
end SerrePositivity.KST.SConstruction
