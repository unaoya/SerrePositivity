module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePath
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.PrismContraction
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.ArrowEndpointPair
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.FiberwiseIntervalKanComparison

/-!
概要：anodyne な部分上の指定ホモトピーを、指定した二つの全体射の比較へ延長する。
方針：指定円柱を curry し、Kan な両端評価へ持ち上げる。
規約：部分円柱を全単体で厳密に保持する。
使われ方：連続 Kan 置換後にも元の輸送円柱を失わない比較。

対応節は Kerodon 3.1（Tag 00SZ）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open HomotopicalAlgebra SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes

/-- 概要：指定部分ホモトピーを、両端を指定した全体ホモトピーへ延長できる。
方針：anodyne 射に対する両端評価の右持ち上げ性を使う。
規約：部分円柱は厳密に一致。使われ方：Kan 置換の全円柱を保つホモトピーの延長。 -/
lemma anodyne_homotopy_extension {A K X : SSet.{u}} [KanComplex X]
    (i : A ⟶ K) (hi : anodyneExtensions i) (f g : K ⟶ X)
    (H : SSet.Homotopy (i ≫ f) (i ≫ g)) :
    ∃ L : SSet.Homotopy f g, (i ▷ (Δ[1] : SSet.{u})) ≫ L.h = H.h := by
  have := hi (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.arrowEndpointPair X)
    (by rw [← HomotopicalAlgebra.fibration_iff]; infer_instance)
  let a := curry ((β_ (Δ[1] : SSet.{u}) A).hom ≫ H.h)
  have sq : CommSq a i (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.arrowEndpointPair X) (lift f g) := ⟨by
    apply CartesianMonoidalCategory.hom_ext
    · change a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 0) = i ≫ f
      dsimp only [a]
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval]
      exact H.h₀
    · change a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 1) = i ≫ g
      dsimp only [a]
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval]
      exact H.h₁⟩
  let R := (β_ K (Δ[1] : SSet.{u})).hom ≫ uncurry sq.lift
  have hzero : SSet.ι₀ ≫ R = f := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ≫ uncurry sq.lift = f
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval, curry_uncurry]
    exact congrArg (fun r ↦ r ≫ fst X X) sq.fac_right
  have hone : SSet.ι₁ ≫ R = g := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K ≫ uncurry sq.lift = g
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval, curry_uncurry]
    exact congrArg (fun r ↦ r ≫ snd X X) sq.fac_right
  refine ⟨⟨R, hzero, hone, ?_⟩, ?_⟩
  · apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property
  · change (i ▷ (Δ[1] : SSet.{u})) ≫ R = _
    dsimp only [R]
    rw [← Category.assoc, BraidedCategory.braiding_naturality_left, Category.assoc,
      ← uncurry_natural_left, sq.fac_left]
    dsimp only [a]
    rw [uncurry_curry, ← Category.assoc, SymmetricCategory.symmetry, Category.id_comp]

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
