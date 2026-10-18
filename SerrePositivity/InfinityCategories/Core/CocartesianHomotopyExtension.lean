module

public import SerrePositivity.InfinityCategories.Core.CocartesianPathLifting

/-!
概要：単射上の cocartesian な垂直辺を持つ輸送の相対延長。
方針：cocartesian な path の始点と基底への射の持ち上げを uncurry する。
規約：基底、始点、指定部分上の輸送をすべて厳密に固定する。
使われ方：Kerodon §5.1.4・§7.1.5 の相対終対象の prism の輸送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：単射上で指定した cocartesian な輸送は基底と始点を固定して全体へ延長できる。
方針：指定された輸送を全部分複体へ含め、始点と基底の pullback への trivial Kan fibration で持ち上げる。
規約：元・標的の quasicategory 性は不要。
使われ方：Kerodon §5.1.4・§7.1.5 の coherent な輸送の相対形。 -/
lemma cocartesianHomotopy_extend {A D E B : SSet.{u}} (p : E ⟶ B) [CocartesianHornFibration p]
    (i : A ⟶ D) [Mono i] (H : (Δ[1] : SSet.{u}) ⊗ A ⟶ E) (f : D ⟶ E)
    (β : (Δ[1] : SSet.{u}) ⊗ D ⟶ B)
    (h₀ : prismEndpoint 0 A ≫ H = i ≫ f)
    (hf : f ≫ p = prismEndpoint 0 D ≫ β)
    (hHp : H ≫ p = (Δ[1] ◁ i) ≫ β)
    (hH : ∀ x : A _⦋0⦌, HasCocartesianHornLifting p (edgeOfSimplex
      (H.app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), PinchedHom.constant x 1)))) :
    ∃ F : (Δ[1] : SSet.{u}) ⊗ D ⟶ E,
      (Δ[1] ◁ i) ≫ F = H ∧ prismEndpoint 0 D ≫ F = f ∧ F ≫ p = β ∧
      ∀ x : D _⦋0⦌, HasCocartesianHornLifting p (edgeOfSimplex
        (F.app (Opposite.op ⦋1⦌)
          (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), PinchedHom.constant x 1))) := by
  have hv : ∀ x, IsCocartesianPathVertex p ((curry H).app (Opposite.op ⦋0⦌) x) := by
    intro x
    unfold IsCocartesianPathVertex
    change HasCocartesianHornLifting p (edgeOfSimplex (intervalFunctorVertexEdge _))
    rw [intervalFunctorVertexEdge_curry]
    exact hH x
  let a := fullSubcomplexLift (IsCocartesianPathVertex p) (curry H) hv
  have ha : a ≫ cocartesianPathSpaceι p = curry H := fullSubcomplexLift_ι _ _ _
  let evB := evaluateFunctorAt (Y := B) (stdSimplex.obj₀Equiv.symm (0 : Fin 2))
  have hbase : f ≫ p = curry β ≫ evB := by
    rw [curry_evaluateFunctorAt_interval]
    exact hf
  let b := pullback.lift f (curry β) hbase
  have hw : a ≫ cocartesianPathSpaceSource p = i ≫ b := by
    apply pullback.hom_ext
    · dsimp only [b, evB]
      rw [Category.assoc, cocartesianPathSpaceSource_fst,
        ← Category.assoc, ha, curry_evaluateFunctorAt_interval, h₀,
        Category.assoc, pullback.lift_fst]
    · dsimp only [b, evB]
      rw [Category.assoc, cocartesianPathSpaceSource_snd,
        ← Category.assoc, ha, ← curry_natural_right, hHp, curry_natural_left,
        Category.assoc, pullback.lift_snd]
  have := TrivialKanFibration.mem (p := cocartesianPathSpaceSource p) i inferInstance
  let sq : CommSq a i (cocartesianPathSpaceSource p) b := ⟨hw⟩
  let F := uncurry (sq.lift ≫ cocartesianPathSpaceι p)
  have hC : curry F = sq.lift ≫ cocartesianPathSpaceι p := curry_uncurry _
  refine ⟨F, ?_, ?_, ?_, ?_⟩
  · apply curry_injective
    rw [curry_natural_left, hC, ← Category.assoc, sq.fac_left, ha]
  · rw [← curry_evaluateFunctorAt_interval, hC]
    have hh := congrArg (fun t ↦ t ≫ pullback.fst p evB) sq.fac_right
    dsimp only [evB, b] at hh
    simpa only [Category.assoc, cocartesianPathSpaceSource_fst, pullback.lift_fst] using hh
  · apply curry_injective
    rw [curry_natural_right, hC]
    have hh := congrArg (fun t ↦ t ≫ pullback.snd p evB) sq.fac_right
    dsimp only [evB, b] at hh
    simpa only [Category.assoc, cocartesianPathSpaceSource_snd, pullback.lift_snd] using hh
  · intro x
    have hx := fullSubcomplexOnVertices_vertex (sq.lift.app (Opposite.op ⦋0⦌) x)
    change IsCocartesianPathVertex p
      ((sq.lift ≫ cocartesianPathSpaceι p).app (Opposite.op ⦋0⦌) x) at hx
    rw [← hC] at hx
    unfold IsCocartesianPathVertex at hx
    change HasCocartesianHornLifting p (edgeOfSimplex (intervalFunctorVertexEdge _)) at hx
    rw [intervalFunctorVertexEdge_curry] at hx
    exact hx

end SerrePositivity.InfinityCategories
