module

public import SerrePositivity.InfinityCategories.Core.CocartesianPathVertices

/-!
概要：cocartesian な path の始点と基底への射の trivial Kan fibration 性。
方針：零次元は辺の持ち上げ、正次元は cocartesian な prism の相対充填を使う。
規約：元・標的の quasicategory 性は仮定しない。
使われ方：Kerodon §5.1.4・§7.1.5 の指定部分を固定した coherent な輸送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：cocartesian な path から始点と基底の path への射は trivial Kan fibration。
方針：境界の path を prism に直して始点の単体と共に持ち上げ、全部分複体へ戻す。
規約：cocartesian fibration の仮定のみで quasicategory 性は不要。
使われ方：Kerodon §5.1.4・§7.1.5 の輸送の coherent な選択。 -/
instance cocartesianPathSpaceSource_trivialKanFibration {E B : SSet.{u}}
    (p : E ⟶ B) [CocartesianHornFibration p] :
    TrivialKanFibration (cocartesianPathSpaceSource p) := by
  rw [trivialKanFibration_iff_boundary]
  intro n
  constructor
  intro a b sq
  cases n with
  | zero =>
    obtain ⟨t, ht⟩ := cocartesianPathSpaceSource_surjective p (SSet.yonedaEquiv b)
    refine CommSq.HasLift.mk' {
      l := SSet.yonedaEquiv.symm t
      fac_left := boundary.hom_ext₀
      fac_right := ?_ }
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply, ht]
  | succ n =>
    let evB := evaluateFunctorAt (Y := B) (stdSimplex.obj₀Equiv.symm (0 : Fin 2))
    let H := uncurry (a ≫ cocartesianPathSpaceι p)
    let β := uncurry (b ≫ pullback.snd p evB)
    let F₀ := b ≫ pullback.fst p evB
    have hC : curry H = a ≫ cocartesianPathSpaceι p := curry_uncurry _
    have h₀ : (boundary (n + 1)).ι ≫ F₀ =
        prismEndpoint 0 (boundary (n + 1) : SSet.{u}) ≫ H := by
      rw [← curry_evaluateFunctorAt_interval, hC]
      have hh := congrArg (fun t ↦ t ≫ pullback.fst p evB) sq.w
      dsimp only [evB] at hh
      simpa only [Category.assoc, cocartesianPathSpaceSource_fst, F₀] using hh.symm
    have hHp : H ≫ p = (Δ[1] ◁ (boundary (n + 1)).ι) ≫ β := by
      have hh := congrArg (fun t ↦ t ≫ pullback.snd p evB) sq.w
      dsimp only [evB] at hh
      simp only [Category.assoc, cocartesianPathSpaceSource_snd] at hh
      rw [← Category.assoc a (cocartesianPathSpaceι p)] at hh
      have hu := congrArg uncurry hh
      rw [uncurry_natural_right, uncurry_natural_left] at hu
      exact hu
    have hF₀p : F₀ ≫ p = prismEndpoint 0 Δ[n + 1] ≫ β := by
      rw [← curry_evaluateFunctorAt_interval]
      dsimp [F₀, β]
      rw [curry_uncurry, Category.assoc, pullback.condition]
      simp only [evB, Category.assoc]
    have hH : HasCocartesianHornLifting p (edgeOfSimplex
        (H.app (Opposite.op ⦋1⦌) (prismBoundaryFirstVerticalEdge n))) := by
      let x : (boundary (n + 1) : SSet.{u}) _⦋0⦌ :=
        ⟨stdSimplex.obj₀Equiv.symm 0, vertex_mem_boundary n 0⟩
      have hx := fullSubcomplexOnVertices_vertex (a.app (Opposite.op ⦋0⦌) x)
      change IsCocartesianPathVertex p ((a ≫ cocartesianPathSpaceι p).app (Opposite.op ⦋0⦌) x) at hx
      rw [← hC] at hx
      unfold IsCocartesianPathVertex at hx
      change HasCocartesianHornLifting p (edgeOfSimplex (intervalFunctorVertexEdge
        ((curry H).app (Opposite.op ⦋0⦌) x))) at hx
      rw [intervalFunctorVertexEdge_curry] at hx
      exact hx
    obtain ⟨F, hF, hF₀, hFp⟩ := prism_lift_boundary_with_endpoint p n H F₀ β h₀ hHp hF₀p hH
    have hc : (boundary (n + 1)).ι ≫ curry F = a ≫ cocartesianPathSpaceι p := by
      rw [← curry_natural_left, hF, hC]
    have hv : ∀ v : (Δ[n + 1] : SSet.{u}) _⦋0⦌,
        IsCocartesianPathVertex p ((curry F).app (Opposite.op ⦋0⦌) v) := by
      intro v
      let x : (boundary (n + 1) : SSet.{u}) _⦋0⦌ :=
        ⟨v, by
          have h := vertex_mem_boundary.{u} n (stdSimplex.obj₀Equiv.{u} v)
          rw [Equiv.symm_apply_apply] at h
          exact h⟩
      have hx := fullSubcomplexOnVertices_vertex (a.app (Opposite.op ⦋0⦌) x)
      have he := ConcreteCategory.congr_hom (NatTrans.congr_app hc (Opposite.op ⦋0⦌)) x
      change (curry F).app (Opposite.op ⦋0⦌) v = (a.app (Opposite.op ⦋0⦌) x).val at he
      exact he.symm ▸ hx
    let g := fullSubcomplexLift (IsCocartesianPathVertex p) (curry F) hv
    have hg : g ≫ cocartesianPathSpaceι p = curry F := fullSubcomplexLift_ι _ _ _
    refine CommSq.HasLift.mk' { l := g, fac_left := ?_, fac_right := ?_ }
    · haveI : Mono (cocartesianPathSpaceι p) := by unfold cocartesianPathSpaceι; infer_instance
      apply (cancel_mono (cocartesianPathSpaceι p)).1
      rw [Category.assoc, hg, hc]
    · apply pullback.hom_ext
      · simp only [Category.assoc, cocartesianPathSpaceSource_fst]
        rw [← Category.assoc, hg, curry_evaluateFunctorAt_interval, hF₀]
      · simp only [Category.assoc, cocartesianPathSpaceSource_snd]
        rw [← Category.assoc, hg]
        apply uncurry_injective
        rw [uncurry_natural_right, uncurry_curry, hFp]

end SerrePositivity.InfinityCategories
