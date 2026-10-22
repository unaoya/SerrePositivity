module

public import SerrePositivity.InfinityCategories.F2.Ind.TerminalCarrierPositiveLift
public import SerrePositivity.InfinityCategories.Core.TrivialFibrationEquivalence

/-!
概要：終頂点を指定した全鎖の実現空間から nerve への射影は trivial Kan fibration。
方針：正次元は終頂点による境界充填、零次元は指定頂点そのものを持ち上げに使う。
規約：quasicategory 性を追加仮定にしない。
使われ方：元の指定頂点を保つ全鎖の整合的な実現。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {I : Type u} [Preorder I] {X : SSet.{u}}

/-- 零次元の持ち上げは同じ添字に指定した元の頂点。 -/
lemma terminalCarrier_exists_zero_lift (A : I → X.Subcomplex)
    (t : ∀ i, (A i).toSSet _⦋0⦌) (q : (Δ[0] : SSet.{u}) ⟶ nerve I) :
    ∃ G : (Δ[0] : SSet.{u}) ⟶ (terminalCarrier A (fun i => (t i).val)).toSSet,
      G ≫ terminalCarrierProjection A (fun i => (t i).val) = q := by
  let F : (Δ[0] : SSet.{u}) ⟶ X :=
    SSet.yonedaEquiv.symm (t ((SSet.yonedaEquiv q).obj 0)).val
  have hp : terminalCarrierCondition A (fun i => (t i).val)
      (SSet.yonedaEquiv F) (SSet.yonedaEquiv q) := by
    rw [show SSet.yonedaEquiv F = (t ((SSet.yonedaEquiv q).obj 0)).val from
      SSet.yonedaEquiv.apply_symm_apply _]
    exact terminalCarrierCondition_zero A _ _ (t _).property
  exact ⟨terminalCarrierSimplex F q hp, terminalCarrierSimplex_projection F q hp⟩

/-- 同じ射影は全境界を持ち上げる trivial Kan fibration。 -/
lemma terminalCarrierProjection_trivialKanFibration (A : I → X.Subcomplex) (hA : Monotone A)
    (t : ∀ i, (A i).toSSet _⦋0⦌) (ht : ∀ i, IsTerminalVertex (t i)) :
    TrivialKanFibration (terminalCarrierProjection A (fun i => (t i).val)) := by
  apply (trivialKanFibration_iff_boundary _).mpr
  intro n
  constructor
  intro b q sq
  cases n with
  | zero =>
    obtain ⟨G, hG⟩ := terminalCarrier_exists_zero_lift A t q
    exact CommSq.HasLift.mk' { l := G, fac_left := boundary.hom_ext₀, fac_right := hG }
  | succ n =>
    obtain ⟨G, hG, hGq⟩ := terminalCarrier_exists_positive_lift A hA t ht n b q sq.w
    exact CommSq.HasLift.mk' { l := G, fac_left := hG, fac_right := hGq }

end SerrePositivity.InfinityCategories.F2.Ind
