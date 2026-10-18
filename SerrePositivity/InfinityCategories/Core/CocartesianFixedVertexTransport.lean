module

public import SerrePositivity.InfinityCategories.Core.CocartesianHomotopyExtension
public import SerrePositivity.InfinityCategories.Core.PrismLastContraction

/-!
概要：一つの頂点を固定した cocartesian な輸送。
方針：指定頂点上で恒等辺の定値 prism を与え、単射上の輸送の延長を使う。
規約：基底の prism もその頂点上で定値とする。
使われ方：Kerodon §7.1.5 の終対象を固定した fiber への輸送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：基底の prism が一頂点上で定値なら、その頂点を固定した cocartesian な輸送が存在する。
方針：指定頂点上の恒等辺が cocartesian なことを用い、単射上の輸送を延長する。
規約：元・標的は quasicategory、p は cocartesian fibration。
使われ方：Kerodon §7.1.5 の終対象の頂点を固定した境界の輸送。 -/
lemma cocartesianHomotopy_exists_fixed_vertex {A E B : SSet.{u}} [Quasicategory E] [Quasicategory B]
    (p : E ⟶ B) [CocartesianHornFibration p]
    (i : (Δ[0] : SSet.{u}) ⟶ A) [Mono i] (f : A ⟶ E) (x : E _⦋0⦌)
    (hix : i ≫ f = SSet.yonedaEquiv.symm x)
    (β : (Δ[1] : SSet.{u}) ⊗ A ⟶ B)
    (hβ₀ : f ≫ p = prismEndpoint 0 A ≫ β)
    (hβi : (Δ[1] ◁ i) ≫ β = SSet.const (p.app (Opposite.op ⦋0⦌) x)) :
    ∃ H : (Δ[1] : SSet.{u}) ⊗ A ⟶ E,
      (Δ[1] ◁ i) ≫ H = SSet.const x ∧ prismEndpoint 0 A ≫ H = f ∧ H ≫ p = β ∧
      ∀ y : A _⦋0⦌, HasCocartesianHornLifting p (edgeOfSimplex
        (H.app (Opposite.op ⦋1⦌)
          (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), PinchedHom.constant y 1))) := by
  have h₀ : prismEndpoint 0 (Δ[0] : SSet.{u}) ≫ SSet.const x = i ≫ f := by
    rw [SSet.comp_const, hix, SSet.yonedaEquiv_symm_zero]
  have hHp : (SSet.const x : (Δ[1] : SSet.{u}) ⊗ Δ[0] ⟶ E) ≫ p =
      (Δ[1] ◁ i) ≫ β := by
    rw [SSet.const_comp, hβi]
  have hH (y : (Δ[0] : SSet.{u}) _⦋0⦌) : HasCocartesianHornLifting p (edgeOfSimplex
      ((SSet.const x : (Δ[1] : SSet.{u}) ⊗ Δ[0] ⟶ E).app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), PinchedHom.constant y 1))) := by
    have hi := isEquivalencePathVertex_const x
    unfold IsEquivalencePathVertex at hi
    rw [intervalFunctorVertexEdge_functorVertex] at hi
    exact hi.hasCocartesianHornLifting p
  exact cocartesianHomotopy_extend p i (SSet.const x) f β h₀ hβ₀ hHp hH

end SerrePositivity.InfinityCategories
