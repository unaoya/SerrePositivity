module
public import SerrePositivity.InfinityCategories.F1.Transport.PrismLiftSpace
public import SerrePositivity.InfinityCategories.F1B.Cofinality.CofinalFunctorVertices
/-!
概要：指定初期図式と指定全底を持つ実屋根評価 prism の全高次空間を構成する。
方針：底上の関手空間の始端制限の fiber を取り、その trivial Kan fibration 性を使う。
規約：元・底・パラメータの充填性や有限性は不要。使われ方：相対評価の全境界充填。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
/-- 指定初期図式と同じ全底を持つ全実 prism の空間。 -/
def roofEvaluationLiftSpace {K E B : SSet.{u}} (p : E ⟶ B) (a : K ⟶ E)
    (γ : (Δ[1] : SSet.{u}) ⊗ K ⟶ B) (hγ : a ≫ p = prismEndpoint 0 K ≫ γ) : SSet.{u} :=
  vertexFiber (cofinalFunctorPre p γ (prismEndpoint 0 K))
    (cofinalFunctorVertex p (prismEndpoint 0 K ≫ γ) a hγ)
/-- 全実評価 prism の空間は、任意次元の境界を充填する可縮 Kan 複体。 -/
lemma roofEvaluationLiftSpace_isContractibleKan {K E B : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (a : K ⟶ E)
    (γ : (Δ[1] : SSet.{u}) ⊗ K ⟶ B) (hγ : a ≫ p = prismEndpoint 0 K ≫ γ) :
    IsContractibleKan (roofEvaluationLiftSpace p a γ hγ) := by
  have := cofinalFunctorPre_trivialKanFibration p γ (prismEndpoint 0 K)
    (prismEndpoint_zero_leftAnodyne K)
  exact vertexFiber_isContractibleKan _ _
/-- 全選択空間上の、実評価 prism の関手空間への普遍族。 -/
def roofEvaluationLiftCurry {K E B : SSet.{u}} (p : E ⟶ B) (a : K ⟶ E)
    (γ : (Δ[1] : SSet.{u}) ⊗ K ⟶ B) (hγ : a ≫ p = prismEndpoint 0 K ≫ γ) :
    roofEvaluationLiftSpace p a γ hγ ⟶ (ihom ((Δ[1] : SSet.{u}) ⊗ K)).obj E :=
  vertexFiberι (cofinalFunctorPre p γ (prismEndpoint 0 K))
    (cofinalFunctorVertex p (prismEndpoint 0 K ≫ γ) a hγ) ≫
      vertexFiberι ((ihom ((Δ[1] : SSet.{u}) ⊗ K)).map p) (functorVertex γ)
/-- 普遍実評価族の全底は、指定した同じ底の図式に厳密に定値。 -/
lemma roofEvaluationLiftCurry_over {K E B : SSet.{u}} (p : E ⟶ B) (a : K ⟶ E)
    (γ : (Δ[1] : SSet.{u}) ⊗ K ⟶ B) (hγ : a ≫ p = prismEndpoint 0 K ≫ γ) :
    roofEvaluationLiftCurry p a γ hγ ≫ (ihom ((Δ[1] : SSet.{u}) ⊗ K)).map p =
      SSet.const (functorVertex γ) := by
  rw [roofEvaluationLiftCurry, Category.assoc, vertexFiberι_comp, SSet.comp_const]
/-- 普遍実評価族の始端は、指定初期図式に全選択空間上で厳密に定値。 -/
lemma roofEvaluationLiftCurry_start {K E B : SSet.{u}} (p : E ⟶ B) (a : K ⟶ E)
    (γ : (Δ[1] : SSet.{u}) ⊗ K ⟶ B) (hγ : a ≫ p = prismEndpoint 0 K ≫ γ) :
    roofEvaluationLiftCurry p a γ hγ ≫ (pre (prismEndpoint 0 K)).app E =
      SSet.const (functorVertex a) := by
  rw [roofEvaluationLiftCurry, Category.assoc, ← cofinalFunctorPre_ι, ← Category.assoc,
    vertexFiberι_comp, SSet.const_comp]
  rfl
end SerrePositivity.InfinityCategories
