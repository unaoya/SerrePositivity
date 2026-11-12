module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeExtensionFiberWitnessRestriction
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.FiberTransportFamily
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PrismLiftSpace

/-!
概要：元の全輸送の始点を実 prism の頂点で固定し、既存 endpointIso の指定値を回収する。
方針：零単体の係数を保つ同じ制限で、元の二つの実 prism を比較する。
規約：prism・実終点・比較を保持。使われ方：全三角形の辺比較を元の輸送比較へ戻す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {E B K L : SSet.{u}} (p : E ⟶ B) [LeftFibration p] {a b : B _⦋0⦌}
  (f : K ⟶ vertexFiber p a) (γ : (Δ[1] : SSet.{u}) ⊗ L ⟶ B)
  (h₁ : prismEndpoint 1 L ≫ γ = SSet.const b)
  (T U : FiberTransportFamily (b := b) p f γ)
local notation "β" => (Δ[1] ◁ snd K L) ≫ γ
local notation "v" => fst K L ≫ f ≫ vertexFiberι p a

/-- 元の全輸送の二実 prism を、同じ実始点・同じ実 fiber 終点で比較する指定値。 -/
def fiberTransportFamilyPrismComparison : FunctorIso T.endpoint U.endpoint :=
  relativeExtensionFiberEndpoint_witnessIso p β (prismEndpoint 0 (K ⊗ L))
    (prismEndpoint_zero_leftAnodyne (K ⊗ L)) v
    (by rw [← T.start, Category.assoc, T.over_base])
    (prismEndpoint 1 (K ⊗ L)) b (fiberTransportFamily_base_endpoint 1 γ b h₁)
    T.prism U.prism T.over_base U.over_base T.start U.start T.endpoint U.endpoint T.finish U.finish

/-- 元の実 prism の始点固定で比較しても、同じ endpointIso の指定値を厳密に回収する。 -/
lemma fiberTransportFamilyPrismComparison_eq_endpointIso :
    fiberTransportFamilyPrismComparison p f γ h₁ T U = T.endpointIso p f γ h₁ U := by
  have hs : (scaffoldFirstVertex 1 ▷ (K ⊗ L)) ≫ 𝟙 ((Δ[1] : SSet.{u}) ⊗ (K ⊗ L)) =
      snd (Δ[0] : SSet.{u}) (K ⊗ L) ≫ prismEndpoint 0 (K ⊗ L) := by
    rw [Category.comp_id, scaffoldFirstVertex_whiskerRight]
    rfl
  have hv : v ≫ p = prismEndpoint 0 (K ⊗ L) ≫ β := by
    rw [← T.start, Category.assoc, T.over_base]
  have hr := relativeExtensionFiberEndpoint_witnessIso_restriction p β
    (prismEndpoint 0 (K ⊗ L)) (prismEndpoint_zero_leftAnodyne (K ⊗ L)) v hv
    (𝟙 ((Δ[1] : SSet.{u}) ⊗ (K ⊗ L))) (snd (Δ[0] : SSet.{u}) (K ⊗ L))
    (scaffoldFirstVertex 1 ▷ (K ⊗ L)) (simplexPrismFirstVertex_leftAnodyne 1 (K ⊗ L)) hs
    (prismEndpoint 1 (K ⊗ L)) (prismEndpoint 1 (K ⊗ L)) (Category.comp_id _)
    b (fiberTransportFamily_base_endpoint 1 γ b h₁)
    T.prism U.prism T.over_base U.over_base T.start U.start T.endpoint U.endpoint T.finish U.finish
  simp only [Category.id_comp] at hr
  exact hr

end SerrePositivity.InfinityCategories.F2
