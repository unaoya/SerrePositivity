module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FiberTransportFamilyRightPrism
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PrismLiftSpace

/-!
概要：元の二つの全輸送を、右結合の同じ prism 延長空間で比較する。
方針：元の底・始点・実終点を保つ相対延長の既存の指定比較を使う。
規約：prism と fiber 終点を選び直さない。使われ方：unstraightening の指定比較との照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の底の全区間族の右結合表示。 -/
def fiberTransportFamilyRightBase {B L : SSet.{u}} (K : SSet.{u})
    (γ : (Δ[1] : SSet.{u}) ⊗ L ⟶ B) : ((Δ[1] : SSet.{u}) ⊗ K) ⊗ L ⟶ B :=
  (α_ Δ[1] K L).hom ≫ (Δ[1] ◁ snd K L) ≫ γ

variable {E B K L : SSet.{u}} (p : E ⟶ B) {a b : B _⦋0⦌}
  (f : K ⟶ vertexFiber p a) (γ : (Δ[1] : SSet.{u}) ⊗ L ⟶ B)
local notation "i" => prismEndpoint 0 K ▷ L
local notation "v" => fst K L ≫ f ≫ vertexFiberι p a

/-- 元の右結合 prism の始点は同じ右結合の底を厳密に被覆する。 -/
lemma fiberTransportFamilyRightComparison_initial
    (T : FiberTransportFamily (b := b) p f γ) :
    (fst K L ≫ f ≫ vertexFiberι p a) ≫ p = i ≫ fiberTransportFamilyRightBase K γ := by
  rw [← fiberTransportFamilyRightPrism_source T, Category.assoc,
    fiberTransportFamilyRightPrism_projection]
  rfl

/-- 元の右結合 prism の終点の底は、元の終点の一点そのもの。 -/
lemma fiberTransportFamilyRightComparison_final
    (h₁ : prismEndpoint 1 L ≫ γ = SSet.const b) :
    (prismEndpoint 1 K ▷ L) ≫ fiberTransportFamilyRightBase K γ = SSet.const b := by
  change prismEndpoint 1 (K ⊗ L) ≫ (Δ[1] ◁ snd K L) ≫ γ = _
  exact fiberTransportFamily_base_endpoint 1 γ b h₁

/-- 元の二輸送の右結合 prism の、元の fiber 終点間の指定比較。 -/
def fiberTransportFamilyRightComparison [LeftFibration p]
    (h₁ : prismEndpoint 1 L ≫ γ = SSet.const b)
    (T U : FiberTransportFamily (b := b) p f γ) : FunctorIso T.endpoint U.endpoint :=
  relativeExtensionFiberEndpoint_witnessIso p (fiberTransportFamilyRightBase K γ) i
    (leftAnodyneExtensions_whiskerRight _ (prismEndpoint_zero_leftAnodyne K) L)
    v (fiberTransportFamilyRightComparison_initial p f γ T) (prismEndpoint 1 K ▷ L) b
    (fiberTransportFamilyRightComparison_final γ h₁)
    (fiberTransportFamilyRightPrism T) (fiberTransportFamilyRightPrism U)
    (fiberTransportFamilyRightPrism_projection T) (fiberTransportFamilyRightPrism_projection U)
    (fiberTransportFamilyRightPrism_source T) (fiberTransportFamilyRightPrism_source U)
    T.endpoint U.endpoint (fiberTransportFamilyRightPrism_target T)
      (fiberTransportFamilyRightPrism_target U)

end SerrePositivity.InfinityCategories.F2
