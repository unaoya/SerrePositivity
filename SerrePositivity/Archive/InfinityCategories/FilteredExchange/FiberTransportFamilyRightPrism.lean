module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.FiberTransportFamily

/-!
概要：元の全輸送の prism を右結合の表示に移し、元の両端と底を保持する。
方針：同じ結合子を前合成し、元の全輸送の三条件を移す。
規約：輸送を再選択しない。使われ方：元の unstraightening の prism 比較との照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {E B K L : SSet.{u}} {p : E ⟶ B} {a b : B _⦋0⦌}
  {f : K ⟶ vertexFiber p a} {γ : (Δ[1] : SSet.{u}) ⊗ L ⟶ B}
  (T : FiberTransportFamily (b := b) p f γ)

/-- 元の全輸送の prism の右結合表示。 -/
def fiberTransportFamilyRightPrism : ((Δ[1] : SSet.{u}) ⊗ K) ⊗ L ⟶ E :=
  (α_ Δ[1] K L).hom ≫ T.prism

/-- 右結合表示の元の始点は、同じ全始点族を保持する。 -/
lemma fiberTransportFamilyRightPrism_source :
    (prismEndpoint 0 K ▷ L) ≫ fiberTransportFamilyRightPrism T =
      fst K L ≫ f ≫ vertexFiberι p a := by
  rw [fiberTransportFamilyRightPrism, ← Category.assoc]
  change prismEndpoint 0 (K ⊗ L) ≫ T.prism = _
  exact T.start

/-- 右結合表示の元の終点は、同じ fiber 終点を保持する。 -/
lemma fiberTransportFamilyRightPrism_target :
    (prismEndpoint 1 K ▷ L) ≫ fiberTransportFamilyRightPrism T =
      T.endpoint ≫ vertexFiberι p b := by
  rw [fiberTransportFamilyRightPrism, ← Category.assoc]
  change prismEndpoint 1 (K ⊗ L) ≫ T.prism = _
  exact T.finish

/-- 右結合表示の元の prism は、同じ底の区間全族を被覆する。 -/
lemma fiberTransportFamilyRightPrism_projection :
    fiberTransportFamilyRightPrism T ≫ p =
      (α_ Δ[1] K L).hom ≫ (Δ[1] ◁ snd K L) ≫ γ := by
  rw [fiberTransportFamilyRightPrism, Category.assoc, T.over_base]

end SerrePositivity.InfinityCategories.F2
