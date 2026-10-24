module

public import SerrePositivity.InfinityCategories.F2.Ind.ConeTerminalSliceFunctorIsoNaturality

/-!
概要：元の底固定比較の始域境界は、同じ全余錐比較を始域で制限した指定値そのもの。
方針：元の境界表示の型の等号移送を取り出し、相対関手の包含の自然性へ渡す。
規約：元の比較同型の値を保持し、新たな比較の選択で代用しない。
使われ方：極大点評価の指定変換を旧族の同じ比較で保持する相対余錐の構成。
-/

@[expose] public section
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.F2.Ind
/-- 概要：型の等号による表示変更は元の値を保持。方針：等号を消去。
規約：指定値を保持。使われ方：元の比較の境界表示を戻す。 -/
private theorem eq_mp_heq {α β : Sort u} (h : α = β) (a : α) : HEq (h.mp a) a := by
  cases h
  rfl
variable {A X : SSet.{u}} [Quasicategory X] (x : X _⦋0⦌)
  (b : join A (Δ[0] : SSet.{u}) ⟶ X)
  (hb : joinInr A Δ[0] ≫ b = SSet.yonedaEquiv.symm x)
  (W : join A (Δ[0] : SSet.{u}) ⟶ sliceOver (SSet.yonedaEquiv.symm x))
  (hp : W ≫ sliceOverProjection (SSet.yonedaEquiv.symm x) = b)
  (ht : joinInr A Δ[0] ≫ W = SSet.yonedaEquiv.symm (sliceIdentityCone x))
/-- 概要：元の始域境界の比較は、同じ全余錐比較の始域制限そのもの。
方針：元の型移送を戻す。規約：指定同型の値を保持。使われ方：旧族の変換保持。 -/
lemma coneTerminalSliceBoundaryRelativeIso_heq_map :
    HEq (coneTerminalSliceBoundaryRelativeIso x b hb W hp ht)
    (VertexIso.map (coneTerminalSliceRelativeIso x b hb W hp ht)
      (relativeFunctorPre (sliceOverProjection (SSet.yonedaEquiv.symm x)) b
        (joinInl A (Δ[0] : SSet.{u})))) := by
  unfold coneTerminalSliceBoundaryRelativeIso
  exact eq_mp_heq _ _
/-- 概要：元の全底と終点を固定した境界比較を、同じ全 slice 族の同型として読む。
方針：元の相対関手空間の包含。規約：同じ指定値。使われ方：元の評価下の余錐の帰還。 -/
def coneTerminalSliceBoundaryFunctorIso :
    FunctorIso (joinInl A (Δ[0] : SSet.{u}) ≫ W) (sliceOverCurry b hb) :=
  relativeFunctorVertexIsoImage _ _ _ _ _ _
    (coneTerminalSliceBoundaryRelativeIso x b hb W hp ht)
/-- 概要：元の境界の全族の比較は、同じ全余錐の比較を始域で制限した指定値。
方針：元の相対比較と包含の自然性。規約：同じ指定値。使われ方：旧族での比較回収。 -/
lemma coneTerminalSliceBoundaryFunctorIso_heq_precomp : HEq
    (coneTerminalSliceBoundaryFunctorIso x b hb W hp ht)
    ((coneTerminalSliceFunctorIso x b hb W hp ht).precomp (joinInl A (Δ[0] : SSet.{u}))) := by
  dsimp only [coneTerminalSliceBoundaryFunctorIso, coneTerminalSliceFunctorIso]
  rw [relativeFunctorVertexIsoImage_precomp]
  apply relativeFunctorVertexIsoImage_heq
  · rfl
  · exact (coneTerminalSliceLift_old x b hb).symm
  · exact coneTerminalSliceBoundaryRelativeIso_heq_map x b hb W hp ht
end SerrePositivity.InfinityCategories.F2.Ind
