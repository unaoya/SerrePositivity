module

public import SerrePositivity.InfinityCategories.F2.Ind.ConeTerminalSliceComparisonNaturality
public import SerrePositivity.InfinityCategories.F2.Ind.RelativeFunctorVertexIsoNaturality

/-!
概要：同じ終点への全余錐の相対比較は、元の試験形状の制限でも同じ指定比較を回収する。
方針：right-anodyne 相対比較の自然性と、標準持ち上げの厳密な全自然性を合成する。
規約：元の底と終点を固定し、同型の存在だけでなく指定値そのものを保持する。
使われ方：指定された極大点評価下の変換を、同じ旧族で保持する相対余錐の構成。
-/

@[expose] public section
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {A A₀ X : SSet.{u}} [Quasicategory X] (x : X _⦋0⦌)
  (b : join A (Δ[0] : SSet.{u}) ⟶ X)
  (hb : joinInr A Δ[0] ≫ b = SSet.yonedaEquiv.symm x)
  (W : join A (Δ[0] : SSet.{u}) ⟶ sliceOver (SSet.yonedaEquiv.symm x))
  (hp : W ≫ sliceOverProjection (SSet.yonedaEquiv.symm x) = b)
  (ht : joinInr A Δ[0] ≫ W = SSet.yonedaEquiv.symm (sliceIdentityCone x))
  (k : A₀ ⟶ A)
/-- 概要：元の全底余錐と恒等終点を固定した比較を、元の全 slice 族の同型で読む。
方針：元の相対関手空間の包含。規約：指定同型を保持。使われ方：旧族の比較の帰還。 -/
def coneTerminalSliceFunctorIso :
    FunctorIso W (coneTerminalSliceLift x b hb) :=
  relativeFunctorVertexIsoImage _ _ _ _ _ _ (coneTerminalSliceRelativeIso x b hb W hp ht)
/-- 概要：同じ全 slice 族の指定比較は、旧族で元の同じ比較へ制限される。
方針：相対比較と元の包含の自然性。規約：同じ指定値。使われ方：元の指定変換の保持。 -/
lemma coneTerminalSliceFunctorIso_precomp : HEq
    ((coneTerminalSliceFunctorIso x b hb W hp ht).precomp (joinMap k (𝟙 Δ[0])))
    (coneTerminalSliceFunctorIso x (joinMap k (𝟙 Δ[0]) ≫ b)
      (by rw [← Category.assoc, joinInr_joinMap, Category.id_comp]; exact hb)
      (joinMap k (𝟙 Δ[0]) ≫ W) (by rw [Category.assoc, hp])
      (by rw [← Category.assoc, joinInr_joinMap, Category.id_comp]; exact ht)) := by
  dsimp only [coneTerminalSliceFunctorIso]
  rw [relativeFunctorVertexIsoImage_precomp]
  apply relativeFunctorVertexIsoImage_heq
  · rfl
  · exact coneTerminalSliceLift_precomp x b hb k
  · exact coneTerminalSliceRelativeIso_precomp x b hb W hp ht k
end SerrePositivity.InfinityCategories.F2.Ind
