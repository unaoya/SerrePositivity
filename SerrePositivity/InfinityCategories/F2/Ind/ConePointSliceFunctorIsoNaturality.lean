module

public import SerrePositivity.InfinityCategories.F2.Ind.ConePointSliceRelativeComparison
public import SerrePositivity.InfinityCategories.F2.Ind.RelativeFunctorVertexIsoNaturality

/-!
概要：元の点の全余錐の比較を全 slice 族の同型へ戻し、旧族への制限で指定値を保持する。
方針：元の相対関手空間の包含と、同じ right-anodyne 比較の自然性を合成する。
規約：元の点写像と両全族を保持する。
使われ方：元の極大点評価の指定変換を、旧族の同じ比較で保持する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {A X : SSet.{u}} [Quasicategory X] (p : (Δ[0] : SSet.{u}) ⟶ X)
  (b : join A (Δ[0] : SSet.{u}) ⟶ X) (hb : joinInr A Δ[0] ≫ b = p)
  (W : join A (Δ[0] : SSet.{u}) ⟶ sliceOver p) (hp : W ≫ sliceOverProjection p = b)
  (ht : sliceOverUncurry (joinInr A Δ[0] ≫ W) = SSet.const (SSet.yonedaEquiv p))
/-- 概要：元の点と全底を固定した比較を、同じ元の全 slice 族の同型へ戻す。
方針：元の相対関手空間の包含。規約：同じ指定値。使われ方：元の指定変換の保持。 -/
def conePointSliceFunctorIso : FunctorIso W (conePointSliceLift p b hb) :=
  relativeFunctorVertexIsoImage _ _ _ _ _ _ (conePointSliceRelativeIso p b hb W hp ht)
/-- 概要：元の全 slice 族の比較は、旧族で元の同じ比較を回収する。
方針：元の相対比較と包含の自然性。規約：同じ指定値。使われ方：元の指定変換の保持。 -/
lemma conePointSliceFunctorIso_precomp {A₀ : SSet.{u}} (k : A₀ ⟶ A) : HEq
    ((conePointSliceFunctorIso p b hb W hp ht).precomp (joinMap k (𝟙 Δ[0])))
    (conePointSliceFunctorIso p (joinMap k (𝟙 Δ[0]) ≫ b)
      (by rw [← Category.assoc, joinInr_joinMap, Category.id_comp]; exact hb)
      (joinMap k (𝟙 Δ[0]) ≫ W) (by rw [Category.assoc, hp]) (by
        rw [← Category.assoc, joinInr_joinMap, Category.id_comp]
        exact ht)) := by
  dsimp only [conePointSliceFunctorIso]
  rw [relativeFunctorVertexIsoImage_precomp]
  apply relativeFunctorVertexIsoImage_heq
  · rfl
  · exact conePointSliceLift_precomp p b hb k
  · exact conePointSliceRelativeIso_precomp p b hb W hp ht k
end SerrePositivity.InfinityCategories.F2.Ind
