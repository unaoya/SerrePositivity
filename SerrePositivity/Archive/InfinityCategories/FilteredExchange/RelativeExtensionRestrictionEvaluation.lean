module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeExtensionRestriction
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.UniversalScaffoldEvaluation

/-!
概要：元の相対延長空間の制限の全評価は、元の全評価の実際の前合成になる。
方針：制限の包含と相対前合成の評価の厳密な式を使う。
規約：全延長と初期値の正方形を保持。使われ方：元の prism 比較を左結合表示へ戻す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 制限した全延長の全評価は、元の実射による前合成そのもの。 -/
lemma relativeExtensionRestriction_uncurry {A D A' D' E B : SSet.{u}}
    (p : E ⟶ B) (b : A ⟶ B) (i : D ⟶ A) (v : D ⟶ E)
    (hv : v ≫ p = i ≫ b) (h : A' ⟶ A) (k : D' ⟶ D) (i' : D' ⟶ A')
    (hs : i' ≫ h = k ≫ i) :
    relativeFunctorUncurry (relativeExtensionRestriction p b i v hv h k i' hs ≫
      relativeFunctorExtensionSpaceι p (h ≫ b) i' (k ≫ v)
        (by rw [Category.assoc, hv, ← Category.assoc, ← hs, Category.assoc])) =
      (h ▷ relativeFunctorExtensionSpace p b i v hv) ≫
        relativeFunctorUncurry (relativeFunctorExtensionSpaceι p b i v hv) := by
  rw [relativeExtensionRestriction_ι, relativeFunctorUncurry_pre]

end SerrePositivity.InfinityCategories.F2
