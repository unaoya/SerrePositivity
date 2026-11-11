module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiberwisePullbackValueKanComparison
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanCospanPoint

/-!
概要：元の値の指定 path を、構成済み全空間 Kan 引き戻し比較の像として厳密に表示する。
方針：元の path を包含と単位で写し、三座標の一致を照合する。
規約：比較射も元の指定 path も選び直さない。
使われ方：標的の有限射を実際の元の一値で持ち上げる定理の終点。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {K E D H B : SSet.{u}} (p : H ⟶ B) (f : E ⟶ H) (g : D ⟶ H) (b : B _⦋0⦌)
  (s : K ⟶ vertexFiber (f ≫ p) b) (t : K ⟶ vertexFiber (g ≫ p) b)
  (L : SSet.Homotopy (s ≫ vertexFiberMap (f ≫ p) p f rfl b)
    (t ≫ vertexFiberMap (g ≫ p) p g rfl b))

/-- 概要：元の値の指定 path を元の全空間の Kan 模型に含める。
方針：元の包含と単位を後合成し、fiber 射の包含式で両端を照合する。
規約：全円柱は L.h の像。使われ方：元の値からの比較の path の表示。 -/
def fiberwisePullbackValueKanPath :
    SSet.Homotopy ((s ≫ vertexFiberι (f ≫ p) b) ≫ f ≫ continuousKanReplacementUnit.app H)
      ((t ≫ vertexFiberι (g ≫ p) b) ≫ g ≫ continuousKanReplacementUnit.app H) where
  h := L.h ≫ vertexFiberι p b ≫ continuousKanReplacementUnit.app H
  h₀ := by
    change SSet.ι₀ ≫ (L.h ≫ vertexFiberι p b ≫ continuousKanReplacementUnit.app H) = _
    rw [← Category.assoc, L.h₀]
    simp only [Category.assoc, vertexFiberMap_ι]
    rfl
  h₁ := by
    change SSet.ι₁ ≫ (L.h ≫ vertexFiberι p b ≫ continuousKanReplacementUnit.app H) = _
    rw [← Category.assoc, L.h₁]
    simp only [Category.assoc, vertexFiberMap_ι]
    rfl
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

/-- 概要：値の指定三座標の比較像は、元の包含による指定 Kan 引き戻し射と厳密に一致。
方針：構成済み比較の三座標と curry の後合成自然性を使う。
規約：元の実際の比較射。使われ方：元の値での有限持ち上げの照合。 -/
lemma fiberwisePullbackValueKanComparison_point :
    intervalPullbackHomotopyPoint (vertexFiberMap (f ≫ p) p f rfl b)
      (vertexFiberMap (g ≫ p) p g rfl b) s t L ≫
        fiberwisePullbackValueKanComparison p f g b =
      kanCospanPoint f g (s ≫ vertexFiberι (f ≫ p) b) (t ≫ vertexFiberι (g ≫ p) b)
        (fiberwisePullbackValueKanPath p f g b s t L) := by
  apply intervalPullback_hom_ext
  · rw [Category.assoc, fiberwisePullbackValueKanComparison_path, ← Category.assoc,
      intervalPullbackHomotopyPoint_path, kanCospanPoint_path, ← curry_natural_right]
    rfl
  · rw [Category.assoc, fiberwisePullbackValueKanComparison_left, ← Category.assoc,
      intervalPullbackHomotopyPoint_left, kanCospanPoint_left]
    rfl
  · rw [Category.assoc, fiberwisePullbackValueKanComparison_right, ← Category.assoc,
      intervalPullbackHomotopyPoint_right, kanCospanPoint_right]
    rfl

end SerrePositivity.InfinityCategories.F2
