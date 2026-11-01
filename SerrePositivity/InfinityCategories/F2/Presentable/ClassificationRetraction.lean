module

public import SerrePositivity.InfinityCategories.F2.Presentable.HomClassificationLaws
public import SerrePositivity.InfinityCategories.Core.Retracts

/-!
概要：全空間の相対 Hom 内の分裂等式を、全分類関手の retract に送る。
方針：分類比較の合成則と相対同型に対する不変性を適用する。
規約：元の分類射を包含・射影として保持する。
使われ方：全解錐から表現可能関手の全自然な retract を得る。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：相対関手空間で分裂する全空間比較は、同じ全分類図式の retract を与える。
方針：指定比較の分類を合成し、相対 Hom 内の同型から恒等変換へ戻す。
規約：点ごとの retract ではなく全関手圏内の retract を構成する。
使われ方：余表現可能性のための全自然な分裂三角形。 -/
def leftClassificationRetraction {E H B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) (q : H ⟶ B) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ H) (hf : f ≫ q = p) (g : H ⟶ E) (hg : g ≫ p = q)
    (h : VertexIso
      (relativeFunctorVertex p p (f ≫ g) (by rw [Category.assoc, hg, hf]))
      (relativeFunctorVertex p p (𝟙 E) (Category.id_comp p))) :
    Idempotent.VertexRetraction (functorVertex (leftStraighteningInfinityDiagram p))
      (functorVertex (leftStraighteningInfinityDiagram q)) where
  i := leftClassificationHom p q f hf
  r := leftClassificationHom q p g hg
  retract := by
    rw [leftClassificationHom_comp]
    rw [leftClassificationHom_eq_of_relativeVertexIso p p _ _ _ _ h]
    exact leftClassificationHom_id p

end SerrePositivity.InfinityCategories.F2.Presentable
