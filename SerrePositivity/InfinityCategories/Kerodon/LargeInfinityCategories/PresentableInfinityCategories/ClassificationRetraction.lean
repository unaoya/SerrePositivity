module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.HomClassificationLaws
public import SerrePositivity.InfinityCategories.HTT.RetractsAndIdempotentCompletion.RetractClosure

/-!
概要：全空間の相対 Hom 内の分裂等式を、全分類関手の retract に送る。
方針：分類比較の合成則と相対同型に対する不変性を適用する。
規約：元の分類射を包含・射影として保持する。
使われ方：全解錐から表現可能関手の全自然な retract を得る。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：相対関手空間で分裂する全空間比較は、同じ全分類図式の retract を与える。
方針：指定比較の分類を合成し、相対 Hom 内の同型から恒等変換へ戻す。
規約：点ごとの retract ではなく全関手圏内の retract を構成する。
使われ方：余表現可能性のための全自然な分裂三角形。 -/
def leftClassificationRetraction {E H B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) (q : H ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q]
    (f : E ⟶ H) (hf : f ≫ q = p) (g : H ⟶ E) (hg : g ≫ p = q)
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex p p (f ≫ g) (by rw [Category.assoc, hg, hf]))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex p p (𝟙 E) (Category.id_comp p))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.VertexRetraction (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityDiagram p))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityDiagram q)) where
  i := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftClassificationHom p q f hf
  r := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftClassificationHom q p g hg
  retract := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftClassificationHom_comp]
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftClassificationHom_eq_of_relativeVertexIso p p _ _ _ _ h]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftClassificationHom_id p

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
