module

public import SerrePositivity.InfinityCategories.F2.Ind.UnderSectionTotalDiagram
public import SerrePositivity.InfinityCategories.F1.SimplicialReplacementFunctor
public import SerrePositivity.InfinityCategories.F1.UniversalScaffold

/-!
概要：元の全空間への under 切断図式の大域評価を、全高次を保つ一つの射として作る。
方針：構成済みの一つの係数自然変換を replacement に写し、元の scaffold 評価を合成する。
規約：元の添字への射影を厳密に保つ。同値性と分類の比較は後続。
使われ方：coherent 前層図式の strict 化の大域比較。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {I : Type u} [Category.{u} I] {B E : SSet.{u}} (p : E ⟶ B ⊗ nerve I)

/-- 元の共同全空間への、全添字の under 切断を同時に評価する射。 -/
def underSectionScaffold : simplicialReplacement (underSectionTotalDiagram p) ⟶ E :=
  simplicialReplacementMap (underSectionTotalForget p) ≫
    universalScaffold (p ≫ snd B (nerve I))

/-- 同じ大域評価は、元の添字の射影を厳密に保つ。 -/
lemma underSectionScaffold_projection :
    underSectionScaffold p ≫ p ≫ snd B (nerve I) =
      simplicialReplacementProjection (underSectionTotalDiagram p) := by
  rw [underSectionScaffold, Category.assoc, universalScaffold_projection,
    simplicialReplacementMap_projection]

end SerrePositivity.InfinityCategories.F2.Ind
