module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.TransformationFamilyDiagram

/-!
概要：関手空間の元の単体を、一点パラメータ付きの全族として評価する。
方針：元の族を一点への射影で引き戻し、既存の prism 評価を使う。
規約：元の全単体を保持。使われ方：指定比較三角形を coherent 変換の族へ読む。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の関手空間の族を、元の底と一点パラメータを持つ全図式へ展開する。 -/
def functorUnitFamilyDiagram {A B X : SSet.{u}} (T : A ⟶ (ihom B).obj X) :
    A ⊗ (B ⊗ (Δ[0] : SSet.{u})) ⟶ X :=
  (α_ A B Δ[0]).inv ≫ functorParameterizedPrism (fst A (Δ[0] : SSet.{u}) ≫ T)

/-- 元の族の制限と一点パラメータ付き評価は、全単体で厳密に可換。 -/
lemma functorUnitFamilyDiagram_pre {A A' B X : SSet.{u}}
    (i : A' ⟶ A) (T : A ⟶ (ihom B).obj X) :
    (i ▷ (B ⊗ (Δ[0] : SSet.{u}))) ≫ functorUnitFamilyDiagram T =
      functorUnitFamilyDiagram (i ≫ T) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨a, b, t⟩
  rfl

end SerrePositivity.InfinityCategories.F2
