module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.FunctorComponentComparison

/-!
概要：元の写像の成分回収を、全三角形と指定した頂点同値に沿って移す。
方針：指定点を選択済み逆射へ送り、同じ三角形と同じ逆の二胞体で元の点へ戻す。
規約：各項からの写像を変更しない。使われ方：任意の指定余極限余錐の脚の点回収。

対応節は Kerodon 9.2（Tag 0639）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects

/-- 頂点同値と元の可換三角形は、元の同じ脚による全成分の回収を保つ。 -/
lemma componentRepresentative_of_triangle {J : Type u} {Z Y : SSet.{u}}
    [Quasicategory Z] [Quasicategory Y] (q : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence Z Y)
    (X : J → SSet.{u}) (f : ∀ j, X j ⟶ Z) (g : ∀ j, X j ⟶ Y)
    (h : ∀ j, SSet.Homotopy (g j) (f j ≫ q.hom))
    (hs : ∀ z : Z _⦋0⦌, ∃ j, ∃ w : X j _⦋0⦌,
      SSet.π₀.mk ((f j).app (Opposite.op ⦋0⦌) w) = SSet.π₀.mk z)
    (y : Y _⦋0⦌) :
    ∃ j, ∃ w : X j _⦋0⦌,
      SSet.π₀.mk ((g j).app (Opposite.op ⦋0⦌) w) = SSet.π₀.mk y := by
  obtain ⟨j, w, hw⟩ := hs (q.inv.app (Opposite.op ⦋0⦌) y)
  have hh := SSet.π₀.sound (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (h j) w)
  change SSet.π₀.mk ((g j).app (Opposite.op ⦋0⦌) w) =
    SSet.π₀.mk (q.hom.app (Opposite.op ⦋0⦌) ((f j).app (Opposite.op ⦋0⦌) w)) at hh
  have hq := congrArg (SSet.mapπ₀ q.hom) hw
  simp only [SSet.mapπ₀_mk] at hq
  exact ⟨j, w, hh.trans (hq.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.qCatEquivalence_inv_hom_component q y))⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects
