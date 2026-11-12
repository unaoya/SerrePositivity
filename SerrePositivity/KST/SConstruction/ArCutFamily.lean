module
public import SerrePositivity.KST.SConstruction.ArCutCofiber

/-! # 任意の切断位置の cofiber 図式の族
概要：gapped 図式を各区間の切断 cofiber 四角形の全高次単体の族に送る。
方針：自然な添字四角形を curry し、全頂点で cofiber 性を証明して持ち上げる。
規約：cofiber は既存の図式内から取り出す。使われ方：Segal 分解と相対図式への比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 同じ図式内の切断四角形を全 Ar 区間について同時に取り出す。 -/
def arCutFamily {n : ℕ} {C : SSet.{u}} (k : Fin (n + 1)) (F : arNerve n ⟶ C) :
    arNerve n ⟶ (ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj C :=
  curry ((β_ (Δ[1] ⊗ Δ[1] : SSet.{u}) (arNerve n)).hom ≫ arCutSquareMap n k ≫ F)

/-- 切断の族の各頂点は対応する実際の四角形の関手頂点。 -/
lemma arCutFamily_vertex {n : ℕ} {C : SSet.{u}} (k : Fin (n + 1))
    (F : arNerve n ⟶ C) (a : Ar.{u} n) :
    (arCutFamily k F).app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ a) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (arCutSquareAt k a ≫ F) := by
  rw [arCutFamily, curry_vertex_value]
  apply congrArg (fun f : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ C => _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f)
  have h : CartesianMonoidalCategory.lift (𝟙 (Δ[1] ⊗ Δ[1] : SSet.{u}))
      (SSet.const (ComposableArrows.mk₀ a)) ≫
        (β_ (Δ[1] ⊗ Δ[1] : SSet.{u}) (arNerve n)).hom =
    CartesianMonoidalCategory.lift (SSet.const (ComposableArrows.mk₀ a))
      (𝟙 (Δ[1] ⊗ Δ[1] : SSet.{u})) := rfl
  rw [← Category.assoc, ← Category.assoc, h]
  rfl

/-- 元の gapped 図式から切断 cofiber 四角形の族を全ての高次単体とともに取り出す。 -/
def gappedCutCofiberFamily {n : ℕ} {C : SSet.{u}} [Quasicategory C]
    (k : Fin (n + 1)) {F : arNerve n ⟶ C} (hF : IsGapped F) :
    arNerve n ⟶ cofiberDiagrams C :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift IsCofiberDiagramVertex (arCutFamily k F) (by
    intro v
    obtain ⟨a, rfl⟩ := nerveEquiv.symm.surjective v
    change IsCofiberDiagramVertex
      ((arCutFamily k F).app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ a))
    rw [arCutFamily_vertex]
    change _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (arCutSquareAt k a ≫ F))) 0 1) ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (arCutSquareAt k a ≫ F)))
    rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagram_functorVertex]
    exact arCutSquareAt_isCofiber k a hF)

/-- 切断 cofiber 族の包含は元の四角形の coherent な族を保持する。 -/
lemma gappedCutCofiberFamily_ι {n : ℕ} {C : SSet.{u}} [Quasicategory C]
    (k : Fin (n + 1)) {F : arNerve n ⟶ C} (hF : IsGapped F) :
    gappedCutCofiberFamily k hF ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι =
      arCutFamily k F :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _

end SerrePositivity.KST.SConstruction
