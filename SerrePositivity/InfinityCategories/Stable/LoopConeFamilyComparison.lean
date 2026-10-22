module
public import SerrePositivity.InfinityCategories.Stable.RelativeTerminalSectionComparison
public import SerrePositivity.InfinityCategories.Stable.LoopDiagramArrows
/-!
概要：任意パラメータの全錐から指定された普遍 loop 錐の族への比較。
方針：相対終対象の全関手比較を、元の universal cone の射影へ適用する。
規約：底を全時刻で固定する。使われ方：HA 1.4.2.27 の余錐分類。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
lemma universalConeFamilyComparison_exists {A K X : SSet.{u}}
    (f : A ⟶ (ihom (join (Δ[0] : SSet.{u}) K)).obj X)
    (g : A ⟶ limitCones K X)
    (h : f ≫ coneRestriction K X = g ≫ limitConeProjection K X) :
    ∃ H : SSet.Homotopy f (g ≫ (relativeTerminalVertices (coneRestriction K X)).ι),
      H.h ≫ coneRestriction K X =
        CartesianMonoidalCategory.fst A (Δ[1] : SSet.{u}) ≫ f ≫ coneRestriction K X := by
  apply relativeTerminalFamilyHomotopy_exists
  · exact h
  · intro a
    exact fullSubcomplexOnVertices_vertex (g.app (Opposite.op ⦋0⦌) a)
lemma loopConeFamilyComparison_exists {A X : SSet.{u}} [Quasicategory X]
    (f : A ⟶ (ihom (join (Δ[0] : SSet.{u}) (horn 2 2 : SSet.{u}))).obj X)
    (g : A ⟶ loopDiagrams X)
    (h : f ≫ coneRestriction (horn 2 2 : SSet.{u}) X =
      g ≫ loopDiagramConeFamily X ≫ limitConeProjection (horn 2 2 : SSet.{u}) X) :
    ∃ H : SSet.Homotopy f (g ≫ loopDiagramConeFamily X ≫
        (relativeTerminalVertices (coneRestriction (horn 2 2 : SSet.{u}) X)).ι),
      H.h ≫ coneRestriction (horn 2 2 : SSet.{u}) X =
        CartesianMonoidalCategory.fst A (Δ[1] : SSet.{u}) ≫ f ≫
          coneRestriction (horn 2 2 : SSet.{u}) X :=
  universalConeFamilyComparison_exists f (g ≫ loopDiagramConeFamily X) (by
    simpa only [Category.assoc] using h)
end SerrePositivity.InfinityCategories
