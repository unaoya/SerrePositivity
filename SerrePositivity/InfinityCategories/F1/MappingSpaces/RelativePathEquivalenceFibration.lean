module

public import SerrePositivity.InfinityCategories.F1.FunctorCategories.InvertingRestrictionRelativePath

/-!
概要：相対可逆 path の持ち上げを持つ同値を、厳密な境界持ち上げへ強める。
方針：可逆 path 置換と相対 path 写像の切断を合成して、元の射の厳密な切断を作る。
規約：モデル構造を使わず、全射性と充満忠実 inner fibration の境界判定を使う。
使われ方：セル付加の比較立方体の解像を trivial Kan fibration で比較する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 相対可逆 path の始点持ち上げを持つ同値には、厳密な切断が存在する。 -/
lemma IsQCatEquivalence.exists_section_of_relativePath {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {p : X ⟶ Y} (hp : IsQCatEquivalence p)
    [TrivialKanFibration (relativeEquivalencePathMapAt p 0)] :
    ∃ s : Y ⟶ X, s ≫ p = 𝟙 Y := by
  have : TrivialKanFibration (equivalencePathReplacementMap p) :=
    hp.equivalencePathReplacementMap_trivialKanFibration
  obtain ⟨s, hs⟩ := trivialKanFibration_exists_section (equivalencePathReplacementMap p)
  obtain ⟨t, ht⟩ := trivialKanFibration_exists_section (relativeEquivalencePathMapAt p 0)
  have hh : t ≫ equivalencePathEndpoint X 1 ≫ p = equivalencePathReplacementMap p := by
    rw [← equivalencePathMap_endpoint p 1, ← relativeEquivalencePathMapAt_fst p 0]
    simp only [← Category.assoc, ht, Category.id_comp]
    rfl
  refine ⟨s ≫ t ≫ equivalencePathEndpoint X 1, ?_⟩
  simp only [Category.assoc, hh, hs]

/-- 内ホーンと相対可逆 path を持ち上げる同値は、全ての境界を持ち上げる。 -/
lemma IsQCatEquivalence.trivialKanFibration_of_relativePath {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {p : X ⟶ Y} [InnerFibration p]
    [TrivialKanFibration (relativeEquivalencePathMapAt p 0)] (hp : IsQCatEquivalence p) :
    TrivialKanFibration p := by
  obtain ⟨s, hs⟩ := hp.exists_section_of_relativePath
  apply hp.isFullyFaithful.trivialKanFibration_of_surjective
  intro y
  refine ⟨s.app (Opposite.op ⦋0⦌) y, ?_⟩
  exact congrArg (fun f : Y ⟶ Y ↦ f.app (Opposite.op ⦋0⦌) y) hs

end SerrePositivity.InfinityCategories
