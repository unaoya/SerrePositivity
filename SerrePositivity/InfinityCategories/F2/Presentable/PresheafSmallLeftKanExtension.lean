module

public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafPointwiseColimits
public import SerrePositivity.InfinityCategories.HomotopyLimits.Idempotent.UniverseLeftKanShape
public import SerrePositivity.InfinityCategories.F2.Ind.EquivalentRestrictionColimit
public import SerrePositivity.InfinityCategories.F1B.KanExtension.LeftCommaCoconeColimit

/-!
概要：任意の小さい射に沿う、前層値図式の全左 Kan 延長の存在。
方針：元の局所添字を宇宙比較し、前層の全小余極限を適用する。
規約：元の射・図式・単位を保持する。
使われ方：elements の bar 図式を次数ごとの一つの coherent な族へまとめる。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 概要：小さい射の同じ局所左 Kan 図式は、前層圏で余極限を持つ。
方針：局所添字の宇宙同型で元の小さい図式に戻す。
規約：小さい始域と終域の quasicategory 性を明示する。
使われ方：元の次数射影に沿う左 Kan 延長の存在入力。 -/
lemma presheafSmallLeftKanDiagram_hasColimit {A B C : SSet.{u}} [Quasicategory A] [Quasicategory B]
    (δ : A ⟶ B) (F : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ PresheafInfinity C)
    (b : ((SSet.uliftFunctor.{u + 1, u}).obj B) _⦋0⦌) :
    HasColimit (leftKanDiagram ((SSet.uliftFunctor.{u + 1, u}).map δ) F b) := by
  rcases b with ⟨b⟩
  let e := F2.Idempotent.leftKanShapeUniverseIso.{u, u + 1} δ b
  apply F2.Ind.hasColimit_of_equivalentRestriction e.hom
    (qCatEquivalenceOfIso e).isQCatEquivalence
  have he : e.hom ≫ leftKanDiagram ((SSet.uliftFunctor.{u + 1, u}).map δ) F
      (ULift.up b) = (SSet.uliftFunctor.{u + 1, u}).map (leftKanProjection δ b) ≫ F := by
    dsimp only [leftKanDiagram]
    rw [← Category.assoc, F2.Idempotent.leftKanShapeUniverseIso_projection]
  rw [he]
  exact presheafInfinity_hasColimit _

/-- 概要：任意の小さい射に沿う前層値の全左 Kan 延長を同じ単位付きで構成できる。
方針：全ての元の局所図式の余極限から存在定理を適用する。
規約：点ごとの値の選択だけに弱めず、全単位変換を得る。
使われ方：bar の全ての面と退化を同時に持つ前層値図式。 -/
lemma presheafSmall_exists_leftKanExtension {A B C : SSet.{u}} [Quasicategory A] [Quasicategory B]
    (δ : A ⟶ B) (F : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ PresheafInfinity C) :
    ∃ (G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ PresheafInfinity C)
      (β : SSet.Homotopy F ((SSet.uliftFunctor.{u + 1, u}).map δ ≫ G)),
      IsLeftKanExtension ((SSet.uliftFunctor.{u + 1, u}).map δ) F G β :=
  F1B.exists_kanLeftExtension_of_local_colimits _ F (presheafSmallLeftKanDiagram_hasColimit δ F)

end SerrePositivity.InfinityCategories.HomotopyLimits
