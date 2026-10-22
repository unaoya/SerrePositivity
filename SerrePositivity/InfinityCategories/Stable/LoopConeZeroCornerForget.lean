module
public import SerrePositivity.InfinityCategories.Stable.ZeroCornerSquareSpanSourceFiber
public import SerrePositivity.InfinityCategories.Stable.LoopConeChoiceModel

/-!
概要：元の普遍 loop 錐の指定点の始対象性と、同じ零隅四角形への移送。
方針：固定 cospan の終対象の自己比較と、実 classifier・選択忘却を接続する。
規約：最後の全四角形図式を厳密に保つ。使われ方：同じ loop 四角形の押し出し性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 元の普遍 loop 錐の同じ指定点と四角形を保つ比較。 -/
def loopConeZeroCornerForget (X : SSet.{u}) [Quasicategory X] :
    loopConeObjects X ⟶ zeroCornerSquares X :=
  (loopConeChoiceIso X).hom ≫
    coneChoiceForget (fullSubcomplexOnVertices ((ihom (horn 2 2 : SSet.{u})).obj X)
      IsZeroOuterCospanVertex).ι ≫ (zeroCornerSquareConeIso X).inv

/-- 元の普遍 loop 錐の同じ指定点と四角形を保つ比較。 -/
lemma loopConeZeroCornerForget_source (X : SSet.{u}) [Quasicategory X] :
    loopConeZeroCornerForget X ≫ zeroCornerSquareSource X = loopConeObjectSource X := by
  let p := (fullSubcomplexOnVertices ((ihom (horn 2 2 : SSet.{u})).obj X)
    IsZeroOuterCospanVertex).ι
  let q := pullback.fst (coneRestriction (horn 2 2 : SSet.{u}) X) p ≫
    coneApexEvaluation (horn 2 2 : SSet.{u}) X
  have hi : (zeroCornerSquareConeIso X).inv ≫ zeroCornerSquareSource X = q := by
    rw [← zeroCornerSquareConeIso_source, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  change ((loopConeChoiceIso X).hom ≫ coneChoiceForget p ≫
    (zeroCornerSquareConeIso X).inv) ≫ zeroCornerSquareSource X = _
  rw [Category.assoc, Category.assoc, hi]
  change (loopConeChoiceIso X).hom ≫ coneChoiceForget p ≫
    pullback.fst (coneRestriction (horn 2 2 : SSet.{u}) X) p ≫
      coneApexEvaluation (horn 2 2 : SSet.{u}) X = _
  rw [← Category.assoc (coneChoiceForget p), coneChoiceForget_diagram,
    ← Category.assoc, loopConeChoiceIso_diagram]
  rfl

/-- 元の普遍 loop 錐の同じ指定点と四角形を保つ比較。 -/
lemma loopConeZeroCornerForget_trivialKanFibration (X : SSet.{u}) [Quasicategory X]
    [HasFiniteLimits X] : TrivialKanFibration (loopConeZeroCornerForget X) := by
  have hp := coneChoiceForget_trivialKanFibration
    (fullSubcomplexOnVertices ((ihom (horn 2 2 : SSet.{u})).obj X)
      IsZeroOuterCospanVertex).ι (fun p ↦ HasFiniteLimits.hasLimit p)
  dsimp only [loopConeZeroCornerForget]
  exact ⟨trivialKanFibrations.comp_mem _ _ (MorphismProperty.rlp_of_isIso _ _)
    (trivialKanFibrations.comp_mem _ _ hp.mem (MorphismProperty.rlp_of_isIso _ _))⟩

/-- 元の普遍 loop 錐の同じ指定点と四角形を保つ比較。 -/
def loopConeZeroCornerSourceFiberMap (X : SSet.{u}) [Quasicategory X] (x : X _⦋0⦌) :
    vertexFiber (loopConeObjectSource X) x ⟶ vertexFiber (zeroCornerSquareSource X) x :=
  vertexFiberMap (loopConeObjectSource X) (zeroCornerSquareSource X)
    (loopConeZeroCornerForget X) (loopConeZeroCornerForget_source X) x

/-- 元の普遍 loop 錐の同じ指定点と四角形を保つ比較。 -/
lemma loopConeZeroCornerSourceFiberMap_trivialKanFibration (X : SSet.{u})
    [Quasicategory X] [HasFiniteLimits X] (x : X _⦋0⦌) :
    TrivialKanFibration (loopConeZeroCornerSourceFiberMap X x) := by
  have := loopConeZeroCornerForget_trivialKanFibration X
  exact HomotopyLimits.vertexFiberMap_trivialKanFibration _ _ _ _ _

/-- 元の普遍 loop 錐の同じ指定点と四角形を保つ比較。 -/
lemma loopConeZeroCornerSourceFiberMap_isQCatEquivalence (X : SSet.{u})
    [Quasicategory X] [HasFiniteLimits X] (x : X _⦋0⦌) :
    IsQCatEquivalence (loopConeZeroCornerSourceFiberMap X x) := by
  have := loopConeZeroCornerSourceFiberMap_trivialKanFibration X x
  exact isQCatEquivalence_of_trivialKanFibration _
end SerrePositivity.InfinityCategories
