module

public import SerrePositivity.InfinityCategories.F2.Presentable.SmallPieceLeftKanExtension
public import SerrePositivity.InfinityCategories.F2.Presentable.Definition

/-!
概要：小さい全形状間の写像に沿う、余完備標的への native 左 Kan 拡張を構成する。
方針：公開の局所添字の宇宙同型で小余極限を持ち上げ、点ごとの存在定理を適用する。
規約：大きい形状一般の余完備性を仮定しない。使われ方：増大部分 poset の余極限族。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Localization
open HomotopyLimits

/-- 小さい元の写像の持ち上げに沿う局所 Kan 図式は、同じ小余極限を持つ。 -/
lemma smallShape_leftKanDiagram_hasColimit
    {K L : SSet.{u}} [Quasicategory K] [Quasicategory L] (δ : K ⟶ L)
    {C : SSet.{u + 1}} [Quasicategory C] (hC : HasSmallColimits C)
    (F : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ C)
    (v : ((SSet.uliftFunctor.{u + 1, u}).obj L) _⦋0⦌) :
    HasColimit (leftKanDiagram ((SSet.uliftFunctor.{u + 1, u}).map δ) F v) := by
  rcases v with ⟨v⟩
  let e := Idempotent.leftKanShapeUniverseIso.{u, u + 1} δ v
  have he : e.hom ≫ leftKanDiagram ((SSet.uliftFunctor.{u + 1, u}).map δ) F
      (ULift.up v) = (SSet.uliftFunctor.{u + 1, u}).map (leftKanProjection δ v) ≫ F := by
    dsimp only [leftKanDiagram]
    rw [← Category.assoc, Idempotent.leftKanShapeUniverseIso_projection]
  have hsmall : HasColimit (e.hom ≫
      leftKanDiagram ((SSet.uliftFunctor.{u + 1, u}).map δ) F (ULift.up v)) := by
    rw [he]
    exact hC (leftKanShape δ v) _
  exact Ind.hasColimit_of_equivalentRestriction e.hom
    (qCatEquivalenceOfIso e).isQCatEquivalence _ hsmall

/-- 元の小さい写像に沿う coherent な全左 Kan 拡張が存在する。 -/
lemma exists_smallShape_leftKanExtension
    {K L : SSet.{u}} [Quasicategory K] [Quasicategory L] (δ : K ⟶ L)
    {C : SSet.{u + 1}} [Quasicategory C] (hC : HasSmallColimits C)
    (F : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ C) :
    ∃ (G : (SSet.uliftFunctor.{u + 1, u}).obj L ⟶ C)
      (β : SSet.Homotopy F ((SSet.uliftFunctor.{u + 1, u}).map δ ≫ G)),
      IsLeftKanExtension ((SSet.uliftFunctor.{u + 1, u}).map δ) F G β :=
  F1B.exists_kanLeftExtension_of_local_colimits _ F
    (smallShape_leftKanDiagram_hasColimit δ hC F)

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
