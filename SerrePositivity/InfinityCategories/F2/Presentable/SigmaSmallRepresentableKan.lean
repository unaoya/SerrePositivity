module

public import SerrePositivity.InfinityCategories.F2.Presentable.SigmaRepresentableColimits
public import SerrePositivity.InfinityCategories.HomotopyLimits.Idempotent.UniverseLeftKanShape
public import SerrePositivity.InfinityCategories.F2.Ind.EquivalentRestrictionColimit
public import SerrePositivity.InfinityCategories.F1B.KanExtension.LeftCommaCoconeColimit

/-!
概要：小さい表現可能図式の任意の小さい射に沿う P_Σ 値左 Kan 延長。
方針：同じ局所添字を宇宙比較し、表現可能小図式の余極限を適用する。
規約：P_Σ 全体の余完備性を仮定しない。
使われ方：小余積の有限部分集合表示と反映した bar 図式。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits

/-- 概要：小さい表現可能図式の指定小射に沿う全局所 Kan 余極限が存在する。
方針：同じ小さい局所射影を底へ合成した表現可能図式へ戻す。
規約：元の射と底への図式を固定する。
使われ方：各有限段の全自然な選択。 -/
lemma sigmaSmallRepresentable_leftKanDiagram_hasColimit
    {A B C : SSet.{u}} [Quasicategory A] [Quasicategory B] [Quasicategory C]
    (hC : ∀ (J : Type u) [Finite J] (p : nerve (Discrete J) ⟶ C.op), HasLimit p)
    (δ : A ⟶ B) (p : A ⟶ C)
    (b : ((SSet.uliftFunctor.{u + 1, u}).obj B) _⦋0⦌) :
    HasColimit (leftKanDiagram ((SSet.uliftFunctor.{u + 1, u}).map δ)
      ((SSet.uliftFunctor.{u + 1, u}).map p ≫ sigmaYonedaInfinityMap C) b) := by
  rcases b with ⟨b⟩
  let e := Idempotent.leftKanShapeUniverseIso.{u, u + 1} δ b
  apply Ind.hasColimit_of_equivalentRestriction e.hom
    (qCatEquivalenceOfIso e).isQCatEquivalence
  have he := Idempotent.leftKanShapeUniverseIso_projection.{u, u + 1} δ b
  dsimp only [leftKanDiagram]
  rw [← Category.assoc, he, ← Category.assoc, ← Functor.map_comp]
  exact sigmaYoneda_smallDiagram_hasColimit hC (leftKanProjection δ b ≫ p)

/-- 概要：小さい表現可能図式の同じ小射に沿う全左 Kan 延長が存在する。
方針：全局所余極限から元の指定単位付き存在定理を使う。
規約：全ての射と全自然変換を保持する。
使われ方：filtered な有限段と単体的な余積段の構成。 -/
lemma sigmaSmallRepresentable_exists_leftKanExtension
    {A B C : SSet.{u}} [Quasicategory A] [Quasicategory B] [Quasicategory C]
    (hC : ∀ (J : Type u) [Finite J] (p : nerve (Discrete J) ⟶ C.op), HasLimit p)
    (δ : A ⟶ B) (p : A ⟶ C) :
    ∃ (G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SigmaPresheafInfinity C)
      (β : SSet.Homotopy ((SSet.uliftFunctor.{u + 1, u}).map p ≫ sigmaYonedaInfinityMap C)
        ((SSet.uliftFunctor.{u + 1, u}).map δ ≫ G)),
      IsLeftKanExtension ((SSet.uliftFunctor.{u + 1, u}).map δ)
        ((SSet.uliftFunctor.{u + 1, u}).map p ≫ sigmaYonedaInfinityMap C) G β :=
  F1B.exists_kanLeftExtension_of_local_colimits _ _
    (sigmaSmallRepresentable_leftKanDiagram_hasColimit hC δ p)

end SerrePositivity.InfinityCategories.F2.Presentable
