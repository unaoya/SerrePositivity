module

public import Mathlib.CategoryTheory.LiftingProperties.Basic
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.FilteredRelativeFactorization

/-!
概要：有限な単体集合間の射に対する右持ち上げ性は filtered 余極限で保たれる。
方針：上辺を一段へ下ろし、下辺を境界を固定して後続段へ下ろしてから持ち上げる。
規約：通常の小圏による図式と実際の余極限余錐を使う。
使われ方：filtered 余極限による Kan fibration と homotopy pullback の保存。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 概要：有限な包含を試験する右持ち上げ性は filtered 余極限へ移る。
方針：二つの有限な辺を同じ段で可換にしてから、段の持ち上げを余極限へ送る。
規約：試験射 i の単射性は不要。使われ方：Kan fibration の filtered 余極限。 -/
lemma hasLiftingProperty_of_filtered_isColimit
    {I : Type u} [SmallCategory I] [IsFiltered I]
    {F G : I ⥤ SSet.{u}} (η : F ⟶ G)
    {cF : Cocone F} (hF : IsColimit cF) {cG : Cocone G} (hG : IsColimit cG)
    (p : cF.pt ⟶ cG.pt) (hp : ∀ j, cF.ι.app j ≫ p = η.app j ≫ cG.ι.app j)
    {A B : SSet.{u}} [A.Finite] [B.Finite] (i : A ⟶ B)
    [∀ j, HasLiftingProperty i (η.app j)] : HasLiftingProperty i p where
  sq_hasLift {a b} sq := by
    obtain ⟨j, aj, haj⟩ := IsFinitelyPresentable.exists_hom_of_isColimit hF a
    have hab : (aj ≫ η.app j) ≫ cG.ι.app j = i ≫ b := by
      rw [Category.assoc, ← hp j, ← Category.assoc, haj]
      exact sq.w
    obtain ⟨k, v, bk, hbk, hb⟩ := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.finite_relative_factorization_of_filtered_isColimit hG
      i j (aj ≫ η.app j) b hab
    have sqk : CommSq (aj ≫ F.map v) i (η.app k) bk := by
      constructor
      change (aj ≫ F.map v) ≫ η.app k = i ≫ bk
      rw [Category.assoc, η.naturality v, ← Category.assoc]
      exact hbk.symm
    refine ⟨⟨{ l := sqk.lift ≫ cF.ι.app k, fac_left := ?_, fac_right := ?_ }⟩⟩
    · rw [← Category.assoc, sqk.fac_left, Category.assoc, cF.w v]
      exact haj
    · rw [Category.assoc, hp k, ← Category.assoc, sqk.fac_right]
      exact hb

end SerrePositivity.InfinityCategories.Project.FilteredExchange
