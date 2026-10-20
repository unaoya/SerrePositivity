module

public import SerrePositivity.KST.LocalizingInvariants.ArrowStableExact
public import SerrePositivity.KST.LocalizingInvariants.CofiberBottomLifting
public import SerrePositivity.KST.LocalizingInvariants.CofiberRightLifting

/-!
概要：安定圏の cofiber の元の全単体上の選択は完全関手。
方針：底辺と右辺の評価の trivial Kan fibration 性から cofiber 回転の完全性を得る。
規約：元の選択された cofiber 関手を変更しない。使われ方：差の実関手の完全性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

/-- 自明 Kan fibration との合成の完全性から元の関手の完全性を戻す。 -/
lemma exact_of_postcomp_trivialKanFibration {A B C : SSet.{u}}
    [Quasicategory B] [Quasicategory C] (q : B ⟶ C) [TrivialKanFibration q]
    (F : A ⟶ B) [IsExactFunctor (F ≫ q)] : IsExactFunctor F where
  preservesZero x hx := (isZeroVertex_iff_map_of_trivialKanFibration q _).2
    (IsExactFunctor.preservesZero (F := F ≫ q) x hx)
  preservesCofiber t ht :=
    (isPushoutSquare_iff_postcomp_trivialKanFibration q (t.square ≫ F)).2
      (IsExactFunctor.preservesCofiber (F := F ≫ q) t ht)

namespace CofiberDiagrams
variable (X : SSet.{u}) [Quasicategory X] [IsStable X]

instance space_isStable : IsStable (space X) := isStable_of_trivialKanFibration (bottom X)

lemma lift_isExact {A : SSet.{u}} (a : A ⟶ (ihom (Δ[1] : SSet.{u})).obj X)
    [IsExactFunctor a] : IsExactFunctor (lift X a) := by
  have : IsExactFunctor (lift X a ≫ bottom X) := (lift_bottom X a).symm ▸ inferInstance
  exact exact_of_postcomp_trivialKanFibration (bottom X) (lift X a)

lemma lift_right_target {A : SSet.{u}} (a : A ⟶ (ihom (Δ[1] : SSet.{u})).obj X) :
    (lift X a ≫ right X) ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
      CofiberFamily.cofiber X a := by
  simp only [right, Category.assoc, stable_pre_evaluateFunctorAt]
  change (lift X a ≫ inclusion X) ≫ evaluateFunctorAt _ = _
  rw [lift_inclusion]
  rfl

end CofiberDiagrams

namespace CofiberFamily
variable (X : SSet.{u}) [Quasicategory X] [IsStable X]

lemma cofiber_isExact {A : SSet.{u}} (a : A ⟶ (ihom (Δ[1] : SSet.{u})).obj X)
    [IsExactFunctor a] : IsExactFunctor (cofiber X a) := by
  have := CofiberDiagrams.lift_isExact X a
  have h : IsExactFunctor ((CofiberDiagrams.lift X a ≫ CofiberDiagrams.right X) ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) := inferInstance
  rw [CofiberDiagrams.lift_right_target] at h
  exact h

end CofiberFamily
end SerrePositivity.KST.LocalizingInvariants
