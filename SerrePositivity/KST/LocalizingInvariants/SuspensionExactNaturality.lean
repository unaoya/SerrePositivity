module

public import SerrePositivity.KST.LocalizingInvariants.CofiberZeroTargetComparison
public import SerrePositivity.KST.LocalizingInvariants.CofiberExactNaturality

/-!
概要：選んだ全単体上の suspension は任意の完全関手と関手同型で可換する。
方針：cofiber の完全関手に関する比較と零終点矢印の始点評価を合成する。
規約：h 圏だけの可換性に弱めない。使われ方：商関手の後の shift の移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.SuspensionExact
variable {X Y : SSet.{u}} [Quasicategory X] [IsStable X]
  [Quasicategory Y] [IsStable Y] (F : X ⟶ Y) [IsExactFunctor F]

omit [Quasicategory Y] [IsStable Y] in
lemma post_arrow_zero_target (x : X _⦋0⦌) : IsZeroTargetArrow
    ((arrow X ≫ (ihom (Δ[1] : SSet.{u})).map F).app (Opposite.op ⦋0⦌) x) := by
  change IsZeroVertex (((arrow X ≫ (ihom (Δ[1] : SSet.{u})).map F) ≫
    evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2))).app (Opposite.op ⦋0⦌) x)
  rw [Category.assoc, arrowMap_evaluation, ← Category.assoc]
  exact IsExactFunctor.preservesZero (F := F) _ (arrow_zero_target X x)

omit [Quasicategory Y] [IsStable Y] [IsExactFunctor F] in
lemma post_arrow_source :
    (arrow X ≫ (ihom (Δ[1] : SSet.{u})).map F) ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) = F := by
  rw [Category.assoc, arrowMap_evaluation, ← Category.assoc, arrow_source, Category.id_comp]

def exactNaturality : FunctorIso (map X ≫ F) (F ≫ map Y) := by
  let b := arrow X ≫ (ihom (Δ[1] : SSet.{u})).map F
  have h : FunctorIso (map X ≫ F) (b ≫ CofiberFamily.cofiber Y (𝟙 _)) := by
    simpa only [map, b, Category.assoc] using
      FunctorIso.precomp (CofiberFamily.exactNaturality F) (arrow X)
  have e := (CofiberFamily.compositionIso Y b).symm ≪≫
    cofiberZeroTargetIso Y b (post_arrow_zero_target F)
  rw [post_arrow_source] at e
  exact h ≪≫ e

end SerrePositivity.KST.LocalizingInvariants.SuspensionExact
