module

public import SerrePositivity.InfinityCategories.F1.Joins.FiniteColimitSpanGeneration
public import SerrePositivity.InfinityCategories.Stable.FiniteOppositeSSet

/-!
概要：終対象と標準 cospan の極限から、全有限極限を生成する。
方針：反対 quasicategory の有限余極限生成を使い、元の全図式へ反転する。
規約：有限性と宇宙を変えず、引き戻しは元の標準ホーン図式として量化する。
使われ方：Ind と一般の quasicategory の有限極限存在の公開判定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 標的の厳密な同型は、指定図式の極限存在を保ち反映する。 -/
lemma hasLimit_iff_postcomp_isIso {K X Y : SSet.{u}} (p : K ⟶ X) (F : X ⟶ Y) [IsIso F] :
    HasLimit p ↔ HasLimit (p ≫ F) := by
  rw [F1B.kanHasLimit_iff_hasColimit_op, F1B.kanHasLimit_iff_hasColimit_op,
    SSet.opFunctor.map_comp]
  exact F1B.kanHasColimit_iff_postcomp_of_isIso _ _

/-- 反対側の全有限余極限から、元の全有限極限を回収する。 -/
lemma hasFiniteLimits_of_op_finiteColimits {X : SSet.{u}} [HasFiniteColimits X.op] :
    HasFiniteLimits X := by
  constructor
  intro K _ p
  exact (F1B.kanHasLimit_iff_hasColimit_op p).mpr (HasFiniteColimits.hasColimit _)

/-- 終対象と全引き戻しが存在すれば、全有限単体集合形状の極限が存在する。 -/
lemma hasFiniteLimits_of_terminal_pullbacks {X : SSet.{u}} [Quasicategory X]
    (t : X _⦋0⦌) (ht : IsTerminalVertex t)
    (hs : ∀ p : (horn 2 2 : SSet.{u}) ⟶ X, HasLimit p) : HasFiniteLimits X := by
  have : HasFiniteColimits X.op := hasFiniteColimits_of_initial_pushouts
    (SSet.opObjEquiv.symm t) ht.op_isInitialVertex (by
      intro p
      apply (F1B.kanHasColimit_iff_hasLimit_op p).mpr
      apply (hasLimit_iff_postcomp_isIso (SSet.opFunctor.map p)
        (SSet.opFunctorCompOpFunctorIso.app X).hom).mpr
      apply (F1B.kanHasLimit_iff_restrict_of_isIso
        (SSet.opFunctor.map p ≫ (SSet.opFunctorCompOpFunctorIso.app X).hom)
        (hornReverseIso 2 0).hom).mpr
      exact hs _)
  exact hasFiniteLimits_of_op_finiteColimits

end SerrePositivity.InfinityCategories
