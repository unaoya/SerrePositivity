module

public import SerrePositivity.InfinityCategories.F2.Idempotent.CompletionBaseChange
public import SerrePositivity.InfinityCategories.F2.Idempotent.SliceComplete

/-!
概要：元の全部分圏による冪等完備化は、任意の図式の slice 上でも冪等完備化。
方針：元の slice 射影の右 fibration 性と、元の pullback の底変換定理を適用する。
規約：充満忠実な inner fibration の仮定を明示し、特に全部分複体の包含を扱う。
使われ方：HTT 5.1.4.4、Quillen A による cofinal 性の準備。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 元の冪等完備化の包含を、任意の元の slice へ引き戻しても冪等完備化。 -/
lemma IsIdempotentCompletion.sliceOver {C D K : SSet.{u}}
    [Quasicategory C] [Quasicategory D] (f : C ⟶ D) [InnerFibration f]
    (hf : IsIdempotentCompletion f) (p : K ⟶ D) :
    IsIdempotentCompletion (pullback.snd f (sliceOverProjection p)) :=
  IsIdempotentCompletion.pullback_rightFibration f hf (sliceOverProjection p)

end SerrePositivity.InfinityCategories.F2.Idempotent
