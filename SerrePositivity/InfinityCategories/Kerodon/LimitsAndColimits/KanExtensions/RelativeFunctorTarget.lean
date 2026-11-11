module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeBoundaryTarget

/-!
概要：単射に沿う相対関手制限の標的は一般 U 上でも quasicategory。
方針：前合成の inner 性を第一射影へ引き戻す。
規約：U の inner 性は不要、添字の射は単射とする。
使われ方：一般 U の元の相対制限と path 置換上の制限の比較。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：単射に沿う相対内部 Hom の標的は一般 U に対して quasicategory。
方針：前合成は inner fibration なので、その引き戻しである第一射影も inner。
規約：標的 D と E のみ quasicategory とする。
使われ方：isofibration 仮定を外す写像空間比較の標的。 -/
lemma kanRelativeInternalHomTarget_quasicategory_of_mono {A B D E : SSet.{u}}
    [Quasicategory D] [Quasicategory E] (U : D ⟶ E)
    (i : A ⟶ B) [Mono i] (s : internalHom.PullbackObjObj i U) : Quasicategory s.pt := by
  have : InnerFibration s.fst :=
    ⟨innerFibrations.of_isPullback s.isPullback.flip
      (InnerFibration.mem (q := (pre i).app E))⟩
  have : Quasicategory ((internalHom.obj (Opposite.op A)).obj D) :=
    inferInstanceAs (Quasicategory ((ihom A).obj D))
  exact quasicategory_of_innerFibration s.fst

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
