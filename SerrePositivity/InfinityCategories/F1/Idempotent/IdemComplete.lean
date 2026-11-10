module

public import SerrePositivity.InfinityCategories.Core.Cocone
public import SerrePositivity.InfinityCategories.HTT.RetractsAndIdempotentCompletion.RetractClosure
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafInfinity
public import SerrePositivity.InfinityCategories.Core.Idempotent.Coherent
public import SerrePositivity.InfinityCategories.Core.Idempotent.FullSubcomplexSplitting
public import SerrePositivity.InfinityCategories.F1.Idempotent.PresheafClosure
public import SerrePositivity.InfinityCategories.F1.Idempotent.PresheafComplete
public import SerrePositivity.InfinityCategories.F1.Idempotent.StrongSplittingColimit
public import SerrePositivity.InfinityCategories.Core.Idempotent.Walking

/-!
概要：元の前層圏内の Yoneda 像の retract 閉包 Idem(C) は冪等完備。
方針：証明済みの前層圏の冪等完備性と、元の閉包の retract 閉性を使って強い分裂を戻す。
規約：普遍性は別工程で証明する。元の全図式の強い分裂を厳密に回収する。
使われ方：HTT 5.1.4.2 の冪等完備化の対象構成の完結。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 元の前層内の Yoneda 像の retract 閉包は、元の coherent な意味で冪等完備。 -/
lemma idem_isIdempotentComplete (C : SSet.{u}) [Quasicategory C] :
    IsIdempotentComplete (Idem C) :=
  fullSubcomplex_isIdempotentComplete IsRetractPresheaf
    (fun h hG ↦ isRetractPresheaf_of_retract h hG)
    (presheafInfinity_isIdempotentComplete C)

/-- 元の Idem(C) 内の任意の全冪等図式は、同じ全図式の余極限を持つ。 -/
lemma idemIdempotent_hasColimit {C : SSet.{u}} [Quasicategory C]
    (d : CoherentIdempotent (Idem C)) : HasColimit d :=
  (idem_isIdempotentComplete C).hasColimit d

end SerrePositivity.InfinityCategories.F2.Idempotent
