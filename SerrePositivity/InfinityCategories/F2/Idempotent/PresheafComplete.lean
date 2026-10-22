module

public import SerrePositivity.InfinityCategories.F2.Idempotent.IdemUniverse
public import SerrePositivity.InfinityCategories.F2.Idempotent.StrongSplittingExistence
public import SerrePositivity.InfinityCategories.F1.PresheafPointwiseColimits
public import SerrePositivity.InfinityCategories.F1B.KanLimitColimitOpposite

/-!
概要：元の前層 ∞ 圏の冪等完備性を小さい余極限から証明する。
方針：全 Idem の厳密な宇宙変更で元の図式を小さい底へ移し、余極限を戻して分裂する。
規約：元の前層図式全体の厳密な強い分裂を結論し、存在を入力に置かない。
使われ方：HTT 5.1.4 の前層内の retract 閉包による冪等完備化。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 元の前層圏の全 coherent 冪等図式は、同じ全図式の余極限を持つ。 -/
lemma presheafIdempotent_hasColimit {C : SSet.{u}}
    (d : CoherentIdempotent (PresheafInfinity C)) : HasColimit d :=
  (F1B.kanHasColimit_iff_restrict_of_isIso d (idemShapeUniverseIso.{u, u + 1}).hom).mpr
    (presheafInfinity_hasColimit _)

/-- 元の前層圏の全 coherent 冪等図式には、同じ全図式の厳密な強い分裂が存在する。 -/
lemma presheafIdempotent_strongSplitting {C : SSet.{u}}
    (d : CoherentIdempotent (PresheafInfinity C)) : Nonempty (StrongSplitting d) :=
  strongSplitting_exists_of_hasColimit d (presheafIdempotent_hasColimit d)

/-- 元の前層 ∞ 圏は冪等完備。 -/
lemma presheafInfinity_isIdempotentComplete (C : SSet.{u}) :
    IsIdempotentComplete (PresheafInfinity C) := presheafIdempotent_strongSplitting

end SerrePositivity.InfinityCategories.F2.Idempotent
