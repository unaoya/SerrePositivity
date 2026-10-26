module
public import SerrePositivity.InfinityCategories.Derived.ClosureFunctoriality.ClosureFunctor
public import SerrePositivity.InfinityCategories.Derived.ClosureFunctoriality.SphereFree

/-!
概要：任意の dg 関手に沿う実加群延長に、基底非依存の閉包関手化を適用する。
方針：延長–制限随伴から必要な余極限保存を供給する。
規約：基底間の実同型互換のみを仮定する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (F : DGFunctor R C D)
  {T : Type u} [LinearOrder T] [WellFoundedLT T] [Nonempty T]
  (hT : ∀ s : ℕ → T, ∃ b, ∀ n, s n < b)
  (B : DGProjectiveModuleFamily R C) (E : DGProjectiveModuleFamily R D)
  (hB : ∀ i, ∃ j, Nonempty
    ((dgModuleExtension R C D F).onClosed.obj (B.2 i).val ≅ (E.2 j).val))

/-- D-3 の f_! 専用入口。φ と実比較同型を保持する。 -/
def dgModuleExtensionClosureFamilyImage :
    DGProjectiveFamilyImage R C D (dgModuleExtension R C D F)
      (dgProjectiveClosureFamily R C (T := T) B)
      (dgProjectiveClosureFamily R D (T := T) E) := by
  let : PreservesColimitsOfSize.{u, u} (dgModuleExtension R C D F).onClosed :=
    (dgModuleExtensionRestrictionAdjunction R C D F).leftAdjoint_preservesColimits
  exact dgProjectiveClosureFamilyImage R C D (dgModuleExtension R C D F) hT B E hB

/-- f_! の固定実代表間の全次数共役作用。 -/
def dgModuleExtensionClosureStrictImage :
    DGModuleStrictImage R C D (dgModuleExtension R C D F)
      (dgProjectiveFamilyObjects R C (dgProjectiveClosureFamily R C (T := T) B))
      (dgProjectiveFamilyObjects R D (dgProjectiveClosureFamily R D (T := T) E)) :=
  (dgModuleExtensionClosureFamilyImage R C D F hT B E hB).strictImage R C D _ _ _

/-- f_! を固定閉包の充満部分 dg 圏の間へ移した厳密関手。 -/
def dgModuleExtensionClosureFunctor :
    DGFunctor R
      {M // dgProjectiveFamilyObjects R C (dgProjectiveClosureFamily R C (T := T) B) M}
      {N // dgProjectiveFamilyObjects R D (dgProjectiveClosureFamily R D (T := T) E) N} :=
  (dgModuleExtensionClosureStrictImage R C D F hT B E hB).functor R C D _ _ _

end SerrePositivity.InfinityCategories
