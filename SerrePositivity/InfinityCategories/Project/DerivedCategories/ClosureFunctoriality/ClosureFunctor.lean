module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.FullFunctor
public import SerrePositivity.DifferentialGraded.Module.Functor

/-!
概要：互換な任意の射影的基底から、閉包代表の充満部分 dg 圏間の実関手を構成。
方針：段階帰納で得た添字 φ と比較同型を、同じ代表の部分圏へ移す。
規約：既存の閉包・cone 入力を変更しない。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality
open CategoryTheory Limits DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D]

/-- 固定族の実加群の像集合。全同型コピーは追加しない。 -/
def dgProjectiveFamilyObjects (B : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGProjectiveModuleFamily R C) : Set (ModuleCategory R C) :=
  Set.range (fun i => (B.2 i).val)

variable (F : DGFunctor R (RightModule R C) (RightModule R D))
  (B : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGProjectiveModuleFamily R C) (E : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGProjectiveModuleFamily R D)

/-- 添字付き比較を、重複を除いた実代表の充満部分圏へ送る。 -/
def DGProjectiveFamilyImage.strictImage (I : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.DGProjectiveFamilyImage R C D F B E) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.DGModuleStrictImage R C D F (dgProjectiveFamilyObjects R C B)
      (dgProjectiveFamilyObjects R D E) where
  obj M := ⟨(E.2 (I.index M.property.choose)).val, ⟨_, rfl⟩⟩
  iso M := F.onClosed.mapIso (eqToIso M.property.choose_spec.symm) ≪≫
    I.iso M.property.choose

variable [PreservesColimitsOfSize.{u, u} F.onClosed]
  {T : Type u} [LinearOrder T] [WellFoundedLT T] [Nonempty T]
  (hT : ∀ s : ℕ → T, ∃ b, ∀ n, s n < b)
  (hB : ∀ i, ∃ j, Nonempty (F.onClosed.obj (B.2 i).val ≅ (E.2 j).val))

/-- D-3 の基底非依存入口：固定閉包の充満部分圏間の厳密 dg 関手。 -/
def dgProjectiveClosureFunctor :
    DGFunctor R
      {M // dgProjectiveFamilyObjects R C (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveClosureFamily R C (T := T) B) M}
      {N // dgProjectiveFamilyObjects R D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveClosureFamily R D (T := T) E) N} :=
  let I := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.dgProjectiveClosureFamilyImage R C D F hT B E hB
  (I.strictImage R C D F _ _).functor R C D F _ _

end SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality
