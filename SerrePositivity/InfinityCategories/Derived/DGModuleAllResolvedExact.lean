module
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedLimitTransfer
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedZeroObjects
public import SerrePositivity.InfinityCategories.Derived.DGModuleFunctorExact
public import SerrePositivity.InfinityCategories.Derived.DGSemifreeProjectiveEquivalence

/-!
概要：全 dg 加群から実半自由出力への分解関手の完全性を供給する。
方針：生の dg 関手の cofiber 保存を pullback に直し、実分解へ移送する。
規約：Small 仮定は係数 dg 圏だけに置き、全加群圏には要求しない。
使われ方：D2 の G-1 e における全加群の実分解と完全関手の合成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
variable (R : Type u) [CommRing R] (D E : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]

/-- 全加群間の任意の dg 関手の、同じ実半自由出力分解は完全。 -/
theorem dgModuleAllResolvedFunctor_isExactFunctor
    (F : DGFunctor R (RightModule R D) (RightModule R E)) :
    IsExactFunctor (dgModuleResolvedInfinity R (RightModule R D) E F) where
  preservesZero := dgModuleResolvedInfinity_preservesZeroVertices R (RightModule R D) E F
  preservesCofiber t ht := by
    let := dgModuleDerivedInfinityCategory_isStable R E
    let := dgModuleFunctorNerve_isExactFunctor R D E F
    have h := IsExactFunctor.preservesCofiber (F := dgNerve.map F) t ht
    apply IsStable.pushout_of_pullback_square
    apply dgModuleResolvedInfinity_isPullbackSquare_of_raw R (RightModule R D) E F
    exact IsStable.pullback_of_pushout_square _ h

omit [DGCategory R E] [Small.{u} E] in
/-- 全加群から同じ実半自由分解への ∞ 関手は完全。 -/
theorem dgModuleResolutionInfinity_isExactFunctor :
    IsExactFunctor (dgModuleResolvedInfinity R (RightModule R D) D (DGFunctor.id _)) :=
  dgModuleAllResolvedFunctor_isExactFunctor R D D (DGFunctor.id _)

end SerrePositivity.InfinityCategories
