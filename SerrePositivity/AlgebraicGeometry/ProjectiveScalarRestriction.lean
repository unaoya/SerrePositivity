module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Algebra.Algebra.RestrictScalars

/-!
概要：KST §5、Stacks 05FS の積環の各因子に沿う射影加群のスカラー制限。
方針：代数の射影性を係数の直和へ広げ、元の射影加群の実分裂をスカラー制限する。
規約：元の環上射影的な代数にだけ適用する。
使われ方：局所化と完備化の二つの基底変更を積環上の射影加群へ戻す。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.AlgebraicGeometry

/--
概要：射影加群を係数とする任意の有限台関数の加群は射影的。
方針：係数加群の直和との標準線形同型で直和の射影性を移す。
規約：KST §5、Stacks 05FS、添字の有限性は要求しない。
使われ方：射影代数上の自由加群のスカラー制限。
-/
theorem projective_finsupp_of_projective
    (R S A : Type u) [CommRing R] [AddCommGroup S] [Module R S] [Module.Projective R S] :
    Module.Projective R (A →₀ S) := by
  classical
  exact Module.Projective.of_equiv' (finsuppLEquivDirectSum R S A).symm

/--
概要：元の環上射影的な代数の射影加群は、元の環上でも射影的。
方針：代数上の有限台自由加群への実分裂を元の環に制限する。
規約：KST §5、Stacks 05FS、代数・加群とも有限生成性を要求しない。
使われ方：積環の各因子の射影加群を積環上の射影加群へ移す。
-/
theorem projective_restrictScalars_of_projective_algebra
    (R S M : Type u) [CommRing R] [CommRing S] [Algebra R S] [Module.Projective R S]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    [Module.Projective S M] : Module.Projective R M := by
  let := projective_finsupp_of_projective R S M
  obtain ⟨e, he⟩ := Module.projective_def'.mp (inferInstance : Module.Projective S M)
  apply Module.Projective.of_split (e.restrictScalars R)
    ((Finsupp.linearCombination S (id : M → M)).restrictScalars R)
  exact congrArg (LinearMap.restrictScalars R) he

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
