module

public import SerrePositivity.AlgebraicGeometry.MittagLefflerFaithfullyFlatDescent
public import SerrePositivity.AlgebraicGeometry.CountableFlatMittagLefflerProjective

/-!
概要：KST §5、Stacks 05A9・05FS の可算生成平坦加群の射影性の忠実平坦降下。
方針：射影性からの Mittag–Leffler 性を降下し、Noether 基底上の可算生成判定を使う。
規約：元の加群の平坦性を明示し、超限帰納法による一般形は使わない。
使われ方：有限型代数の射影性を局所化と完備化の忠実平坦被覆から得る。
-/

@[expose] public section
universe u
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct

/--
概要：Noether 基底上の可算生成平坦加群の射影性は忠実平坦な基底変更から降下する。
方針：基底変更後の射影性を Mittag–Leffler 性に移し、降下と可算生成判定を合成する。
規約：KST §5、Stacks 05A9 の本レーンに必要な特殊形。拡張環の Noether 性は不要。
使われ方：05FS の平坦有限型代数の射影性の存在。
-/
theorem projective_of_countable_flat_of_faithfullyFlat
    (R T M : Type u) [CommRing R] [IsNoetherianRing R]
    [CommRing T] [Algebra R T] [Module.FaithfullyFlat R T]
    [AddCommGroup M] [Module R M] [Module.Flat R M]
    [Module.Projective T (T ⊗[R] M)] (hcount : HasCountableGeneratingSet R M) :
    Module.Projective R M :=
  projective_of_countable_flat_mittagLeffler hcount
    (isModuleMittagLeffler_of_faithfullyFlat R T M
      (isModuleMittagLeffler_of_projective T (T ⊗[R] M)))

/--
概要：Noether 基底の有限型代数上有限な平坦加群の射影性は忠実平坦な基底変更から降下する。
方針：有限型代数上有限な加群の可算生成性を、忠実平坦降下の判定へ渡す。
規約：KST §5、Stacks 05A9・05FS、元の加群は基礎環上平坦。
使われ方：一般の幾何学的整な代数の射影性の忠実平坦被覆。
-/
theorem projective_of_finiteType_finite_flat_of_faithfullyFlat
    (R B T M : Type u) [CommRing R] [IsNoetherianRing R]
    [CommRing B] [Algebra R B] [Algebra.FiniteType R B]
    [CommRing T] [Algebra R T] [Module.FaithfullyFlat R T]
    [AddCommGroup M] [Module R M] [Module B M] [IsScalarTower R B M]
    [Module.Finite B M] [Module.Flat R M] [Module.Projective T (T ⊗[R] M)] :
    Module.Projective R M :=
  projective_of_countable_flat_of_faithfullyFlat R T M
    (hasCountableGeneratingSet_of_finiteType_finite R B M)

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
