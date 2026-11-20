module

public import SerrePositivity.AlgebraicGeometry.FreeStalkRankBaseChange
public import Mathlib.RingTheory.Localization.AtPrime.Extension

/-!
概要：KST §5、Stacks 0810・0811 の任意の局所化による自由 locus の照合。
方針：局所化先の素点局所環を元の環の素点局所環としても使い、テンソル取消で自由性を比較する。
規約：有限性や加群の平坦性は要求しない。
使われ方：境界外の相対平坦性から得た一般点での自由性を元の代数へ戻す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct

variable {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M]

/--
概要：局所化先の素点での基底変更加群の自由性は、縮約素点での元の加群の自由性と同値。
方針：二段局所化で同じ局所環を使い、二段テンソルの取消同型で自由性を運ぶ。
規約：KST §5、Stacks 0810・0811、局所化環は標準実装に限定しない。
使われ方：境界外の基底変更から元の自由 locus への所属を得る。
-/
theorem mem_freeLocus_baseChange_iff_of_isLocalization (T : Submonoid R)
    [IsLocalization T S] (Q : PrimeSpectrum S) :
    Q ∈ Module.freeLocus S (S ⊗[R] M) ↔
      Q.comap (algebraMap R S) ∈ Module.freeLocus R M := by
  let L := Localization.AtPrime Q.asIdeal
  let φ : R →+* L := (algebraMap S L).comp (algebraMap R S)
  let : Algebra R L := φ.toAlgebra
  let : Module R L := φ.toAlgebra.toModule
  let : @IsScalarTower R S L (inferInstance : Algebra R S).toSMul
      (inferInstance : Algebra S L).toSMul (inferInstance : Algebra R L).toSMul :=
    IsScalarTower.of_algebraMap_eq' (R := R) (S := S) (A := L) rfl
  let : IsLocalization.AtPrime L (Q.comap (algebraMap R S)).asIdeal :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization T (T := L) Q.asIdeal
  rw [Module.mem_freeLocus_iff_tensor Q L,
    Module.mem_freeLocus_iff_tensor (Q.comap (algebraMap R S)) L]
  exact Module.Free.iff_of_equiv
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R S L L M)

/--
概要：局所化先の基底変更加群の自由 locus は元の自由 locus の逆像。
方針：各素点で同じ局所環を使う自由性の同値を集合の等式にする。
規約：KST §5、Stacks 0810・0811、環や加群の有限性は不要。
使われ方：局所化先で得た自由な開部分を元の自由 locus と照合する。
-/
theorem freeLocus_baseChange_of_isLocalization (T : Submonoid R) [IsLocalization T S] :
    Module.freeLocus S (S ⊗[R] M) =
      (PrimeSpectrum.comap (algebraMap R S)) ⁻¹' Module.freeLocus R M := by
  ext Q
  exact mem_freeLocus_baseChange_iff_of_isLocalization T Q

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
