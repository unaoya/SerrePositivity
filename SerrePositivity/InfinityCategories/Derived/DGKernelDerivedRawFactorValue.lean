module
public import SerrePositivity.InfinityCategories.Derived.DGKernelDerivedHomRawFactor
/-!
概要：指定された全関手射の制限と比較を、元の値を保って照合する。
方針：同じ端点・全関手圏の作用・実包含後の一致を使う。
規約：射の可逆性と追加の平坦性は不要。使われ方：ξ と κ の全射自然性。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet MonoidalClosed DifferentialGraded DGNerve
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] (D E : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
lemma dgKernelDerivedRawFactorIso_heq (P : BimoduleCategory R E D) :
    HEq (dgKernelDerivedRawFactorIso R D E P)
      (dgModuleResolvedInfinity_rawFactorIso R (SemifreeDGModules R D) E
        (dgSemifreeKernelModuleDG R D E (BimoduleCategory.underlying R E D P))) := by
  rfl
end
end SerrePositivity.InfinityCategories
