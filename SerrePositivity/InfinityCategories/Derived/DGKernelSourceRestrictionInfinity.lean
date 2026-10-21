module
public import SerrePositivity.InfinityCategories.Derived.DGKernelSourceGraphBimoduleIso
public import SerrePositivity.InfinityCategories.Derived.DGKernelBimoduleIso
/-!
概要：graph による入力変更と一般 kernel の実作用を、元の始域制限 kernel へ同定する。
方針：全 Hom 自然な co-Yoneda の実同型を、同じ出力分解へ送る。
規約：元の kernel と dg 圏に平坦性を追加しない。
使われ方：cell 分解上での一般 kernel の実作用の計算。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
variable (R : Type u) [CommRing R] (C D E : Type v)
  [DGCategory R C] [Small.{u} C] [DGCategory R D] [Small.{u} D]
  [DGCategory R E] [Small.{u} E]
/-- graph による入力変更と元の kernel の作用は、元の始域制限 kernel の実作用と全関手同型。 -/
def dgKernelDerivedInfinity_sourceRestrictionIso (F : DGFunctor R C D)
    (P : Bimodule R E D) :
    FunctorIso (dgModuleExtensionInfinity R C D F ≫ dgKernelDerivedInfinity R D E P)
      (dgKernelDerivedInfinity R C E (F.comp P)) :=
  dgKernelDerivedInfinity_sourceGraphIso R C D E F P ≪≫
    dgKernelDerivedInfinity_bimoduleIso R C E (dgKernelSourceGraphBimoduleIso R C D E F P)
end SerrePositivity.InfinityCategories
