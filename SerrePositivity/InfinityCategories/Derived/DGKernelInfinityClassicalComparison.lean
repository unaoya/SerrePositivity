module
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedClassicalComparison
public import SerrePositivity.InfinityCategories.Derived.DGKernelClassicalComparison
/-!
概要：元の一般 kernel ∞ 関手の通常の h 上の作用を、既存の導来 tensor へ照合する。
方針：同じ実出力分解の比較と実 augmentation の主導来比較を合成する。
規約：元の出力の射影性・局所 Hom 平坦性を仮定しない。使われ方：一般 RHom の ∞ 随伴。
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
/-- 同じ実 kernel ∞ 関手の通常の h と古典的導来 tensor の全関手比較。 -/
def dgKernelDerivedInfinity_classicalIso (P : Bimodule R E D) :
    (hoFunctor.map (dgKernelDerivedInfinity R D E P)).toFunctor ⋙
      (dgStableHomotopyEquivalence R (SemifreeDGModules R E)).functor ⋙
        dgSemifreeModuleToDerived R E ≅
    (dgStableHomotopyEquivalence R (SemifreeDGModules R D)).functor ⋙
      dgSemifreeModuleToDerived R D ⋙ Morita.kernelDerivedTensorOnBimodule R D E P :=
  dgModuleResolvedInfinity_classicalIso R (SemifreeDGModules R D) E
      (dgSemifreeKernelModuleDG R D E P) ≪≫
    Functor.isoWhiskerLeft
      (dgStableHomotopyEquivalence R (SemifreeDGModules R D)).functor
      (dgKernelOutputResolutionClassicalComparisonIso R D E P ≪≫ Functor.associator _ _ _)
end SerrePositivity.InfinityCategories
