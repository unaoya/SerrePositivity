module
public import SerrePositivity.InfinityCategories.Derived.DGKernelCellModel
public import SerrePositivity.InfinityCategories.Derived.DGKernelTargetModelInfinity
/-!
概要：任意の元の kernel の実作用を、両端の cell 分解上の指定半自由 kernel の作用へ比較する。
方針：同じ入力 graph 比較と出力 augmentation の全関手比較を、指定入力逆で合成する。
規約：原 Hom の平坦性・原出力の射影性・追加の模型選択を仮定しない。
使われ方：元の一般 kernel の導来合成を平坦模型上で計算する。
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
/-- 両端を分解した指定 kernel の作用と元の出力 graph の延長は、元の始域制限作用と同型。 -/
def dgKernelCellModel_targetIso (P : Bimodule R E D) :
    FunctorIso
      (dgKernelDerivedInfinity R (DGCategoryCellResolution.Source R D)
        (DGCategoryCellResolution.Source R E)
        (BimoduleCategory.underlying R _ _ (dgKernelCellModel R D E P)) ≫
          (dgCellModuleSourceEquivalence R E).hom)
      (dgKernelDerivedInfinity R (DGCategoryCellResolution.Source R D) E
        ((DGCategoryCellResolution.augmentation R D).comp P)) := by
  let ρ := dgKernelCellResolution R D E P
  exact dgKernelDerivedInfinity_targetModelIso R (DGCategoryCellResolution.Source R D)
    (DGCategoryCellResolution.Source R E) E (DGCategoryCellResolution.augmentation R E)
    (BimoduleCategory.of R E (DGCategoryCellResolution.Source R D)
      ((DGCategoryCellResolution.augmentation R D).comp P))
    (dgKernelCellModel R D E P) ρ.π
    (DGCategoryCellResolution.augmentation_quasiEquivalence R E)
    (dgKernelCellModel_rightRelativeKFlat R D E P) ρ.quasiIso
/-- 元の一般 kernel の実作用は、指定入力逆・指定平坦模型の実作用・指定出力同値の合成と同型。 -/
def dgKernelDerivedInfinity_cellModelIso (P : Bimodule R E D) :
    FunctorIso (dgKernelDerivedInfinity R D E P)
      ((dgCellModuleSourceEquivalence R D).inv ≫
        dgKernelDerivedInfinity R (DGCategoryCellResolution.Source R D)
          (DGCategoryCellResolution.Source R E)
          (BimoduleCategory.underlying R _ _ (dgKernelCellModel R D E P)) ≫
            (dgCellModuleSourceEquivalence R E).hom) :=
  dgKernelDerivedInfinity_cellSourceIso R D E P ≪≫
    FunctorIso.precomp (dgKernelCellModel_targetIso R D E P).symm
      (dgCellModuleSourceEquivalence R D).inv
end SerrePositivity.InfinityCategories
