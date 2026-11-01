module
public import SerrePositivity.InfinityCategories.Derived.DGKernelCellComposite
public import SerrePositivity.InfinityCategories.Core.FunctorIsoWhiskerComposition
/-!
概要：任意の二 kernel の元の実作用の合成を、指定平坦模型の通常合成の作用へ比較する。
方針：同じ指定模型、実加群圏の比較同型と右相対 K-flat 時の実導来合成を使う。
規約：元の kernel と Hom の平坦性・出力の射影性を仮定しない。
使われ方：一般 kernel の合成と全 coherence。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
variable (R : Type u) [CommRing R] (D E K : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
  [DGCategory R K] [Small.{u} K]
/-- 元の任意二 kernel の実作用の合成は、指定平坦模型の通常合成の実作用と全関手同型。 -/
def dgKernelDerivedInfinity_compositionCellIso
    (P : Bimodule R E D) (Q : Bimodule R K E) :
    FunctorIso (dgKernelDerivedInfinity R D E P ≫ dgKernelDerivedInfinity R E K Q)
      ((dgCellModuleSourceEquivalence R D).inv ≫
        dgKernelDerivedInfinity R (DGCategoryCellResolution.Source R D)
          (DGCategoryCellResolution.Source R K) (dgKernelCellComposite R D E K P Q) ≫
            (dgCellModuleSourceEquivalence R K).hom) := by
  let eD := dgCellModuleSourceEquivalence R D
  let eE := dgCellModuleSourceEquivalence R E
  let eK := dgCellModuleSourceEquivalence R K
  let A := dgKernelDerivedInfinity R (DGCategoryCellResolution.Source R D)
    (DGCategoryCellResolution.Source R E)
    (BimoduleCategory.underlying R _ _ (dgKernelCellModel R D E P))
  let B := dgKernelDerivedInfinity R (DGCategoryCellResolution.Source R E)
    (DGCategoryCellResolution.Source R K)
    (BimoduleCategory.underlying R _ _ (dgKernelCellModel R E K Q))
  let C := dgKernelDerivedInfinity R (DGCategoryCellResolution.Source R D)
    (DGCategoryCellResolution.Source R K) (dgKernelCellComposite R D E K P Q)
  have a : FunctorIso
      (dgKernelDerivedInfinity R D E P ≫ dgKernelDerivedInfinity R E K Q)
      ((eD.inv ≫ A ≫ eE.hom) ≫ (eE.inv ≫ B ≫ eK.hom)) :=
    (dgKernelDerivedInfinity_cellModelIso R D E P).postcomp
      (dgKernelDerivedInfinity R E K Q) ≪≫
      (dgKernelDerivedInfinity_cellModelIso R E K Q).precomp (eD.inv ≫ A ≫ eE.hom)
  have b : FunctorIso
      ((eD.inv ≫ A ≫ eE.hom) ≫ (eE.inv ≫ B ≫ eK.hom))
      (eD.inv ≫ A ≫ B ≫ eK.hom) := by
    have h := FunctorIso.precomp (eE.homInvIso.postcomp (B ≫ eK.hom)) (eD.inv ≫ A)
    simpa only [Category.assoc, Category.id_comp] using! h
  have t : FunctorIso (A ≫ B) C :=
    dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R
      (DGCategoryCellResolution.Source R D) (DGCategoryCellResolution.Source R E)
      (DGCategoryCellResolution.Source R K)
      (BimoduleCategory.underlying R _ _ (dgKernelCellModel R D E P))
      (BimoduleCategory.underlying R _ _ (dgKernelCellModel R E K Q))
      (dgKernelCellModel_rightRelativeKFlat R D E P)
  have c : FunctorIso (eD.inv ≫ A ≫ B ≫ eK.hom) (eD.inv ≫ C ≫ eK.hom) := by
    have h := (t.postcomp eK.hom).precomp eD.inv
    simpa only [Category.assoc] using! h
  exact a ≪≫ b ≪≫ c
end SerrePositivity.InfinityCategories
