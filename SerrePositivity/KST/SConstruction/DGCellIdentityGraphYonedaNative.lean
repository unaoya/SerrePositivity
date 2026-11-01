module
public import SerrePositivity.KST.SConstruction.DGCellResolvedGraphNativeAugmentation
public import SerrePositivity.KST.SConstruction.DGFunctorCoherence
public import SerrePositivity.DifferentialGraded.Bimodule.DiagonalRestriction
public import SerrePositivity.InfinityCategories.Derived.DGBimoduleResolvedMapInvertible
public import SerrePositivity.InfinityCategories.Core.FunctorIsoTransport
/-!
概要：元 cell 増大の全 Hom 写像で元 Yoneda と恒等制限 graph を全比較する。
方針：D 正本の対角制限射とその準同型判定を native 全関手射へ適用する。
規約：元増大・元 Hom 写像と同じ全自然性を保持し、補題を複製しない。
使われ方：元実逆回転全比較を同じ resolved 射影へ戻す。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (B : Type (max (u + 1) v))
  [DGCategory R B] [Small.{u} B]
local notation "P" => DGCategoryCellResolution.Source R B
local notation "α" => DGCategoryCellResolution.augmentation R B
local notation "ρ" => dgModuleResolvedInfinity R (RightModule R (P)) (P)
  (DGFunctor.id (RightModule R (P)))

/-- 概要：元 cell 増大の対角比較は同じ恒等制限 graph への native 全関手同型。
方針：元対角制限射の全比較を準同型反転し、恒等 graph の全端点だけ回収する。
規約：新しい実比較射を選ばない。使われ方：元増大後の実逆回転比較の射影回収。 -/
def dgCellIdentityGraphYonedaNativeComparison :
    FunctorIso (dgNerve.map (dgYoneda R (P)) ≫ (ρ))
      (dgNerve.map (dgCellRestrictedGraphModuleFunctor R B (DGFunctor.id B)) ≫ (ρ)) := by
  let f := Bimodule.diagonalRestrictionMap R (P) B (α)
  have hf : BimoduleCategory.quasiIso R (P) (P) f :=
    (Bimodule.diagonalRestrictionMap_quasiIso_iff R (P) B (α)).mpr
      (DGCategoryCellResolution.augmentation_quasiEquivalence R B).1
  let t := functorHomPostcomp
    (dgNerve.map (BimoduleCategory.underlying R (P) (P)
      (BimoduleCategory.of R (P) (P) (Bimodule.diagonal R (P)))))
    (dgNerve.map (BimoduleCategory.underlying R (P) (P)
      ((BimoduleCategory.pairedRestrictionFunctor R B B (P) (P) (α) (α)).obj
        (BimoduleCategory.of R B B (Bimodule.diagonal R B)))))
    (ρ) ((dgBimoduleFunctorHomFunctor R (P) (P)).map f)
  haveI : IsIso t :=
    dgBimoduleFunctorHomFunctor_resolvedMap_isIso_of_quasiIso.{u, max (u + 1) v}
      R (P) (P) f hf
  let e := asIso t
  have hg : functorGraph R B B (DGFunctor.id B) = Bimodule.diagonal R B :=
    strictDGFunctor_id_comp (dgYoneda R B)
  have ht := congrArg (fun K =>
    (BimoduleCategory.pairedRestrictionFunctor R B B (P) (P) (α) (α)).obj
      (BimoduleCategory.of R B B K)) hg
  exact F2.functorIsoOfEq e rfl (congrArg (fun K =>
    dgNerve.map (BimoduleCategory.underlying R (P) (P) K) ≫ (ρ)) ht.symm)
end SerrePositivity.KST.SConstruction
