module
public import SerrePositivity.InfinityCategories.Derived.DGKernelSourceRestrictionInfinity
public import SerrePositivity.InfinityCategories.Derived.CellDGResolutionNerve
public import SerrePositivity.InfinityCategories.Derived.DGModuleMoritaInfinity
/-!
概要：元の一般 kernel の実作用を、cell 分解上の作用と指定入力同値の逆へ比較する。
方針：cell 増大の実加群 ∞ 同値と、同じ graph 始域制限比較を使う。
規約：元の dg 圏に局所 Hom 平坦性を追加しない。
使われ方：一般導来合成の入力模型移送。
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
/-- cell 増大の実延長を順方向に持つ、実導来加群 ∞ 圏の同値。 -/
def dgCellModuleSourceEquivalence :
    QCatEquivalence
      (dgModuleDerivedInfinityCategory R (DGCategoryCellResolution.Source R D))
      (dgModuleDerivedInfinityCategory R D) :=
  (dgModuleExtensionInfinity_isQCatEquivalence_of_quasiEquivalence R
    (DGCategoryCellResolution.Source R D) D (DGCategoryCellResolution.augmentation R D)
    (DGCategoryCellResolution.augmentation_quasiEquivalence R D)).choose
/-- 指定入力同値の順方向は元の cell 増大の実延長そのもの。 -/
lemma dgCellModuleSourceEquivalence_hom :
    (dgCellModuleSourceEquivalence R D).hom =
      dgModuleExtensionInfinity R (DGCategoryCellResolution.Source R D) D
        (DGCategoryCellResolution.augmentation R D) := rfl
/-- 元の一般 kernel の実作用を、同じ cell 増大と指定入力逆で比較する。 -/
def dgKernelDerivedInfinity_cellSourceIso (P : Bimodule R E D) :
    FunctorIso (dgKernelDerivedInfinity R D E P)
      ((dgCellModuleSourceEquivalence R D).inv ≫
        dgKernelDerivedInfinity R (DGCategoryCellResolution.Source R D) E
          ((DGCategoryCellResolution.augmentation R D).comp P)) := by
  let e := dgCellModuleSourceEquivalence R D
  let K := dgKernelDerivedInfinity R D E P
  have a := dgKernelDerivedInfinity_sourceRestrictionIso R
    (DGCategoryCellResolution.Source R D) D E (DGCategoryCellResolution.augmentation R D) P
  have b := (FunctorIso.postcomp e.invHomIso K).symm
  have c := a.precomp e.inv
  simpa only [Category.assoc, Category.id_comp] using! (b ≪≫ c)
end SerrePositivity.InfinityCategories
