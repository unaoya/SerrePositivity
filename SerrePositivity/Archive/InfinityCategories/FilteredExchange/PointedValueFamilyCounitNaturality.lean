module
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoChainTransport

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedValueFamilyFactorPresentation
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorIsoSquareValueTransport
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.FunctorIsoWhiskerExchange
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoWhiskerUnit
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoWhiskerComposition
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorIsoChainTransport

/-!
概要：元の値比較の終点余単位因子は、元の任意の値同型に対して指定自然性を満たす。
方針：同じ指定余単位の交換正方形を元の実端点表示へ移し、同じ因子で共役する。
規約：指定余単位と同型を保持。使われ方：元の値比較の三因子の整理。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable (L : KanObject.{u}) {P : SSet.{u + 1}}
  {v v' : P ⟶ (SSet.uliftFunctor.{u + 1, u}).obj L.obj} (a : FunctorIso v v')
local notation "A" => CategoryTheory.Functor.obj SSet.uliftFunctor (KanObject.obj L)
local notation "V" => QCatEquivalence.hom
  (pointedSpaceFiberValueEquivalence (spaceInfinityVertex L))
local notation "R" => pointedRightFiberComparison L
local notation "C" => pointedValueRightComparison_counitIso (spaceInfinityVertex L)

/-- 元の終点余単位の二成分は、同じ値同型と元の右 Hom の往復の像で整合する。 -/
lemma pointedValueFamilyTargetCounitIso_naturality :
    (a.postcomp R).postcomp V ≪≫ pointedValueFamilyTargetCounitIso L v' =
      pointedValueFamilyTargetCounitIso L v ≪≫ a := by
  have hm : pointedValueRightComparison (spaceInfinityVertex L) ≫ V = R ≫ V := by
    rw [pointedValueRightComparison_standard]
  have hf := (heq_of_eq (functorIso_postcomp_postcomp a R V)).trans
    (functorIso_postcomp_heq_of_map_eq a hm)
  exact functorIso_square_of_heq
    (a.postcomp (pointedValueRightComparison (spaceInfinityVertex L) ≫ V))
    (FunctorIso.precomp C v') (FunctorIso.precomp C v) (a.postcomp (𝟙 A))
    ((a.postcomp R).postcomp V) (pointedValueFamilyTargetCounitIso L v')
    (pointedValueFamilyTargetCounitIso L v) a
    (by simp only [pointedValueRightComparison_standard, Category.assoc])
    (by simp only [pointedValueRightComparison_standard, Category.assoc])
    (Category.comp_id v) (Category.comp_id v') hf
    (pointedValueFamilyTargetCounitIso_heq_counit L v')
    (pointedValueFamilyTargetCounitIso_heq_counit L v)
    (heq_of_eq (functorIso_postcomp_id a).symm)
    (functorIso_whisker_exchange (Y := A) (Z := A) a C)

/-- 元の終点余単位を介する往復の像は、同じ値同型と同じ指定余単位の逆へ整理できる。 -/
lemma pointedValueFamilyTargetCounitIso_conjugation :
    (pointedValueFamilyTargetCounitIso L v).symm ≪≫ (a.postcomp R).postcomp V =
      a ≪≫ (pointedValueFamilyTargetCounitIso L v').symm := by
  calc
    _ = (pointedValueFamilyTargetCounitIso L v).symm ≪≫
        ((a.postcomp R).postcomp V ≪≫ pointedValueFamilyTargetCounitIso L v') ≪≫
          (pointedValueFamilyTargetCounitIso L v').symm := by
      simp only [Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl]
    _ = (pointedValueFamilyTargetCounitIso L v).symm ≪≫
        (pointedValueFamilyTargetCounitIso L v ≪≫ a) ≪≫
          (pointedValueFamilyTargetCounitIso L v').symm := by
      rw [pointedValueFamilyTargetCounitIso_naturality]
    _ = _ := by simp only [← Iso.trans_assoc, Iso.symm_self_id, Iso.refl_trans]

end SerrePositivity.InfinityCategories.F2
