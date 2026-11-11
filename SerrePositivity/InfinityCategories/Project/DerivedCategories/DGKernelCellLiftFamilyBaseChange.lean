module
public import Mathlib.CategoryTheory.Whiskering
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKernelCellLiftFamily
/-!
概要：一般の模型族の添字前合成を、結合子を明示した同じ指定比較で照合する。
方針：元の比較との可換性と全ての成分が恒等であることを証明する。
規約：関手レコードの暗黙の同定に依存しない。使われ方：模型族の図式制限の整合性。
-/
@[expose] public section
universe u v w z w₁ z₁
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet DifferentialGraded MonoidalClosed
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] (D E : Type v)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
local notation "DC" => _root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R D
local notation "EC" => _root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R E
def dgKernelCellLiftFamilyBaseChangeIso
    {C : Type w} [Category.{z} C] {C' : Type w₁} [Category.{z₁} C']
    (P : C ⥤ _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E D) (Q : C ⥤ _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R EC DC)
    (q : Q ⟶ P ⋙ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellRestrictionFunctor R D E)
    (hQ : ∀ X, _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R EC DC
      (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R EC DC (Q.obj X)))
    (hq : ∀ X, _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.quasiIso R EC DC (q.app X)) (H : C' ⥤ C) :
    H ⋙ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellLiftFamilyModelHomFunctor R D E P Q q hQ hq ≅
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellLiftFamilyModelHomFunctor R D E (H ⋙ P) (H ⋙ Q)
        (Functor.whiskerLeft H q) (fun X => hQ (H.obj X)) (fun X => hq (H.obj X)) :=
  (Functor.isoWhiskerLeft H (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellLiftFamilyHomIso R D E P Q q hQ hq)).symm ≪≫
    (Functor.associator H P (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor R D E)).symm ≪≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellLiftFamilyHomIso R D E (H ⋙ P) (H ⋙ Q) (Functor.whiskerLeft H q)
        (fun X => hQ (H.obj X)) (fun X => hq (H.obj X))
lemma dgKernelCellLiftFamilyBaseChangeIso_comparison
    {C : Type w} [Category.{z} C] {C' : Type w₁} [Category.{z₁} C']
    (P : C ⥤ _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E D) (Q : C ⥤ _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R EC DC)
    (q : Q ⟶ P ⋙ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellRestrictionFunctor R D E)
    (hQ : ∀ X, _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R EC DC
      (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R EC DC (Q.obj X)))
    (hq : ∀ X, _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.quasiIso R EC DC (q.app X)) (H : C' ⥤ C) :
    Functor.isoWhiskerLeft H (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellLiftFamilyHomIso R D E P Q q hQ hq) ≪≫
        dgKernelCellLiftFamilyBaseChangeIso R D E P Q q hQ hq H =
      (Functor.associator H P (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor R D E)).symm ≪≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellLiftFamilyHomIso R D E (H ⋙ P) (H ⋙ Q) (Functor.whiskerLeft H q)
          (fun X => hQ (H.obj X)) (fun X => hq (H.obj X)) := by
  simp only [dgKernelCellLiftFamilyBaseChangeIso, Iso.self_symm_id_assoc]
lemma dgKernelCellLiftFamilyBaseChangeIso_app
    {C : Type w} [Category.{z} C] {C' : Type w₁} [Category.{z₁} C']
    (P : C ⥤ _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E D) (Q : C ⥤ _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R EC DC)
    (q : Q ⟶ P ⋙ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellRestrictionFunctor R D E)
    (hQ : ∀ X, _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R EC DC
      (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R EC DC (Q.obj X)))
    (hq : ∀ X, _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.quasiIso R EC DC (q.app X)) (H : C' ⥤ C) (X : C') :
    (dgKernelCellLiftFamilyBaseChangeIso R D E P Q q hQ hq H).app X =
      Iso.refl ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellLiftFamilyModelHomFunctor R D E P Q q hQ hq).obj (H.obj X)) := by
  apply Iso.ext
  let e := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_cellModelLiftIso R D E
    (P.obj (H.obj X)) (Q.obj (H.obj X)) (q.app (H.obj X))
    (hQ (H.obj X)) (hq (H.obj X))
  change e.inv ≫ 𝟙 _ ≫ e.hom = 𝟙 _
  simp only [Category.id_comp, Iso.inv_hom_id]
end
end SerrePositivity.InfinityCategories.Project.DerivedCategories
