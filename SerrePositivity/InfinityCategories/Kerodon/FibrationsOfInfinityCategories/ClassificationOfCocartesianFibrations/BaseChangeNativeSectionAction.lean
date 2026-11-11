module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.BaseChangeNativeObjectIso
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.BaseChangeNativeSections
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.NativeHomWhisker
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SectionsAction

/-!
概要：元の結合同型の豊穣射を section に作用させると、既存の結合比較成分になる。
方針：同じ相対豊穣合成を全パラメーターで評価し、既存の section 比較と照合する。
規約：通常の同型、core の豊穣射、既存の分類比較の同じ代表を保持する。
使われ方：元の結合共役の分類像と既存の Hom 輸送の同定。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 元の結合同型を表す同じ core の豊穣射の section 作用は、既存の結合比較成分。 -/
lemma cocartesianBaseChangeNativeObjectIso_sectionAction
    {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
    (l : A ⥤ D) (k : D ⥤ C) (p : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationCategory (nerve C)) (a : A) :
    (ρ_ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransport
      (pullback.fst (nerveMap l) (pullback.fst (nerveMap k) p.val.hom)) a)).inv ≫
      _ ◁ (eHomEquiv SSet.{u} (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeNativeObjectIso l k p).hom ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.cocartesianRelativeFunctorSpace
          (pullback.fst (nerveMap l) (pullback.fst (nerveMap k) p.val.hom))
          (pullback.fst (nerveMap (l ⋙ k)) p.val.hom))).ι) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSectionsAction (Over.mk (nerveMap (Under.forget a)))
        (Over.mk (pullback.fst (nerveMap l) (pullback.fst (nerveMap k) p.val.hom)))
        (Over.mk (pullback.fst (nerveMap (l ⋙ k)) p.val.hom)) =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeAssociativityComponent p.val.hom l k a).hom := by
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianSectionsι
    (pullback.fst (nerveMap (l ⋙ k)) p.val.hom) (nerveMap (Under.forget a)))).mp
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_injective
  have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeAssociativityComponent_native_uncurry p.val.hom l k a
    (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransport
      (pullback.fst (nerveMap l) (pullback.fst (nerveMap k) p.val.hom)) a))
  simp only [Category.id_comp] at hc
  refine Eq.trans ?_ hc.symm
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨x, s⟩
  change (((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorComposition (Over.mk (nerveMap (Under.forget a)))
    (Over.mk (pullback.fst (nerveMap l) (pullback.fst (nerveMap k) p.val.hom)))
    (Over.mk (pullback.fst (nerveMap (l ⋙ k)) p.val.hom))).app n
      (s.val, ((eHomEquiv SSet.{u} (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeNativeObjectIso l k p).hom).app
        n PUnit.unit).val.val)).val.app n (𝟙 n)) x = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeFunctorComposition_apply]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianNativeHomEquiv_apply (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeNativeObjectIso l k p).hom
    (𝟙 n) (s.val.val.app n (𝟙 n) x)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
