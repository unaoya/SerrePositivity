module

public import SerrePositivity.InfinityCategories.F1.CocartesianBaseChangeNativeObjectIso
public import SerrePositivity.InfinityCategories.F1.CocartesianBaseChangeNativeSections
public import SerrePositivity.InfinityCategories.F1.CocartesianNativeHomWhisker
public import SerrePositivity.InfinityCategories.F1.CocartesianSectionsAction

/-!
概要：元の結合同型の豊穣射を section に作用させると、既存の結合比較成分になる。
方針：同じ相対豊穣合成を全パラメーターで評価し、既存の section 比較と照合する。
規約：通常の同型、core の豊穣射、既存の分類比較の同じ代表を保持する。
使われ方：元の結合共役の分類像と既存の Hom 輸送の同定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
namespace SerrePositivity.InfinityCategories

/-- 元の結合同型を表す同じ core の豊穣射の section 作用は、既存の結合比較成分。 -/
lemma cocartesianBaseChangeNativeObjectIso_sectionAction
    {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
    (l : A ⥤ D) (k : D ⥤ C) (p : CocartesianFibrationCategory (nerve C)) (a : A) :
    (ρ_ (kanCocartesianStrictTransport
      (pullback.fst (nerveMap l) (pullback.fst (nerveMap k) p.val.hom)) a)).inv ≫
      _ ◁ (eHomEquiv SSet.{u} (cocartesianBaseChangeNativeObjectIso l k p).hom ≫
        (quasicategoryCore (cocartesianRelativeFunctorSpace
          (pullback.fst (nerveMap l) (pullback.fst (nerveMap k) p.val.hom))
          (pullback.fst (nerveMap (l ⋙ k)) p.val.hom))).ι) ≫
      cocartesianSectionsAction (Over.mk (nerveMap (Under.forget a)))
        (Over.mk (pullback.fst (nerveMap l) (pullback.fst (nerveMap k) p.val.hom)))
        (Over.mk (pullback.fst (nerveMap (l ⋙ k)) p.val.hom)) =
    (cocartesianBaseChangeAssociativityComponent p.val.hom l k a).hom := by
  apply (cancel_mono (kanCocartesianSectionsι
    (pullback.fst (nerveMap (l ⋙ k)) p.val.hom) (nerveMap (Under.forget a)))).mp
  apply relativeFunctorUncurry_injective
  have hc := cocartesianBaseChangeAssociativityComponent_native_uncurry p.val.hom l k a
    (𝟙 (kanCocartesianStrictTransport
      (pullback.fst (nerveMap l) (pullback.fst (nerveMap k) p.val.hom)) a))
  simp only [Category.id_comp] at hc
  refine Eq.trans ?_ hc.symm
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨x, s⟩
  change (((relativeFunctorComposition (Over.mk (nerveMap (Under.forget a)))
    (Over.mk (pullback.fst (nerveMap l) (pullback.fst (nerveMap k) p.val.hom)))
    (Over.mk (pullback.fst (nerveMap (l ⋙ k)) p.val.hom))).app n
      (s.val, ((eHomEquiv SSet.{u} (cocartesianBaseChangeNativeObjectIso l k p).hom).app
        n PUnit.unit).val.val)).val.app n (𝟙 n)) x = _
  rw [relativeFunctorComposition_apply]
  exact cocartesianNativeHomEquiv_apply (cocartesianBaseChangeNativeObjectIso l k p).hom
    (𝟙 n) (s.val.val.app n (𝟙 n) x)

end SerrePositivity.InfinityCategories
