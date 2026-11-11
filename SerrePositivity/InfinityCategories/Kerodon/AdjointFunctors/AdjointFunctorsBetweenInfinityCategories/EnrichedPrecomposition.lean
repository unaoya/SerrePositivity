module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.Adjunction

/-!
概要：QCat の豊穣前合成と内部 Hom の前合成の比較。
方針：単体的な前合成を評価写像上で比較し、hoFunctor のモノイダル構造で移送する。
規約：関手圏の豊穣構造と閉構造を定義上一致すると仮定しない。
使われ方：Kerodon Prop 6.2.1.17（Tag 02F1） のパラメータ自然性と双圏の adjunct 対応の接続。

対応節は Kerodon 6.2（Tag 02EH）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Bicategory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories

/-- 概要：QCat の単体的豊穣前合成は内部 Hom の前合成。
方針：uncurry して評価写像上で比較する。
規約：Mathlib の関手圏としての豊穣構造を使う。
使われ方：双圏の whisker と単体集合の pre の照合。 -/
lemma qcatSSetPrecomposition {W X Y : SSet.{u}}
    [Quasicategory W] [Quasicategory X] [Quasicategory Y]
    (i : W ⟶ X) : eHomWhiskerRight SSet (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap i) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatOf Y) = (pre i).app Y := by
  apply uncurry_injective
  have hp : uncurry ((pre i).app Y) =
      (i ▷ ((ihom X).obj Y)) ≫ (ihom.ev X).app Y := by
    simpa only [Category.id_comp, uncurry_id_eq_ev] using
      (uncurry_pre_app Y (𝟙 ((ihom X).obj Y)) i)
  rw [hp, uncurry_eq]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨x, F⟩
  rfl

/-- 概要：QCat の一胞体の Cat 豊穣表示と hoFunctor の単位の整合。
方針：hoFunctor.unitHomEquiv の等式を Cat の射へ移す。
規約：eHomEquiv の二つの表示を等式で比較する。
使われ方：豊穣前合成の hoFunctor による移送。 -/
lemma qcatCatHomEquiv {W X : SSet.{u}} [Quasicategory W] [Quasicategory X] (i : W ⟶ X) :
    eHomEquiv Cat (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap i) = Functor.LaxMonoidal.ε hoFunctor ≫
      hoFunctor.map (eHomEquiv SSet (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap i)) := by
  exact congrArg Functor.toCatHom (hoFunctor.unitHomEquiv_eq _ _)
/-- 概要：QCat の Cat 豊穣前合成は内部 Hom の前合成を h に写した関手。
方針：移送した合成・単位と hoFunctor のモノイダル自然性を計算する。
規約：Cat の射の等式であり、対象上だけの比較ではない。
使われ方：双圏の前合成と h Fun の前合成の接続。 -/
lemma qcatCatPrecomposition {W X Y : SSet.{u}}
    [Quasicategory W] [Quasicategory X] [Quasicategory Y] (i : W ⟶ X) :
    eHomWhiskerRight Cat (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap i) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatOf Y) = hoFunctor.map ((pre i).app Y) := by
  unfold eHomWhiskerRight
  rw [qcatCatHomEquiv]
  change (MonoidalCategory.leftUnitor _).inv ≫
      (Functor.LaxMonoidal.ε hoFunctor ≫ hoFunctor.map (eHomEquiv SSet (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap i))) ▷ _ ≫
        (Functor.LaxMonoidal.μ hoFunctor _ _) ≫
          hoFunctor.map (eComp SSet (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatOf W) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatOf X) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatOf Y)) = _
  rw [MonoidalCategory.comp_whiskerRight, Category.assoc,
    Functor.LaxMonoidal.μ_natural_left_assoc]
  rw [Functor.LaxMonoidal.left_unitality_inv_assoc]
  rw [← Functor.map_comp, ← Functor.map_comp]
  rw [← eHomWhiskerRight, qcatSSetPrecomposition]

local instance qcatPrecompositionHomCategory (X Y : SSet.QCat.{u}) : Category.{u} (X ⟶ Y) :=
  SSet.QCat.bicategory.homCategory X Y

/-- 概要：QCat の左 whisker と内部 Hom の前合成作用は一致する。
方針：豊穣前合成の比較を射に適用し、対象の輸送を相殺する。
規約：二胞体は h Fun の射全体を扱い、辺の代表を選ばない。
使われ方：Kerodon Prop 6.2.1.17（Tag 02F1） のパラメータ自然性の接続。 -/
lemma qcatCell_whiskerLeft {W X Y : SSet.{u}} [Quasicategory W] [Quasicategory X] [Quasicategory Y]
    (i : W ⟶ X) {F G : X ⟶ Y} (α : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap F ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap G) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap i ◁ α) =
      (hoFunctor.map ((pre i).app Y)).toFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv _ _ α) := by
  change eqToHom (CatEnrichedOrdinary.homEquiv_comp (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap i) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap F)) ≫
      (eHomWhiskerRight Cat (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap i) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatOf Y)).toFunctor.map
        (CatEnrichedOrdinary.Hom.base α) ≫
          eqToHom (CatEnrichedOrdinary.homEquiv_comp (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap i) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap G)).symm = _
  have hh := CategoryTheory.Functor.congr_hom
    (congrArg Cat.Hom.toFunctor (qcatCatPrecomposition i)) (CatEnrichedOrdinary.Hom.base α)
  rw [hh]
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
