module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.EnrichedPrecomposition

/-!
概要：QCat の豊穣後合成と内部 Hom の後合成の比較。
方針：評価写像で単体的な作用を比較し、hoFunctor のモノイダル構造で移す。
規約：前合成の比較と同様に二胞体全体で一致を示す。
使われ方：Kerodon Prop 6.2.1.17（Tag 02F1） の対象変数に関する自然性。

対応節は Kerodon 6.2（Tag 02EH）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Bicategory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories

/-- 概要：QCat の単体的な後合成は内部 Hom の共変な作用。
方針：uncurry して評価写像上で比較する。
規約：Mathlib の関手圏の豊穣構造を使う。
使われ方：右 whisker の内部 Hom による表示。 -/
lemma qcatSSetPostcomposition {W X Y : SSet.{u}}
    [Quasicategory W] [Quasicategory X] [Quasicategory Y] (F : X ⟶ Y) :
    eHomWhiskerLeft SSet (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatOf W) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap F) = (ihom W).map F := by
  apply uncurry_injective
  rw [uncurry_ihom_map, uncurry_eq]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨x, H⟩
  rfl

/-- 概要：QCat の Cat 豊穣後合成は内部 Hom の後合成を h に写した関手。
方針：単位・合成の移送と右単位子のモノイダル整合を使う。
規約：Cat の射としての等式。
使われ方：二胞体の右 whisker と h Fun の後合成の比較。 -/
lemma qcatCatPostcomposition {W X Y : SSet.{u}}
    [Quasicategory W] [Quasicategory X] [Quasicategory Y] (F : X ⟶ Y) :
    eHomWhiskerLeft Cat (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatOf W) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap F) = hoFunctor.map ((ihom W).map F) := by
  unfold eHomWhiskerLeft
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCatHomEquiv]
  change (MonoidalCategory.rightUnitor _).inv ≫
      _ ◁ (Functor.LaxMonoidal.ε hoFunctor ≫ hoFunctor.map (eHomEquiv SSet (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap F))) ≫
        (Functor.LaxMonoidal.μ hoFunctor _ _) ≫
          hoFunctor.map (eComp SSet (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatOf W) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatOf X) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatOf Y)) = _
  rw [MonoidalCategory.whiskerLeft_comp, Category.assoc,
    Functor.LaxMonoidal.μ_natural_right_assoc,
    Functor.LaxMonoidal.right_unitality_inv_assoc]
  rw [← Functor.map_comp, ← Functor.map_comp]
  rw [← eHomWhiskerLeft, qcatSSetPostcomposition]

local instance qcatPostcompositionHomCategory (X Y : SSet.QCat.{u}) : Category.{u} (X ⟶ Y) :=
  SSet.QCat.bicategory.homCategory X Y

/-- 概要：QCat の右 whisker は内部 Hom の後合成の h での作用に一致する。
方針：豊穣後合成の比較を射に適用して輸送を相殺する。
規約：可逆性を仮定しない任意の二胞体を扱う。
使われ方：対象変数の射に関する adjunct 対応の自然性。 -/
lemma qcatCell_whiskerRight {W X Y : SSet.{u}}
    [Quasicategory W] [Quasicategory X] [Quasicategory Y]
    {U V : W ⟶ X} (α : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap U ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap V) (F : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv _ _ (α ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap F) =
      (hoFunctor.map ((ihom W).map F)).toFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv _ _ α) := by
  change eqToHom (CatEnrichedOrdinary.homEquiv_comp (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap U) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap F)) ≫
      (eHomWhiskerLeft Cat (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatOf W) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap F)).toFunctor.map
        (CatEnrichedOrdinary.Hom.base α) ≫
          eqToHom (CatEnrichedOrdinary.homEquiv_comp (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap V) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap F)).symm = _
  have hh := CategoryTheory.Functor.congr_hom
    (congrArg Cat.Hom.toFunctor (qcatCatPostcomposition F)) (CatEnrichedOrdinary.Hom.base α)
  rw [hh]
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
