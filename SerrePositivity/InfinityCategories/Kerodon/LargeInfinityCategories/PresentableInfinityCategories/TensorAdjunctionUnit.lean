module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.TensorUnitHom
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitHomFormula

/-!
概要：二つの全随伴の元の単位を直積にまとめ、全 Hom 比較の成分を計算する。
方針：構成した直積単位の射影と、単位 Hom 比較の前後合成の公式を使う。
規約：元の全パラメーターと同じ二胞体を保持する。
使われ方：直積の全随伴と presentable な積の反映模型。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

variable {X Y X' Y' : SSet.{u}} [Quasicategory X] [Quasicategory Y]
  [Quasicategory X'] [Quasicategory Y']
  {F : X ⟶ Y} {R : Y ⟶ X} {G : X' ⟶ Y'} {S : Y' ⟶ X'}

local instance : Quasicategory (X ⊗ X') := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.quasicategory_tensor X X'
local instance : Quasicategory (Y ⊗ Y') := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.quasicategory_tensor Y Y'

/-- 概要：二つの全随伴の単位を直積の両射影に制限する。
方針：元の全二胞体を射影に沿って前合成する。
規約：対象の再選択は行わない。
使われ方：直積単位の指定成分。 -/
def tensorAdjunctionUnitComponents (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction F R) (b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction G S) :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom ((𝟙 (X ⊗ X')) ≫ fst X X') (((F ⊗ₘ G) ≫ (R ⊗ₘ S)) ≫ fst X X') ×
      _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom ((𝟙 (X ⊗ X')) ≫ snd X X') (((F ⊗ₘ G) ≫ (R ⊗ₘ S)) ≫ snd X X') := by
  constructor
  · change _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (fst X X') (fst X X' ≫ F ≫ R)
    exact (hoFunctor.map ((pre (fst X X')).app X)).toFunctor.map a.unitHom
  · change _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (snd X X') (snd X X' ≫ G ≫ S)
    exact (hoFunctor.map ((pre (snd X X')).app X')).toFunctor.map b.unitHom

/-- 概要：二つの全随伴の元の単位から直積関手の全単位候補を構成する。
方針：元の射影成分を全 Hom 分解の逆で戻す。
規約：直積随伴の存在は入力にしない。
使われ方：直積関手の単位による全 Hom 判定。 -/
def tensorAdjunctionUnit (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction F R) (b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction G S) :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 (X ⊗ X')) ((F ⊗ₘ G) ≫ (R ⊗ₘ S)) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorHomTensorEquiv _ _).symm (tensorAdjunctionUnitComponents a b)

lemma tensorAdjunctionUnit_components (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction F R) (b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction G S) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorHomTensorEquiv (𝟙 (X ⊗ X')) ((F ⊗ₘ G) ≫ (R ⊗ₘ S)) (tensorAdjunctionUnit a b) =
      tensorAdjunctionUnitComponents a b :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorHomTensorEquiv _ _).apply_symm_apply _

lemma tensorAdjunctionUnit_fst (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction F R) (b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction G S) :
    (hoFunctor.map ((ihom (X ⊗ X')).map (fst X X'))).toFunctor.map
      (tensorAdjunctionUnit a b) =
        (hoFunctor.map ((pre (fst X X')).app X)).toFunctor.map a.unitHom := by
  change @Eq (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (fst X X') (fst X X' ≫ F ≫ R)) _ _
  have h := congrArg Prod.fst (tensorAdjunctionUnit_components a b)
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorHomTensorEquiv_apply, tensorAdjunctionUnitComponents, id_eq,
    Category.id_comp, Category.assoc, tensorHom_fst] using h

lemma tensorAdjunctionUnit_snd (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction F R) (b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction G S) :
    (hoFunctor.map ((ihom (X ⊗ X')).map (snd X X'))).toFunctor.map
      (tensorAdjunctionUnit a b) =
        (hoFunctor.map ((pre (snd X X')).app X')).toFunctor.map b.unitHom := by
  change @Eq (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (snd X X') (snd X X' ≫ G ≫ S)) _ _
  have h := congrArg Prod.snd (tensorAdjunctionUnit_components a b)
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorHomTensorEquiv_apply, tensorAdjunctionUnitComponents, id_eq,
    Category.id_comp, Category.assoc, tensorHom_snd] using h

/-- 概要：直積の単位 Hom 比較は二つの元の随伴の単位 Hom 比較に分解される。
方針：元の二胞体の合成・前後合成と直積分解の可換性を使う。
規約：任意の全パラメーター A を扱う。
使われ方：直積の単位 Hom 比較の全単射性。 -/
lemma tensorAdjunctionUnit_homMap_components (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction F R)
    (b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction G S) {A : SSet.{u}} [Quasicategory A]
    (U : A ⟶ X ⊗ X') (V : A ⟶ Y ⊗ Y')
    (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (U ≫ (F ⊗ₘ G)) V) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorHomTensorEquiv U (V ≫ (R ⊗ₘ S))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatUnitHomMap (tensorAdjunctionUnit a b) U V α) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatUnitHomMap a.unitHom (U ≫ fst X X') (V ≫ fst Y Y')
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorHomTensorEquiv (U ≫ (F ⊗ₘ G)) V α).1,
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatUnitHomMap b.unitHom (U ≫ snd X X') (V ≫ snd Y Y')
          (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorHomTensorEquiv (U ≫ (F ⊗ₘ G)) V α).2) := by
  have hfst := congrArg Prod.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorHomTensorEquiv_postcomp R S α)
  have hsnd := congrArg Prod.snd (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorHomTensorEquiv_postcomp R S α)
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorHomTensorEquiv_apply] at hfst hsnd
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorHomTensorEquiv_apply, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatUnitHomMap_formula,
    CategoryTheory.Functor.map_comp, ← _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorHom_pre_post, tensorAdjunctionUnit_fst,
    tensorAdjunctionUnit_snd, ← _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorHom_pre_comp, hfst, hsnd]


end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
