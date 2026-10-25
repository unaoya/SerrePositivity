module

public import SerrePositivity.InfinityCategories.F2.Presentable.TensorUnitHom
public import SerrePositivity.InfinityCategories.F1B.Adjunction.UnitHomFormula

/-!
概要：二つの全随伴の元の単位を直積にまとめ、全 Hom 比較の成分を計算する。
方針：構成した直積単位の射影と、単位 Hom 比較の前後合成の公式を使う。
規約：元の全パラメーターと同じ二胞体を保持する。
使われ方：直積の全随伴と presentable な積の反映模型。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable

variable {X Y X' Y' : SSet.{u}} [Quasicategory X] [Quasicategory Y]
  [Quasicategory X'] [Quasicategory Y']
  {F : X ⟶ Y} {R : Y ⟶ X} {G : X' ⟶ Y'} {S : Y' ⟶ X'}

local instance : Quasicategory (X ⊗ X') := F2.quasicategory_tensor X X'
local instance : Quasicategory (Y ⊗ Y') := F2.quasicategory_tensor Y Y'

/-- 概要：二つの全随伴の単位を直積の両射影に制限する。
方針：元の全二胞体を射影に沿って前合成する。
規約：対象の再選択は行わない。
使われ方：直積単位の指定成分。 -/
def tensorAdjunctionUnitComponents (a : QCatAdjunction F R) (b : QCatAdjunction G S) :
    FunctorHom ((𝟙 (X ⊗ X')) ≫ fst X X') (((F ⊗ₘ G) ≫ (R ⊗ₘ S)) ≫ fst X X') ×
      FunctorHom ((𝟙 (X ⊗ X')) ≫ snd X X') (((F ⊗ₘ G) ≫ (R ⊗ₘ S)) ≫ snd X X') := by
  constructor
  · change FunctorHom (fst X X') (fst X X' ≫ F ≫ R)
    exact (hoFunctor.map ((pre (fst X X')).app X)).toFunctor.map a.unitHom
  · change FunctorHom (snd X X') (snd X X' ≫ G ≫ S)
    exact (hoFunctor.map ((pre (snd X X')).app X')).toFunctor.map b.unitHom

/-- 概要：二つの全随伴の元の単位から直積関手の全単位候補を構成する。
方針：元の射影成分を全 Hom 分解の逆で戻す。
規約：直積随伴の存在は入力にしない。
使われ方：直積関手の単位による全 Hom 判定。 -/
def tensorAdjunctionUnit (a : QCatAdjunction F R) (b : QCatAdjunction G S) :
    FunctorHom (𝟙 (X ⊗ X')) ((F ⊗ₘ G) ≫ (R ⊗ₘ S)) :=
  (functorHomTensorEquiv _ _).symm (tensorAdjunctionUnitComponents a b)

lemma tensorAdjunctionUnit_components (a : QCatAdjunction F R) (b : QCatAdjunction G S) :
    functorHomTensorEquiv (𝟙 (X ⊗ X')) ((F ⊗ₘ G) ≫ (R ⊗ₘ S)) (tensorAdjunctionUnit a b) =
      tensorAdjunctionUnitComponents a b :=
  (functorHomTensorEquiv _ _).apply_symm_apply _

lemma tensorAdjunctionUnit_fst (a : QCatAdjunction F R) (b : QCatAdjunction G S) :
    (hoFunctor.map ((ihom (X ⊗ X')).map (fst X X'))).toFunctor.map
      (tensorAdjunctionUnit a b) =
        (hoFunctor.map ((pre (fst X X')).app X)).toFunctor.map a.unitHom := by
  change @Eq (FunctorHom (fst X X') (fst X X' ≫ F ≫ R)) _ _
  have h := congrArg Prod.fst (tensorAdjunctionUnit_components a b)
  simpa only [functorHomTensorEquiv_apply, tensorAdjunctionUnitComponents, id_eq,
    Category.id_comp, Category.assoc, tensorHom_fst] using h

lemma tensorAdjunctionUnit_snd (a : QCatAdjunction F R) (b : QCatAdjunction G S) :
    (hoFunctor.map ((ihom (X ⊗ X')).map (snd X X'))).toFunctor.map
      (tensorAdjunctionUnit a b) =
        (hoFunctor.map ((pre (snd X X')).app X')).toFunctor.map b.unitHom := by
  change @Eq (FunctorHom (snd X X') (snd X X' ≫ G ≫ S)) _ _
  have h := congrArg Prod.snd (tensorAdjunctionUnit_components a b)
  simpa only [functorHomTensorEquiv_apply, tensorAdjunctionUnitComponents, id_eq,
    Category.id_comp, Category.assoc, tensorHom_snd] using h

/-- 概要：直積の単位 Hom 比較は二つの元の随伴の単位 Hom 比較に分解される。
方針：元の二胞体の合成・前後合成と直積分解の可換性を使う。
規約：任意の全パラメーター A を扱う。
使われ方：直積の単位 Hom 比較の全単射性。 -/
lemma tensorAdjunctionUnit_homMap_components (a : QCatAdjunction F R)
    (b : QCatAdjunction G S) {A : SSet.{u}} [Quasicategory A]
    (U : A ⟶ X ⊗ X') (V : A ⟶ Y ⊗ Y')
    (α : FunctorHom (U ≫ (F ⊗ₘ G)) V) :
    functorHomTensorEquiv U (V ≫ (R ⊗ₘ S))
      (qcatUnitHomMap (tensorAdjunctionUnit a b) U V α) =
      (qcatUnitHomMap a.unitHom (U ≫ fst X X') (V ≫ fst Y Y')
        (functorHomTensorEquiv (U ≫ (F ⊗ₘ G)) V α).1,
        qcatUnitHomMap b.unitHom (U ≫ snd X X') (V ≫ snd Y Y')
          (functorHomTensorEquiv (U ≫ (F ⊗ₘ G)) V α).2) := by
  have hfst := congrArg Prod.fst (functorHomTensorEquiv_postcomp R S α)
  have hsnd := congrArg Prod.snd (functorHomTensorEquiv_postcomp R S α)
  simp only [functorHomTensorEquiv_apply] at hfst hsnd
  simp only [functorHomTensorEquiv_apply, qcatUnitHomMap_formula,
    CategoryTheory.Functor.map_comp, ← functorHom_pre_post, tensorAdjunctionUnit_fst,
    tensorAdjunctionUnit_snd, ← functorHom_pre_comp, hfst, hsnd]


end SerrePositivity.InfinityCategories.F2.Presentable
