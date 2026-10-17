module
public import SerrePositivity.DifferentialGraded.Morita.U16a
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-! # Morita作用の正方形から実際の右随伴の正方形へ

## 概要
二つのkernel作用が同値なら、左作用の比較正方形を実際の一般右随伴の比較へ運ぶ。

## 方針
左作用の正方形の逆、元の実際の余単位、変更後の実際の単位から自然同型を構成する。

## 規約と注意
係数環・対象宇宙を独立に保つ。左右の作用の同値性は三条件Morita判定から供給できる。
左作用の比較を入力から新たに証明したとはしない。係数変更の未完図式を代用しない。

## 使われ方
U16dの係数変更比較を、U16cで同定した実際の右随伴側へ接続する。
-/
@[expose] public section
noncomputable section
universe u u' v w v' w'
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (A' : Type u') [CommRing A']
  (D' : Type v') [DGCategory A' D'] [Small.{u'} D']
  (E' : Type w') [DGCategory A' E'] [Small.{u'} E']
  (K : Kernel A D E) (K' : Kernel A' D' E')
  [(kernelDerivedTensor A D E K).IsEquivalence]
  [(kernelDerivedTensor A' D' E' K').IsEquivalence]
  (S : DerivedModuleCategory A D ⥤ DerivedModuleCategory A' D')
  (T : DerivedModuleCategory A E ⥤ DerivedModuleCategory A' E')
  (e : kernelDerivedTensor A D E K ⋙ T ≅ S ⋙ kernelDerivedTensor A' D' E' K')

/-- 実際の両随伴で転置した、右随伴側の比較自然同型。 -/
def kernelRightAdjointSquareIso :
    kernelDerivedHom A D E K ⋙ S ≅ T ⋙ kernelDerivedHom A' D' E' K' := by
  have : IsIso (kernelDerivedUnit A' D' E' K') := by
    change IsIso (kernelDerivedAdjunction A' D' E' K').unit
    infer_instance
  have : IsIso (kernelDerivedCounit A D E K) := by
    change IsIso (kernelDerivedAdjunction A D E K).counit
    infer_instance
  let R := kernelDerivedHom A D E K
  let R' := kernelDerivedHom A' D' E' K'
  let L := kernelDerivedTensor A D E K
  let L' := kernelDerivedTensor A' D' E' K'
  let η := asIso (kernelDerivedUnit A' D' E' K')
  let ε := asIso (kernelDerivedCounit A D E K)
  exact (rightUnitor (R ⋙ S)).symm ≪≫ isoWhiskerLeft (R ⋙ S) η ≪≫
    (associator (R ⋙ S) L' R').symm ≪≫
    isoWhiskerRight (associator R S L') R' ≪≫
    isoWhiskerRight (isoWhiskerLeft R e.symm) R' ≪≫
    isoWhiskerRight (associator R L T).symm R' ≪≫
    isoWhiskerRight (isoWhiskerRight ε T) R' ≪≫
    isoWhiskerRight (leftUnitor T) R'

/-- 比較の成分は、変更後の実際の単位と元の実際の余単位で計算する。 -/
lemma kernelRightAdjointSquareIso_hom_app (Y : DerivedModuleCategory A E) :
    (kernelRightAdjointSquareIso A D E A' D' E' K K' S T e).hom.app Y =
      (kernelDerivedUnit A' D' E' K').app (S.obj ((kernelDerivedHom A D E K).obj Y)) ≫
        (kernelDerivedHom A' D' E' K').map (e.inv.app ((kernelDerivedHom A D E K).obj Y)) ≫
        (kernelDerivedHom A' D' E' K').map (T.map ((kernelDerivedCounit A D E K).app Y)) := by
  dsimp only [kernelRightAdjointSquareIso]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, isoWhiskerLeft_hom,
    isoWhiskerRight_hom, whiskerLeft_app, whiskerRight_app, rightUnitor_inv_app,
    associator_hom_app, associator_inv_app, leftUnitor_hom_app, asIso_hom,
    CategoryTheory.Functor.map_id, Category.id_comp]
  erw [Category.id_comp, Category.id_comp, CategoryTheory.Functor.map_id, Category.comp_id]
  rfl

/-- 右随伴の正方形は、実際の余単位で元の左作用の比較に戻る。 -/
lemma kernelRightAdjointSquareIso_counit (Y : DerivedModuleCategory A E) :
    (kernelDerivedTensor A' D' E' K').map
        ((kernelRightAdjointSquareIso A D E A' D' E' K K' S T e).hom.app Y) ≫
      (kernelDerivedCounit A' D' E' K').app (T.obj Y) =
    e.inv.app ((kernelDerivedHom A D E K).obj Y) ≫
      T.map ((kernelDerivedCounit A D E K).app Y) := by
  let g := e.inv.app ((kernelDerivedHom A D E K).obj Y) ≫
    T.map ((kernelDerivedCounit A D E K).app Y)
  have hn := (kernelDerivedCounit A' D' E' K').naturality g
  simp only [Functor.comp_map, Functor.id_map] at hn
  rw [kernelRightAdjointSquareIso_hom_app, ← Functor.map_comp,
    Functor.map_comp, Category.assoc]
  erw [hn]
  rw [← Category.assoc]
  erw [kernelDerived_left_triangle A' D' E' K'
    (S.obj ((kernelDerivedHom A D E K).obj Y)), Category.id_comp]

/-- 右随伴の比較は、係数変更の両側の実際の単位にも整合する。 -/
lemma kernelRightAdjointSquareIso_unit (X : DerivedModuleCategory A D) :
    S.map ((kernelDerivedUnit A D E K).app X) ≫
        (kernelRightAdjointSquareIso A D E A' D' E' K K' S T e).hom.app
          ((kernelDerivedTensor A D E K).obj X) =
      (kernelDerivedUnit A' D' E' K').app (S.obj X) ≫
        (kernelDerivedHom A' D' E' K').map (e.inv.app X) := by
  let η := (kernelDerivedUnit A D E K).app X
  let ε := (kernelDerivedCounit A D E K).app ((kernelDerivedTensor A D E K).obj X)
  have hu := (kernelDerivedUnit A' D' E' K').naturality (S.map η)
  simp only [Functor.id_map, Functor.comp_map] at hu
  have he := e.inv.naturality η
  simp only [Functor.comp_map] at he
  have hg : (kernelDerivedTensor A' D' E' K').map (S.map η) ≫
      (e.inv.app ((kernelDerivedHom A D E K).obj ((kernelDerivedTensor A D E K).obj X)) ≫
        T.map ε) = e.inv.app X := by
    rw [← Category.assoc]
    erw [he]
    rw [Category.assoc, ← T.map_comp]
    erw [kernelDerived_left_triangle A D E K X,
      CategoryTheory.Functor.map_id, Category.comp_id]
    rfl
  rw [kernelRightAdjointSquareIso_hom_app, ← Category.assoc]
  erw [hu]
  simp only [Category.assoc]
  slice_lhs 2 4 => rw [← Functor.map_comp, ← Functor.map_comp]
  erw [hg]
  rfl

/-- 恒等な左作用正方形は、実際の右随伴の恒等正方形へ運ばれる。 -/
lemma kernelRightAdjointSquareIso_identity :
    kernelRightAdjointSquareIso A D E A D E K K (𝟭 _) (𝟭 _)
        (rightUnitor (kernelDerivedTensor A D E K) ≪≫
          (leftUnitor (kernelDerivedTensor A D E K)).symm) =
      rightUnitor (kernelDerivedHom A D E K) ≪≫
        (leftUnitor (kernelDerivedHom A D E K)).symm := by
  apply Iso.ext
  apply NatTrans.ext
  funext Y
  rw [kernelRightAdjointSquareIso_hom_app]
  simp only [Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app, rightUnitor_inv_app,
    leftUnitor_hom_app, Iso.trans_hom, Iso.symm_hom, rightUnitor_hom_app,
    leftUnitor_inv_app, Functor.id_map]
  erw [Category.id_comp, Category.id_comp, CategoryTheory.Functor.map_id, Category.id_comp]
  exact kernelDerived_right_triangle A D E K Y

end SerrePositivity.DifferentialGraded.Morita
