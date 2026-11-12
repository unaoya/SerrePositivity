module

public import SerrePositivity.EInfinity.BarrattEccles.RightFrames
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.ResolutionHom
public import Mathlib.CategoryTheory.Limits.Yoneda
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products

/-!
# 共通の右 frame への余積の Hom

## 概要
HA §3.2.4.7 の余積余錐の検査で、同じ右 frame への Hom を二つの Hom の積へ分ける。

## 方針
反対圏で余積を積として読み、Yoneda と図式の前合成の極限保存を使う。

## 規約
比較の二つの射は、元の余積の指定包含による前合成である。

## 使われ方
CAlg の native な余錐の二つの脚と写像空間の積比較の照合。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity
open CategoryTheory Limits Opposite
open _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom
variable {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]

/-- The opposite of the specified coproduct is the product with the specified projections. -/
def coprodOppositeProductIso (X Y : C) : op (X ⨿ Y) ≅ op X ⨯ op Y where
  hom := prod.lift coprod.inl.op coprod.inr.op
  inv := (coprod.desc prod.fst.unop prod.snd.unop).op
  hom_inv_id := by
    apply Quiver.Hom.unop_inj
    apply coprod.hom_ext
    · simp only [unop_comp, Quiver.Hom.unop_op, unop_id,
        coprod.inl_desc_assoc, Category.comp_id]
      apply Quiver.Hom.op_inj
      simp only [op_comp, Quiver.Hom.op_unop, prod.lift_fst]
    · simp only [unop_comp, Quiver.Hom.unop_op, unop_id,
        coprod.inr_desc_assoc, Category.comp_id]
      apply Quiver.Hom.op_inj
      simp only [op_comp, Quiver.Hom.op_unop, prod.lift_snd]
  inv_hom_id := by
    apply prod.hom_ext
    · simp only [Category.assoc, prod.lift_fst, Category.id_comp]
      apply Quiver.Hom.unop_inj
      simp only [unop_comp, Quiver.Hom.unop_op, coprod.inl_desc]
    · simp only [Category.assoc, prod.lift_snd, Category.id_comp]
      apply Quiver.Hom.unop_inj
      simp only [unop_comp, Quiver.Hom.unop_op, coprod.inr_desc]

/-- The simplicial Hom of a coproduct into a single right frame is the product of the two Homs. -/
def rightFrameCoprodHomIso (F : SimplexCategory ⥤ Cᵒᵖ) (X Y : C) :
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom F).obj (op (X ⨿ Y)) ≅
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom F).obj (op X) ⨯ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom F).obj (op Y) :=
  (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom F).mapIso (coprodOppositeProductIso X Y) ≪≫
    asIso (prodComparison (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom F) (op X) (op Y))

/-- The first projection of the comparison is exactly restriction along the first inclusion. -/
@[reassoc]
lemma rightFrameCoprodHomIso_fst (F : SimplexCategory ⥤ Cᵒᵖ) (X Y : C) :
    (rightFrameCoprodHomIso F X Y).hom ≫ prod.fst =
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom F).map coprod.inl.op := by
  simp only [rightFrameCoprodHomIso, Iso.trans_hom, Functor.mapIso_hom, asIso_hom,
    Category.assoc, prodComparison_fst, ← Functor.map_comp]
  rw [coprodOppositeProductIso, prod.lift_fst]

/-- The second projection of the comparison is exactly restriction along the second inclusion. -/
@[reassoc]
lemma rightFrameCoprodHomIso_snd (F : SimplexCategory ⥤ Cᵒᵖ) (X Y : C) :
    (rightFrameCoprodHomIso F X Y).hom ≫ prod.snd =
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom F).map coprod.inr.op := by
  simp only [rightFrameCoprodHomIso, Iso.trans_hom, Functor.mapIso_hom, asIso_hom,
    Category.assoc, prodComparison_snd, ← Functor.map_comp]
  rw [coprodOppositeProductIso, prod.lift_snd]

end SerrePositivity.EInfinity
