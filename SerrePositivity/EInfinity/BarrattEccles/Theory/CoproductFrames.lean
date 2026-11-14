module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.CoproductModel
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Replacements.SourceInvariance
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.SimplexResolution
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.ResolutionHom
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-!
# 余積の余単体的 frame の指定比較

概要：HA 3.2.4.7 の二項余積の検査に、二つの分解の余積からの比較を作る。
方針：Reedy モデルの cofibrancy と augmentation の二つのうち三つの性質を使う。
規約：単体集合のモデル構造を要求せず、指定した包含を保つ。
使われ方：native な余積錐の全 Hom の積比較。［一般∞］の移動候補。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w t
namespace SerrePositivity.EInfinity
open CategoryTheory Limits HomotopicalAlgebra Opposite
open SerrePositivity.Reedy SerrePositivity.HomotopyFunctionComplex
variable {C : Type u} [Category.{v} C] [ModelCategory C]

/-- Cofibrant な両入力の弱同値の余積は弱同値。 -/
lemma coprodMap_weakEquivalence {X X' Y Y' : C}
    [IsCofibrant X] [IsCofibrant X'] [IsCofibrant Y] [IsCofibrant Y']
    (f : X ⟶ X') (g : Y ⟶ Y') [WeakEquivalence f] [WeakEquivalence g] :
    WeakEquivalence (coprod.map f g) := by
  have := modelCoprodWith_map_weakEquivalence Y f
  have := modelCoprodWith_map_weakEquivalence X' g
  have he : coprod.map f g = coprod.map f (𝟙 Y) ≫
      (coprod.braiding X' Y).hom ≫ coprod.map g (𝟙 X') ≫
        (coprod.braiding Y' X').hom := by
    apply coprod.hom_ext <;> simp
  rw [he]
  infer_instance

variable (q : CofibrantResolutionFamily (C := C) simplex)

/-- 二つの指定された分解の余積から、余積の指定分解への射。 -/
def coproductFrameComparison (X Y : C) :
    q.obj.obj X ⨿ q.obj.obj Y ⟶ q.obj.obj (X ⨿ Y) :=
  coprod.desc (q.obj.map coprod.inl) (q.obj.map coprod.inr)

/-- この比較の第一制限は、指定包含に分解を適用した射。 -/
@[reassoc (attr := simp)]
lemma coproductFrameComparison_inl (X Y : C) :
    coprod.inl ≫ coproductFrameComparison q X Y = q.obj.map coprod.inl :=
  coprod.inl_desc _ _

/-- この比較の第二制限も指定包含を保つ。 -/
@[reassoc (attr := simp)]
lemma coproductFrameComparison_inr (X Y : C) :
    coprod.inr ≫ coproductFrameComparison q X Y = q.obj.map coprod.inr :=
  coprod.inr_desc _ _

/-- 二つの frame の余積は Reedy cofibrant。 -/
lemma coproductFrame_cofibrant (X Y : C) :
    reedyLeft simplex (cofibrations C) (initial.to (q.obj.obj X ⨿ q.obj.obj Y)) := by
  let := simplexModelCategory C
  have : IsCofibrant (q.obj.obj X) := ⟨q.cofibrant X⟩
  have : IsCofibrant (q.obj.obj Y) := ⟨q.cofibrant Y⟩
  exact (modelCoprodWith_cofibrant (q.obj.obj X) (q.obj.obj Y)).1

/-- 同じ augmentation への比較は各次数で弱同値。 -/
lemma coproductFrameComparison_weakEquivalence (X Y : C)
    [IsCofibrant X] [IsCofibrant Y] (n : SimplexCategory) :
    weakEquivalences C ((coproductFrameComparison q X Y).app n) := by
  let E := (evaluation SimplexCategory C).obj n
  have : IsCofibrant ((q.obj.obj X).obj n) := (q.atObject X).isCofibrant_obj n
  have : IsCofibrant ((q.obj.obj Y).obj n) := (q.atObject Y).isCofibrant_obj n
  have : WeakEquivalence ((q.augmentation.app X).app n) :=
    ⟨(q.atObject X).augmentation_weakEquivalence n⟩
  have : WeakEquivalence ((q.augmentation.app Y).app n) :=
    ⟨(q.atObject Y).augmentation_weakEquivalence n⟩
  have : IsCofibrant (((Functor.const SimplexCategory).obj X).obj n) := ‹IsCofibrant X›
  have : IsCofibrant (((Functor.const SimplexCategory).obj Y).obj n) := ‹IsCofibrant Y›
  have := coprodMap_weakEquivalence ((q.augmentation.app X).app n)
    ((q.augmentation.app Y).app n)
  have he : coprodComparison E (q.obj.obj X) (q.obj.obj Y) ≫
      (coproductFrameComparison q X Y).app n ≫ (q.augmentation.app (X ⨿ Y)).app n =
    coprod.map ((q.augmentation.app X).app n) ((q.augmentation.app Y).app n) := by
    apply coprod.hom_ext
    · rw [coprodComparison_inl_assoc]
      change ((coprod.inl : q.obj.obj X ⟶ q.obj.obj X ⨿ q.obj.obj Y) ≫
        coproductFrameComparison q X Y ≫ q.augmentation.app (X ⨿ Y)).app n = _
      rw [← Category.assoc, coproductFrameComparison_inl]
      rw [coprod.inl_map]
      exact NatTrans.congr_app (q.augmentation.naturality (coprod.inl : X ⟶ X ⨿ Y)) n
    · rw [coprodComparison_inr_assoc]
      change ((coprod.inr : q.obj.obj Y ⟶ q.obj.obj X ⨿ q.obj.obj Y) ≫
        coproductFrameComparison q X Y ≫ q.augmentation.app (X ⨿ Y)).app n = _
      rw [← Category.assoc, coproductFrameComparison_inr]
      rw [coprod.inr_map]
      exact NatTrans.congr_app (q.augmentation.naturality (coprod.inr : Y ⟶ X ⨿ Y)) n
  have hc : weakEquivalences C (coprodComparison E (q.obj.obj X) (q.obj.obj Y) ≫
      (coproductFrameComparison q X Y).app n ≫ (q.augmentation.app (X ⨿ Y)).app n) := by
    rw [he]
    exact mem_weakEquivalences _
  have haug : weakEquivalences C ((q.augmentation.app (X ⨿ Y)).app n) :=
    (q.atObject (X ⨿ Y)).augmentation_weakEquivalence n
  have hmid := (weakEquivalences C).of_postcomp
    (coprodComparison E (q.obj.obj X) (q.obj.obj Y) ≫
      (coproductFrameComparison q X Y).app n) _ haug
        (by simpa only [Category.assoc] using hc)
  exact (weakEquivalences C).of_precomp _ _ (mem_weakEquivalences _) hmid

/-- 指定 frame 比較の Hom は anodyne 反転後に同型（Hovey §5）。 -/
lemma coproductFrameComparison_hom_isIso {D : Type w} [Category.{t} D]
    (L : SSet.{v} ⥤ D) (hL : SSet.anodyneExtensions.IsInvertedBy L)
    (X Y Z : C) [IsCofibrant X] [IsCofibrant Y] [IsFibrant Z] :
    IsIso (L.map ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap (coproductFrameComparison q X Y)).app Z)) :=
  _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.source_weakEquivalence_isIso L hL (coproductFrameComparison q X Y)
    (coproductFrame_cofibrant q X Y) (q.cofibrant (X ⨿ Y))
    (coproductFrameComparison_weakEquivalence q X Y) Z

end SerrePositivity.EInfinity
