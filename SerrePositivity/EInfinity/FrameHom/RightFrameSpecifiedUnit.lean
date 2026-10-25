module

public import SerrePositivity.EInfinity.FrameHom.RightFrameSpecifiedLocalization
public import SerrePositivity.EInfinity.FrameHom.RightFrameHammockUnitComparison
public import SerrePositivity.EInfinity.Hammock.AsSmallArrow
public import SerrePositivity.EInfinity.SimplicialLocalization.KanHammockArrowNormalization

/-!
概要：指定局所化への実 frame 比較は元の局所化射の同じ零単体を保持する。
方針：同じ六辺の単位公式を元の AsSmall 射へ回収し、指定二胞体の比較を後合成する。
規約：指定 K と二胞体を保持し、生の辺の厳密化を要求しない。
使われ方：Sp の元の射・端点成分による共役の照合。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.FrameHom
open CategoryTheory HomotopicalAlgebra SSet Opposite Hammock MonoidalCategory
open SerrePositivity.Reedy SerrePositivity.InfinityCategories SerrePositivity.SimplicialModel
open SerrePositivity.KST.Comparison SimplicialLocalization
open scoped Simplicial
variable {C : Type u} [Category.{v} C] [ModelCategory C] {X Y : C} [IsCofibrant X]
  (q : CofibrantResolution (C := C) simplex X)
  (r : CofibrantResolutionFamily (C := Cᵒᵖ) simplex) (f : X ⟶ Y)
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
attribute [local instance] rightFrameHom_kanComplex

/-- 概要：実 frame 比較の元の単位点は元の持ち上げた通常射の coherent Hom 点と一致する。
方針：同じ六辺の単位公式と Ex∞ 単位の自然性・元の宇宙比較を合成する。
規約：anodyne 反転後の同じ零単体。
使われ方：元の hammock 源関手の射の回収。
-/
lemma rightFrameHammockPinchedEquivalence_unit_arrow_Q :
    AnodyneHomotopy.anodyneQ.map
      (rightFrameHammockUnitPoint q r f 0 ≫
        (rightFrameHammockPinchedEquivalence q r cof Y).hom) =
    AnodyneHomotopy.anodyneQ.map
      (arrowMap (modelRelativeCategory C).weakEquivalences (AsSmall.up.map f) ≫
        exInfinityUnit.app _ ≫ kanHammockHomPinchedMap (modelRelativeCategory C)
          (modelRelativeObject C X) (modelRelativeObject C Y)) := by
  have h := congrArg (arrowMap (weakEquivalences C) f ≫ ·)
    (exInfinityUnit.naturality (AsSmallComparison.colimitIso (weakEquivalences C) X Y).hom)
  simp only [Functor.id_map] at h
  have ha : arrowMap (weakEquivalences C) f ≫ exInfinityUnit.app _ ≫
      exInfinity.map (AsSmallComparison.colimitIso (weakEquivalences C) X Y).hom =
      arrowMap (modelRelativeCategory C).weakEquivalences (AsSmall.up.map f) ≫
        exInfinityUnit.app _ := by
    change arrowMap (weakEquivalences C) f ≫
      exInfinityUnit.app (colimitGraph (weakEquivalences C) X Y) ≫
        exInfinity.map (AsSmallComparison.colimitIso (weakEquivalences C) X Y).hom =
      arrowMap (AsSmallComparison.weak (weakEquivalences C)) (AsSmall.up.map f) ≫
        exInfinityUnit.app (colimitGraph (AsSmallComparison.weak (weakEquivalences C))
          (AsSmall.up.obj X) (AsSmall.up.obj Y))
    exact h.symm.trans (by
      simpa only [Category.assoc] using congrArg
        (fun a => a ≫ exInfinityUnit.app
          (colimitGraph (AsSmallComparison.weak (weakEquivalences C))
            (AsSmall.up.obj X) (AsSmall.up.obj Y)))
        (AsSmallComparison.arrowMap_colimitIso (weakEquivalences C) f))
  exact (rightFrameHammockPinchedEquivalence_unit_Q q r f cof).trans
    (congrArg AnodyneHomotopy.anodyneQ.map
      (by simpa only [Category.assoc] using congrArg (· ≫ kanHammockHomPinchedMap
        (modelRelativeCategory C) (modelRelativeObject C X) (modelRelativeObject C Y)) ha))

variable {Q : SSet.{max u v}} [Quasicategory Q]
  (G : nerve (modelRelativeCategory C).category ⟶ Q)
  (hG : IsLocalization G (weakNerveEdges (modelRelativeCategory C)))
  (hH : IsLocalization (hammockLocalizationNerveMap (modelRelativeCategory C))
    (weakNerveEdges (modelRelativeCategory C)))
  (K : kanHammockNerve (modelRelativeCategory C) ⟶ Q)
  (e : FunctorIso (hammockLocalizationNerveMap (modelRelativeCategory C) ≫ K) G)

/-- 概要：指定局所化への同じ実比較は元の射を同じ指定二胞体で共役した点へ送る。
方針：元の局所化辺の零単体公式へ同じ K と両端成分の作用を後合成する。
規約：指定 K・二胞体 e を保持し、選択した逆を変更しない。
使われ方：全 coherent 比較の零単体と元の G の射の整合。
-/
lemma rightFrameSpecifiedPinchedEquivalence_unit_Q :
    AnodyneHomotopy.anodyneQ.map
      (rightFrameHammockUnitPoint q r f 0 ≫
        (rightFrameSpecifiedPinchedEquivalence q r cof G hG hH K e Y).hom) =
    AnodyneHomotopy.anodyneQ.map
      (arrowMap (modelRelativeCategory C).weakEquivalences (AsSmall.up.map f) ≫
        exInfinityUnit.app _ ≫ kanHammockHomPinchedMap (modelRelativeCategory C)
          (modelRelativeObject C X) (modelRelativeObject C Y) ≫
            ((rightFrameSpecifiedLocalizationData G hG hH K e).pinchedEquivalence
              (nerveVertex (modelRelativeObject C X))
              (nerveVertex (modelRelativeObject C Y))).hom) := by
  rw [rightFrameSpecifiedPinchedEquivalence_hom]
  have h := congrArg (fun t => t ≫ AnodyneHomotopy.anodyneQ.map
    ((rightFrameSpecifiedLocalizationData G hG hH K e).pinchedEquivalence
      (nerveVertex (modelRelativeObject C X)) (nerveVertex (modelRelativeObject C Y))).hom)
      (rightFrameHammockPinchedEquivalence_unit_arrow_Q q r f cof)
  simpa only [Functor.map_comp, Category.assoc] using h

end SerrePositivity.EInfinity.FrameHom
