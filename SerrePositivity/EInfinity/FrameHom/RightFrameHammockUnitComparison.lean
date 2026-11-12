module

public import SerrePositivity.EInfinity.FrameHom.RightFrameHammockUnitPoints

/-!
概要：同じ六辺から選択した実比較の零単体を元の hammock 射へ照合する。
方針：全段階の同じ単位点を Ex∞ 自然性で送り、指定逆の単位で合成する。
規約：元の射・元の比較・選択した逆を保持する。
使われ方：指定局所化の二胞体による共役公式への入力。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.EInfinity.FrameHom
open CategoryTheory HomotopicalAlgebra SSet Opposite Hammock MonoidalCategory
open SerrePositivity.Reedy SerrePositivity.InfinityCategories SerrePositivity.SimplicialModel

open scoped Simplicial

/-- 概要：同じ逆比較で単位点の等式を逆向きへ送る。
方針：元の指定逆の単位を使い、右から同じ逆を合成する。
規約：反転後の同じ点。使われ方：六辺の三つの逆向き辺。 -/
lemma point_inverse_Q {A B T : SSet.{w}} [Quasicategory A] [Quasicategory B]
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence A B) (a : T ⟶ A) (b : T ⟶ B)
    (h : AnodyneHomotopy.anodyneQ.map a ≫ AnodyneHomotopy.anodyneQ.map e.hom =
      AnodyneHomotopy.anodyneQ.map b) :
    AnodyneHomotopy.anodyneQ.map b ≫ AnodyneHomotopy.anodyneQ.map e.inv =
      AnodyneHomotopy.anodyneQ.map a := by
  rw [← h, Category.assoc, qCatEquivalence_hom_inv_Q, Category.comp_id]

variable {C : Type u} [Category.{v} C] [ModelCategory C] {X Y : C}
  (q : CofibrantResolution (C := C) simplex X)
  (r : CofibrantResolutionFamily (C := Cᵒᵖ) simplex) (f : X ⟶ Y)

/-- 概要：元の各単位点の Kan 化を同じ六辺で追跡する。
方針：同じ Ex∞ 単位の自然性を元の六辺の等式に合成する。
規約：全辺の元の向き。使われ方：実成分比較の零単体公式。 -/
lemma rightFrameHammockKanUnitPoint_edge_Q (i : Fin 6) :
    AnodyneHomotopy.anodyneQ.map
      (rightFrameHammockUnitPoint q r f (rightFrameHammockEdgeSource i) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app _) ≫
      AnodyneHomotopy.anodyneQ.map ((rightFrameHammockKanEdge q r i).app
        (AsSmall.up.obj Y)) =
    AnodyneHomotopy.anodyneQ.map
      (rightFrameHammockUnitPoint q r f (rightFrameHammockEdgeTarget i) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app _) := by
  let p := rightFrameHammockUnitPoint q r f (rightFrameHammockEdgeSource i)
  let a := (rightFrameHammockFamilyEdge q r i).app Y
  have h := congrArg (p ≫ ·) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.naturality a)
  have hQ := congrArg AnodyneHomotopy.anodyneQ.map h
  simp only [Functor.map_comp, Category.assoc] at hQ ⊢
  exact hQ.symm.trans (by
    rw [← Category.assoc, ← Functor.map_comp]
    exact congrArg (fun t => t ≫ AnodyneHomotopy.anodyneQ.map (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app _))
      (rightFrameHammockUnitPoint_edge_Q q r f i))

variable [IsCofibrant X]
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
attribute [local instance] rightFrameHammockKanDiagram_kanComplex _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameHom_kanComplex

/-- 概要：選択した同じ全六辺の実合成は元の射の零単体を回収する。
方針：三つの順向き辺と三つの逆向き辺の単位点を順に合成する。
規約：同じ実 QCat 同値の順射を保持する。
使われ方：元の frame 比較の零単体と指定局所化射の照合。 -/
lemma rightFrameHammockKanComponentEquivalence_unit_Q :
    AnodyneHomotopy.anodyneQ.map
      ((rightFrameHammockUnitPoint q r f 0 ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app _) ≫
        (rightFrameHammockKanComponentEquivalence q r cof Y).hom) =
    AnodyneHomotopy.anodyneQ.map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap (weakEquivalences C) f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app _) := by
  let p (i : Fin 7) := rightFrameHammockUnitPoint q r f i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app _
  let e (i : Fin 6) := rightFrameHammockKanEdgeEquivalence q r cof i (AsSmall.up.obj Y)
  have h (i : Fin 6) : AnodyneHomotopy.anodyneQ.map (p (rightFrameHammockEdgeSource i)) ≫
      AnodyneHomotopy.anodyneQ.map (e i).hom =
        AnodyneHomotopy.anodyneQ.map (p (rightFrameHammockEdgeTarget i)) :=
    rightFrameHammockKanUnitPoint_edge_Q q r f i
  have h0 := h 0
  have h1 := h 1
  have h4 := h 4
  dsimp only [rightFrameHammockEdgeSource, rightFrameHammockEdgeTarget] at h0 h1 h4
  have h2 := point_inverse_Q (e 2) (p 3) (p 2) (h 2)
  have h3 := point_inverse_Q (e 3) (p 4) (p 3) (h 3)
  have h5 := point_inverse_Q (e 5) (p 6) (p 5) (h 5)
  change AnodyneHomotopy.anodyneQ.map
    (p 0 ≫ (e 0).hom ≫ (e 1).hom ≫ (e 2).inv ≫ (e 3).inv ≫ (e 4).hom ≫ (e 5).inv) =
      AnodyneHomotopy.anodyneQ.map (p 6)
  simp only [Functor.map_comp]
  rw [← Category.assoc, h0]
  rw [← Category.assoc, h1]
  rw [← Category.assoc, h2]
  rw [← Category.assoc, h3]
  rw [← Category.assoc, h4]
  exact h5

/-- 概要：元の実 right frame→pinched 比較は元の射の同じ hammock 零単体を回収する。
方針：六辺の元の零単体公式に同じ宇宙同型と coherent Hom 比較を後合成する。
規約：同じ実 QCat 比較の順射。使われ方：指定二胞体による元の局所化射への共役。
-/
lemma rightFrameHammockPinchedEquivalence_unit_Q :
    AnodyneHomotopy.anodyneQ.map
      (rightFrameHammockUnitPoint q r f 0 ≫
        (rightFrameHammockPinchedEquivalence q r cof Y).hom) =
    AnodyneHomotopy.anodyneQ.map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap (weakEquivalences C) f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app _ ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (AsSmallComparison.colimitIso (weakEquivalences C) X Y).hom ≫
          SimplicialLocalization.kanHammockHomPinchedMap
            (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory C)
            (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeObject C X)
            (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeObject C Y)) := by
  rw [rightFrameHammockPinchedEquivalence_factor]
  have h := congrArg (fun t => t ≫ AnodyneHomotopy.anodyneQ.map
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (AsSmallComparison.colimitIso (weakEquivalences C) X Y).hom ≫
      SimplicialLocalization.kanHammockHomPinchedMap
        (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory C)
        (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeObject C X)
        (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeObject C Y)))
      (rightFrameHammockKanComponentEquivalence_unit_Q q r f cof)
  simpa only [Functor.map_comp, Category.assoc] using h

end SerrePositivity.EInfinity.FrameHom
