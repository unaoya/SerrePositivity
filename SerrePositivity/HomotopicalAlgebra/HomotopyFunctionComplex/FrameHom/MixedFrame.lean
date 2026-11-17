module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionHom
public import SerrePositivity.HomotopicalAlgebra.Simplicial.DiagonalAdjunction
public import Mathlib.CategoryTheory.Opposites

/-!
# 始域・終域の両 frame の実際の混合 Hom

概要：Hovey §5 の両側の frame の同次元の射を単体集合にする。
方針：二重 Hom の対角を取り、augmentation から二つの実際の比較射を作る。
規約：この段階ではモデル構造・弱同値性・Kan 性を仮定しない。
使われ方：始域 frame と右 frame の錐の自然な共通比較。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedFrame

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.SerrePositivity.HomotopyFunctionComplex

variable {C : Type u} [Category.{v} C] (A : SimplexCategory ⥤ C)

/-- 概要：終域の単体的図式から両 frame の同次元の Hom を作る（Hovey §5）。
方針：終域図式に始域の cosimplicial Hom を適用して対角を取る。
規約：すべての単体と作用素は元の圏の射。
使われ方：両側の frame の比較の共通対象。 -/
abbrev mixedFunctor : (SimplexCategoryᵒᵖ ⥤ C) ⥤ SSet.{v} :=
  (Functor.whiskeringRight SimplexCategoryᵒᵖ C SSet.{v}).obj (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A) ⋙
    _root_.SerrePositivity.BisimplicialModel.diagonal

/-- 概要：固定した始域から終域の単体的図式への Hom（Hovey §5）。
方針：元の圏の covariant Hom を図式に後合成する。
規約：各単体は元の始域からの実際の射。
使われ方：右 frame の Hom の反対射表示を元の射で扱う。 -/
abbrev rightHomFunctor (X : C) : (SimplexCategoryᵒᵖ ⥤ C) ⥤ SSet.{v} :=
  (Functor.whiskeringRight SimplexCategoryᵒᵖ C (Type v)).obj (coyoneda.obj (op X))

/-- 概要：終域の augmentation は始域 Hom から混合 Hom への比較を与える（Hovey §5）。
方針：各次元で元の射に augmentation を後合成する。
規約：比較はすべての単体作用素に自然。
使われ方：始域 frame の側から共通の混合 Hom へ移る。 -/
def leftComparison {Z : C} {R : SimplexCategoryᵒᵖ ⥤ C}
    (b : (Functor.const SimplexCategoryᵒᵖ).obj Z ⟶ R) :
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj Z ⟶ (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedFrame.mixedFunctor A).obj R where
  app n := ↾fun h => h ≫ b.app n
  naturality n m f := by
    apply ConcreteCategory.hom_ext
    intro h
    change (A.map f.unop ≫ h) ≫ b.app m = A.map f.unop ≫ (h ≫ b.app n) ≫ R.map f
    have hb : b.app m = b.app n ≫ R.map f := by
      have h := b.naturality f
      change 𝟙 Z ≫ b.app m = b.app n ≫ R.map f at h
      exact (Category.id_comp _).symm.trans h
    rw [hb]
    simp only [Category.assoc]

/-- 概要：始域の augmentation は右 Hom から混合 Hom への比較を与える（Hovey §5）。
方針：各次元で元の射に augmentation を前合成する。
規約：単体集合のモデル構造は不要。
使われ方：右 frame の側から共通の混合 Hom へ移る。 -/
def rightComparison {X : C} (a : A ⟶ (Functor.const SimplexCategory).obj X)
    (R : SimplexCategoryᵒᵖ ⥤ C) :
    (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedFrame.rightHomFunctor X).obj R ⟶ (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedFrame.mixedFunctor A).obj R where
  app n := ↾fun h => a.app n.unop ≫ h
  naturality n m f := by
    apply ConcreteCategory.hom_ext
    intro h
    change a.app m.unop ≫ (h ≫ R.map f) = A.map f.unop ≫ (a.app n.unop ≫ h) ≫ R.map f
    have ha : A.map f.unop ≫ a.app n.unop = a.app m.unop := by
      have h := a.naturality f.unop
      change A.map f.unop ≫ a.app n.unop = a.app m.unop ≫ 𝟙 X at h
      exact h.trans (Category.comp_id _)
    rw [← ha]
    simp only [Category.assoc]

/-- 概要：右 Hom は反対圏の cosimplicial Hom と同型（Hovey §5）。
方針：各次元で射を反対化する。
規約：全単体作用素で同じ元の射を保持する。
使われ方：反対圏の frame Hom の不変性を右 Hom へ移す。 -/
def rightHomIso (X : C) (R : SimplexCategoryᵒᵖ ⥤ C) :
    (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedFrame.rightHomFunctor X).obj R ≅ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom R.rightOp).obj (op X) :=
  NatIso.ofComponents (fun _ => Equiv.toIso
    { toFun := fun h => h.op
      invFun := fun h => h.unop
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }) (by
    intro n m f
    ext h
    rfl)

/-- 概要：混合 Hom の二つの座標の反転は同じ単体集合を与える（Hovey §5）。
方針：各次元の射を反対化し、二つの合成順序の結合則を照合する。
規約：新たな frame の選択は行わない。
使われ方：右側の比較を反対圏の左側の比較へ移す。 -/
def flipIso (R : SimplexCategoryᵒᵖ ⥤ C) :
    (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedFrame.mixedFunctor A).obj R ≅ (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedFrame.mixedFunctor R.rightOp).obj A.op :=
  NatIso.ofComponents (fun _ => Equiv.toIso
    { toFun := fun h => h.op
      invFun := fun h => h.unop
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }) (by
    intro n m f
    ext h
    apply Quiver.Hom.unop_inj
    change A.map f.unop ≫ (h ≫ R.map f) = (A.map f.unop ≫ h) ≫ R.map f
    exact (Category.assoc _ _ _).symm)

end SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedFrame
