module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Core.Equivalence
public import SerrePositivity.InfinityCategories.Core.FunctorCompositionEvaluation
public import SerrePositivity.InfinityCategories.Core.FunctorEvaluation
public import SerrePositivity.InfinityCategories.Core.PrismContraction
public import SerrePositivity.InfinityCategories.Core.Pullback
public import SerrePositivity.InfinityCategories.Core.PushoutShape
public import SerrePositivity.InfinityCategories.F1.Transport.PointFunctorEvaluation
public import SerrePositivity.InfinityCategories.Core.Quasicategory.SquareArrowFamily

/-!
概要：矢印族とその添字の収縮から実正方形の族を構成する。
方針：矢印・収縮時間・添字の三因子を組み合わせ、四辺への制限を厳密に計算する。
規約：quasicategory 性は不要。使われ方：最終外ホーンの cartesian 判定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.InfinityCategories.F1B.Quasicategory
open SerrePositivity.KST.LocalizingInvariants

def arrowContractionSquares {A X : SSet.{u}} (c : (Δ[1] : SSet.{u}) ⊗ A ⟶ A)
    (f : A ⟶ (ihom (Δ[1] : SSet.{u})).obj X) :
    A ⟶ (ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj X :=
  curry ((α_ (Δ[1] : SSet.{u}) Δ[1] A).hom ≫ (Δ[1] ◁ c) ≫ uncurry f)

lemma arrowContractionSquares_bottom {A X : SSet.{u}} (c : (Δ[1] : SSet.{u}) ⊗ A ⟶ A)
    (f : A ⟶ (ihom (Δ[1] : SSet.{u})).obj X) :
    _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.arrowContractionSquares c f ≫ (pre squareBottomEdge).app X =
      (prismEndpoint 0 A ≫ c) ≫ f := by
  apply uncurry_injective
  rw [uncurry_pre_app, _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.arrowContractionSquares, uncurry_curry, uncurry_natural_left]
  have h : (squareBottomEdge ▷ A) ≫ (α_ (Δ[1] : SSet.{u}) Δ[1] A).hom =
      Δ[1] ◁ prismEndpoint 0 A := rfl
  rw [← Category.assoc (squareBottomEdge ▷ A), h]
  simp only [Category.assoc, whiskerLeft_comp]

lemma arrowContractionSquares_top {A X : SSet.{u}} (c : (Δ[1] : SSet.{u}) ⊗ A ⟶ A)
    (f : A ⟶ (ihom (Δ[1] : SSet.{u})).obj X) :
    _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.arrowContractionSquares c f ≫ (pre squareTopEdge).app X =
      (prismEndpoint 1 A ≫ c) ≫ f := by
  apply uncurry_injective
  rw [uncurry_pre_app, _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.arrowContractionSquares, uncurry_curry, uncurry_natural_left]
  have h : (squareTopEdge ▷ A) ≫ (α_ (Δ[1] : SSet.{u}) Δ[1] A).hom =
      Δ[1] ◁ prismEndpoint 1 A := rfl
  rw [← Category.assoc (squareTopEdge ▷ A), h]
  simp only [Category.assoc, whiskerLeft_comp]

lemma arrowContractionSquares_right {A X : SSet.{u}} (c : (Δ[1] : SSet.{u}) ⊗ A ⟶ A)
    (f : A ⟶ (ihom (Δ[1] : SSet.{u})).obj X) :
    _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.arrowContractionSquares c f ≫ (pre squareRightEdge).app X =
      curry (c ≫ f ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) := by
  apply uncurry_injective
  rw [uncurry_pre_app, _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.arrowContractionSquares, uncurry_curry, uncurry_curry]
  have h : (squareRightEdge ▷ A) ≫ (α_ (Δ[1] : SSet.{u}) Δ[1] A).hom ≫ (Δ[1] ◁ c) =
      c ≫ lift (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) (𝟙 A) := rfl
  have hev : lift (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) (𝟙 A) ≫ uncurry f =
      f ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) := by
    simpa only [curry_uncurry] using
      (curry_evaluateFunctorAt_vertex (uncurry f) (stdSimplex.obj₀Equiv.symm (1 : Fin 2))).symm
  calc
    _ = (c ≫ lift (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) (𝟙 A)) ≫ uncurry f := by
      simpa only [Category.assoc] using congrArg (fun k => k ≫ uncurry f) h
    _ = _ := by rw [Category.assoc, hev]

lemma arrowContractionSquares_left {A X : SSet.{u}} (c : (Δ[1] : SSet.{u}) ⊗ A ⟶ A)
    (f : A ⟶ (ihom (Δ[1] : SSet.{u})).obj X) :
    _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.arrowContractionSquares c f ≫ (pre squareLeftEdge).app X =
      curry (c ≫ f ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) := by
  apply uncurry_injective
  rw [uncurry_pre_app, _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.arrowContractionSquares, uncurry_curry, uncurry_curry]
  have h : (squareLeftEdge ▷ A) ≫ (α_ (Δ[1] : SSet.{u}) Δ[1] A).hom ≫ (Δ[1] ◁ c) =
      c ≫ lift (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) (𝟙 A) := rfl
  have hev : lift (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) (𝟙 A) ≫ uncurry f =
      f ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
    simpa only [curry_uncurry] using
      (curry_evaluateFunctorAt_vertex (uncurry f) (stdSimplex.obj₀Equiv.symm (0 : Fin 2))).symm
  calc
    _ = (c ≫ lift (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) (𝟙 A)) ≫ uncurry f := by
      simpa only [Category.assoc] using congrArg (fun k => k ≫ uncurry f) h
    _ = _ := by rw [Category.assoc, hev]

def contractionAtVertex {A : SSet.{u}} (c : (Δ[1] : SSet.{u}) ⊗ A ⟶ A) (v : A _⦋0⦌) :
    (Δ[1] : SSet.{u}) ⟶ A := lift (𝟙 _) (SSet.const v) ≫ c

lemma arrowContractionSquares_vertex {A X : SSet.{u}} (c : (Δ[1] : SSet.{u}) ⊗ A ⟶ A)
    (f : A ⟶ (ihom (Δ[1] : SSet.{u})).obj X) (v : A _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.arrowContractionSquares c f).app (Opposite.op ⦋0⦌) v =
      functorVertex (uncurry (_root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.contractionAtVertex c v ≫ f)) := by
  apply CategoryTheory.Functor.functorHom_ext
  intro d α
  have hα : α = (SimplexCategory.const d.unop ⦋0⦌ 0).op := Subsingleton.elim _ _
  subst α
  apply ConcreteCategory.hom_ext
  intro s
  rfl

end SerrePositivity.InfinityCategories.F1B.Quasicategory

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.arrowContractionSquares (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.arrowContractionSquares := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.arrowContractionSquares

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.arrowContractionSquares_bottom := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.arrowContractionSquares_bottom

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.arrowContractionSquares_left := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.arrowContractionSquares_left

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.arrowContractionSquares_right := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.arrowContractionSquares_right

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.arrowContractionSquares_top := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.arrowContractionSquares_top

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.arrowContractionSquares_vertex := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.arrowContractionSquares_vertex

@[deprecated _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.contractionAtVertex (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.contractionAtVertex := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.contractionAtVertex

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.arrowContractionSquares.eq_1 := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.arrowContractionSquares.eq_1
