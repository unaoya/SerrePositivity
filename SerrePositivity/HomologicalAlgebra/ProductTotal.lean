module
public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.Algebra.Homology.Opposite
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.Limits.Shapes.Products
import all Mathlib.Algebra.Homology.TotalComplex

/-!
概要：非有界二重余鎖複体の積全複体と、その成分への指定射影。
方針：両方の複体方向を反対圏へ移し、直和 total を反転する。
規約：対角線の有限性も積の完全性も仮定しない。必要なのは反対圏の直和の存在。
使われ方：HA 1.2.4、IS-W2 の余単体的複体の Tot。native 極限性はここでは主張しない。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open CategoryTheory Limits Opposite
namespace SerrePositivity.HomologicalAlgebra.ProductTotal

set_option backward.defeqAttrib.useBackward true in
/-- 積 total を反対圏で計算するときの整数鎖次数の符号。 -/
scoped instance : ComplexShape.TensorSigns (ComplexShape.down ℤ) where
  ε' := MonoidHom.mk' Int.negOnePow Int.negOnePow_add
  rel_add p q r h := by change _ + 1 = _ at h ⊢; omega
  add_rel p q r h := by change _ + 1 = _ at h ⊢; omega
  ε'_succ := by
    rintro p q h
    change q + 1 = p at h
    subst p
    change Int.negOnePow q = -Int.negOnePow (q + 1)
    rw [Int.negOnePow_succ, neg_neg]

variable (C : Type u) [Category.{v} C] [Preadditive C]

/-- 両方の複体方向を反転する全関手。 -/
def doubleOpFunctor :
    (HomologicalComplex₂ C (.up ℤ) (.up ℤ))ᵒᵖ ⥤
      HomologicalComplex₂ Cᵒᵖ (.down ℤ) (.down ℤ) :=
  HomologicalComplex.opFunctor (CochainComplex C ℤ) (.up ℤ) ⋙
    (HomologicalComplex.opFunctor C (.up ℤ)).mapHomologicalComplex (.down ℤ)

variable [∀ K : HomologicalComplex₂ Cᵒᵖ (.down ℤ) (.down ℤ), K.HasTotal (.down ℤ)]

/-- 積全複体の全関手。次数 q の対象は a+b=q の成分の積。 -/
def functor : HomologicalComplex₂ C (.up ℤ) (.up ℤ) ⥤ CochainComplex C ℤ :=
  (doubleOpFunctor C ⋙
    HomologicalComplex₂.totalFunctor Cᵒᵖ (.down ℤ) (.down ℤ) (.down ℤ )).rightOp ⋙
      HomologicalComplex.unopFunctor C (.down ℤ)

variable {C}
/-- 元の二重複体の指定された (a,b) 成分への射影。 -/
def π (K : HomologicalComplex₂ C (.up ℤ) (.up ℤ)) (a b q : ℤ) (h : a+b=q) :
    ((functor C).obj K).X q ⟶ (K.X a).X b :=
  (((doubleOpFunctor C).obj (op K)).ιTotal (.down ℤ) a b q h).unop

/-- 積全複体の一つの次数へ、成分の族から射を作る。 -/
def lift (K : HomologicalComplex₂ C (.up ℤ) (.up ℤ)) {M : C} (q : ℤ)
    (f : ∀ a b : ℤ, a+b=q → (M ⟶ (K.X a).X b)) :
    M ⟶ ((functor C).obj K).X q :=
  (((doubleOpFunctor C).obj (op K)).totalDesc (fun a b h => (f a b h).op)).unop

@[reassoc (attr := simp)]
theorem lift_π (K : HomologicalComplex₂ C (.up ℤ) (.up ℤ)) {M : C} (q : ℤ)
    (f : ∀ a b : ℤ, a+b=q → (M ⟶ (K.X a).X b)) (a b : ℤ) (h : a+b=q) :
    lift K q f ≫ π K a b q h = f a b h := by
  exact congrArg Quiver.Hom.unop
    (((doubleOpFunctor C).obj (op K)).ι_totalDesc (fun a b h => (f a b h).op) a b h)

/-- 指定射影は積全複体への射を判定する。 -/
@[ext]
theorem hom_ext (K : HomologicalComplex₂ C (.up ℤ) (.up ℤ)) {M : C} (q : ℤ)
    {f g : M ⟶ ((functor C).obj K).X q}
    (h : ∀ a b (hab : a+b=q), f ≫ π K a b q hab = g ≫ π K a b q hab) : f = g := by
  apply Quiver.Hom.op_inj
  apply HomologicalComplex₂.total.hom_ext
  intro a b hab
  exact congrArg Quiver.Hom.op (h a b hab)

/-- 元の二重複体の射の各成分と、指定射影の厳密な自然性。 -/
@[reassoc]
theorem map_π {K L : HomologicalComplex₂ C (.up ℤ) (.up ℤ)} (f : K ⟶ L)
    (a b q : ℤ) (h : a+b=q) :
    ((functor C).map f).f q ≫ π L a b q h =
      π K a b q h ≫ (f.f a).f b := by
  exact congrArg Quiver.Hom.unop
    (HomologicalComplex₂.ιTotal_map _ _ ((doubleOpFunctor C).map f.op) (.down ℤ) a b q h)

/-- 全微分の指定成分は横微分と符号付き縦微分の二項だけからなる。 -/
theorem d_π (K : HomologicalComplex₂ C (.up ℤ) (.up ℤ))
    (a b q : ℤ) (h : a+b=q+1) :
    ((functor C).obj K).d q (q+1) ≫ π K a b (q+1) h =
      π K (a-1) b q (by omega) ≫ (K.d (a-1) a).f b +
      a.negOnePow • (π K a (b-1) q (by omega) ≫ (K.X a).d (b-1) b) := by
  let L := (doubleOpFunctor C).obj (op K)
  have hh : L.ιTotal (.down ℤ) a b (q+1) h ≫ (L.total (.down ℤ)).d (q+1) q =
      (L.d a (a-1)).f b ≫ L.ιTotal (.down ℤ) (a-1) b q (by dsimp; omega) +
      a.negOnePow • ((L.X a).d b (b-1) ≫
        L.ιTotal (.down ℤ) a (b-1) q (by dsimp; omega)) := by
    change _ ≫ (L.D₁ (.down ℤ) (q+1) q + L.D₂ (.down ℤ) (q+1) q) = _
    rw [Preadditive.comp_add, L.ι_D₁, L.ι_D₂,
      L.d₁_eq (.down ℤ) (i₁' := a-1) (by change a-1+1=a; omega) b q (by dsimp; omega),
      L.d₂_eq (.down ℤ) a (i₂' := b-1) (by change b-1+1=b; omega) q (by dsimp; omega)]
    simp [ComplexShape.ε₁, ComplexShape.ε₂, ComplexShape.ε, L]
    rfl
  simpa [Units.smul_def, functor, π, L, doubleOpFunctor,
    HomologicalComplex.opFunctor, HomologicalComplex.unopFunctor,
    HomologicalComplex₂.totalFunctor] using congrArg Quiver.Hom.unop hh

/-- 全次数 q の指定射影を持つ積錐。 -/
def fan (K : HomologicalComplex₂ C (.up ℤ) (.up ℤ)) (q : ℤ) :
    Fan (fun ab : {ab : ℤ × ℤ // ab.1 + ab.2 = q} => (K.X ab.val.1).X ab.val.2) :=
  Fan.mk (((functor C).obj K).X q) (fun ab => π K ab.val.1 ab.val.2 q ab.property)

/-- 各全次数の対象が実際に対角線成分の積であること。 -/
def fanIsLimit (K : HomologicalComplex₂ C (.up ℤ) (.up ℤ)) (q : ℤ) :
    IsLimit (fan K q) :=
  Fan.IsLimit.mk _
    (fun s => lift K q (fun a b h => s.π.app ⟨⟨(a,b), h⟩⟩))
    (by intro s ab; exact lift_π K q _ ab.val.1 ab.val.2 ab.property)
    (by
      intro s m hm
      apply hom_ext K q
      intro a b hab
      rw [lift_π]
      exact hm ⟨(a,b), hab⟩)

end SerrePositivity.HomologicalAlgebra.ProductTotal
