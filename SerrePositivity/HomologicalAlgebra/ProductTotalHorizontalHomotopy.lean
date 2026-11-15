module
public import SerrePositivity.HomologicalAlgebra.ProductTotalHorizontalComponents

/-!
概要：非有界二重複体の横ホモトピーを、同じ積全複体のホモトピーへ移す。
方針：指定射影で横ホモトピー方程式を使い、縦微分の二項を隣接する横次数の符号で相殺する。
規約：有界性・積の完全性・収束を仮定しない。比較に使う二つの射を保持する。
使われ方：HA 1.2.4、G10 の線形重みの分解比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory Limits Preadditive HomologicalComplex
open scoped SerrePositivity.HomologicalAlgebra.ProductTotal
namespace SerrePositivity.HomologicalAlgebra.ProductTotal
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [∀ K : HomologicalComplex₂ Cᵒᵖ (.down ℤ) (.down ℤ), K.HasTotal (.down ℤ)]
variable {K L : HomologicalComplex₂ C (.up ℤ) (.up ℤ)} {f g : K ⟶ L}

/-- 同じ積射影での横ホモトピー方程式。 -/
theorem horizontalComponent_comm (h : Homotopy f g) (p : ℤ) :
    ((functor C).map f).f p =
      ((functor C).obj K).d p (p+1) ≫
        horizontalComponent (fun a => h.hom (a+1) a) (p+1) p +
      horizontalComponent (fun a => h.hom (a+1) a) p (p-1) ≫
        ((functor C).obj L).d (p-1) p + ((functor C).map g).f p := by
  apply hom_ext L p
  intro a b hab
  have hh := h.comm a
  rw [dNext_eq _ (by simp : (ComplexShape.up ℤ).Rel a (a+1)),
    prevD_eq _ (by simp : (ComplexShape.up ℤ).Rel (a-1) a)] at hh
  have hhb := congrArg (fun k => k.f b) hh
  rw [map_π, add_comp, add_comp, map_π, Category.assoc,
    horizontalComponent_π, πOrZero_eq K (a+1) b (p+1) (by omega),
    ← Category.assoc, d_π K (a+1) b p (by omega)]
  have hd : ((functor C).obj L).d (p-1) p ≫ π L a b p hab =
      π L (a-1) b (p-1) (by omega) ≫ (L.d (a-1) a).f b +
      a.negOnePow • (π L a (b-1) (p-1) (by omega) ≫ (L.X a).d (b-1) b) := by
    have haux (m : ℤ) (hm : p-1+1 = m) (hab' : a+b=m) :
        ((functor C).obj L).d (p-1) m ≫ π L a b m hab' =
          π L (a-1) b (p-1) (by omega) ≫ (L.d (a-1) a).f b +
          a.negOnePow • (π L a (b-1) (p-1) (by omega) ≫ (L.X a).d (b-1) b) := by
      cases hm
      exact d_π L a b (p-1) hab'
    exact haux p (by omega) hab
  rw [Category.assoc, hd, comp_add, Linear.comp_units_smul,
    ← Category.assoc, horizontalComponent_π,
    ← Category.assoc, horizontalComponent_π]
  have hs (c : ℤ) (hc : c = a) (hcb : c+b=p) :
      π K c b p hcb ≫ (K.d c (a+1)).f b =
        π K a b p hab ≫ (K.d a (a+1)).f b := by cases hc; rfl
  rw [hs (a+1-1) (by omega)]
  have ht : πOrZero K (a-1+1) b p ≫ (h.hom (a-1+1) (a-1)).f b =
      π K a b p hab ≫ (h.hom a (a-1)).f b := by
    rw [sub_add_cancel, πOrZero_eq K a b p hab]
  rw [ht, πOrZero_eq K (a+1) (b-1) p (by omega)]
  rw [add_comp, Linear.units_smul_comp]
  simp only [Category.assoc, Int.negOnePow_succ, Units.neg_smul]
  rw [← (h.hom (a+1) a).comm (b-1) b]
  change (f.f a).f b = (K.d a (a+1)).f b ≫ (h.hom (a+1) a).f b +
    (h.hom a (a-1)).f b ≫ (L.d (a-1) a).f b + (g.f a).f b at hhb
  rw [hhb]
  simp only [comp_add]
  abel

/-- 元の二つの射の横ホモトピーを、積 Tot の同じ二つの射へ移す。 -/
def horizontalHomotopy (h : Homotopy f g) :
    Homotopy ((functor C).map f) ((functor C).map g) where
  hom := horizontalComponent (fun a => h.hom (a+1) a)
  zero := horizontalComponent_shape _
  comm p := by
    rw [dNext_eq _ (by simp : (ComplexShape.up ℤ).Rel p (p+1)),
      prevD_eq _ (by simp : (ComplexShape.up ℤ).Rel (p-1) p)]
    exact horizontalComponent_comm h p

end SerrePositivity.HomologicalAlgebra.ProductTotal
