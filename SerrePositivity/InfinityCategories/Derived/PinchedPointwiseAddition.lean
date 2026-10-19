module
public import SerrePositivity.InfinityCategories.Derived.PinchedNormalizedPointed

/-! # 実 pinched 写像の線形座標による加法

概要：同じ始域を持つ実 pinched Hom への二写像を、各単体の線形座標で加える。
方針：線形表示の自然性と、線形引き戻しの加法性を使う。
規約：全ての面と退化を厳密に保存する。使われ方：差の prism から元の二写像の比較へ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerve.PinchedHom SSet
open scoped Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] {x y : D}

/-- 実 pinched Hom への写像の各単体での線形和。 -/
def pinchedPointwiseAdd {K : SSet.{max u v}}
    (f g : K ⟶ DGNerve.pinchedHom A D x y) : K ⟶ DGNerve.pinchedHom A D x y where
  app d := ↾fun a => (toLinearSimplex (f.app d a) + toLinearSimplex (g.app d a)).toPinched
  naturality {m n} α := by
    apply ConcreteCategory.hom_ext
    intro a
    have hf := ConcreteCategory.congr_hom (f.naturality α) a
    have hg := ConcreteCategory.congr_hom (g.naturality α) a
    change f.app n (K.map α a) = (f.app m a).pullback α.unop at hf
    change g.app n (K.map α a) = (g.app m a).pullback α.unop at hg
    apply (linearEquiv x y n.unop.len).injective
    change toLinearSimplex
      ((toLinearSimplex (f.app n (K.map α a)) + toLinearSimplex (g.app n (K.map α a))).toPinched) =
        toLinearSimplex
          ((toLinearSimplex (f.app m a) + toLinearSimplex (g.app m a)).toPinched.pullback α.unop)
    simp only [hf, hg, LinearSimplex.toLinearSimplex_toPinched, toLinearSimplex_pullback,
      map_add]

/-- 前合成は点ごとの線形和と厳密に可換。 -/
lemma pinchedPointwiseAdd_precomp {K L : SSet.{max u v}}
    (a : L ⟶ K) (f g : K ⟶ DGNerve.pinchedHom A D x y) :
    a ≫ pinchedPointwiseAdd f g = pinchedPointwiseAdd (a ≫ f) (a ≫ g) := rfl

/-- 零頂点の定値写像を加えても変わらない。 -/
lemma pinchedPointwiseAdd_zero {K : SSet.{max u v}} (f : K ⟶ DGNerve.pinchedHom A D x y) :
    pinchedPointwiseAdd f (SSet.const (0 : LinearSimplex A x y 0).toPinched) = f := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro a
  apply (linearEquiv x y d.unop.len).injective
  change toLinearSimplex ((toLinearSimplex (f.app d a) + toLinearSimplex
    ((0 : LinearSimplex A x y 0).toPinched.pullback
      (SimplexCategory.const d.unop ⦋0⦌ 0))).toPinched) = toLinearSimplex (f.app d a)
  rw [pinchedZeroSimplex_pullback, LinearSimplex.toLinearSimplex_toPinched,
    LinearSimplex.toLinearSimplex_toPinched, add_zero]

/-- 二つの単体写像の点ごとの和は、線形和の単体写像。 -/
lemma pinchedPointwiseAdd_yoneda {n : ℕ} (s t : LinearSimplex A x y n) :
    pinchedPointwiseAdd (SSet.yonedaEquiv.symm s.toPinched) (SSet.yonedaEquiv.symm t.toPinched) =
      SSet.yonedaEquiv.symm (s + t).toPinched := by
  apply SSet.yonedaEquiv.injective
  simp [SSet.yonedaEquiv, uliftYonedaEquiv, pinchedPointwiseAdd,
    LinearSimplex.toLinearSimplex_toPinched]

end SerrePositivity.InfinityCategories
