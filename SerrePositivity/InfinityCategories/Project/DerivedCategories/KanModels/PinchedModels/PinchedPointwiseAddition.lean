module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.PinchedModels.PinchedNormalizedPointed

/-! # 実 pinched 写像の線形座標による加法

概要：同じ始域を持つ実 pinched Hom への二写像を、各単体の線形座標で加える。
方針：線形表示の自然性と、線形引き戻しの加法性を使う。
規約：全ての面と退化を厳密に保存する。使われ方：差の prism から元の二写像の比較へ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] {x y : D}

/-- 実 pinched Hom への写像の各単体での線形和。 -/
def pinchedPointwiseAdd {K : SSet.{max u v}}
    (f g : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y) : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y where
  app d := ↾fun a => (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex (f.app d a) + _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex (g.app d a)).toPinched
  naturality {m n} α := by
    apply ConcreteCategory.hom_ext
    intro a
    have hf := ConcreteCategory.congr_hom (f.naturality α) a
    have hg := ConcreteCategory.congr_hom (g.naturality α) a
    change f.app n (K.map α a) = (f.app m a).pullback α.unop at hf
    change g.app n (K.map α a) = (g.app m a).pullback α.unop at hg
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.linearEquiv x y n.unop.len).injective
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex (f.app n (K.map α a)) + _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex (g.app n (K.map α a))).toPinched) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex (f.app m a) + _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex (g.app m a)).toPinched.pullback α.unop)
    simp only [hf, hg, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearSimplex_toPinched, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearSimplex_pullback,
      map_add]

/-- 前合成は点ごとの線形和と厳密に可換。 -/
lemma pinchedPointwiseAdd_precomp {K L : SSet.{max u v}}
    (a : L ⟶ K) (f g : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y) :
    a ≫ pinchedPointwiseAdd f g = pinchedPointwiseAdd (a ≫ f) (a ≫ g) := rfl

/-- 零頂点の定値写像を加えても変わらない。 -/
lemma pinchedPointwiseAdd_zero {K : SSet.{max u v}} (f : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y) :
    pinchedPointwiseAdd f (SSet.const (0 : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex A x y 0).toPinched) = f := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro a
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.linearEquiv x y d.unop.len).injective
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex (f.app d a) + _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex
    ((0 : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex A x y 0).toPinched.pullback
      (SimplexCategory.const d.unop ⦋0⦌ 0))).toPinched) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex (f.app d a)
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedZeroSimplex_pullback, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearSimplex_toPinched,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearSimplex_toPinched, add_zero]

/-- 二つの単体写像の点ごとの和は、線形和の単体写像。 -/
lemma pinchedPointwiseAdd_yoneda {n : ℕ} (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex A x y n) :
    pinchedPointwiseAdd (SSet.yonedaEquiv.symm s.toPinched) (SSet.yonedaEquiv.symm t.toPinched) =
      SSet.yonedaEquiv.symm (s + t).toPinched := by
  apply SSet.yonedaEquiv.injective
  simp [SSet.yonedaEquiv, uliftYonedaEquiv, pinchedPointwiseAdd,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearSimplex_toPinched]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
