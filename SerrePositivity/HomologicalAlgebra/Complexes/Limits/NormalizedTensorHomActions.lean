module

public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.TruncatedDoldKanFunctor

/-!
# 元の前後合成と実正規化テンソル Hom 同値の全次数整合

概要：元の複体射の前後作用は、同じ実 Hom 複体上の前後作用の DK 像へ移る。
方針：実閉随伴の両変数自然性と構成した正規化 Hom の標的自然性を使う。
規約：全複体・全次数の同じ射に対する等式。
使われ方：自由単位による前合成と正規化 Hom 比較の同定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

lemma normalizedSimplexTensorHomEquiv_postcomp (X : Complex A) {Y Z : Complex A}
    (n : SimplexCategory) (f : (_root_.SerrePositivity.ComplexLimits.normalizedSimplexTensor A X).obj n ⟶ Y) (g : Y ⟶ Z) :
    _root_.SerrePositivity.ComplexLimits.normalizedSimplexTensorHomEquiv A X Z n (f ≫ g) =
      ((_root_.SerrePositivity.ComplexLimits.truncatedDoldKanFunctor A).map (homPostcompose X g)).app (Opposite.op n)
        (_root_.SerrePositivity.ComplexLimits.normalizedSimplexTensorHomEquiv A X Y n f) := by
  change _root_.SerrePositivity.ComplexLimits.normalizedSimplexHomEquiv A _ n (tensorHomEquiv X _ Z (f ≫ g)) = _
  rw [tensorHomEquiv_naturality_target]
  exact _root_.SerrePositivity.ComplexLimits.normalizedSimplexHomEquiv_postcomp A n _ _

lemma normalizedSimplexTensorHomEquiv_precomp {X X' : Complex A} (Y : Complex A)
    (g : X' ⟶ X) (n : SimplexCategory) (f : (_root_.SerrePositivity.ComplexLimits.normalizedSimplexTensor A X).obj n ⟶ Y) :
    _root_.SerrePositivity.ComplexLimits.normalizedSimplexTensorHomEquiv A X' Y n
      ((g ▷ (_root_.SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).obj (SSet.stdSimplex.obj n)) ≫ f) =
      ((_root_.SerrePositivity.ComplexLimits.truncatedDoldKanFunctor A).map (homPrecompose g Y)).app (Opposite.op n)
        (_root_.SerrePositivity.ComplexLimits.normalizedSimplexTensorHomEquiv A X Y n f) := by
  change _root_.SerrePositivity.ComplexLimits.normalizedSimplexHomEquiv A _ n (tensorHomEquiv X' _ Y (_ ≫ f)) = _
  rw [tensorHomEquiv_naturality_domain]
  exact _root_.SerrePositivity.ComplexLimits.normalizedSimplexHomEquiv_postcomp A n _ _

lemma internalHom_pre_eq {X X' : Complex A} (g : X' ⟶ X) (Y : Complex A) :
    (MonoidalClosed.pre g).app Y = homPrecompose g Y := by
  have h := tensorHomEquiv_naturality_domain g ((ihom.ev X).app Y)
  change MonoidalClosed.curry (_ ≫ (ihom.ev X).app Y) =
    MonoidalClosed.curry ((ihom.ev X).app Y) ≫ homPrecompose g Y at h
  rw [← MonoidalClosed.curry_pre_app, ← MonoidalClosed.uncurry_id_eq_ev,
    MonoidalClosed.curry_uncurry, Category.id_comp, Category.id_comp] at h
  exact h

end SerrePositivity.ComplexLimits
