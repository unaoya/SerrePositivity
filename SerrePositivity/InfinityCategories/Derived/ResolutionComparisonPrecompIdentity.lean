module
public import SerrePositivity.InfinityCategories.Derived.FunctorIsoPrecompIdentity
public import SerrePositivity.InfinityCategories.Derived.ResolutionProjectionComparison
public import SerrePositivity.InfinityCategories.Derived.ResolutionSourceComparisonNormalization
public import SerrePositivity.InfinityCategories.F2.CatInfinity.FunctorIsoWhiskerUnit
/-!
概要：元の指定分解変更比較を、同じ実二経路の前合成比較と入力変換へ同定する。
方針：恒等入力と二段前合成則を保ち、元の指定射の共役式を回収する。
規約：同値の逆と比較を選び直さない。使われ方：元の導来射作用との照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet MonoidalClosed
lemma qCatResolutionOutputComparisonIso_precomp_id_heq
    {X Y A T : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    [Quasicategory A] [Quasicategory T]
    (Q : QCatEquivalence X A) (S : QCatEquivalence Y A)
    (H : X ⟶ Y) (RX : X ⟶ T) (RY : Y ⟶ T)
    (hs : H ≫ S.hom = Q.hom) (hr : H ≫ RY = RX) :
    HEq (qCatResolutionOutputComparisonIso Q S H RX RY hs hr)
      (qCatResolutionOutputPrecompIso Q S (𝟙 A) H RX RY
        (by simpa only [Category.comp_id] using hs) hr) := by
  subst RX
  simp only [qCatResolutionOutputComparisonIso, qCatResolutionOutputPrecompIso,
    F2.functorIso_postcomp_id, functorIso_precomp_id, Eq.mp, Eq.mpr]
  rfl
end SerrePositivity.InfinityCategories
