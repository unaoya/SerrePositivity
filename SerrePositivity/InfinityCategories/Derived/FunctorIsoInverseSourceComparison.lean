module
public import SerrePositivity.InfinityCategories.Derived.FunctorIsoSandwichCompositor
public import SerrePositivity.InfinityCategories.Derived.FunctorIsoPrecompIdentity
public import SerrePositivity.InfinityCategories.Derived.ActionComparisonComposition
public import SerrePositivity.InfinityCategories.F2.CatInfinity.FunctorIsoWhiskerExchange
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.FunctorIsoWhiskerCancellation
/-!
概要：始域同値の指定逆を使う比較を、前向きの比較正方形へ回収する。
方針：同じ比較値・前後合成の交換則を保持する。
規約：同値の三角式は仮定しない。使われ方：一般 cell 合成子の五角式。
-/
@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
def functorIsoInverseSourceComparison {X A Y : SSet.{u}}
    (L : X ⟶ A) (s : A ⟶ X) (e : FunctorIso (L ≫ s) (𝟙 X))
    (F : A ⟶ Y) (M : X ⟶ Y) (a : FunctorIso F (s ≫ M)) :
    FunctorIso (L ≫ F) M := by
  have q := a.precomp L ≪≫ e.postcomp M
  exact q
lemma functorIsoInverseSourceComparison_refl {X A Y : SSet.{u}}
    (L : X ⟶ A) (s : A ⟶ X) (e : FunctorIso (L ≫ s) (𝟙 X)) (M : X ⟶ Y) :
    functorIsoInverseSourceComparison L s e (s ≫ M) M (Iso.refl _) = e.postcomp M := by
  simp only [functorIsoInverseSourceComparison, F2.functorIso_precomp_eq_mapIso,
    CategoryTheory.Functor.mapIso_refl]
  exact Iso.refl_trans _
lemma functorIsoInverseSource_transport {X A Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y]
    (L : X ⟶ A) (s : A ⟶ X) (e : FunctorIso (L ≫ s) (𝟙 X))
    (F : A ⟶ Y) (M N : X ⟶ Y) (a : FunctorIso F (s ≫ M)) (t : FunctorIso M N) :
    (FunctorIso.precomp (a ≪≫ t.precomp s) L) ≪≫ e.postcomp N =
      functorIsoInverseSourceComparison L s e F M a ≪≫ t := by
  have hx := F2.functorIso_whisker_exchange e t
  have he : e.postcomp M ≪≫ t = t.precomp (L ≫ s) ≪≫ e.postcomp N := by
    simpa only [functorIso_precomp_id] using! hx
  calc
    _ = a.precomp L ≪≫ (t.precomp (L ≫ s) ≪≫ e.postcomp N) := by
      simp only [F2.functorIso_precomp_trans, F2.functorIso_precomp_precomp, Iso.trans_assoc]
    _ = a.precomp L ≪≫ (e.postcomp M ≪≫ t) := by rw [← he]
    _ = _ := by simp only [functorIsoInverseSourceComparison, Iso.trans_assoc]
end
end SerrePositivity.InfinityCategories
