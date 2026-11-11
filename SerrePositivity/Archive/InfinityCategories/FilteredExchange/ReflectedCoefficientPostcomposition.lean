module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.MorphismInitialHeadCoordinates
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedRepresentableCoefficients
/-!
概要：反転した全 Hom 係数の後合成と head の二射合成を整合させる。
方針：反転の自然性と豊穣合成の結合則を全次数で評価する。
規約：非定値な元の係数を保持し、固定射だけを定値単体として扱う。
使われ方：最大化側の最後辺の全係数を、第一射の作用後の最後射と照合する。
-/

@[expose] public section
noncomputable section
open CategoryTheory SSet SimplicialThickening MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
/-- 概要：後合成した反転係数の評価は、同じ係数の反転評価の後合成。
方針：Yoneda の自然性と反転の後合成則を使う。
規約：全次数の係数を保持。使われ方：実 prism の係数作用の計算。 -/
lemma reflectedSimplexMap_post_app {X Y : SSet.{u}} (f : X ⟶ Y) {n : ℕ}
    (p : X.op _⦋n⦌) :
    reflectedSimplexMap (SSet.yonedaEquiv.symm ((SSet.opFunctor.map f).app (Opposite.op ⦋n⦌) p)) =
      reflectedSimplexMap (SSet.yonedaEquiv.symm p) ≫ f := by
  have h : SSet.yonedaEquiv.symm ((SSet.opFunctor.map f).app (Opposite.op ⦋n⦌) p) =
      SSet.yonedaEquiv.symm p ≫ SSet.opFunctor.map f := by
    apply SSet.yonedaEquiv.injective
    simp only [Equiv.apply_symm_apply, SSet.yonedaEquiv_comp]
  rw [h, reflectedSimplexMap_post]
/-- 概要：第一射を作用させた係数と最後射の head は、二射合成の head に等しい。
方針：whiskering を豊穣合成として評価し、結合則を使う。
規約：係数の定値性を仮定しない。使われ方：Ncomp の head の全 Hom 比較。 -/
lemma simplicialHom_postcomp_head {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {x X Y Z : C} {A : SSet.{u}} (q : A ⟶ SimplicialCategory.sHom x X)
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    lift (q ≫ eHomWhiskerLeft SSet x f)
      (SSet.const (SimplicialCategory.homEquiv' _ _ g)) ≫ eComp SSet x Y Z =
    lift q (SSet.const (SimplicialCategory.homEquiv' _ _ (f ≫ g))) ≫ eComp SSet x X Z := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro a
  change (eComp SSet x Y Z).app d
    ((eHomWhiskerLeft SSet x f).app d (q.app d a),
      PinchedHom.constant (SimplicialCategory.homEquiv' _ _ g) d.unop.len) =
    (eComp SSet x X Z).app d (q.app d a,
      PinchedHom.constant (SimplicialCategory.homEquiv' _ _ (f ≫ g)) d.unop.len)
  have h := simplicialHomWhiskerLeft_app x f d (q.app d a)
  change (eHomWhiskerLeft SSet x f).app d (q.app d a) = _ at h
  rw [h, simplicialHom_assoc_elements, simplicialHom_constant_comp]
/-- 概要：固定射との head の豊穣合成は同じ係数の後合成。
方針：whiskering の各次数の公式を使う。
規約：全係数を保持。使われ方：最後辺の零時刻の head を揃える。 -/
lemma simplicialHom_head_postcomp {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {x X Y : C} {A : SSet.{u}} (q : A ⟶ SimplicialCategory.sHom x X) (f : X ⟶ Y) :
    lift q (SSet.const (SimplicialCategory.homEquiv' _ _ f)) ≫ eComp SSet x X Y =
      q ≫ eHomWhiskerLeft SSet x f := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro a
  exact (simplicialHomWhiskerLeft_app x f d (q.app d a)).symm
end SerrePositivity.InfinityCategories.F2
