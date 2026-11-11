module
public import SerrePositivity.KST.SConstruction.DGStrictGluingFunctor
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.PrimitiveComparison

/-!
概要：元全 Hom 自然な閉比較から作った厳密 gluing 関手の第三比較は零である。
方針：元 comma 関手の厳密回収と代表 Hom 比較を使い、同じ零 cochain を戻す。
規約：任意の gluing 斉次射の第三成分を零とは仮定しない。
使われ方：実中央射の元始域に戻した逆回転比較の全自然性。
-/
@[expose] public section
noncomputable section
universe u v w t
namespace SerrePositivity.KST.SConstruction
open CategoryTheory CochainComplex HomComplex
open DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)
  {P : Type t} [DGCategory R P]
  (L : DGFunctor R P C) (G : DGFunctor R P D)
  (μ : ∀ x, zeroCycles (M.value (L.obj x) (G.obj x)))
  (h : ∀ x y,
    G.map x y ≫ M.toFunctor.map (G.obj x) (G.obj y) ≫
      eHomWhiskerRight (Complex R)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingAugmentation R C D M (dgStrictGluingObject R C D M L G μ x))
        (ForgetEnrichment.of (Complex R) (M.toFunctor.obj (G.obj y))) =
    (L.comp (dgYoneda R C)).map x y ≫
      eHomWhiskerLeft (Complex R)
        (ForgetEnrichment.of (Complex R) (representable R (L.obj x)))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingAugmentation R C D M (dgStrictGluingObject R C D M L G μ y)))
local notation "H" => dgStrictGluingFunctor R C D M L G μ h

/-- 概要：同じ元厳密 gluing 関手の全 Hom 上の第三比較は指定零。
方針：同じ comma 因子分解と零比較の回収を使う。
規約：全パラメーター複体の等号。使われ方：第三成分零の cone 計算への帰着。 -/
lemma dgStrictGluingFunctor_comparison_zero (x y : P) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComparison R C D M ((H).obj x) ((H).obj y)
      (homObject R P x y) ((H).map x y) = 0 := by
  let A := dgStrictGluingCommaFamily R C D M L G μ h
  have hm : (H).map x y ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomRepresentableIso R C D M ((H).obj x) ((H).obj y)).hom =
      A.toDGFunctor.map x y := by
    have he : HEq (((H).comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToComma R C D M)).map x y)
        (A.toDGFunctor.map x y) := by
      rw [dgStrictGluingFunctor_toComma]
    exact eq_of_heq he
  have he := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComparison_yoneda R C D M ((H).obj x) ((H).obj y)
    (homObject R P x y) ((H).map x y)
  rw [hm] at he
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComparison R D (RightModule R C) M.toFunctor
    (A.obj x) (A.obj y) _ (A.homMap x y)).comp _ _ = _ at he
  erw [A.homMap_comparison x y, Cochain.zero_comp] at he
  exact he.symm
end SerrePositivity.KST.SConstruction
