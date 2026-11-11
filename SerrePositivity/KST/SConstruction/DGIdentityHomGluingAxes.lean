module
public import SerrePositivity.KST.SConstruction.DGIdentityHomGluingStrictCone

/-!
概要：元厳密比較の恒等 Hom gluing 表示で同じ二軸の全 Hom 作用を回収する。
方針：元左右射影の全関手等号を Hom 射へ評価する。
規約：元始域への制限と全 Hom 鎖写像を保持する。
使われ方：元 gluing cone 族と全自然な module cone 族の入力比較。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  {P : Type w} [DGCategory R P] (F G : DGFunctor R P C)
  (a : ∀ x, ForgetEnrichment.of (Complex R) (F.obj x) ⟶
    ForgetEnrichment.of (Complex R) (G.obj x))
  (h : ∀ x y, F.map x y ≫
      eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) (F.obj x)) (a y) =
      G.map x y ≫ eHomWhiskerRight (Complex R) (a x)
        (ForgetEnrichment.of (Complex R) (G.obj y)))
local notation "I" => DGFunctor.id C
local notation "M" => dgHomGluingBimodule R C C C (I) (I)
local notation "H" => dgIdentityHomGluingFunctor R C F G a h

/-- 概要：元恒等 Hom gluing 関手の左軸の全 Hom 作用は元左関手。
方針：元左射影の厳密関手等号を評価する。
規約：全次数鎖写像の等号。使われ方：同じ実 cone 左成分の照合。 -/
lemma dgIdentityHomGluingFunctor_left_map (x y : P) :
    (H).map x y ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftHomMap R C C (M) ((H).obj x) ((H).obj y) = F.map x y := by
  have he : HEq (((H).comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeft R C C (M))).map x y) (F.map x y) := by
    have hp := dgIdentityHomGluingFunctor_left R C F G a h
    generalize (H).comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeft R C C (M)) = K at hp ⊢
    cases hp
    rfl
  exact eq_of_heq he

/-- 概要：元恒等 Hom gluing 関手の右軸の全 Hom 作用は元右関手。
方針：元右射影の厳密関手等号と元 Hom 射影の回収を使う。
規約：全次数鎖写像の等号。使われ方：同じ実 cone 右成分の照合。 -/
lemma dgIdentityHomGluingFunctor_right_map (x y : P) :
    (H).map x y ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightHomMap R C C (M) ((H).obj x) ((H).obj y) = G.map x y := by
  have he : HEq (((H).comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRight R C C (M))).map x y) (G.map x y) := by
    have hp := dgIdentityHomGluingFunctor_right R C F G a h
    generalize (H).comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRight R C C (M)) = K at hp ⊢
    cases hp
    rfl
  exact (congrArg (fun t => (H).map x y ≫ t)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRight_map R C C (M) ((H).obj x) ((H).obj y)).symm).trans (eq_of_heq he)
end SerrePositivity.KST.SConstruction
