module
public import SerrePositivity.KST.SConstruction.DGIdentityHomGluingAxes

/-!
概要：元厳密比較の恒等 gluing cone の二軸を同じ Yoneda 族へ回収する。
方針：全 Hom 射影の回収を同じ Yoneda で後合成する。
規約：元左右関手の全 Hom 鎖写像を保持する。
使われ方：同じ実 cone 入力同型の全自然性。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
private lemma postIdentity {V : Type*} [Category V] {X Y Z W : V}
    (a : X ⟶ Y) (b : Y ⟶ Z) (c : X ⟶ Z) (d : Z ⟶ W) (h : a ≫ b = c) :
    a ≫ (b ≫ 𝟙 Z ≫ d) = c ≫ d := by
  simpa only [Category.id_comp, ← Category.assoc] using congrArg (fun t => t ≫ d) h
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

/-- 概要：元実 cone 左成分は元左関手の同じ Yoneda Hom 作用。
方針：元左射影の全 Hom 回収を Yoneda で後合成する。
規約：全次数鎖写像。使われ方：同じ元 cone 入力全比較の左成分。 -/
lemma dgIdentityHomGluingFunctor_coneLeftMap (x y : P) :
    (H).map x y ≫ dgHomGluingConeLeftMap R C C C (I) (I) ((H).obj x) ((H).obj y) =
      (F.comp (dgYoneda R C)).map x y :=
  postIdentity _ _ _ _ (dgIdentityHomGluingFunctor_left_map R C F G a h x y)

/-- 概要：元実 cone 右成分は元右関手の同じ Yoneda Hom 作用。
方針：元右射影の全 Hom 回収を Yoneda で後合成する。
規約：全次数鎖写像。使われ方：同じ元 cone 入力全比較の右成分。 -/
lemma dgIdentityHomGluingFunctor_coneRightMap (x y : P) :
    (H).map x y ≫ dgHomGluingConeRightMap R C C C (I) (I) ((H).obj x) ((H).obj y) =
      (G.comp (dgYoneda R C)).map x y :=
  postIdentity _ _ _ _ (dgIdentityHomGluingFunctor_right_map R C F G a h x y)
end SerrePositivity.KST.SConstruction
