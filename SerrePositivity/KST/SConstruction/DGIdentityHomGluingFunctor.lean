module
public import SerrePositivity.KST.SConstruction.DGHomGluingFunctor

/-!
概要：同じ小 dg 基底内の全 Hom 自然な閉比較を恒等 Hom gluing の厳密関手にする。
方針：既存の Hom gluing 関手を恒等二脚へ特殊化し、恒等後合成だけを正規化する。
規約：元二関手と元閉比較を保持。使われ方：LT 逆回転の二実像小模型。
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

/-- 概要：同じ実比較を保つ恒等 Hom gluing への厳密 dg 関手。
方針：恒等後合成の単位則を元 Hom gluing 関手へ渡す。
規約：元の全 Hom を保持。使われ方：逆回転の共通小基底への関手化。 -/
def dgIdentityHomGluingFunctor : DGFunctor R P
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C C (dgHomGluingBimodule R C C C (DGFunctor.id C) (DGFunctor.id C))) :=
  dgHomGluingFunctor R C C C (DGFunctor.id C) (DGFunctor.id C) F G a (by
    intro x y
    change (F.map x y ≫ 𝟙 _) ≫
        eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) (F.obj x)) (a y) =
      (G.map x y ≫ 𝟙 _) ≫ eHomWhiskerRight (Complex R) (a x)
        (ForgetEnrichment.of (Complex R) (G.obj y))
    exact (congrArg (fun k => k ≫ eHomWhiskerLeft (Complex R)
        (ForgetEnrichment.of (Complex R) (F.obj x)) (a y)) (Category.comp_id _)).trans
      ((h x y).trans (congrArg (fun k => k ≫ eHomWhiskerRight (Complex R) (a x)
        (ForgetEnrichment.of (Complex R) (G.obj y))) (Category.comp_id _)).symm))
/-- 概要：同じ恒等 Hom gluing 関手の対象は元の指定比較対象。
方針：同じ元対象の構成を回収する。規約：閉比較を保持。
使われ方：元の比較射と全対象作用の照合。 -/
lemma dgIdentityHomGluingFunctor_obj (x : P) :
    (dgIdentityHomGluingFunctor R C F G a h).obj x =
      dgHomGluingComparisonObject R C C C (DGFunctor.id C) (DGFunctor.id C) F G a x := rfl

/-- 概要：同じ関手の左射影は元左関手そのもの。
方針：元 Hom gluing 関手の厳密回収式を使う。
規約：全 dg 関手の等号。使われ方：元逆回転の左成分。 -/
lemma dgIdentityHomGluingFunctor_left :
    (dgIdentityHomGluingFunctor R C F G a h).comp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeft R C C (dgHomGluingBimodule R C C C (DGFunctor.id C) (DGFunctor.id C))) = F := by
  unfold dgIdentityHomGluingFunctor
  apply dgHomGluingFunctor_left

/-- 概要：同じ関手の右射影は元右関手そのもの。
方針：元 Hom gluing 関手の厳密回収式を使う。
規約：全 dg 関手の等号。使われ方：元逆回転の右成分。 -/
lemma dgIdentityHomGluingFunctor_right :
    (dgIdentityHomGluingFunctor R C F G a h).comp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRight R C C (dgHomGluingBimodule R C C C (DGFunctor.id C) (DGFunctor.id C))) = G := by
  unfold dgIdentityHomGluingFunctor
  apply dgHomGluingFunctor_right
end SerrePositivity.KST.SConstruction
