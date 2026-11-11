module
public import SerrePositivity.KST.SConstruction.DGStrictGluingComparisonZero
public import SerrePositivity.KST.SConstruction.DGIdentityHomGluingFunctor
public import SerrePositivity.KST.SConstruction.DGHomGluingConeHomMap

/-!
概要：元の厳密比較から恒等 Hom gluing へ入る同じ関手の第三成分を零と照合する。
方針：元 strict gluing の零比較を特殊化し、同じ Yoneda で後合成する。
規約：元全 Hom 上の cochain 等号を保つ。使われ方：中央射始域上の比較自然性。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory HomologicalComplex CochainComplex HomComplex
open DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  {P : Type w} [DGCategory R P] (F G : DGFunctor R P C)
  (a : ∀ x, ForgetEnrichment.of (Complex R) (F.obj x) ⟶
    ForgetEnrichment.of (Complex R) (G.obj x))
  (h : ∀ x y, F.map x y ≫
    eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) (F.obj x)) (a y) =
    G.map x y ≫ eHomWhiskerRight (Complex R) (a x)
      (ForgetEnrichment.of (Complex R) (G.obj y)))
local notation "H" => dgIdentityHomGluingFunctor R C F G a h
local notation "I" => DGFunctor.id C
local notation "M" => dgHomGluingBimodule R C C C (I) (I)

/-- 概要：元比較の恒等 Hom gluing 表示は第三比較零を全 Hom 上で保つ。
方針：同じ厳密 gluing の一般結果へ特殊化する。
規約：元関手を変更しない。使われ方：元比較族上の零第三成分の証拠。 -/
lemma dgIdentityHomGluingFunctor_comparison_zero (x y : P) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComparison R C C (M) ((H).obj x) ((H).obj y)
      (homObject R P x y) ((H).map x y) = 0 := by
  unfold dgIdentityHomGluingFunctor dgHomGluingFunctor
  exact dgStrictGluingFunctor_comparison_zero R C C (M) F G _ _ x y

/-- 概要：同じ実 cone 作用の第三 cochain は元始域への制限で零になる。
方針：元第三比較の零等号を同じ Yoneda で後合成する。
規約：点ごとの零性に落とさない。使われ方：全 cone 作用の対角表示との照合。 -/
lemma dgIdentityHomGluingFunctor_conePrimitive_zero (x y : P) :
    (Cochain.ofHom ((H).map x y)).comp
      (dgHomGluingConePrimitive R C C C (I) (I) ((H).obj x) ((H).obj y))
      (zero_add (-1)) = 0 := by
  change (Cochain.ofHom ((H).map x y)).comp
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomPrimitive R C C (M) ((H).obj x) ((H).obj y)).comp
      (Cochain.ofHom ((dgYoneda R C).map _ _)) (add_zero (-1))) (zero_add (-1)) = 0
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain]
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComparison R C C (M) ((H).obj x) ((H).obj y)
    (homObject R P x y) ((H).map x y)).comp _ _ = 0
  rw [dgIdentityHomGluingFunctor_comparison_zero, Cochain.zero_comp]
/-- 概要：元厳密比較の像の各斉次射においても第三 cone 成分は零。
方針：同じ全 cochain 零等号を元の斉次射で評価する。
規約：全整数次数。使われ方：元実 cone Hom 作用の第三成分除去。 -/
lemma dgIdentityHomGluingFunctor_conePrimitive_apply_zero (x y : P) (n : ℤ)
    (z : (homObject R P x y).X n) :
    (dgHomGluingConePrimitive R C C C (I) (I) ((H).obj x) ((H).obj y)).v
      n (n - 1) (by omega) (((H).map x y).f n z) = 0 := by
  have he := congrArg (fun c => c.v n (n - 1) (by omega) z)
    (dgIdentityHomGluingFunctor_conePrimitive_zero R C F G a h x y)
  simpa only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, ModuleCat.comp_apply, Cochain.zero_v,
    ModuleCat.hom_zero, LinearMap.zero_apply] using he

/-- 概要：元始域上の同じ実 cone 作用は元左右成分と第三成分零で表される。
方針：全 cochain 零等号を元 Hom 作用の回収式に代入する。
規約：元の全 Hom 写像を変更しない。使われ方：指定比較成分の全自然性の計算。 -/
lemma dgIdentityHomGluingFunctor_coneHomMap_apply (x y : P) (n : ℤ)
    (z : (homObject R P x y).X n) :
    (dgHomGluingConeHomMap R C C C (I) (I) ((H).obj x) ((H).obj y)).f n
      (((H).map x y).f n z) =
    dgGluingModuleConeElement R C
      (dgHomGluingTargetModuleMap R C C C (I) (I) ((H).obj x))
      (dgHomGluingTargetModuleMap R C C C (I) (I) ((H).obj y))
      ((dgHomGluingConeLeftMap R C C C (I) (I) ((H).obj x) ((H).obj y)).f n
        (((H).map x y).f n z))
      ((dgHomGluingConeRightMap R C C C (I) (I) ((H).obj x) ((H).obj y)).f n
        (((H).map x y).f n z))
      (0 : (moduleHom R C (representable R (F.obj x))
        (representable R (G.obj y))).X (n - 1)) (by omega) := by
  rw [dgHomGluingConeHomMap_apply, dgIdentityHomGluingFunctor_conePrimitive_apply_zero]
  rfl

end SerrePositivity.KST.SConstruction
