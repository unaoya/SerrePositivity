module
public import SerrePositivity.KST.SConstruction.DGHomGluingModuleConeHomMap
public import SerrePositivity.KST.SConstruction.DGHomGluingModuleConeIdentity
public import SerrePositivity.KST.SConstruction.DGHomGluingModuleConeCompositionDegree
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.FunctorMapping
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Algebra

/-!
概要：全次数で自然な加群比較の点ごとの元 cone を、一つの実 dg 関手へ束ねる。
方針：同じ比較閉射と左右の元 Hom 作用を、第三 cochain 零の実 cone 写像へ渡す。
規約：閉次数零だけの自然性で代用しない。使われ方：逆回転比較の全関手族化。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory HomologicalComplex CochainComplex HomComplex
open DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {P : Type w} [DGCategory R P] (F G : DGFunctor R P (RightModule R D)) (η : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G)

/-- 概要：同じ厳密比較の元閉零成分。
方針：元閉元・閉射対応の逆を使う。規約：成分を選び直さない。
使われ方：元点ごとの実 cone の指定射。 -/
def dgModuleNaturalConeArrow (x : P) :
    ForgetEnrichment.of (Complex R) (F.obj x) ⟶ ForgetEnrichment.of (Complex R) (G.obj x) :=
  (closedHomEquiv R (RightModule R D) (F.obj x) (G.obj x)).symm (η.app x)

/-- 概要：同じ閉射を閉元へ戻すと元比較成分そのもの。
方針：元の同じ閉射・閉元対応を使用する。
規約：全次数自然性の元成分を保持。使われ方：cone Hom 微分式。 -/
lemma dgModuleNaturalConeArrow_cycle (x : P) :
    (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R)
      (dgModuleNaturalConeArrow R D F G η x))).val = (η.app x).val :=
  congrArg Subtype.val ((closedHomEquiv R (RightModule R D) (F.obj x) (G.obj x)).apply_symm_apply
    (η.app x))

local notation "a" => dgModuleNaturalConeArrow R D F G η

/-- 元全自然性は第三 cochain 零の cone 微分境界式を満たす。 -/
lemma dgModuleNaturalConeZeroBoundary (x y : P) (n : ℤ) (z : (homObject R P x y).X n) :
    (0 : Cochain (homObject R P x y)
      (moduleHom R D (F.obj x) (G.obj y)) (-1)).v (n + 1) n (by omega)
      ((homObject R P x y).d n (n + 1) z) =
    compose R (x := F.obj x) (y := F.obj y) (z := G.obj y)
        (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) (a y))).val
        ((F.map x y).f n z) (add_zero n) -
      compose R (x := F.obj x) (y := G.obj x) (z := G.obj y) ((G.map x y).f n z)
        (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) (a x))).val (zero_add n) -
      (moduleHom R D (F.obj x) (G.obj y)).d (n - 1) n
        ((0 : Cochain (homObject R P x y)
          (moduleHom R D (F.obj x) (G.obj y)) (-1)).v n (n - 1) (by omega) z) := by
  simp only [Cochain.zero_v, ModuleCat.hom_zero, LinearMap.zero_apply, map_zero, sub_zero,
    dgModuleNaturalConeArrow_cycle]
  exact (sub_eq_zero.mpr (η.naturality z)).symm

/-- 概要：同じ点ごとの実 cone の全 Hom 鎖写像。
方針：元二関手の Hom と元全自然性を、第三成分零の cone 構成子へ渡す。
規約：全整数次数を保持。使われ方：実 cone 関手の全 Hom 作用。 -/
def dgModuleNaturalConeHomMap (x y : P) : homObject R P x y ⟶
    moduleHom R D (ForgetEnrichment.to (Complex R) (moduleCone R D (a x)))
      (ForgetEnrichment.to (Complex R) (moduleCone R D (a y))) :=
  dgGluingModuleConeHomMap R D (a x) (a y) (F.map x y) (G.map x y) 0
    (dgModuleNaturalConeZeroBoundary R D F G η x y)

/-- 概要：同じ全 Hom 作用の斉次成分は元二作用と第三成分零。
方針：元構成子を回収する。規約：元の実 cone を保持。
使われ方：単位・合成と全比較の計算。 -/
lemma dgModuleNaturalConeHomMap_apply (x y : P) (n : ℤ) (z : (homObject R P x y).X n) :
    (dgModuleNaturalConeHomMap R D F G η x y).f n z =
      dgGluingModuleConeElement R D (a x) (a y) ((F.map x y).f n z) ((G.map x y).f n z)
        (0 : (moduleHom R D (F.obj x) (G.obj y)).X (n - 1)) (by omega) := rfl

/-- 概要：同じ cone Hom 作用は元単位を保つ。
方針：元二関手の単位保存と元 cone の単位公式を使う。
規約：同じ全 Hom 写像。使われ方：実 dg 関手の構成。 -/
lemma dgModuleNaturalConeHomMap_unit (x : P) :
    (dgModuleNaturalConeHomMap R D F G η x x).f 0 (unitElement R x).val =
      (unitElement R (ForgetEnrichment.to (Complex R) (moduleCone R D (a x)))).val := by
  rw [dgModuleNaturalConeHomMap_apply, DGFunctor.map_unitElement, DGFunctor.map_unitElement]
  exact dgGluingModuleConeElement_identity R D (a x)

private lemma naturalConeMapUnits {U V : ModuleCat R} (f : U ⟶ V) (r : ℤˣ) (z : U) :
    f (r • z) = r • f z := map_zsmul f.hom (r : ℤ) z

/-- 概要：同じ cone Hom 作用は通常順合成を全整数次数で保つ。
方針：第三成分零の実 cone 合成式と元二関手の合成保存を使う。
規約：閉零次数に制限しない。使われ方：全関手族としての実 cone。 -/
lemma dgModuleNaturalConeHomMap_comp (x y z : P) {r s : ℤ}
    (f : GradedHom R x y r) (g : GradedHom R y z s) :
    (dgModuleNaturalConeHomMap R D F G η x z).f (r + s) (compose R g f rfl) =
      compose R (x := ForgetEnrichment.to (Complex R) (moduleCone R D (a x)))
        (y := ForgetEnrichment.to (Complex R) (moduleCone R D (a y)))
        (z := ForgetEnrichment.to (Complex R) (moduleCone R D (a z)))
        ((dgModuleNaturalConeHomMap R D F G η y z).f s g)
        ((dgModuleNaturalConeHomMap R D F G η x y).f r f) rfl := by
  rw [dgModuleNaturalConeHomMap_apply, dgModuleNaturalConeHomMap_apply,
    dgModuleNaturalConeHomMap_apply]
  rw [dgGluingModuleConeElement_comp_at R D (a x) (a y) (a z)
    (o := r + s - 1) _ _ _ (by omega) _ _ _ (by omega) (by omega)]
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.map_compose, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.zero_compose, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_zero,
    smul_zero, add_zero]

/-- 概要：同じ cone Hom 作用は豊穣順合成も保つ。
方針：通常順合成の保存と同じ Koszul 符号の線形性を使う。
規約：全整数次数を保持。使われ方：実 dg 関手の構成子。 -/
lemma dgModuleNaturalConeHomMap_forward (x y z : P) (r s n : ℤ) (hn : r + s = n)
    (f : GradedHom R x y r) (g : GradedHom R y z s) :
    (dgModuleNaturalConeHomMap R D F G η x z).f n (forward R f g hn) =
      forward R (x := ForgetEnrichment.to (Complex R) (moduleCone R D (a x)))
        (y := ForgetEnrichment.to (Complex R) (moduleCone R D (a y)))
        (z := ForgetEnrichment.to (Complex R) (moduleCone R D (a z)))
        ((dgModuleNaturalConeHomMap R D F G η x y).f r f)
        ((dgModuleNaturalConeHomMap R D F G η y z).f s g) hn := by
  cases hn
  rw [forward_eq_signed_compose, forward_eq_signed_compose]
  erw [naturalConeMapUnits, dgModuleNaturalConeHomMap_comp]

/-- 概要：元の厳密自然比較の点ごとの実 cone を束ねた dg 関手。
方針：元二関手の全 Hom と第三成分零の作用・単位・合成保存を束ねる。
規約：点ごとの同値だけで全自然性を代用しない。
使われ方：実逆回転 cone 比較の全関手族化。 -/
def dgModuleNaturalConeFunctor : DGFunctor R P (RightModule R D) :=
  DGFunctor.ofHomMaps R (fun x => ForgetEnrichment.to (Complex R) (moduleCone R D (a x)))
    (dgModuleNaturalConeHomMap R D F G η) (dgModuleNaturalConeHomMap_unit R D F G η)
    (dgModuleNaturalConeHomMap_forward R D F G η)

end SerrePositivity.KST.SConstruction
