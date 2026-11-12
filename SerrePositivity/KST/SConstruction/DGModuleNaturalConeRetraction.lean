module
public import SerrePositivity.KST.SConstruction.DGModuleNaturalConeNullHomotopy

/-!
概要：元厳密比較の実 cone の右射影を全次数自然な斉次元として保持する。
方針：第三成分零の cone 作用の右制限を元実 Hom end へ移す。
規約：右射影は閉射とは限らず、厳密自然変換とは呼ばない。
使われ方：実逆回転 cone 比較の同じ右成分の全自然性。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory HomologicalComplex CochainComplex HomComplex
open DifferentialGraded InfinityCategories
private lemma coneCochainZeroSnd {R : Type u} [CommRing R] {A B C E : Complex R}
    (f : A ⟶ B) (g : C ⟶ E) {n : ℤ}
    (a : Homogeneous A C n) (b : Homogeneous B E n) :
    (dgGluingConeCochain f g a b (0 : Homogeneous A E (n - 1)) (by omega)).comp
      (mappingCone.snd g) (add_zero n) =
      (mappingCone.snd f).comp b (zero_add n) := by
  rw [dgGluingConeCochain_snd, Cochain.comp_zero, smul_zero, sub_zero]

variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

/-- 概要：第三成分零の元 cone 作用は右射影と全次数で可換する。
方針：元実 Hom end の各評価で同じ snd の回収式を使う。
規約：右射影の閉性を仮定しない。使われ方：逆回転比較の右成分。 -/
lemma dgGluingModuleConeElement_zero_snd {M N P Q : ModuleCategory R D}
    (f : M ⟶ N) (g : P ⟶ Q) {n : ℤ} (a) (b) :
    compose R (x := ForgetEnrichment.to (Complex R) (moduleCone R D f))
        (y := ForgetEnrichment.to (Complex R) (moduleCone R D g))
        (z := ForgetEnrichment.to (Complex R) Q)
        (moduleConeSndElement R D g)
        (dgGluingModuleConeElement R D f g a b
          (0 : (moduleHom R D (ForgetEnrichment.to (Complex R) M)
            (ForgetEnrichment.to (Complex R) Q)).X (n - 1)) (by omega)) (add_zero n) =
      compose R (x := ForgetEnrichment.to (Complex R) (moduleCone R D f))
        (y := ForgetEnrichment.to (Complex R) N)
        (z := ForgetEnrichment.to (Complex R) Q)
        b (moduleConeSndElement R D f) (zero_add n) := by
  apply moduleHomElement_ext R D
  intro x
  rw [moduleHomCompose_π, moduleConeSndElement_π, dgGluingModuleConeElement_π,
    moduleHomCompose_π, moduleConeSndElement_π, map_zero]
  exact coneCochainZeroSnd _ _ _ _

variable {P : Type w} [DGCategory R P]
  (F G : DGFunctor R P (RightModule R D)) (η : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G)
local notation "a" => dgModuleNaturalConeArrow R D F G η
local notation "T" => dgModuleNaturalConeFunctor R D F G η

/-- 概要：元実 cone の同じ右射影の斉次成分。
方針：元 cone の次数零元をそのまま使う。
規約：閉性を主張しない。使われ方：同じ逆回転 cone 比較の構成成分。 -/
def dgModuleNaturalConeRetractionElement (x : P) :
    (moduleHom R D ((T).obj x) (G.obj x)).X 0 := moduleConeSndElement R D (a x)

/-- 概要：同じ右射影は元厳密比較族の全 Hom について次数零で自然。
方針：第三成分零の元 cone の右射影式を特殊化する。
規約：閉零射だけの自然性へ弱めない。使われ方：実合成比較の全次数自然性。 -/
lemma dgModuleNaturalConeRetractionElement_naturality (x y : P) (n : ℤ)
    (z : GradedHom R x y n) :
    compose R (x := (T).obj x) (y := (T).obj y) (z := G.obj y)
      (dgModuleNaturalConeRetractionElement R D F G η y) (((T).map x y).f n z)
      (add_zero n) =
    compose R (x := (T).obj x) (y := G.obj x) (z := G.obj y)
      ((G.map x y).f n z) (dgModuleNaturalConeRetractionElement R D F G η x)
      (zero_add n) :=
  dgGluingModuleConeElement_zero_snd R D (a x) (a y) ((F.map x y).f n z) ((G.map x y).f n z)
end SerrePositivity.KST.SConstruction
