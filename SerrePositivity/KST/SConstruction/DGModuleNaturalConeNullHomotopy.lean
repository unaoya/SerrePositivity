module
public import SerrePositivity.KST.SConstruction.DGModuleNaturalConeBoundary
public import SerrePositivity.DifferentialGraded.Complexes.Cone

/-!
概要：元厳密比較と標準右包含の合成を零化する元左包含の全次数自然性を保持する。
方針：第三成分零の cone 作用の左制限と同じ微分境界式を使う。
規約：次数 −1 の符号付き自然性であり、閉零射の自然性へ弱めない。
使われ方：元 cone 四角形の指定零化二単体を全関手族として構成する。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory HomologicalComplex CochainComplex HomComplex
open DifferentialGraded InfinityCategories
private lemma coneCochainZeroInl {R : Type u} [CommRing R] {A B C E : Complex R}
    (f : A ⟶ B) (g : C ⟶ E) {n : ℤ} (a : Homogeneous A C n) (b : Homogeneous B E n) :
    (mappingCone.inl f).comp
      (dgGluingConeCochain f g a b (0 : Homogeneous A E (n - 1)) (by omega))
      (by omega : -1 + n = n - 1) =
    n.negOnePow • a.comp (mappingCone.inl g) (by omega : n + -1 = n - 1) := by
  rw [dgGluingConeCochain_zero_comparison]
  apply Cochain.ext
  intro i j hij
  obtain ⟨k, rfl⟩ : ∃ k : ℤ, i = k + 1 := ⟨i - 1, by omega⟩
  rw [Cochain.comp_v _ _ _ (k + 1) k j (by omega) (by omega),
    Cochain.units_smul_v, Cochain.comp_v _ _ _ (k + 1) (j + 1) j (by omega) (by omega)]
  exact coneMapCochain_inl_v _ _ _ _ k j (by omega)

variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

/-- 概要：第三成分零の実 cone 作用は左包含と同じ Koszul 符号で可換。
方針：実 Hom end の各評価で元 cone の左制限式を使う。
規約：全整数次数を保持。使われ方：指定零化の斉次自然性。 -/
lemma dgGluingModuleConeElement_zero_inl {M N P Q : ModuleCategory R D}
    (f : M ⟶ N) (g : P ⟶ Q) {n : ℤ} (a) (b) :
    compose R (x := ForgetEnrichment.to (Complex R) M)
        (y := ForgetEnrichment.to (Complex R) (moduleCone R D f))
        (z := ForgetEnrichment.to (Complex R) (moduleCone R D g))
        (dgGluingModuleConeElement R D f g a b
          (0 : (moduleHom R D (ForgetEnrichment.to (Complex R) M)
            (ForgetEnrichment.to (Complex R) Q)).X (n - 1)) (by omega))
        (moduleConeInlElement R D f) (by omega : -1 + n = n - 1) =
      n.negOnePow • compose R (x := ForgetEnrichment.to (Complex R) M)
        (y := ForgetEnrichment.to (Complex R) P)
        (z := ForgetEnrichment.to (Complex R) (moduleCone R D g))
        (moduleConeInlElement R D g) a (by omega : n + -1 = n - 1) := by
  apply moduleHomElement_ext R D
  intro x
  rw [moduleHomCompose_π, dgGluingModuleConeElement_π, moduleConeInlElement_π,
    Units.smul_def, map_zsmul, moduleHomCompose_π, moduleConeInlElement_π, map_zero]
  exact coneCochainZeroInl _ _ _ _

variable {P : Type w} [DGCategory R P]
  (F G : DGFunctor R P (RightModule R D)) (η : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G)
local notation "a" => dgModuleNaturalConeArrow R D F G η
local notation "T" => dgModuleNaturalConeFunctor R D F G η

/-- 概要：元比較と標準包含の合成を零化する同じ実左包含。
方針：元 cone の次数 −1 元を使用する。規約：零化を選び直さない。
使われ方：全関手族の指定零化成分。 -/
def dgModuleNaturalConeNullHomotopyElement (x : P) :
    (moduleHom R D (F.obj x) ((T).obj x)).X (-1) := moduleConeInlElement R D (a x)

/-- 概要：元左包含の微分は元比較と元右包含の合成。
方針：同じ実 cone の標準境界式を適用する。
規約：元実射を保持。使われ方：指定零化二単体の境界。 -/
lemma dgModuleNaturalConeNullHomotopyElement_d (x : P) :
    (moduleHom R D (F.obj x) ((T).obj x)).d (-1) 0
      (dgModuleNaturalConeNullHomotopyElement R D F G η x) =
    (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R)
      (a x ≫ moduleConeInr R D (a x)))).val := moduleConeInlElement_d R D (a x)

/-- 概要：同じ零化元は全 Hom に関して次数 −1 の符号付き自然性を満たす。
方針：第三成分零の元 cone 作用の左制限を使う。
規約：元全次数と Koszul 符号を保持。使われ方：指定二単体の全パラメーター化。 -/
lemma dgModuleNaturalConeNullHomotopyElement_naturality (x y : P) (n : ℤ)
    (z : GradedHom R x y n) :
    compose R (x := F.obj x) (y := (T).obj x) (z := (T).obj y)
      (((T).map x y).f n z) (dgModuleNaturalConeNullHomotopyElement R D F G η x)
      (by omega : -1 + n = n - 1) =
    n.negOnePow • compose R (x := F.obj x) (y := F.obj y) (z := (T).obj y)
      (dgModuleNaturalConeNullHomotopyElement R D F G η y) ((F.map x y).f n z)
      (by omega : n + -1 = n - 1) :=
  dgGluingModuleConeElement_zero_inl R D (a x) (a y) ((F.map x y).f n z) ((G.map x y).f n z)
end SerrePositivity.KST.SConstruction
