module

public import SerrePositivity.KST.DerivedBlowup.ExteriorProductCochainDifferential
public import SerrePositivity.KST.DerivedBlowup.ChartComplexes
public import Mathlib.Algebra.Category.ModuleCat.Biproducts

/-!
概要：KST Def3.1 の生成元追加後の Koszul 外積複体と cone の項を同定する。
方針：整数次数の二成分分解と既存 homotopyCofiber の biprod 表示を合成する。
規約：cone の第一成分は q+1 次、第二成分は q 次。
使われ方：反復 cone 比較の複体同型の成分。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory CategoryTheory.Limits HomologicalComplex homotopyCofiber

variable {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]

/-- 概要：元の Koszul 複体の a 倍写像の cone。
方針：既存 mappingCone を使う。
規約：KST Def3.1、最後の関係式を外側の cone に取る。使われ方：帰納段階の比較対象。 -/
abbrev exteriorScalarCone (d : M →ₗ[R] R) (a : R) :=
  CochainComplex.mappingCone (smulId a (exteriorKoszulCochain d))

/-- 概要：cone の項を二成分の直積加群と同定する。
方針：homotopyCofiber の標準 biprod 同型と ModuleCat の直積同型を使う。
規約：KST Def3.1。使われ方：外積二成分分解との比較。 -/
def exteriorScalarConePairIso (d : M →ₗ[R] R) (a : R) (q : ℤ) :
    (exteriorScalarCone d a).X q ≅ ModuleCat.of R
      ((exteriorKoszulCochain d).X (q + 1) × (exteriorKoszulCochain d).X q) :=
  XIsoBiprod (smulId a (exteriorKoszulCochain d)) q (q + 1) rfl ≪≫
    ModuleCat.biprodIsoProd _ _

/-- 概要：生成元追加後の外積複体から cone への項ごとの同型。
方針：外積分解を cone の二成分表示の逆へ合成する。
規約：KST Def3.1。使われ方：複体同型の component。 -/
def exteriorToConeXIso (d : M →ₗ[R] R) (a : R) (q : ℤ) :
    (exteriorKoszulCochain (exteriorProductDifferential d a)).X q ≅
      (exteriorScalarCone d a).X q :=
  (exteriorProductCochainEquiv d a q).toModuleIso ≪≫ (exteriorScalarConePairIso d a q).symm

/-- 概要：cone 比較の第一射影は二成分分解の第一成分。
方針：biprod と直積の比較公式を使う。
規約：KST Def3.1。使われ方：shifted 成分の chain 条件。 -/
@[reassoc] theorem exteriorToConeXIso_fst (d : M →ₗ[R] R) (a : R) (q : ℤ) :
    (exteriorToConeXIso d a q).hom ≫
        fstX (smulId a (exteriorKoszulCochain d)) q (q + 1) rfl =
      ModuleCat.ofHom
        ((LinearMap.fst R _ _).comp (exteriorProductCochainEquiv d a q).toLinearMap) := by
  simp [exteriorToConeXIso, exteriorScalarConePairIso, fstX, Category.assoc]

/-- 概要：cone 比較の第二射影は二成分分解の第二成分。
方針：biprod と直積の比較公式を使う。
規約：KST Def3.1。使われ方：非 shifted 成分の chain 条件。 -/
@[reassoc] theorem exteriorToConeXIso_snd (d : M →ₗ[R] R) (a : R) (q : ℤ) :
    (exteriorToConeXIso d a q).hom ≫ sndX (smulId a (exteriorKoszulCochain d)) q =
      ModuleCat.ofHom
        ((LinearMap.snd R _ _).comp (exteriorProductCochainEquiv d a q).toLinearMap) := by
  have hs (j : ℤ) (hj : (ComplexShape.up ℤ).Rel q j) :
      sndX (smulId a (exteriorKoszulCochain d)) q =
        (XIsoBiprod (smulId a (exteriorKoszulCochain d)) q j hj).hom ≫ biprod.snd := by
    obtain rfl := (ComplexShape.up ℤ).next_eq' hj
    exact dite_eq_left hj
  rw [hs (q + 1) rfl]
  simp [exteriorToConeXIso, exteriorScalarConePairIso, Category.assoc]

end SerrePositivity.KST.DerivedBlowup
