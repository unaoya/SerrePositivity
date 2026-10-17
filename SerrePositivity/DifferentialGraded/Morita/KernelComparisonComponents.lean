module
public import SerrePositivity.DifferentialGraded.Morita.KernelComparisonNaturality

/-! # 通常kernel代表上の主作用比較の成分

## 概要
指定した標準局所化の通常代表では、主作用と既存作用の比較成分を恒等射として計算する。

## 方針
元の比較を定義するeqToIsoの成分を計算し、通常kernel射での作用も同じ計算へ接続する。

## 規約と注意
比較の定義は変えない。局所Hom K-flat性やkernelの射影性は不要。

## 使われ方
U16aの計算モデルのcoherenceを公開比較へ移す際の同じ代表上の簡約。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]

/-- 通常代表上の公開比較同型は同じ作用の恒等比較。 -/
lemma kernelDerivedTensorOnBimoduleIso_refl (P : BimoduleCategory A E D) :
    kernelDerivedTensorOnBimoduleIso A D E P =
      Iso.refl (kernelDerivedTensorOnBimodule A D E (BimoduleCategory.underlying A E D P)) := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  simp only [kernelDerivedTensorOnBimoduleIso, Iso.app_hom, eqToIso.hom, eqToHom_app,
    Iso.refl_hom, NatTrans.id_app]
  rfl

/-- 通常kernel射の主作用は元の入力解像度作用の射そのもの。 -/
lemma kernelDerivedTensorFunctor_map_base {P P' : BimoduleCategory A E D} (f : P ⟶ P') :
    (kernelDerivedTensorFunctor A D E).map ((bimoduleToDerived A E D).map f) =
      kernelResolutionDerivedTensorMap A D E (moduleCanonicalProjectiveResolution A D) f := by
  have h := kernelDerivedTensorOnBimoduleIso_naturality A D E f
  rw [kernelDerivedTensorOnBimoduleIso_refl, kernelDerivedTensorOnBimoduleIso_refl] at h
  simp only [Iso.refl_hom] at h
  erw [Category.comp_id, Category.id_comp] at h
  exact h

end SerrePositivity.DifferentialGraded.Morita
