module

public import SerrePositivity.KST.Comparison.HomologyHomotopy
public import Mathlib.Algebra.Homology.QuasiIso

/-!
# 整数ホモロジー同型と鎖複体の擬同型

概要：整数ホモロジー同型を正規化・非正規化鎖複体の実際の擬同型と同定する。
方針：正規化包含の鎖ホモトピー同値と擬同型の二対三性を使う。
規約：Waldhausen LNM 1126 §1.7・§1.8 のセル濾過の計算。
使われ方：pushout と filtered colimit の鎖複体の完全性による比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory AlgebraicTopology

/--
概要：整数ホモロジー同型であることは正規化整数鎖写像の擬同型性と同値である。
方針：実際のホモロジー写像による擬同型の判定を各次数で使う。
規約：ホモロジーの定義と Mathlib の擬同型を結ぶ。
使われ方：複体の圏の定理を整数ホモロジーへ移す。
-/
theorem integralHomologyIsomorphism_iff_normalized_quasiIso {X Y : SSet.{u}} (f : X ⟶ Y) :
    IntegralHomologyIsomorphism f ↔ QuasiIso (normalizedIntegralChains.map f) := by
  rw [quasiIso_iff]
  exact forall_congr' (fun n => quasiIsoAt_iff_isIso_homologyMap _ n |>.symm)

/--
概要：正規化包含は擬同型である。
方針：実際の鎖ホモトピー同値の順方向の写像として判定する。
規約：全ての単体集合。
使われ方：正規化と非正規化の擬同型性の比較。
-/
instance normalizationInclusion_quasiIso (X : SSet.{u}) :
    QuasiIso (normalizationInclusion.app X) :=
  (normalizationHomotopyEquiv X).quasiIso_hom

/--
概要：整数ホモロジー同型であることは非正規化整数鎖写像の擬同型性とも同値である。
方針：正規化包含の自然性と、包含の擬同型性による二対三性を使う。
規約：自由鎖複体の余極限保存を利用できる模型へ移す。
使われ方：horn 添付と順序余極限。
-/
theorem integralHomologyIsomorphism_iff_unnormalized_quasiIso {X Y : SSet.{u}} (f : X ⟶ Y) :
    IntegralHomologyIsomorphism f ↔ QuasiIso (unnormalizedIntegralChains.map f) := by
  rw [integralHomologyIsomorphism_iff_normalized_quasiIso,
    ← quasiIso_iff_comp_right (normalizedIntegralChains.map f)
      (normalizationInclusion.app Y), normalizationInclusion.naturality f,
    quasiIso_iff_comp_left]

end SerrePositivity.KST.Comparison
