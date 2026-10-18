module

public import SerrePositivity.KST.DerivedGeometry.AffineZeroQuasicoherent
public import SerrePositivity.KST.DerivedGeometry.PlusTriangleHomology
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT

/-!
概要：アフィン係数層の準連接コホモロジー条件は標準の上下切断で保たれる。
方針：切断三角のコホモロジー比較と、残りの次数の零性を用いる。
規約：Dqc は元の全層導来圏の充満部分圏。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 のアフィン本質的全射性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory AlgebraicGeometry
namespace SerrePositivity.KST.DerivedGeometry
variable {R : CommRingCat.{u}} (H : Type u) [Ring H] [Algebra R H]
  [HasDerivedCategory (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).Modules]

/--
概要：アフィン係数層の上側切断は準連接コホモロジーを持つ。
方針：切断の境界以下のコホモロジーを元のものと同型にし、上では零性を用いる。
規約：下に有界な元の全層導来対象。
使われ方：TT §3、Toën §3.2 の本質的全射性の有限区間への帰着。
-/
lemma affineDqcPlus_truncLE
    (K : DerivedCategory.Plus (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).Modules)
    (hK : (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).hasQuasicoherentCohomology K.obj)
    (a : ℤ) :
    (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).hasQuasicoherentCohomology
      ((DerivedCategory.Plus.TStructure.t.truncLE a).obj K).obj := by
  let B := tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom
  let t := DerivedCategory.Plus.TStructure.t (C := B.Modules)
  let T := (t.triangleLEGT a).obj K
  have : T.obj₁.IsLE a := by
    change t.IsLE ((t.truncLE a).obj K) a
    infer_instance
  have : T.obj₃.IsGE (a + 1) := by
    change t.IsGE ((t.truncGT a).obj K) (a + 1)
    infer_instance
  intro n
  by_cases hn : n ≤ a
  · have : T.obj₃.IsGE (n + 1) :=
      t.isGE_of_ge T.obj₃ (n + 1) (a + 1) (by omega)
    have hi := plusTriangle_homology_mor₁_isIso T (t.triangleLEGT_distinguished a K) n
    exact (SheafOfModules.isQuasicoherent (Scheme.Spec.obj (.op R)).ringCatSheaf).prop_of_iso
      (B.forget.mapIso (asIso ((DerivedCategory.Plus.homologyFunctor B.Modules n).map T.mor₁))).symm
      (hK n)
  · exact affineCoefficient_isQuasicoherent_of_isZero H _
      (DerivedCategory.Plus.isZero_homology_of_isLE T.obj₁ a n (by omega))

/--
概要：アフィン係数層の下側切断は準連接コホモロジーを持つ。
方針：境界より上のコホモロジーを元のものと同型にし、下では零性を用いる。
規約：下に有界な元の全層導来対象。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の有限振幅の帰納。
-/
lemma affineDqcPlus_truncGT
    (K : DerivedCategory.Plus (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).Modules)
    (hK : (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).hasQuasicoherentCohomology K.obj)
    (a : ℤ) :
    (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).hasQuasicoherentCohomology
      ((DerivedCategory.Plus.TStructure.t.truncGT a).obj K).obj := by
  let B := tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom
  let t := DerivedCategory.Plus.TStructure.t (C := B.Modules)
  let T := (t.triangleLEGT a).obj K
  have : T.obj₁.IsLE a := by
    change t.IsLE ((t.truncLE a).obj K) a
    infer_instance
  have : T.obj₃.IsGE (a + 1) := by
    change t.IsGE ((t.truncGT a).obj K) (a + 1)
    infer_instance
  intro n
  by_cases hn : a < n
  · have : T.obj₁.IsLE (n - 1) := t.isLE_of_le T.obj₁ a (n - 1) (by omega)
    have hi := plusTriangle_homology_mor₂_isIso T (t.triangleLEGT_distinguished a K) n
    exact (SheafOfModules.isQuasicoherent (Scheme.Spec.obj (.op R)).ringCatSheaf).prop_of_iso
      (B.forget.mapIso (asIso ((DerivedCategory.Plus.homologyFunctor B.Modules n).map T.mor₂)))
      (hK n)
  · exact affineCoefficient_isQuasicoherent_of_isZero H _
      (DerivedCategory.Plus.isZero_homology_of_isGE T.obj₃ (a + 1) n (by omega))

end SerrePositivity.KST.DerivedGeometry
