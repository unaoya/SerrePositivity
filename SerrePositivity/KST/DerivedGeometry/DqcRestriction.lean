module

public import SerrePositivity.KST.DerivedGeometry.DerivedRestriction
public import SerrePositivity.KST.DerivedGeometry.OpenRestrictionForget
public import Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
概要：準連接コホモロジーを持つ実際の導来対象を開部分へ制限する。
方針：係数忘却と開制限の比較をコホモロジーに適用する。
規約：各項の準連接性や係数の平坦性を要求しない。
使われ方：TT 3.19・8.1、Toën §3.2 の T2・T3 の入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w w'
open CategoryTheory AlgebraicGeometry
namespace SerrePositivity.KST.DerivedGeometry.CoefficientSheaf
variable {X : Scheme.{u}} (B : CoefficientSheaf X) (U : X.Opens)
  [HasDerivedCategory.{w} B.Modules] [HasDerivedCategory.{w'} (B.restrict U).Modules]

/--
概要：導来開制限の基礎 O コホモロジーは元の基礎コホモロジーの開制限。
方針：導来制限のコホモロジー比較と忘却の自然同型を合成する。
規約：同じ層と同じコホモロジーを比較する。
使われ方：TT 3.19・8.1 の Dqc の局所性。
-/
def derivedRestrictionUnderlyingHomologyIso (n : ℤ) :
    B.derivedRestriction U ⋙ (B.restrict U).underlyingCohomology n ≅
      B.underlyingCohomology n ⋙ Scheme.Modules.restrictFunctor U.ι :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (B.derivedRestrictionHomologyIso U n) (B.restrict U).forget ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (DerivedCategory.homologyFunctor B.Modules n)
      (B.openRestrictionForgetIso U) ≪≫
    (Functor.associator _ _ _).symm

/--
概要：係数つき Dqc の対象の開制限も準連接コホモロジーを持つ。
方針：全次数のコホモロジー比較と準連接層の開制限の定理を使う。
規約：複体の各項は任意の係数加群層でよい。
使われ方：TT 3.19・8.1、Toën §3.2 の係数つき Dqc の制限。
-/
lemma derivedRestriction_hasQuasicoherentCohomology (M : DerivedCategory B.Modules)
    (hM : B.hasQuasicoherentCohomology M) :
    (B.restrict U).hasQuasicoherentCohomology ((B.derivedRestriction U).obj M) := by
  intro n
  let : ((B.underlyingCohomology n).obj M).IsQuasicoherent := hM n
  exact (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).prop_of_iso
    ((B.derivedRestrictionUnderlyingHomologyIso U n).app M).symm
    (show (((Scheme.Modules.restrictFunctor U.ι).obj
      ((B.underlyingCohomology n).obj M))).IsQuasicoherent from inferInstance)

/--
概要：係数つき Dqc から開部分の係数つき Dqc への制限関手。
方針：実際の導来開制限を準連接コホモロジーの部分圏へ制限する。
規約：厳密な複体の降下データへ定義し直さない。
使われ方：TT 3.19・8.1、Toën §3.2 の局所化・Zariski 降下。
-/
def dqcRestriction : B.Dqc ⥤ (B.restrict U).Dqc :=
  ObjectProperty.lift _ (B.dqcInclusion ⋙ B.derivedRestriction U)
    (fun M => B.derivedRestriction_hasQuasicoherentCohomology U M.obj M.property)

end SerrePositivity.KST.DerivedGeometry.CoefficientSheaf
