module

public import SerrePositivity.AlgebraicGeometry.ProjectiveCechFunctor
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
概要：通常の全タプル Čech H⁰ を、次数零の余境界の核と比較する。
方針：左端の境界が零であることと、ModuleCat の cycles の具体的な核を使う。
規約：長さ零の増大項を通常の次数零と取り違えない。
使われ方：標準開の切断の equalizer 部分環と Čech H⁰ の照合。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u v
variable {R : Type u} {ι : Type v} [CommRing R] [DecidableEq ι]

/-- 全タプル Čech H⁰ と最初の余境界の核の比較。BST13 Lemma 3.8 の H⁰ に使う Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
def fullCechH0KernelIso (D : Finset ι ⥤ ModuleCat R) :
    (fullCechComplex D).homology 0 ≅ ModuleCat.of R (LinearMap.ker (fullCechDifferential D 1)) := by
  have hd : ((fullCechComplex D).sc' 0 0 1).g.hom = fullCechDifferential D 1 := by
    change (CochainComplex.of.d
      (fun q ↦ ModuleCat.of R (FullCechCochains D (q + 1)))
      (fun q ↦ ModuleCat.ofHom (fullCechDifferential D (q + 1))) 0 (0 + 1)).hom = _
    rw [CochainComplex.of_d]
    rfl
  refine (asIso ((fullCechComplex D).homologyπ 0)).symm ≪≫
    (fullCechComplex D).cyclesIsoSc' 0 0 1 (by simp) (by simp) ≪≫ ?_
  have e : ((fullCechComplex D).sc' 0 0 1).cycles ≅
      ModuleCat.of R (LinearMap.ker ((fullCechComplex D).sc' 0 0 1).g.hom) :=
    ((fullCechComplex D).sc' 0 0 1).moduleCatCyclesIso
  exact e ≪≫ (LinearEquiv.ofEq _ _ (congrArg LinearMap.ker hd)).toModuleIso

end SerrePositivity.AlgebraicGeometry
