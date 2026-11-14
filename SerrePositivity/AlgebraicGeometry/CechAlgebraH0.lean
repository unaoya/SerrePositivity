module

public import SerrePositivity.AlgebraicGeometry.CechRingEqualizer
public import SerrePositivity.AlgebraicGeometry.FullCechH0Compatible

/-!
概要：適合する代数係数の切断の部分代数を Čech H⁰ と比較する。
方針：二つの面の equalizer と差の核を同定する。
規約：環構造は元の切断の成分ごとの乗法から来る。
使われ方：射影 Čech H⁰ の有限性を切断の環へ移す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u v
variable {R : Type u} {ι : Type v} [CommRing R] [DecidableEq ι]
variable (D : Finset ι ⥤ CommAlgCat.{u} R)

/-- 代数係数の環図式。 -/
abbrev algebraCechRingDiagram := D ⋙ forget₂ (CommAlgCat R) CommRingCat

/-- 代数係数の加群図式。 -/
abbrev algebraCechModuleDiagram :=
  D ⋙ forget₂ (CommAlgCat R) (AlgCat R) ⋙ forget₂ (AlgCat R) (ModuleCat R)

/-- 代数係数の全タプルの切断に、成分ごとのスカラー作用を入れる。 -/
instance fullAlgebraCechCochainsAlgebra (k : ℕ) :
    Algebra R (FullRingCechCochains (algebraCechRingDiagram D) k) :=
  inferInstanceAs (Algebra R ((t : Fin k → ι) → D.obj (cechTupleSupport t)))

/-- 二重点での片側の制限を代数準同型として扱う。 -/
def fullAlgebraCechFace (i : Fin 2) :
    FullRingCechCochains (algebraCechRingDiagram D) 1 →ₐ[R]
      FullRingCechCochains (algebraCechRingDiagram D) 2 where
  __ := fullRingCechFace (algebraCechRingDiagram D) i
  commutes' r := by
    funext t
    exact (D.map (homOfLE (cechTupleSupport_face_subset t i))).hom.commutes r

/-- 適合する切断の部分代数。乗法は切断環の乗法。 -/
def fullAlgebraCechEqualizer := (fullAlgebraCechFace D 0).equalizer (fullAlgebraCechFace D 1)

/-- 適合する切断の部分加群は、Čech の最初の余境界の核。 -/
theorem fullAlgebraCechEqualizer_toSubmodule :
    (fullAlgebraCechEqualizer D).toSubmodule =
      LinearMap.ker (fullCechDifferential (algebraCechModuleDiagram D) 1) := by
  ext a
  change (fullAlgebraCechFace D 0 a = fullAlgebraCechFace D 1 a) ↔ _
  rw [LinearMap.mem_ker, funext_iff, funext_iff]
  apply forall_congr'
  intro t
  have he : fullCechDifferential (algebraCechModuleDiagram D) 1 a t =
      fullAlgebraCechFace D 0 a t - fullAlgebraCechFace D 1 a t :=
    fullCechDifferential_one_apply (algebraCechModuleDiagram D) a t
  constructor
  · intro h
    exact he.trans (sub_eq_zero.mpr h)
  · intro h
    exact sub_eq_zero.mp (he.symm.trans h)

/-- 適合する切断の部分代数の加法群と Čech H⁰ の線形同型。
BST13 Lemma 3.8 の H⁰ に用いる Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
def fullAlgebraCechH0Equiv : (fullAlgebraCechEqualizer D) ≃ₗ[R]
    (fullCechComplex (algebraCechModuleDiagram D)).homology 0 :=
  (LinearEquiv.ofEq _ _ (fullAlgebraCechEqualizer_toSubmodule D)).trans
    (fullCechH0KernelIso (algebraCechModuleDiagram D)).toLinearEquiv.symm

/-- Čech H⁰ が有限なら、適合する切断の部分代数も基底環上有限。
BST13 Lemma 3.8 の H⁰ の有限性に用いる Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem fullAlgebraCechEqualizer_finite
    [Module.Finite R ((fullCechComplex (algebraCechModuleDiagram D)).homology 0)] :
    Module.Finite R (fullAlgebraCechEqualizer D) :=
  Module.Finite.of_surjective (fullAlgebraCechH0Equiv D).symm.toLinearMap
    (fullAlgebraCechH0Equiv D).symm.surjective

end SerrePositivity.AlgebraicGeometry
