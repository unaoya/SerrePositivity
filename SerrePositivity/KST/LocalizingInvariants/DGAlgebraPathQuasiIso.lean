module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPathHomotopy

/-!
概要：実乗法的経路で結ばれた二つの元の代数射は、同時に準同型である。
方針：経路から元の鎖ホモトピーを回収し、各ホモロジー射の等式を使う。
規約：実射への準同型判定。使われ方：像 class の構成で得た底射の比較。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.Path
variable {R : Type u} [CommRing R] {A B : Mon (Complex R)} {a b : A ⟶ B}

lemma Witness.quasiIsoAt_iff (w : Witness R a b) (j : ℤ) :
    QuasiIsoAt a.hom j ↔ QuasiIsoAt b.hom j := by
  rw [quasiIsoAt_iff_isIso_homologyMap, quasiIsoAt_iff_isIso_homologyMap,
    w.chainHomotopy.homologyMap_eq]

lemma Witness.quasiIso_iff (w : Witness R a b) : QuasiIso a.hom ↔ QuasiIso b.hom := by
  rw [_root_.quasiIso_iff, _root_.quasiIso_iff]
  apply forall_congr'
  intro j
  rw [quasiIsoAt_iff_isIso_homologyMap, quasiIsoAt_iff_isIso_homologyMap,
    w.chainHomotopy.homologyMap_eq]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.Path
