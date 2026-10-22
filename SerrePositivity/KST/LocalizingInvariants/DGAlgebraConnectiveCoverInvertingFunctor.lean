module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraConnectiveCoverFunctor
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPathInvertingFunctor

/-!
概要：connective 準同型だけを反転する関手を、元の cover による前合成で全準同型反転へ移す。
方針：smart 切断の準同型保存と、元の cover counit の自然性を使う。
規約：元の関手を非 connective な代数上で変更したとは主張しない。使われ方：値の比較の移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R]

lemma connectiveCoverMap_quasiIso {A B : Mon (Complex R)} (f : A ⟶ B) (hf : QuasiIso f.hom) :
    QuasiIso (connectiveCoverMap R f).hom := by
  have := hf
  change QuasiIso (CochainComplex.truncLEMap f.hom 0)
  rw [CochainComplex.quasiIso_truncLEMap_iff]
  intro i hi
  infer_instance

variable {D : Type v} [Category.{w} D] (L : Mon (Complex R) ⥤ D)

lemma invertsQuasiIsos_coverFunctor (hL : InvertsConnectiveQuasiIsos R L) :
    InvertsQuasiIsos R (connectiveCoverFunctor R ⋙ L) := by
  intro A B f hf
  exact hL (connectiveCover_isConnective R A) (connectiveCover_isConnective R B)
    (connectiveCoverMap R f) (connectiveCoverMap_quasiIso R f hf)

lemma coverCounit_naturality_value {A B : Mon (Complex R)} (f : A ⟶ B) :
    (connectiveCoverFunctor R ⋙ L).map f ≫ L.map (connectiveCoverInclusion R B) =
      L.map (connectiveCoverInclusion R A) ≫ L.map f := by
  change L.map (connectiveCoverMap R f) ≫ L.map (connectiveCoverInclusion R B) = _
  have h : connectiveCoverMap R f ≫ connectiveCoverInclusion R B =
      connectiveCoverInclusion R A ≫ f := (connectiveCoverCounit R).naturality f
  rw [← L.map_comp, h, L.map_comp]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
