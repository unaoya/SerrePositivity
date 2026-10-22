module
public import SerrePositivity.InfinityCategories.F2.Idempotent.CompletenessEquivalence
public import SerrePositivity.InfinityCategories.Derived.DGStableHomotopyEquivalence
public import SerrePositivity.InfinityCategories.Derived.DGNerveUniverseLift
public import SerrePositivity.InfinityCategories.Derived.DGAlgebraPerfectInfinity
public import SerrePositivity.DifferentialGraded.Perfect.EnhancementIdempotents
public import SerrePositivity.InfinityCategories.F2.Idempotent.Completion
public import SerrePositivity.InfinityCategories.F2.Idempotent.CompletenessUniverse
public import Mathlib.CategoryTheory.Idempotents.Basic
/-!
概要：実 Perf の coherent 冪等完備性と、H⁰ 分裂から dg nerve への一般判定。
方針：充満忠実像の retract と Yoneda 冪等完備化、対象宇宙持ち上げを接続する。
規約：元の全 Idem 図式を厳密に回収する強い分裂を結論とする。
使われ方：β5(f)、非可換 dg 代数の Perf(A) の Cat^perf への供給。
-/
@[expose] public section
noncomputable section
universe u v w z
open CategoryTheory
variable {C : Type u} [Category.{v} C] {D : Type w} [Category.{z} D]
namespace SerrePositivity.InfinityCategories
/-- 冪等完備な通常の圏の充満忠実像は同型を除いて retract に閉じる。 -/
lemma fullFaithful_retract_iso_in_image (F : C ⥤ D) [F.Full] [F.Faithful]
    [IsIdempotentComplete C] (x : C) (y : D)
    (i : y ⟶ F.obj x) (r : F.obj x ⟶ y) (h : i ≫ r = 𝟙 y) :
    ∃ z : C, Nonempty (y ≅ F.obj z) := by
  let p : x ⟶ x := F.preimage (r ≫ i)
  have hpmap : F.map p = r ≫ i := F.map_preimage _
  have hp : p ≫ p = p := by
    apply F.map_injective
    rw [F.map_comp, hpmap]
    simp only [Category.assoc, ← Category.assoc i r, h, Category.id_comp]
  obtain ⟨z, j, s, hjs, hsj⟩ := IsIdempotentComplete.idempotents_split x p hp
  refine ⟨z, ⟨⟨i ≫ F.map s, F.map j ≫ r, ?_, ?_⟩⟩⟩
  · calc
      _ = i ≫ F.map (s ≫ j) ≫ r := by simp only [F.map_comp, Category.assoc]
      _ = i ≫ (r ≫ i) ≫ r := by rw [hsj, hpmap]
      _ = 𝟙 y := by simp only [← Category.assoc, h, Category.id_comp]
  · calc
      _ = F.map j ≫ (r ≫ i) ≫ F.map s := by simp only [Category.assoc]
      _ = F.map (j ≫ p ≫ s) := by rw [F.map_comp, F.map_comp, hpmap]
      _ = 𝟙 (F.obj z) := by
        rw [← hsj]
        simp only [← Category.assoc, hjs, Category.id_comp, F.map_id]

end SerrePositivity.InfinityCategories
namespace SerrePositivity.InfinityCategories
open SSet
open scoped Simplicial
open F2.Idempotent
universe a
/-- h の冪等完備性から、実充満忠実関手の像の retract を回収する。 -/
lemma fullyFaithful_retract_image_of_ho_complete {X Y : SSet.{a}}
    [Quasicategory X] [Quasicategory Y] (F : X ⟶ Y) (hF : IsFullyFaithful F)
    [CategoryTheory.IsIdempotentComplete (hoFunctor.obj X)]
    (x : X _⦋0⦌) (y : Y _⦋0⦌)
    (r : VertexRetraction y (F.app (Opposite.op ⦋0⦌) x)) :
    ∃ z : X _⦋0⦌, Nonempty (VertexIso y (F.app (Opposite.op ⦋0⦌) z)) := by
  have h := hF.toHoFullyFaithful
  let := h.full
  let := h.faithful
  obtain ⟨z, hz⟩ := fullFaithful_retract_iso_in_image (hoFunctor.map F).toFunctor
    (HomotopyCategory.mk x) (HomotopyCategory.mk y) r.i r.r r.retract
  obtain ⟨z, rfl⟩ := Truncated.HomotopyCategory.mk_surjective z
  exact ⟨z, hz⟩
/-- 持ち上げた h の分裂から元の全 Idem 図式の強い分裂を回収する。 -/
lemma idempotentComplete_of_ulift_ho_complete (X : SSet.{a}) [Quasicategory X]
    [CategoryTheory.IsIdempotentComplete
      (hoFunctor.obj ((SSet.uliftFunctor.{a + 1, a}).obj X))] :
    F2.Idempotent.IsIdempotentComplete X := by
  have he : IsEssentiallySurjective (idemYoneda X) := by
    intro y
    obtain ⟨x, ⟨r⟩⟩ := idemVertex_retract_idemYoneda y
    obtain ⟨z, ⟨e⟩⟩ := fullyFaithful_retract_image_of_ho_complete
      (idemYoneda X) (idemYoneda_isFullyFaithful X) (ULift.up x) y r
    exact ⟨z, ⟨e.symm⟩⟩
  have hq := isQCatEquivalence_of_isFullyFaithful_of_isEssentiallySurjective (idemYoneda X)
    (idemYoneda_isFullyFaithful X) he
  exact isIdempotentComplete_of_ulift
    ((idem_isIdempotentComplete X).of_equivalence hq.choose.symm)
end SerrePositivity.InfinityCategories

namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
universe b c d
variable (R : Type b) [CommRing R] (C : Type c) [DGCategory R C]
/-- 対象だけの宇宙持ち上げは、同じ全 Hom を保つ H⁰ 同値。 -/
def dgUniverseLiftH0Equivalence :
    DifferentialGraded.HomotopyCategory R C ≌
      DifferentialGraded.HomotopyCategory R (DGUniverseLift.{c, d} C) :=
  CategoryTheory.Equivalence.mk (dgUniverseLiftUp R C).onHomotopy
    (dgUniverseLiftDown R C).onHomotopy
    (eqToIso (by rw [← DGFunctor.onHomotopy_comp, dgUniverseLiftUp_comp_down,
      DGFunctor.onHomotopy_id]))
    (eqToIso (by rw [← DGFunctor.onHomotopy_comp, dgUniverseLiftDown_comp_up,
      DGFunctor.onHomotopy_id]))
/-- H⁰ の冪等完備性は元の dg nerve の全 coherent 冪等完備性を与える。 -/
lemma dgNerve_isIdempotentComplete_of_h0
    [CategoryTheory.IsIdempotentComplete (DifferentialGraded.HomotopyCategory R C)] :
    F2.Idempotent.IsIdempotentComplete (dgNerve R C) := by
  let e := (Cat.equivOfIso (hoFunctor.mapIso
    (dgNerveUniverseLiftIso.{b, c, max b c + 1} R C))).trans
      ((dgStableHomotopyEquivalence R (DGUniverseLift.{c, max b c + 1} C)).trans
        (dgUniverseLiftH0Equivalence.{b, c, max b c + 1} R C).symm)
  let := CategoryTheory.Idempotents.Equivalence.isIdempotentComplete e.symm inferInstance
  exact idempotentComplete_of_ulift_ho_complete (dgNerve R C)
variable (D : Type c) [DGCategory R D] [Small.{b} D]
/-- 任意の小 dg 圏の実 Perf は coherent な意味で冪等完備。 -/
lemma dgModulePerfectInfinityCategory_isIdempotentComplete :
    F2.Idempotent.IsIdempotentComplete (dgModulePerfectInfinityCategory R D) :=
  dgNerve_isIdempotentComplete_of_h0 R (PerfectDGModule R D)
/-- 非可換 dg 代数の実 Perf は coherent な意味で冪等完備。 -/
lemma dgAlgebraPerfectInfinityCategory_isIdempotentComplete (B : Mon (Complex R)) :
    F2.Idempotent.IsIdempotentComplete (dgAlgebraPerfectInfinityCategory R B) :=
  dgModulePerfectInfinityCategory_isIdempotentComplete R (dgAlgebraCategory R B)
end SerrePositivity.InfinityCategories
