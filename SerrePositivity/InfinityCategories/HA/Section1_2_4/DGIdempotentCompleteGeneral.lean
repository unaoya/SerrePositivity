module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CompletenessEquivalence
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Triangles.DGStableHomotopyEquivalence
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.Nerves.DGNerveUniverseLift
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.Completion
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CompletenessUniverse
public import Mathlib.CategoryTheory.Idempotents.Basic
/-!
概要：H⁰ の分裂から dg nerve の全 coherent 冪等完備性を回収する一般入口。
方針：充満忠実像の retract と Yoneda 完備化を対象宇宙の持ち上げで接続する。
規約：Small 仮定を追加せず、元の全 Idem 図式の強い分裂を保つ。
使われ方：dg の実 perfect 模型に安定性の依存を介さず適用する。
-/
@[expose] public section
noncomputable section
universe u v w z
open _root_.CategoryTheory
variable {C : Type u} [Category.{v} C] {D : Type w} [Category.{z} D]
namespace SerrePositivity.InfinityCategories.HA.Section1_2_4
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

end SerrePositivity.InfinityCategories.HA.Section1_2_4
namespace SerrePositivity.InfinityCategories.HA.Section1_2_4
open _root_.SSet
open scoped _root_.Simplicial

universe a
/-- h の冪等完備性から、実充満忠実関手の像の retract を回収する。 -/
lemma fullyFaithful_retract_image_of_ho_complete {X Y : SSet.{a}}
    [Quasicategory X] [Quasicategory Y] (F : X ⟶ Y) (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful F)
    [CategoryTheory.IsIdempotentComplete (hoFunctor.obj X)]
    (x : X _⦋0⦌) (y : Y _⦋0⦌)
    (r : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.VertexRetraction y (F.app (Opposite.op ⦋0⦌) x)) :
    ∃ z : X _⦋0⦌, Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso y (F.app (Opposite.op ⦋0⦌) z)) := by
  have h := hF.toHoFullyFaithful
  let := h.full
  let := h.faithful
  obtain ⟨z, hz⟩ := _root_.SerrePositivity.InfinityCategories.HA.Section1_2_4.fullFaithful_retract_iso_in_image (hoFunctor.map F).toFunctor
    (HomotopyCategory.mk x) (HomotopyCategory.mk y) r.i r.r r.retract
  obtain ⟨z, rfl⟩ := Truncated.HomotopyCategory.mk_surjective z
  exact ⟨z, hz⟩
/-- 持ち上げた h の分裂から元の全 Idem 図式の強い分裂を回収する。 -/
lemma idempotentComplete_of_ulift_ho_complete (X : SSet.{a}) [Quasicategory X]
    [CategoryTheory.IsIdempotentComplete
      (hoFunctor.obj ((SSet.uliftFunctor.{a + 1, a}).obj X))] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete X := by
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsEssentiallySurjective (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemYoneda X) := by
    intro y
    obtain ⟨x, ⟨r⟩⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemVertex_retract_idemYoneda y
    obtain ⟨z, ⟨e⟩⟩ := _root_.SerrePositivity.InfinityCategories.HA.Section1_2_4.fullyFaithful_retract_image_of_ho_complete
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemYoneda X) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemYoneda_isFullyFaithful X) (ULift.up x) y r
    exact ⟨z, ⟨e.symm⟩⟩
  have hq := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.isQCatEquivalence_of_isFullyFaithful_of_isEssentiallySurjective (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemYoneda X)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemYoneda_isFullyFaithful X) he
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.isIdempotentComplete_of_ulift
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idem_isIdempotentComplete X).of_equivalence hq.choose.symm)
end SerrePositivity.InfinityCategories.HA.Section1_2_4

namespace SerrePositivity.InfinityCategories.HA.Section1_2_4
open _root_.CategoryTheory _root_.SerrePositivity.DifferentialGraded _root_.SSet
universe b c d
variable (R : Type b) [CommRing R] (C : Type c) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
/-- 対象だけの宇宙持ち上げは、同じ全 Hom を保つ H⁰ 同値。 -/
def dgUniverseLiftH0Equivalence :
    _root_.SerrePositivity.DifferentialGraded.HomotopyCategory R C ≌
      _root_.SerrePositivity.DifferentialGraded.HomotopyCategory R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{c, d} C) :=
  CategoryTheory.Equivalence.mk (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp R C).onHomotopy
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown R C).onHomotopy
    (eqToIso (by rw [← DGFunctor.onHomotopy_comp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp_comp_down,
      _root_.SerrePositivity.DifferentialGraded.DGFunctor.onHomotopy_id]))
    (eqToIso (by rw [← DGFunctor.onHomotopy_comp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown_comp_up,
      _root_.SerrePositivity.DifferentialGraded.DGFunctor.onHomotopy_id]))
/-- H⁰ の冪等完備性は元の dg nerve の全 coherent 冪等完備性を与える。 -/
lemma dgNerve_isIdempotentComplete_of_h0
    [CategoryTheory.IsIdempotentComplete (_root_.SerrePositivity.DifferentialGraded.HomotopyCategory R C)] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R C) := by
  let e := (Cat.equivOfIso (hoFunctor.mapIso
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveUniverseLiftIso.{b, c, max b c + 1} R C))).trans
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableHomotopyEquivalence R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{c, max b c + 1} C)).trans
        (_root_.SerrePositivity.InfinityCategories.HA.Section1_2_4.dgUniverseLiftH0Equivalence.{b, c, max b c + 1} R C).symm)
  let := CategoryTheory.Idempotents.Equivalence.isIdempotentComplete e.symm inferInstance
  exact _root_.SerrePositivity.InfinityCategories.HA.Section1_2_4.idempotentComplete_of_ulift_ho_complete (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R C)
end SerrePositivity.InfinityCategories.HA.Section1_2_4

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "1.2.4.6" (partial := direction) "仮定：宇宙を持ち上げた準圏のホモトピー圏が冪等完備（HA の (2) を持ち上げた条件。Lean は安定性を要求しない）。結論：全 coherent 冪等射が分裂する。HA の (2)⇒(1) に対応し、(1)⇒(2) はこの型にない（Lean が弱い）。"] _root_.SerrePositivity.InfinityCategories.HA.Section1_2_4.idempotentComplete_of_ulift_ho_complete
