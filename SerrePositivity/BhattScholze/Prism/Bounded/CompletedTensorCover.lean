module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.BhattScholze.Prism.Bounded.CompletedTensorH0
import all SerrePositivity.BhattScholze.Prism.Bounded.CompleteFlatReduction
import SerrePositivity.BhattScholze.Prism.Basic.Rigidity
import SerrePositivity.BhattScholze.Prism.Bounded.CompletionFiniteResidue
import Mathlib.RingTheory.TensorProduct.Quotient
import SerrePositivity.CommutativeAlgebra.CompletelyFlat.Criterion

/-!
# 有界 prism の完備テンソル積の完全平坦性

## 概要
完全平坦な prism の射を任意の有界 prism の射で底変換した完備テンソル積は完全平坦。

## 方針
導来完備な底変換の剰余を調べ、離散性を示してから完全平坦性を通常の環へ移す。

## 規約
BS 著者版 Corollary 3.12 (a)。二元完備化は左因子の向きで取る。

## 使われ方
有界 prism の押し出し。
-/

public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

namespace SerrePositivity.BhattScholze.Prismatic

open CategoryTheory CategoryTheory.Limits DerivedCompletion HomologicalComplex
attribute [local instance] HasDerivedCategory.standard adicQuotientAlgebra
open scoped TensorProduct
open TensorProduct

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]

private theorem complete_completion_of_complete (a b : B)
    (X : ConcreteDerivedCategory B) (hc : IsComplete B a X) :
    IsComplete B a ((derivedComplexCompletionFunctor B b).obj X) := by
  let K := DerivedCategory.Q.objPreimage X
  let e := DerivedCategory.Q.objObjPreimageIso X
  have hK := isComplete_of_iso B a e.symm hc
  have h := isComplete_complexTowerHomotopyLimitObject_of_stages B a
    (complexPowerKoszulStage B b K) (complexPowerKoszulTransition B b K)
    (fun n ↦ isComplete_Q_mappingCone B a (smulId (b ^ n) K) hK hK)
  exact isComplete_of_iso B a
    (((derivedComplexCompletionComparison B b).app K).symm ≪≫
      (derivedComplexCompletionFunctor B b).mapIso e) h

private theorem completelyFlat_of_discrete_completelyFlat
    (I : Ideal B) (M : ModuleCat.{u} B)
    (hf : IsDerivedCompletelyFlat I (boundedAboveDerivedSingleFunctor.obj M)) :
    IsCompletelyFlat I M := by
  let q := Ideal.Quotient.mk I
  let e := (boundedAboveDerivedBaseChangeModuleNatIso q).app M
  let F (i : ℤ) := DerivedCategory.homologyFunctor (ModuleCat (B ⧸ I)) i
  unfold IsDerivedCompletelyFlat at hf
  have ht : scalarExtensionTorVanishing q M := by
    apply (derivedModuleBaseChange_negative_homology_vanishes_iff q M).mp
    intro n hn
    exact (hf.1 (-(n : ℤ)) (by omega)).of_iso ((F (-(n : ℤ))).mapIso e.symm)
  let L := (F 0).obj
    ((boundedAboveDerivedBaseChange q).obj (boundedAboveDerivedSingleFunctor.obj M)).obj
  let e₀ : ((ModuleCat.extendScalars q).obj M) ≃ₗ[B ⧸ I] L :=
    ((boundedAboveDerivedBaseChangeModuleH0Iso q).app M).symm.toLinearEquiv
  let : Module.Flat (B ⧸ I) L := hf.2
  exact isCompletelyFlat_of_acyclic_flat_reduction I M ht (Module.Flat.of_linearEquiv e₀)

/-- 概要：有界 prism 上で、完備テンソル積は左因子上完全平坦。
方針：二座標の完備導来底変換の離散性を使い、零次の線形同値を通して移す。
規約：BS 著者版 Corollary 3.12 (a)。右因子は共通の基底上で完全平坦。
使われ方：prismatic site の完全平坦な押し出し。 -/
theorem prismCompletedTensor_completelyFlat
    {p : ℕ} [Fact p.Prime] (P : OrientedPrism p A) (Q : OrientedPrism p B)
    (hQ : IsBoundedPrism Q) (g : OrientedPrism.Hom P Q) (f : A →+* C)
    (hf : letI := f.toAlgebra; IsCompletelyFlat (Ideal.span {(p : A), P.generator}) C) :
    letI := f.toAlgebra
    letI := g.toRingHom.toAlgebra
    let T := PrismCompletedTensor (A := A) (C := C) Q
    letI := (prismCompletedTensorLeft Q (A := A) (C := C)).toAlgebra
    IsCompletelyFlat (Ideal.span {(p : B), Q.generator}) T := by
  let := f.toAlgebra
  let := g.toRingHom.toAlgebra
  let I := Ideal.span {(p : A), P.generator}
  let J := Ideal.span {(p : B), Q.generator}
  let l := prismCompletedTensorLeft Q (A := A) (C := C)
  let := l.toAlgebra
  have hg : I.map g.toRingHom = J := by
    change (Ideal.span {(p : A), P.generator}).map g.toRingHom = _
    rw [← Set.singleton_union, Ideal.span_union, Ideal.map_sup, Ideal.map_span,
      Set.image_singleton, map_natCast]
    change Ideal.span {(p : B)} ⊔ P.ideal.map g.toRingHom = _
    rw [g.map_ideal_eq, OrientedPrism.ideal, ← Ideal.span_union, Set.singleton_union]
  let X := boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A C)
  let Y := pairCompletedBaseChange g.toRingHom (p : B) Q.generator X
  have hY : IsDerivedCompletelyFlat J Y :=
    pairCompletedBaseChange_completelyFlat g.toRingHom I (p : B) Q.generator hg hf
  have hdp : IsComplete B Q.generator Y.obj :=
    derivedComplexCompletionFunctor_isComplete B Q.generator _
  have hpp : IsComplete B (p : B) Y.obj :=
    complete_completion_of_complete (p : B) Q.generator _
      (derivedComplexCompletionFunctor_isComplete B (p : B) _)
  have hpure := derivedCompletelyFlat_isDiscrete_of_boundedPrism Q hQ Y hpp hdp hY
  let := hpure.1
  let := hpure.2.1
  let L := (DerivedCategory.homologyFunctor (ModuleCat B) 0).obj Y.obj
  let e : Y ≅ boundedAboveDerivedSingleFunctor.obj L :=
    ObjectProperty.isoMk _ (normalizedPureHomologyIso Y.obj 0)
  have hL : IsDerivedCompletelyFlat J (boundedAboveDerivedSingleFunctor.obj L) := by
    unfold IsDerivedCompletelyFlat at hY ⊢
    let e' := DerivedCategory.Minus.ι.mapIso ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk J)).mapIso e)
    refine ⟨fun i hi ↦ (hY.1 i hi).of_iso
      ((DerivedCategory.homologyFunctor (ModuleCat (B ⧸ J)) i).mapIso e'.symm), ?_⟩
    let : Module.Flat (B ⧸ J) ((DerivedCategory.homologyFunctor (ModuleCat (B ⧸ J)) 0).obj
        (DerivedCategory.Minus.ι.obj ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk J)).obj Y))) :=
      hY.2
    exact Module.Flat.of_linearEquiv
      ((DerivedCategory.homologyFunctor (ModuleCat (B ⧸ J)) 0).mapIso e'.symm).toLinearEquiv
  exact isCompletelyFlat_of_linearEquiv J (pairCompletedBaseChangeH0LinearEquiv (A := A) (C := C) Q)
    (completelyFlat_of_discrete_completelyFlat J L hL)

/-- 完備な底変換で忠実性も保たれる。 -/
theorem prismCompletedTensor_completelyFaithfullyFlat
    {p : ℕ} [Fact p.Prime] (P : OrientedPrism p A) (Q : OrientedPrism p B)
    (hQ : IsBoundedPrism Q) (g : OrientedPrism.Hom P Q) (f : A →+* C)
    (hf : letI := f.toAlgebra; IsCompletelyFaithfullyFlat (Ideal.span {(p : A), P.generator}) C) :
    letI := f.toAlgebra
    letI := g.toRingHom.toAlgebra
    let H := PrismCompletedTensor (A := A) (C := C) Q
    letI := (prismCompletedTensorLeft Q (A := A) (C := C)).toAlgebra
    IsCompletelyFaithfullyFlat (Ideal.span {(p : B), Q.generator}) H := by
  let := f.toAlgebra
  let := g.toRingHom.toAlgebra
  let H := PrismCompletedTensor (A := A) (C := C) Q
  let T := B ⊗[A] C
  let d := algebraMap B T Q.generator
  let : CommRing (PDCompletionH0 T p d) := pdCompletionCommRing T p d
  let v : T →+* H := pdCompletionUnit T p d
  let l : B →+* H := prismCompletedTensorLeft Q
  let := l.toAlgebra
  let I := Ideal.span {(p : A), P.generator}
  let J := Ideal.span {(p : B), Q.generator}
  let E := B ⧸ J
  let U := A ⧸ I
  let q := Ideal.Quotient.mk J
  have hg : I.map g.toRingHom ≤ J := by
    change (Ideal.span {(p : A), P.generator}).map g.toRingHom ≤ _
    rw [Ideal.map_span, Set.image_pair, map_natCast, Ideal.span_le]
    intro x hx
    rcases hx with h | h
    · rw [h]
      exact Ideal.subset_span (Set.mem_insert _ _)
    · obtain rfl := Set.mem_singleton_iff.mp h
      have hd : Q.ideal ≤ J := Ideal.span_le.mpr (Set.singleton_subset_iff.mpr
        (Ideal.subset_span (Set.mem_insert_of_mem _ rfl)))
      exact hd g.map_generator_mem
  let α : U →+* E := Ideal.quotientMap J g.toRingHom (Ideal.map_le_iff_le_comap.mp hg)
  let : Algebra U E := α.toAlgebra
  let : IsScalarTower A U E := IsScalarTower.of_algebraMap_eq' rfl
  refine ⟨prismCompletedTensor_completelyFlat P Q hQ g f hf.1, ?_⟩
  let J' := J.map (algebraMap B T)
  have hpJ : (p : T) ^ (1 : ℕ) ∈ J' := by
    simpa only [pow_one, map_natCast] using
      Ideal.mem_map_of_mem (algebraMap B T) (Ideal.subset_span (Set.mem_insert (p : B) {Q.generator}))
  have hdJ : d ^ (1 : ℕ) ∈ J' := by
    rw [pow_one]
    exact Ideal.mem_map_of_mem (algebraMap B T)
      (Ideal.subset_span (Set.mem_insert_of_mem _ rfl))
  have hJ : J'.map v = J.map l := by
    rw [Ideal.map_map]
    rfl
  obtain ⟨e, he⟩ := exists_pdCompletion_finiteResidue_equiv p d J' 1 1 hpJ hdJ
  let e₁ := (Ideal.quotEquivOfEq hJ.symm).trans e
  let e₂ := (Algebra.TensorProduct.quotientTensorEquiv (R := A) B C B J).symm
  let : Algebra E (H ⧸ J.map l) := adicQuotientAlgebra J H
  let er := e₁.trans e₂.toRingEquiv
  let e₃ : (H ⧸ J.map l) ≃ₗ[E] E ⊗[A] C :=
    { er.toAddEquiv with
      map_smul' := by
        intro a x
        obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
        change er (Ideal.Quotient.mk (J.map l) (l b) * x) = (q b) • er x
        have hsmul : (q b) • er x = (q b ⊗ₜ[A] (1 : C)) * er x :=
          Algebra.smul_def (q b) (er x)
        rw [hsmul, map_mul]
        congr 1
        change e₂ (e (Ideal.Quotient.mk _ (v (algebraMap B T b)))) =
          algebraMap E (E ⊗[A] C) (q b)
        rw [show e (Ideal.Quotient.mk _ (v (algebraMap B T b))) =
          Ideal.Quotient.mk J' (algebraMap B T b) from RingHom.congr_fun he _]
        change e₂ (Ideal.Quotient.mk J' (b ⊗ₜ[A] (1 : C))) = (q b ⊗ₜ[A] (1 : C))
        exact Algebra.TensorProduct.quotientTensorEquiv_symm_apply_tmul B C B J b 1 }
  let e₄ := (Algebra.TensorProduct.quotIdealMapEquivQuotTensor H J).symm.toLinearEquiv
  let e₅ := (AlgebraTensorModule.cancelBaseChange A U E E C).symm
  let : Module.FaithfullyFlat U (U ⊗[A] C) := hf.2
  let : Module.FaithfullyFlat E (E ⊗[U] (U ⊗[A] C)) := inferInstance
  exact Module.FaithfullyFlat.of_linearEquiv _ _ (e₄.trans (e₃.trans e₅))

end SerrePositivity.BhattScholze.Prismatic

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Lemma 3.7" (partial := special) "(1) と (2)（完全平坦な複体の離散性、通常の導来圏で、BS-W15 K4）、(3)（完全平坦な δ 代数から有界 prism、exists_boundedPrism_of_completelyFlat_deltaAlgebra）は本体。(4) は不要（D19）。向き付きの基底 ／ 11-11 更新（2） ／ 11-12 夜更新（ノート本文の更新時）"] _root_.SerrePositivity.BhattScholze.Prismatic.prismCompletedTensor_completelyFaithfullyFlat
