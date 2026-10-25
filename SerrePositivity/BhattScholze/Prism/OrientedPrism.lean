module

public import SerrePositivity.BhattScholze.Prism.OrientedDeltaPair
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.AdicComparison

/-! # 非零因子の生成元を選択したprism

BS著者公開版Def 3.2の主イデアルの場合。Cartierイデアルは(d)とし、
導来(p,d)完備性は生成元p,dに関する既存の実導来完備性を使う。
一般Cartierイデアルの局所化降下や圏全体の構築は含めない。
-/

@[expose] public noncomputable section
universe u v w
namespace SerrePositivity.BhattScholze
variable (p : ℕ) [Fact p.Prime] (A : Type u) [CommRing A]

/-- oriented prism：δ環、正則な生成元、導来(p,d)完備性、prismのイデアル条件。
生成元以外のCartierイデアルはこの型の対象外。 -/
structure OrientedPrism where
  deltaStructure : DeltaStructure p A
  generator : A
  generator_regular : Function.Injective (fun x : A ↦ generator * x)
  complete_p : DerivedCompletion.IsModuleComplete A (p : A) (ModuleCat.of A A)
  complete_generator : DerivedCompletion.IsModuleComplete A generator (ModuleCat.of A A)
  p_mem : (p : A) ∈ Ideal.span {generator, deltaStructure.frobeniusLift generator}

namespace OrientedPrism
variable {p A}

/-- 選択生成元の主イデアル。 -/
def ideal (P : OrientedPrism p A) : Ideal A := Ideal.span {P.generator}

/-- 選択生成元の主イデアルは有限生成。 -/
theorem ideal_fg (P : OrientedPrism p A) : P.ideal.FG :=
  Submodule.fg_span (Set.toFinite _)

/-- 原典のp∈I+φ(I)Aを選択した主イデアルについて満たす。 -/
theorem p_mem_sup_map (P : OrientedPrism p A) :
    (p : A) ∈ P.ideal ⊔ P.ideal.map P.deltaStructure.frobeniusLift := by
  simpa only [ideal, Ideal.map_span, Set.image_singleton, ← Ideal.span_union,
    Set.singleton_union] using P.p_mem

/-- distinguishedな正則元と実導来完備性からoriented prismを構成する。 -/
def ofDistinguished (D : DeltaStructure p A) (d : A)
    (hd : D.IsDistinguished d) (hreg : Function.Injective (fun x : A ↦ d * x))
    (hp : DerivedCompletion.IsModuleComplete A (p : A) (ModuleCat.of A A))
    (hc : DerivedCompletion.IsModuleComplete A d (ModuleCat.of A A)) : OrientedPrism p A :=
  ⟨D, d, hreg, hp, hc, hd.p_mem_span⟩

/-- 非零因子の生成元に関して、導来完備性から古典的完備性を得る。 -/
theorem isAdicComplete_generator (P : OrientedPrism p A) :
    IsAdicComplete (Ideal.span {P.generator}) A :=
  (DerivedCompletion.isModuleComplete_iff_isAdicComplete_of_regular A P.generator
    (ModuleCat.of A A) P.generator_regular).mp P.complete_generator

/-- pが正則なら、prismの導来p完備性から古典的p完備性を得る。 -/
theorem isAdicComplete_p_of_regular (P : OrientedPrism p A)
    (hp : Function.Injective (fun x : A ↦ (p : A) * x)) :
    IsAdicComplete (Ideal.span {(p : A)}) A :=
  (DerivedCompletion.isRingModuleComplete_iff_isAdicComplete_natCast A p hp).mp P.complete_p

/-- pが正則なoriented prismの選択生成元はdistinguished。
導来比較でp,dをJacobson根基へ移し、既存Lemma 2.25を適用する。 -/
theorem isDistinguished_of_p_regular (P : OrientedPrism p A)
    (hp : Function.Injective (fun x : A ↦ (p : A) * x)) :
    P.deltaStructure.IsDistinguished P.generator := by
  let := P.isAdicComplete_generator
  let := P.isAdicComplete_p_of_regular hp
  apply P.deltaStructure.isDistinguished_of_p_mem_span P.generator
  · exact IsAdicComplete.le_jacobson_bot (Ideal.span {P.generator})
      (Ideal.subset_span (by simp))
  · exact IsAdicComplete.le_jacobson_bot (Ideal.span {(p : A)})
      (Ideal.subset_span (by simp))
  · exact P.p_mem

end OrientedPrism
end SerrePositivity.BhattScholze
