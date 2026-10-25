module

public import SerrePositivity.BhattScholze.Delta.DeltaPTorsionReduction
public import SerrePositivity.BhattScholze.Delta.Division.DeltaDivisionClassicalCompletion
public import SerrePositivity.BhattScholze.Delta.Distinguished
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import SerrePositivity.CommutativeAlgebra.AdicCompletionRegular
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.AdicComparison

/-! # 古典的p除算候補におけるdistinguished元の単元係数

既存Lemma 2.24を具体的な候補と標準射へ適用する。
実導来完備化との比較や完全平坦性はこの計算の結論に含めない。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- p除算候補の二元表示の完備化イデアルは、実際にはpの主イデアル。 -/
theorem deltaPDivisionAdicIdeal_eq_span_p (D : DeltaStructure p A) (a : σ → A) :
    deltaDivisionAdicIdeal D (p : A) a =
      Ideal.span {(p : DeltaDivisionTorsionQuotient D (p : A) a)} := by
  let B := DeltaDivisionTorsionQuotient D (p : A) a
  exact (congrArg (fun b : B ↦ Ideal.span {(p : B), b})
    (map_natCast (deltaDivisionTorsionMap D (p : A) a) p)).trans
      (congrArg (Ideal.span : Set B → Ideal B)
        (Set.insert_eq_of_mem (Set.mem_singleton (p : B))))

/-- 古典的p除算候補はp進完備。二元表示のイデアルから正確に移送する。 -/
theorem classicalPDivision_isAdicComplete (D : DeltaStructure p A) (a : σ → A) :
    IsAdicComplete (Ideal.span {(p : ClassicalDeltaDivisionCompletion D (p : A) a)})
      (ClassicalDeltaDivisionCompletion D (p : A) a) := by
  let B := DeltaDivisionTorsionQuotient D (p : A) a
  let I := deltaDivisionAdicIdeal D (p : A) a
  let C := ClassicalDeltaDivisionCompletion D (p : A) a
  have hc := AdicCompletion.isAdicComplete_self I (deltaDivisionAdicIdeal_fg D (p : A) a)
  have hmap : I.map (algebraMap B C) = Ideal.span {(p : C)} := by
    calc
      _ = (Ideal.span {(p : B)}).map (algebraMap B C) :=
        congrArg (fun J : Ideal B ↦ J.map (algebraMap B C))
          (deltaPDivisionAdicIdeal_eq_span_p D a)
      _ = Ideal.span {algebraMap B C (p : B)} := by rw [Ideal.map_span, Set.image_singleton]
      _ = _ := congrArg (fun c : C ↦ Ideal.span {c}) (map_natCast (algebraMap B C) p)
  exact hmap ▸ hc

/-- p正則な旧ねじれ除去商のp進完備化にも新しいpねじれは生じない。 -/
theorem classicalPDivision_p_mul_injective (D : DeltaStructure p A) (a : σ → A) :
    Function.Injective (fun x : ClassicalDeltaDivisionCompletion D (p : A) a ↦
      (p : ClassicalDeltaDivisionCompletion D (p : A) a) * x) := by
  let B := DeltaDivisionTorsionQuotient D (p : A) a
  have hpB : IsSMulRegular B (p : B) := deltaDivisionTorsionQuotient_p_mul_injective D a
  have aux (J : Ideal B) (hJ : J = Ideal.span {(p : B)}) :
      IsSMulRegular (AdicCompletion J B) (algebraMap B (AdicCompletion J B) (p : B)) := by
    subst J
    exact SerrePositivity.isSMulRegular_adicCompletion_span_singleton B (p : B) hpB
  have h := aux (deltaDivisionAdicIdeal D (p : A) a) (deltaPDivisionAdicIdeal_eq_span_p D a)
  let C := ClassicalDeltaDivisionCompletion D (p : A) a
  exact Eq.mp (congrArg (fun c : C ↦ IsSMulRegular C c) (map_natCast (algebraMap B C) p)) h

/-- この古典的候補自身の導来p完備性。p正則性を証明して既存比較を適用する。 -/
theorem classicalPDivision_isModuleComplete (D : DeltaStructure p A) (a : σ → A) :
    SerrePositivity.DerivedCompletion.IsModuleComplete
      (ClassicalDeltaDivisionCompletion D (p : A) a)
      (p : ClassicalDeltaDivisionCompletion D (p : A) a)
      (ModuleCat.of (ClassicalDeltaDivisionCompletion D (p : A) a)
        (ClassicalDeltaDivisionCompletion D (p : A) a)) :=
  (SerrePositivity.DerivedCompletion.isRingModuleComplete_iff_isAdicComplete_natCast
    _ p (classicalPDivision_p_mul_injective D a)).mpr (classicalPDivision_isAdicComplete D a)

/-- p除算変数の既存古典的完備化への標準像。 -/
def classicalPDivisionVariable (D : DeltaStructure p A) (a : σ → A) (s : σ) :
    ClassicalDeltaDivisionCompletion D (p : A) a :=
  algebraMap (DeltaDivisionTorsionQuotient D (p : A) a) _
    (Ideal.Quotient.mk _ (deltaAdjoinDivisionVariable D (p : A) a s))

/-- p除算変数の標準像とpとの積は指定元の像。 -/
theorem classicalPDivisionVariable_relation (D : DeltaStructure p A) (a : σ → A) (s : σ) :
    (p : ClassicalDeltaDivisionCompletion D (p : A) a) * classicalPDivisionVariable D a s =
      classicalDeltaDivisionMap D (p : A) a (a s) := by
  let q : DeltaAdjoinDivision D (p : A) a →+* DeltaDivisionTorsionQuotient D (p : A) a :=
    Ideal.Quotient.mk _
  let k := (algebraMap (DeltaDivisionTorsionQuotient D (p : A) a)
    (ClassicalDeltaDivisionCompletion D (p : A) a)).comp q
  have h := congrArg k (deltaAdjoinDivision_relation D (p : A) a s)
  simpa only [k, q, classicalPDivisionVariable, classicalDeltaDivisionMap,
    deltaDivisionTorsionMap, RingHom.comp_apply, map_mul, map_natCast] using h

/-- 具体的な古典的p除算候補ではpはJacobson根基に属する。 -/
theorem classicalPDivision_p_mem_jacobson (D : DeltaStructure p A) (a : σ → A) :
    (p : ClassicalDeltaDivisionCompletion D (p : A) a) ∈ Ideal.jacobson (⊥ : Ideal _) := by
  let B := DeltaDivisionTorsionQuotient D (p : A) a
  let I := deltaDivisionAdicIdeal D (p : A) a
  let C := ClassicalDeltaDivisionCompletion D (p : A) a
  let : IsAdicComplete (I.map (algebraMap B C)) C :=
    AdicCompletion.isAdicComplete_self I (deltaDivisionAdicIdeal_fg D (p : A) a)
  apply IsAdicComplete.le_jacobson_bot (I.map (algebraMap B C))
  have hp : (p : B) ∈ I := Ideal.subset_span (Set.mem_insert _ _)
  change (p : C) ∈ (I.map (algebraMap B C) : Ideal C)
  have hm := Ideal.mem_map_of_mem (algebraMap B C) hp
  exact Eq.mp (congrArg (fun c : C ↦ c ∈ (I.map (algebraMap B C) : Ideal C))
    (map_natCast (algebraMap B C) p)) hm

/-- 指定元がdistinguishedなら、古典的p除算候補内の具体的な除算変数像は単元。 -/
theorem classicalPDivisionVariable_isUnit (D : DeltaStructure p A) (a : σ → A) (s : σ)
    (ha : D.IsDistinguished (a s)) : IsUnit (classicalPDivisionVariable D a s) := by
  have hp := classicalPDivision_p_mem_jacobson D a
  apply (DeltaStructure.isDistinguished_factor (classicalDeltaDivisionStructure D (p : A) a)
    (p : ClassicalDeltaDivisionCompletion D (p : A) a) (classicalPDivisionVariable D a s)
    ?_ hp hp).2
  rw [classicalPDivisionVariable_relation]
  exact (classicalDeltaDivisionMap_isDeltaHom D (p : A) a).map_isDistinguished ha

/-- 原典Prop.3.13のφ(y)=p*u型の具体的な単元係数（古典的候補での結果）。 -/
theorem exists_classicalPDivision_unit_factor (D : DeltaStructure p A) (a : σ → A) (s : σ)
    (ha : D.IsDistinguished (a s)) :
    ∃ u : (ClassicalDeltaDivisionCompletion D (p : A) a)ˣ,
      (u : ClassicalDeltaDivisionCompletion D (p : A) a) = classicalPDivisionVariable D a s ∧
      classicalDeltaDivisionMap D (p : A) a (a s) = p * (u : _) := by
  obtain ⟨u, hu⟩ := classicalPDivisionVariable_isUnit D a s ha
  exact ⟨u, hu, by rw [hu]; exact (classicalPDivisionVariable_relation D a s).symm⟩

end SerrePositivity.BhattScholze
