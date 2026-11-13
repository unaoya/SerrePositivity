module

public import SerrePositivity.BhattScholze.Prismatic.Envelopes.Envelope
public import SerrePositivity.BhattScholze.Delta.DividedPower.PDivision.PDivisionCompletion

/-!
# 結晶基底での完備 δ 除算と envelope

## 概要
生成元が p の基底 prism では、指定元の p 除算を添加して完備化した環が
それらの元と p で生成されるイデアルの prismatic envelope になる。

## 方針
基底上の prism 射が p の主イデアルを保つことと、完備 δ 除算の普遍性を使う。

## 規約
対象は向き付き prism。

## 使われ方
affine Čech–Alexander 模型の各項と結晶比較の橋。
-/

public noncomputable section

universe u

namespace SerrePositivity.BhattScholze.Prismatic

variable {p : ℕ} [Fact p.Prime] {A R : Type u} [CommRing A] [CommRing R]
    (P : OrientedPrism p A) (hP : P.generator = p)
    (D : DeltaStructure p R) (β : A →+* R) (hβ : P.deltaStructure.IsDeltaHom D β)
    {σ : Type u} (y : σ → R)

local notation "C" => ClassicalDeltaDivisionCompletion D (p : R) y
local notation "η" => classicalDeltaDivisionMap D (p : R) y

/-- p 除算環を生成元 p の向き付き prism として読む。 -/
def crystallineDivisionPrism : OrientedPrism p C := by
  letI := classicalPDivision_isAdicComplete D y
  exact OrientedPrism.crystalline (classicalDeltaDivisionStructure D (p : R) y)
    (classicalPDivision_p_mul_injective D y)

theorem crystallineDivisionPrism_generator : (crystallineDivisionPrism D y).generator = p := by
  simp [crystallineDivisionPrism]

theorem crystallineDivisionPrism_deltaStructure :
    (crystallineDivisionPrism D y).deltaStructure =
      classicalDeltaDivisionStructure D (p : R) y := by
  simp [crystallineDivisionPrism]

/-- 基底生成元と指定元で生成される envelope のイデアル。 -/
def crystallineDivisionIdeal : Ideal R := Ideal.span (insert (β P.generator) (Set.range y))

theorem crystallineDivisionIdeal_generator :
    β P.generator ∈ crystallineDivisionIdeal P β y :=
  Ideal.subset_span (Set.mem_insert _ _)

include hP in
set_option maxHeartbeats 700000 in
-- 二段階商と標準単位を含む型を、prism の普遍性の各条件と照合する。
/-- 完備 p 除算環は、結晶基底上で指定元の prismatic envelope になる。 -/
theorem crystallineDivision_isPrismaticEnvelope :
    IsPrismaticEnvelope P D β hβ (crystallineDivisionIdeal P β y)
      (crystallineDivisionIdeal_generator P β y) (crystallineDivisionPrism D y) η := by
  let Q := crystallineDivisionPrism D y
  have hQ : Q.ideal = Ideal.span {(p : C)} :=
    congrArg (fun d : C => Ideal.span {d}) (crystallineDivisionPrism_generator D y)
  have hη : η (β P.generator) = (p : C) :=
    (congrArg ((η).comp β) hP).trans (map_natCast ((η).comp β) p)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [crystallineDivisionPrism_deltaStructure]
    exact classicalDeltaDivisionMap_isDeltaHom D (p : R) y
  · change Ideal.span {P.generator} ≤ Q.ideal.comap ((η).comp β)
    rw [Ideal.span_singleton_le_iff_mem]
    change η (β P.generator) ∈ Q.ideal
    rw [hη, hQ]
    exact Ideal.subset_span rfl
  · rw [hQ, hη]
  · rw [Ideal.map_le_iff_le_comap, crystallineDivisionIdeal, Ideal.span_le]
    rintro x (hx | ⟨s, rfl⟩)
    · change η x ∈ Q.ideal
      rw [show x = β P.generator from hx, hη, hQ]
      exact Ideal.subset_span rfl
    · change η (y s) ∈ Q.ideal
      rw [hQ, Ideal.mem_span_singleton]
      exact ⟨classicalPDivisionVariable D y s, (classicalPDivisionVariable_relation D y s).symm⟩
  · intro E _ Q' f hf hbase hmap
    let f₀ : OrientedPrism.Hom P Q' := ⟨f.comp β, hf.comp hβ, hbase⟩
    have hI : Ideal.span {(p : E)} = Q'.ideal := by
      have h := f₀.map_ideal_eq
      change (Ideal.span {P.generator}).map f₀.toRingHom = _ at h
      rw [hP, Ideal.map_span, Set.image_singleton, map_natCast] at h
      exact h
    have hreg : Function.Injective (fun x : E => (p : E) * x) := by
      have hm : Q'.generator ∈ Ideal.span {(p : E)} := by
        rw [hI]
        exact Ideal.subset_span rfl
      obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp hm
      intro x y hxy
      change (p : E) * x = (p : E) * y at hxy
      apply Q'.generator_regular
      change Q'.generator * x = Q'.generator * y
      rw [hb, mul_right_comm _ b x, mul_right_comm _ b y, hxy]
    have hy (s : σ) : f (p : R) ∣ f (y s) := by
      rw [map_natCast]
      apply Ideal.mem_span_singleton.mp
      rw [hI]
      apply hmap (Ideal.mem_map_of_mem _ _)
      exact Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_range_self s))
    let := Q'.isAdicComplete_p_of_regular hreg
    rw [crystallineDivisionPrism_deltaStructure]
    exact existsUnique_classicalDeltaDivisionHom D Q'.deltaStructure (p : R) y f hf
      (by simpa only [map_natCast] using hreg) hy (Ideal.span {(p : E)})
      (Ideal.subset_span rfl) (by rw [map_natCast]; exact Ideal.subset_span rfl)

end SerrePositivity.BhattScholze.Prismatic
