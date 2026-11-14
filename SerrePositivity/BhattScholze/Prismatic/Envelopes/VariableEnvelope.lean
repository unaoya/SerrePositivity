module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.BhattScholze.Prismatic.Envelopes.CompletedFreeDelta
public import SerrePositivity.BhattScholze.Prism.Basic.Rigidity

/-!
# 変数に沿う prismatic envelope の普遍性

## 概要
選んだ初期変数を基底生成元で割る置換が、完備自由 δ 環の中で envelope を与える。

## 方針
標的の prism イデアルは基底生成元の像で生成され、その像は正則である。
選んだ変数の像を一意に割って完備自由 δ 環の普遍性を使う。

## 規約
候補環における基底生成元の正則性を仮定する。

## 使われ方
affine Čech–Alexander 模型の次数ごとの envelope。
-/

public section
noncomputable section

universe u

open CategoryTheory
open SerrePositivity.DerivedCompletion

namespace SerrePositivity.BhattScholze.Prismatic

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable (P : OrientedPrism p A) (S : Type u) (Z : Set S)

local notation "C" => completedFreeDelta P S
local notation "DC" => completedFreeDeltaStructure P S
local notation "ι" => completedFreeDeltaBase P S
local notation "X" => completedFreeDeltaVariable P S
local notation "d" => OrientedPrism.generator P
local notation "c" => completedFreeDeltaBase P S (OrientedPrism.generator P)

private noncomputable def scaleCoordinate {R : Type u} [CommRing R] (a : R) (s : S)
    (x : R) : R := by
  classical
  exact if s ∈ Z then a * x else x

private theorem scaleCoordinate_natural {R T : Type u} [CommRing R] [CommRing T]
    (f : R →+* T) (a : R) (s : S) (x : R) :
    f (scaleCoordinate S Z a s x) = scaleCoordinate S Z (f a) s (f x) := by
  classical
  by_cases hs : s ∈ Z <;> simp [scaleCoordinate, hs]

private theorem scaleCoordinate_injective {R : Type u} [CommRing R] {a : R}
    (ha : Function.Injective (a * ·)) (s : S) :
    Function.Injective (scaleCoordinate S Z a s) := by
  classical
  intro x y h
  by_cases hs : s ∈ Z
  · apply ha
    simpa only [scaleCoordinate, ite_eq_left hs] using h
  · simpa only [scaleCoordinate, ite_eq_right hs] using h

private theorem exists_variableEnvelopeSubstitution :
    ∃! η : C →+* C, (DC).IsDeltaHom DC η ∧ η.comp ι = ι ∧
      ∀ s, η (X s) = scaleCoordinate S Z c s (X s) :=
  existsUnique_completedFreeDeltaHom P S DC ι (completedFreeDeltaBase_isDeltaHom P S)
    (completedFreeDelta_complete_p P S) (completedFreeDelta_complete_generator P S)
    (fun s => scaleCoordinate S Z c s (X s))

/-- 選んだ初期変数を基底生成元と変数の積へ送る δ 射。 -/
def variableEnvelopeSubstitution : C →+* C :=
  (exists_variableEnvelopeSubstitution P S Z).choose

private theorem variableEnvelopeSubstitution_spec :
    let η := variableEnvelopeSubstitution P S Z
    (DC).IsDeltaHom DC η ∧ η.comp ι = ι ∧ ∀ s, η (X s) = scaleCoordinate S Z c s (X s) :=
  (exists_variableEnvelopeSubstitution P S Z).choose_spec.1

/-- 変数の置換は基底射を保つ。 -/
theorem variableEnvelopeSubstitution_base :
    (variableEnvelopeSubstitution P S Z).comp ι = ι :=
  (variableEnvelopeSubstitution_spec P S Z).2.1

/-- 基底生成元の像が正則なら、完備自由 δ 環は向き付き prism。 -/
def completedFreeDeltaPrism (hreg : Function.Injective (c * ·)) : OrientedPrism p C :=
  OrientedPrism.ofDistinguished DC c
    ((completedFreeDeltaBase_isDeltaHom P S).map_isDistinguished P.isDistinguished_generator)
    hreg (completedFreeDelta_complete_p P S) (completedFreeDelta_complete_generator P S)

/-- 候補 prism のイデアルは基底生成元の像で生成される。 -/
theorem completedFreeDeltaPrism_ideal (hreg : Function.Injective (c * ·)) :
    (completedFreeDeltaPrism P S hreg).ideal = Ideal.span {c} := by
  unfold completedFreeDeltaPrism
  rfl

private theorem variableEnvelopeSubstitution_lift
    {D : Type u} [CommRing D] (QD : OrientedPrism p D) (f : OrientedPrism.Hom P QD)
    (g : C →+* D) (hg : (DC).IsDeltaHom QD.deltaStructure g)
    (hb : g.comp ι = f.toRingHom)
    (hZ : ∀ s ∈ Z, g (X s) ∈ QD.ideal) :
    ∃! h : C →+* D, (DC).IsDeltaHom QD.deltaStructure h ∧
      h.comp (variableEnvelopeSubstitution P S Z) = g := by
  let η := variableEnvelopeSubstitution P S Z
  have hη := variableEnvelopeSubstitution_spec P S Z
  have hpre (s : S) : ∃ x : D, scaleCoordinate S Z (f.toRingHom d) s x = g (X s) := by
    classical
    by_cases hs : s ∈ Z
    · have hx := hZ s hs
      rw [← f.span_map_generator, Ideal.mem_span_singleton] at hx
      obtain ⟨x, hx⟩ := hx
      exact ⟨x, by simpa [scaleCoordinate, hs] using hx.symm⟩
    · exact ⟨g (X s), by simp [scaleCoordinate, hs]⟩
  let a (s : S) := (hpre s).choose
  have ha (s : S) : scaleCoordinate S Z (f.toRingHom d) s (a s) = g (X s) :=
    (hpre s).choose_spec
  obtain ⟨h, hh, hu⟩ := existsUnique_completedFreeDeltaHom P S QD.deltaStructure
    f.toRingHom f.map_delta QD.complete_p f.isModuleComplete_map_generator a
  have hhη : h.comp η = g := by
    refine completedFreeDeltaHom_ext P S QD.deltaStructure f.toRingHom f.map_delta
      QD.complete_p f.isModuleComplete_map_generator (hh.1.comp hη.1) hg ?_ hb ?_
    · rw [RingHom.comp_assoc, hη.2.1, hh.2.1]
    · intro s
      change h (η (X s)) = g (X s)
      rw [hη.2.2, scaleCoordinate_natural, (show h (ι d) = f.toRingHom d from RingHom.congr_fun hh.2.1 d), hh.2.2, ha]
  refine ⟨h, ⟨hh.1, hhη⟩, ?_⟩
  intro l hl
  have hlb : l.comp ι = f.toRingHom := by
    rw [← hη.2.1, ← RingHom.comp_assoc, hl.2, hb]
  apply hu
  refine ⟨hl.1, hlb, fun s => ?_⟩
  apply scaleCoordinate_injective S Z f.map_generator_mul_injective s
  rw [ha]
  have hlX : l (η (X s)) = g (X s) := RingHom.congr_fun hl.2 (X s)
  rw [hη.2.2, scaleCoordinate_natural, (show l (ι d) = f.toRingHom d from RingHom.congr_fun hlb d)] at hlX
  exact hlX

/-- 概要：完備自由 δ 環上で選んだ初期変数を基底生成元で割る envelope
（BS 著者版 Example 3.14 の、候補環の生成元が正則な場合）。
方針：標的での一意な除法と完備自由 δ 環の普遍性を使う。
規約：候補の生成元は基底生成元の像。
使われ方：affine Čech–Alexander 模型の各項。 -/
theorem isPrismaticEnvelope_variableSubstitution (hreg : Function.Injective (c * ·)) :
    IsPrismaticEnvelope P DC ι (completedFreeDeltaBase_isDeltaHom P S)
      (variableIdeal P S Z) (Ideal.subset_span (Set.mem_insert _ _))
      (completedFreeDeltaPrism P S hreg) (variableEnvelopeSubstitution P S Z) := by
  classical
  let η := variableEnvelopeSubstitution P S Z
  have hη := variableEnvelopeSubstitution_spec P S Z
  refine ⟨hη.1, ?_, ?_, ?_, ?_⟩
  · rw [hη.2.1, OrientedPrism.ideal, Ideal.span_le]
    intro x hx
    obtain rfl := Set.mem_singleton_iff.mp hx
    exact Ideal.subset_span rfl
  · change Ideal.span {c} = Ideal.span {η (ι d)}
    rw [(show η (ι d) = ι d from RingHom.congr_fun hη.2.1 d)]
  · rw [Ideal.map_le_iff_le_comap, variableIdeal, Ideal.span_le]
    intro x hx
    change η x ∈ Ideal.span {c}
    rcases hx with h | ⟨s, rfl⟩
    · rw [h, (show η (ι d) = ι d from RingHom.congr_fun hη.2.1 d)]
      exact Ideal.subset_span rfl
    · change η (X s) ∈ Ideal.span {c}
      rw [hη.2.2, scaleCoordinate, ite_eq_left s.property, Ideal.mem_span_singleton]
      exact dvd_mul_right _ _
  · intro D _ QD g hg hb hI
    let f : OrientedPrism.Hom P QD :=
      ⟨g.comp ι, hg.comp (completedFreeDeltaBase_isDeltaHom P S), hb⟩
    refine variableEnvelopeSubstitution_lift P S Z QD f g hg rfl fun s hs => ?_
    exact hI (Ideal.mem_map_of_mem g
      (Ideal.subset_span (Set.mem_insert_of_mem _ ⟨⟨s, hs⟩, rfl⟩)))

end SerrePositivity.BhattScholze.Prismatic

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Ex 3.14" (partial := special) "自由変数（候補環の生成元が正則）の envelope。一般の滑らかな B₀ → R は未 ／ 11-10 更新"] _root_.SerrePositivity.BhattScholze.Prismatic.isPrismaticEnvelope_variableSubstitution
