module

public import SerrePositivity.BhattScholze.Prismatic.Envelopes.CompletedFreeDeltaFlat
public import SerrePositivity.BhattScholze.Delta.Division.Source
public import SerrePositivity.BhattScholze.Semiperfectoid.Discrete.DiscretePrism

/-!
# 未完備自由源からの変数包絡

## 概要
自由 δ 源の初期変数を d 倍の自由変数へ送る射は、完備自由 δ 環を包絡にする。

## 方針
標的で一意に除算し、完備自由 δ 環の普遍性で延長する。

## 規約
BS 著者版 Example 7.9 の普遍変数の場合。源の完備化は後で比較する。

## 使われ方
一般の分類射に沿う完備通常テンソル積による lci 包絡。
-/

public noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.BhattScholze.Prismatic

open _root_.SerrePositivity.DerivedCompletion

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable (P : OrientedPrism p A) (S : Type u)

local notation "U" => RelativeFreeDeltaRing (R := A) S
local notation "D" => relativeFreeDeltaStructure S P.deltaStructure
local notation "C" => (MvPolynomial.C : A →+* U)
local notation "d" => P.generator
local notation "H" => completedFreeDelta P S
local notation "ι" => completedFreeDeltaBase P S
local notation "Y" => completedFreeDeltaVariable P S
local notation "c" => ι d

/-- 概要：未完備の自由変数を、完備環の d 倍の自由変数へ送る射。
方針：自由 δ 環の置換に標準完備化射を合成する。
規約：BS 著者版 Example 7.9 の普遍分類源。
使われ方：源を未完備にした普遍変数包絡。 -/
@[expose] def _root_.SerrePositivity.BhattScholze.Semiperfectoid.rawVariableEnvelopeMap : U →+* H :=
  (pdCompletionUnit U p (C d)).comp (_root_.SerrePositivity.BhattScholze.deltaDivisionSourceMap P.deltaStructure d)

/-- 概要：未完備変数包絡の射は係数上で標準基底射。
方針：自由 δ 置換が係数を固定することを使う。
規約：BS 著者版 Example 7.9。
使われ方：分類射の基底条件。 -/
theorem _root_.SerrePositivity.BhattScholze.Semiperfectoid.rawVariableEnvelopeMap_C (a : A) :
    _root_.SerrePositivity.BhattScholze.Semiperfectoid.rawVariableEnvelopeMap P S (C a) = ι a := by
  change pdCompletionUnit U p (C d) (_root_.SerrePositivity.BhattScholze.deltaDivisionSourceMap P.deltaStructure d (C a)) = _
  rw [_root_.SerrePositivity.BhattScholze.deltaDivisionSourceMap_C]
  rfl

/-- 概要：未完備の初期変数の像は d と対応する自由変数の積。
方針：自由 δ 置換の初期座標公式を完備化で写す。
規約：BS 著者版 Example 7.9 の f/d 座標。
使われ方：包絡の持ち上げと剰余の完全平坦性。 -/
theorem _root_.SerrePositivity.BhattScholze.Semiperfectoid.rawVariableEnvelopeMap_X (s : S) :
    _root_.SerrePositivity.BhattScholze.Semiperfectoid.rawVariableEnvelopeMap P S (MvPolynomial.X (s, 0)) = c * Y s := by
  let := pdCompletionCommRing U p (C d)
  change pdCompletionUnit U p (C d)
    (_root_.SerrePositivity.BhattScholze.deltaDivisionSourceMap P.deltaStructure d (MvPolynomial.X (s, 0))) = _
  rw [_root_.SerrePositivity.BhattScholze.deltaDivisionSourceMap_X, Function.iterate_zero_apply, map_mul]
  rfl

/-- 概要：未完備自由源の変数イデアルの包絡は、既存の完備自由 δ prism。
方針：標的 prism で初期変数を d で一意に割り、完備自由性を適用する。
規約：BS 著者版 Example 7.9。候補環の生成元の正則性を仮定する。
使われ方：未完備の分類源を使った一般の正則列の包絡。 -/
theorem _root_.SerrePositivity.BhattScholze.Semiperfectoid.isPrismaticEnvelope_rawVariableMap (hreg : Function.Injective (c * ·)) :
    ∃ Q₀ : _root_.SerrePositivity.BhattScholze.OrientedPrism p H, Q₀.generator = c ∧
    _root_.SerrePositivity.BhattScholze.Prismatic.IsPrismaticEnvelope P D C (_root_.SerrePositivity.BhattScholze.relativeFreeDeltaStructure_C_isDeltaHom S P.deltaStructure)
      (Ideal.span {C d} ⊔ Ideal.span (Set.range fun s : S => MvPolynomial.X (s, 0)))
      ((show Ideal.span {C d} ≤ _ from le_sup_left) (Ideal.subset_span (Set.mem_singleton _)))
      Q₀ (_root_.SerrePositivity.BhattScholze.Semiperfectoid.rawVariableEnvelopeMap P S) := by
  let := pdCompletionCommRing U p (C d)
  have hrc : IsRegular c := ⟨hreg, fun x y h => hreg (by simpa only [mul_comm] using h)⟩
  let Q₀ := P.ofDiscreteDelta (_root_.SerrePositivity.BhattScholze.Prismatic.completedFreeDeltaStructure P S) ι
    (_root_.SerrePositivity.BhattScholze.Prismatic.completedFreeDeltaBase_isDeltaHom P S) hrc
    (_root_.SerrePositivity.BhattScholze.Prismatic.completedFreeDelta_complete_p P S) (_root_.SerrePositivity.BhattScholze.Prismatic.completedFreeDelta_complete_generator P S)
  let η := _root_.SerrePositivity.BhattScholze.Semiperfectoid.rawVariableEnvelopeMap P S
  have hη : (D).IsDeltaHom (_root_.SerrePositivity.BhattScholze.Prismatic.completedFreeDeltaStructure P S) η :=
    (_root_.SerrePositivity.BhattScholze.pdCompletionUnit_isDeltaHom D (C d)).comp
      (_root_.SerrePositivity.BhattScholze.deltaDivisionSourceMap_isDeltaHom P.deltaStructure d)
  have hηC : η.comp C = ι := RingHom.ext (_root_.SerrePositivity.BhattScholze.Semiperfectoid.rawVariableEnvelopeMap_C P S)
  refine ⟨Q₀, rfl, hη, ?_, ?_, ?_, ?_⟩
  · rw [hηC]
    exact (P.toDiscreteDelta (_root_.SerrePositivity.BhattScholze.Prismatic.completedFreeDeltaStructure P S) ι
      (_root_.SerrePositivity.BhattScholze.Prismatic.completedFreeDeltaBase_isDeltaHom P S) hrc
      (_root_.SerrePositivity.BhattScholze.Prismatic.completedFreeDelta_complete_p P S) (_root_.SerrePositivity.BhattScholze.Prismatic.completedFreeDelta_complete_generator P S)).ideal_le
  · change Ideal.span {c} = Ideal.span {η (C d)}
    rw [_root_.SerrePositivity.BhattScholze.Semiperfectoid.rawVariableEnvelopeMap_C]
  · apply Ideal.map_le_iff_le_comap.mpr
    apply sup_le
    · apply (Ideal.comap η _).span_singleton_le_iff_mem.mpr
      change η (C d) ∈ Ideal.span {c}
      rw [_root_.SerrePositivity.BhattScholze.Semiperfectoid.rawVariableEnvelopeMap_C]
      exact Ideal.subset_span (Set.mem_singleton _)
    · apply Ideal.span_le.mpr
      rintro _ ⟨s, rfl⟩
      change η (MvPolynomial.X (s, 0)) ∈ Ideal.span {c}
      rw [_root_.SerrePositivity.BhattScholze.Semiperfectoid.rawVariableEnvelopeMap_X]
      rw [Ideal.mem_span_singleton]
      exact dvd_mul_right _ _
  · intro T _ Q v hv hb hJ
    let f : _root_.SerrePositivity.BhattScholze.OrientedPrism.Hom P Q :=
      ⟨v.comp C, hv.comp (_root_.SerrePositivity.BhattScholze.relativeFreeDeltaStructure_C_isDeltaHom S P.deltaStructure), hb⟩
    have hpre (s : S) : ∃ a : T, f.toRingHom d * a = v (MvPolynomial.X (s, 0)) := by
      have hx : v (MvPolynomial.X (s, 0)) ∈ Q.ideal :=
        hJ (Ideal.mem_map_of_mem v ((show Ideal.span (Set.range fun s : S =>
          MvPolynomial.X (s, 0)) ≤ _ from le_sup_right)
            (Ideal.subset_span (Set.mem_range_self s))))
      rw [← f.span_map_generator, Ideal.mem_span_singleton] at hx
      obtain ⟨a, ha⟩ := hx
      exact ⟨a, ha.symm⟩
    let a (s : S) := (hpre s).choose
    have ha (s : S) := (hpre s).choose_spec
    obtain ⟨k, hk, hu⟩ := _root_.SerrePositivity.BhattScholze.Prismatic.existsUnique_completedFreeDeltaHom P S Q.deltaStructure
      f.toRingHom f.map_delta Q.complete_p f.isModuleComplete_map_generator a
    have hkη : k.comp η = v := by
      obtain ⟨w, _, hw⟩ := _root_.SerrePositivity.BhattScholze.existsUnique_relativeFreeDeltaHom P.deltaStructure Q.deltaStructure
        f.toRingHom f.map_delta (fun s : S => v (MvPolynomial.X (s, 0)))
      apply (hw _ ⟨hk.1.comp hη, ?_, ?_⟩).trans
        (hw v ⟨hv, rfl, fun _ => rfl⟩).symm
      · rw [RingHom.comp_assoc, hηC, hk.2.1]
      · intro s
        change k (η (MvPolynomial.X (s, 0))) = _
        rw [_root_.SerrePositivity.BhattScholze.Semiperfectoid.rawVariableEnvelopeMap_X, map_mul,
          show k c = f.toRingHom d from RingHom.congr_fun hk.2.1 d, hk.2.2, ha]
    refine ⟨k, ⟨hk.1, hkη⟩, ?_⟩
    intro l hl
    have hlC : l.comp ι = f.toRingHom := by
      rw [← hηC, ← RingHom.comp_assoc, hl.2]
    apply hu
    refine ⟨hl.1, hlC, fun s => ?_⟩
    apply f.map_generator_mul_injective
    change f.toRingHom d * l (Y s) = f.toRingHom d * a s
    rw [show f.toRingHom d * a s = v (MvPolynomial.X (s, 0)) from ha s]
    have hx := RingHom.congr_fun hl.2 (MvPolynomial.X (s, 0))
    change l (η (MvPolynomial.X (s, 0))) = v (MvPolynomial.X (s, 0)) at hx
    rw [_root_.SerrePositivity.BhattScholze.Semiperfectoid.rawVariableEnvelopeMap_X, map_mul,
      show l c = f.toRingHom d from RingHom.congr_fun hlC d] at hx
    exact hx

end SerrePositivity.BhattScholze.Prismatic
