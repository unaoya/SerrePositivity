module

public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionBoundedChains
public import Mathlib.Data.Set.Finite.Lattice

/-!
概要：有限順序の幅を固定した非退化な実原子は、全次数と四Homを合わせても有限個。
方針：実頂点の重みの境界と次元の境界から、有限な対象・射の実関手を有限和へ入れる。
規約：原典の文字列の幅との全比較は別に行う。元の全実関手そのものの有限性。
使われ方：Riehl–Verity Proposition 4.2.15の実filtrationの各幅の有限性、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の有限の実範囲。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：固定次数・固定幅の実原子は有限個。
方針：全実頂点の重みの上限で、既に有限と示した全実関手へ単射で入れる。
規約：非退化性は不要な強い固定次数の有限性。使われ方：Riehl–Verity §4.2の各幅。 -/
lemma walkingAdjunctionAtomicWidth_finite (n : ℕ) (X Y : WalkingAdjunctionPoint) (w : ℕ) :
    Finite {H : ComposableArrows (walkingAdjunctionHom X Y) n //
      WalkingAdjunctionLevelIsAtomic (X := ⟨X⟩) (Y := ⟨Y⟩) H ∧
        walkingAdjunctionOrdinalWidth H = w} := by
  let := walkingAdjunctionBoundedChains_finite n X Y w
  let encode : {H : ComposableArrows (walkingAdjunctionHom X Y) n //
      WalkingAdjunctionLevelIsAtomic (X := ⟨X⟩) (Y := ⟨Y⟩) H ∧
        walkingAdjunctionOrdinalWidth H = w} →
      {H : ComposableArrows (walkingAdjunctionHom X Y) n //
        ∀ i, walkingAdjunctionWeight X Y (H.obj i) ≤ w} := fun H => ⟨H.val, fun i => by
    have hi := walkingAdjunctionOrdinalWidth_vertex_weight_le H.val H.property.1 i
    rw [H.property.2] at hi
    exact hi⟩
  apply Finite.of_injective encode
  intro H K h
  apply Subtype.ext
  exact congrArg (fun b : {H : ComposableArrows (walkingAdjunctionHom X Y) n //
    ∀ i, walkingAdjunctionWeight X Y (H.obj i) ≤ w} => b.val) h

/-- 概要：有限順序の幅を固定した非退化な実原子は、全次数を合わせても有限個。
方針：非退化原子の次元を幅未満へ入れ、有限な実関手の有限和の像を取る。
規約：元の全次数の全実関手を含む。使われ方：Riehl–Verity Proposition 4.2.15の実有限性。 -/
lemma walkingAdjunctionAtomicWidth_set_finite (X Y : WalkingAdjunctionPoint) (w : ℕ) :
    {p : Σ n : ℕ, ComposableArrows (walkingAdjunctionHom X Y) n |
      WalkingAdjunctionLevelIsAtomic (X := ⟨X⟩) (Y := ⟨Y⟩) p.2 ∧
        ULift.up p.2 ∈ (WalkingAdjunctionHomShape.{u} X Y).nonDegenerate p.1 ∧
          walkingAdjunctionOrdinalWidth p.2 = w}.Finite := by
  let (n : Fin w) : Finite {H : ComposableArrows (walkingAdjunctionHom X Y) n.val //
      WalkingAdjunctionLevelIsAtomic (X := ⟨X⟩) (Y := ⟨Y⟩) H ∧
        ULift.up H ∈ (WalkingAdjunctionHomShape.{u} X Y).nonDegenerate n.val ∧
          walkingAdjunctionOrdinalWidth H = w} := by
    let := walkingAdjunctionAtomicWidth_finite n.val X Y w
    apply Finite.of_injective (fun H =>
      (⟨H.val, H.property.1, H.property.2.2⟩ :
        {H : ComposableArrows (walkingAdjunctionHom X Y) n.val //
          WalkingAdjunctionLevelIsAtomic (X := ⟨X⟩) (Y := ⟨Y⟩) H ∧
            walkingAdjunctionOrdinalWidth H = w}))
    intro H K h
    apply Subtype.ext
    exact congrArg (fun b : {H : ComposableArrows (walkingAdjunctionHom X Y) n.val //
      WalkingAdjunctionLevelIsAtomic (X := ⟨X⟩) (Y := ⟨Y⟩) H ∧
        walkingAdjunctionOrdinalWidth H = w} => b.val) h
  let B := Σ n : Fin w, {H : ComposableArrows (walkingAdjunctionHom X Y) n.val //
    WalkingAdjunctionLevelIsAtomic (X := ⟨X⟩) (Y := ⟨Y⟩) H ∧
      ULift.up H ∈ (WalkingAdjunctionHomShape.{u} X Y).nonDegenerate n.val ∧
        walkingAdjunctionOrdinalWidth H = w}
  let f : B → (Σ n : ℕ, ComposableArrows (walkingAdjunctionHom X Y) n) :=
    fun b => ⟨b.1.val, b.2.val⟩
  apply (Set.finite_range f).subset
  rintro ⟨n, H⟩ ⟨ha, hnd, hw⟩
  have hn := walkingAdjunctionOrdinalWidth_dimension_lt H ha hnd
  rw [hw] at hn
  exact ⟨⟨⟨n, hn⟩, ⟨H, ha, hnd, hw⟩⟩, rfl⟩

/-- 概要：実全随伴の二対象の全体は有限。
方針：二対象をBoolへ単射で入れる。規約：元の二対象そのもの。
使われ方：Riehl–Verity §4.2の四Homを合わせた各幅の有限性。 -/
lemma walkingAdjunctionPoint_finite : Finite WalkingAdjunctionPoint := by
  apply Finite.of_injective (fun X : WalkingAdjunctionPoint =>
    match X with | .plus => true | .minus => false)
  intro X Y h
  cases X <;> cases Y <;> simp_all

/-- 概要：有限順序の幅を固定した全非退化実原子は、四Homと全次数を合わせても有限個。
方針：固定した両端での有限性を、二対象の有限な依存和へ入れる。
規約：元の実全関手の有限集合。使われ方：Riehl–Verity Proposition 4.2.15の各幅。 -/
lemma walkingAdjunctionAllAtomicWidth_set_finite (w : ℕ) :
    {p : Σ X : WalkingAdjunctionPoint, Σ Y : WalkingAdjunctionPoint,
        Σ n : ℕ, ComposableArrows (walkingAdjunctionHom X Y) n |
      WalkingAdjunctionLevelIsAtomic (X := ⟨p.1⟩) (Y := ⟨p.2.1⟩) p.2.2.2 ∧
        ULift.up p.2.2.2 ∈
          (WalkingAdjunctionHomShape.{u} p.1 p.2.1).nonDegenerate p.2.2.1 ∧
            walkingAdjunctionOrdinalWidth p.2.2.2 = w}.Finite := by
  let := walkingAdjunctionPoint_finite
  have h := (Set.toFinite (Set.univ : Set WalkingAdjunctionPoint)).sigma (fun X _ =>
    (Set.toFinite (Set.univ : Set WalkingAdjunctionPoint)).sigma (fun Y _ =>
      walkingAdjunctionAtomicWidth_set_finite.{u} X Y w))
  simpa only [Set.sigma, Set.mem_univ, Set.mem_ofPred_eq, true_and] using h

/-- 概要：有限順序の幅が指定値以下の全非退化実原子は有限個。
方針：指定値以下の自然数の有限個の各幅の集合へ入れる。
規約：四Hom・全次数の元の実全関手。使われ方：Riehl–Verity §4.2の実有限な初期範囲。 -/
lemma walkingAdjunctionAllAtomicWidth_le_set_finite (w : ℕ) :
    {p : Σ X : WalkingAdjunctionPoint, Σ Y : WalkingAdjunctionPoint,
        Σ n : ℕ, ComposableArrows (walkingAdjunctionHom X Y) n |
      WalkingAdjunctionLevelIsAtomic (X := ⟨p.1⟩) (Y := ⟨p.2.1⟩) p.2.2.2 ∧
        ULift.up p.2.2.2 ∈
          (WalkingAdjunctionHomShape.{u} p.1 p.2.1).nonDegenerate p.2.2.1 ∧
            walkingAdjunctionOrdinalWidth p.2.2.2 ≤ w}.Finite := by
  have h := Set.finite_iUnion (fun k : Fin (w + 1) =>
    walkingAdjunctionAllAtomicWidth_set_finite.{u} k.val)
  apply h.subset
  intro p hp
  apply Set.mem_iUnion.mpr
  exact ⟨⟨walkingAdjunctionOrdinalWidth p.2.2.2, Nat.lt_succ_of_le hp.2.2⟩,
    hp.1, hp.2.1, rfl⟩

end SerrePositivity.InfinityCategories.HA.Monads
