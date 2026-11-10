module

public import SerrePositivity.AlgebraicGeometry.ChartBaseChange
public import SerrePositivity.AlgebraicGeometry.ChartRegularLift
public import SerrePositivity.AlgebraicGeometry.PureFreeStalkBaseChange

/-!
概要：ブローアップの標準チャート環は係数環の平坦底変換と可換。
方針：底変換したチャートでも中心の生成元が正則なので、チャートの普遍性で逆写像を作る。
規約：中心の底変換はイデアルの拡大で与える。
使われ方：基底の共通中心によるブローアップを étale チャートへ引き戻す。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open scoped TensorProduct

/--
概要：平坦な底変換後の標準チャート環は、元の標準チャート環の底変換と同型。
方針：元のチャートで正則かつ単項な中心が底変換でも正則かつ単項であることを使う。
規約：同型は元のチャートの写像と新しい基底の係数写像を保存する。
使われ方：Stacks 0814 で基底中心のブローアップを局所中心のブローアップと比較する。
-/
theorem exists_chartTensorEquiv_of_flat
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
    (I : Ideal R) (a : I) :
    let f := algebraMap R S
    let J := I.map f
    let a' := centerImageElement I J f le_rfl a
    let C := BlowupChartRing I a
    letI : Algebra R C := (chartBaseMap I a).toAlgebra
    ∃ e : (C ⊗[R] S) ≃+* BlowupChartRing J a',
      (∀ c : C, e (c ⊗ₜ[R] (1 : S)) = chartBaseChangeMap I J f le_rfl a c) ∧
      ∀ s : S, e ((1 : C) ⊗ₜ[R] s) = chartBaseMap J a' s := by
  let f := algebraMap R S
  let J := I.map f
  let a' := centerImageElement I J f le_rfl a
  let C := BlowupChartRing I a
  let D := BlowupChartRing J a'
  let : Algebra R C := (chartBaseMap I a).toAlgebra
  let : Algebra R D := ((chartBaseMap J a').comp f).toAlgebra
  let E := C ⊗[R] S
  let i := (Algebra.TensorProduct.includeRight : S →ₐ[R] E).toRingHom
  let k := algebraMap C E
  have hi : i.comp f = k.comp (chartBaseMap I a) := by
    ext r
    exact Algebra.TensorProduct.includeRight.commutes r
  have ha : i a'.1 = k (chartBaseMap I a a.1) := DFunLike.congr_fun hi a.1
  have hregC : k (chartBaseMap I a a.1) ∈ nonZeroDivisors E :=
    (algebraMap_isRegular_of_flat C E _
      (isRegular_iff_mem_nonZeroDivisors.mpr
        (chartBaseMap_mem_nonZeroDivisors I a))).mem_nonZeroDivisors
  have hreg : i a'.1 ∈ nonZeroDivisors E := ha.symm ▸ hregC
  have hJ : J.map i = Ideal.span {i a'.1} := by
    change (I.map f).map i = _
    rw [Ideal.map_map, hi, ← Ideal.map_map, chart_map_ideal_eq_span, Ideal.map_span,
      Set.image_singleton, ha]
  let g := chartRegularLift J i a' hreg hJ
  let t : C →ₐ[R] D :=
    { toRingHom := chartBaseChangeMap I J f le_rfl a
      commutes' := chartBaseChangeMap_base I J f le_rfl a }
  let v : S →ₐ[R] D :=
    { toRingHom := chartBaseMap J a'
      commutes' := fun _ => rfl }
  let F : E →ₐ[R] D := Algebra.TensorProduct.lift t v (fun _ _ => .all _ _)
  have hgS (s : S) : g (chartBaseMap J a' s) = i s := chartRegularLift_base J i a' hreg hJ s
  have hgC : g.comp t.toRingHom = k := by
    apply chart_hom_ext_of_regular I (k.comp (chartBaseMap I a)) a hregC
    · intro r
      rw [RingHom.comp_apply, show t.toRingHom (chartBaseMap I a r) =
        chartBaseMap J a' (f r) from chartBaseChangeMap_base I J f le_rfl a r, hgS]
      exact DFunLike.congr_fun hi r
    · intro r
      rfl
  have hF₁ : Function.LeftInverse g F := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul c s =>
      rw [Algebra.TensorProduct.lift_tmul, map_mul]
      change g (t c) * g (chartBaseMap J a' s) = _
      rw [hgS]
      change (g.comp t.toRingHom) c * i s = c ⊗ₜ[R] s
      rw [hgC]
      change (c ⊗ₜ[R] (1 : S)) * ((1 : C) ⊗ₜ[R] s) = _
      simp
    | add z w hz hw => simp [hz, hw]
  have hF₂ : F.toRingHom.comp g = RingHom.id D := by
    apply chart_hom_ext_of_regular J (chartBaseMap J a') a' (chartBaseMap_mem_nonZeroDivisors J a')
    · intro s
      rw [RingHom.comp_apply, hgS]
      change F ((1 : C) ⊗ₜ[R] s) = _
      rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
      rfl
    · intro s
      rfl
  let e := RingEquiv.ofBijective F.toRingHom
    ⟨hF₁.injective, fun d => ⟨g d, DFunLike.congr_fun hF₂ d⟩⟩
  refine ⟨e, ?_, ?_⟩
  · intro c
    change F (c ⊗ₜ[R] (1 : S)) = _
    rw [Algebra.TensorProduct.lift_tmul, map_one, mul_one]
    rfl
  · intro s
    change F ((1 : C) ⊗ₜ[R] s) = _
    rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
    rfl

end SerrePositivity.AlgebraicGeometry
