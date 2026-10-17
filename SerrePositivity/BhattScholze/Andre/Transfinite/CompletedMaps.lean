module

public import SerrePositivity.BhattScholze.Andre.Transfinite.BoundedCompletion
public import SerrePositivity.BhattScholze.Andre.Transfinite.Composition
public import SerrePositivity.BhattScholze.Andre.Transfinite.ResidueTensorColimit
public import SerrePositivity.BhattScholze.Andre.Transfinite.TorsionBound
open SerrePositivity SerrePositivity.BhattScholze.Andre.Transfinite
@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre.Transfinite
/-- ## 概要
p 完全忠実平坦な写像の終域の p 冪ねじれが有界なら、その終域の通常 p 進完備化への合成も p 完全忠実平坦である。
BS Thm 7.14（著者版 p.61）の極限段の標準射を扱う。

## 方針
有界ねじれによる完備化の完全忠実平坦性を、元の写像の完全忠実平坦性と合成する。

## 規約
環と添字は Type u とし、標準段射・標準完備化射そのものを用いる。
p 正則性・Noether 性・遷移射の単射性を要求しない。

## 使われ方
超限反復の極限段で、初段からの完全忠実平坦性を維持する。
-/
theorem isCompletelyFaithfullyFlat_adicCompletion_comp {R T : Type u} [CommRing R] [CommRing T]
    (p : ℕ) (φ : R →+* T)
    (hφ : letI := φ.toAlgebra; IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) T)
    (hbound : ∃ N : ℕ, ∀ n : ℕ, ∀ x : T,
      (p : T) ^ n * x = 0 → (p : T) ^ N * x = 0) :
    letI := ((algebraMap T (AdicCompletion (Ideal.span {(p : T)}) T)).comp φ).toAlgebra
    IsCompletelyFaithfullyFlat (Ideal.span {(p : R)})
      (AdicCompletion (Ideal.span {(p : T)}) T) := by
  apply isCompletelyFaithfullyFlat_natCast_comp φ
    (algebraMap T (AdicCompletion (Ideal.span {(p : T)}) T)) p hφ
  exact isCompletelyFaithfullyFlat_adicCompletion_of_bounded_torsion T (p : T) hbound


/-- ## 概要
最小段から各段への写像が p 完全忠実平坦なら、環余極限への標準写像も p 完全忠実平坦である。
BS Thm 7.14（著者版 p.61）の極限段の標準射を扱う。

## 方針
最小段を共通係数環として各遷移射を代数射にする。非交和余極限との比較を
元の最小段の係数作用に関して線形化し、代数余極限の既証定理を移す。

## 規約
環と添字は Type u とし、標準段射・標準完備化射そのものを用いる。
p 正則性・Noether 性・遷移射の単射性を要求しない。

## 使われ方
超限反復の極限段で、初段からの完全忠実平坦性を維持する。
-/
theorem isCompletelyFaithfullyFlat_ringDirectLimit_of_orderBot
    {p : ℕ} {ι : Type u} [Preorder ι] [OrderBot ι] [IsDirectedOrder ι]
    (R : ι → Type u) [∀ i, CommRing (R i)]
    (f : ∀ i j, i ≤ j → R i →+* R j)
    [DirectedSystem R (fun i j h ↦ f i j h)]
    (hflat : ∀ i, letI := (f ⊥ i bot_le).toAlgebra;
      IsCompletelyFaithfullyFlat (Ideal.span {(p : R ⊥)}) (R i)) :
    letI := (Ring.DirectLimit.of R (fun i j h ↦ f i j h) ⊥).toAlgebra
    IsCompletelyFaithfullyFlat (Ideal.span {(p : R ⊥)})
      (Ring.DirectLimit R (fun i j h ↦ f i j h)) := by
  let (i : ι) : Algebra (R ⊥) (R i) := (f ⊥ i bot_le).toAlgebra
  let g : ∀ i j, i ≤ j → R i →ₐ[R ⊥] R j := fun i j h ↦
    { f i j h with commutes' := fun r ↦ DirectedSystem.map_map' f bot_le h r }
  let : DirectedSystem R (fun i j h ↦ g i j h) := inferInstanceAs
    (DirectedSystem R (fun i j h ↦ f i j h))
  let L := Ring.DirectLimit R (fun i j h ↦ f i j h)
  let D := _root_.DirectLimit R g
  let : Algebra (R ⊥) L := (Ring.DirectLimit.of R (fun i j h ↦ f i j h) ⊥).toAlgebra
  let a : L →+* D := Ring.DirectLimit.lift R (fun i j h ↦ f i j h) D
    (_root_.DirectLimit.Ring.of R g) (fun i j h x ↦ _root_.DirectLimit.Ring.of_f h x)
  let b : D →+* L := _root_.DirectLimit.Ring.lift R g L
    (Ring.DirectLimit.of R (fun i j h ↦ f i j h))
    (fun i j h x ↦ Ring.DirectLimit.of_f h x)
  have hba : b.comp a = RingHom.id L := by
    apply Ring.DirectLimit.hom_ext
    intro i
    ext x
    change b (a (Ring.DirectLimit.of R (fun i j h ↦ f i j h) i x)) = _
    have ha : a (Ring.DirectLimit.of R (fun i j h ↦ f i j h) i x) =
        _root_.DirectLimit.Ring.of R g i x := Ring.DirectLimit.lift_of ..
    rw [ha]
    rfl
  have hab : a.comp b = RingHom.id D := by
    apply _root_.DirectLimit.Ring.hom_ext
    intro i
    ext x
    change a (Ring.DirectLimit.of R (fun i j h ↦ f i j h) i x) = _
    exact Ring.DirectLimit.lift_of ..
  let e : L ≃+* D :=
    { a with
      invFun := b
      left_inv := RingHom.congr_fun hba
      right_inv := RingHom.congr_fun hab }
  have he (r : R ⊥) : e (algebraMap (R ⊥) L r) = algebraMap (R ⊥) D r := by
    change a (Ring.DirectLimit.of R (fun i j h ↦ f i j h) ⊥ r) = _
    trans (_root_.DirectLimit.Ring.of R g ⊥ r)
    · exact Ring.DirectLimit.lift_of ..
    · rw [_root_.DirectLimit.algebraMap_def (f := g) ⊥]
      have hself : algebraMap (R ⊥) (R ⊥) r = r := DirectedSystem.map_self' f r
      rw [hself]
      rfl
  let E : L ≃ₗ[R ⊥] D :=
    { e.toAddEquiv with
      map_smul' := by
        intro r x
        simp only [RingHom.id_apply]
        rw [Algebra.smul_def, Algebra.smul_def]
        change e (algebraMap (R ⊥) L r * x) = algebraMap (R ⊥) D r * e x
        rw [map_mul, he] }
  exact isCompletelyFaithfullyFlat_of_linearEquiv (Ideal.span {(p : R ⊥)}) E.symm
    (isCompletelyFaithfullyFlat_algebraDirectLimit R g _ hflat)


/-- ## 概要
perfectoid 環の有向系で、最小段から各段への写像が p 完全忠実平坦なら、
余極限の通常 p 進完備化への標準合成も p 完全忠実平坦である。
BS Thm 7.14（著者版 p.61）の極限段の標準射を扱う。

## 方針
環余極限への標準写像の完全忠実平坦性と、perfectoid 環の余極限の
p 冪ねじれの境界 1 を、完備化への合成定理に入力する。

## 規約
環と添字は Type u とし、標準段射・標準完備化射そのものを用いる。
p 正則性・Noether 性・遷移射の単射性を要求しない。

## 使われ方
超限反復の極限段で、初段からの完全忠実平坦性を維持する。
-/
theorem isCompletelyFaithfullyFlat_completedRingDirectLimit_of_orderBot {p : ℕ} [Fact p.Prime]
    {ι : Type u} [Preorder ι] [OrderBot ι] [IsDirectedOrder ι]
    (R : ι → Type u) [∀ i, CommRing (R i)]
    (f : ∀ i j, i ≤ j → R i →+* R j)
    [DirectedSystem R (fun i j h ↦ f i j h)]
    (hR : ∀ i, IsIntegralPerfectoid (R i) p)
    (hflat : ∀ i, letI := (f ⊥ i bot_le).toAlgebra;
      IsCompletelyFaithfullyFlat (Ideal.span {(p : R ⊥)}) (R i)) :
    let L := Ring.DirectLimit R (fun i j h ↦ f i j h)
    let C := AdicCompletion (Ideal.span {(p : L)}) L
    letI := ((algebraMap L C).comp
      (Ring.DirectLimit.of R (fun i j h ↦ f i j h) ⊥)).toAlgebra
    IsCompletelyFaithfullyFlat (Ideal.span {(p : R ⊥)}) C := by
  apply isCompletelyFaithfullyFlat_adicCompletion_comp p
    (Ring.DirectLimit.of R (fun i j h ↦ f i j h) ⊥)
    (isCompletelyFaithfullyFlat_ringDirectLimit_of_orderBot R f hflat)
  refine ⟨1, ?_⟩
  intro n x hx
  simpa only [pow_one] using
    ringDirectLimit_p_power_torsion_bound_of_perfectoid R f p hR n x hx
end SerrePositivity.BhattScholze.Andre.Transfinite
