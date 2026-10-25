module
public import SerrePositivity.DifferentialGraded.Module.ShiftUnitDifferential
/-!
概要：異なるシフト間の斉次 Hom を、元の斉次 Hom から構成する。
方針：互いに逆な shift の斉次単位で前後から合成する。
規約：元の全次数 Hom と二つの shift を保持し、次数の等式を明示する。
使われ方：coherent bar 微分の単体ごとのブロック。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

/-- シフト包含・射影による、元の斉次 Hom の同じブロック。 -/
def moduleHomShiftBlock (s t : ℤ) {M N : RightModule R D} {q k : ℤ}
    (f : (moduleHom R D M N).X q) (hk : s + q - t = k) :
    (moduleHom R D (shiftModule s M) (shiftModule t N)).X k :=
  compose R (x := shiftModule s M) (y := N) (z := shiftModule t N)
    (moduleShiftInElement R D t N)
    (compose R (x := shiftModule s M) (y := M) (z := N)
      f (moduleShiftOutElement R D s M) rfl) (by omega)

lemma moduleHomShiftBlock_π (s t : ℤ) {M N : RightModule R D} {q k : ℤ}
    (f : (moduleHom R D M N).X q) (hk : s + q - t = k) (x : D) :
    (moduleHomπ R D (shiftModule s M) (shiftModule t N) x).f k
      (moduleHomShiftBlock R D s t f hk) =
    (((moduleHomπ R D (shiftModule s M) M x).f s (moduleShiftOutElement R D s M)).comp
      ((moduleHomπ R D M N x).f q f) rfl).comp
      ((moduleHomπ R D N (shiftModule t N) x).f (-t) (moduleShiftInElement R D t N))
      (by omega) := by
  unfold moduleHomShiftBlock
  rw [moduleHomCompose_π, moduleHomCompose_π]

lemma moduleHomShiftBlock_d (s t : ℤ) {M N : RightModule R D} {q k : ℤ}
    (f : (moduleHom R D M N).X q) (hk : s + q - t = k) :
    (moduleHom R D (shiftModule s M) (shiftModule t N)).d k (k + 1)
      (moduleHomShiftBlock R D s t f hk) =
      (-t).negOnePow • moduleHomShiftBlock R D s t
        ((moduleHom R D M N).d q (q + 1) f) (by omega : s + (q + 1) - t = k + 1) := by
  have hi : differential R (x := N) (y := shiftModule t N)
      (moduleShiftInElement R D t N) = 0 := moduleShiftInElement_d R D t N
  have ho : differential R (x := shiftModule s M) (y := M)
      (moduleShiftOutElement R D s M) = 0 := moduleShiftOutElement_d R D s M
  subst k
  unfold moduleHomShiftBlock
  change differential R (x := shiftModule s M) (y := shiftModule t N) _ = _
  rw [differential_compose, differential_compose, hi, ho]
  simp only [compose, forward, TensorProduct.zero_tmul, TensorProduct.tmul_zero,
    map_zero, smul_zero, zero_add, add_zero]
  let φ (a : {a : ℤ // s + (q + 1) = a}) :
      (moduleHom R D (shiftModule s M) (shiftModule t N)).X (s + q - t + 1) :=
    (-t).negOnePow • compose R (x := shiftModule s M) (y := N) (z := shiftModule t N)
      (moduleShiftInElement R D t N)
      (compose R (x := shiftModule s M) (y := M) (z := N)
        ((moduleHom R D M N).d q (q + 1) f) (moduleShiftOutElement R D s M) a.property)
      (by have := a.property; omega)
  have he : (⟨s + q + 1, by omega⟩ : {a : ℤ // s + (q + 1) = a}) =
      ⟨s + (q + 1), rfl⟩ := Subtype.ext (by change s + q + 1 = s + (q + 1); omega)
  have hφ := congrArg φ he
  dsimp only [φ, compose, forward, differential] at hφ
  exact hφ

end SerrePositivity.DifferentialGraded
