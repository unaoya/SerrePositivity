module
public import SerrePositivity.DifferentialGraded.Module.ShiftBlocks
/-!
概要：シフト間の斉次ブロック構成は、元の Hom 加群の線形写像である。
方針：元の評価ごとの cochain 合成へ戻し、中間係数の加法性と線形性を使う。
規約：次数と両端の shift を明示し、有限和と符号スカラーを同じ写像で扱う。
使われ方：HA 微分の有限和を bar の shift ブロックへ送る。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex
variable (R : Type u) [CommRing R]

/-- 概要：二つの固定 cochain の間の合成を線形写像として扱う。
方針：cochain 合成の両線形性を使う。
規約：三つの次数の和を明示する。使われ方：shift ブロックの係数の線形性。 -/
def cochainSandwichLinear {K M N L : Complex R} {s t : ℤ}
    (A : Cochain K M s) (B : Cochain N L t) (q k : ℤ) (hk : s + q + t = k) :
    Cochain M N q →ₗ[R] Cochain K L k where
  toFun f := (A.comp f rfl).comp B hk
  map_add' f g := by rw [Cochain.comp_add, Cochain.add_comp]
  map_smul' a f := by rw [Cochain.comp_smul, Cochain.smul_comp]; rfl

variable (D : Type v) [DGCategory R D] [Small.{u} D]

/-- 概要：シフト間のブロックを作る線形写像。
方針：両側の斉次単位との合成を評価する。
規約：全次数の等式を明示する。使われ方：bar 係数の有限和と微分。 -/
def moduleHomShiftBlockLinear (s t : ℤ) (M N : RightModule R D) (q k : ℤ)
    (hk : s + q - t = k) :
    (moduleHom R D M N).X q →ₗ[R]
      (moduleHom R D (shiftModule s M) (shiftModule t N)).X k where
  toFun f := moduleHomShiftBlock R D s t f hk
  map_add' f g := by
    apply moduleHomElement_ext R D (M := shiftModule s M) (N := shiftModule t N)
    intro x
    simp only [map_add, moduleHomShiftBlock_π]
    exact (cochainSandwichLinear R
      ((moduleHomπ R D (shiftModule s M) M x).f s (moduleShiftOutElement R D s M))
      ((moduleHomπ R D N (shiftModule t N) x).f (-t) (moduleShiftInElement R D t N))
      q k (by omega)).map_add _ _
  map_smul' a f := by
    apply moduleHomElement_ext R D (M := shiftModule s M) (N := shiftModule t N)
    intro x
    simp only [map_smul, moduleHomShiftBlock_π, RingHom.id_apply]
    exact (cochainSandwichLinear R
      ((moduleHomπ R D (shiftModule s M) M x).f s (moduleShiftOutElement R D s M))
      ((moduleHomπ R D N (shiftModule t N) x).f (-t) (moduleShiftInElement R D t N))
      q k (by omega)).map_smul a _

lemma moduleHomShiftBlock_zero (s t : ℤ) (M N : RightModule R D) (q k : ℤ)
    (hk : s + q - t = k) :
    moduleHomShiftBlock R D s t (0 : (moduleHom R D M N).X q) hk = 0 :=
  (moduleHomShiftBlockLinear R D s t M N q k hk).map_zero

lemma moduleHomShiftBlock_unit_d (s t : ℤ) (M : RightModule R D) (k : ℤ)
    (hk : s + 0 - t = k) :
    (moduleHom R D (shiftModule s M) (shiftModule t M)).d k (k + 1)
      (moduleHomShiftBlock R D s t (unitElement R M).val hk) = 0 := by
  rw [moduleHomShiftBlock_d R D]
  have hu : (moduleHom R D M M).d 0 1 (unitElement R M).val = 0 :=
    differential_unit R M
  let L := moduleHomShiftBlockLinear R D s t M M 1 (k + 1) (by omega)
  have hb := (congrArg L hu).trans L.map_zero
  exact (congrArg (fun z => (-t).negOnePow • z) hb).trans (smul_zero _)

end SerrePositivity.DifferentialGraded
