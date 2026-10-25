module
public import SerrePositivity.DifferentialGraded.Module.ShiftBlocks
public import SerrePositivity.DifferentialGraded.Complexes.GradedConjugationComposition
/-!
概要：シフト間の斉次 Hom ブロックの合成は、元の斉次 Hom の合成と厳密に一致する。
方針：評価ごとの六項合成で、中間の shift 包含・射影の対を消去する。
規約：全次数と三つの shift を保ち、閉零射や h 圏へ制限しない。
使われ方：coherent bar の二段 prefix に現れる二乗項。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

lemma moduleHomShiftBlock_comp (s t r : ℤ) {M N P : RightModule R D} {p q a b c : ℤ}
    (f : (moduleHom R D M N).X p) (g : (moduleHom R D N P).X q)
    (ha : s + p - t = a) (hb : t + q - r = b) (hc : a + b = c) :
    compose R (x := shiftModule s M) (y := shiftModule t N) (z := shiftModule r P)
      (moduleHomShiftBlock R D t r g hb) (moduleHomShiftBlock R D s t f ha) hc =
      moduleHomShiftBlock R D s r (compose R (x := M) (y := N) (z := P) g f rfl)
        (by omega : s + (p + q) - r = c) := by
  apply moduleHomElement_ext R D (M := shiftModule s M) (N := shiftModule r P)
  intro x
  rw [moduleHomCompose_π R D, moduleHomShiftBlock_π R D,
    moduleHomShiftBlock_π R D, moduleHomShiftBlock_π R D, moduleHomCompose_π R D]
  have hu := congrArg ((moduleHomπ R D N N x).f 0) (moduleShiftInOut R D t N)
  rw [moduleHomCompose_π R D, yoneda_moduleUnit_π] at hu
  exact cochainSixfold_cancel _ _ _ _ _ _ hu ha hb hc

end SerrePositivity.DifferentialGraded
