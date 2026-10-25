module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.ZeroShift
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.MaurerCartanDescent
public import SerrePositivity.DifferentialGraded.Module.ShiftUnitRelations
public import SerrePositivity.InfinityCategories.DGNerve.NestedCut
public import SerrePositivity.DifferentialGraded.Module.HomCycles

/-!
概要：shift ブロックの零 shift 標的を、元の閉零射への後合成へ戻す。
方針：後合成を閉零要素の斉次合成と同定し、shift 単位の逆関係を使う。
規約：全次数の加群自然性を保つ。
使われ方：strict augmentation の一次元の面と prefix の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

lemma dgStrictPostcompose_eq_compose {T M N : ModuleCategory R D}
    (f : M ⟶ N) {q : ℤ}
    (z : (moduleHom R D (ForgetEnrichment.to (Complex R) T)
      (ForgetEnrichment.to (Complex R) M)).X q) :
    (eHomWhiskerLeft (Complex R) T f).f q z =
      compose R (x := ForgetEnrichment.to (Complex R) T)
        (y := ForgetEnrichment.to (Complex R) M)
        (z := ForgetEnrichment.to (Complex R) N)
        (closedHomEquiv R (RightModule R D) M N f).val z (add_zero q) := by
  apply moduleHomElement_ext R D
    (M := ForgetEnrichment.to (Complex R) T) (N := ForgetEnrichment.to (Complex R) N)
  intro x
  rw [moduleHomWhiskerLeft_apply_π, moduleHomCompose_π]
  exact congrArg (fun a => ((moduleHomπ R D
    (ForgetEnrichment.to (Complex R) T) (ForgetEnrichment.to (Complex R) M) x).f q z).comp
      a (add_zero q)) (moduleEvaluation_cochain R D x f)

lemma dgStrictPostcompose_shiftIn_zero (M : RightModule R D) :
    (eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) M)
      (moduleShiftZeroIsoObj R D M).hom).f 0 (moduleShiftInElement R D 0 M) =
        (unitElement R M).val := by
  rw [dgStrictPostcompose_eq_compose, ← dgStrictShiftOut_zero R D]
  exact moduleShiftInOut R D 0 M

lemma dgStrictPostcompose_shiftBlock_zero {M N : RightModule R D}
    (f : (moduleHom R D M N).X 0) :
    (eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) (shiftModule 1 M))
      (moduleShiftZeroIsoObj R D N).hom).f 1
        (moduleHomShiftBlock R D 1 0 f (by omega)) =
      compose R (x := shiftModule 1 M) (y := M) (z := N)
        f (moduleShiftOutElement R D 1 M) (add_zero 1) := by
  rw [moduleHomShiftBlock,
    dgCoherentBarHom_postcompose_comp R D
      (M := ForgetEnrichment.of (Complex R) (shiftModule 1 M))
      (N := ForgetEnrichment.of (Complex R) N)
      (P := ForgetEnrichment.of (Complex R) (shiftModule 0 N))
      (Q := ForgetEnrichment.of (Complex R) N)]
  change compose R (x := shiftModule 1 M) (y := N) (z := N)
    ((eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) N)
      (moduleShiftZeroIsoObj R D N).hom).f 0 (moduleShiftInElement R D 0 N))
    (compose R (x := shiftModule 1 M) (y := M) (z := N)
      f (moduleShiftOutElement R D 1 M) (add_zero 1)) (add_zero 1) = _
  rw [dgStrictPostcompose_shiftIn_zero R D]
  exact unit_compose R _

lemma dgStrictPostcompose_comp {T M N P : ModuleCategory R D}
    (f : M ⟶ N) (g : N ⟶ P) {q : ℤ}
    (z : (moduleHom R D (ForgetEnrichment.to (Complex R) T)
      (ForgetEnrichment.to (Complex R) M)).X q) :
    (eHomWhiskerLeft (Complex R) T (f ≫ g)).f q z =
      (eHomWhiskerLeft (Complex R) T g).f q
        ((eHomWhiskerLeft (Complex R) T f).f q z) :=
  congrArg (fun a => a.f q z) (eHomWhiskerLeft_comp (Complex R) T f g)

lemma dgStrictPostcompose_eq_of_heq {T N N' P : ModuleCategory R D}
    (hN : N = N') (f : N ⟶ P) (g : N' ⟶ P) (hfg : HEq f g) (q : ℤ)
    (z : (moduleHom R D (ForgetEnrichment.to (Complex R) T)
      (ForgetEnrichment.to (Complex R) N)).X q)
    (w : (moduleHom R D (ForgetEnrichment.to (Complex R) T)
      (ForgetEnrichment.to (Complex R) N')).X q) (hzw : HEq z w) :
    (eHomWhiskerLeft (Complex R) T f).f q z =
      (eHomWhiskerLeft (Complex R) T g).f q w := by
  cases hN
  cases hfg
  cases hzw
  rfl

lemma dgStrictPostcompose_shiftBlock_unit {M P : ModuleCategory R D} (p : M ⟶ P) :
    (eHomWhiskerLeft (Complex R)
      (ForgetEnrichment.of (Complex R) (shiftModule 1 (ForgetEnrichment.to (Complex R) M)))
      ((moduleShiftZeroIsoObj R D (ForgetEnrichment.to (Complex R) M)).hom ≫ p)).f 1
      (moduleHomShiftBlock R D 1 0
        (unitElement R (ForgetEnrichment.to (Complex R) M)).val (by omega)) =
    (eHomWhiskerLeft (Complex R)
      (ForgetEnrichment.of (Complex R) (shiftModule 1 (ForgetEnrichment.to (Complex R) M)))
      p).f 1 (moduleShiftOutElement R D 1 (ForgetEnrichment.to (Complex R) M)) := by
  rw [dgStrictPostcompose_comp R D,
    dgStrictPostcompose_shiftBlock_zero R D
      (M := ForgetEnrichment.to (Complex R) M)
      (N := ForgetEnrichment.to (Complex R) M), unit_compose]
  rfl

lemma dgStrictPostcompose_shiftBlock_closed {M N P : ModuleCategory R D}
    (f : M ⟶ N) (p : N ⟶ P) :
    (eHomWhiskerLeft (Complex R)
      (ForgetEnrichment.of (Complex R) (shiftModule 1 (ForgetEnrichment.to (Complex R) M)))
      ((moduleShiftZeroIsoObj R D (ForgetEnrichment.to (Complex R) N)).hom ≫ p)).f 1
      (moduleHomShiftBlock R D 1 0
        (closedHomEquiv R (RightModule R D) M N f).val (by omega)) =
    (eHomWhiskerLeft (Complex R)
      (ForgetEnrichment.of (Complex R) (shiftModule 1 (ForgetEnrichment.to (Complex R) M)))
      (f ≫ p)).f 1 (moduleShiftOutElement R D 1 (ForgetEnrichment.to (Complex R) M)) := by
  rw [dgStrictPostcompose_comp R D,
    dgStrictPostcompose_shiftBlock_zero R D
      (M := ForgetEnrichment.to (Complex R) M)
      (N := ForgetEnrichment.to (Complex R) N)]
  refine Eq.trans (dgCoherentBarHom_postcompose_comp R D
    (M := ForgetEnrichment.of (Complex R) (shiftModule 1 (ForgetEnrichment.to (Complex R) M)))
    (N := M) (P := N) (Q := P) p
    (moduleShiftOutElement R D 1 (ForgetEnrichment.to (Complex R) M))
    (closedHomEquiv R (RightModule R D) M N f).val (add_zero 1)) ?_
  have hc : (eHomWhiskerLeft (Complex R) M p).f 0
      (closedHomEquiv R (RightModule R D) M N f).val =
    (closedHomEquiv R (RightModule R D) M P (f ≫ p)).val :=
    moduleHomCycle_postcompose R D f p
  refine Eq.trans (congrArg (fun z => compose R
    (x := shiftModule 1 (ForgetEnrichment.to (Complex R) M))
    (y := ForgetEnrichment.to (Complex R) M) (z := ForgetEnrichment.to (Complex R) P)
    z (moduleShiftOutElement R D 1 (ForgetEnrichment.to (Complex R) M)) (add_zero 1)) hc) ?_
  exact (dgStrictPostcompose_eq_compose R D (f ≫ p)
    (moduleShiftOutElement R D 1 (ForgetEnrichment.to (Complex R) M))).symm

end SerrePositivity.InfinityCategories
