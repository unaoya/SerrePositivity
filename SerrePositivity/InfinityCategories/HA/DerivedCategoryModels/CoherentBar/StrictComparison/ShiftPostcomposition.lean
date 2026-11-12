module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.ZeroShift
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.MaurerCartanDescent
public import SerrePositivity.DifferentialGraded.Module.ShiftResolution
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NestedCut
public import SerrePositivity.DifferentialGraded.Module.Hom.ConeComparison

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
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]

lemma dgStrictPostcompose_eq_compose {T M N : _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D}
    (f : M ⟶ N) {q : ℤ}
    (z : (_root_.SerrePositivity.DifferentialGraded.moduleHom R D (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) T)
      (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) M)).X q) :
    (eHomWhiskerLeft (_root_.SerrePositivity.DifferentialGraded.Complex R) T f).f q z =
      _root_.SerrePositivity.DifferentialGraded.compose R (x := ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) T)
        (y := ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) M)
        (z := ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) N)
        (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv R (_root_.SerrePositivity.DifferentialGraded.RightModule R D) M N f).val z (add_zero q) := by
  apply _root_.SerrePositivity.DifferentialGraded.moduleHomElement_ext R D
    (M := ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) T) (N := ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) N)
  intro x
  rw [_root_.SerrePositivity.DifferentialGraded.moduleHomWhiskerLeft_apply_π, _root_.SerrePositivity.DifferentialGraded.moduleHomCompose_π]
  exact congrArg (fun a => ((_root_.SerrePositivity.DifferentialGraded.moduleHomπ R D
    (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) T) (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) M) x).f q z).comp
      a (add_zero q)) (_root_.SerrePositivity.DifferentialGraded.moduleEvaluation_cochain R D x f)

lemma dgStrictPostcompose_shiftIn_zero (M : _root_.SerrePositivity.DifferentialGraded.RightModule R D) :
    (eHomWhiskerLeft (_root_.SerrePositivity.DifferentialGraded.Complex R) (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) M)
      (_root_.SerrePositivity.DifferentialGraded.moduleShiftZeroIsoObj R D M).hom).f 0 (_root_.SerrePositivity.DifferentialGraded.moduleShiftInElement R D 0 M) =
        (_root_.SerrePositivity.DifferentialGraded.unitElement R M).val := by
  rw [dgStrictPostcompose_eq_compose, ← _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgStrictShiftOut_zero R D]
  exact _root_.SerrePositivity.DifferentialGraded.moduleShiftInOut R D 0 M

lemma dgStrictPostcompose_shiftBlock_zero {M N : _root_.SerrePositivity.DifferentialGraded.RightModule R D}
    (f : (_root_.SerrePositivity.DifferentialGraded.moduleHom R D M N).X 0) :
    (eHomWhiskerLeft (_root_.SerrePositivity.DifferentialGraded.Complex R) (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (_root_.SerrePositivity.DifferentialGraded.shiftModule 1 M))
      (_root_.SerrePositivity.DifferentialGraded.moduleShiftZeroIsoObj R D N).hom).f 1
        (_root_.SerrePositivity.DifferentialGraded.moduleHomShiftBlock R D 1 0 f (by omega)) =
      _root_.SerrePositivity.DifferentialGraded.compose R (x := _root_.SerrePositivity.DifferentialGraded.shiftModule 1 M) (y := M) (z := N)
        f (_root_.SerrePositivity.DifferentialGraded.moduleShiftOutElement R D 1 M) (add_zero 1) := by
  rw [_root_.SerrePositivity.DifferentialGraded.moduleHomShiftBlock,
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarHom_postcompose_comp R D
      (M := ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (_root_.SerrePositivity.DifferentialGraded.shiftModule 1 M))
      (N := ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) N)
      (P := ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (_root_.SerrePositivity.DifferentialGraded.shiftModule 0 N))
      (Q := ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) N)]
  change _root_.SerrePositivity.DifferentialGraded.compose R (x := _root_.SerrePositivity.DifferentialGraded.shiftModule 1 M) (y := N) (z := N)
    ((eHomWhiskerLeft (_root_.SerrePositivity.DifferentialGraded.Complex R) (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) N)
      (_root_.SerrePositivity.DifferentialGraded.moduleShiftZeroIsoObj R D N).hom).f 0 (_root_.SerrePositivity.DifferentialGraded.moduleShiftInElement R D 0 N))
    (_root_.SerrePositivity.DifferentialGraded.compose R (x := _root_.SerrePositivity.DifferentialGraded.shiftModule 1 M) (y := M) (z := N)
      f (_root_.SerrePositivity.DifferentialGraded.moduleShiftOutElement R D 1 M) (add_zero 1)) (add_zero 1) = _
  rw [dgStrictPostcompose_shiftIn_zero R D]
  exact _root_.SerrePositivity.DifferentialGraded.unit_compose R _

lemma dgStrictPostcompose_comp {T M N P : _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D}
    (f : M ⟶ N) (g : N ⟶ P) {q : ℤ}
    (z : (_root_.SerrePositivity.DifferentialGraded.moduleHom R D (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) T)
      (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) M)).X q) :
    (eHomWhiskerLeft (_root_.SerrePositivity.DifferentialGraded.Complex R) T (f ≫ g)).f q z =
      (eHomWhiskerLeft (_root_.SerrePositivity.DifferentialGraded.Complex R) T g).f q
        ((eHomWhiskerLeft (_root_.SerrePositivity.DifferentialGraded.Complex R) T f).f q z) :=
  congrArg (fun a => a.f q z) (eHomWhiskerLeft_comp (_root_.SerrePositivity.DifferentialGraded.Complex R) T f g)

lemma dgStrictPostcompose_eq_of_heq {T N N' P : _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D}
    (hN : N = N') (f : N ⟶ P) (g : N' ⟶ P) (hfg : HEq f g) (q : ℤ)
    (z : (_root_.SerrePositivity.DifferentialGraded.moduleHom R D (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) T)
      (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) N)).X q)
    (w : (_root_.SerrePositivity.DifferentialGraded.moduleHom R D (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) T)
      (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) N')).X q) (hzw : HEq z w) :
    (eHomWhiskerLeft (_root_.SerrePositivity.DifferentialGraded.Complex R) T f).f q z =
      (eHomWhiskerLeft (_root_.SerrePositivity.DifferentialGraded.Complex R) T g).f q w := by
  cases hN
  cases hfg
  cases hzw
  rfl

lemma dgStrictPostcompose_shiftBlock_unit {M P : _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D} (p : M ⟶ P) :
    (eHomWhiskerLeft (_root_.SerrePositivity.DifferentialGraded.Complex R)
      (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (_root_.SerrePositivity.DifferentialGraded.shiftModule 1 (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) M)))
      ((_root_.SerrePositivity.DifferentialGraded.moduleShiftZeroIsoObj R D (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) M)).hom ≫ p)).f 1
      (_root_.SerrePositivity.DifferentialGraded.moduleHomShiftBlock R D 1 0
        (_root_.SerrePositivity.DifferentialGraded.unitElement R (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) M)).val (by omega)) =
    (eHomWhiskerLeft (_root_.SerrePositivity.DifferentialGraded.Complex R)
      (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (_root_.SerrePositivity.DifferentialGraded.shiftModule 1 (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) M)))
      p).f 1 (_root_.SerrePositivity.DifferentialGraded.moduleShiftOutElement R D 1 (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) M)) := by
  rw [dgStrictPostcompose_comp R D,
    dgStrictPostcompose_shiftBlock_zero R D
      (M := ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) M)
      (N := ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) M), _root_.SerrePositivity.DifferentialGraded.unit_compose]
  rfl

lemma dgStrictPostcompose_shiftBlock_closed {M N P : _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D}
    (f : M ⟶ N) (p : N ⟶ P) :
    (eHomWhiskerLeft (_root_.SerrePositivity.DifferentialGraded.Complex R)
      (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (_root_.SerrePositivity.DifferentialGraded.shiftModule 1 (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) M)))
      ((_root_.SerrePositivity.DifferentialGraded.moduleShiftZeroIsoObj R D (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) N)).hom ≫ p)).f 1
      (_root_.SerrePositivity.DifferentialGraded.moduleHomShiftBlock R D 1 0
        (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv R (_root_.SerrePositivity.DifferentialGraded.RightModule R D) M N f).val (by omega)) =
    (eHomWhiskerLeft (_root_.SerrePositivity.DifferentialGraded.Complex R)
      (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (_root_.SerrePositivity.DifferentialGraded.shiftModule 1 (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) M)))
      (f ≫ p)).f 1 (_root_.SerrePositivity.DifferentialGraded.moduleShiftOutElement R D 1 (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) M)) := by
  rw [dgStrictPostcompose_comp R D,
    dgStrictPostcompose_shiftBlock_zero R D
      (M := ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) M)
      (N := ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) N)]
  refine Eq.trans (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarHom_postcompose_comp R D
    (M := ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (_root_.SerrePositivity.DifferentialGraded.shiftModule 1 (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) M)))
    (N := M) (P := N) (Q := P) p
    (_root_.SerrePositivity.DifferentialGraded.moduleShiftOutElement R D 1 (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) M))
    (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv R (_root_.SerrePositivity.DifferentialGraded.RightModule R D) M N f).val (add_zero 1)) ?_
  have hc : (eHomWhiskerLeft (_root_.SerrePositivity.DifferentialGraded.Complex R) M p).f 0
      (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv R (_root_.SerrePositivity.DifferentialGraded.RightModule R D) M N f).val =
    (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv R (_root_.SerrePositivity.DifferentialGraded.RightModule R D) M P (f ≫ p)).val :=
    _root_.SerrePositivity.DifferentialGraded.moduleHomCycle_postcompose R D f p
  refine Eq.trans (congrArg (fun z => _root_.SerrePositivity.DifferentialGraded.compose R
    (x := _root_.SerrePositivity.DifferentialGraded.shiftModule 1 (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) M))
    (y := ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) M) (z := ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) P)
    z (_root_.SerrePositivity.DifferentialGraded.moduleShiftOutElement R D 1 (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) M)) (add_zero 1)) hc) ?_
  exact (dgStrictPostcompose_eq_compose R D (f ≫ p)
    (_root_.SerrePositivity.DifferentialGraded.moduleShiftOutElement R D 1 (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) M))).symm

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
