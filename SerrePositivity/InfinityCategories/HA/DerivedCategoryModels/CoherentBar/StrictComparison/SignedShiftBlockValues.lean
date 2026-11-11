module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.ShiftBlockValues

/-!
概要：一次 bar 列の外側の符号が連続する shift 単位の符号と相殺する。
方針：shift ブロックの実評価式へ整数符号の恒等式を適用する。
規約：元の閉零係数と実次数輸送を残す。
使われ方：通常のホモロジー bar の交代面和との比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory DifferentialGraded HomologicalComplex CochainComplex HomComplex
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

lemma dgBarSignedShiftBlock_v (n : ℤ) {M N : RightModule R D}
    (f : (moduleHom R D M N).X 0) (x : D) (p q : ℤ) (hpq : p + 1 = q) :
    (n + 1).negOnePow •
      (((moduleHomπ R D (shiftModule (n + 1) M) (shiftModule n N) x).f 1
        (moduleHomShiftBlock R D (n + 1) n f (by omega))).v p q hpq) =
    ((M.obj (Opposite.op x)).shiftFunctorObjXIso (n + 1) p (p + (n + 1)) rfl).hom ≫
      (((moduleHomπ R D M N x).f 0 f).v (p + (n + 1)) (p + (n + 1)) (by omega)) ≫
        ((N.obj (Opposite.op x)).shiftFunctorObjXIso n q (p + (n + 1)) (by omega)).inv := by
  rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgBarShiftBlock_v R D (n + 1) n f (by omega), smul_smul,
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgBarShiftUnitSign_succ_mul, ← Int.negOnePow_add,
    show (n + 1) + (n + 1) = 2 * (n + 1) by ring,
    Int.negOnePow_two_mul, one_smul]

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
