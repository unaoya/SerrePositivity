module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.ShiftUnitSigns

/-!
概要：閉零係数から作る shift ブロックの実評価式。
方針：同じ斉次単位の評価を合成し、二つの定数符号を保持する。
規約：元の Hom 要素と次数輸送を明示する。
使われ方：実 coherent bar の面・辺の一次微分の符号計算。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory DifferentialGraded HomologicalComplex CochainComplex HomComplex
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

set_option maxHeartbeats 800000 in
-- 同じ Hom の二重合成の局所評価に限る上限。
lemma dgBarShiftBlock_v (s t : ℤ) {M N : RightModule R D}
    (f : (moduleHom R D M N).X 0) {k : ℤ} (hk : s + 0 - t = k)
    (x : D) (p q : ℤ) (hpq : p + k = q) :
    (((moduleHomπ R D (shiftModule s M) (shiftModule t N) x).f k
      (moduleHomShiftBlock R D s t f hk)).v p q hpq) =
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgBarShiftUnitSign s * _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgBarShiftUnitSign t) •
      (((M.obj (Opposite.op x)).shiftFunctorObjXIso s p (p + s) rfl).hom ≫
        (((moduleHomπ R D M N x).f 0 f).v (p + s) (p + s) (by omega)) ≫
          ((N.obj (Opposite.op x)).shiftFunctorObjXIso t q (p + s) (by omega)).inv) := by
  rw [moduleHomShiftBlock_π]
  erw [Cochain.comp_v _ _ _ p (p + s) q (by omega) (by omega),
    Cochain.comp_v _ _ _ p (p + s) (p + s) rfl (by omega),
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgBarShiftOutElement_v R D s M x p (p + s) rfl,
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgBarShiftInElement_v R D t N x (p + s) q (by omega)]
  simp only [Linear.units_smul_comp, Linear.comp_units_smul, smul_smul, Category.assoc]
  rw [mul_comm (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgBarShiftUnitSign t) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgBarShiftUnitSign s)]

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
