module
public import SerrePositivity.DifferentialGraded.Module.ShiftResolution

/-!
概要：bar の shift ブロックを作る斉次単位の次数ごとの評価式。
方針：元の leftShift・rightShift の定数符号と次数同型を明示する。
規約：定数符号を省略せず、実 Hom 要素を計算する。
使われ方：coherent bar の一次面微分の符号の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory DifferentialGraded HomologicalComplex CochainComplex HomComplex
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

def dgBarShiftUnitSign (s : ℤ) : ℤˣ := (s * s + s * (s - 1) / 2).negOnePow

lemma dgBarShiftOutElement_v (s : ℤ) (M : RightModule R D) (x : D) (p q : ℤ)
    (hpq : p + s = q) :
    (((moduleHomπ R D (shiftModule s M) M x).f s (moduleShiftOutElement R D s M)).v
      p q hpq) =
    dgBarShiftUnitSign s • ((M.obj (Opposite.op x)).shiftFunctorObjXIso s p q hpq.symm).hom := by
  rw [moduleShiftOutElement_π, Cochain.leftShift_v _ s s (zero_add s)
    p q hpq q (by omega)]
  simp only [Cochain.ofHom_v, HomologicalComplex.id_f, Category.comp_id]
  rfl

lemma dgBarShiftInElement_v (s : ℤ) (M : RightModule R D) (x : D) (p q : ℤ)
    (hpq : p + -s = q) :
    (((moduleHomπ R D M (shiftModule s M) x).f (-s) (moduleShiftInElement R D s M)).v
      p q hpq) =
    dgBarShiftUnitSign s •
      ((M.obj (Opposite.op x)).shiftFunctorObjXIso s q p (by omega)).inv := by
  rw [moduleShiftInElement_π, Cochain.units_smul_v,
    Cochain.rightShift_v _ s (-s) (neg_add_cancel s) p q hpq p (by omega)]
  simp only [Cochain.ofHom_v, HomologicalComplex.id_f, Category.id_comp]
  rfl

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
