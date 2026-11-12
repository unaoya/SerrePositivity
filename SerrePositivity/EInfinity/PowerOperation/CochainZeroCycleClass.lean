module

public import SerrePositivity.EInfinity.HomologyZero.Classes
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# 零次閉元の具体表示と実 cycles・homology 射の照合

DAG XIII §2.2 の指定単位の計算で用いる一般の補助。元の閉元と類写像を保持する。
［一般∞］移動候補。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
variable {A : Type u} [CommRing A]

/-- 元の零次閉元の加群と実 cycles の標準比較。 -/
def zeroCyclesActualIso (M : Complex A) : ModuleCat.of A (zeroCycles M) ≅ M.cycles 0 :=
  (M.sc' (-1) 0 1).moduleCatCyclesIso.symm ≪≫
    (M.cyclesIsoSc' (-1) 0 1 (by simp [CochainComplex.prev])
      (by simp [CochainComplex.next])).symm

@[reassoc]
lemma zeroCyclesActualIso_i (M : Complex A) :
    (zeroCyclesActualIso M).hom ≫ M.iCycles 0 =
      (M.sc' (-1) 0 1).moduleCatLeftHomologyData.i := by
  simp [zeroCyclesActualIso]

@[reassoc]
lemma zeroCyclesActualIso_homologyπ (M : Complex A) :
    (zeroCyclesActualIso M).hom ≫ M.homologyπ 0 =
      ModuleCat.ofHom (HomologyZero.classMap M) := by
  simp only [zeroCyclesActualIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    HomologyZero.classMap, HomologyZero.quotientIso, Iso.trans_inv, ModuleCat.ofHom_hom]
  rw [← HomologicalComplex.π_homologyIsoSc'_inv,
    ShortComplex.moduleCatCyclesIso_inv_π_assoc]

end SerrePositivity.EInfinity.PowerOperation
