module

public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneTruncation

/-!
# シフトした smart 切断の標準遷移

DAG XIII §2.2 の Eilenberg–Mac Lane 構造射の鎖の側の前段。
包含をシフトし、同じ smart 切断の包含を通して持ち上げる。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
variable {A : Type u} [CommRing A]

/-- 非正 smart 切断を一つシフトしたものは、なお非正次数に台を持つ。 -/
instance shiftedSmartTruncation_isStrictlyLE (M : Complex A) :
    ((M.truncLE 0)⟦(1 : ℤ)⟧).IsStrictlyLE 0 := by
  have : ((M.truncLE 0)⟦(1 : ℤ)⟧).IsStrictlyLE (-1) :=
    (M.truncLE 0).isStrictlyLE_shift 0 1 (-1) (by omega)
  exact CochainComplex.isStrictlyLE_of_le _ (-1) 0 (by omega)

/-- 包含のシフトを、標的の同じ smart 切断へ持ち上げる実際の射。 -/
def smartShiftTransition (M : Complex A) :
    (M.truncLE 0)⟦(1 : ℤ)⟧ ⟶ (M⟦(1 : ℤ)⟧).truncLE 0 :=
  inv (((M.truncLE 0)⟦(1 : ℤ)⟧).ιTruncLE 0) ≫
    CochainComplex.truncLEMap ((shiftFunctor (Complex A) (1 : ℤ)).map (M.ιTruncLE 0)) 0

/-- この射は、元の指定包含をシフトした同じ射を与える。 -/
lemma smartShiftTransition_ι (M : Complex A) :
    smartShiftTransition M ≫ (M⟦(1 : ℤ)⟧).ιTruncLE 0 =
      (shiftFunctor (Complex A) (1 : ℤ)).map (M.ιTruncLE 0) := by
  dsimp only [smartShiftTransition]
  rw [Category.assoc, CochainComplex.ιTruncLE_naturality]
  simp only [IsIso.inv_hom_id_assoc]

/-- 指定遷移は任意の複体の射に関して自然である。 -/
lemma smartShiftTransition_naturality {M N : Complex A} (f : M ⟶ N) :
    (shiftFunctor (Complex A) (1 : ℤ)).map (CochainComplex.truncLEMap f 0) ≫
      smartShiftTransition N =
    smartShiftTransition M ≫
      CochainComplex.truncLEMap ((shiftFunctor (Complex A) (1 : ℤ)).map f) 0 := by
  have : Mono ((N⟦(1 : ℤ)⟧).ιTruncLE 0) :=
    inferInstanceAs (Mono (HomologicalComplex.ιTruncLE
      (N⟦(1 : ℤ)⟧) (ComplexShape.embeddingUpIntLE 0)))
  apply (cancel_mono ((N⟦(1 : ℤ)⟧).ιTruncLE 0)).1
  rw [Category.assoc, smartShiftTransition_ι, Category.assoc,
    CochainComplex.ιTruncLE_naturality, ← Category.assoc, smartShiftTransition_ι]
  rw [← Functor.map_comp, ← Functor.map_comp, CochainComplex.ιTruncLE_naturality]

/-- 構造射の鎖の側は、厳密に負の次数で準同型である。 -/
lemma smartShiftTransition_quasiIsoAt (M : Complex A) (i : ℤ) (hi : i < 0) :
    QuasiIsoAt (smartShiftTransition M) i := by
  have : QuasiIsoAt (M.ιTruncLE 0) (1 + i) :=
    CochainComplex.quasiIsoAt_ιTruncLE M 0 (1 + i) (by omega)
  have : QuasiIsoAt ((shiftFunctor (Complex A) (1 : ℤ)).map (M.ιTruncLE 0)) i :=
    (CochainComplex.quasiIsoAt_shift_iff (M.ιTruncLE 0) 1 i (1 + i) rfl).mpr
      inferInstance
  have : QuasiIsoAt ((M⟦(1 : ℤ)⟧).ιTruncLE 0) i :=
    CochainComplex.quasiIsoAt_ιTruncLE _ 0 i (by omega)
  have : QuasiIsoAt (smartShiftTransition M ≫ (M⟦(1 : ℤ)⟧).ιTruncLE 0) i := by
    rw [smartShiftTransition_ι]
    infer_instance
  exact quasiIsoAt_of_comp_right (smartShiftTransition M)
    ((M⟦(1 : ℤ)⟧).ιTruncLE 0) i

end SerrePositivity.EInfinity.PowerOperation
