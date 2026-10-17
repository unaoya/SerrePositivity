module
public import SerrePositivity.DifferentialGraded.Morita.CriterionPerfHomComparison
public import SerrePositivity.DifferentialGraded.Morita.CriterionPerfEquivalence

/-! # 主 kernel の Perf 判定の三つの独立した条件

第二条件は通常代表とその主 kernel への同型を持つ存在命題とする。
比較そのものは源の列を射影置換した全 Hom 複体の射である。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]
  (E : Type w) [DGCategory A E] [Small.{u} E]

/-- 全 Hom の擬同型比較を持つ通常代表が存在するという、主 kernel 上の条件。 -/
def criterionPerfKernelFullHomQuasiIso (K : Kernel A D E) : Prop :=
  ∃ P : BimoduleCategory A E D,
    Nonempty ((bimoduleToDerived A E D).obj P ≅ K) ∧
      criterionPerfFullHomQuasiIso A D E (BimoduleCategory.underlying A E D P)

/-- 通常代表から主 kernel の第二条件を与える。 -/
lemma criterionPerfKernelFullHomQuasiIso_of_model
    (P : BimoduleCategory A E D) (K : Kernel A D E)
    (e : (bimoduleToDerived A E D).obj P ≅ K)
    (h : criterionPerfFullHomQuasiIso A D E (BimoduleCategory.underlying A E D P)) :
    criterionPerfKernelFullHomQuasiIso A D E K := ⟨P, ⟨e⟩, h⟩

/-- 第二条件は主 kernel の同型で移送でき、代表の選択を構造に固定しない。 -/
lemma criterionPerfKernelFullHomQuasiIso_iso_iff {K L : Kernel A D E} (e : K ≅ L) :
    criterionPerfKernelFullHomQuasiIso A D E K ↔
      criterionPerfKernelFullHomQuasiIso A D E L := by
  constructor
  · rintro ⟨P, ⟨i⟩, h⟩
    exact ⟨P, ⟨i ≪≫ e⟩, h⟩
  · rintro ⟨P, ⟨i⟩, h⟩
    exact ⟨P, ⟨i ≪≫ e.symm⟩, h⟩

/-- 列の perfect 性、全 Hom 複体比較、厚い生成性を独立に保持する。 -/
structure CriterionPerfConditions (K : Kernel A D E) : Prop where
  columnsPerfect : kernelColumnsPerfect A D E K
  fullHomQuasiIso : criterionPerfKernelFullHomQuasiIso A D E K
  columnsThickGenerate : criterionPerfColumnsThickGenerate A D E K

end SerrePositivity.DifferentialGraded.Morita
