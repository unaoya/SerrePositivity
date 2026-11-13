module
public import SerrePositivity.KST.SConstruction.DGOdotQuotient
public import SerrePositivity.KST.SConstruction.DGSmallPerfectSquareGeneration

/-! # 実 dg 代数四角形の自由生成条件と元の End 包含
概要：左右の実自由生成条件を明示し、同じ実代数四角形の元の End 包含へ接続する。
方針：構成済みの実比較対角に対する生成・Morita 判定を、そのまま特殊化する。
規約：生成条件の供給は DGOdotGenerators で行う。使われ方：D の実自由生成 API の接続先。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "A" => _root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R (DGOdotInput.source d)
local notation "C" => _root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R (DGOdotInput.left d)
local notation "D" => _root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R (DGOdotInput.right d)
local notation "E" => _root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R (DGOdotInput.corner d)
local notation "L" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R (DGOdotInput.top d)
local notation "G" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R (DGOdotInput.side d)
local notation "p" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R (DGOdotInput.lower d)
local notation "q" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R (DGOdotInput.upper d)
local notation "CL" => DGSmallPerfectArrowTarget R (A) (C) (L)
local notation "DR" => DGSmallPerfectArrowTarget R (A) (D) (G)
local notation "I" => dgOdotQuotientInput R d

/-- D の実自由生成 API から供給する、同じ小模型の二つの具体的条件。 -/
structure DGOdotGeneratorConditions : Prop where
  left : modulePerfectOver R (CL)
    {dgSmallPerfectArrowTargetRepresentable R (A) (C) (L)
      ((L).obj (dgOdotInputSourcePoint R d))} = modulePerfect R (CL)
  right : modulePerfectOver R (DR)
    {dgSmallPerfectArrowTargetRepresentable R (A) (D) (G) (dgOdotInputRightPoint R d)} =
      modulePerfect R (DR)

/-- 明示した実自由生成条件の下で、同じ実商への元の End 包含の実 Perf 延長は同値。 -/
lemma dgOdotEndInclusion_isMorita (hgen : DGOdotGeneratorConditions R d) :
    (quasiEquivalencePerfectExtension R (I).endObject (I).quotientObject
      (I).endInclusion).IsEquivalence :=
  dgSmallPerfectSquareEndInclusion_isMorita R (A) (C) (D) (E) (L) (G) (p) (q)
    (dgOdotInput_dg_commutes R d) (dgOdotInputRightPoint R d) (dgOdotInputSourcePoint R d)
    hgen.left hgen.right

/-- 同じ実自由生成条件の下で、元の End 包含の実 dg Perf 延長も準同値。 -/
lemma dgOdotEndInclusion_perfectDG_quasiEquivalence (hgen : DGOdotGeneratorConditions R d) :
    QuasiEquivalence (perfectDGExtension R (I).endObject (I).quotientObject (I).endInclusion) := by
  let := dgOdotEndInclusion_isMorita R d hgen
  exact perfectDGExtension_quasiEquivalence R (I).endObject (I).quotientObject (I).endInclusion

end SerrePositivity.KST.SConstruction
