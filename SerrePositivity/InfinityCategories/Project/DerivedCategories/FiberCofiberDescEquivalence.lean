module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FiberCofiberConeIso
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CoconeConeContraction

/-! # 標準 fiber の cofiber 比較はホモトピー同値

概要：明示的な cofiber 比較を cocone 射影の cone の縮約と同定する。
方針：直和の符号同型を cone に移し、二つの包含で写像を比較する。
規約：二脚・ホモトピーを保持する元の比較射に同値性を与える。使われ方：D7 の双対側。
-/
@[expose] public section
open CategoryTheory Limits SerrePositivity.DifferentialGraded

open CochainComplex HomComplex
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
variable {S : Type u} [CommRing S] {B C D : Complex S}
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
/-- 明示的比較は符号修正同型の後の cocone-cone 縮約。 -/
lemma fiberCofiberDesc_eq (g : B ⟶ D) (h : C ⟶ D) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fiberCofiberDesc g h = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fiberInputConeIso g h).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.coconeConeDesc (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberDifference g h) := by
  apply HomologicalComplex.hom_ext
  intro p
  apply mappingCone.ext_from
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberDifference (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackProjectionB g h) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackProjectionC g h)) (p + 1) p rfl
  · simp [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fiberCofiberDesc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fiberInputConeIso, mappingCone.map, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.coconeConeDesc,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fiberNullHomotopy_eq_neg_mappingCocone_snd]
  · simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fiberCofiberDesc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fiberInputConeIso, mappingCone.map, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.coconeConeDesc,
      HomologicalComplex.comp_f, Category.assoc, mappingCone.inr_f_desc_f,
      mappingCone.inr_f_desc_f_assoc]
    exact (congrArg (fun k => k.f p) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fiberSignDifference_sum g h)).symm

/-- 二射影の cofiber と元の終域のホモトピー同値。 -/
def fiberCofiberHomotopyEquiv (g : B ⟶ D) (h : C ⟶ D) :
    HomotopyEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutCofiber (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackProjectionB g h) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackProjectionC g h)) D :=
  (HomotopyEquiv.ofIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fiberInputConeIso g h)).trans
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.coconeConeHomotopyEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberDifference g h))

/-- ホモトピー同値の順射は元の明示的比較そのもの。 -/
lemma fiberCofiberHomotopyEquiv_hom (g : B ⟶ D) (h : C ⟶ D) :
    (fiberCofiberHomotopyEquiv g h).hom = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fiberCofiberDesc g h :=
  (fiberCofiberDesc_eq g h).symm

/-- 標準 fiber の cofiber から終域への明示的比較はホモトピー同値。 -/
lemma fiberCofiberDesc_homotopyEquivalence (g : B ⟶ D) (h : C ⟶ D) :
    HomologicalComplex.homotopyEquivalences (ModuleCat.{u} S) (.up ℤ)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fiberCofiberDesc g h) :=
  ⟨fiberCofiberHomotopyEquiv g h, fiberCofiberHomotopyEquiv_hom g h⟩

/-- 標準 fiber の cofiber から終域への明示的比較は擬同型。 -/
lemma fiberCofiberDesc_quasiIso (g : B ⟶ D) (h : C ⟶ D) : QuasiIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fiberCofiberDesc g h) := by
  rw [← fiberCofiberHomotopyEquiv_hom]
  infer_instance

end SerrePositivity.InfinityCategories.Project.DerivedCategories
