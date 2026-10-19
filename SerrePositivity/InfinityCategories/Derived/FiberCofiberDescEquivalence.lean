module
public import SerrePositivity.InfinityCategories.Derived.FiberCofiberConeIso
public import SerrePositivity.InfinityCategories.Derived.CoconeConeContraction

/-! # 標準 fiber の cofiber 比較はホモトピー同値

概要：明示的な cofiber 比較を cocone 射影の cone の縮約と同定する。
方針：直和の符号同型を cone に移し、二つの包含で写像を比較する。
規約：二脚・ホモトピーを保持する元の比較射に同値性を与える。使われ方：D7 の双対側。
-/
@[expose] public section
open CategoryTheory Limits SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.DGNerve
open CochainComplex HomComplex
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
variable {S : Type u} [CommRing S] {B C D : Complex S}
namespace SerrePositivity.InfinityCategories
/-- 明示的比較は符号修正同型の後の cocone-cone 縮約。 -/
lemma fiberCofiberDesc_eq (g : B ⟶ D) (h : C ⟶ D) :
    fiberCofiberDesc g h = (fiberInputConeIso g h).hom ≫ coconeConeDesc (fiberDifference g h) := by
  apply HomologicalComplex.hom_ext
  intro p
  apply mappingCone.ext_from
    (cofiberDifference (pullbackProjectionB g h) (pullbackProjectionC g h)) (p + 1) p rfl
  · simp [fiberCofiberDesc, fiberInputConeIso, mappingCone.map, coconeConeDesc,
      fiberNullHomotopy_eq_neg_mappingCocone_snd]
  · simp only [fiberCofiberDesc, fiberInputConeIso, mappingCone.map, coconeConeDesc,
      HomologicalComplex.comp_f, Category.assoc, mappingCone.inr_f_desc_f,
      mappingCone.inr_f_desc_f_assoc]
    exact (congrArg (fun k => k.f p) (fiberSignDifference_sum g h)).symm

/-- 二射影の cofiber と元の終域のホモトピー同値。 -/
def fiberCofiberHomotopyEquiv (g : B ⟶ D) (h : C ⟶ D) :
    HomotopyEquiv (pushoutCofiber (pullbackProjectionB g h) (pullbackProjectionC g h)) D :=
  (HomotopyEquiv.ofIso (fiberInputConeIso g h)).trans
    (coconeConeHomotopyEquiv (fiberDifference g h))

/-- ホモトピー同値の順射は元の明示的比較そのもの。 -/
lemma fiberCofiberHomotopyEquiv_hom (g : B ⟶ D) (h : C ⟶ D) :
    (fiberCofiberHomotopyEquiv g h).hom = fiberCofiberDesc g h :=
  (fiberCofiberDesc_eq g h).symm

/-- 標準 fiber の cofiber から終域への明示的比較はホモトピー同値。 -/
lemma fiberCofiberDesc_homotopyEquivalence (g : B ⟶ D) (h : C ⟶ D) :
    HomologicalComplex.homotopyEquivalences (ModuleCat.{u} S) (.up ℤ)
      (fiberCofiberDesc g h) :=
  ⟨fiberCofiberHomotopyEquiv g h, fiberCofiberHomotopyEquiv_hom g h⟩

/-- 標準 fiber の cofiber から終域への明示的比較は擬同型。 -/
lemma fiberCofiberDesc_quasiIso (g : B ⟶ D) (h : C ⟶ D) : QuasiIso (fiberCofiberDesc g h) := by
  rw [← fiberCofiberHomotopyEquiv_hom]
  infer_instance

end SerrePositivity.InfinityCategories
