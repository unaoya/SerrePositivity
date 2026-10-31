module
public import SerrePositivity.DifferentialGraded.Category.ComplexHomotopyComparison
public import SerrePositivity.DifferentialGraded.Category.FullSubcategory
public import SerrePositivity.PerfectComplex.Perfect.HomotopyCategory

/-! # 既存の有界有限射影複体の全Hom dg enhancement

strictlyPerfectComplexとPerfectHomotopyをそのまま使う。
一対象Aの主Perfとの同定は、別に有限生成・retractを照合して証明する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A]

/-- 既存の有界有限射影複体を対象とし、主Hom複体をそのまま持つ充満dg部分圏。 -/
abbrev StrictPerfectDGComplex := DGFullSubcategory (Complex A) (strictlyPerfectComplex A)

/-- 既存の有限射影対象から全非有界複体へのdg包含。 -/
def strictPerfectDGComplexInclusion : DGFunctor A (StrictPerfectDGComplex A) (Complex A) :=
  dgFullSubcategoryInclusion A (Complex A) (strictlyPerfectComplex A)

/-- 有限射影複体のH⁰包含は充満。 -/
instance strictPerfectDGComplexInclusionHomotopyFull :
    (strictPerfectDGComplexInclusion A).onHomotopy.Full := by
  dsimp [strictPerfectDGComplexInclusion]
  infer_instance

/-- 有限射影複体のH⁰包含は忠実。 -/
instance strictPerfectDGComplexInclusionHomotopyFaithful :
    (strictPerfectDGComplexInclusion A).onHomotopy.Faithful := by
  dsimp [strictPerfectDGComplexInclusion]
  infer_instance

/-- 有限射影dg複体のH⁰から、既存の全複体ホモトピー圏への比較。 -/
def strictPerfectDGComplexToHomotopy : HomotopyCategory A (StrictPerfectDGComplex A) ⥤
    _root_.HomotopyCategory (ModuleCat.{u} A) (.up ℤ) :=
  (strictPerfectDGComplexInclusion A).onHomotopy ⋙ complexHomotopyComparison A

/-- 比較像は元の複体を代表とするので、既存perfectHomotopyPropertyを満たす。 -/
lemma strictPerfectDGComplexToHomotopy_obj_perfect
    (X : HomotopyCategory A (StrictPerfectDGComplex A)) :
    perfectHomotopyProperty A ((strictPerfectDGComplexToHomotopy A).obj X) := by
  let M : StrictPerfectDGComplex A := ForgetEnrichment.to (Complex A) X.as
  exact (perfectHomotopyProperty_quotient A M.val).mpr M.property

/-- 有限射影dg複体のH⁰から既存PerfectHomotopyへの比較。 -/
def strictPerfectDGComplexToPerfect : HomotopyCategory A (StrictPerfectDGComplex A) ⥤
    PerfectHomotopy A :=
  (perfectHomotopyProperty A).lift (strictPerfectDGComplexToHomotopy A)
    (strictPerfectDGComplexToHomotopy_obj_perfect A)

/-- 既存PerfectHomotopyへの比較は充満。全Hom包含と全複体比較の充満性を継承する。 -/
instance strictPerfectDGComplexToPerfectFull : (strictPerfectDGComplexToPerfect A).Full := by
  dsimp [strictPerfectDGComplexToPerfect, strictPerfectDGComplexToHomotopy]
  infer_instance

/-- 既存PerfectHomotopyへの比較は忠実。同じHom複体と境界関係を使う。 -/
instance strictPerfectDGComplexToPerfectFaithful :
    (strictPerfectDGComplexToPerfect A).Faithful := by
  dsimp [strictPerfectDGComplexToPerfect, strictPerfectDGComplexToHomotopy]
  infer_instance

/-- 既存PerfectHomotopyの対象が持つ実際の有限射影代表を選んで、本質的全射性を得る。 -/
instance strictPerfectDGComplexToPerfectEssSurj : (strictPerfectDGComplexToPerfect A).EssSurj where
  mem_essImage X := by
    let P : Complex A := X.obj.as
    have hP : strictlyPerfectComplex A P := (perfectHomotopyProperty_quotient A P).mp X.property
    let M : StrictPerfectDGComplex A := ⟨P, hP⟩
    exact ⟨(toHomotopy A (StrictPerfectDGComplex A)).obj (ForgetEnrichment.of (Complex A) M),
      ⟨(perfectHomotopyProperty A).isoMk (Iso.refl _)⟩⟩

/-- 全Homと実際の有限射影代表により、比較は同値である。 -/
instance strictPerfectDGComplexToPerfectIsEquivalence :
    (strictPerfectDGComplexToPerfect A).IsEquivalence where

/-- 既存PerfectHomotopyの、主Homを持つdg enhancementによるH⁰表示。 -/
def strictPerfectDGComplexHomotopyEquivalence :
    HomotopyCategory A (StrictPerfectDGComplex A) ≌ PerfectHomotopy A :=
  (strictPerfectDGComplexToPerfect A).asEquivalence

end SerrePositivity.DifferentialGraded
