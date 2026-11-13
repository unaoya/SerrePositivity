module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictBarThetaNaturality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictBarNormalizedGradedFunctor
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.NormalizedDifferential

/-!
概要：元のstrict自然変換の射が、正規化前後の同じMC項と可換する。
方針：一点評価の全次数の等式を全Homへ戻し、同じ包含・射影の自然性を用いる。
規約：元の正規化の微分を使う。自然性を新たな仮定として課さない。
使われ方：3b-3 R6、正規化barの関手と同じ射影の構成。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite SSet CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
open SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison

variable (A : Type u) [CommRing A] (J : Type) [SmallCategory J]

/-- 元のstrict自然変換とMC項の全Hom上の同じ可換式。 -/
lemma strictBarTheta_naturality
    {F G : J ⥤ ModuleCategory A PUnit.{1}} (η : F ⟶ G) :
    (eHomWhiskerRight (Complex A) (strictBarGradedMap A J η)
      (dgCoherentBarGraded A PUnit.{1} (smallStrictBarDiagram A G))).f 1
        (dgCoherentBarTheta A PUnit.{1} (smallStrictBarDiagram A G)) =
      (eHomWhiskerLeft (Complex A)
        (dgCoherentBarGraded A PUnit.{1} (smallStrictBarDiagram A F))
        (strictBarGradedMap A J η)).f 1
          (dgCoherentBarTheta A PUnit.{1} (smallStrictBarDiagram A F)) := by
  apply moduleHomElement_ext A PUnit.{1}
    (M := ForgetEnrichment.to (Complex A) (dgCoherentBarGraded A PUnit.{1} (smallStrictBarDiagram A F)))
    (N := ForgetEnrichment.to (Complex A) (dgCoherentBarGraded A PUnit.{1} (smallStrictBarDiagram A G)))
  rintro ⟨⟩
  apply Cochain.ext
  intro i j hij
  have hj : j = i + 1 := by omega
  subst j
  simpa only [moduleHomWhiskerRight_apply_π A PUnit.{1}
      (P := dgCoherentBarGraded A PUnit.{1} (smallStrictBarDiagram A G)) (strictBarGradedMap A J η),
    moduleHomWhiskerLeft_apply_π A PUnit.{1}
      (T := dgCoherentBarGraded A PUnit.{1} (smallStrictBarDiagram A F)) (strictBarGradedMap A J η),
    Cochain.zero_cochain_comp_v, Cochain.comp_zero_cochain_v, Cochain.ofHom_v] using!
      strictBarTheta_point_naturality A J η i

/-- 同じ包含・射影で正規化したMC項も、元のstrict自然変換と可換する。 -/
lemma strictBarNormalizedTheta_naturality
    {F G : J ⥤ ModuleCategory A PUnit.{1}} (η : F ⟶ G) :
    (eHomWhiskerRight (Complex A) (strictBarNormalizedGradedMap A J η)
      (dgCoherentBarNormalizedGraded A PUnit.{1} (smallStrictBarDiagram A G))).f 1
        (dgCoherentBarNormalizedTheta A PUnit.{1} (smallStrictBarDiagram A G)) =
      (eHomWhiskerLeft (Complex A)
        (dgCoherentBarNormalizedGraded A PUnit.{1} (smallStrictBarDiagram A F))
        (strictBarNormalizedGradedMap A J η)).f 1
          (dgCoherentBarNormalizedTheta A PUnit.{1} (smallStrictBarDiagram A F)) := by
  apply moduleHomElement_ext A PUnit.{1}
    (M := ForgetEnrichment.to (Complex A) (dgCoherentBarNormalizedGraded A PUnit.{1} (smallStrictBarDiagram A F)))
    (N := ForgetEnrichment.to (Complex A) (dgCoherentBarNormalizedGraded A PUnit.{1} (smallStrictBarDiagram A G)))
  rintro ⟨⟩
  apply Cochain.ext
  intro q r hqr
  have hr : r = q + 1 := by omega
  subst r
  let BF := dgCoherentBarGraded A PUnit.{1} (smallStrictBarDiagram A F)
  let BG := dgCoherentBarGraded A PUnit.{1} (smallStrictBarDiagram A G)
  let NF := dgCoherentBarNormalizedGraded A PUnit.{1} (smallStrictBarDiagram A F)
  let NG := dgCoherentBarNormalizedGraded A PUnit.{1} (smallStrictBarDiagram A G)
  simp only [dgCoherentBarNormalizedTheta,
    moduleHomWhiskerRight_apply_π A PUnit.{1} (M := dgCoherentBarNormalizedGraded A PUnit.{1} (smallStrictBarDiagram A F)) (N := dgCoherentBarNormalizedGraded A PUnit.{1} (smallStrictBarDiagram A G)) (P := dgCoherentBarNormalizedGraded A PUnit.{1} (smallStrictBarDiagram A G)) (strictBarNormalizedGradedMap A J η),
    moduleHomWhiskerLeft_apply_π A PUnit.{1} (T := dgCoherentBarNormalizedGraded A PUnit.{1} (smallStrictBarDiagram A F)) (M := dgCoherentBarNormalizedGraded A PUnit.{1} (smallStrictBarDiagram A F)) (N := dgCoherentBarNormalizedGraded A PUnit.{1} (smallStrictBarDiagram A G)) (strictBarNormalizedGradedMap A J η),
    moduleHomWhiskerRight_apply_π A PUnit.{1} (M := dgCoherentBarNormalizedGraded A PUnit.{1} (smallStrictBarDiagram A G)) (N := dgCoherentBarGraded A PUnit.{1} (smallStrictBarDiagram A G)) (P := dgCoherentBarNormalizedGraded A PUnit.{1} (smallStrictBarDiagram A G)) (dgCoherentBarNormalizedInclusion A PUnit.{1} (smallStrictBarDiagram A G)),
    moduleHomWhiskerLeft_apply_π A PUnit.{1} (T := dgCoherentBarGraded A PUnit.{1} (smallStrictBarDiagram A G)) (M := dgCoherentBarGraded A PUnit.{1} (smallStrictBarDiagram A G)) (N := dgCoherentBarNormalizedGraded A PUnit.{1} (smallStrictBarDiagram A G)) (dgCoherentBarNormalizedProjection A PUnit.{1} (smallStrictBarDiagram A G)),
    moduleHomWhiskerRight_apply_π A PUnit.{1} (M := dgCoherentBarNormalizedGraded A PUnit.{1} (smallStrictBarDiagram A F)) (N := dgCoherentBarGraded A PUnit.{1} (smallStrictBarDiagram A F)) (P := dgCoherentBarNormalizedGraded A PUnit.{1} (smallStrictBarDiagram A F)) (dgCoherentBarNormalizedInclusion A PUnit.{1} (smallStrictBarDiagram A F)),
    moduleHomWhiskerLeft_apply_π A PUnit.{1} (T := dgCoherentBarGraded A PUnit.{1} (smallStrictBarDiagram A F)) (M := dgCoherentBarGraded A PUnit.{1} (smallStrictBarDiagram A F)) (N := dgCoherentBarNormalizedGraded A PUnit.{1} (smallStrictBarDiagram A F)) (dgCoherentBarNormalizedProjection A PUnit.{1} (smallStrictBarDiagram A F)),
    Cochain.zero_cochain_comp_v, Cochain.comp_zero_cochain_v, Cochain.ofHom_v, Category.assoc]
  have hi := congrArg (fun f => ((moduleEvaluation A PUnit.{1} PUnit.unit).map f).f q)
    (strictBarNormalizedGradedMap_inclusion A J η)
  have hp := congrArg (fun f => ((moduleEvaluation A PUnit.{1} PUnit.unit).map f).f (q + 1))
    (strictBarGradedMap_projection A J η)
  simp only [CategoryTheory.Functor.map_comp, HomologicalComplex.comp_f] at hi hp
  rw [reassoc_of% hi, strictBarTheta_point_naturality_assoc, hp]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
