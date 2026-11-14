module
public import SerrePositivity.KST.NonConnective.DGKappaPerfectSupplyComparison
public import SerrePositivity.DifferentialGraded.Morita.CriterionPerfTriangulated
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Triangles.DGPretriangulatedTria

/-!
概要：同じ実評価 Morita 核と実供給 P を用いて、実小核の perfect 加群を代表対象へ戻す。
方針：元の実評価の全列による回収を、同じ Perf 作用の充満忠実性で反映する。
規約：同じ I に条件付き。一般の dg 圏の前三角性 API を新設しない。
使われ方：K-7 c5 の同じ実小核からその Perf への Yoneda 比較を検証する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] (D : PerfDGInput.{u, max (u + 1) v} R)
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)
local notation "C" => dgKappaResolvedKernelKInput R D I

/-- 概要：同じ I の実小核上の perfect 対象は、同じ実核の代表加群と同型。
方針：実評価の Perf 同値の像を同じ評価列へ戻し、同じ充満忠実な主作用で反映する。
規約：元の P は D-8 e の実供給を使い、I の存在は主張しない。
使われ方：K-7 c5 の同じ native 実核とその Perf の照合。 -/
theorem dgKappaResolvedKernel_perfect_isRepresentable (M : PerfectModuleCategory R (C)) :
    ∃ x : C, Nonempty (M.obj ≅ (triaRepresentable R (C) x).obj) := by
  let P := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaPerfect.dgKappaPerfectInput R D I
  let W := dgKappaResolvedEvaluationKernel_perfectEquivalence R D I P
  let Y := W.equivalence.functor.obj M
  obtain ⟨c, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (perfectDGModuleToPerfect R D Set.univ) Y
  let N : PerfectDGModule R D := ForgetEnrichment.to (Complex R) c.as
  obtain ⟨x, ⟨ex⟩⟩ := dgKappaResolvedEvaluationBimodule_covers R D I P N
  let Q : PerfectModuleCategory R (C) :=
    ⟨(triaRepresentable R (C) x).obj,
      modulePerfectOver_representable R (C) x (Set.mem_univ _)⟩
  have er : (Morita.kernelDerivedTensor R (C) D
      (dgKappaResolvedEvaluationKernel R D I)).obj Q.obj ≅
      (moduleToDerived R D).obj (ForgetEnrichment.of (Complex R)
        ((dgKappaResolvedEvaluationBimodule R D I).rightAt x)) :=
    (Morita.criterionPerfYonedaMainDerivedIso R (C) D
      (dgKappaResolvedEvaluationBimodule R D I)).app (ForgetEnrichment.of (Complex R) x)
  have ey : (moduleToDerived R D).obj (ForgetEnrichment.of (Complex R) N.val) ≅ Y.obj :=
    ((moduleToHomotopyDerivedIso R D).app (ForgetEnrichment.of (Complex R) N.val)).symm ≪≫
      (perfectModuleInclusion R D Set.univ).mapIso e
  have eqy : (W.equivalence.functor.obj Q).obj ≅ Y.obj :=
    (W.comparison.app Q).symm ≪≫ er ≪≫ ex ≪≫ ey
  have eF : W.equivalence.functor.obj M ≅ W.equivalence.functor.obj Q :=
    (modulePerfect R D).isoMk eqy.symm
  exact ⟨x, ⟨(perfectModuleInclusion R (C) Set.univ).mapIso
    (W.equivalence.functor.preimageIso eF)⟩⟩

/-- 概要：同じ実小核は、実供給 P と元の評価 Morita 比較により dg 前三角である。
方針：実小核の有限 cell 対象を同じ perfect 対象として読み、構成済みの代表対象へ戻す。
規約：同じ I に条件付き。任意の平坦商核の一般 API としては主張しない。
使われ方：D 正本の dg Yoneda 完備化を同じ実小核へ適用する。 -/
theorem dgKappaResolvedKernel_isDGPretriangulated : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R (C) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.isDGPretriangulated_of_tria_representable R (C)
  intro X
  let M : PerfectModuleCategory R (C) :=
    ⟨X.obj, (derivedFiniteCellOver R (C) Set.univ).le_retractClosure _ X.property⟩
  obtain ⟨x, ⟨e⟩⟩ := dgKappaResolvedKernel_perfect_isRepresentable R D I M
  exact ⟨x, ⟨(derivedFiniteCellOver R (C) Set.univ).isoMk e⟩⟩

end SerrePositivity.KST.NonConnective
