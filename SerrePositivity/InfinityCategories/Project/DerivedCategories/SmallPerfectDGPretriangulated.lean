module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.SmallPerfectRelativeEvaluationImage
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGPretriangulatedTria
/-!
概要：指定生成集合の実小 Perf 模型の dg 前三角性を証明する。
方針：実評価の完全忠実な Perf 作用で tria の各対象を同じ小代表の表現可能対象へ戻す。
規約：全 Perf の Small 性を仮定せず、元の小 dg 模型と全 Hom を保持する。
使われ方：D-18。D2 の小 Perf gluing への thick 核判定の適用。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D] (S : Set D)
local notation "C" => SmallPerfectDGModuleOver R D S

lemma smallPerfectDGModuleOver_tria_isRepresentable (X : TriaCategory R (C)) :
    ∃ c : C, Nonempty (X ≅ triaRepresentable R (C) c) := by
  let T := Morita.kernelDerivedTensor R (C) D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.smallPerfectRelativeEvaluationKernel R D S)
  let F := Morita.perfectDerivedKernelAction R (C) D
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.smallPerfectRelativeEvaluationKernel R D S)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.smallPerfectRelativeEvaluation_columnsPerfect R D S)
  let PX : PerfectModuleCategory R (C) :=
    ⟨X.obj, (derivedFiniteCellOver R (C) Set.univ).le_retractClosure _ X.property⟩
  have hX : modulePerfectOver R D S (T.obj PX.obj) :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.smallPerfectRelativeEvaluation_preservesPerfectOver R D S PX.property
  obtain ⟨Y, ⟨eY⟩⟩ := Functor.EssSurj.mem_essImage (smallPerfectDGModuleToPerfect R D S)
    (⟨T.obj PX.obj, hX⟩ : PerfectModuleCategoryOver R D S)
  let c : C := ForgetEnrichment.to (Complex R) Y.as
  let Q : PerfectModuleCategory R (C) :=
    ⟨(triaRepresentable R (C) c).obj, modulePerfectOver_representable R (C) c (Set.mem_univ _)⟩
  let ec : T.obj Q.obj ≅ (perfectModuleInclusion R D S).obj
      ((smallPerfectDGModuleToPerfect R D S).obj Y) :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.smallPerfectRelativeEvaluation_representableIso R D S c ≪≫
      ((moduleToHomotopyDerivedIso R D).app (ForgetEnrichment.of (Complex R) c.val.val)).symm
  let eD : T.obj PX.obj ≅ T.obj Q.obj :=
    ((perfectModuleInclusion R D S).mapIso eY).symm ≪≫ ec.symm
  let eF : F.obj PX ≅ F.obj Q := (modulePerfect R D).isoMk eD
  let e := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.smallPerfectRelativeEvaluation_perfectFullyFaithful R D S).preimageIso eF
  exact ⟨c, ⟨(derivedFiniteCellOver R (C) Set.univ).isoMk
    ((perfectModuleInclusion R (C) Set.univ).mapIso e)⟩⟩

lemma smallPerfectDGModuleOver_isDGPretriangulated :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R (SmallPerfectDGModuleOver R D S) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.isDGPretriangulated_of_tria_representable R (C)
    (smallPerfectDGModuleOver_tria_isRepresentable R D S)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
