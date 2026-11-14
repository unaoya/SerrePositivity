module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CompactnessAndPresentability.SmallPerfectEvaluationEquivalence

/-!
概要：実評価同値に沿って単一の自由生成元を戻す。
方針：既存の実評価・導来 tensor と完全加群の厚い閉包を使う。
規約：生成性の結論を追加仮定にしない。使われ方：β5 と K-S• の実自由代表。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
local notation "C" => SmallPerfectDGModuleOver R D Set.univ

lemma smallPerfectEvaluation_singleton_generates (b : C) (d : D)
    (hD : modulePerfectOver R D {d} = modulePerfect R D)
    (eb : (moduleToDerived R D).obj (ForgetEnrichment.of (Complex R)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.smallPerfectEvaluationBimodule R D).obj b)) ≅
        (moduleToDerived R D).obj (ForgetEnrichment.of (Complex R) (representable R d))) :
    modulePerfectOver R (C) {b} = modulePerfect R (C) := by
  let K := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.smallPerfectEvaluationKernel R D
  let T := Morita.kernelDerivedTensor R (C) D K
  let := Morita.criterionPerfKernelCommShift R (C) D K
  let := Morita.criterionPerfKernelIsTriangulated R (C) D K
  let W := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.smallPerfectEvaluationKernel_perfectEquivalence R D
  let Inc : modulePerfectOver R (C) {b} ≤ modulePerfect R (C) :=
    modulePerfectOver_mono R (C) (Set.subset_univ _)
  let J : PerfectModuleCategoryOver R (C) {b} ⥤ PerfectModuleCategory R (C) :=
    (modulePerfect R (C)).lift (perfectModuleInclusion R (C) {b})
      (fun x ↦ Inc _ x.property)
  let : (perfectModuleInclusion R (C) {b}).Full :=
    inferInstanceAs ((modulePerfectOver R (C) {b}).ι.Full)
  let : (perfectModuleInclusion R (C) {b}).Faithful :=
    inferInstanceAs ((modulePerfectOver R (C) {b}).ι.Faithful)
  let : J.Full := by dsimp [J]; infer_instance
  let : J.Faithful := by dsimp [J]; infer_instance
  let : (perfectModuleInclusion R D Set.univ).Full :=
    inferInstanceAs ((modulePerfect R D).ι.Full)
  let : (perfectModuleInclusion R D Set.univ).Faithful :=
    inferInstanceAs ((modulePerfect R D).ι.Faithful)
  let G := perfectModuleInclusion R (C) Set.univ ⋙ T
  let gFF : G.FullyFaithful :=
    (Functor.FullyFaithful.ofFullyFaithful
      (W.equivalence.functor ⋙ perfectModuleInclusion R D Set.univ)).ofIso W.comparison.symm
  let H := perfectModuleInclusion R (C) {b} ⋙ T
  have hFF : H.FullyFaithful := by
    change (J ⋙ G).FullyFaithful
    exact (Functor.FullyFaithful.ofFullyFaithful J).comp gFF
  let : H.Full := hFF.full
  let : H.Faithful := hFF.faithful
  let : H.essImage.IsStableUnderRetracts := Morita.criterionPerfEssImage_retract_closed H
  have hall : modulePerfect R D ≤ H.essImage := by
    rw [← hD]
    apply modulePerfectOver_le_of_generators R D H.essImage {d}
    intro x hx
    have hx : x = d := Set.mem_singleton_iff.mp hx
    subst x
    refine ⟨⟨_, modulePerfectOver_representable R (C) b (Set.mem_singleton b)⟩, ⟨?_⟩⟩
    exact Morita.kernelDerivedColumnActionIso R (C) D K b ≪≫
      Morita.kernelDerivedColumnComputation R (C) D b
        (BimoduleCategory.of R D (C) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.smallPerfectEvaluationBimodule R D)) ≪≫ eb
  apply le_antisymm Inc
  intro X hX
  have hTX : modulePerfect R D (T.obj X) :=
    (Morita.kernelColumnsPerfect_iff_preservesPerfect R (C) D K).mp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.smallPerfectEvaluationKernel_columnsPerfect R D) X hX
  obtain ⟨Y, ⟨eY⟩⟩ := hall _ hTX
  let Y' : PerfectModuleCategory R (C) := ⟨Y.obj, Inc _ Y.property⟩
  let X' : PerfectModuleCategory R (C) := ⟨X, hX⟩
  let e : Y' ≅ X' := gFF.preimageIso eY
  exact (modulePerfectOver R (C) {b}).prop_of_iso
    ((perfectModuleInclusion R (C) Set.univ).mapIso e) Y.property

end SerrePositivity.InfinityCategories.Project.DerivedCategories
