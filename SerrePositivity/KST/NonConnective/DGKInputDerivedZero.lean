module
public import SerrePositivity.KST.NonConnective.DGKInputPerfectZero
public import SerrePositivity.DifferentialGraded.Endomorphism.Scalar.HomComparison
public import SerrePositivity.DifferentialGraded.Derived.Basic

/-!
概要：固定 ν が零なら、同じ元 dg 入力の主導来圏の全対象は零。
方針：恒等関手の零自然変換の同型軌跡へ元の局所生成を適用する。
規約：主導来圏の零性を追加仮定にしない。
使われ方：K-7 f の実懸垂反復での零保存。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] (A : PerfDGInput.{u, max (u + 1) v} R)
  (hA : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory (dgKInputStableValue R A))
include hA

/-- 同じ主導来圏は固定 ν の零性だけから全対象が零となる。 -/
theorem dgKInputDerived_isZero (X : DerivedModuleCategory R A) : IsZero X := by
  let G := 𝟭 (DerivedModuleCategory R A)
  let α : 𝟭 (DerivedModuleCategory R A) ⟶ G := 0
  let : NatTrans.CommShift α ℤ := ⟨fun _ => by ext X; simp [α]⟩
  let P := derivedNatTransIsoLocus R A G α
  have hX : P X := by
    apply moduleLocalizing_all R A P
    · intro J F hF
      exact derivedNatTransIsoLocus_coproduct R A G α F hF
    · intro Y hY
      have hz : IsZero Y := (perfectModuleInclusion R A Set.univ).map_isZero
        (dgKInputClassicalPerfect_isZero R A hA ⟨Y, hY⟩)
      exact hz.isIso hz _
  let : IsIso (0 : X ⟶ X) := hX
  exact IsZero.of_epi_zero X X

omit hA in
/-- 同じ主導来圏の全対象が零なら、元の固定 ν も零。 -/
theorem dgKInputStableValue_isZero_of_derived
    (hD : ∀ X : DerivedModuleCategory R A, IsZero X) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory (dgKInputStableValue R A) := by
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModulePerfectInfinityCategory_isStable R A
  have h0 (M : PerfectDGModule R A) : IsZero
      ((toHomotopy R (PerfectDGModule R A)).obj (ForgetEnrichment.of (Complex R) M)) := by
    let H := perfectDGModuleToDerived R A Set.univ
    let X := (toHomotopy R (PerfectDGModule R A)).obj (ForgetEnrichment.of (Complex R) M)
    exact IsZero.of_full_of_faithful_of_isZero H X (hD (H.obj X))
  have hN (z : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (PerfectDGModule R A)) _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex z := by
    let w := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.chosenZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (PerfectDGModule R A))
    obtain ⟨M, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.symm.surjective z
    obtain ⟨N, hN⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.symm.surjective w.vertex
    have hn : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (PerfectDGModule R A))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex N) := by
      have he : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex N = w.vertex := hN
      exact he.symm ▸ w.isZero
    exact hn.of_vertexIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVertexIsoOfH0 R (PerfectDGModule R A) ((h0 N).iso (h0 M)))
  let e := presentedPerfectDGQCatEvaluationEquivalence R A
  let : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor e.inv := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_isQCatEquivalence e.symm.isQCatEquivalence
  intro z
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesZero (F := e.inv) _ (hN (e.hom.app _ z))).of_vertexIso
    (e.homInvIso.app z)

end SerrePositivity.KST.NonConnective
