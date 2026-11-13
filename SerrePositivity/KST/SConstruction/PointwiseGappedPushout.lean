module
public import SerrePositivity.KST.SConstruction.PointwiseDiagramPushout
public import SerrePositivity.KST.SConstruction.SConstructionStability
public import SerrePositivity.KST.SConstruction.GappedIso

/-! # gapped な span の点ごとの押し出し
概要：同じ点ごとの押し出し選択の apex は gapped。
方針：安定な S_n 内の押し出しと包含後の普遍四角形を比較する。
規約：与えた元の選択を保持する。使われ方：McCarthy の ρ の gapped 性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：gapped 図式の span の選んだ点ごとの押し出し頂点は gapped。
方針：S_n 内の普遍四角形と関手圏の選んだ普遍四角形を同じ span 上で比較する。
規約：全入力の gapped 性から結論する。使われ方：raw ρ の持ち上げ。 -/
lemma pointwisePushoutApex_isGapped {n : ℕ} {D : SSet.{u}} [Quasicategory D] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable D]
    (F : (horn 2 0 : SSet.{u}) ⊗ arNerve n ⟶ D)
    (hg : ∀ a : (horn 2 0 : SSet.{u}) _⦋0⦌, IsGapped
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (arNerve n) D).symm
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv (arNerve n) (horn 2 0) D (curry F)).app
          (Opposite.op ⦋0⦌) a))) :
    IsGapped (pointwisePushoutApex (curry F)) := by
  let : Quasicategory (diagramSpace n D) :=
    inferInstanceAs (Quasicategory ((ihom (arNerve n)).obj D))
  let p := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv (arNerve n) (horn 2 0) D (curry F)
  let q : (horn 2 0 : SSet.{u}) ⟶ sConstruction n D := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift _ p hg
  obtain ⟨R, hR, hRp⟩ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.exists_stable_pushoutSquare_of_span q
  let Q := chosenDiagramPushout (curry F)
  have hs : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (R ≫ (gappedSubcomplex n D).ι) = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan Q := by
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan R) ≫ (gappedSubcomplex n D).ι = _
    rw [hR]
    exact (chosenDiagramPushout_span (curry F)).symm
  let e := pushoutSquareIsoOfSpanIso (R ≫ (gappedSubcomplex n D).ι) Q
    ((gappedInclusion_preservesSConstructionData n D).2 R hRp)
    (chosenDiagramPushout_isPushout _) (by rw [hs])
  have ea := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map e (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
    (stdSimplex.obj₀Equiv.symm (1 : Fin 2), stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex] at ea
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((gappedSubcomplex n D).ι.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex R 1 1))
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (chosenDiagramPushout (curry F)) 1 1) at ea
  rw [chosenDiagramPushout_apex] at ea
  apply (gappedDiagram_isGapped (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex R 1 1)).of_functorIso
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (gappedDiagram (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex R 1 1))) _
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (gappedDiagram (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex R 1 1)) =
      (gappedSubcomplex n D).ι.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex R 1 1) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ D).apply_symm_apply _
  rw [he]
  exact ea

end SerrePositivity.KST.SConstruction
