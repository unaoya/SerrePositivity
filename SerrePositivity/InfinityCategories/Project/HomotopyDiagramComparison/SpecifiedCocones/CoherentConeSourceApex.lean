module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.CoherentConeSourceFamily
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.CosliceSourceIdentity

/-!
概要：錐全体上の明示的な豊穣 Hom の族は、頂点で標準の Hom 比較を与える。
方針：錐の頂点での標準切断を恒等射と同定し、coslice の前合成の単位計算を適用する。
規約：局所 Kan 性・錐の極限性・頂点評価の逆の選択を用いない。
使われ方：HTT 4.2.4.1 の coend 余錐の普遍性の頂点条件。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
variable {C : Type v} [Category.{u} C] [SimplicialCategory C]
  {K : SSet.{max u v}} {p : K ⟶ SimplicialNerve C}

/-- 頂点を正規化した錐全体の標準切断の頂点制限も、恒等射の coslice 点になる。 -/
lemma coherentConeSourceSectionAt_apex (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) (z : C)
    (hz : c.vertex = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex z) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{max u v}) K ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentConeSourceSectionAt c z hz =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cosliceIdentityPoint (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex z) := by
  have ht {a b : (SimplicialNerve C) _⦋0⦌} (h : a = b) :
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cosliceIdentityPoint a ≫ eqToHom (congrArg
        (fun w ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (SSet.yonedaEquiv.symm w)) h) = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cosliceIdentityPoint b := by
    cases h
    exact Category.comp_id _
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentConeSourceSectionAt, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneIdentityCosliceSection_apex, ht hz]

/-- 明示的な錐全体の Hom の族の頂点評価は、標準の coslice fiber 比較そのもの。 -/
lemma coherentConeSourceFamily_evaluation (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) (z : C)
    (hz : c.vertex = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex z) (x : C) :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentConeSourceFamily c z hz x ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.coherentConeApexEvaluation c z hz x =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentCosliceFiberComparison x z := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex x)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex z)
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.coherentConeApexEvaluation_ι,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.relativeFunctorUncurry_at_vertex, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentConeSourceFamily_uncurry,
    ← Category.assoc, lift_whiskerRight, SSet.const_comp]
  have hv : (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentConeSourceSectionAt c z hz).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.joinApexVertex K) =
      SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cosliceIdentityPoint (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex z)) := by
    have h := congrArg (fun f ↦ SSet.yonedaEquiv f)
      (coherentConeSourceSectionAt_apex c z hz)
    have hj : SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{max u v}) K) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.joinApexVertex K := by
      change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{max u v}) K).app (Opposite.op ⦋0⦌)
        (SSet.yonedaEquiv (𝟙 Δ[0])) = _
      congr 1
      apply stdSimplex.objEquiv.injective
      apply SimplexCategory.Hom.ext
      apply OrderHom.ext
      funext i
      exact (Fin.eq_zero _).trans (Fin.eq_zero _).symm
    simpa only [SSet.yonedaEquiv_comp, hj] using h
  rw [hv, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.coherentCosliceSourcePrecomposition_identity]

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
