module
public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.ProjectiveBoundaryContraction
public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.ProjectiveHornWeakFactorization
public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.ProjectiveWeightRestriction
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithfulCalculus

/-!
概要：射影cofibrantな元の重み間の成分ごとの弱同値は、Kan係数への制限でホモトピー同値。
方針：まずKan標的への自由ホーン分解を二つの既知の制限へ分け、一般標的は同じホーン置換で移す。
規約：IS-W2 R03a.1の型つきの中間定理。SSetモデル構造は仮定しない。
使われ方：元のBK重みと指定された一点重みの同じ一つの比較射。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.SSet _root_.HomotopicalAlgebra
open _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open scoped _root_.SSet.modelCategoryQuillen
variable (I : Type u) [SmallCategory I]

/-- 元の重みの終射の自由ホーン分解の中間重みは、各値がKan。 -/
theorem projectiveHornReplacement_kan (W : I ⥤ SSet.{u}) (i : I) :
    SSet.KanComplex ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.projectiveHornFactorization I (terminal.from W)).Z.obj i) := by
  let p := (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.projectiveHornFactorization I (terminal.from W)).p.app i
  have hp := _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.projectiveHornFactorization_p_fibration I (terminal.from W) i
  exact (isFibrant_iff_of_isTerminal p
    (terminalIsTerminal.isTerminalObj ((CategoryTheory.evaluation I SSet.{u}).obj i) _)).mpr hp

/-- 元の標的重みが各値でKanの場合の、同じ弱同値の制限のホモトピー同値。 -/
theorem weightedSectionsPre_homotopyEquivalence_of_projective_cofibrant_kan_target
    (V W : I ⥤ SSet.{u}) (f : V ⟶ W)
    (hV : (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.boundaries I).rlp.llp (initial.to V))
    (hW : (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.boundaries I).rlp.llp (initial.to W))
    (hf : ∀ i, IsWeakHomotopyEquivalence (f.app i))
    (hWK : ∀ i, SSet.KanComplex (W.obj i))
    (H : I ⥤ SSet.{u}) (hH : ∀ i, SSet.KanComplex (H.obj i)) :
    IsSimplicialHomotopyEquivalence (weightedSectionsPre f H) := by
  let d := _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.projectiveHornFactorization I f
  have hZ := _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.projectiveHornFactorization_cofibrant I f hV
  letI vKan := _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weightedSections_kanComplex_of_projective_cofibrant I V hV H hH
  letI wKan := _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weightedSections_kanComplex_of_projective_cofibrant I W hW H hH
  letI zKan := _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weightedSections_kanComplex_of_projective_cofibrant I d.Z hZ H hH
  have hi := _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weightedSectionsPre_homotopyEquivalence_of_projectiveHorn d.i d.hi hV hZ hH
  have hp := _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weightedSectionsPre_homotopyEquivalence_of_projectiveBoundary I d.p
    (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.projectiveHornFactorization_p_boundary_rlp I f hf hWK) hZ hW H
  have hc := hp.comp hi
  rw [← weightedSectionsPre_comp, d.fac] at hc
  exact hc

/-- R03a.1：元の射影cofibrantな重みの成分ごとの弱同値は、全Kan係数で制限のホモトピー同値。 -/
theorem weightedSectionsPre_homotopyEquivalence_of_projective_cofibrant
    (V W : I ⥤ SSet.{u}) (f : V ⟶ W)
    (hV : (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.boundaries I).rlp.llp (initial.to V))
    (hW : (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.boundaries I).rlp.llp (initial.to W))
    (hf : ∀ i, IsWeakHomotopyEquivalence (f.app i))
    (H : I ⥤ SSet.{u}) (hH : ∀ i, SSet.KanComplex (H.obj i)) :
    IsSimplicialHomotopyEquivalence (weightedSectionsPre f H) := by
  let d := _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.projectiveHornFactorization I (terminal.from W)
  have hR := _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.projectiveHornFactorization_cofibrant I (terminal.from W) hW
  have hf' (i : I) : IsWeakHomotopyEquivalence ((f ≫ d.i).app i) :=
    (hf i).comp (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.projectiveHornFactorization_i_weak I (terminal.from W) i)
  have hc := _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weightedSectionsPre_homotopyEquivalence_of_projective_cofibrant_kan_target
    I V d.Z (f ≫ d.i) hV hR hf' (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.projectiveHornReplacement_kan I W) H hH
  have hi := _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weightedSectionsPre_homotopyEquivalence_of_projectiveHorn d.i d.hi hW hR hH
  letI vKan := _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weightedSections_kanComplex_of_projective_cofibrant I V hV H hH
  letI wKan := _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weightedSections_kanComplex_of_projective_cofibrant I W hW H hH
  letI rKan := _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weightedSections_kanComplex_of_projective_cofibrant I d.Z hR H hH
  rw [weightedSectionsPre_comp] at hc
  exact hi.cancel_left hc

end SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight
