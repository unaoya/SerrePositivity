module

public import SerrePositivity.KST.Spectra.FreeActionEndNaturality
public import SerrePositivity.KST.Spectra.KanCompositeCancellation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorComposition

/-!
概要：自由作用の重みの end は係数の全基点 π_* 同型を保つ。
方針：内部 Hom との自然な同型で比較し、実際の Whitehead 逆を内部 Hom の後合成へ送る。
規約：始域の参照頂点を明示する。
使われ方：Goerss–Jardine VIII §2、HA §1.4.2。群作用の cochain の Ω 条件の比較。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed SSet
open scoped MonoidalClosed Simplicial
open SerrePositivity.InfinityCategories


namespace SerrePositivity.KST.Spectra.FreeActionFamily

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：自由作用の同変 end の係数の π_* 同型は end の全基点 π_* 同型を誘導する。
方針：軌道集合からの内部 Hom への自然な比較を経由する。
規約：G の有限性は不要。始域の係数の頂点を一つ明示する。
使われ方：Goerss–Jardine VIII §2。自由作用の cochain のホモトピー不変性。 -/
lemma endMap_piIsomorphism {G : Type u} [Group G] (S : Type u)
    {B C : Action SSet.{u} G} [KanComplex B.V] [KanComplex C.V]
    (τ : B ⟶ C) (hτ : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism τ.hom) (b : B.V _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap (weight S) (coefficientsMap τ)) := by
  let K := (Functor.const (SimplexCategoryᵒᵖ)).obj S
  let : KanComplex ((ihom K).obj B.V) := inferInstance
  let : KanComplex ((ihom K).obj C.V) := inferInstance
  have hpost := kanPiIsomorphism_of_qCatEquivalence ((ihom K).map τ.hom)
    ((kanPiIsomorphism_homotopyEquivalence_atVertex τ.hom hτ b).isQCatEquivalence.postcompose K)
  have hcomp : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap (weight S) (coefficientsMap τ) ≫ (endIso S C).hom) := by
    rw [endIso_natural]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanPiIsomorphism.of_iso (endIso S B)).comp hpost
  exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism.of_comp hcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanPiIsomorphism.of_iso (endIso S C))

end

end SerrePositivity.KST.Spectra.FreeActionFamily
