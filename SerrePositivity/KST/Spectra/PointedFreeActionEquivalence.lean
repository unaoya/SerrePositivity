module

public import SerrePositivity.KST.Spectra.FreeActionEndEquivalence
public import SerrePositivity.KST.Spectra.PointedWeightedEndMap

/-!
概要：自由作用の点つき end による係数の全基点 π_* 同型の保存。
方針：忘却した end の自然な同型と自由作用の通常の end の同型保存を使う。
規約：係数の射は基点を保つ厳密な同変射。
使われ方：Goerss–Jardine VIII §2、HA §1.4.2。群作用の cochain の各次数のホモトピー比較。
-/

@[expose] public section

universe u

open CategoryTheory SSet


namespace SerrePositivity.KST.Spectra.FreeActionFamily

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

instance pointedFreeEnd_kanComplex {G : Type u} [Group G] (S : Type u)
    (B : Action PointedSimplicialSet.{u} G) [KanComplex B.V.right] :
    KanComplex (PointedWeightedEnd.obj (weight S) (pointedCoefficients B)).right :=
  pointedEnd_kanComplex S B

/-- 概要：点つき係数の同変射が誘導する作用図式の自然変換。
方針：作用と一対象圏上の図式の同値を適用して小さな圏へ移す。
規約：各成分は元の点つき射。
使われ方：Goerss–Jardine VIII §2。自由作用の点つき end の係数の射。 -/
def pointedCoefficientsMap {G : Type u} [Group G]
    {B C : Action PointedSimplicialSet.{u} G} (τ : B ⟶ C) :
    pointedCoefficients B ⟶ pointedCoefficients C :=
  Functor.whiskerLeft AsSmall.down (Action.FunctorCategoryEquivalence.functor.map τ)

/-- 概要：自由作用の点つき end は係数の全基点 π_* 同型を保つ。
方針：係数の基点を参照頂点にし、忘却比較の自然性で通常の end の結果を移す。
規約：群の有限性は不要。
使われ方：Goerss–Jardine VIII §2、HA §1.4.2。cochain の各次数の同型保存。 -/
lemma pointedEndMap_piIsomorphism {G : Type u} [Group G] (S : Type u)
    {B C : Action PointedSimplicialSet.{u} G} [KanComplex B.V.right] [KanComplex C.V.right]
    (τ : B ⟶ C) (hτ : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism τ.hom.right) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism
      (X := (PointedWeightedEnd.obj (weight S) (pointedCoefficients B)).right)
      (Y := (PointedWeightedEnd.obj (weight S) (pointedCoefficients C)).right)
      (PointedWeightedEnd.map (weight S) (pointedCoefficientsMap τ)).right := by
  let B₀ := (PointedSimplicialSet.forget.mapAction G).obj B
  let C₀ := (PointedSimplicialSet.forget.mapAction G).obj C
  let : KanComplex B₀.V := inferInstanceAs (KanComplex B.V.right)
  let : KanComplex C₀.V := inferInstanceAs (KanComplex C.V.right)
  let : KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections (weight S)
      (pointedCoefficients B ⋙ PointedSimplicialSet.forget)) := end_kanComplex S B₀
  let : KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections (weight S)
      (pointedCoefficients C ⋙ PointedSimplicialSet.forget)) := end_kanComplex S C₀
  have hn := endMap_piIsomorphism S ((PointedSimplicialSet.forget.mapAction G).map τ) hτ
    (PointedSimplicialSet.basepoint B.V)
  have hc : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism
      ((PointedWeightedEnd.map (weight S) (pointedCoefficientsMap τ)).right ≫
        (PointedWeightedEnd.underlyingIso (weight S) (pointedCoefficients C)).hom) := by
    rw [PointedWeightedEnd.underlyingIso_natural]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanPiIsomorphism.of_iso
      (PointedWeightedEnd.underlyingIso (weight S) (pointedCoefficients B))).comp hn
  exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism.of_comp hc (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanPiIsomorphism.of_iso
    (PointedWeightedEnd.underlyingIso (weight S) (pointedCoefficients C)))

end

end SerrePositivity.KST.Spectra.FreeActionFamily
