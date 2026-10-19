module

public import SerrePositivity.InfinityCategories.F1.LeftTransportRepresentation

/-!
概要：transport representation の底の任意の射への制限。
方針：底上の比較を引き戻し、unstraightening の底変換同型で移す。
規約：分類図式と pointed space への全空間の射をともに厳密に保つ。
使われ方：Kerodon Theorem 5.6.5.12、境界上で固定する表現の制限。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

attribute [local instance] vertexFiber_kanComplex_of_leftFibration

local instance representationRestrictionPullbackLeftFibration {E B D : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (g : D ⟶ B) : LeftFibration (pullback.snd p g) :=
  ⟨leftFibrations.pullback_snd p g (LeftFibration.mem (p := p))⟩

/-- 概要：任意の底変換で transport representation を制限する。
方針：比較の fiber の同値性を引き戻し、unstraightening の底変換同型を合成する。
規約：境界など quasicategory でない底にも適用できる。
使われ方：Kerodon §5.6.5、指定された境界表現を比較する制限作用。 -/
noncomputable def LeftTransportRepresentation.restrict {E B D : SSet.{u + 1}}
    {p : E ⟶ B} [LeftFibration p] (R : LeftTransportRepresentation p) (g : D ⟶ B) :
    LeftTransportRepresentation (pullback.snd p g) := by
  let q := leftUnstraighteningProjection R.diagram
  let e := leftUnstraighteningBaseChangeIso R.diagram g
  let f := fiberComparisonBaseChange p q R.comparison R.over_base g
  have he : e.inv ≫ leftUnstraighteningProjection (g ≫ R.diagram) = pullback.snd q g := by
    rw [← leftUnstraighteningBaseChangeIso_hom_snd R.diagram g]
    exact e.inv_hom_id_assoc _
  have hf : f ≫ pullback.snd q g = pullback.snd p g :=
    fiberComparisonBaseChange_projection p q R.comparison R.over_base g
  refine { diagram := g ≫ R.diagram
           comparison := f ≫ e.inv
           over_base := by rw [Category.assoc, he, hf]
           fiber_equivalence := ?_ }
  intro d
  rw [← vertexFiberMap_comp (pullback.snd p g) (pullback.snd q g)
    (leftUnstraighteningProjection (g ≫ R.diagram)) f e.inv hf he d]
  exact (fiberComparisonBaseChange_isQCatEquivalence_fibers p q R.comparison
    R.over_base R.fiber_equivalence g d).comp
      (qCatEquivalenceOfIso (vertexFiberIsoOfTotalIso (pullback.snd q g)
        (leftUnstraighteningProjection (g ≫ R.diagram)) e.symm he d)).isQCatEquivalence

/-- 概要：制限後の分類図式は元の分類図式の厳密な前合成。
方針：制限の構成の底側を計算する。
規約：比較の同値類ではなく単体集合の射の等式。
使われ方：Kerodon §5.6.5、境界上の底の射を固定する条件。 -/
lemma LeftTransportRepresentation.restrict_diagram {E B D : SSet.{u + 1}}
    {p : E ⟶ B} [LeftFibration p] (R : LeftTransportRepresentation p) (g : D ⟶ B) :
    (R.restrict g).diagram = g ≫ R.diagram := rfl

/-- 概要：制限後の全空間の pointed space への射は元の射の厳密な制限。
方針：unstraightening の底変換同型の第一成分と比較の引き戻しの第一射影を計算する。
規約：境界上で底側と全空間側の両方を同時に固定する。
使われ方：Kerodon Theorem 5.6.5.12、表現の相対延長の全空間側の条件。 -/
lemma LeftTransportRepresentation.restrict_pointedMap {E B D : SSet.{u + 1}}
    {p : E ⟶ B} [LeftFibration p] (R : LeftTransportRepresentation p) (g : D ⟶ B) :
    (R.restrict g).pointedMap = pullback.fst p g ≫ R.pointedMap := by
  have hi : (leftUnstraighteningBaseChangeIso R.diagram g).inv ≫
      pullback.fst pointedSpaceProjection (g ≫ R.diagram) =
        pullback.fst (leftUnstraighteningProjection R.diagram) g ≫
          pullback.fst pointedSpaceProjection R.diagram := by
    calc
      _ = (leftUnstraighteningBaseChangeIso R.diagram g).inv ≫
          leftUnstraighteningMap (g ≫ R.diagram) R.diagram g rfl ≫
            pullback.fst pointedSpaceProjection R.diagram := by
        rw [leftUnstraighteningMap_pointed]
      _ = _ := by
        rw [← leftUnstraighteningBaseChangeIso_hom_fst]
        simp only [Category.assoc, Iso.inv_hom_id_assoc]
  change (fiberComparisonBaseChange p (leftUnstraighteningProjection R.diagram)
    R.comparison R.over_base g ≫ (leftUnstraighteningBaseChangeIso R.diagram g).inv) ≫
      pullback.fst pointedSpaceProjection (g ≫ R.diagram) = _
  rw [Category.assoc, hi, ← Category.assoc]
  simp only [fiberComparisonBaseChange, pullback.lift_fst]
  rfl

/-- 概要：表現の厳密な制限一致は、底側と全空間側の二つの射の一致で判定する。
方針：制限の両射の公式と表現の外延性を組み合わせる。
規約：g は境界包含に限らず任意の底の射。
使われ方：Kerodon Theorem 5.6.5.12、相対延長が満たすべき厳密な条件。 -/
lemma LeftTransportRepresentation.restrict_eq_iff {E B D : SSet.{u + 1}}
    {p : E ⟶ B} [LeftFibration p] (R : LeftTransportRepresentation p) (g : D ⟶ B)
    (S : LeftTransportRepresentation (pullback.snd p g)) :
    R.restrict g = S ↔ g ≫ R.diagram = S.diagram ∧
      pullback.fst p g ≫ R.pointedMap = S.pointedMap := by
  constructor
  · rintro rfl
    exact ⟨rfl, (R.restrict_pointedMap g).symm⟩
  · rintro ⟨hF, hpointed⟩
    apply LeftTransportRepresentation.ext
    · exact hF
    · rw [R.restrict_pointedMap g]
      exact hpointed

end SerrePositivity.InfinityCategories
