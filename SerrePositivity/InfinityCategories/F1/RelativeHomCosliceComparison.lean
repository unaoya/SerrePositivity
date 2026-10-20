module

public import SerrePositivity.InfinityCategories.F1.LeftFibrationCoslicePointFamily
public import SerrePositivity.InfinityCategories.F1.LeftFibrationCoslicePointUniqueness
public import SerrePositivity.InfinityCategories.F1.RelativeHomPointedNaturality
public import SerrePositivity.InfinityCategories.F1.LeftUnstraighteningFiberTransport

/-!
概要：表現対象の coslice から、その Hom 関手の unstraightening への実際の底上の比較。
方針：恒等射の pointed 頂点を始点 fiber へ戻し、同じ coslice 全体の延長を使う。
規約：全対象の一つの射を構成する。同値性はこの射の fiber 作用を照合して別に示す。
使われ方：coherent Hom 関手の回収を、恒等点での大域的な相対 Hom の評価へ接続する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- Hom 関手の実際の頂点評価は、元の相対 Hom の Kan 複体を表す。 -/
lemma relativeHomCoherentEvaluation_value {B : SSet.{u}} (q r : LeftFibrationObject B) :
    (leftFibrationCoherentEvaluation q.val).app (Opposite.op ⦋0⦌) (coherentNerveVertex r) =
      spaceInfinityVertex ((relativeFunctorEnrichedEvaluation q.val).obj r) := by
  rw [spaceInfinityVertex_eq_coherent]
  exact coherentNerveMap_vertex (relativeFunctorEnrichedEvaluation q.val) r

/-- Hom 関手の unstraightening の fiber を、同じ Hom の値上の pointed fiber へ移す。 -/
def relativeHomUnstraighteningFiberIso {B : SSet.{u}} (q r : LeftFibrationObject B) :
    vertexFiber (leftUnstraighteningProjection (leftFibrationCoherentEvaluation q.val))
      (coherentNerveVertex r) ≅
    vertexFiber pointedSpaceProjection
      (spaceInfinityVertex ((relativeFunctorEnrichedEvaluation q.val).obj r)) :=
  leftUnstraighteningFiberIso (leftFibrationCoherentEvaluation q.val) (coherentNerveVertex r) ≪≫
    eqToIso (congrArg (vertexFiber pointedSpaceProjection)
      (relativeHomCoherentEvaluation_value q r))

/-- Hom 関手の unstraightening の始点 fiber における、実際の恒等射の点。 -/
def relativeHomUnstraighteningIdentity {B : SSet.{u}} (q : LeftFibrationObject B) :
    (vertexFiber (leftUnstraighteningProjection (leftFibrationCoherentEvaluation q.val))
      (coherentNerveVertex q)) _⦋0⦌ :=
  (relativeHomUnstraighteningFiberIso q q).inv.app (Opposite.op ⦋0⦌) (relativeHomPointedIdentity q)

/-- 同じ fiber 同型は、選んだ始点を元の恒等射の pointed 頂点へ厳密に戻す。 -/
lemma relativeHomUnstraighteningIdentity_pointed {B : SSet.{u}} (q : LeftFibrationObject B) :
    (relativeHomUnstraighteningFiberIso q q).hom.app (Opposite.op ⦋0⦌)
      (relativeHomUnstraighteningIdentity q) = relativeHomPointedIdentity q := by
  let e := ((CategoryTheory.evaluation SimplexCategoryᵒᵖ (Type (u + 1))).obj
    (Opposite.op ⦋0⦌)).mapIso (relativeHomUnstraighteningFiberIso q q)
  exact (CategoryTheory.Iso.toEquiv e).apply_symm_apply (relativeHomPointedIdentity q)

/-- 恒等射の点から coslice 全体へ延長した、Hom 関手の unstraightening への比較射。 -/
def relativeHomCosliceComparison {B : SSet.{u}} (q : LeftFibrationObject B) :
    sliceUnder (SSet.yonedaEquiv.symm (coherentNerveVertex q)) ⟶
      leftUnstraightening (leftFibrationCoherentEvaluation q.val) :=
  lift (𝟙 _) (SSet.const (relativeHomUnstraighteningIdentity q)) ≫
    leftFibrationCoslicePointFamily
      (leftUnstraighteningProjection (leftFibrationCoherentEvaluation q.val))
      (coherentNerveVertex q)

/-- この比較射は、coslice の元の射影を厳密に保つ。 -/
lemma relativeHomCosliceComparison_projection {B : SSet.{u}} (q : LeftFibrationObject B) :
    relativeHomCosliceComparison q ≫
      leftUnstraighteningProjection (leftFibrationCoherentEvaluation q.val) =
      sliceUnderProjection (SSet.yonedaEquiv.symm (coherentNerveVertex q)) := by
  rw [relativeHomCosliceComparison, Category.assoc,
    leftFibrationCoslicePointFamily_projection,
    ← Category.assoc, lift_fst, Category.id_comp]
  rfl

/-- coslice の恒等錐は、全空間の実際の恒等射の点へ送られる。 -/
lemma relativeHomCosliceComparison_identity {B : SSet.{u}} (q : LeftFibrationObject B) :
    (relativeHomCosliceComparison q).app (Opposite.op ⦋0⦌)
      (cosliceIdentityCone (coherentNerveVertex q)) =
        (relativeHomUnstraighteningIdentity q).val := by
  have h := congrArg (fun k ↦ k.app (Opposite.op ⦋0⦌) (relativeHomUnstraighteningIdentity q))
    (leftFibrationCoslicePointFamily_identity
      (leftUnstraighteningProjection (leftFibrationCoherentEvaluation q.val))
      (coherentNerveVertex q))
  have h₀ : SimplexCategory.const ⦋0⦌ ⦋0⦌ 0 = 𝟙 ⦋0⦌ := by
    apply SimplexCategory.Hom.ext
    apply DFunLike.ext
    intro i
    exact @Subsingleton.elim (Fin 1) inferInstance _ _
  change (leftFibrationCoslicePointFamily
    (leftUnstraighteningProjection (leftFibrationCoherentEvaluation q.val))
      (coherentNerveVertex q)).app (Opposite.op ⦋0⦌)
      ((sliceUnder (SSet.yonedaEquiv.symm (coherentNerveVertex q))).map
        (SimplexCategory.const ⦋0⦌ ⦋0⦌ 0).op
        (cosliceIdentityCone (coherentNerveVertex q)),
          relativeHomUnstraighteningIdentity q) = _ at h
  rw [h₀, show (𝟙 ⦋0⦌).op = 𝟙 (Opposite.op ⦋0⦌) from rfl,
    CategoryTheory.Functor.map_id] at h
  change (leftFibrationCoslicePointFamily
    (leftUnstraighteningProjection (leftFibrationCoherentEvaluation q.val))
      (coherentNerveVertex q)).app (Opposite.op ⦋0⦌)
      (cosliceIdentityCone (coherentNerveVertex q),
        (vertexFiber (leftUnstraighteningProjection (leftFibrationCoherentEvaluation q.val))
          (coherentNerveVertex q)).map (SimplexCategory.const ⦋0⦌ ⦋0⦌ 0).op
            (relativeHomUnstraighteningIdentity q)) = _
  rw [h₀, show (𝟙 ⦋0⦌).op = 𝟙 (Opposite.op ⦋0⦌) from rfl,
    CategoryTheory.Functor.map_id]
  exact h

/-- 同じ大域的な比較射を、任意のテスト標的で実際の pointed fiber へ制限する。 -/
def relativeHomCosliceComparisonFiber {B : SSet.{u}} (q r : LeftFibrationObject B) :
    vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm (coherentNerveVertex q)))
      (coherentNerveVertex r) ⟶
    vertexFiber pointedSpaceProjection
      (spaceInfinityVertex ((relativeFunctorEnrichedEvaluation q.val).obj r)) :=
  vertexFiberMap _ _ (relativeHomCosliceComparison q) (relativeHomCosliceComparison_projection q)
    (coherentNerveVertex r) ≫ (relativeHomUnstraighteningFiberIso q r).hom

/-- 正規化した fiber 同型を pointed 全空間へ含めると、元の引き戻しの第一射影となる。 -/
lemma relativeHomUnstraighteningFiberIso_hom_ι {B : SSet.{u}} (q r : LeftFibrationObject B) :
    (relativeHomUnstraighteningFiberIso q r).hom ≫ vertexFiberι pointedSpaceProjection
      (spaceInfinityVertex ((relativeFunctorEnrichedEvaluation q.val).obj r)) =
    vertexFiberι (leftUnstraighteningProjection (leftFibrationCoherentEvaluation q.val))
      (coherentNerveVertex r) ≫ pullback.fst pointedSpaceProjection
        (leftFibrationCoherentEvaluation q.val) := by
  dsimp only [relativeHomUnstraighteningFiberIso, Iso.trans_hom, eqToIso.hom]
  rw [Category.assoc, vertexFiberTransport_ι pointedSpaceProjection
    (relativeHomCoherentEvaluation_value q r)]
  exact leftUnstraighteningFiberIso_hom_ι (leftFibrationCoherentEvaluation q.val)
    (coherentNerveVertex r)

/-- 各 fiber の比較は、構成済みの同じ大域射の pointed-space 成分そのもの。 -/
lemma relativeHomCosliceComparisonFiber_ι {B : SSet.{u}} (q r : LeftFibrationObject B) :
    relativeHomCosliceComparisonFiber q r ≫ vertexFiberι pointedSpaceProjection
      (spaceInfinityVertex ((relativeFunctorEnrichedEvaluation q.val).obj r)) =
    vertexFiberι (sliceUnderProjection (SSet.yonedaEquiv.symm (coherentNerveVertex q)))
      (coherentNerveVertex r) ≫ relativeHomCosliceComparison q ≫
        pullback.fst pointedSpaceProjection (leftFibrationCoherentEvaluation q.val) := by
  rw [relativeHomCosliceComparisonFiber, Category.assoc,
    relativeHomUnstraighteningFiberIso_hom_ι, ← Category.assoc, vertexFiberMap_ι]
  exact Category.assoc _ _ _

/-- 任意のパラメーター上で、同じ恒等点を持つ大域比較を相対関手として表す。 -/
def relativeHomCosliceComparisonSectionFamily {B : SSet.{u}} (q : LeftFibrationObject B)
    (P : SSet.{u + 1}) :
    P ⟶ relativeFunctorSpace
      (leftUnstraighteningProjection (leftFibrationCoherentEvaluation q.val))
      (sliceUnderProjection (SSet.yonedaEquiv.symm (coherentNerveVertex q))) :=
  SSet.const (relativeHomUnstraighteningIdentity q) ≫
    leftFibrationCoslicePointSection
      (leftUnstraighteningProjection (leftFibrationCoherentEvaluation q.val))
      (coherentNerveVertex q)

/-- この相対関手の族を展開すると、元の一つの大域比較を厳密に回収する。 -/
lemma relativeHomCosliceComparisonSectionFamily_uncurry {B : SSet.{u}}
    (q : LeftFibrationObject B) (P : SSet.{u + 1}) :
    relativeFunctorUncurry (relativeHomCosliceComparisonSectionFamily q P) =
      fst (sliceUnder (SSet.yonedaEquiv.symm (coherentNerveVertex q))) P ≫
        relativeHomCosliceComparison q := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  rfl

/-- 恒等錐での同じ値を持つ任意の族は、全対象上でこの実際の大域比較と同型。 -/
def relativeHomCosliceComparisonSectionFamily_uniqueIso
    {B : SSet.{u}} (q : LeftFibrationObject B) {P : SSet.{u + 1}}
    (f : P ⟶ relativeFunctorSpace
      (leftUnstraighteningProjection (leftFibrationCoherentEvaluation q.val))
      (sliceUnderProjection (SSet.yonedaEquiv.symm (coherentNerveVertex q))))
    (h : f ≫ leftFibrationCoslicePointEvaluate
      (leftUnstraighteningProjection (leftFibrationCoherentEvaluation q.val))
      (coherentNerveVertex q) = SSet.const (relativeHomUnstraighteningIdentity q)) :
    FunctorIso f (relativeHomCosliceComparisonSectionFamily q P) := by
  apply leftFibrationCoslicePointEvaluate_equalIso
    (leftUnstraighteningProjection (leftFibrationCoherentEvaluation q.val))
    (coherentNerveVertex q)
  rw [relativeHomCosliceComparisonSectionFamily, Category.assoc,
    leftFibrationCoslicePointSection_evaluate, Category.comp_id]
  exact h

end SerrePositivity.InfinityCategories
