module

public import SerrePositivity.EInfinity.BarrattEccles.MappingSmallSpanRecovery

/-!
# 元の三本矢への右比較射の反転性

概要：元の Map^h の共通始域から特殊な三本矢への同じ右射を局所化で反転する。
方針：小さい全図式への反転性と回収を合成し、元の左脚の恒等射の合成を正規化。
規約：元の比較射・全単体・全作用素を保持し、元の代数の cofibrancy は仮定しない。
使われ方：元の Map^h と特殊な三本矢のホモトピー型の比較。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory _root_.HomotopicalAlgebra Opposite
open SerrePositivity.SimplicialModel

namespace SerrePositivity.EInfinity.BarrattEccles

variable (A : Type u) [CommRing A]

/-- 同じ小さい全図式の回収で、元の右射そのものを全単体・全作用素で回収する。 -/
lemma mappingSpaceSmallSpanGrothendieckNerveMap_fac (X Y : (operad A).Algebra) :
    mappingSpaceSmallSpanGrothendieckNerveMap A X Y ≫ mappingSmallSpanRecoveryNerveMap A X Y =
      mappingSpaceSpecialHammockNerveMap A X Y := by
  let := modelCategory A
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro c
  refine CategoryTheory.Functor.ext (fun j => ?_) ?_
  · let s := (mappingSpaceSpecialHammockFunctor A X Y).obj (c.obj j)
    change ({s with
      leftMap := s.leftMap ≫ 𝟙 X
      left_mem := by simpa only [Category.comp_id] using s.left_mem}) = s
    simp only [Category.comp_id]
  · intro i j h
    apply _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.hom_ext
    · simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
      let q := (SerrePositivity.Reedy.cosimplicialResolutionFamily
        (mappingCofibrantFactorization A)).obj.obj X
      change 𝟙 _ ≫ q.map (𝟙 _ ≫ (c.map h).down.unop.hom.unop) =
        q.map (c.map h).down.unop.hom.unop
      simp only [Category.id_comp]
    · simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
      rfl

/-- 同じ元の右比較射そのものは、任意の可換環上で局所化で可逆。 -/
lemma mappingSpaceSpecialHammockNerveMap_localized_isIso (X Y : (operad A).Algebra) :
    IsIso (AnodyneHomotopy.anodyneQ.map (mappingSpaceSpecialHammockNerveMap A X Y)) := by
  have := mappingSpaceSmallSpanGrothendieckNerveMap_localized_isIso A X Y
  have := mappingSmallSpanRecoveryNerveMap_localized_isIso A X Y
  rw [← mappingSpaceSmallSpanGrothendieckNerveMap_fac, CategoryTheory.Functor.map_comp]
  infer_instance

/-- 同じ元の右射は、元の三本矢の nerve の Kan 性なしで弱ホモトピー同値。 -/
lemma mappingSpaceSpecialHammockNerveMap_isWeakHomotopyEquivalence
    (X Y : (operad A).Algebra) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence
      (mappingSpaceSpecialHammockNerveMap A X Y) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.AnodyneWeakDetection.isWeakHomotopyEquivalence _
    (mappingSpaceSpecialHammockNerveMap_localized_isIso A X Y)

/-- 元の大きい全図式への同じ中間射も、元の回収との厳密な因子分解で反転。 -/
lemma mappingSpaceSpanGrothendieckNerveMap_localized_isIso (X Y : (operad A).Algebra) :
    IsIso (AnodyneHomotopy.anodyneQ.map (mappingSpaceSpanGrothendieckNerveMap A X Y)) :=
  (mappingSpaceSpecialHammockNerveMap_localized_isIso_iff A X Y).mp
    (mappingSpaceSpecialHammockNerveMap_localized_isIso A X Y)

end SerrePositivity.EInfinity.BarrattEccles
