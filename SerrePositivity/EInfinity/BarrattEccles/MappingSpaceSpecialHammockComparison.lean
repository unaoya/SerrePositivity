module

public import SerrePositivity.EInfinity.BarrattEccles.MappingSpaceSpanNerveInversion

/-!
# 元の Map^h と特殊な三本矢の同じ共通比較

概要：同じ元の全単体の共通始域からの二射が弱同値となり、局所化後の同型を与える。
方針：元の左 augmentation と右射の反転性を使い、その同じ二射で同型を定める。
規約：単体的 DK Hom との比較や ∞ 局所化の普遍性の完成とは扱わない。
使われ方：Map^h と hammock 局所化の比較の frame 側の具体的な同定。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Opposite
open SerrePositivity.SimplicialModel

namespace SerrePositivity.EInfinity.BarrattEccles

variable (A : Type u) [CommRing A]

/-- 元の共通始域から同じ Map^h への左射も弱ホモトピー同値。 -/
lemma mappingSpaceIndexAugmentation_isWeakHomotopyEquivalence
    (X Y : (operad A).Algebra) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence
      (mappingSpaceIndexAugmentation A X Y) :=
  FrameHom.AnodyneWeakDetection.isWeakHomotopyEquivalence _
    (mappingSpaceIndexAugmentation_localized_isIso A X Y)

/-- 元の Map^h と特殊な三本矢の局所化後の同型は同じ二つの元の射で定める。 -/
def mappingSpaceSpecialHammockComparisonIso (X Y : (operad A).Algebra) :
    AnodyneHomotopy.anodyneQ.obj
        (SSet.uliftFunctor.{u + 1, u}.obj (((mappingSpace A).obj (op X)).obj Y)) ≅
      AnodyneHomotopy.anodyneQ.obj (nerve (algebraSpecialHammock A X Y)) := by
  have := mappingSpaceIndexAugmentation_localized_isIso A X Y
  have := mappingSpaceSpecialHammockNerveMap_localized_isIso A X Y
  exact (asIso (AnodyneHomotopy.anodyneQ.map (mappingSpaceIndexAugmentation A X Y))).symm ≪≫
    asIso (AnodyneHomotopy.anodyneQ.map (mappingSpaceSpecialHammockNerveMap A X Y))

/-- 同じ左射を前合成すると元の右射そのものを局所化後も回収。 -/
lemma mappingSpaceSpecialHammockComparisonIso_fac (X Y : (operad A).Algebra) :
    AnodyneHomotopy.anodyneQ.map (mappingSpaceIndexAugmentation A X Y) ≫
        (mappingSpaceSpecialHammockComparisonIso A X Y).hom =
      AnodyneHomotopy.anodyneQ.map (mappingSpaceSpecialHammockNerveMap A X Y) := by
  have := mappingSpaceIndexAugmentation_localized_isIso A X Y
  change AnodyneHomotopy.anodyneQ.map (mappingSpaceIndexAugmentation A X Y) ≫
    (inv (AnodyneHomotopy.anodyneQ.map (mappingSpaceIndexAugmentation A X Y)) ≫
      AnodyneHomotopy.anodyneQ.map (mappingSpaceSpecialHammockNerveMap A X Y)) = _
  exact IsIso.hom_inv_id_assoc _ _

end SerrePositivity.EInfinity.BarrattEccles
