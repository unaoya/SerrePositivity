module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.RightConeBoundary

/-!
概要：同じ底上の全空間の射の持ち上げ性を頂点 fiber の誘導射へ移す。
方針：fiber の包含で四角形を全空間へ移し、底の固定条件で充填を fiber へ戻す。
規約：持ち上げる射自身の性質を使い、底への二つの射影の充填性は要求しない。
使われ方：Kerodon 7.4.1.6（Tag 05QS）、7.5.4.6（Tag 03BB） の right fibration の写像空間の比較 span。

対応節は Kerodon 7.4（Tag 02SX）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces

/-- 概要：全空間の比較の持ち上げ性は頂点 fiber の比較でも成立する。
方針：包含後の四角形を充填し、標的の fiber の固定条件から始域の固定条件を得る。
規約：試験射 i は任意。
使われ方：Kerodon 7.4.1.6（Tag 05QS） の比較 span の射影の持ち上げ性。 -/
lemma vertexFiberMap_hasLiftingProperty {A D E E' B : SSet.{u}}
    (p : E ⟶ B) (q : E' ⟶ B) (f : E ⟶ E') (hf : f ≫ q = p)
    (b : B.obj (Opposite.op ⦋0⦌)) (i : A ⟶ D) [HasLiftingProperty i f] :
    HasLiftingProperty i (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap p q f hf b) := by
  constructor
  intro a d sq
  have hs : CommSq (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b) i f (d ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι q b) := by
    constructor
    have h := congrArg (fun z ↦ z ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι q b) sq.w
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap_ι, ← Category.assoc, Category.assoc] at h
    exact h
  have hbase : hs.lift ≫ p = SSet.const b := by
    calc
      _ = hs.lift ≫ (f ≫ q) := congrArg (fun z ↦ hs.lift ≫ z) hf.symm
      _ = (hs.lift ≫ f) ≫ q := (Category.assoc _ _ _).symm
      _ = _ := by rw [hs.fac_right, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.comp_const]
  refine CommSq.HasLift.mk'
    { l := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift p b hs.lift hbase, fac_left := ?_, fac_right := ?_ }
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext p b
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι]
    exact hs.fac_left
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext q b
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap_ι, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι]
    exact hs.fac_right

/-- 概要：全空間の自明 Kan fibration は頂点 fiber でも自明 Kan fibration を誘導する。
方針：全境界の持ち上げ性を fiber の誘導射へ移す。
規約：始域と終域の Kan 性は不要。
使われ方：Kerodon 7.4.1.6（Tag 05QS） の写像空間への span の自明な射影。 -/
instance vertexFiberMap_trivialKanFibration {E E' B : SSet.{u}}
    (p : E ⟶ B) (q : E' ⟶ B) (f : E ⟶ E') (hf : f ≫ q = p)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration f] (b : B.obj (Opposite.op ⦋0⦌)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap p q f hf b) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibration_iff_boundary _).2
  intro n
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := f) (boundary n).ι inferInstance
  exact vertexFiberMap_hasLiftingProperty p q f hf b _

/-- 概要：全空間の right fibration は頂点 fiber でも right fibration を誘導する。
方針：正の添字のホーンの持ち上げ性を fiber の誘導射へ移す。
規約：底への射影 p・q の充填性は不要。
使われ方：Kerodon 7.4.1.6（Tag 05QS）、7.5.4.6（Tag 03BB） の写像空間の比較 span の終域への射。 -/
instance vertexFiberMap_rightFibration {E E' B : SSet.{u}}
    (p : E ⟶ B) (q : E' ⟶ B) (f : E ⟶ E') (hf : f ≫ q = p)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration f] (b : B.obj (Opposite.op ⦋0⦌)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap p q f hf b) where
  mem := by
    intro A D i hi
    have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration.mem (p := f) i hi
    exact vertexFiberMap_hasLiftingProperty p q f hf b i

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
