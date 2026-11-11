module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.TransformationFamilyDiagram
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.RepresentationTensor
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：一般の二つの選択表現の間の相対射の族の実現を束ねる。
方針：分類図式の変換の族と pointed な prism の三条件を記録する。
規約：unstraightening の標準表現に限定しない。
使われ方：一般の left fibrations の straightening の写像空間の作用。

対応節は Kerodon 7.4（Tag 02SX）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces

/-- 概要：選択表現の間の相対射を変換の族が実現する pointed な証拠。
方針：全パラメーターで始点・終点・底を同時に保持する。
規約：相対射の可逆性を要求しない。
使われ方：写像空間全体の射の復元と比較。 -/
@[kerodon 05R7]
structure TransportRepresentationFamilyWitness {E F B K : SSet.{u + 1}}
    {p : E ⟶ B} {q : F ⟶ B} [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q]
    (R : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation p) (S : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation q)
    (t : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningTransformationSpace R.diagram S.diagram) (f : E ⊗ K ⟶ F) where
  prism : ((Δ[1] : SSet.{u + 1}) ⊗ E) ⊗ K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PointedSpaceInfinity.{u}
  source : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 E ▷ K) ≫ prism = fst E K ≫ R.pointedMap
  target : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 E ▷ K) ≫ prism = f ≫ S.pointedMap
  projection : prism ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection =
    ((Δ[1] ◁ p) ▷ K) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorParameterizedPrism (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry t)

/-- 概要：証拠の prism を区間を左に出した表示へ移す。
方針：結合子の逆で前合成する。
規約：全空間とパラメーターを保持する。
使われ方：積の底上の collage による一意性。 -/
def TransportRepresentationFamilyWitness.leftPrism {E F B K : SSet.{u + 1}}
    {p : E ⟶ B} {q : F ⟶ B} [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q]
    {R : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation p} {S : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation q}
    {t : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningTransformationSpace R.diagram S.diagram} {f : E ⊗ K ⟶ F}
    (w : TransportRepresentationFamilyWitness R S t f) :
    (Δ[1] : SSet.{u + 1}) ⊗ (E ⊗ K) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PointedSpaceInfinity.{u} :=
  (α_ Δ[1] E K).inv ≫ w.prism

/-- 概要：区間を左に出した証拠は同じ図式の族を被覆する。
方針：結合子の自然性と証拠の射影条件を使う。
規約：パラメーターの大きさに制限を置かない。
使われ方：coherent な族の一意性への入力。 -/
lemma TransportRepresentationFamilyWitness.leftPrism_projection {E F B K : SSet.{u + 1}}
    {p : E ⟶ B} {q : F ⟶ B} [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q]
    {R : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation p} {S : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation q}
    {t : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningTransformationSpace R.diagram S.diagram} {f : E ⊗ K ⟶ F}
    (w : TransportRepresentationFamilyWitness R S t f) :
    w.leftPrism ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection =
      (Δ[1] ◁ (p ▷ K)) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentTransformationFamilyDiagram t := by
  rw [TransportRepresentationFamilyWitness.leftPrism, Category.assoc, w.projection,
    ← Category.assoc]
  have hn : (α_ (Δ[1] : SSet.{u + 1}) E K).inv ≫ ((Δ[1] ◁ p) ▷ K) =
      (Δ[1] ◁ (p ▷ K)) ≫ (α_ Δ[1] B K).inv := by
    apply SSet.hom_ext; intro n; rfl
  rw [hn, Category.assoc]
  rfl


end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
