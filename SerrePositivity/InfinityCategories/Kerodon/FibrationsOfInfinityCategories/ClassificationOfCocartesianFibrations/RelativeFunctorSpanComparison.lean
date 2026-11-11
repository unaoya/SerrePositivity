module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.RelativeFunctorOverEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftCoherentTransportReconstruction

/-!
概要：底上の同値の span による相対写像空間の比較と coherent transport への適用。
方針：span の二つの前合成を相対関手空間の同値とし、一方の逆と合成する。
規約：標的は任意の left fibration。全空間の同値だけから相対性を推論しない。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、coherent な復元が相対写像空間で持つ普遍性。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：底上の前合成同値の span は任意の left fibration への相対写像空間の同値を与える。
方針：二つの相対前合成の同値の間で共通の写像空間を消去する。
規約：底は quasicategory、span の三つの全空間には充填性を要求しない。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、復元比較の定義域を相対関手空間で置き換える。 -/
noncomputable def relativeFunctorEquivalenceOfSpan
    {E B : SSet.{u}} [Quasicategory B] (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p]
    {a b c : Over B} (f : c ⟶ a) (g : c ⟶ b)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence f.left) (hg : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence g.left) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p a.hom) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p b.hom) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.relativeFunctorOverPre_isQCatEquivalence p f hf).choose.trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.relativeFunctorOverPre_isQCatEquivalence p g hg).choose.symm

/-- 概要：元の left fibration と coherent transport の unstraightening から任意の left fibration への相対写像空間は同値。
方針：宇宙を揃えた底上の復元 span に相対関手空間の span 比較を適用する。
規約：標的の left fibration は u+1 の持ち上げた底上に任意に指定する。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、coherent な表現の存在方向の相対写像空間での検証。 -/
lemma nonempty_leftCoherentTransportRelativeEquivalence
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] {Y : SSet.{u + 1}}
    (q : Y ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (nerve C)) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q] :
    Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace q ((SSet.uliftFunctor.{u + 1, u}).map p))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace q (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftCoherentTransport p)))) := by
  obtain ⟨Z, t, a, b, _, ha, hb, ea, eb⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.exists_leftCoherentTransport_reconstruction_span p
  exact ⟨relativeFunctorEquivalenceOfSpan q
    (Over.homMk (U := Over.mk t) (V := Over.mk ((SSet.uliftFunctor.{u + 1, u}).map p)) a ha)
    (Over.homMk (U := Over.mk t)
      (V := Over.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftCoherentTransport p))) b hb) ea eb⟩

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
