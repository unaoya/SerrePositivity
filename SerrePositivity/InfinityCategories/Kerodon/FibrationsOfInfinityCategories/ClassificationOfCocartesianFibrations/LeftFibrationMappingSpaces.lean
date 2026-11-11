module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationInfinity
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.HomEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.Edges

/-!
概要：left fibrations の ∞ 圏の頂点・辺と相対関手空間による写像空間の模型。
方針：底上の射を coherent nerve の辺にし、局所 Kan な単体的圏の Hom 比較を適用する。
規約：相対関手空間は u、coherent nerve の写像空間と比較するときは u+1 に持ち上げる。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、straightening の写像空間の同値の判定。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：指定した left fibration を束縛した対象にする。
方針：射影を Over 圏の対象とし、left fibration 性を添える。
規約：底と全空間は同じ宇宙 u。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、具体的な fibration を ∞ 圏の対象として扱う。 -/
def leftFibrationObjectOf {E B : SSet.{u}} (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B := ⟨Over.mk p, inferInstanceAs (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p)⟩

/-- 概要：指定した left fibration を left fibrations の ∞ 圏の頂点にする。
方針：束縛した対象の coherent nerve の標準頂点を使う。
規約：底の quasicategory 性は不要。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、分類の fibration 側の具体的な対象。 -/
noncomputable def leftFibrationInfinityVertex {E B : SSet.{u}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationInfinity B) _⦋0⦌ :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (leftFibrationObjectOf p)

/-- 概要：底を保つ left fibrations の射は ∞ 圏の辺を定める。
方針：通常の底上の射を単体的圏の通常の射とし、coherent nerve の辺へ写す。
規約：辺の始点・終点は指定した二つの fibration の標準頂点。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、全空間の比較を ∞ 圏内の射として扱う。 -/
noncomputable def leftFibrationInfinityEdge {E F B : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q]
    (f : E ⟶ F) (hf : f ≫ q = p) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationInfinity B).Edge
      (leftFibrationInfinityVertex p) (leftFibrationInfinityVertex q) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge
    (show leftFibrationObjectOf p ⟶ leftFibrationObjectOf q from
      Over.homMk (U := Over.mk p) (V := Over.mk q) f hf)

/-- 概要：left fibrations の ∞ 圏の右写像空間は相対関手空間の持ち上げと同値。
方針：局所 Kan な単体的圏の coherent Hom 比較を二つの束縛した fibration に適用する。
規約：順方向は豊穣 Hom から coherent nerve の右写像空間への標準比較。
使われ方：Kerodon Theorem 4.6.7.5（Tag 01LE）、Corollary 5.6.0.6（Tag 028T）、分類の充満忠実性の検証。 -/
noncomputable def leftFibrationInfinityMappingEquivalence {E F B : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence ((SSet.uliftFunctor.{u + 1, u}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace q p))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (leftFibrationInfinityVertex p) (leftFibrationInfinityVertex q)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomEquivalence (leftFibrationObjectOf p) (leftFibrationObjectOf q)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
