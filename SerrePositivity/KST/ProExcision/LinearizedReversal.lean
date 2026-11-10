module
public import SerrePositivity.KST.ProExcision.AlternatingReversalIso
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedSpace
public import Mathlib.AlgebraicTopology.SimplicialSet.Op

/-!
# 自由整数鎖複体の順序反転の実同型

概要：単体的集合の順序反転を自由整数複体の自然な実鎖同型で元の複体へ移す。
方針：自由化と反転の可換性を、証明済みの交代面写像の符号付き同型へ合成する。
規約：KST Proposition 4.14、SW92 §1.2 の反対 bar 比較。
使われ方：借用する H_* の模型を介した行側の比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory
open AlgebraicTopology

/-- 概要：順序反転と自由整数加群化の実可換同型。
方針：各次数で同じ自由加群と同じ係数写像であることを使う。
規約：SW92 §1.2。使われ方：実交代鎖同型への接続。 -/
def linearizedReversalIso (X : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace X.op ≅ SimplicialObject.opFunctor.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace X) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl)

/-- 概要：自由化と反転の可換同型は単体的集合の射に自然。
方針：各次数の実射を定義で評価する。
規約：SW92 §1.2。使われ方：相対写像への反転の移送。 -/
lemma linearizedReversalIso_natural {X Y : SSet.{u}} (f : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap (SSet.opFunctor.map f) ≫ (linearizedReversalIso Y).hom =
      (linearizedReversalIso X).hom ≫ SimplicialObject.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap f) := by
  apply NatTrans.ext
  funext n
  rfl

/-- 概要：自由整数交代鎖複体の順序反転の実鎖同型。
方針：自由化と反転の可換性を、符号付きの交代鎖同型へ合成する。
規約：KST Proposition 4.14、SW92 §1.2。反転不変性を入力にしない。
使われ方：反対 bar のホモロジー比較。 -/
def linearizedReversalChainIso (X : SSet.{u}) :
    AlternatingFaceMapComplex.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace X.op) ≅
      AlternatingFaceMapComplex.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace X) :=
  (alternatingFaceMapComplex _).mapIso (linearizedReversalIso X) ≪≫
    alternatingReversalIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace X)

/-- 概要：自由整数鎖複体の反転同型は単体的集合の射に自然。
方針：自由化の可換同型の自然性と交代鎖同型の自然性を合成する。
規約：SW92 §1.2 の相対比較。使われ方：H_* の自然な実同型への移送。 -/
lemma linearizedReversalChainIso_natural {X Y : SSet.{u}} (f : X ⟶ Y) :
    AlternatingFaceMapComplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap (SSet.opFunctor.map f)) ≫
        (linearizedReversalChainIso Y).hom =
      (linearizedReversalChainIso X).hom ≫ AlternatingFaceMapComplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap f) := by
  let A := alternatingFaceMapComplex (ModuleCat.{u} ℤ)
  change A.map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap (SSet.opFunctor.map f)) ≫
      (A.map (linearizedReversalIso Y).hom ≫ (alternatingReversalIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace Y)).hom) =
    (A.map (linearizedReversalIso X).hom ≫ (alternatingReversalIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace X)).hom) ≫
      A.map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap f)
  rw [← Category.assoc, ← A.map_comp, linearizedReversalIso_natural, A.map_comp, Category.assoc]
  have hr : A.map (SimplicialObject.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap f)) ≫
      (alternatingReversalIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace Y)).hom =
    (alternatingReversalIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace X)).hom ≫ A.map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap f) :=
    alternatingReversalIso_natural (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap f)
  rw [hr, Category.assoc]

end SerrePositivity.KST.ProExcision
