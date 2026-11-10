module
public import SerrePositivity.KST.ProExcision.LinearizedReversal
public import SerrePositivity.KST.ProExcision.HomologyModel

/-!
# 借用するホモロジー関手の順序反転不変性

概要：実符号付き鎖同型から、借用関手とその反転の自然な実同型を構成する。
方針：H_* の自然な複体模型の同型を、実鎖同型のホモロジー同型へ合成する。
規約：KST Proposition 4.14、SW92 §1.2。反転不変性を新しい仮定にしない。
使われ方：非可換な列側から行側の相対比較への移送。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory HomologicalComplex

/-- 概要：非被約自由整数交代鎖複体の実関手。
方針：既存の自由化と交代面写像複体の二つの実関手を合成する。
規約：KST App. A の C(-) の鎖模型。使われ方：H_* の模型同型の自然変換への束ね。 -/
def linearizedChainFunctor : SSet.{u} ⥤ ChainComplex (ModuleCat.{u} ℤ) ℕ :=
  (SimplicialObject.whiskering _ _).obj _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization ⋙
    AlgebraicTopology.alternatingFaceMapComplex _

/-- 概要：自由整数鎖複体の順序反転の実自然同型。
方針：対象ごとの実鎖同型と証明済みの自然性を束ねる。
規約：SW92 §1.2。使われ方：反転不変性のホモロジーへの移送。 -/
def linearizedReversalChainNatIso : SSet.opFunctor ⋙ linearizedChainFunctor.{u} ≅ linearizedChainFunctor :=
  NatIso.ofComponents linearizedReversalChainIso (fun f ↦ linearizedReversalChainIso_natural f)

/-- 概要：借用する自然な複体模型を関手間の自然同型として読む。
方針：構造体の模型同型と自然性をそのまま束ねる。
規約：KST App. A、H_* 自体は所有レーンの関手。
使われ方：実鎖同型を借用 H_* へ移す。 -/
def SimplicialHomologyModel.toNatIso {F : SSet.{u} ⥤ ModuleCat.{u} ℤ} {i : ℕ}
    (M : SimplicialHomologyModel F i) :
    F ≅ linearizedChainFunctor ⋙ homologyFunctor (ModuleCat.{u} ℤ) (.down ℕ) i :=
  NatIso.ofComponents M.iso (fun f ↦ M.naturality f)

/-- 概要：借用する H_* とその単体の順序反転は自然に実同型。
方針：模型同型、実符号付き鎖同型のホモロジー、逆の模型同型を合成する。
規約：KST Proposition 4.14、SW92 §1.2。反転不変性を仮定しない。
使われ方：反対 bar の比較と相対零化の行側への移送。 -/
def SimplicialHomologyModel.reversalNatIso {F : SSet.{u} ⥤ ModuleCat.{u} ℤ} {i : ℕ}
    (M : SimplicialHomologyModel F i) : SSet.opFunctor ⋙ F ≅ F :=
  Functor.isoWhiskerLeft SSet.opFunctor M.toNatIso ≪≫
    (Functor.associator SSet.opFunctor linearizedChainFunctor
      (homologyFunctor (ModuleCat.{u} ℤ) (.down ℕ) i)).symm ≪≫
    Functor.isoWhiskerRight linearizedReversalChainNatIso (homologyFunctor (ModuleCat.{u} ℤ) (.down ℕ) i) ≪≫
    M.toNatIso.symm

end SerrePositivity.KST.ProExcision
