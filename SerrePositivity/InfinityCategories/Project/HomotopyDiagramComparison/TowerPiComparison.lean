module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.MappingPathTargetLifting

/-!
概要：点つき Kan fibration の塔の段ごとの π_* 同型は極限でも π_* 同型。
方針：mapping path の中間の塔を挟み、源側と標的側の極限の射の RLP を検証する。
規約：両塔の全段が Kan、全遷移が fibration、比較は厳密に可換。
使われ方：Goerss–Jardine I §§7–8、BF 1978 §2、HTT 4.2.4.1、Sp の塔の Ω 条件。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open SerrePositivity.KST.Spectra
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
attribute [local instance] _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.mappingPathTowerLimit_kanComplex

/-- 概要：段ごとの π_* 同型から作る mapping path の塔の標的射影は全ての単射への RLP を持つ。
方針：初段の相対 Whitehead と各段の相対比較の RLP を塔の持ち上げ定理へ渡す。
規約：両塔の Kan 性と fibration 性を全段で仮定する。
使われ方：極限の比較の右因子の全基点 π_* 同型性。 -/
lemma mappingPathTowerLimitTarget_rlp (X Y : ℕ → PointedSimplicialSet.{u})
    (dX : ∀ n, X (n + 1) ⟶ X n) (dY : ∀ n, Y (n + 1) ⟶ Y n)
    (f : ∀ n, X n ⟶ Y n) (hf : ∀ n, dX n ≫ f n = f (n + 1) ≫ dY n)
    [∀ n, KanComplex (X n).right] [∀ n, KanComplex (Y n).right]
    [∀ n, Fibration (dX n).right] [∀ n, Fibration (dY n).right]
    (hπ : ∀ n, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (f n).right) :
    (MorphismProperty.monomorphisms SSet.{u}).rlp (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.mappingPathTowerLimitTarget X Y dX dY f hf) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.towerMap_rlp
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mappingPathProjection_rlp_of_piIsomorphism (f 0) (hπ 0)
  · intro n
    change (MorphismProperty.monomorphisms SSet.{u}).rlp
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.mappingPathTargetMatchingMap (f (n + 1)) (f n) (dX n) (dY n) (hf n).symm)
    exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.mappingPathTargetMatchingMap_rlp _ _ _ _ _ (hπ (n + 1)) (hπ n)

/-- 概要：段ごとの π_* 同型から作る mapping path の塔の標的射影は極限でも π_* 同型。
方針：中間極限の Kan 性と標的射影の全ての単射への RLP を使う。
規約：全基点・全自然数次数で判定する。
使われ方：元の塔の比較の π_* 同型性への因子分解。 -/
lemma mappingPathTowerLimitTarget_piIsomorphism (X Y : ℕ → PointedSimplicialSet.{u})
    (dX : ∀ n, X (n + 1) ⟶ X n) (dY : ∀ n, Y (n + 1) ⟶ Y n)
    (f : ∀ n, X n ⟶ Y n) (hf : ∀ n, dX n ≫ f n = f (n + 1) ≫ dY n)
    [∀ n, KanComplex (X n).right] [∀ n, KanComplex (Y n).right]
    [∀ n, Fibration (dX n).right] [∀ n, Fibration (dY n).right]
    (hπ : ∀ n, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (f n).right) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.mappingPathTowerLimitTarget X Y dX dY f hf) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.kanPiIsomorphism_of_monoRight _ (mappingPathTowerLimitTarget_rlp X Y dX dY f hf hπ)

/-- 概要：点つき Kan fibration の二塔の段ごとの全基点 π_* 同型は極限でも π_* 同型。
方針：定数 path と標的射影の極限の比較の合成を元の塔の射に同定する。
規約：比較射自身の fibration 性や相対比較の RLP を追加の前提に置かない。
使われ方：Ω スペクトルの塔の極限の随伴構造射の π_* 同型性。 -/
lemma pointedTowerMap_piIsomorphism (X Y : ℕ → PointedSimplicialSet.{u})
    (dX : ∀ n, X (n + 1) ⟶ X n) (dY : ∀ n, Y (n + 1) ⟶ Y n)
    (f : ∀ n, X n ⟶ Y n) (hf : ∀ n, dX n ≫ f n = f (n + 1) ≫ dY n)
    [∀ n, KanComplex (X n).right] [∀ n, KanComplex (Y n).right]
    [∀ n, Fibration (dX n).right] [∀ n, Fibration (dY n).right]
    (hπ : ∀ n, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (f n).right) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.towerMap (fun n ↦ (f n).right)
      (fun n ↦ congrArg Under.Hom.right (hf n))) := by
  have h := (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.mappingPathTowerLimitUnit_piIsomorphism X Y dX dY f hf).comp
    (mappingPathTowerLimitTarget_piIsomorphism X Y dX dY f hf hπ)
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.mappingPathTowerLimitUnit_target] at h
  exact h

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
