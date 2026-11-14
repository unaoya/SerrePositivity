module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.DiagramComparisons.LoopTowers
public import SerrePositivity.KST.Spectra.CofibrantOmegaSequence

/-!
概要：Kan 列の塔の段ごとの厳密極限と随伴構造射。
方針：各段の整合族の極限へ懸垂した射影と元の構造射を組み立てる。
規約：構造射の単射性と Ω 条件は別途検証する。
使われ方：BF 1978 §2、HA §1.4.2、HTT 4.2.4.1、Sp の塔の対象。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open SerrePositivity.KST.Spectra
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section

/-- 概要：Kan 列の塔の段ごとの極限の懸垂構造射。
方針：懸垂した各射影と各段の構造射を次段の極限へ持ち上げる。
規約：Kan 列の射の厳密可換性を使う。
使われ方：実際の塔の極限の構造射。 -/
def towerSequenceSigma (X : ℕ → KanSequence.{u})
    (d : ∀ n, KanSequence.Hom (X (n + 1)) (X n)) (k : ℕ) :
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointedTowerLimit (fun n ↦ ((X n).level k).space) (fun n ↦ (d n).app k)) ⟶
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointedTowerLimit (fun n ↦ ((X n).level (k + 1)).space) (fun n ↦ (d n).app (k + 1)) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointedTowerLift _ _
    (fun n ↦ PointedSimplicialSet.circle.{u} ◁ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointedTowerProjection _ _ n ≫ (X n).sigma k)
    (fun n ↦ by
      rw [Category.assoc, ← (d n).comm k, ← Category.assoc, ← whiskerLeft_comp,
        _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointedTowerProjection_comp])

/-- 概要：段ごとに fibration の Kan 列の塔の厳密極限の Kan 列。
方針：各段の極限の Kan 性を使い、構成した構造射を束ねる。
規約：各段の対象を置換せず、整合族の極限をそのまま使う。
使われ方：Ω 条件と構造射の単射性を検証する対象。 -/
def towerKanSequence (X : ℕ → KanSequence.{u})
    (d : ∀ n, KanSequence.Hom (X (n + 1)) (X n))
    [∀ n k, Fibration ((d n).app k).right] : KanSequence.{u} where
  level k := ⟨_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointedTowerLimit (fun n ↦ ((X n).level k).space) (fun n ↦ (d n).app k),
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.limit_kanComplex _ _⟩
  sigma := towerSequenceSigma X d

/-- 概要：Kan 列の塔の極限から指定段への厳密な射影。
方針：各段の射影を取り、構造射の持ち上げの成分計算を使う。
規約：元の塔の Kan 列の射。
使われ方：Sp の極限錐の脚を束ねる前の射影。 -/
def towerKanSequenceProjection (X : ℕ → KanSequence.{u})
    (d : ∀ n, KanSequence.Hom (X (n + 1)) (X n))
    [∀ n k, Fibration ((d n).app k).right] (n : ℕ) :
    KanSequence.Hom (towerKanSequence X d) (X n) where
  app k := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointedTowerProjection _ _ n
  comm k := by
    change _ = towerSequenceSigma X d k ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointedTowerProjection _ _ n
    rw [towerSequenceSigma, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointedTowerLift_projection]

/-- 概要：各段の随伴構造射から作る塔の極限の比較射。
方針：射影と随伴構造射を合成し、随伴可換性で loop の塔へ持ち上げる。
規約：元の列の Ω 条件は要求しない。
使われ方：実際の随伴構造射の π_* 同型性の検証。 -/
def towerSequenceAdjointMap (X : ℕ → KanSequence.{u})
    (d : ∀ n, KanSequence.Hom (X (n + 1)) (X n)) (k : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointedTowerLimit (fun n ↦ ((X n).level k).space) (fun n ↦ (d n).app k) ⟶
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointedTowerLimit (fun n ↦ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace ((X n).level (k + 1)).space)
        (fun n ↦ PointedObject.basedHomMap PointedSimplicialSet.circle.{u} ((d n).app (k + 1))) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointedTowerLift _ _
    (fun n ↦ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointedTowerProjection _ _ n ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv _ _ ((X n).sigma k))
    (fun n ↦ by
      rw [Category.assoc, ← (d n).adjoint_comm k, ← Category.assoc,
        _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointedTowerProjection_comp])

/-- 概要：極限の構造射の随伴は loop と極限の同型の下で各随伴の塔の比較に一致する。
方針：各射影で検査し、随伴の Hom 同値の両変数の自然性を使う。
規約：Ω 条件や構造射の単射性を要求しない厳密な等式。
使われ方：Sp の塔の Ω 条件を塔の π_* 比較へ帰着する。 -/
lemma towerSequenceSigma_adjoint (X : ℕ → KanSequence.{u})
    (d : ∀ n, KanSequence.Hom (X (n + 1)) (X n)) (k : ℕ) :
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv _ _ (towerSequenceSigma X d k) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.loopTowerIso (fun n ↦ ((X n).level (k + 1)).space)
          (fun n ↦ (d n).app (k + 1))).hom = towerSequenceAdjointMap X d k := by
  apply _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointedTowerLimit_hom_ext
  intro n
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.loopTowerIso_hom_projection,
    towerSequenceAdjointMap, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointedTowerLift_projection]
  let adj := PointedSimplicialSet.smashHomAdjunction PointedSimplicialSet.circle.{u}
  change adj.homEquiv _ _ (towerSequenceSigma X d k) ≫
      (PointedObject.basedHomFunctor PointedSimplicialSet.circle.{u}).map
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointedTowerProjection (fun n ↦ ((X n).level (k + 1)).space)
          (fun n ↦ (d n).app (k + 1)) n) =
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointedTowerProjection (fun n ↦ ((X n).level k).space) (fun n ↦ (d n).app k) n ≫
      adj.homEquiv _ _ ((X n).sigma k)
  rw [← adj.homEquiv_naturality_right, towerSequenceSigma, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointedTowerLift_projection]
  exact adj.homEquiv_naturality_left
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointedTowerProjection (fun n ↦ ((X n).level k).space) (fun n ↦ (d n).app k) n)
    ((X n).sigma k)

end
end SerrePositivity.InfinityCategories.HomotopyLimits
