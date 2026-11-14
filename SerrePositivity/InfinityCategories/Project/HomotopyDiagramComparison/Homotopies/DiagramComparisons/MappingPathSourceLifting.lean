module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.DiagramComparisons.RelativeFreePathLifting
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.DiagramComparisons.MappingPathTowers

/-!
概要：mapping path の源射影の相対比較は全ての単射に RLP を持つ。
方針：指定端点と底の path を同時に持ち上げ、二つの引き戻しの普遍性で貼る。
規約：標的側の縦射の fibration 性を使い、源側の縦射には要求しない。
使われ方：Goerss–Jardine I §7、HTT A.3.3、Sp の塔の比較の源側の因子。
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

/-- 概要：mapping path の源射影の相対比較射。
方針：元の源の成分と前段の mapping path の成分を引き戻しへ組にする。
規約：標的は基礎単体集合の引き戻し。
使われ方：塔の各相対比較を前回の towerMatchingMap に同定する。 -/
def mappingPathSourceMatchingMap {X Y X' Y' : PointedSimplicialSet.{u}}
    (f : X ⟶ Y) (f' : X' ⟶ Y') (a : X ⟶ X') (b : Y ⟶ Y')
    (h : f ≫ b = a ≫ f') :
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPath f).right ⟶ pullback a.right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathRetraction f').right :=
  pullback.lift (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathRetraction f).right (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.mappingPathMap f f' a b h).right (by
    simpa only [Under.comp_right] using
      congrArg Under.Hom.right (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.mappingPathMap_source f f' a b h).symm)

/-- 概要：標的側の縦射が fibration なら mapping path の源射影の相対比較は全ての単射への RLP を持つ。
方針：前段の path と次段の源を同時に指定し、端点を固定した path の相対充填を使う。
規約：源側の縦射の fibration 性や元の射の π_* 同型性は不要。
使われ方：mapping path の塔から源の塔への極限の射の全ての単射への RLP。 -/
lemma mappingPathSourceMatchingMap_rlp {X Y X' Y' : PointedSimplicialSet.{u}}
    (f : X ⟶ Y) (f' : X' ⟶ Y') (a : X ⟶ X') (b : Y ⟶ Y')
    (h : f ≫ b = a ≫ f') [Fibration b.right] :
    (MorphismProperty.monomorphisms SSet.{u}).rlp (mappingPathSourceMatchingMap f f' a b h) := by
  intro T U j hj
  have : Mono j := hj
  constructor
  intro t u sq
  let uX := u ≫ pullback.fst a.right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathRetraction f').right
  let uM := u ≫ pullback.snd a.right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathRetraction f').right
  have hs : t ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathRetraction f).right = j ≫ uX := by
    have he := congrArg (fun k : T ⟶ pullback a.right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathRetraction f').right ↦
      k ≫ pullback.fst a.right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathRetraction f').right) sq.w
    simpa only [Category.assoc, mappingPathSourceMatchingMap, pullback.lift_fst, uX] using he
  have hm : t ≫ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.mappingPathMap f f' a b h).right = j ≫ uM := by
    have he := congrArg (fun k : T ⟶ pullback a.right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathRetraction f').right ↦
      k ≫ pullback.snd a.right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathRetraction f').right) sq.w
    simpa only [Category.assoc, mappingPathSourceMatchingMap, pullback.lift_snd, uM] using he
  let pb := _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedPullback_isPullback (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint Y 1) f
  let pb' := _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedPullback_isPullback (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint Y' 1) f'
  have hpb : (pullback.fst (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint Y 1) f).right ≫
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint Y 1).right = (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathRetraction f).right ≫ f.right := pb.w
  have hpb' : (pullback.fst (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint Y' 1) f').right ≫
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint Y' 1).right = (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathRetraction f').right ≫ f'.right := pb'.w
  have hpath := congrArg Under.Hom.right (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.mappingPathMap_path f f' a b h)
  have hsource := congrArg Under.Hom.right (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.mappingPathMap_source f f' a b h)
  have hv := congrArg Under.Hom.right h
  simp only [Under.comp_right] at hpath hsource hv
  have hu : uX ≫ a.right = uM ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathRetraction f').right := by
    exact (Category.assoc _ _ _).trans
      ((congrArg (u ≫ ·) pullback.condition).trans (Category.assoc _ _ _).symm)
  have hc : j ≫ (uX ≫ f.right) =
      (t ≫ (pullback.fst (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint Y 1) f).right) ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint Y 1).right := by
    rw [← Category.assoc, ← hs, Category.assoc, ← hpb, ← Category.assoc]
  have he : (t ≫ (pullback.fst (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint Y 1) f).right) ≫
      (PointedObject.basedHomMap _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.freeInterval.{u} b).right =
        j ≫ (uM ≫ (pullback.fst (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint Y' 1) f').right) := by
    rw [Category.assoc, ← hpath, ← Category.assoc, hm, Category.assoc]
  have ha : (uX ≫ f.right) ≫ b.right =
      (uM ≫ (pullback.fst (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint Y' 1) f').right) ≫
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint Y' 1).right := by
    rw [Category.assoc, hv, ← Category.assoc, hu, Category.assoc, ← hpb', ← Category.assoc]
  obtain ⟨v, hjv, hend, hbase⟩ := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.relativeFreePath_lift b 1 j
    (t ≫ (pullback.fst (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint Y 1) f).right) (uX ≫ f.right)
    (uM ≫ (pullback.fst (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint Y' 1) f').right) hc he ha
  let l := pb.lift v uX hend
  refine ⟨⟨{ l := l, fac_left := ?_, fac_right := ?_ }⟩⟩
  · apply pb.hom_ext
    · rw [Category.assoc, IsPullback.lift_fst]
      exact hjv
    · rw [Category.assoc, IsPullback.lift_snd]
      exact hs.symm
  · apply pullback.hom_ext
    · simp only [Category.assoc, mappingPathSourceMatchingMap, pullback.lift_fst]
      change l ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathRetraction f).right = uX
      exact pb.lift_snd _ _ _
    · simp only [Category.assoc, mappingPathSourceMatchingMap, pullback.lift_snd]
      change l ≫ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.mappingPathMap f f' a b h).right = uM
      apply pb'.hom_ext
      · rw [Category.assoc, hpath, ← Category.assoc, IsPullback.lift_fst]
        exact hbase
      · change (l ≫ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.mappingPathMap f f' a b h).right) ≫
          (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathRetraction f').right = uM ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathRetraction f').right
        rw [Category.assoc, hsource, ← Category.assoc]
        have hls : l ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathRetraction f).right = uX := pb.lift_snd _ _ _
        exact (congrArg (· ≫ a.right) hls).trans hu

/-- 概要：標的の遷移が Kan fibration の mapping path の塔から源への極限の射は全ての単射への RLP を持つ。
方針：各段の始点評価の RLP と相対比較の RLP を塔の相対持ち上げ定理へ渡す。
規約：標的の各段の Kan 性を初段の RLP に用いる。
使われ方：塔の極限の π_* 比較の一方の因子の検証。 -/
lemma mappingPathTowerLimitSource_rlp (X Y : ℕ → PointedSimplicialSet.{u})
    (dX : ∀ n, X (n + 1) ⟶ X n) (dY : ∀ n, Y (n + 1) ⟶ Y n)
    (f : ∀ n, X n ⟶ Y n) (hf : ∀ n, dX n ≫ f n = f (n + 1) ≫ dY n)
    [∀ n, KanComplex (Y n).right] [∀ n, Fibration (dY n).right] :
    (MorphismProperty.monomorphisms SSet.{u}).rlp (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.mappingPathTowerLimitSource X Y dX dY f hf) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.towerMap_rlp
  · exact _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathRetraction_rlp (f 0)
  · intro n
    change (MorphismProperty.monomorphisms SSet.{u}).rlp
      (mappingPathSourceMatchingMap (f (n + 1)) (f n) (dX n) (dY n) (hf n).symm)
    exact mappingPathSourceMatchingMap_rlp _ _ _ _ _

/-- 概要：両縦射が fibration の可換正方形は mapping path 間の fibration を与える。
方針：源射影の相対比較を経由し、全ての単射への RLP と引き戻し射影を合成する。
規約：対象の Kan 性や横射の π_* 同型性は不要。
使われ方：mapping path の中間の塔の遷移の fibration 性。 -/
lemma mappingPathMap_fibration {X Y X' Y' : PointedSimplicialSet.{u}}
    (f : X ⟶ Y) (f' : X' ⟶ Y') (a : X ⟶ X') (b : Y ⟶ Y')
    (h : f ≫ b = a ≫ f') [Fibration a.right] [Fibration b.right] :
    Fibration (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.mappingPathMap f f' a b h).right := by
  have hm := mappingPathSourceMatchingMap_rlp f f' a b h
  have : Fibration (mappingPathSourceMatchingMap f f' a b h) :=
    (SSet.modelCategoryQuillen.fibration_iff _).mpr
      (fun _ _ j hj ↦ hm j (J_le_monomorphisms _ hj))
  have : Fibration (pullback.snd a.right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathRetraction f').right) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fibration_pullback_snd _ _
  have he : mappingPathSourceMatchingMap f f' a b h ≫
      pullback.snd a.right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathRetraction f').right = (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.mappingPathMap f f' a b h).right :=
    pullback.lift_snd ..
  rw [← he]
  infer_instance

/-- 概要：Kan な段と fibration の遷移を持つ二塔の mapping path の中間極限は Kan。
方針：中間の各段の Kan 性と各遷移の fibration 性を既存の塔の極限へ渡す。
規約：各段は元の mapping path の対象。
使われ方：極限の因子分解で実際の全基点 π_* 比較を使うための Kan 性。 -/
lemma mappingPathTowerLimit_kanComplex (X Y : ℕ → PointedSimplicialSet.{u})
    (dX : ∀ n, X (n + 1) ⟶ X n) (dY : ∀ n, Y (n + 1) ⟶ Y n)
    (f : ∀ n, X n ⟶ Y n) (hf : ∀ n, dX n ≫ f n = f (n + 1) ≫ dY n)
    [∀ n, KanComplex (X n).right] [∀ n, KanComplex (Y n).right]
    [∀ n, Fibration (dX n).right] [∀ n, Fibration (dY n).right] :
    KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.limit (fun n ↦ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPath (f n)).right)
      (fun n ↦ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.mappingPathTowerStep X Y dX dY f hf n).right)) := by
  have (n : ℕ) : Fibration (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.mappingPathTowerStep X Y dX dY f hf n).right :=
    mappingPathMap_fibration _ _ _ _ _
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.limit_kanComplex _ _

attribute [local instance] mappingPathTowerLimit_kanComplex

/-- 概要：mapping path の中間極限から源の極限への射は全基点 π_* 同型。
方針：両極限の Kan 性と源への射の全ての単射への RLP を組み合わせる。
規約：元の各段の比較射 f の π_* 同型性を使わない。
使われ方：塔の極限の比較の因子分解の源側の検証。 -/
lemma mappingPathTowerLimitSource_piIsomorphism (X Y : ℕ → PointedSimplicialSet.{u})
    (dX : ∀ n, X (n + 1) ⟶ X n) (dY : ∀ n, Y (n + 1) ⟶ Y n)
    (f : ∀ n, X n ⟶ Y n) (hf : ∀ n, dX n ≫ f n = f (n + 1) ≫ dY n)
    [∀ n, KanComplex (X n).right] [∀ n, KanComplex (Y n).right]
    [∀ n, Fibration (dX n).right] [∀ n, Fibration (dY n).right] :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.mappingPathTowerLimitSource X Y dX dY f hf) := by
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.kanPiIsomorphism_of_monoRight _ (mappingPathTowerLimitSource_rlp X Y dX dY f hf)

/-- 概要：元の源の極限から mapping path の中間極限への定数 path の比較は全基点 π_* 同型。
方針：源射影との合成が恒等射であることと源射影の π_* 同型性を使う。
規約：元の比較射 f の π_* 同型性には依存しない。
使われ方：塔の元の比較へ戻すための左因子の検証。 -/
lemma mappingPathTowerLimitUnit_piIsomorphism (X Y : ℕ → PointedSimplicialSet.{u})
    (dX : ∀ n, X (n + 1) ⟶ X n) (dY : ∀ n, Y (n + 1) ⟶ Y n)
    (f : ∀ n, X n ⟶ Y n) (hf : ∀ n, dX n ≫ f n = f (n + 1) ≫ dY n)
    [∀ n, KanComplex (X n).right] [∀ n, KanComplex (Y n).right]
    [∀ n, Fibration (dX n).right] [∀ n, Fibration (dY n).right] :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.mappingPathTowerLimitUnit X Y dX dY f hf) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism.of_comp (g := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.mappingPathTowerLimitSource X Y dX dY f hf) _
    (mappingPathTowerLimitSource_piIsomorphism X Y dX dY f hf)
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.mappingPathTowerLimitUnit_source]
  exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism.id _

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
