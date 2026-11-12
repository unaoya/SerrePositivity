module
public import SerrePositivity.KST.Fibration.ZeroMiddleReconstructedDiagonal

/-!
概要：元の実二胞体族を固定ホーン内で正規化し、厳密対角の貼り合わせ後に元へ戻す。
方針：normalize(t)=encode(longHom(t)) を同じ再構成データで取り、指定 fiber 内同型を写す。
規約：厳密対角回収は正規化族にだけ適用する。旧 (9)・(9b) の条項を保持する。
使われ方：K-6 c4 の共有対角を全族で貼り合わせる条件付き利用側。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} _⦋2⦌) (hZ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory (s.obj ⟨ULift.up 1⟩))
  (K : SSet.{u + 1}) (h9 : zeroMiddleControlledTriangleSupply.{u})
  (t : (zeroMiddleFullSReconstructionTriangleSpace s hZ K) _⦋0⦌)

/-- 概要：同じ実族の読出しから再構成した正規化点。
方針：同じ encode・longHom の零次作用を合成する。
規約：元の固定ホーンの fiber 内に留まる。
使われ方：全族の厳密対角回収を適用する指定点。 -/
def zeroMiddleNormalizedFamilyPoint :
    (zeroMiddleFullSReconstructionTriangleSpace s hZ K) _⦋0⦌ :=
  zeroMiddleReconstructedFamilyPoint s hZ K h9
    ((zeroMiddleFullSReconstructionRead s hZ K h9).app (Opposite.op ⦋0⦌) t)

/-- 概要：同じ正規化を読み戻すと元の読出し点そのもの。
方針：同じ全族切断式を元の読出し点で評価する。
規約：元の実族 t 自身との等式は主張しない。
使われ方：同じ長 Hom 入力で正規化を反復する整合性。 -/
theorem zeroMiddleNormalizedFamilyPoint_read :
    (zeroMiddleFullSReconstructionRead s hZ K h9).app (Opposite.op ⦋0⦌)
      (zeroMiddleNormalizedFamilyPoint s hZ K h9 t) =
        (zeroMiddleFullSReconstructionRead s hZ K h9).app (Opposite.op ⦋0⦌) t :=
  zeroMiddleReconstructedFamilyPoint_read s hZ K h9 _

/-- 概要：同じ正規化は固定ホーンの fiber 内で冪等。
方針：正規化点の読出しを同じ元の読出しへ回収する。
規約：元 t が正規化済みであることは要求しない。
使われ方：同じ正規化族で対角回収と可逆比較を併用する。 -/
theorem zeroMiddleNormalizedFamilyPoint_idempotent :
    zeroMiddleNormalizedFamilyPoint s hZ K h9
      (zeroMiddleNormalizedFamilyPoint s hZ K h9 t) =
        zeroMiddleNormalizedFamilyPoint s hZ K h9 t := by
  unfold zeroMiddleNormalizedFamilyPoint
  rw [zeroMiddleReconstructedFamilyPoint_read]

/-- 概要：元の実族と同じ正規化点は固定ホーン fiber 内で指定同型を持つ。
方針：Ind-S (9) の正規化後仕様の同じ可逆比較を選ぶ。
規約：元 t 自身の厳密対角回収を仮定しない。
使われ方：正規化族での貼り合わせを元の実族へ戻す。 -/
def zeroMiddleNormalizedFamilyPointIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso t (zeroMiddleNormalizedFamilyPoint s hZ K h9 t) :=
  Classical.choice (zeroMiddleFullSReconstructionRead_normalizeComparison s hZ K h9 t)

/-- 概要：正規化した同じ実族は元の指定二短辺を厳密保持する。
方針：同じ元読出し点を再構成の実ホーン回収へ代入する。
規約：全族のホーン写像の等式を保持する。
使われ方：正規化後に共有対角の全族を貼り合わせる。 -/
theorem zeroMiddleNormalizedFamily_horn :
    ((horn 2 (1 : Fin 3)).ι ▷ K) ≫ zeroMiddleReconstructedFamily s hZ K h9
      ((zeroMiddleFullSReconstructionRead s hZ K h9).app (Opposite.op ⦋0⦌) t) =
        zeroMiddleFullSReconstructionHorn s hZ K :=
  zeroMiddleReconstructedFamily_horn s hZ K h9 _

/-- 概要：元の実二胞体全族から正規化後の同じ全族への可逆比較。
方針：固定ホーン fiber 内の指定同型を同じ包含へ写す。
規約：共有対角は正規化族側で厳密回収し、この同型で元へ戻す。
使われ方：K-6 c4 の正規化後の貼り合わせと元の上側二胞体の比較。 -/
def zeroMiddleNormalizedFamilyIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (Δ[2] ⊗ K) _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}).symm t.val)
    (zeroMiddleReconstructedFamily s hZ K h9
      ((zeroMiddleFullSReconstructionRead s hZ K h9).app (Opposite.op ⦋0⦌) t)) := by
  have hf : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (Δ[2] ⊗ K) _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}).symm t.val) = t.val :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).apply_symm_apply _
  have hg := zeroMiddleReconstructedFamily_vertex s hZ K h9
    ((zeroMiddleFullSReconstructionRead s hZ K h9).app (Opposite.op ⦋0⦌) t)
  have ht := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map (zeroMiddleNormalizedFamilyPointIso s hZ K h9 t)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((pre ((horn 2 (1 : Fin 3)).ι ▷ K)).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (zeroMiddleFullSReconstructionHorn s hZ K)))
  exact eqToIso (congrArg HomotopyCategory.mk hf) ≪≫ ht ≪≫
    eqToIso (congrArg HomotopyCategory.mk hg.symm)

/-- 概要：正規化前後の同じ入力点では全 native 長 Hom が一致する。
方針：元の読出し回収と同じ encode 像の回収を、同一の長 Hom 入力で接続する。
規約：対角の元 t での厳密回収は使わない。各点の全 native Hom を比較する。
使われ方：正規化後の貼り合わせを元のラベル作用へ戻す照合。 -/
theorem zeroMiddleNormalizedFamily_longHom (k : K _⦋0⦌) :
    let original := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (Δ[2] ⊗ K) _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}).symm t.val
    let normalized := zeroMiddleReconstructedFamily s hZ K h9
      ((zeroMiddleFullSReconstructionRead s hZ K h9).app (Opposite.op ⦋0⦌) t)
    let a := SSet.yonedaEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv Δ[2] _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}).symm
      ((curry original).app (Opposite.op ⦋0⦌) k))
    let b := SSet.yonedaEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv Δ[2] _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}).symm
      ((curry normalized).app (Opposite.op ⦋0⦌) k))
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((SSet.uliftFunctor.{u + 1, u}).map
      (a.map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((SSet.uliftFunctor.{u + 1, u}).map
        (b.map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩))) := by
  have h := zeroMiddleFullSReconstructionRead_recovery s hZ K h9 t k
  dsimp only [zeroMiddleFullSReconstructionRecovery] at h
  exact h.symm.trans (zeroMiddleReconstructedFamily_longHom s hZ K h9
    ((zeroMiddleFullSReconstructionRead s hZ K h9).app (Opposite.op ⦋0⦌) t) k)

end SerrePositivity.KST.Fibration
