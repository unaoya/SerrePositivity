module
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FunctorIsoTensor
public import SerrePositivity.KST.Fibration.ZeroMiddleComparisonSupply
public import SerrePositivity.KST.Fibration.ZeroMiddleLongFamilyComparison

/-!
概要：同じ実全 S• 再構成の供給値を、正規化対角と全族可逆比較を持つデータにまとめる。
方針：供給された同じ encode/read を一度選び、以後の入力と比較で共有する。
規約：新しい存在仮定はない。厳密切断・厳密冪等性は要求しない。
使われ方：K-6 c4 の実正規化上側と元の指定長 Hom への可逆移送。
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
  (K : SSet.{u + 1})

/-- 概要：同じ実全 S• 二短辺に対する再構成・読出しと元の指定比較。
方針：公開供給の同じ証拠から全フィールドを同時に取り出す。
規約：採用済みの全族可逆比較を使い、厳密切断は含めない。
使われ方：実入力を正規化し、その対角を可逆移送で元へ戻す。 -/
structure ZeroMiddleSuppliedReconstruction where
  encode : zeroMiddleFullSReconstructionLongSpace s hZ K ⟶
    zeroMiddleFullSReconstructionTriangleSpace s hZ K
  read : zeroMiddleFullSReconstructionTriangleSpace s hZ K ⟶
    zeroMiddleFullSReconstructionLongSpace s hZ K
  comparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (encode ≫ read) (𝟙 _)
  recovery : zeroMiddleFullSReconstructionRecovery s hZ K read
  diagonal : zeroMiddleFullSReconstructionDiagonalRecovery s hZ K encode read
  normalizeComparison : zeroMiddleFullSReconstructionNormalizeComparison s hZ K encode read

/-- 概要：同じ実全 S• 座標への再構成供給値。
方針：F1 の公開定理を消費した同じ実供給を一度選ぶ。
規約：主経路の存在仮定を追加しない。
使われ方：全長 Hom の実入力ごとの共通再構成データ。 -/
def zeroMiddleSuppliedReconstruction : ZeroMiddleSuppliedReconstruction s hZ K := by
  apply Classical.choice
  obtain ⟨encode, read, ⟨e⟩, recovery, diagonal, norm⟩ :=
    zeroMiddleFullSComparisonReconstruction_supplied s hZ K
  exact ⟨⟨encode, read, e, recovery, diagonal, norm⟩⟩

variable {s hZ K}
variable (D : ZeroMiddleSuppliedReconstruction s hZ K)
  (ℓ : (zeroMiddleFullSReconstructionLongSpace s hZ K) _⦋0⦌)

/-- 概要：同じ encode 像を読み戻した全長 Hom 入力。
方針：供給値の同じ二写像を順に適用する。
規約：元入力との厳密等式は主張しない。
使われ方：正規化上側の厳密対角に現れる読出し。 -/
def ZeroMiddleSuppliedReconstruction.readback :=
  D.read.app (Opposite.op ⦋0⦌) (D.encode.app (Opposite.op ⦋0⦌) ℓ)

/-- 概要：読み戻した同じ実入力から元入力への全族可逆比較。
方針：供給値の比較を元の長 Hom 空間内で評価する。
規約：指定合成端 fiber 内の同型であり、点ごとの Hom 比較ではない。
使われ方：正規化後の全対角から元入力へ戻る移送。 -/
def ZeroMiddleSuppliedReconstruction.readbackIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (D.readback ℓ) ℓ :=
  zeroMiddleFullSComparisonReadPoint s hZ K D.encode D.read D.comparison ℓ

/-- 概要：同じ読み戻しの直接 path 全族から元入力の全族への同型。
方針：合成端を固定した fiber 内の比較を同じ直接 path 評価へ写す。
規約：全パラメータを保持する。厳密等式へ置き換えない。
使われ方：再構成後の共有対角を元へ移送する。 -/
def ZeroMiddleSuppliedReconstruction.directIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (zeroMiddleLongPointFamily s hZ K (D.readback ℓ) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
        (ULift.up (ComposableArrows.mk₀ coherentTriangleDirectPath)))
      (zeroMiddleLongPointFamily s hZ K ℓ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
        (ULift.up (ComposableArrows.mk₀ coherentTriangleDirectPath))) :=
  zeroMiddleLongPointDirectFamilyIso s hZ K _ _ (D.readbackIso ℓ)

/-- 概要：同じ encode 像を正規化した実二胞体空間内の点。
方針：同じ読み戻し入力を同じ encode へ戻す。
規約：厳密冪等性を仮定しない。
使われ方：全対角の厳密回収を適用する実入力。 -/
def ZeroMiddleSuppliedReconstruction.normalizedPoint :
    (zeroMiddleFullSReconstructionTriangleSpace s hZ K) _⦋0⦌ :=
  D.encode.app (Opposite.op ⦋0⦌) (D.readback ℓ)

/-- 概要：正規化した同じ実全 S• 上側二胞体族。
方針：同じ再構成点の関手頂点を実全族へ戻す。
規約：各パラメータ点で再選択しない。
使われ方：正規化側の共有対角を持つ実全族。 -/
def ZeroMiddleSuppliedReconstruction.normalizedFamily :
    (Δ[2] : SSet.{u + 1}) ⊗ K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).symm (D.normalizedPoint ℓ).val

/-- 概要：同じ正規化族の関手頂点表示は元の再構成点。
方針：標準の頂点表示の両逆を使う。
規約：同じ全族を保持する。
使われ方：元の固定ホーンと正規化対角への接続。 -/
theorem ZeroMiddleSuppliedReconstruction.normalizedFamily_vertex :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (D.normalizedFamily ℓ) = (D.normalizedPoint ℓ).val :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).apply_symm_apply _

/-- 概要：正規化族は元の二短辺の全ホーンを厳密に保つ。
方針：同じ固定ホーン fiber の点の条件を実全族へ戻す。
規約：新たな存在仮定や厳密切断を使わない。
使われ方：可逆対角移送の前後で二短辺を保持する。 -/
theorem ZeroMiddleSuppliedReconstruction.normalizedFamily_horn :
    ((horn 2 (1 : Fin 3)).ι ▷ K) ≫ D.normalizedFamily ℓ =
      zeroMiddleFullSReconstructionHorn s hZ K := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).injective
  change (((pre ((horn 2 (1 : Fin 3)).ι ▷ K)).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}).app
    (Opposite.op ⦋0⦌)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (D.normalizedFamily ℓ)) = _
  rw [D.normalizedFamily_vertex ℓ]
  exact (D.normalizedPoint ℓ).property.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero _)

private theorem suppliedReconstructionDirectPath_eq :
    coherentTriangleDirectPath.{u} =
      ({ I := {ULift.up 0, ULift.up 2}
         left := by simp
         right := by simp
         left_le := fun k _ => Fin.zero_le k.down
         le_right := fun k _ => Fin.le_last k.down } : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleNativePath.{u}) := by
  apply SimplicialThickening.Path.ext
  ext ⟨k⟩
  fin_cases k <;> simp [coherentTriangleDirectPath, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentOnePath] <;> decide

/-- 概要：正規化上側の対角は同じ読み戻し入力の直接 path 全族を厳密に回収する。
方針：元の encode 像を正規化対角条項へ代入する。
規約：元入力との比較は directIso に分離する。厳密切断は使わない。
使われ方：正規化側の厳密対角から元入力への全族可逆移送。 -/
theorem ZeroMiddleSuppliedReconstruction.normalizedFamily_diagonal :
    (stdSimplex.δ (1 : Fin 3) ▷ K) ≫ D.normalizedFamily ℓ =
      (Δ[1] ◁ (zeroMiddleLongPointFamily s hZ K (D.readback ℓ) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
        (ULift.up (ComposableArrows.mk₀ coherentTriangleDirectPath)))) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison
          (stableCoreSingleKanObject (s.obj ⟨ULift.up 0⟩))
          (stableCoreSingleKanObject (s.obj ⟨ULift.up 2⟩))) := by
  rw [suppliedReconstructionDirectPath_eq]
  have h := D.diagonal (D.encode.app (Opposite.op ⦋0⦌) ℓ)
  dsimp only [zeroMiddleFullSReconstructionDiagonalRecovery] at h
  simpa only [ZeroMiddleSuppliedReconstruction.normalizedFamily,
    ZeroMiddleSuppliedReconstruction.normalizedPoint,
    ZeroMiddleSuppliedReconstruction.readback, zeroMiddleLongPointFamily,
    ] using h

/-- 概要：元の encode 像と同じ正規化像は固定ホーン内で可逆比較される。
方針：供給の正規化比較を元の encode 像へ適用する。
規約：元の実点との厳密等式は主張しない。
使われ方：正規化族での構成を元の再構成像へ戻す。 -/
def ZeroMiddleSuppliedReconstruction.normalizedPointIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (D.encode.app (Opposite.op ⦋0⦌) ℓ) (D.normalizedPoint ℓ) :=
  Classical.choice (D.normalizeComparison (D.encode.app (Opposite.op ⦋0⦌) ℓ))

/-- 概要：正規化上側の実全対角は元の指定対角全族と可逆比較される。
方針：同じ直接 path 全族比較を F2 正本の直積同型で区間へ延ばし、標準区間像へ送る。
規約：厳密切断も新しい存在仮定も使わない。全時刻の関手同型を保持する。
使われ方：K-6 c4 の共有対角を可逆比較に沿って移送する。 -/
def ZeroMiddleSuppliedReconstruction.diagonalIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      ((stdSimplex.δ (1 : Fin 3) ▷ K) ≫ D.normalizedFamily ℓ)
      ((Δ[1] ◁ (zeroMiddleLongPointFamily s hZ K ℓ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
        (ULift.up (ComposableArrows.mk₀ coherentTriangleDirectPath)))) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison
          (stableCoreSingleKanObject (s.obj ⟨ULift.up 0⟩))
          (stableCoreSingleKanObject (s.obj ⟨ULift.up 2⟩)))) := by
  let ei : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (𝟙 (Δ[1] : SSet.{u + 1})) (𝟙 Δ[1]) := Iso.refl _
  have ewhole := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorIsoTensor ei (D.directIso ℓ)
  simp only [id_tensorHom] at ewhole
  exact eqToIso (congrArg (fun f => HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f))
    (D.normalizedFamily_diagonal ℓ)) ≪≫ ewhole.postcomp _

end SerrePositivity.KST.Fibration
