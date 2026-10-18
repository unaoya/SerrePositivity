module

public import SerrePositivity.KST.Descent.FiniteFlatFreeCharts

/-!
# 準コンパクト基底上の有限忠実平坦射の有限自由アフィン被覆

## 概要
各点で構成した実際の有限自由チャートから、基底全体の有限アフィン開被覆を得る。

## 方針
各点で一つのチャートを選び、開像の被覆に準コンパクト性を適用する。

## 規約
選んだチャートの環・正の有限基底・指定 Cartesian 性をそのまま保持する。

## 使われ方
論文 補題 3.2 の局所自明化を有限 Zariski Čech 被覆として使う。
原典の τ 位相の層論を Čech 計算へ置換するための実際の有限被覆。
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace SerrePositivity.KST.Descent

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [AlgebraicGeometry.Flat f]
  [Surjective f] [LocallyOfFinitePresentation f]

/-- 概要：各基底点を覆う実際の有限自由チャートを選ぶ（論文 補題 3.2）。
方針：各点での存在定理を適用する。
規約：チャートの Cartesian 性と正の有限基底を保持する。
使われ方：有限部分被覆を取る前の点で添字付けした族。 -/
noncomputable def finiteFreeChartFamily (y : Y) : FiniteFreeAffineChart f :=
  (exists_finiteFreeAffineChart_at_point f y).choose

/-- 概要：選んだチャートはその基底点を実際に覆う（論文 補題 3.2）。
方針：選択した存在定理の点の等式を取り出す。
規約：チャート射の像への所属を実際の点の持ち上げで返す。
使われ方：開像による基底全体の被覆。 -/
theorem finiteFreeChartFamily_covers (y : Y) :
    ∃ z : Spec (finiteFreeChartFamily f y).baseRing,
      (finiteFreeChartFamily f y).baseMap z = y :=
  (exists_finiteFreeAffineChart_at_point f y).choose_spec

variable [CompactSpace Y]

/-- 概要：実際の有限自由チャート族から基底全体を覆う有限部分族を得る（補題 3.2）。
方針：開埋め込みの開像に準コンパクト性を適用する。
規約：有限部分族のチャートの座標環と基底を変更しない。
使われ方：同じ前層を適用する有限 Zariski Čech 被覆。 -/
theorem exists_finiteFreeChart_indices :
    ∃ s : Finset Y, ∀ y : Y, ∃ i ∈ s,
      ∃ z : Spec (finiteFreeChartFamily f i).baseRing,
        (finiteFreeChartFamily f i).baseMap z = y := by
  have hcov : Set.univ ⊆ ⋃ i : Y, Set.range (finiteFreeChartFamily f i).baseMap := by
    intro y _
    exact Set.mem_iUnion.mpr ⟨y, finiteFreeChartFamily_covers f y⟩
  have hopen (i : Y) : IsOpen (Set.range (finiteFreeChartFamily f i).baseMap) := by
    have := (finiteFreeChartFamily f i).openImmersion
    exact (finiteFreeChartFamily f i).baseMap.isOpenEmbedding.isOpen_range
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover _ hopen hcov
  refine ⟨s, ?_⟩
  intro y
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hs (Set.mem_univ y))
  obtain ⟨his, z, hz⟩ := Set.mem_iUnion.mp hi
  exact ⟨i, his, z, hz⟩

/-- 概要：基底全体を覆う有限自由チャートの有限添字集合（論文 補題 3.2）。
方針：有限部分被覆の存在定理から選ぶ。
規約：空の基底では空の有限集合も許す。
使われ方：実際のアフィン開被覆の有限添字型。 -/
noncomputable def finiteFreeChartIndices : Finset Y :=
  (exists_finiteFreeChart_indices f).choose

/-- 概要：選んだ有限部分族の被覆性（論文 補題 3.2）。
方針：有限部分被覆の選択の仕様を取り出す。
規約：実際のチャート射での点の持ち上げ。
使われ方：アフィン開被覆の構成。 -/
theorem finiteFreeChartIndices_covers (y : Y) :
    ∃ i : finiteFreeChartIndices f,
      ∃ z : Spec (finiteFreeChartFamily f i.val).baseRing,
        (finiteFreeChartFamily f i.val).baseMap z = y := by
  obtain ⟨i, hi, z, hz⟩ := (exists_finiteFreeChart_indices f).choose_spec y
  exact ⟨⟨i, hi⟩, z, hz⟩

/-- 概要：有限忠実平坦射を有限自由に自明化する実際の有限アフィン開被覆（補題 3.2）。
方針：選んだ有限部分族をそのままスキームの開被覆にする。
規約：各チャートに正の有限基底と元の射への Cartesian 正方形が付随する。
使われ方：有限平坦 transfer の局所 rank 公式と Zariski Čech 降下。 -/
noncomputable def finiteFreeAffineOpenCover : Y.AffineOpenCover where
  I₀ := finiteFreeChartIndices f
  X i := (finiteFreeChartFamily f i.val).baseRing
  f i := (finiteFreeChartFamily f i.val).baseMap
  map_prop i := (finiteFreeChartFamily f i.val).openImmersion
  idx y := (finiteFreeChartIndices_covers f y).choose
  covers y := (finiteFreeChartIndices_covers f y).choose_spec

/-- 概要：自明化する実際のアフィン開被覆は有限（論文 補題 3.2）。
方針：有限集合の subtype の有限性を使う。
規約：元の基底全体の有限部分被覆。
使われ方：有限 Čech 被覆の反復と係数つき降下。 -/
instance : Finite (finiteFreeAffineOpenCover f).I₀ :=
  inferInstanceAs (Finite (finiteFreeChartIndices f))

end SerrePositivity.KST.Descent
