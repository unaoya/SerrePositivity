# K-B：採用済みの有限 native BF 四角形比較

概要：採用済みの未完備 Verdier 列と Perf 完備化の分離を、元の実構造辺へ進めるための追加経路。
方針：同じ D-9 の一つの実四角形に限る有限 BF 比較を K-S• 正本に依頼する。一般の StableInfinity 上の K 関手化は再開しない。
規約：ユーザー採用。以下は供給依頼の命題の型であり、届くまでは同じ命題を明示引数に取る。存在の証明・公理・供給済み成果としては扱わない。固定 S・ν・K、I と既存屋根を保持する。
使われ方：実供給後、同じ元の実核・cone・実商の BF 四角形から実 fiber 比較と構造辺を構成する。

## 採用された範囲（ユーザー経由でコーディネータへ中継済み）

- 既存 `kSpectrumMap` は StableModel の完全射ごとの実 BF 射。一般の高次面の整流は K-S• 計画 L1 のユーザー指示で中断済み。固定 `dgKInputK` は Perf 完備化後の値であり、未完備 native 実列の K 四角形にはそのまま代入できない。
- 現在の `dgKappaNativeStructureEdge` と `DGSuspensionNativeFibrationSequence` は、同じ未完備実 fibration 辺とその非負次数比較を明示引数に取る検証済み利用側。辺の実供給を完成扱いしない。
- 採用：同じ厳密 dg 入力・D-9 の同じ一つの native Verdier 提示に限る有限 BF 四角形比較を K-S• に依頼する。四辺を元の `kSpectrumMap` の実辺として保持し、各正段の全四角形を同じ元の S• 境界商の全図式へ比較する。四頂点・四辺や π 群だけの照合で代用しない。一般 StableInfinity の BF 関手化の再開は依頼しない。
- 採用後の接続：K-6 は未完備全 S• 四角形比較を同じ BF 四角形へ渡し、K-7 は同じ実 fiber から同じ cone の零性を経る構造辺を供給する。固定 ν と完備化の比較は既存の hcofinal 経路をそのまま使う。

## 型（/tmp/kb-raw-bf-square-request.lean で照合済み）

以下の命題の証明を K-S• が供給する。届くまでは K-B が同じ命題を明示仮定引数として利用側を進める。

```lean
module
public import SerrePositivity.KST.NonConnective.DGKappaNativeSquareComparison
public import SerrePositivity.KST.Fibration.SpectrumSpaceEvaluation
@[expose] public section
noncomputable section
universe u v w
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.Spectra
open SerrePositivity.KST.LocalizingInvariants SerrePositivity.KST.Fibration
open SerrePositivity.KST.NonConnective
local instance rawBFRequestSpectrumCategory : SimplicialCategory OmegaSpectrum.{w} :=
  OmegaSpectrum.simplicialCategory
variable (R : Type u) [CommRing R] (D : PerfDGInput.{u, max (u + 1) v} R)
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)
def kbRawBFSquareRequest : Prop :=
  let d := dgKappaNativeVerdierDiagram R D I
  ∃ Φ : (Δ[1] ⊗ Δ[1] : SSet.{max (u + 1) v + 1}) ⟶ Sp.{max (u + 1) v},
    squareBottomEdge ≫ Φ = SSet.yonedaEquiv.symm
      (coherentNerveEdge (kSpectrumMap (sInputExactMap d.inclusion))).edge ∧
    squareRightEdge ≫ Φ = SSet.yonedaEquiv.symm
      (coherentNerveEdge (kSpectrumMap (sInputExactMap d.projection))).edge ∧
    squareLeftEdge ≫ Φ = SSet.yonedaEquiv.symm
      (coherentNerveEdge (kSpectrumMap (sInputExactMap (toZeroCategory d.left)))).edge ∧
    squareTopEdge ≫ Φ = SSet.yonedaEquiv.symm
      (coherentNerveEdge (kSpectrumMap (sInputExactMap (fromZeroCategory d.right)))).edge ∧
    ∀ r : ℕ, Nonempty (FunctorIso
      (Φ ≫ coherentNerveMap (spectrumSpaceEvaluation.{max (u + 1) v} (r + 1)))
      (d.square ≫ coherentNerveMap (stableBoundaryClosedKanEnrichedFunctor.{max (u + 1) v} r)))
#check kbRawBFSquareRequest
```

正段比較は同じ元の全四角形への FunctorIso として要求する。供給側は元の置換射影・境界商比較を使い、指定包含・商辺と二胞体の照合を保持する。κ-compact 模型 I の存在、一般の連結 K の Sp 引き戻し性、完成した全入力自然性はこの依頼に含めない。
