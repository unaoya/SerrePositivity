# K-7 工程 b：D 側への未供給入力一覧

2026-10-23。D の β5 と β3 を読み取り専用で確認した。`DGModuleCompactEquivalence` は通常の compact/perfect 比較であり、非可算 κ の dg 小模型の供給ではない。D の計画も同じ追加依存を未提供としている。依頼の仲介はコーディネータが行い、K-7 から D へ直接送信しない。

## 必要な二つの値（未構成）

```lean
-- R : Type u, [CommRing R], D : Type v, [DGCategory R D], [Small.{u} D]
-- κ : Cardinal.{u}, Cardinal.aleph0 < κ, κ.IsRegular
I : DGKappaConeInput R D κ
P : DGKappaPerfectInput R D I
```

正確な依存型・宇宙・名前は `KST/NonConnective/DGKappaConeInput.lean` と `DGKappaPerfectInput.lean` が正本。以下では `Q := I.objects`、`C := DGFullSubcategory (ModuleCategory R D) Q`、`V M := dgConeModuleDerivedVertex R D M`、`φ := dgKappaConeDerivedComparison R D I` と略記する。V の値域は β5 の実半自由模型 `dgModuleDerivedInfinityCategory R D`。

## D の供給状況（09:57までの成果との照合、停止引き継ぎ）

候補 `Q := dgKappaClosedProjectiveObjects R D κ` に対する個別宣言。K-7 の I・P の実値への接続は未実施。D 所有ファイルは読み取り専用で確認した。

| I / P のフィールド | D の供給宣言・状態 |
|---|---|
| `uncountable`・`regular` | κ に対する明示条件 `Cardinal.aleph0 < κ`・`κ.IsRegular` |
| `objects`・`small`・`projective` | `DGKappaClosedProjectiveFamily.lean` の `dgKappaClosedProjectiveObjects`・`…_small`・`…_projective` |
| `derivedFullyFaithful` | `DGKappaClosedProjectiveComparison.lean` の `dgKappaClosedProjectiveObjects_derivedFullyFaithful` |
| `countableClosed`・`binaryClosed` | `DGKappaClosedProjectiveOperations.lean` の `dgKappaClosedProjectiveObjects_countableClosed`・`…_binaryClosed` |
| `perfectCovers` | `DGKappaClosedPerfectCover.lean` の `dgKappaClosedProjectiveObjects_perfectCovers`（ordinary 導来圏での被覆） |
| `kappaCompact`・`covers` | 未供給。F2 の全共変 Hom による κ-compact 性と全頂点被覆が必要 |
| `pretriangulated` | 未供給。本体未統合の D 試作 `dgKappaClosedProjectiveObjects_isDGPretriangulated` は完成供給に数えない |
| P の `comparison`・`isEquivalence`・`inclusion` | すべて未供給。ordinary `perfectCovers` からは推論しない |

同じ候補に対する `dgKappaClosedProjectiveObjects_zero`・`…_shift`・`…_cone` も D の Operations にあり、実零加群所属 Z の供給材料となる。任意の明示入力 I に Z が自動で付くとは結論しない。D の現行引き継ぎも前三角性を未統合、κ-compact 性・被覆を未証明と記載している。

## `DGKappaConeInput` のフィールド名と型

| 名前 | 型 |
|---|---|
| `uncountable` | `Cardinal.aleph0 < κ` |
| `regular` | `κ.IsRegular` |
| `objects` | `Set (ModuleCategory R D)` |
| `small` | `Small.{u} C` |
| `pretriangulated` | `IsDGPretriangulated R C` |
| `projective` | `∀ M, Q M → moduleHomotopicallyProjective R D M` |
| `derivedFullyFaithful` | `IsFullyFaithful φ` |
| `kappaCompact` | `∀ M, Q M → F2.Compact.IsKappaCompact κ (V M)` |
| `covers` | `∀ y, F2.Compact.IsKappaCompact κ y → ∃ M, Q M ∧ Nonempty (VertexIso (V M) y)` |
| `countableClosed` | `∀ M : ℕ → ModuleCategory R D, (∀ n, Q (M n)) → Q (∐ M)` |
| `binaryClosed` | `∀ M N, Q M → Q N → Q (M ⨿ N)` |
| `perfectCovers` | `∀ M, modulePerfect R D ((moduleToDerived R D).obj M) → ∃ N, Q N ∧ Nonempty ((moduleToDerived R D).obj N ≅ (moduleToDerived R D).obj M)` |

`objects` は同型コピー全体を含む replete な対象型である必要はなく、実加群の選んだ代表系。その代表系自体に small 性と実直和の閉性が必要。全加群圏全体や全 κ-compact 加群型の small 性を仮定してはいない。

κ-compact 性は、通常の Hom 集合の有限台条件ではなく、F2 の全共変 Hom 関手による κ-filtered 余極限保存で検査する。可算直和の κ-compact 閉性を κ の記号だけから推論せず、`countableClosed` を明示する。

## `DGKappaPerfectInput` のフィールド名と型

`S := dgStableClosureNerve R C (dgKappaConePerfectObjects R D I)`、`j := dgStableClosureInclusion R C (dgKappaConePerfectObjects R D I)` と略記する。

| 名前 | 型 |
|---|---|
| `comparison` | `dgModulePerfectInfinityCategory R D ⟶ S` |
| `isEquivalence` | `IsQCatEquivalence comparison` |
| `inclusion` | `FunctorIso ((comparison ≫ j) ≫ φ) (dgPerfectInclusionInfinity R D)` |

通常の導来圏での `perfectCovers` だけから、この全写像空間の同値と全関手比較を結論していない。

## K-7 側で構成する出力

- 実 dg 加群の可算直和の全 Hom chain map、単位・豊穣合成の保存、射影性の保存。
- 同じ C 上の実 dg 自己関手 T と id ⊕ T、両向きの全斉次射に自然な厳密 dg 変換、各成分の指定した両側逆。
- 元の dg nerve 上の実関手同型 `dgKappaSwindleInfinityIso`。swindle 自体は I・P のフィールドに含めない。
- C の同じ perfect 対象で零化する cell 分解後の Drinfeld 商、実商関手、安定性と β3 の Verdier 列、固定 `PerfDGInput` への包装。
- P を入力した元の Perf の全頂点の零化。

入力 I・P の存在、F1 の Ind 安定性、K-6、K の加法性による消滅、懸垂の全入力射に対する反復作用は、この工程の出力から証明済みと扱わない。

## 工程 c：同じ κ の反復供給（未構成）

```lean
-- A : PerfDGInput.{u, max (u + 1) v} R
s : DGSuspensionStageProvider.{u, v} R κ
-- 定義上は (A : PerfDGInput.{u, max (u + 1) v} R) → DGSuspensionStageInput R κ A
-- s A のフィールド cone : DGKappaConeInput R A κ
-- s A のフィールド perfect : DGKappaPerfectInput R A (s A).cone
```

正本は `KST/NonConnective/DGSuspensionIteration.lean`。`dgSuspensionIteration R s A n` は各段で同じ `s` と κ を用い、`dgSuspensionIterationStage` はその段で使った I・P の対そのものを保持する。供給の存在を証明したとは扱わず、入力射への作用・全高次整合性もこの対象別反復だけからは推論しない。追加の必要型の記録であり、D・F1 へ直接の依頼は送っていない。

## 工程 c：同じ代表系内の実零加群（未供給）

```lean
Z : DGKappaZeroInput R D I
-- 定義上は I.objects (moduleZero R D)
```

正本は `KST/NonConnective/DGKappaZeroFunctor.lean`。I の存在やフィールドを変更せず、同じ I に関する追加の所属証拠として保持する。前三角性は零対象をホモトピー同値の範囲で与えるが、実零加群そのものが選んだ非 replete な代表系に入るとは結論しない。全 Hom を零へ送る厳密な零 dg 自己関手を同じ cone 内で作る際に使う。K の加法性・消滅・K-6 を入力するものではない。存在は未証明であり、D へ直接依頼していない。
