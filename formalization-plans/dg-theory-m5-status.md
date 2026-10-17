# M5（dg一般論）の完了状況とM9への引継ぎ

2026-10-17、ユーザー決定。**M5は中心作用と群作用を除いて完了。**
U16全体の受入は[dg-theory.md §17.282](archive/dg-theory.md#17282-u16全体受入とm5完了範囲の確定2026-10-17)。
U16dは担当の最終受入表の範囲で完了し、残接続を保留するという線引きによる。
旧計画の全一般化や中間記録の「未完」を、今回すべて証明したという意味ではない。
中心作用と群Gの作用はM9の手順9・10で形を決め、M9で実装・比較する。
この記録・検証を終えた後は停止し、新しい単位に着手しない。

固定版はLean `v4.35.0-rc4`、Mathlib `e6bbacd0e1b7307ff6e17da09cd2455f60804fa6`。
任意可換環A、非有界cochain、d:+1、ホモトピー:−1、Mathlib Enrichedを主モデルとする。
対象宇宙・Small・局所K-flat・モデル条件・compact生成は各公開宣言の仮定を保持する。

## (a) U0〜U17の受入表

入口のパスは `SerrePositivity/DifferentialGraded/` 以下。
記録の「本計画」は当時の計画 [archive/dg-theory.md](archive/dg-theory.md) を指す。

| 単位 | 現在の状態 | 記録ファイル・節 | 主要な入口 |
| --- | --- | --- | --- |
| U0：仕様・宇宙・規約 | 受入済み | 本計画§11 | README.md、StageOne.lean |
| U1：Hom複体・符号付き合成 | 受入済み | 本計画§11 | StageOne.lean、Complexes/ |
| U2：豊穣dg圏・成分 | 受入済み | 本計画§11 | Category/Components.lean、Category/Comparison.lean |
| U3：H⁰・関手・準同値 | 受入済み | 本計画§11 | Functor/QuasiEquivalence.lean、StageOne.lean |
| U4：閉対称モノイダル構造 | 受入済み | 本計画§12.3 | Complexes/Enrichment.lean、StageTwo.lean |
| U5：dg加群・Yoneda | 受入済み | 本計画§12.7 | Module/Yoneda.lean、Module/Ring.lean |
| U6：自由加群・評価随伴 | 受入済み | 本計画§13.5 | Module/FreeHomNaturality.lean、StageThree.lean |
| U7：shift・cone・極限余極限 | 受入済み | 本計画§13.13 | StageFour.lean |
| U8：ホモトピー・acyclic | 受入済み | 本計画§13.16 | StageFive.lean |
| U9：quasiIsoによる局所化 | 受入済み | 本計画§13.19 | StageSix.lean |
| U10：semifree解像度・導来圏の構造 | 受入済み | 本計画§13.88 | StageSeven.lean |
| U11：左加群・bimodule・tensor | 受入済み | 本計画§17.159 | StageEight.lean |
| U12a/b/c/d：K-flat・導来tensor | 受入済み | 本計画§17.59・70・72・73 | Tensor/KFlatComplex.lean、Derived/TensorBifunctor.lean |
| U12e-local | 受入済み、局所Hom K-flat条件を保持 | 本計画§17.249 | Derived/BimoduleLocal.lean、Checks/U12eLocal.lean |
| U12e-general（R1〜R7） | 部分実装のまま中断・未受入 | [一般版棚卸し](dg-theory-u12e-general-inventory.md)、本計画§17.249 | Resolution/General.leanと棚卸しの既存パス（主線へ追加importしない） |
| U12f：係数変更 | 明示条件下で受入済み | [係数変更記録](archive/dg-theory-scalar-extension.md) | Tensor/ScalarExtension.lean、Derived/ScalarExtensionTensor.lean |
| U13：perfect・compact・enhancement | U13a〜e受入済み | [U13受入記録](archive/dg-theory-u13-acceptance.md) | Perfect/CompactConverse.lean、Perfect/SmallEnhancementTriangulated.lean、同記録の環比較 |
| U14：endomorphism表示 | U14a〜c受入済み | [U14記録](archive/dg-theory-u14.md)、最終受入 | Endomorphism/の再構成・Perf・全導来比較（下記公開名） |
| U15a/b/c：明示的dg商と普遍性 | 受入済み | 本計画§17.138・144 | Quotient/Category.lean、Quotient/Universal.lean |
| U15d：path係数変更 | 受入済み | [係数変更記録](archive/dg-theory-scalar-extension.md) | Quotient/ScalarExtension.lean |
| U15e：局所K-flat版 | 受入済み | [局所商記録](archive/dg-theory-u17a-u13d.md)、U15e27・最終照合 | Quotient/DerivedComparisonEquivalence.lean、DerivedComparisonPerfect.lean |
| U15e：分解版 | 中断、今回作らない | 本計画§17.249・282 | U12e-general完成後の旧計画のみ（完成入口なし） |
| U16a/b/c/d | ユーザー指定の範囲で全体受入済み | 本計画§17.282、[Morita統合](archive/dg-theory-morita.md)、[Perf判定](archive/dg-theory-morita-criterion.md)、[U16b/d最終表](archive/dg-theory-morita-qe.md) | Morita/U16.lean、U16Checks.lean、ScalarExtensionAcceptanceChecks.lean |
| U17a | 受入済み | [局所商記録](archive/dg-theory-u17a-u13d.md)、U17a | Verdier/、Quotient/DerivedComparisonEquivalence.lean |
| U17b：局所perfect・Morita比較 | 最終担当表の範囲で受入済み | 同記録U17b1〜9・完了監査 | Verdier/U17.lean、KernelComparisonNaturality.lean |
| U17c：既存順序交換・論文比較 | 受入済み | 同記録U17c1〜2・完了監査 | Verdier/OrderSquare.lean |
| U17d：係数変更・支持・retractの個別図式 | 最終担当表の範囲で受入済み。中心・G作用はM9、高次整合性は保留 | 同記録U17d1〜8・完了監査 | Verdier/U17.lean、SupportSquare.lean、RetractSquare.lean、ScalarDirectCompletion.lean |

## (b) M5の完了条件との照合

| 完了条件 | 証拠・現在の範囲 |
| --- | --- |
| dg圏・加群・導来圏を実際に定義する | U0〜U11。準同型による局所化、全Hom、semifree計算、三角構造・余積まで。D4mのモデル比較を完成条件にしない |
| 導来tensor・合成・Morita | U12-local、U14、U16。実際の一般右随伴とunit/counit、作用の両単位・結合coherenceまで。全導来Morita十分性には両側のcompact生成を明示 |
| dg商とperfect hullをVerdier商・Karoubi包絡へ比較 | U15e局所版・U17。`localQuotientTriaEquivalence`、`localPerfectQuotientEquivalence`、`localPerfectOrderSquare`。商への関手・線形性・shift・三角形と個別の自然図式を保持 |
| scalar extensionの自然な比較 | U12f・U15d・U17d、U16d最終表。非flat係数変更も許し、必要な両側の局所条件・モデル条件は宣言通り。下記の追加接続は保留 |
| 中心作用・群Gの作用 | M9手順9・10へ移す。ここで証明済みとはしない |

以上のユーザー決定の完了条件により、**中心作用と群作用を除いて完了**。
これはM6のK理論やM9の具体的表示自体の完了を意味しない。

## (c) 保留・中断と再開点

| 項目 | 状態・再開条件 | 再開点 |
| --- | --- | --- |
| 中心作用・中心局所化 | M9手順9で必要な形を固定して着手 | Verdier/SupportSquare.leanの既存支持比較と、M9の具体的パラメータ。compact性から冪の零作用と中心局所化の比較は未実装 |
| 群Gの作用 | M9手順10でstrict作用・ひねりの形を固定して着手 | U12f/U15dの係数変更、既存ランク商のtwist/changeRing。群作用の一致は未実装 |
| U12e-general R1〜R7 | 中断・未受入。M6で必要になった場合のみ再開 | §17.249、[棚卸し](dg-theory-u12e-general-inventory.md)。R1外側右単位→R2同時制限単位→R3結合子→R4制限の恒等/合成/交換→R5changeEquivalence→R6分解変更coherence→R7一般監査。既存成果・名前・型は保持 |
| U15e分解版 | 今回作らない。M6が局所版で足りない場合のみ再開 | U12e-generalのR1〜R7を完成してから§15.5の分解版へ。局所版DerivedComparison*を再利用 |
| D4m | 今回作らない。M6でモデル比較が必要になった場合のみ再開 | §4のG1/G2/G5契約、既存局所化D(D)と同じWの比較。共有ModelCategory/Quillen/転送は元のK理論系列の担当 |
| U17高次整合性 | 今回作らない。M6で個別図式以上が必要になった場合のみ再開 | 局所商記録の最終監査、KernelCompositionComparison/ConjugatedCompositionNaturality。高次coherenceやすべての経路比較へのCommShiftを追加主張しない |
| U16d：Perf移送の追加統合 | M9でMoritaとTへの係数変更の可換性が必要なら再開 | CoherencePerfectUnit/Associatorの両単位・結合coherenceは完成済み。追加のM9図式の照合のみ保留 |
| U16d：局所化正方形の追加自然性 | 同上 | ScalarExtensionKernelLocalizedSquare、KernelDerivedNaturality、KernelLocalizationAugmentation。通常代表＋hα・hAug・hP'の正方形は受入済み。全主kernel射・条件族への追加統合は保留 |
| U16d：U12f成分同定 | 同上 | `scalarKernelTensorBaseChange`、`scalarKernelOutputEvaluationIso`、`scalarKernelOutputLeft_model`・`scalarKernelOutputRight_model`、`scalarKernelEvaluationAugmentation_relativeKFlat`。未コミットScalarExtensionKernelOutputComponents.leanは型照合とtensor写像簡約でビルド未完、受入対象外として保持 |
| U16d：合成kernelの係数変更比較 | 同上 | `scalarKernelDerivedExtension`、`scalarKernelLocalizedCompositionSquare`、`scalarPerfectSquareComposition_eq`。貼合せ作用図式は完成。元の合成kernelの係数変更と変更済み二kernelの合成とのkernel同型・既存正方形との一致は保留 |

U16dの正確な仮定と再開点は担当の[最終受入記録](archive/dg-theory-morita-qe.md)を正本とする。
hπとhPN・hP'を代用しない。未検証ファイルは公開入口・受入ビルドから除外されている。
過去の調査§17.255・263・271は保存し、方針(ii)を維持する。

## (d) M9の手順と利用できる公開API

以下は**M9で利用できる一般成果**の対応表。具体的自由列・小ランク条件・環・群との同定はM9側の仕事である。
完全修飾名の共通接頭辞は `SerrePositivity.DifferentialGraded.`。
`DGQuotient.` と `Morita.` はその下の名前空間、他は特記したものを除き同じ直下。

| M9手順 | dg成果・公開名 | 明示する入力・M9に残る当てはめ |
| --- | --- | --- |
| 1：E_Sの加法的生成性 | dgの外（可換環論） | 既存の自由列のretract・ランク比較を使う |
| 2：積の行列環B_Sによる表示 | dgの外（可換環論） | 具体的endomorphism環の同定。一般表示はU14の `perfectEndomorphismEquivalence`、`endomorphismDerivedEquivalence_ofCompactGenerator` を利用可能 |
| 3：Homの平坦性・無限積tensor | dgの外（可換環論） | 有限表示性、積とtensor、A上の平坦性の具体的証明を供給する |
| 4：dg商 | U15：`DGQuotient.quotientHom`、`DGQuotient.inclusion`、`DGQuotient.universalEquiv`、`DGQuotient.existsUnique_extension` | 小ランク部分圏とcontracting homotopyを固定。明示的pathと最終微分を使う |
| 5：Homの次数 | U15長さfiltration：`DGQuotient.epsilonDegree`、`DGQuotient.term`、`DGQuotient.lengthSubmodule`、`DGQuotient.lengthComplex`、`DGQuotient.lengthSubmodule_exhaustive` | epsilonDegree w = −length w。元Homが次数零という具体的入力から非正次数性を計算する。スペクトル次数への翻訳はM6。非正次数性のM9当てはめを証明済みとはしない |
| 6：K-flat性 | U15e：`DGQuotient.allHomKFlat_of_flat_zero`、`DGQuotient.localQuotientTriaEquivalence_of_flat_zero`、`DGQuotient.localPerfectQuotientEquivalence_of_flat_zero`。U12d：`moduleDerivedTensorBifunctor`、`ScalarExtension.relativeKFlatTensorComputation`。複体：`complexKFlat_of_flat_bounds` | 次数零以外IsZero、零次HomのModule.Flatを供給する。商前の局所K-flatと商HomのK-flatを混同せず、path項・flatness・次数の範囲を使う。TのA-flat性は追加しない |
| 7：係数変更 | U15d：`DGQuotient.quotientHomBaseChangeIso`、`DGQuotient.quotientHomBaseChangeIso_path_component`、`DGQuotient.quotientBaseChangeDGFunctor_inclusion`。U12f：`ScalarExtension.derivedTensorBaseChange`、`ScalarExtension.complexDerivedExtensionKFlatComputation`。U17d：`DGQuotient.sourceScalarLocalQuotientSquare`、`DGQuotient.sourceScalarCanonicalQuotientSquare`、`DGQuotient.sourceScalarCompletedPerfectSquare` | 固定pathの比較。元とT側の局所条件を別々に確認。U12fのモデル条件を保持し、U16dの保留接続を必要とするかはM9で判断 |
| 8：perfect hullと既存𝒫_S | U17b/c：`DGQuotient.localPerfectQuotientEquivalence`、`DGQuotient.localPerfectOrderSquare`、`DGQuotient.localPerfectPaperSequenceComparison_eq`、`paperSequenceComparison_eq_orderSquare`。U13：`modulePerfect`、`moduleCompact_iff_perfect`。U16c：`Morita.criterionPerfMorita_iff`、`Morita.kernelMoritaAdjunctionEquivalence`、`Morita.kernelMoritaPerfInverseIso`。U16b：`Morita.quasiEquivalenceDerivedGraphIsEquivalence`、`Morita.quasiEquivalenceGraphActionOnPerfectIso` | 具体的null部分圏とランク商を同定。U16c全導来版は三条件と両側compact生成を保持。一般の圏同値からdg準同値を推測しない |
| 9：支持・中心局所化 | 支持はU17d：`DGQuotient.localTriaSupport_iff`、`DGQuotient.localTriaSupportSquare`、`DGQuotient.localCompletedSupportSquare`、`DGQuotient.localPerfectSupportSquare` | 中心作用・中心局所化・compactnessからの冪の零作用は保留、M9で実装。一般Tに一様支持代表元を要求しない |
| 10：群Gによるひねり | 群作用は保留、M9で実装 | 具体的G作用・T因子の自己同型と既存twist/changeRingの一致、unit/compの図式を固定する |

手順8の既存側は `SerrePositivity.Asymptotic.paperRankEquivalence`・`SerrePositivity.Asymptotic.paperSequenceComparison`、
`SerrePositivity.karoubiVerdierOrderEquivalence`。一般比較はこれらと同じ図式を与えるが、
M9の具体的圏の同定そのものを省略するものではない。

## 検証と再現

各単位の過去の対象ビルド・監査は受入表の記録に保持する。
最終合同検証はU16、U12e-local、StageSeven/Eight、U17、既存Spectra.StageTwoを同時に扱う。
公理監査の許容範囲は `propext`・`Classical.choice`・`Quot.sound` のみ。

```sh
lake build SerrePositivity.DifferentialGraded.Morita.U16Checks SerrePositivity.DifferentialGraded.Verdier.ChecksU17Integration SerrePositivity.DifferentialGraded.Checks.U12eLocal SerrePositivity.DifferentialGraded.Checks.StageSeven SerrePositivity.DifferentialGraded.Checks.StageEight SerrePositivity.Spectra.StageTwo
lake env lean SerrePositivity/DifferentialGraded/Morita/U16Checks.lean
```

U16Checksは担当の54監査入口を束ねるScalarExtensionAcceptanceChecksもimportする。
最終合同ビルド成功（4780 jobs、警告・エラー0）。ログの815個の重複を除いた宣言は標準3公理以内。
直接実行では主要65宣言を再監査。ChecksU17Integrationの直接実行は構造の型検査であり、
import先の監査出力を再出力するものではない。各Checksの `#print axioms` が監査集合の正本。
M9対応表の公開名43件も固定版Leanの `#check` で照合済み。
新規sorry・axiom・引用・資源上限変更なし。既存APIの改名・型変更なし。
