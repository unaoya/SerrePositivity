# 残る形式化の全体像

作成日：2026-10-13。更新：2026-10-30（§2〜§4・§8 を現状へ更新）。状態：現状と計画の整理。

## 1. この文書の範囲

残る未証明依存と、既存の抽象化・具体的構成・論文への接続との関係を整理する。
6番の詳細は [Frobenius ホモロジーの計画](archive/frobenius-homology.md) にまとめているため、
ここでは位置付けだけを記す。1〜3番の詳細は [環の存在構成の計画](archive/local-algebra-1-3.md)、
4〜5番は [交点重複度の計画](archive/intersection-inputs-4-5.md) を参照する。
7番以降は別作業で進めるため、この文書では一覧と依存関係だけを扱い、新しい詳細計画は作らない。

番号1〜13は会話で用いた「外部引用一覧」の番号であり、論文の定理・補題番号ではない。
定理3.1と補題4.6に対応する二つの保留入力は、当初の13項目とは別に数える。番号1〜7・12・13は主定理の経路から外れ、番号は参照のため保持する。

## 2. 現在の達成範囲

リポジトリでは、環に依存しない Euler 評価、反復錐、消滅、下界、対称な比較の共通理論と、
perfect 複体・ランク商による実現を実装している。
利用する標準可換環論と、具体的な長さ代数から論文の主定理への接続も実装されている。

主定理の未証明依存は **3件** である（[公理監査](../scripts/audit_axioms.lean)、2026-10-18 の G1 達成以降）。

- Bhatt–Scholze の導来 perfectoid 化の E3 界面の存在（Def 8.2・Lemma 8.4・Prop 8.5・Cor 8.11–8.12・Cor 8.14・Thm 10.11）：
  `BhattScholze.Inputs.exists_perfectoidizationInterfaceE3`（[BhattScholze/Inputs/PerfectoidizationInterface](../SerrePositivity/BhattScholze/Inputs/PerfectoidizationInterface.lean)）。
- 保留中の K 理論の二件：`Section4.supportedRankK0_descent`（論文 補題4.6）、`theorem_3_1_K0`（論文 定理3.1）。

以前の BS の二件（Thm 1.17(1) の整代数の perfectoid 化の存在、Cor 8.12 の環としての切除）は、
この界面から証明した定理になった（2026-10-18、[∞ 圏の計画](archive/stage-i/infinity-lanes/infinity-categories.md) の G1）。
界面の原典照合と型は [perfectoid 化の界面](bhatt-scholze/perfectoidization-interface.md) にある。

`main_statement` と `core_statement` に直接の `sorry` はないが、これらの入力に依存する。
引用1・2・3は実構成へ置換した。引用4は剰余標数零の対角線論法、引用6はパラメータ Koszul 複体の
初等的な証明で、主定理が依存しないようにした（どちらも `Inputs` の宣言自体は `sorry` のまま残る）。
引用5は巡回 Adams 作用素で証明した（2026-10-15）。
BS Cor 7.3／Thm 7.4 の全射性は、André の補題を使わない根添加の構成で証明した（2026-10-16）。
André の補題（BS Thm 7.14）、BS Lemma 10.3・Remark 10.7、CLMST の Prop 2.4.7・Cor 4.0.4 も証明した（2026-10-17）。
実装変更後の依存は [公理監査](../scripts/audit_axioms.lean) で再確認する。

## 3. 外部引用の一覧

| 番号 | 現在の引用 | 役割・利用先 | 今後の担当範囲 |
| --- | --- | --- | --- |
| 1（解消済み） | 指定した剰余体を持つ完備平坦局所拡大 | 実図式・直極限・一般Noether判定・共通完備化平坦性から証明。補題2.1も引用非依存 | [1〜3の計画](archive/local-algebra-1-3.md) |
| 2（解消済み） | Cohen–Gabber 正規化 | 等標数の完備整域を、生成的に分離な有限拡大として正則基底上に置く | [微分経路の計画](archive/cohen-gabber-differentials.md)。Gabberの微分経路で証明済み |
| 3（解消済み） | 混標数の Cohen 正規化 | 完全剰余体のWitt係数とパラメータから実際の冪級数評価を構成し、有限性・単射性を証明 | 同上 |
| 4（主定理から除外） | Serre の体を含む場合の正値性 | 剰余標数零の場合を対角線論法で証明し、主定理は依存しない | [対角線論法の計画](archive/serre-equal-characteristic.md) |
| 5（解消済み） | Roberts–Gillet–Soulé の交点重複度消滅 | 台つき巡回 Adams 二乗・三乗と重み消滅により全剰余標数で証明。公開型を保持 | [Adams の計画](archive/intersection-vanishing-adams.md)。S1–S11 と利用先の公理監査が完了 |
| 6（主定理から除外） | Roberts の Frobenius 高次ホモロジー消滅 | パラメータ Koszul 複体の場合を初等的に証明し、主定理は依存しない | [初等版の計画](archive/frobenius-koszul-elementary.md)。一般形は [専用計画](archive/frobenius-homology.md) |
| 7（解消済み） | 標準パラメータ根の塔の完備化が integral perfectoid | Witt係数表示から条件を供給し、有限段Frobenius核・実際のtilt・Fontaine核から証明 | `RootTower/WittPresentation`。旧Inputsは証明済みの互換入口 |
| 8（界面へ集約） | 有限代数の perfectoidization の存在 | 混標数の具体的な代数を作る。BS Thm 1.17(1) を E3 界面から証明し、引用は界面の存在 1 件に集約 | [BS](bhatt-scholze/notes/bhatt-scholze.md)、[界面](bhatt-scholze/perfectoidization-interface.md) |
| 9〜11（解消済み） | perfectoid ideal・Koszul ホモロジー・正規化長さの公式 | CLMST Prop 2.4.7・Cor 4.0.4 を証明（2026-10-17）。その証明が使う BS Cor 8.12 の環版は E3 界面から証明 | [CLMST](archive/clmst.md)、[BS](bhatt-scholze/notes/bhatt-scholze.md) |
| 12（解消済み） | 有限生成加群で正規化長さ `λ∞ = λ*` | Noether 局所基底の有限段計算から証明済み。有限表示の場合も一致 | `FiniteGeneration.lean`。引用としては残らない |
| 13（解消済み） | 正規化長さの短完全列での加法性 | Noether局所基底の有限段評価から一般加法性を証明 | 共通の長さ層。引用としては残らない |

宣言の所在：

- 1：[ResidueFieldExtension](../SerrePositivity/Inputs/ResidueFieldExtension.lean)。
- 2・3：[CohenNormalization](../SerrePositivity/Inputs/CohenNormalization.lean)。
- 4：旧 `Inputs/SerrePositivity.lean`（Serre の等標数正値性の一般形）は 2026-10-17 に削除。主定理が使う剰余標数零の場合は `IntersectionMultiplicity/EqualCharZeroPositivity.lean` で証明済み。
- 5：[IntersectionTheory](../SerrePositivity/Inputs/IntersectionTheory.lean)。
- 6：旧 `Inputs/RobertsFrobenius.lean`（Roberts の Frobenius ホモロジー消滅の一般形）は 2026-10-17 に削除。必要なパラメータ Koszul 複体の場合は `CommutativeAlgebra/ParameterKoszulGrowth.lean` で証明済み。
- 7：[PerfectoidTower](../SerrePositivity/Inputs/PerfectoidTower.lean)。
- 8：[Perfectoidization](../SerrePositivity/Inputs/Perfectoidization.lean)（互換入口）。残る引用は [BhattScholze/Inputs/PerfectoidizationInterface](../SerrePositivity/BhattScholze/Inputs/PerfectoidizationInterface.lean)。
- 9〜11：[CLMST](../SerrePositivity/Inputs/CLMST.lean)。
- 12・13：[RootTowerLength/Tower](../SerrePositivity/LengthAlgebra/RootTowerLength/Tower.lean)。

## 4. K理論の二つの保留入力

| 保留入力 | 現在の範囲 | 専用計画 |
| --- | --- | --- |
| `theorem_3_1_K0` | 離散係数に対する、支持つきK₀の有理降下の帰結 | [KST 経路](archive/stage-i/kst-lanes/k-theory-kst-route.md) |
| `Section4.supportedRankK0_descent` | 補題4.6の係数の dg 表示と一般係数版の降下を合わせた帰結 | 同上 |

これらを利用する比較と主定理への接続は既に実装されているが、
保留入力そのものの証明は残っている。
専用計画では、単にK₀の帰結を別名で引用するのでなく、スペクトル・dg 理論の基盤から進める方針を記録している。
経路は 2026-10-18 に KST 経路（KST Thm A＋離散冪零不変性で cdh 降下を得て定理3.1、補題4.6 は F5 で迂回、K は安定 ∞ 圏の K）に決めた。
レーン別の計画は [kst-lanes/](archive/stage-i/kst-lanes/) にある。2026-10-28 からは、先に ∞ 圏基盤を整備する
（[∞ 圏基盤の整備計画](archive/stage-i/infinity-foundation-plan.md)）ため、各レーンは停止している。

5番にも支持つきK理論を使う証明があるが、定理3.1・補題4.6の降下を証明すれば、
5番も自動的に証明されるわけではない。Adams 操作や、その固有値・次元との関係は別の成果物である。

## 5. 理論の依存関係

全体は、次の層に分けて考える。

1. **具体的な環の準備：1〜3。** 剰余体、係数環、正則な正規化を作る。
2. **長さの基礎：12・13。** 塔上の正規化長さと加法性を確保する。
3. **等標数の実現：6。** Frobenius による高次ホモロジーの消滅を使う。
4. **混標数の実現：7〜11。** perfectoid 構成と almost の結果を長さの二性質へ接続する。
5. **抽象的比較の具体的適用：二つのK理論入力。** 群作用・支持・係数変更に関する降下を供給する。
6. **古典的な交点重複度の入力：4・5。** 等標数正値性と、低次元項の消滅を供給する。

現在、層 1・2・3・6 の引用は解消または主定理から除外した。残るのは層 4 の土台にある E3 界面と、層 5 の K 理論の二入力である。

共通 Euler・比較理論はこれらの環の構成から独立している。
新しい証明は、この共通理論を置き換えるのではなく、その具体的な入力を下から証明していく。

1〜3は両標数の構成に関わる。
12・13は正規化長さの土台であり、7〜11を一括して「perfectoid 理論」と呼ぶと、この区別が見えなくなる。
6の個々のホモロジー消滅と、5の Euler 数の消滅も別の仕事として扱う。

## 6. 作業の性格と見通し

この表は当初（2026-10-13）の見通しとして残す。1〜7・9〜13 は完了または主定理から除外した。

| 範囲 | 主な数学 | 見通し |
| --- | --- | --- |
| 1 | 平坦局所拡大、剰余体、完備化 | 単生成拡大から分割できる。任意の体拡大と Noether・平坦性を両立させる構成が重い |
| 2・3 | Cohen 構造、冪級数、有限正規化、分離性、Witt 環 | 共通部分が多い。2の分離的な選択と3の係数環はそれぞれ深い入力 |
| 4 | 完備テンソル積、対角線、Tor と Koszul、重複度 | 証明済みの Koszul・重複度理論を再利用できるが、対角線への接続は独立に整備が必要 |
| 5 | 局所 Chern character／Riemann–Roch、または Adams 操作 | 大きな理論整備。実装経路は未確定 |
| 6 | Frobenius、tight closure または双対化、長さの増大 | 専用計画で、まず必要な Koszul 版に範囲を絞る |
| 7〜11 | perfectoid 構成、almost の結果、長さへの変換 | 別作業の計画に従う |
| 12・13 | 塔の有限表示・有限生成近似、長さと完全列 | 別作業で扱う。一般の almost 理論全体を必ず先に作ると決めたものではない |
| 二つのK理論入力 | スペクトル、dg 理論、有理降下 | 大きな基盤整備として独立に進める |

これは相対的な性格の整理であり、日数の見積もりではない。
「標準可換環論の定理」であることは、Lean で短く実装できることを意味しない。
必要な API と、最初の具体的な補題の実装結果から工数を評価し直す。

## 7. 外部引用とは別の改善・拡張

[リポジトリの残作業](../README.md)には、次の項目も記録されている。

- 有限近似の補題5.4を、具体的な塔から抽象的な塔と両立する長さへ述べ直すこと。
- Koszul 重複度公式を、環自身の場合から任意の有限生成加群へ拡張すること。

これらは外部引用や二つのK理論入力とは別である。
特に後者は4番の証明経路の選択に関係するため、4〜5の計画で必要な範囲を検討する。
一般加群版を既に証明済みと見なして計画を立てない。

## 8. 各文書の役割と完了条件

- この文書：対象と依存関係の全体像。詳細計画や原典の全文を重複させない。
- [1〜3の計画](archive/local-algebra-1-3.md)：基礎環の存在構成、共通API、最初の実装単位。
- [4〜5の計画](archive/intersection-inputs-4-5.md)：古典的交点重複度の証明経路。
- [6の計画](archive/frobenius-homology.md)：Frobenius ホモロジー消滅の調査と段階別計画。
- [CLMST の計画](archive/clmst.md)：9〜11番。2026-10-17 に完了。
- [BS の計画](bhatt-scholze/notes/bhatt-scholze.md)：δ環・prism から perfectoid 化まで。8番と E3 界面を担当する（別セッション）。
- [perfectoid 化の界面](bhatt-scholze/perfectoidization-interface.md)：残る BS の引用（E3 界面）の原典照合と型。
- [K理論の KST 経路](archive/stage-i/kst-lanes/k-theory-kst-route.md)：定理3.1・補題4.6の基盤と降下。旧計画は [archive/k-theory-v1.md](archive/k-theory-v1.md)、dg 理論は [M5 の完了状況](archive/dg-theory-m5-status.md)。
- [∞ 圏基盤の整備計画](archive/stage-i/infinity-foundation-plan.md)：K 理論の各レーンを再開する前に行う ∞ 層の整備。

完了の報告では、次を分ける。

1. 原典の定義・ステートメントを正確に述べたこと。
2. 名前付き引用からの接続を証明したこと。
3. 引用していた結果そのものを証明したこと。
4. その補助定理まで含めて未証明依存を解消したこと。

`sorry` を別の名前や別の層へ移しただけでは、未証明依存の解消とは数えない。
引用を残して接続を完成する作業にも意味があるが、どの段階を達成したかを明記する。
