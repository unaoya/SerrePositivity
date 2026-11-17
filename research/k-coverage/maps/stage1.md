# 停止点 1　KST と Land–Tamme

照合基点は `86fb5ab0c`。原典の版は各目次に記載。Lean 4.35.0-rc4 で、入力のソースと依存の版を照合し、既存の olean に対する `#check` と `#print axioms` を共有ロック下で実行した。

| 文献 | own | mathlib | both | partial | interface | none | 計 | 凍結 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| KST | 4 | 0 | 0 | 52 | 12 | 82 | 150 | 32 |
| Land–Tamme | 0 | 0 | 0 | 39 | 6 | 87 | 132 | 4 |

集計の none には、独立した主張を持たない節・付録の見出しと記法表（KST 23 行、Land–Tamme 11 行）を含む。これらの内容は節内の項目行で照合した。

- KST 4.9 は有限生成加群の Koszul ホモロジーのプロ消滅まで一致し、凍結側にある。4.10 は各次数の加群複体のプロ同型で、単体環としての比較が残る。4.8 の対応候補は連結性を仮定した dg の不変量についての定理で、非連結 K 自身を供給するものではない。
- KST 3.7 は前層の抽象ブローアップの完全列および Cat^perf の局所化条件の界面。3.8–3.15 の範囲で見つけた dg の局所チャート比較や完全加群の模型だけでは、原典の押し出しの充満忠実性、負捻りの消滅、部分商の同値を組み立てられない。5.2–5.6 に向けた通常ブローアップの幾何や Koszul 塔の部品は個別に記録した。
- Land–Tamme 1.3 は、dg Milnor 四角形から実 resolved 商の冪等完備化を頂点とする Sp 引き戻しを得る。1.13–1.16 が要求する End と導来テンソルの下部の同定、両側の双加群と乗法写像の比較は見つからなかった。
- Land–Tamme 2.31 は `IsKConnective` を仮定して、非正 dg 塔の実 Perf 値の連結度と弱同値を比較する。2.32・2.35 のプロ四角形の組立と、2.4・2.6(i) の K 自身の 1 連結性が残る。旧表の 3.12・B.2 の `route` は指定どおり `unknown`。

凍結の根拠は [L2](../../../formalization-plans/archive/stage-i/kst-lanes/L2-comparison.md) と [L6](../../../formalization-plans/archive/stage-i/kst-lanes/L6-pro-excision.md) の冒頭。KST の番号と題名の再確認に伴い (2.3)、2.14、(4.4)、(4.5)、4.15、A.2–A.4 の短い題名を修正した。

型と公理は [KST](kst/kernel-evidence.json) と [Land–Tamme](land-tamme/kernel-evidence.json) の記録にある。none の項目別の引用、概念名、近接する宣言型は [KST](kst/none-search.json) と [Land–Tamme](land-tamme/none-search.json) に記録した。

KST 2.12・5.1 の候補が要求する SSet のモデル圏は、宣言を import した環境で合成できなかった。Kan–Quillen の局所選択は存在するが、`sorry` 付きの存在入力に依存する。[型クラス検査](kst/model-category-evidence.json)
