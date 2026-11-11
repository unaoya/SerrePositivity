# 第6章：goal の5項目の照合

検査対象は main `0bf6fa239` を取り込んだ `research/htt-review`。HTT は `toc.md` に記録した2017-04-09版。照合は本体の宣言のみを対象とし、計画やビルドしない下書きを証明に数えない。

| HTT | 判定 | 照合の要点 |
| --- | --- | --- |
| 6.2.2.1 | partial / special | 通常圏の nerve の場合。`Sieve` の前合成閉性、`Sieve.pullback`、`GrothendieckTopology` の最大篩・基底変換・局所性の三公理を本文と照合した。一般の準圏の slice と篩の比較までは含まない。 |
| 6.2.2.6 | none | 被覆篩が表す mono U→j(c) に局所な **空間値**前層の全部分準圏。通常の `Presheaf.IsSheaf` は matching Hom 集合の一意貼合で、この全 mapping-space 局所性との比較を欠く。 |
| 6.2.2.7 | none | 任意の高次 site の Shv(C) が **位相的**局所化となる主張。一般の Bousfield reflector はあるが、元の被覆篩からの生成辺、local objects＝空間値層、pullback 安定性、同じ反射の左完全性との接続がない。 |
| 6.2.3.5 | none | 元の f の slice 内の τ≤−1(f) が終対象であることと、同じ Čech nerve が **余極限解消**となることの iff。通常の kernel-pair coequalizer・厳密な Čech nerve・BS の環の向きの Čech conerve は、この高次切断との比較を持たない。 |
| 6.5.2.8 | none | 全 ∞-connective morphisms が強飽和かつ小生成という、類全体の同定。指定した辺族の `stronglySaturatedClosure` はあるが、相対ホモトピー層と有効全射性で定めたこの類との同定はない。Kan 空間の Whitehead だけは任意の ∞ トポスの同じ射類の結果ではない。 |

設計の `drafts/Sheaves/SpaceValued.lean` は本体に入っておらず、層化を入力とし `sorry` の残る部分もある。`ModelBridge/Inputs/KanQuillen.lean` のモデル圏の入力は SSet 用で、存在定理には `sorry` がある。これらを完成した空間値層化の instance として用いていない。

6.2.2.1 の3宣言は kernel で確認した。うち `Sieve` と `Sieve.pullback` は変更のない既存検査記録、`GrothendieckTopology` は今回の検査による。詳細な型・公理・検査時点は `check/ch6-6.2-kernel-evidence.json`、他の4項目の個別検索は `check/ch6-6.2.2-none-search.json`・`ch6-6.2.3-none-search.json`・`ch6-6.5.2-none-search.json` にある。
