# P⁰の項目単位の閉包 v3：既形式化の項目で展開を止める（⑤d、2026-11-16）

基準は `deb58367a` を取り込んだ枝 `codex/p0-item-closure`、直前のv2コミットは `68d0a75cc`。今回のユーザー決定11-16を、`formalization-plans/stage-ii/p0/p0-section-map.md` §8–§10の根・項目単位・一般性・モデル圏回避の規則に追加した。

旧1,014項目の `v1/` は変更せず、直前の2,000項目の `items.csv`・`edges.csv`・`order.md`・`excluded-model.csv` は内容そのままで `v2/` に保存した。節単位の経過資料、文献対応表、地図、Leanは変更していない。

## 結果

**2,367項目で探索キューが空になった。reviewの停止規則を適用した参照閉包の採取は完成し、上限4,000項目には届かなかった。** モデル圏なしの代替証明が未確認の項目は下記のとおり残る。これらの証明まで完成したという意味ではない。

位置ごとに重複を統合した辺は **8,852件**（位置を区別しない項目対8,034対）。収録した停止点 **307項目**、出辺を採取した項目2060、未展開キュー0。停止点の出辺は0件。未解決の証明42項目。

| 文献 | 到達項目 | 停止点 | 出辺採取 | 未解決証明 |
|---|---|---|---|---|
| DAGXIII | 27 | 0 | 27 | 0 |
| NS | 25 | 0 | 25 | 0 |
| HA | 277 | 8 | 269 | 14 |
| HTT | 224 | 53 | 171 | 28 |
| Kerodon | 1814 | 246 | 1568 | 0 |
| 合計 | 2367 | 307 | 2060 | 42 |

`items.csv` は5列 `source,number,kind,reached_from,reason` のまま。停止点は `reason` の先頭を `stopped:own`・`stopped:mathlib`・`stopped:both` とし、使用したreviewのファイル・行番号も記録する。状態列や実装状態一覧は新設していない。

## 状態の正本と停止規則

各 `research/<文献>-coverage/review/*.csv` だけを読む。HA・HTT・DAG XIII・NSは `status`、Kerodonは **`status_new`** を使用する。`own`・`mathlib`・`both` は項目を収録したところで停止し、主張・証明・定義入力・代替証明を含めてその項目を始点とする辺を一つも展開しない。`partial`・`none` は従前どおり展開する。11-12以降のコードの再調査や状態の独自判定は行っていない。

reviewに行のない項目は **531項目**。いずれもKerodonのRemark・Example等または新しく原典から同定した項目である。これらに `none` 等の状態を作って割り当てず、停止の根拠がないため展開を続けた。正本にない状態を補う処理はしていない。

| 文献 | reviewファイル数 | 使用列 | review本文を固定したSHA256 |
|---|---|---|---|
| DAGXIII | 3 | status | 237cefaecc01490991eb7789cb140c66cbf0a147ad3e4952ef83869fcec064d8 |
| NS | 8 | status | abffc5aea7948413b6ecb84308c616b0e9e2748de10768f4a77a67318ee86c4a |
| HA | 10 | status | aa6ac73b78dac3b427b43c36302d5ca8c4aa518691504d094c03839d8dad5a77 |
| HTT | 8 | status | e31cab341ed5d7ab135c7058c44ee6e879457e742f1b2b900e7d1dc731a12bcd |
| Kerodon | 10 | status_new | 1f275126da0573eb6d6325fb0e16431b434189aa81cef75f7cd210c7d5731eb8 |

上の指紋は各文献について、reviewの相対パス順の `path SHA256` の行（末尾はLF）を連結してハッシュ化したもの。コミット前に全ファイルがこの採取時の指紋と一致することを検査する。

## 停止点と刈り込み：文献・章ごとの集計

比較対象は **v2の既収録2,000項目**。その採用辺にreview停止だけを適用すると222項目が到達不能になる。そのうち43項目は今回の追加展開で別経路から再到達した。最終表から外れた項目は **179項目**、うちreviewの刈り込みで外れたと確認できるもの **179項目**、それ以外の不在は0項目。今回初めて収録した項目は546項目。

「刈り込みで外れた」は、このv2スナップショットとの比較であり、上限なし・停止なしの全閉包を別途計算したという数ではない。以下の最終除外数は別経路から再到達した項目を差し引いている。モデル圏証明からの除外はこの集計と区別する。章は番号の最初の成分、付録はA・B、NSはローマ数字で集計する。

| 文献 | 停止点 | v2で一旦刈り込み | 別経路で復帰 | 最終的に刈り込みで外れた |
|---|---|---|---|---|
| DAGXIII | 0 | 0 | 0 | 0 |
| NS | 0 | 0 | 0 | 0 |
| HA | 8 | 0 | 0 | 0 |
| HTT | 53 | 53 | 1 | 52 |
| Kerodon | 246 | 169 | 42 | 127 |
| 合計 | 307 | 222 | 43 | 179 |

| 文献 | 章 | 到達項目 | 停止点 | 刈り込みで外れた(v2比) |
|---|---|---|---|---|
| DAGXIII | 1 | 1 | 0 | 0 |
| DAGXIII | 2 | 26 | 0 | 0 |
| NS | A | 1 | 0 | 0 |
| NS | I | 16 | 0 | 0 |
| NS | II | 3 | 0 | 0 |
| NS | III | 3 | 0 | 0 |
| NS | IV | 2 | 0 | 0 |
| HA | 1 | 42 | 8 | 0 |
| HA | 2 | 60 | 0 | 0 |
| HA | 3 | 45 | 0 | 0 |
| HA | 4 | 84 | 0 | 0 |
| HA | 5 | 14 | 0 | 0 |
| HA | 6 | 9 | 0 | 0 |
| HA | 7 | 19 | 0 | 0 |
| HA | A | 4 | 0 | 0 |
| HTT | 1 | 11 | 6 | 2 |
| HTT | 2 | 38 | 15 | 4 |
| HTT | 3 | 25 | 1 | 2 |
| HTT | 4 | 50 | 6 | 12 |
| HTT | 5 | 98 | 24 | 31 |
| HTT | 6 | 0 | 0 | 1 |
| HTT | A | 2 | 1 | 0 |
| Kerodon | 1 | 101 | 37 | 26 |
| Kerodon | 2 | 66 | 7 | 2 |
| Kerodon | 3 | 212 | 42 | 23 |
| Kerodon | 4 | 420 | 83 | 54 |
| Kerodon | 5 | 314 | 28 | 6 |
| Kerodon | 6 | 67 | 12 | 2 |
| Kerodon | 7 | 289 | 25 | 8 |
| Kerodon | 8 | 234 | 7 | 4 |
| Kerodon | 9 | 96 | 5 | 2 |
| Kerodon | 11 | 15 | 0 | 0 |

## 根と到達元

| 文献 | 番号 | 種類 |
|---|---|---|
| DAGXIII | 2.2.6 | Construction |
| DAGXIII | 2.2.7 | Remark |
| NS | I.1.7 | Construction |
| NS | I.1.8 | Lemma |
| NS | I.1.9 | Lemma |
| NS | I.1.10 | Definition |
| NS | I.1.13 | Definition |
| NS | I.3.1 | Theorem |
| NS | III.1.1 | Proposition |
| NS | III.1.2 | Proposition |
| NS | III.1.4 | Definition |
| NS | IV.1.1 | Definition |
| NS | IV.1.2 | Example |

13根は前回と同じ。節の他の項目を一括で追加せず、番号つき項目の主張・証明の引用を追う。定義・記法や別位置の証明も入力に含む。`reached_from` は採用した全辺で再計算し、DAG-only（DAG根だけ）、DAG+NS（両方）、NS-only（NS根だけ）の後に直接の親・根の印を置いた。

| 到達元 | 項目数 |
|---|---|
| DAG+NS | 203 |
| DAG-only | 2070 |
| NS-only | 94 |

## モデル圏を使う証明の差替え

§9の規則は維持する。停止点でないHA・HTTの数学的主張は元の番号・全仮定・全結論を保持し、モデル圏を使う原証明の出辺は採用しない。同じ一般性のKerodon証明を検収できた場合だけ `kind=kerodon-proof` の辺を置く。

今回は **1項目・2辺**。

| 元の項目 | 採用するKerodon項目・原典 | 一般性の比較 |
|---|---|---|
| HTT 5.5.3.12 | [7.1.9.8](https://kerodon.net/tag/06AJ) | 三つのpresentable∞圏、両脚colimit-preserving。前者でpresentability、後者で射影のcolimit保存とその反映という残りの結論を得る。原証明のproof出辺を採用しない。将来のdocstringにも原典項目・採用Tag・差替えを記録する |
| HTT 5.5.3.12 | [9.5.4.6](https://kerodon.net/tag/06PA) | 三つのpresentable∞圏、両脚colimit-preserving。前者でpresentability、後者で射影のcolimit保存とその反映という残りの結論を得る。原証明のproof出辺を採用しない。将来のdocstringにも原典項目・採用Tag・差替えを記録する |

v2で差し替えた4項目のうちHTT4.1.3.1はreviewのownで展開を止め、HTT3.3.1.3・5.4.6.6は刈り込み後の閉包に残らなかった。そのため今回はHTT5.5.3.12からの2辺だけを差替え辺として数える。HTT5.5.3.12はpresentabilityだけでなく射影のcolimit保存とその判定も必要で、9.5.4.6（06PA）と7.1.9.8（06AJ）を併用する。対応表の似た番号だけから同じ主張と推測していない。将来のdocstringに元の項目・採用番号／Tag・証明差替え・opposite等を記すべき箇所であり、今回Leanへの追記はしていない。

### 未解決の証明

次の項目は `reason` にも `unresolved:` と記録した。代替証明が未確認のままモデル圏を使う原証明の出辺を切っているため、これはモデル圏なしの証明の完成を意味しない。`[ModelCategory SSet]` を仮定する構成も置いていない。

| 文献 | 番号 | 未解決の理由 |
|---|---|---|
| HA | 2.4.1.8 | 元の証明にモデル圏の使用（直接、またはモデル圏についての補題への参照）がある。同じ全主張・全仮定のモデル圏なしKerodon証明は今回の対応表・原典検索では確認できなかった |
| HA | 3.1.2.3 | 元の証明にモデル圏の使用（直接、またはモデル圏についての補題への参照）がある。同じ全主張・全仮定のモデル圏なしKerodon証明は今回の対応表・原典検索では確認できなかった |
| HA | 3.2.2.1 | 元の証明にモデル圏の使用（直接、またはモデル圏についての補題への参照）がある。同じ全主張・全仮定のモデル圏なしKerodon証明は今回の対応表・原典検索では確認できなかった |
| HA | 3.2.2.8 | 元の証明にモデル圏の使用（直接、またはモデル圏についての補題への参照）がある。同じ全主張・全仮定のモデル圏なしKerodon証明は今回の対応表・原典検索では確認できなかった |
| HA | 3.2.4.3 | 元の証明にモデル圏の使用（直接、またはモデル圏についての補題への参照）がある。同じ全主張・全仮定のモデル圏なしKerodon証明は今回の対応表・原典検索では確認できなかった |
| HA | 3.4.1.4 | 元の証明にモデル圏の使用（直接、またはモデル圏についての補題への参照）がある。同じ全主張・全仮定のモデル圏なしKerodon証明は今回の対応表・原典検索では確認できなかった |
| HA | 3.4.4.3 | 元の証明にモデル圏の使用（直接、またはモデル圏についての補題への参照）がある。同じ全主張・全仮定のモデル圏なしKerodon証明は今回の対応表・原典検索では確認できなかった |
| HA | 4.2.2.12 | 主張はAlg_LMとLMod_Aの∞圏の同値。モデル圏の言い換え自体を主張と分類しない。元証明のモデル圏使用に代わる同じ一般性のKerodon証明は未確認 |
| HA | 4.4.1.11 | 元の証明にモデル圏の使用（直接、またはモデル圏についての補題への参照）がある。同じ全主張・全仮定のモデル圏なしKerodon証明は今回の対応表・原典検索では確認できなかった |
| HA | 4.4.1.28 | 元の証明にモデル圏の使用（直接、またはモデル圏についての補題への参照）がある。同じ全主張・全仮定のモデル圏なしKerodon証明は今回の対応表・原典検索では確認できなかった |
| HA | 4.8.1.2 | 主張・定義自体がモデル圏の構造・対象を使う。採用経路がstatementの入力の場合は未解決として主張を保持 |
| HA | 5.1.3.2 | 元の証明にモデル圏の使用（直接、またはモデル圏についての補題への参照）がある。同じ全主張・全仮定のモデル圏なしKerodon証明は今回の対応表・原典検索では確認できなかった |
| HA | 7.1.2.13 | 元の証明にモデル圏の使用（直接、またはモデル圏についての補題への参照）がある。同じ全主張・全仮定のモデル圏なしKerodon証明は今回の対応表・原典検索では確認できなかった |
| HA | A.3.2 | 元の証明にモデル圏の使用（直接、またはモデル圏についての補題への参照）がある。同じ全主張・全仮定のモデル圏なしKerodon証明は今回の対応表・原典検索では確認できなかった |
| HTT | 2.3.4.18 | 元の証明にモデル圏の使用（直接、またはモデル圏についての補題への参照）がある。同じ全主張・全仮定のモデル圏なしKerodon証明は今回の対応表・原典検索では確認できなかった |
| HTT | 3.2.2.12 | 元の証明にモデル圏の使用（直接、またはモデル圏についての補題への参照）がある。同じ全主張・全仮定のモデル圏なしKerodon証明は今回の対応表・原典検索では確認できなかった |
| HTT | 3.3.1.2 | 元の証明にモデル圏の使用（直接、またはモデル圏についての補題への参照）がある。同じ全主張・全仮定のモデル圏なしKerodon証明は今回の対応表・原典検索では確認できなかった |
| HTT | 3.3.1.5 | 元の証明にモデル圏の使用（直接、またはモデル圏についての補題への参照）がある。同じ全主張・全仮定のモデル圏なしKerodon証明は今回の対応表・原典検索では確認できなかった |
| HTT | 3.3.3.1 | 元の証明にモデル圏の使用（直接、またはモデル圏についての補題への参照）がある。同じ全主張・全仮定のモデル圏なしKerodon証明は今回の対応表・原典検索では確認できなかった |
| HTT | 3.3.4.5 | 元の証明にモデル圏の使用（直接、またはモデル圏についての補題への参照）がある。同じ全主張・全仮定のモデル圏なしKerodon証明は今回の対応表・原典検索では確認できなかった |
| HTT | 4.1.1.8 | 元の証明にモデル圏の使用（直接、またはモデル圏についての補題への参照）がある。同じ全主張・全仮定のモデル圏なしKerodon証明は今回の対応表・原典検索では確認できなかった |
| HTT | 4.1.2.13 | 元の証明にモデル圏の使用（直接、またはモデル圏についての補題への参照）がある。同じ全主張・全仮定のモデル圏なしKerodon証明は今回の対応表・原典検索では確認できなかった |
| HTT | 4.1.2.14 | 元の証明にモデル圏の使用（直接、またはモデル圏についての補題への参照）がある。同じ全主張・全仮定のモデル圏なしKerodon証明は今回の対応表・原典検索では確認できなかった |
| HTT | 4.1.2.17 | 元の証明にモデル圏の使用（直接、またはモデル圏についての補題への参照）がある。同じ全主張・全仮定のモデル圏なしKerodon証明は今回の対応表・原典検索では確認できなかった |
| HTT | 4.2.2.4 | 元の証明にモデル圏の使用（直接、またはモデル圏についての補題への参照）がある。同じ全主張・全仮定のモデル圏なしKerodon証明は今回の対応表・原典検索では確認できなかった |
| HTT | 4.3.1.7 | 元の証明にモデル圏の使用（直接、またはモデル圏についての補題への参照）がある。同じ全主張・全仮定のモデル圏なしKerodon証明は今回の対応表・原典検索では確認できなかった |
| HTT | 4.3.1.9 | 元の証明にモデル圏の使用（直接、またはモデル圏についての補題への参照）がある。同じ全主張・全仮定のモデル圏なしKerodon証明は今回の対応表・原典検索では確認できなかった |
| HTT | 4.3.2.7 | 元の証明にモデル圏の使用（直接、またはモデル圏についての補題への参照）がある。同じ全主張・全仮定のモデル圏なしKerodon証明は今回の対応表・原典検索では確認できなかった |
| HTT | 4.3.3.10 | 元の証明にモデル圏の使用（直接、またはモデル圏についての補題への参照）がある。同じ全主張・全仮定のモデル圏なしKerodon証明は今回の対応表・原典検索では確認できなかった |
| HTT | 4.4.4.5 | 元の証明にモデル圏の使用（直接、またはモデル圏についての補題への参照）がある。同じ全主張・全仮定のモデル圏なしKerodon証明は今回の対応表・原典検索では確認できなかった |
| HTT | 5.1.3.1 | 候補Kerodon8.3.3.13（Tag03NJ）はlocally small∞圏が域。HTTは任意の単体集合K。一般Kからの移送・旧式Yoneda構成との比較をモデル圏なしに検収していない |
| HTT | 5.1.5.2 | 元の証明にモデル圏の使用（直接、またはモデル圏についての補題への参照）がある。同じ全主張・全仮定のモデル圏なしKerodon証明は今回の対応表・原典検索では確認できなかった |
| HTT | 5.2.8.22 | 元の証明にモデル圏の使用（直接、またはモデル圏についての補題への参照）がある。同じ全主張・全仮定のモデル圏なしKerodon証明は今回の対応表・原典検索では確認できなかった |
| HTT | 5.3.3.3 | 元の証明にモデル圏の使用（直接、またはモデル圏についての補題への参照）がある。同じ全主張・全仮定のモデル圏なしKerodon証明は今回の対応表・原典検索では確認できなかった |
| HTT | 5.3.4.9 | 元の証明にモデル圏の使用（直接、またはモデル圏についての補題への参照）がある。同じ全主張・全仮定のモデル圏なしKerodon証明は今回の対応表・原典検索では確認できなかった |
| HTT | 5.3.4.10 | 元の証明にモデル圏の使用（直接、またはモデル圏についての補題への参照）がある。同じ全主張・全仮定のモデル圏なしKerodon証明は今回の対応表・原典検索では確認できなかった |
| HTT | 5.3.4.12 | 元の証明にモデル圏の使用（直接、またはモデル圏についての補題への参照）がある。同じ全主張・全仮定のモデル圏なしKerodon証明は今回の対応表・原典検索では確認できなかった |
| HTT | 5.3.4.14 | 元の証明にモデル圏の使用（直接、またはモデル圏についての補題への参照）がある。同じ全主張・全仮定のモデル圏なしKerodon証明は今回の対応表・原典検索では確認できなかった |
| HTT | 5.4.1.2 | 元の証明にモデル圏の使用（直接、またはモデル圏についての補題への参照）がある。同じ全主張・全仮定のモデル圏なしKerodon証明は今回の対応表・原典検索では確認できなかった |
| HTT | 5.4.4.1 | 元の証明にモデル圏の使用（直接、またはモデル圏についての補題への参照）がある。同じ全主張・全仮定のモデル圏なしKerodon証明は今回の対応表・原典検索では確認できなかった |
| HTT | 5.4.5.7 | 候補Kerodon9.2.9.1（06F6）は(κ,λ)-compactness、µ-smallなdiagramのlimit。HTTのκ-filtered colimit・κ-compactnessとの全てのcardinal/universe条件の比較は未検収 |
| HTT | 5.4.5.13 | 候補Kerodon9.2.8.11（06N1）は(κ,λ)-compactness。HTTの全regular κでのκ-compactnessとの比較を未検収 |

Kerodonのprojectively cofibrant（Definition7.5.6.1、Tag03C4）はlevelwise trivial Kan fibrationに対する持ち上げ性。7.5.6.6（03CA）、9.1.6.9（03DN）もその直接の性質である。7.5.3.3（03AS）のexplicit isofibrant replacementはweighted nerveとstrict transportによる明示構成で、7.5.3.7（03AW）・7.5.3.12（03B1）の証明もこの構成・isofibrationを使う。語の部分一致（isofibrant replacement中のfibrant replacement等）をModelCategoryの仮定と誤認しない。これは文献の証明経路の検収であり、reviewの実装状態を再判定したものではない。

### モデル圏証明だけから届く項目の除外表

`excluded-model.csv` はv2で検収した387項目のうち、現在の項目と重ならない **383項目**を継承する。新たなreview停止による刈り込みをモデル圏除外と混ぜていない。`cut_from` と根拠位置は元の証明経路を切る理由を保持する。一般の補助命題を含む original-proof-helper は主張自体がモデル圏についてだという判定ではない。v2の未展開部分からの再到達で保持が必要になった項目はこの表から除く。未解決の証明が残るため、永久に不要だと認定した表ではない。

## 原典の参照の検収

DAG XIII（2011-12-15）、NS（arXiv:1707.01799v2）、HA（2017-09-18）、HTT（2017-04-09）のPDF・番号付き項目の位置はv2と同じ。出典URLとPDF指紋は `v2/order.md` の「原典と採取位置」を参照する。辺の `PDF p.` は物理ページ、`text L` は `pdftotext -layout` の1始まりの行。Kerodonは公式Tagページの主張と付随する証明のarticleだけを読む。ナビゲーション・節導入の文章は出辺にしない。

v2で残っていた NS I.1.1→HA§6.1.6 の節参照は、preadditive/semiadditiveのDefinition6.1.6.13へ具体化した。Kerodonの定義入力（∞圏、単体集合、Kan complex、(co)Cartesian fibration/edge、projectively cofibrant diagram）も用語の使用から同定した。到達先がreviewでown・mathlib・bothなら、そこで止める。

式のTagは原典HTMLでその式を含む番号つき項目へ戻す。自項目内の式は別項目として数えず、他項目の式は `kind=kerodon-equation-owner` の辺にする。Tag06SQは項目ではなく§4.8.4であり、引用元Example4.8.2.16が明記するTheorem4.8.4.1へ解決した。

今回原典で番号つき項目と確認した、従来のKerodon目録にない項目は **15項目**。状態はreviewから新設せず、該当番号のreview行がなければ展開する。既存対応表を書き換えず、次の差を報告する。

| 原典番号 | 種類 | Tag |
|---|---|---|
| 11.5.0.111 | Proposition | [025C](https://kerodon.net/tag/025C) |
| 11.9.6.1 | Proposition | [03PB](https://kerodon.net/tag/03PB) |
| 11.9.6.2 | Proposition | [03PE](https://kerodon.net/tag/03PE) |
| 11.9.6.3 | Corollary | [03PF](https://kerodon.net/tag/03PF) |
| 11.9.6.4 | Remark | [03PG](https://kerodon.net/tag/03PG) |
| 11.9.6.5 | Proposition | [03PH](https://kerodon.net/tag/03PH) |
| 11.9.8.5 | Proposition | [025B](https://kerodon.net/tag/025B) |
| 11.9.8.7 | Corollary | [025F](https://kerodon.net/tag/025F) |
| 11.9.9.1 | Remark | [026Y](https://kerodon.net/tag/026Y) |
| 11.9.9.2 | Construction | [029M](https://kerodon.net/tag/029M) |
| 11.9.9.3 | Lemma | [029N](https://kerodon.net/tag/029N) |
| 11.9.9.4 | Lemma | [029P](https://kerodon.net/tag/029P) |
| 11.9.9.6 | Lemma | [029R](https://kerodon.net/tag/029R) |
| 11.9.9.7 | Lemma | [029S](https://kerodon.net/tag/029S) |
| 11.9.9.8 | Remark | [029T](https://kerodon.net/tag/029T) |

番号引用の未同定は0件、原典取得失敗0件、未解決の非項目タグ参照0件。NSの上記節参照は採取器の原ログに残るが、定義入力の辺によって解決済みである。既存目録の番号・種類と取得原典の不一致は0件。

Kerodonの一括PDFと現行HTMLの番号の違い（例：Tag02QE）はv2で報告したとおり。現在のTagと既存目録が一致する項目はその番号を使い、PDFの古い番号を流用しない。

<details>
<summary>節ごとの到達項目数</summary>

| 文献 | 節 | 項目数 |
|---|---|---|
| DAGXIII | 1.1 | 1 |
| DAGXIII | 2.1 | 19 |
| DAGXIII | 2.2 | 7 |
| NS | A | 1 |
| NS | I.1 | 10 |
| NS | I.3 | 5 |
| NS | I.4 | 1 |
| NS | II.2 | 3 |
| NS | III.1 | 3 |
| NS | IV.1 | 2 |
| HA | 1.1.1 | 3 |
| HA | 1.1.2 | 6 |
| HA | 1.1.3 | 3 |
| HA | 1.1.4 | 1 |
| HA | 1.2.1 | 5 |
| HA | 1.4.2 | 20 |
| HA | 1.4.3 | 1 |
| HA | 1.4.4 | 3 |
| HA | 2 | 3 |
| HA | 2.1.1 | 9 |
| HA | 2.1.2 | 8 |
| HA | 2.1.3 | 3 |
| HA | 2.2.1 | 6 |
| HA | 2.2.4 | 10 |
| HA | 2.2.5 | 1 |
| HA | 2.3.1 | 1 |
| HA | 2.3.2 | 4 |
| HA | 2.3.3 | 2 |
| HA | 2.4.1 | 6 |
| HA | 2.4.2 | 6 |
| HA | 2.4.3 | 1 |
| HA | 3.1.1 | 15 |
| HA | 3.1.2 | 1 |
| HA | 3.2.1 | 7 |
| HA | 3.2.2 | 4 |
| HA | 3.2.4 | 5 |
| HA | 3.3.1 | 1 |
| HA | 3.3.2 | 1 |
| HA | 3.4.1 | 5 |
| HA | 3.4.3 | 3 |
| HA | 3.4.4 | 3 |
| HA | 4.1.1 | 4 |
| HA | 4.1.2 | 4 |
| HA | 4.1.3 | 1 |
| HA | 4.1.7 | 1 |
| HA | 4.2.1 | 7 |
| HA | 4.2.2 | 8 |
| HA | 4.2.3 | 4 |
| HA | 4.2.4 | 2 |
| HA | 4.3.1 | 2 |
| HA | 4.3.2 | 3 |
| HA | 4.4.1 | 6 |
| HA | 4.4.2 | 4 |
| HA | 4.4.3 | 1 |
| HA | 4.5.1 | 1 |
| HA | 4.5.2 | 2 |
| HA | 4.6.2 | 9 |
| HA | 4.7.3 | 3 |
| HA | 4.7.4 | 1 |
| HA | 4.8.1 | 4 |
| HA | 4.8.2 | 1 |
| HA | 4.8.3 | 5 |
| HA | 4.8.4 | 10 |
| HA | 4.8.5 | 1 |
| HA | 5.1 | 1 |
| HA | 5.1.1 | 8 |
| HA | 5.1.3 | 2 |
| HA | 5.1.4 | 2 |
| HA | 5.3.1 | 1 |
| HA | 6.1.6 | 9 |
| HA | 7.1 | 1 |
| HA | 7.1.1 | 1 |
| HA | 7.1.2 | 1 |
| HA | 7.1.3 | 6 |
| HA | 7.2.4 | 2 |
| HA | 7.3.2 | 6 |
| HA | 7.5 | 2 |
| HA | A.3 | 4 |
| HTT | 1.1.2 | 2 |
| HTT | 1.1.4 | 1 |
| HTT | 1.1.5 | 4 |
| HTT | 1.2.4 | 1 |
| HTT | 1.2.9 | 1 |
| HTT | 1.2.13 | 2 |
| HTT | 2.0.0 | 1 |
| HTT | 2.1.2 | 7 |
| HTT | 2.1.3 | 2 |
| HTT | 2.2.2 | 1 |
| HTT | 2.3.4 | 2 |
| HTT | 2.4.1 | 6 |
| HTT | 2.4.2 | 4 |
| HTT | 2.4.4 | 9 |
| HTT | 2.4.5 | 1 |
| HTT | 2.4.7 | 5 |
| HTT | 3.1.0 | 1 |
| HTT | 3.1.1 | 7 |
| HTT | 3.1.2 | 2 |
| HTT | 3.1.3 | 2 |
| HTT | 3.2.2 | 3 |
| HTT | 3.3.1 | 3 |
| HTT | 3.3.2 | 3 |
| HTT | 3.3.3 | 3 |
| HTT | 3.3.4 | 1 |
| HTT | 4.1.1 | 3 |
| HTT | 4.1.2 | 6 |
| HTT | 4.1.3 | 1 |
| HTT | 4.2.2 | 2 |
| HTT | 4.2.3 | 7 |
| HTT | 4.2.4 | 1 |
| HTT | 4.3.1 | 8 |
| HTT | 4.3.2 | 9 |
| HTT | 4.3.3 | 3 |
| HTT | 4.4.2 | 5 |
| HTT | 4.4.3 | 2 |
| HTT | 4.4.4 | 3 |
| HTT | 5.1.2 | 2 |
| HTT | 5.1.3 | 2 |
| HTT | 5.1.5 | 5 |
| HTT | 5.1.6 | 3 |
| HTT | 5.2.2 | 4 |
| HTT | 5.2.3 | 1 |
| HTT | 5.2.4 | 3 |
| HTT | 5.2.7 | 6 |
| HTT | 5.2.8 | 4 |
| HTT | 5.3.1 | 3 |
| HTT | 5.3.2 | 1 |
| HTT | 5.3.3 | 1 |
| HTT | 5.3.4 | 10 |
| HTT | 5.3.5 | 9 |
| HTT | 5.3.6 | 3 |
| HTT | 5.4.1 | 1 |
| HTT | 5.4.2 | 2 |
| HTT | 5.4.4 | 3 |
| HTT | 5.4.5 | 9 |
| HTT | 5.4.7 | 3 |
| HTT | 5.5.0 | 1 |
| HTT | 5.5.1 | 4 |
| HTT | 5.5.2 | 2 |
| HTT | 5.5.3 | 7 |
| HTT | 5.5.4 | 6 |
| HTT | 5.5.7 | 2 |
| HTT | 5.5.8 | 1 |
| HTT | A.1.2 | 1 |
| HTT | A.2.6 | 1 |
| Kerodon | 1.1.0 | 6 |
| Kerodon | 1.1.1 | 2 |
| Kerodon | 1.1.2 | 4 |
| Kerodon | 1.1.3 | 10 |
| Kerodon | 1.1.4 | 7 |
| Kerodon | 1.1.5 | 2 |
| Kerodon | 1.1.6 | 3 |
| Kerodon | 1.2.1 | 2 |
| Kerodon | 1.2.3 | 2 |
| Kerodon | 1.2.4 | 1 |
| Kerodon | 1.2.5 | 1 |
| Kerodon | 1.3.1 | 2 |
| Kerodon | 1.3.3 | 1 |
| Kerodon | 1.3.4 | 3 |
| Kerodon | 1.3.5 | 1 |
| Kerodon | 1.3.6 | 1 |
| Kerodon | 1.3.7 | 7 |
| Kerodon | 1.4.0 | 2 |
| Kerodon | 1.4.2 | 1 |
| Kerodon | 1.4.3 | 1 |
| Kerodon | 1.4.4 | 1 |
| Kerodon | 1.4.5 | 2 |
| Kerodon | 1.4.6 | 4 |
| Kerodon | 1.5.1 | 1 |
| Kerodon | 1.5.2 | 6 |
| Kerodon | 1.5.3 | 2 |
| Kerodon | 1.5.4 | 7 |
| Kerodon | 1.5.5 | 5 |
| Kerodon | 1.5.6 | 6 |
| Kerodon | 1.5.7 | 8 |
| Kerodon | 2.1.2 | 1 |
| Kerodon | 2.1.3 | 1 |
| Kerodon | 2.1.5 | 1 |
| Kerodon | 2.1.7 | 4 |
| Kerodon | 2.2.0 | 3 |
| Kerodon | 2.2.1 | 3 |
| Kerodon | 2.2.4 | 3 |
| Kerodon | 2.2.5 | 4 |
| Kerodon | 2.3.1 | 4 |
| Kerodon | 2.3.2 | 3 |
| Kerodon | 2.3.5 | 3 |
| Kerodon | 2.4.1 | 5 |
| Kerodon | 2.4.2 | 4 |
| Kerodon | 2.4.3 | 7 |
| Kerodon | 2.4.4 | 9 |
| Kerodon | 2.4.5 | 6 |
| Kerodon | 2.4.6 | 5 |
| Kerodon | 3.1.1 | 6 |
| Kerodon | 3.1.2 | 5 |
| Kerodon | 3.1.3 | 7 |
| Kerodon | 3.1.5 | 9 |
| Kerodon | 3.1.6 | 1 |
| Kerodon | 3.1.7 | 14 |
| Kerodon | 3.1.8 | 5 |
| Kerodon | 3.2.1 | 2 |
| Kerodon | 3.2.2 | 3 |
| Kerodon | 3.2.3 | 6 |
| Kerodon | 3.2.4 | 12 |
| Kerodon | 3.2.5 | 3 |
| Kerodon | 3.2.6 | 9 |
| Kerodon | 3.2.7 | 2 |
| Kerodon | 3.2.8 | 4 |
| Kerodon | 3.3.1 | 6 |
| Kerodon | 3.3.2 | 7 |
| Kerodon | 3.3.3 | 3 |
| Kerodon | 3.3.4 | 2 |
| Kerodon | 3.3.5 | 2 |
| Kerodon | 3.3.6 | 9 |
| Kerodon | 3.3.7 | 7 |
| Kerodon | 3.4.0 | 5 |
| Kerodon | 3.4.1 | 11 |
| Kerodon | 3.4.2 | 5 |
| Kerodon | 3.4.5 | 8 |
| Kerodon | 3.4.6 | 4 |
| Kerodon | 3.5.1 | 17 |
| Kerodon | 3.5.2 | 4 |
| Kerodon | 3.5.3 | 7 |
| Kerodon | 3.5.7 | 4 |
| Kerodon | 3.5.9 | 6 |
| Kerodon | 3.6.1 | 11 |
| Kerodon | 3.6.2 | 4 |
| Kerodon | 3.6.3 | 1 |
| Kerodon | 3.6.4 | 1 |
| Kerodon | 4.1.1 | 8 |
| Kerodon | 4.1.2 | 10 |
| Kerodon | 4.1.3 | 3 |
| Kerodon | 4.1.4 | 5 |
| Kerodon | 4.2.1 | 3 |
| Kerodon | 4.2.3 | 1 |
| Kerodon | 4.2.4 | 1 |
| Kerodon | 4.2.5 | 4 |
| Kerodon | 4.2.6 | 3 |
| Kerodon | 4.3.1 | 1 |
| Kerodon | 4.3.2 | 1 |
| Kerodon | 4.3.3 | 5 |
| Kerodon | 4.3.5 | 2 |
| Kerodon | 4.3.6 | 13 |
| Kerodon | 4.3.7 | 8 |
| Kerodon | 4.4.1 | 5 |
| Kerodon | 4.4.2 | 9 |
| Kerodon | 4.4.3 | 14 |
| Kerodon | 4.4.4 | 5 |
| Kerodon | 4.4.5 | 10 |
| Kerodon | 4.5.1 | 13 |
| Kerodon | 4.5.2 | 5 |
| Kerodon | 4.5.3 | 23 |
| Kerodon | 4.5.4 | 11 |
| Kerodon | 4.5.5 | 11 |
| Kerodon | 4.5.6 | 11 |
| Kerodon | 4.5.7 | 14 |
| Kerodon | 4.5.8 | 7 |
| Kerodon | 4.6.1 | 10 |
| Kerodon | 4.6.2 | 6 |
| Kerodon | 4.6.3 | 6 |
| Kerodon | 4.6.4 | 11 |
| Kerodon | 4.6.5 | 5 |
| Kerodon | 4.6.6 | 1 |
| Kerodon | 4.6.7 | 21 |
| Kerodon | 4.6.8 | 13 |
| Kerodon | 4.7.1 | 5 |
| Kerodon | 4.7.2 | 3 |
| Kerodon | 4.7.3 | 12 |
| Kerodon | 4.7.6 | 10 |
| Kerodon | 4.8.1 | 6 |
| Kerodon | 4.8.2 | 23 |
| Kerodon | 4.8.3 | 13 |
| Kerodon | 4.8.4 | 7 |
| Kerodon | 4.8.5 | 3 |
| Kerodon | 4.8.8 | 7 |
| Kerodon | 4.9.1 | 3 |
| Kerodon | 4.9.2 | 3 |
| Kerodon | 4.9.3 | 7 |
| Kerodon | 4.9.4 | 16 |
| Kerodon | 4.9.5 | 11 |
| Kerodon | 4.9.6 | 2 |
| Kerodon | 4.9.7 | 2 |
| Kerodon | 4.9.8 | 8 |
| Kerodon | 5.1.1 | 14 |
| Kerodon | 5.1.2 | 5 |
| Kerodon | 5.1.3 | 9 |
| Kerodon | 5.1.4 | 16 |
| Kerodon | 5.1.5 | 3 |
| Kerodon | 5.1.6 | 7 |
| Kerodon | 5.1.7 | 11 |
| Kerodon | 5.2.1 | 3 |
| Kerodon | 5.2.2 | 10 |
| Kerodon | 5.2.3 | 8 |
| Kerodon | 5.2.4 | 5 |
| Kerodon | 5.2.5 | 3 |
| Kerodon | 5.2.6 | 2 |
| Kerodon | 5.2.8 | 11 |
| Kerodon | 5.3.1 | 15 |
| Kerodon | 5.3.2 | 15 |
| Kerodon | 5.3.3 | 18 |
| Kerodon | 5.3.4 | 10 |
| Kerodon | 5.3.5 | 6 |
| Kerodon | 5.3.6 | 9 |
| Kerodon | 5.3.7 | 5 |
| Kerodon | 5.3.8 | 4 |
| Kerodon | 5.4.1 | 1 |
| Kerodon | 5.4.2 | 5 |
| Kerodon | 5.4.3 | 4 |
| Kerodon | 5.4.4 | 2 |
| Kerodon | 5.4.5 | 8 |
| Kerodon | 5.4.6 | 7 |
| Kerodon | 5.4.7 | 7 |
| Kerodon | 5.4.8 | 7 |
| Kerodon | 5.4.9 | 1 |
| Kerodon | 5.5.3 | 9 |
| Kerodon | 5.5.4 | 1 |
| Kerodon | 5.5.5 | 7 |
| Kerodon | 5.6.0 | 2 |
| Kerodon | 5.6.2 | 14 |
| Kerodon | 5.6.4 | 5 |
| Kerodon | 5.6.5 | 15 |
| Kerodon | 5.6.6 | 14 |
| Kerodon | 5.6.7 | 7 |
| Kerodon | 5.6.8 | 7 |
| Kerodon | 5.6.9 | 2 |
| Kerodon | 6.1.1 | 2 |
| Kerodon | 6.1.2 | 1 |
| Kerodon | 6.1.3 | 6 |
| Kerodon | 6.1.4 | 1 |
| Kerodon | 6.2.1 | 4 |
| Kerodon | 6.2.2 | 5 |
| Kerodon | 6.2.5 | 7 |
| Kerodon | 6.2.6 | 3 |
| Kerodon | 6.3.1 | 15 |
| Kerodon | 6.3.2 | 10 |
| Kerodon | 6.3.4 | 4 |
| Kerodon | 6.3.5 | 8 |
| Kerodon | 6.3.6 | 1 |
| Kerodon | 7.1.0 | 1 |
| Kerodon | 7.1.1 | 9 |
| Kerodon | 7.1.2 | 8 |
| Kerodon | 7.1.3 | 8 |
| Kerodon | 7.1.4 | 6 |
| Kerodon | 7.1.5 | 11 |
| Kerodon | 7.1.6 | 15 |
| Kerodon | 7.1.7 | 6 |
| Kerodon | 7.1.8 | 9 |
| Kerodon | 7.1.9 | 8 |
| Kerodon | 7.2.1 | 13 |
| Kerodon | 7.2.2 | 12 |
| Kerodon | 7.2.3 | 10 |
| Kerodon | 7.3.1 | 10 |
| Kerodon | 7.3.2 | 5 |
| Kerodon | 7.3.3 | 5 |
| Kerodon | 7.3.4 | 2 |
| Kerodon | 7.3.5 | 8 |
| Kerodon | 7.3.6 | 13 |
| Kerodon | 7.3.7 | 6 |
| Kerodon | 7.3.8 | 12 |
| Kerodon | 7.4.1 | 8 |
| Kerodon | 7.4.2 | 3 |
| Kerodon | 7.4.3 | 7 |
| Kerodon | 7.4.4 | 7 |
| Kerodon | 7.4.5 | 10 |
| Kerodon | 7.4.6 | 3 |
| Kerodon | 7.5.1 | 4 |
| Kerodon | 7.5.2 | 9 |
| Kerodon | 7.5.3 | 10 |
| Kerodon | 7.5.4 | 9 |
| Kerodon | 7.5.5 | 9 |
| Kerodon | 7.5.6 | 2 |
| Kerodon | 7.5.7 | 1 |
| Kerodon | 7.5.8 | 7 |
| Kerodon | 7.6.2 | 6 |
| Kerodon | 7.6.3 | 6 |
| Kerodon | 7.6.6 | 6 |
| Kerodon | 7.7.0 | 3 |
| Kerodon | 7.7.7 | 2 |
| Kerodon | 8.1.0 | 2 |
| Kerodon | 8.1.1 | 8 |
| Kerodon | 8.1.2 | 14 |
| Kerodon | 8.1.3 | 7 |
| Kerodon | 8.1.4 | 5 |
| Kerodon | 8.1.6 | 10 |
| Kerodon | 8.1.7 | 9 |
| Kerodon | 8.1.9 | 5 |
| Kerodon | 8.1.10 | 4 |
| Kerodon | 8.2.0 | 4 |
| Kerodon | 8.2.1 | 7 |
| Kerodon | 8.2.2 | 8 |
| Kerodon | 8.2.3 | 7 |
| Kerodon | 8.2.4 | 6 |
| Kerodon | 8.2.5 | 2 |
| Kerodon | 8.2.6 | 2 |
| Kerodon | 8.3.1 | 5 |
| Kerodon | 8.3.2 | 12 |
| Kerodon | 8.3.3 | 11 |
| Kerodon | 8.3.4 | 11 |
| Kerodon | 8.3.5 | 5 |
| Kerodon | 8.3.7 | 6 |
| Kerodon | 8.4.1 | 8 |
| Kerodon | 8.4.2 | 6 |
| Kerodon | 8.4.3 | 3 |
| Kerodon | 8.4.6 | 7 |
| Kerodon | 8.5.1 | 1 |
| Kerodon | 8.5.2 | 2 |
| Kerodon | 8.5.3 | 1 |
| Kerodon | 8.5.4 | 1 |
| Kerodon | 8.5.5 | 2 |
| Kerodon | 8.5.6 | 6 |
| Kerodon | 8.6.1 | 3 |
| Kerodon | 8.6.2 | 7 |
| Kerodon | 8.6.3 | 10 |
| Kerodon | 8.6.4 | 3 |
| Kerodon | 8.6.5 | 15 |
| Kerodon | 8.6.6 | 8 |
| Kerodon | 8.6.8 | 1 |
| Kerodon | 9.1.0 | 1 |
| Kerodon | 9.1.1 | 8 |
| Kerodon | 9.1.3 | 10 |
| Kerodon | 9.1.4 | 10 |
| Kerodon | 9.1.5 | 8 |
| Kerodon | 9.1.6 | 8 |
| Kerodon | 9.1.8 | 2 |
| Kerodon | 9.1.9 | 5 |
| Kerodon | 9.2.0 | 2 |
| Kerodon | 9.2.1 | 1 |
| Kerodon | 9.2.2 | 3 |
| Kerodon | 9.2.3 | 1 |
| Kerodon | 9.2.4 | 2 |
| Kerodon | 9.2.5 | 5 |
| Kerodon | 9.2.8 | 2 |
| Kerodon | 9.3.1 | 3 |
| Kerodon | 9.3.2 | 3 |
| Kerodon | 9.3.4 | 8 |
| Kerodon | 9.3.7 | 3 |
| Kerodon | 9.4.4 | 3 |
| Kerodon | 9.4.5 | 2 |
| Kerodon | 9.4.8 | 1 |
| Kerodon | 9.4.9 | 2 |
| Kerodon | 9.5.4 | 3 |
| Kerodon | 11.5.0 | 1 |
| Kerodon | 11.9.6 | 5 |
| Kerodon | 11.9.8 | 2 |
| Kerodon | 11.9.9 | 7 |

</details>

## 小さい検収

CSVの列、項目キーの一意性、13根、根からの到達、到達元分類、全辺の両端、停止点の出辺0件と `stopped:<状態>`、reviewの固定指紋、文献・章別集計、強連結成分間の依存順、除外表との非交差を検査した。v2の4ファイルとv1の3ファイルは前コミットの内容とバイト一致。差分はこの閉包の紙資料のみで、対応表・地図・Leanの変更とビルドは行っていない。

## 依存の順

辺は「使う項目→前提」。強連結成分を縮約したDAGで前提を先に並べる。2253成分、複数項目を含むもの25成分。成分内は相互参照として扱い、線形の証明順を主張しない。停止点はその前提を展開しない葉である。未解決証明に代替証明の辺を加えれば順序・到達先は変わり得る。

1. HTT 1.1.2.1
2. HTT 1.1.2.4
3. DAGXIII 1.1.5
4. DAGXIII 2.1.1
5. DAGXIII 2.1.2
6. DAGXIII 2.1.3
7. DAGXIII 2.1.4
8. DAGXIII 2.1.5
9. DAGXIII 2.1.6
10. DAGXIII 2.1.7
11. DAGXIII 2.1.9
12. HA 1.1.1.1
13. DAGXIII 2.1.10
14. DAGXIII 2.1.11
15. DAGXIII 2.1.12
16. DAGXIII 2.1.14
17. HA 1.1.2.1
18. DAGXIII 2.1.15
19. HA 1.1.1.9
20. HTT 5.2.3.5
21. HA 1.1.1.8
22. HTT 1.2.13.4
23. HTT 2.4.2.1
24. HTT 2.4.4.8
25. HTT 2.4.4.9
26. HTT 4.2.2.7
27. HTT 2.1.3.4
28. HTT 1.1.4.1
29. HTT 1.1.5.14
30. HTT 2.4.1.1
31. HTT A.1.2.2
32. HTT 3.1.1.1
33. HTT 2.0.0.3
34. HTT 2.4.1.7
35. HTT 3.1.1.6
36. HTT 3.1.1.10
37. HTT 3.1.1.4
38. HTT 2.1.2.6
39. HTT 3.1.1.5
40. HTT 3.1.1.7
41. HTT 3.1.2.3
42. HTT 3.1.2.1
43. HTT 3.1.3.2
44. HTT 3.1.3.3
45. HTT 3.3.1.5
46. HTT 4.2.2.4
47. HTT 5.1.2.1
48. HTT 5.1.2.2
49. HA 1.1.2.9
50. DAGXIII 2.1.16
51. DAGXIII 2.1.17
52. DAGXIII 2.1.18
53. DAGXIII 2.1.21
54. DAGXIII 2.1.23
55. DAGXIII 2.1.25
56. HA 2.0.0.2
57. HA 2.0.0.3
58. HA 2.0.0.7
59. HA 2.1.1.8
60. HA 2.1.1.10
61. HA 2.1.2.10
62. HA 2.1.3.1
63. HA 4.1.1.10
64. HA 2.4.2.4
65. HA 2.4.1.3
66. HTT 3.2.2.12
67. HTT 3.2.2.13
68. HTT 4.3.2.15
69. HA 2.4.1.5
70. HA 2.4.1.7
71. HA 2.4.1.8
72. HA 2.4.1.9
73. HA 2.4.2.5
74. HA 2.4.2.6
75. DAGXIII 2.2.1
76. DAGXIII 2.2.2
77. DAGXIII 2.2.3
78. HA 3.3.1.9
79. HA 3.4.1.10
80. HTT 3.2.2.7
81. HTT 4.1.1.3
82. HTT 4.1.2.15
83. HTT 4.1.3.1
84. HA 3.4.1.11
85. HA 2.3.2.1
86. HA 2.3.2.10
87. HTT 2.1.2.2
88. HTT 2.4.4.2
89. HTT 2.4.4.4
90. HTT 2.4.4.5
91. HTT 2.1.2.9
92. HTT 2.1.2.5
93. HTT 2.1.3.3
94. HTT 2.1.2.3
95. HTT 2.1.2.4
96. HTT 1.2.9.3; HTT 2.1.2.1; HTT 2.4.5.1 （相互参照）
97. HTT 2.4.1.3
98. HTT 4.3.2.2
99. HTT 4.3.2.7
100. HTT 4.1.1.1
101. HTT 4.3.1.7
102. HTT 4.3.2.8
103. HTT 4.3.2.13
104. HA 2.3.2.11
105. HA 2.3.2.5
106. HTT 4.3.1.5
107. HA 3.4.3.13
108. HA 3.4.3.14
109. HA 3.4.3.15
110. HA 3.4.1.12
111. HTT 5.2.7.6
112. HTT 5.2.7.8
113. HTT 5.2.8.19
114. HTT 5.2.8.22
115. HTT 5.2.8.17
116. HTT 5.2.8.18
117. HA 3.4.1.3
118. HA 3.4.1.4
119. HTT 1.1.5.10
120. HTT 1.1.5.12
121. HA 5.1.0.2
122. HA 4.2.1.19
123. HA 3.2.2.8
124. HA 3.2.2.9
125. HA 2.1.2.7
126. HA 2.1.2.9
127. HTT 4.4.4.9
128. HTT 4.4.4.10
129. HA 2.3.3.23
130. HA 2.4.2.1
131. HA 2.1.1.1
132. HA 2.1.1.7
133. HA 2.1.1.18
134. HA 2.1.1.19
135. HA 2.1.1.20
136. HA 2.1.1.21
137. HA 4.1.1.3
138. HA 4.1.2.5
139. HA 4.1.2.9
140. HA 2.3.3.6
141. HA 4.1.2.11
142. HA 4.1.3.19
143. HA 2.4.2.11
144. HA 4.1.1.1
145. HA 4.2.1.2
146. HA 4.2.1.10
147. HA 4.2.2.8
148. HA 4.2.2.26
149. HA 4.2.2.12
150. HA 4.2.2.17
151. HTT 2.4.4.7
152. HTT 3.3.1.2
153. HTT 3.3.1.7
154. HTT 4.3.1.13
155. HTT 4.3.1.14
156. HTT 4.3.1.15
157. HA 4.2.3.1
158. HA 4.2.3.2
159. HA 4.3.1.12
160. HA 4.3.2.1
161. HA 2.1.2.6
162. HA 2.1.2.11
163. HA 2.1.3.5
164. HA 4.3.2.6
165. HA 5.3.1.19
166. HA 4.8.3.9
167. HA 4.8.3.19
168. HA 4.2.2.16
169. HA 4.2.3.5
170. HA 4.6.2.7
171. HA 4.7.4.13
172. HA 4.2.1.13
173. HA 4.2.4.8
174. HA 4.6.2.9
175. HA 4.7.3.5
176. HA 4.7.3.14
177. HA 4.7.3.16
178. HA 4.8.1.1
179. HTT 2.4.1.6
180. HTT 2.4.1.8
181. HA 7.3.2.1
182. HA 7.3.2.2
183. HTT 5.2.2.1
184. HA 7.3.2.3
185. HA 4.8.4.10
186. HA 4.8.4.13
187. HA 4.8.4.3
188. HA 2.1.2.16
189. HA 2.1.3.4
190. HA 4.2.2.6
191. HA 4.3.2.2
192. HA 4.8.4.4
193. HA 4.8.4.5
194. HA 4.8.4.6
195. HA 2.4.2.8
196. HA 4.1.2.10
197. HA 4.2.2.2
198. HA 4.2.2.9
199. HA 4.8.4.12
200. HTT 5.4.7.15
201. HTT 5.4.7.11
202. HTT 4.3.2.9
203. HTT 5.5.2.3
204. HA 4.8.4.1; HA 4.8.4.14 （相互参照）
205. HA 4.8.3.13
206. HTT 2.4.2.7
207. HTT 2.4.2.8
208. HTT 5.2.2.4
209. HA 4.6.2.1; HA 4.6.2.10; HA 4.6.2.12; HA 4.6.2.13; HA 4.6.2.17; HA 4.8.3.15; HA 4.8.3.21 （相互参照）
210. HA 2.3.1.1
211. HA 3.3.2.1
212. HA 5.1.3.1
213. HA 5.1.3.2
214. HA 5.1.4.12
215. HTT 5.5.8.4
216. HA 5.1.4.10
217. HA 1.4.2.8; HA 1.4.3.1 （相互参照）
218. HA 4.8.2.19
219. HA 5.1.1.5
220. HA 7.1.0.1
221. HA 7.1.3.5
222. HA 7.1.3.8
223. DAGXIII 2.2.4
224. HTT 2.4.4.1
225. HTT 2.4.4.3
226. HA 2.2.4.11
227. HA 2.2.4.12
228. HA 2.1.2.2
229. HA 2.1.2.4
230. HA 2.2.4.13
231. HA 2.2.4.14
232. HTT 2.4.7.2
233. HTT 2.4.7.5
234. HTT 1.2.4.3
235. HTT 2.4.7.10
236. HTT 2.4.7.11
237. HTT 2.4.7.12
238. HA 2.2.4.15
239. HA 2.2.4.16
240. HA 2.2.4.4
241. HA 2.2.4.8
242. HA 2.2.4.5
243. HA 2.2.4.6
244. HA 3.1.1.2
245. HTT 2.4.1.4
246. HTT 2.4.2.4
247. HTT 2.4.4.6
248. HA 3.1.1.5
249. HTT 3.1.1.11
250. HA 3.1.1.15
251. HA 3.1.1.16
252. HA 3.1.1.20
253. HA 3.4.4.3
254. HA 3.4.4.4
255. HA 3.4.4.5
256. HA 3.1.1.18
257. HA 3.1.2.3
258. HA 4.3.1.1
259. HA 4.4.1.1
260. HA 4.4.1.8
261. HA 4.4.1.11
262. HA 4.4.1.9
263. HA 4.4.1.12
264. HA 4.4.2.4
265. HA 4.4.2.5
266. HA 4.4.2.8
267. HA 4.4.1.28
268. HA 4.4.2.10
269. HA 4.4.3.12
270. HA 4.5.1.2
271. HA 3.1.1.4
272. HA 3.1.1.6
273. HA 3.1.1.9
274. HA 3.1.1.8
275. HA 3.1.1.11
276. HA 3.1.1.12
277. HA 3.1.1.10
278. HA 3.1.1.14
279. HTT 4.3.1.9
280. HTT 4.3.1.10
281. HA 3.1.1.13
282. HA 3.2.1.1
283. HA 4.5.2.2
284. HA 4.5.2.1
285. HA 7.2.4.1
286. HA 1.2.1.4
287. HA 1.2.1.1
288. HTT 3.3.3.1
289. HTT 3.3.3.2
290. HA 1.2.1.16
291. HTT 5.3.1.20
292. HTT 5.3.5.8
293. HTT 5.5.0.1
294. Kerodon 1.4.0.1
295. Kerodon 1.1.0.6
296. Kerodon 1.2.5.1
297. Kerodon 3.4.1.2
298. Kerodon 3.4.1.3
299. Kerodon 3.4.1.5
300. Kerodon 3.4.1.9
301. Kerodon 3.4.1.11
302. Kerodon 3.4.1.10; Kerodon 3.4.1.13 （相互参照）
303. Kerodon 4.3.6.8
304. Kerodon 4.3.6.12
305. Kerodon 4.2.1.5
306. Kerodon 4.1.1.2
307. Kerodon 4.1.1.8
308. Kerodon 4.1.1.9
309. Kerodon 4.2.1.4
310. Kerodon 4.4.2.11
311. Kerodon 5.1.4.1
312. Kerodon 5.1.1.1
313. Kerodon 5.1.1.9
314. Kerodon 5.1.4.9
315. Kerodon 4.1.3.3
316. Kerodon 4.5.4.14
317. Kerodon 3.1.8.11
318. Kerodon 1.3.3.1
319. Kerodon 1.5.6.4
320. Kerodon 1.5.7.3
321. Kerodon 1.3.6.1
322. Kerodon 1.3.7.5
323. Kerodon 1.5.4.4
324. Kerodon 1.5.4.7
325. Kerodon 1.5.4.10
326. Kerodon 1.5.4.13
327. Kerodon 1.1.0.9
328. Kerodon 1.3.7.2
329. Kerodon 1.5.7.6
330. Kerodon 1.5.7.1
331. Kerodon 1.5.7.7
332. Kerodon 1.1.3.1
333. Kerodon 1.1.4.12
334. Kerodon 1.3.1.3; Kerodon 1.3.4.1; Kerodon 1.3.4.2; Kerodon 1.3.4.3; Kerodon 1.5.6.8; Kerodon 1.5.7.4; Kerodon 1.5.7.8 （相互参照）
335. Kerodon 4.1.1.10
336. Kerodon 4.4.1.6
337. Kerodon 1.4.6.10
338. Kerodon 4.4.2.6
339. Kerodon 4.4.2.1
340. Kerodon 4.5.1.20
341. Kerodon 4.5.1.21
342. Kerodon 4.5.6.10
343. Kerodon 4.1.1.13
344. Kerodon 5.1.1.13
345. Kerodon 5.1.2.4
346. Kerodon 5.1.1.4
347. Kerodon 5.1.3.4
348. Kerodon 5.1.3.5
349. Kerodon 5.1.3.6
350. Kerodon 5.1.1.12
351. Kerodon 5.1.3.7
352. Kerodon 5.1.3.8
353. Kerodon 5.1.3.9
354. Kerodon 5.1.4.5
355. Kerodon 5.1.4.6
356. Kerodon 5.1.4.8
357. Kerodon 5.1.4.12
358. Kerodon 5.1.4.15
359. Kerodon 3.1.2.12
360. Kerodon 4.4.2.13
361. Kerodon 3.1.2.11
362. Kerodon 4.4.4.7
363. Kerodon 4.4.4.8
364. Kerodon 4.4.5.8
365. Kerodon 1.5.2.4
366. Kerodon 1.1.2.6
367. Kerodon 1.1.3.2
368. Kerodon 1.1.3.3
369. Kerodon 1.1.3.4
370. Kerodon 1.1.3.8
371. Kerodon 1.1.3.11
372. Kerodon 1.1.6.8
373. Kerodon 1.1.6.9
374. Kerodon 1.1.6.10
375. Kerodon 1.5.2.5
376. Kerodon 1.5.2.6
377. Kerodon 1.5.2.8
378. Kerodon 1.5.2.10
379. Kerodon 4.4.4.4
380. Kerodon 4.4.5.9
381. Kerodon 3.1.7.5
382. Kerodon 4.5.1.16
383. Kerodon 3.1.5.4
384. Kerodon 3.1.5.10
385. Kerodon 4.5.1.1
386. Kerodon 4.5.1.4
387. Kerodon 4.5.1.6
388. Kerodon 4.4.3.1
389. Kerodon 1.5.1.6
390. Kerodon 4.4.3.5
391. Kerodon 4.4.4.5
392. Kerodon 4.5.1.7
393. Kerodon 4.5.1.19
394. Kerodon 4.5.1.22
395. Kerodon 3.1.8.1
396. Kerodon 3.1.3.6
397. Kerodon 3.4.0.2
398. Kerodon 3.4.0.7
399. Kerodon 3.1.3.3
400. Kerodon 3.4.0.9
401. Kerodon 3.4.1.6
402. Kerodon 4.5.3.6
403. Kerodon 3.1.1.2
404. Kerodon 3.1.1.10
405. Kerodon 3.1.1.11
406. Kerodon 4.1.1.5
407. Kerodon 4.1.1.1
408. Kerodon 4.4.1.4
409. Kerodon 4.4.3.7
410. Kerodon 4.4.3.11
411. Kerodon 4.4.3.17
412. Kerodon 4.4.3.18
413. Kerodon 4.4.3.19
414. Kerodon 4.5.3.7
415. Kerodon 4.5.3.15
416. Kerodon 4.5.3.22
417. Kerodon 4.5.3.19
418. Kerodon 4.4.5.6
419. Kerodon 4.4.5.7
420. Kerodon 4.5.3.27
421. Kerodon 4.5.3.28
422. Kerodon 4.5.3.30
423. Kerodon 4.5.3.31
424. Kerodon 4.8.1.10
425. Kerodon 4.1.3.2
426. Kerodon 1.4.6.3
427. Kerodon 4.4.1.14
428. Kerodon 4.4.5.3
429. Kerodon 4.4.5.5
430. Kerodon 4.5.3.2
431. Kerodon 4.5.3.1
432. Kerodon 4.5.3.23
433. Kerodon 4.5.3.24
434. Kerodon 4.5.4.11
435. Kerodon 4.8.2.13
436. Kerodon 4.6.1.14
437. Kerodon 4.8.1.7
438. Kerodon 4.8.2.15
439. Kerodon 4.8.2.14
440. Kerodon 4.4.5.10
441. Kerodon 4.8.2.17
442. Kerodon 4.8.2.1
443. Kerodon 4.8.3.1
444. Kerodon 4.8.3.8
445. Kerodon 4.8.3.9
446. Kerodon 4.8.3.16
447. Kerodon 4.2.6.3
448. Kerodon 4.3.6.1
449. Kerodon 4.6.5.10
450. Kerodon 4.7.1.1
451. Kerodon 4.7.1.2
452. Kerodon 3.1.8.12
453. Kerodon 3.1.7.17
454. Kerodon 3.4.2.10
455. Kerodon 3.4.2.12
456. Kerodon 3.5.1.26
457. Kerodon 3.5.1.27
458. Kerodon 3.2.6.3
459. Kerodon 3.2.6.8
460. Kerodon 3.2.6.9
461. Kerodon 3.3.6.2
462. Kerodon 3.1.7.6
463. Kerodon 1.1.1.7
464. Kerodon 1.1.4.13
465. Kerodon 3.1.3.1
466. Kerodon 1.5.4.9
467. Kerodon 3.1.2.10
468. Kerodon 4.2.5.4
469. Kerodon 4.2.6.1
470. Kerodon 4.2.6.2
471. Kerodon 3.1.5.3
472. Kerodon 3.2.5.1
473. Kerodon 3.2.5.2
474. Kerodon 3.2.5.5
475. Kerodon 3.2.6.4
476. Kerodon 3.2.6.5
477. Kerodon 3.2.6.6
478. Kerodon 3.2.6.7
479. Kerodon 3.2.7.1
480. Kerodon 3.2.8.1
481. Kerodon 1.1.5.2
482. Kerodon 1.1.5.10
483. Kerodon 3.3.4.6
484. Kerodon 3.3.6.3
485. Kerodon 3.3.2.7
486. Kerodon 3.3.6.4
487. Kerodon 3.3.6.5
488. Kerodon 3.3.6.6
489. Kerodon 3.3.6.8
490. Kerodon 3.3.6.9
491. Kerodon 3.3.7.1
492. Kerodon 3.5.1.1
493. Kerodon 3.1.5.1
494. Kerodon 3.1.7.1
495. Kerodon 3.2.1.14
496. Kerodon 3.2.1.13
497. Kerodon 3.2.2.16
498. Kerodon 3.2.2.17
499. Kerodon 3.5.1.5
500. Kerodon 3.5.1.13
501. Kerodon 3.5.1.14
502. Kerodon 3.5.1.15
503. Kerodon 3.5.1.22
504. Kerodon 3.5.1.28
505. Kerodon 1.1.3.6
506. Kerodon 3.2.4.1
507. Kerodon 3.2.4.8
508. Kerodon 3.2.4.12
509. Kerodon 1.2.4.7
510. Kerodon 3.2.3.4
511. Kerodon 3.2.3.5
512. Kerodon 3.2.3.6
513. Kerodon 3.2.3.7
514. Kerodon 3.2.3.8
515. Kerodon 3.2.3.9
516. Kerodon 3.2.2.10
517. Kerodon 3.2.4.10
518. Kerodon 3.2.4.11
519. Kerodon 3.2.4.13
520. Kerodon 3.2.4.14
521. Kerodon 3.5.1.12
522. Kerodon 3.5.2.1
523. Kerodon 3.5.1.17
524. Kerodon 3.5.1.10; Kerodon 3.5.2.2; Kerodon 3.5.2.4; Kerodon 3.5.2.9 （相互参照）
525. Kerodon 3.5.7.20
526. Kerodon 3.5.3.10
527. Kerodon 1.5.3.2
528. Kerodon 3.5.3.12
529. Kerodon 8.3.3.1
530. Kerodon 8.3.3.9
531. Kerodon 8.4.2.1
532. Kerodon 1.1.3.13
533. Kerodon 1.1.0.8
534. Kerodon 1.1.3.14
535. Kerodon 1.1.4.4
536. Kerodon 1.1.2.1
537. Kerodon 1.1.2.10
538. Kerodon 1.1.4.5
539. Kerodon 1.1.4.6
540. Kerodon 1.1.4.9
541. Kerodon 3.5.3.16
542. Kerodon 3.5.3.17
543. Kerodon 3.5.3.18
544. Kerodon 3.5.3.21
545. Kerodon 3.5.3.23
546. Kerodon 4.7.6.16
547. Kerodon 4.7.6.17
548. Kerodon 4.5.4.12
549. Kerodon 4.7.6.4
550. Kerodon 4.8.1.6
551. Kerodon 4.4.3.10
552. Kerodon 4.4.5.11
553. Kerodon 4.6.1.11
554. Kerodon 4.6.1.24
555. Kerodon 4.6.1.22
556. Kerodon 4.8.2.4
557. Kerodon 1.5.5.14
558. Kerodon 3.1.2.3
559. Kerodon 3.1.7.14
560. Kerodon 3.1.7.16
561. Kerodon 1.5.5.4
562. Kerodon 1.5.5.5
563. Kerodon 3.1.7.10
564. Kerodon 3.1.7.13
565. Kerodon 3.3.7.5
566. Kerodon 3.3.7.6
567. Kerodon 3.3.7.7
568. Kerodon 3.1.8.10
569. Kerodon 3.2.6.1
570. Kerodon 4.6.1.13
571. Kerodon 4.8.1.1
572. Kerodon 4.8.1.4
573. Kerodon 4.8.2.6
574. Kerodon 4.8.2.7
575. Kerodon 4.8.2.19
576. Kerodon 4.8.2.20
577. Kerodon 4.8.2.21
578. Kerodon 4.8.2.22
579. Kerodon 4.8.2.24
580. Kerodon 4.8.2.25
581. Kerodon 5.1.2.5
582. Kerodon 4.3.6.14
583. Kerodon 4.2.5.3
584. Kerodon 4.4.2.15
585. Kerodon 4.4.2.14
586. Kerodon 4.6.5.7
587. Kerodon 4.6.8.5
588. Kerodon 4.3.6.16
589. Kerodon 5.1.1.14
590. Kerodon 4.8.3.19
591. Kerodon 4.8.2.28
592. Kerodon 4.8.2.29
593. Kerodon 4.8.2.30
594. Kerodon 4.8.2.5
595. Kerodon 4.8.2.31
596. Kerodon 4.8.3.5
597. Kerodon 4.8.3.26
598. Kerodon 4.8.3.29
599. Kerodon 3.4.1.4
600. Kerodon 3.5.7.8
601. Kerodon 3.5.7.1
602. Kerodon 3.5.9.1
603. Kerodon 3.5.9.8
604. Kerodon 3.3.7.2
605. Kerodon 3.3.7.3
606. Kerodon 3.5.9.9
607. Kerodon 3.5.9.11
608. Kerodon 4.8.3.32
609. Kerodon 4.8.3.38
610. Kerodon 4.8.3.39
611. Kerodon 4.6.1.16
612. Kerodon 4.6.1.18
613. Kerodon 4.6.8.1
614. Kerodon 1.5.7.5
615. Kerodon 4.1.3.1
616. Kerodon 4.1.4.4
617. Kerodon 4.6.8.4
618. Kerodon 5.1.3.10
619. Kerodon 4.6.8.9
620. Kerodon 1.4.4.1
621. Kerodon 4.6.8.10
622. Kerodon 4.6.8.15
623. Kerodon 5.1.7.4
624. Kerodon 4.5.4.7
625. Kerodon 4.5.4.8
626. Kerodon 4.5.5.10
627. Kerodon 1.5.3.7
628. Kerodon 4.5.5.4
629. Kerodon 4.5.5.11
630. Kerodon 5.1.7.5
631. Kerodon 5.1.7.8
632. Kerodon 4.4.4.9
633. Kerodon 4.1.1.6
634. Kerodon 4.5.6.7
635. Kerodon 5.1.7.13
636. Kerodon 5.5.3.3
637. Kerodon 3.2.4.3
638. Kerodon 3.2.7.2
639. Kerodon 4.4.5.1
640. Kerodon 4.5.5.15
641. Kerodon 4.5.6.18
642. Kerodon 4.5.4.5
643. Kerodon 4.5.4.6
644. Kerodon 4.5.5.12
645. Kerodon 4.5.5.13
646. Kerodon 4.8.2.12
647. Kerodon 4.8.5.11
648. Kerodon 4.8.8.10
649. Kerodon 5.3.4.9
650. Kerodon 5.3.2.3
651. Kerodon 5.3.2.2
652. Kerodon 5.3.2.4
653. Kerodon 5.3.2.7
654. Kerodon 5.3.2.8
655. Kerodon 5.3.2.12
656. Kerodon 5.3.6.3
657. Kerodon 4.5.1.17
658. Kerodon 4.5.4.10
659. Kerodon 4.8.2.11
660. Kerodon 4.8.5.10
661. Kerodon 4.8.8.9
662. Kerodon 4.8.8.12
663. Kerodon 4.3.6.5
664. Kerodon 4.3.7.8
665. Kerodon 4.5.3.35
666. Kerodon 4.5.4.9
667. Kerodon 4.5.5.1
668. Kerodon 4.5.5.9
669. Kerodon 4.5.6.2
670. Kerodon 5.2.3.14
671. Kerodon 4.3.3.24
672. Kerodon 5.2.3.12
673. Kerodon 5.2.3.13
674. Kerodon 5.2.3.16
675. Kerodon 5.2.3.17
676. Kerodon 5.2.3.18
677. Kerodon 5.2.3.15
678. Kerodon 5.2.4.5
679. Kerodon 5.3.4.6
680. Kerodon 5.3.4.17
681. Kerodon 5.3.4.18
682. Kerodon 5.1.4.13
683. Kerodon 1.1.4.1
684. Kerodon 4.5.7.3
685. Kerodon 4.5.7.8
686. Kerodon 4.5.7.11
687. Kerodon 4.5.7.12
688. Kerodon 4.5.7.13
689. Kerodon 4.5.7.16
690. Kerodon 4.5.7.17
691. Kerodon 4.5.7.18
692. Kerodon 4.1.2.2
693. Kerodon 1.4.5.4
694. Kerodon 1.4.5.3
695. Kerodon 1.5.7.10
696. Kerodon 4.1.2.6
697. Kerodon 1.4.3.1
698. Kerodon 4.1.2.7
699. Kerodon 4.1.2.8
700. Kerodon 4.1.2.9
701. Kerodon 4.1.2.4; Kerodon 4.1.2.10; Kerodon 4.1.2.11 （相互参照）
702. Kerodon 4.4.1.12
703. Kerodon 4.4.3.2
704. Kerodon 4.4.3.6
705. Kerodon 4.5.7.20
706. Kerodon 4.5.7.21
707. Kerodon 4.5.7.22
708. Kerodon 4.5.7.23
709. Kerodon 3.2.8.3
710. Kerodon 4.4.5.4
711. Kerodon 4.1.4.3
712. Kerodon 5.2.5.5
713. Kerodon 4.1.2.17
714. Kerodon 5.2.1.3
715. Kerodon 5.2.1.5
716. Kerodon 5.2.1.1
717. Kerodon 5.2.2.10
718. Kerodon 5.2.2.11
719. Kerodon 5.2.2.13
720. Kerodon 5.2.8.5
721. Kerodon 4.4.2.9
722. Kerodon 5.1.1.11
723. Kerodon 5.2.2.5
724. Kerodon 5.2.2.9
725. Kerodon 5.2.5.1
726. Kerodon 5.2.5.2
727. Kerodon 2.1.2.17
728. Kerodon 2.1.7.1
729. Kerodon 4.6.1.1
730. Kerodon 1.1.1.4
731. Kerodon 4.6.8.11
732. Kerodon 4.6.8.12
733. Kerodon 4.6.8.13
734. Kerodon 5.2.8.4
735. Kerodon 5.2.8.8
736. Kerodon 5.2.8.9
737. Kerodon 5.2.8.10
738. Kerodon 2.3.5.1
739. Kerodon 2.2.0.1
740. Kerodon 2.4.2.8
741. Kerodon 2.4.3.1
742. Kerodon 2.4.4.1
743. Kerodon 2.4.4.15
744. Kerodon 4.6.5.1
745. Kerodon 4.6.5.2
746. Kerodon 4.6.7.3
747. Kerodon 4.6.7.1
748. Kerodon 4.6.7.16
749. Kerodon 4.6.7.18
750. Kerodon 4.6.7.22
751. Kerodon 3.6.1.8
752. Kerodon 4.6.2.3
753. Kerodon 4.6.2.7
754. Kerodon 4.6.2.12
755. Kerodon 4.6.7.11
756. Kerodon 2.4.4.9
757. Kerodon 1.2.3.13
758. Kerodon 1.3.7.7
759. Kerodon 2.4.4.6
760. Kerodon 1.3.7.8
761. Kerodon 1.3.7.9
762. Kerodon 1.3.7.11
763. Kerodon 2.4.4.10; Kerodon 2.4.4.11; Kerodon 2.4.4.16 （相互参照）
764. Kerodon 4.6.7.13
765. Kerodon 4.6.7.14
766. Kerodon 2.4.4.2
767. Kerodon 4.6.7.10
768. Kerodon 4.6.7.21
769. Kerodon 1.3.7.1
770. Kerodon 2.4.4.17
771. Kerodon 4.6.7.27
772. Kerodon 4.6.7.28
773. Kerodon 4.6.7.29
774. Kerodon 4.6.3.3
775. Kerodon 3.1.3.7
776. Kerodon 3.1.3.11
777. Kerodon 4.1.4.1
778. Kerodon 4.1.4.6
779. Kerodon 4.4.3.15
780. Kerodon 4.6.3.6
781. Kerodon 4.6.3.8
782. Kerodon 4.6.3.9
783. Kerodon 4.6.3.1
784. Kerodon 4.6.3.7
785. Kerodon 5.1.3.3
786. Kerodon 5.1.1.10
787. Kerodon 5.4.2.1
788. Kerodon 5.4.2.2
789. Kerodon 5.4.7.1
790. Kerodon 5.4.2.4
791. Kerodon 5.4.3.8
792. Kerodon 5.4.4.1
793. Kerodon 2.2.1.13
794. Kerodon 2.2.1.14
795. Kerodon 2.2.1.15
796. Kerodon 2.2.4.5
797. Kerodon 2.2.4.14
798. Kerodon 2.2.0.6; Kerodon 2.2.5.7 （相互参照）
799. Kerodon 2.2.4.17
800. Kerodon 2.3.1.1
801. Kerodon 2.3.1.8
802. Kerodon 2.3.1.9
803. Kerodon 2.3.1.15
804. Kerodon 2.3.2.5
805. Kerodon 2.3.5.4
806. Kerodon 2.3.5.6
807. Kerodon 2.1.5.16
808. Kerodon 2.1.3.2
809. Kerodon 2.1.7.2
810. Kerodon 2.1.7.4
811. Kerodon 2.1.7.5
812. Kerodon 2.2.0.3
813. Kerodon 2.2.5.1
814. Kerodon 2.2.5.4
815. Kerodon 2.2.5.5
816. Kerodon 2.4.1.3
817. Kerodon 2.4.1.4
818. Kerodon 2.4.2.9
819. Kerodon 2.4.3.5
820. Kerodon 2.4.3.11
821. Kerodon 2.4.5.4
822. Kerodon 2.4.5.2
823. Kerodon 2.4.5.5
824. Kerodon 2.4.5.8
825. Kerodon 2.4.5.10
826. Kerodon 5.4.8.2
827. Kerodon 1.3.1.1
828. Kerodon 1.1.0.2
829. Kerodon 2.4.1.12
830. Kerodon 2.4.2.4
831. Kerodon 3.2.4.16
832. Kerodon 4.8.4.8
833. Kerodon 2.4.3.2
834. Kerodon 2.4.3.8
835. Kerodon 5.4.5.9
836. Kerodon 5.4.3.1
837. Kerodon 5.4.5.7
838. Kerodon 5.4.5.10
839. Kerodon 5.4.6.10
840. Kerodon 5.2.2.4
841. Kerodon 5.4.3.9
842. Kerodon 5.4.4.2
843. Kerodon 1.1.2.8
844. Kerodon 5.4.1.1
845. Kerodon 5.4.5.2
846. Kerodon 5.4.5.6
847. Kerodon 5.4.5.14
848. Kerodon 5.4.6.11
849. Kerodon 5.4.6.8
850. Kerodon 5.4.6.14
851. Kerodon 5.4.7.9
852. Kerodon 5.4.8.3
853. Kerodon 5.4.8.4
854. Kerodon 2.4.6.13
855. Kerodon 5.4.8.5
856. Kerodon 5.4.8.1
857. Kerodon 5.4.8.6
858. Kerodon 5.4.8.7
859. Kerodon 2.4.1.6
860. Kerodon 2.4.5.1
861. Kerodon 2.4.3.10; Kerodon 2.4.6.10 （相互参照）
862. Kerodon 2.4.6.11
863. Kerodon 2.4.6.9
864. Kerodon 2.4.1.8
865. Kerodon 2.4.6.1
866. Kerodon 3.1.5.12
867. Kerodon 4.6.7.5
868. Kerodon 4.6.7.6
869. Kerodon 4.6.8.20
870. Kerodon 5.5.3.5
871. Kerodon 5.5.3.6
872. Kerodon 5.4.2.6
873. Kerodon 5.4.7.10
874. Kerodon 5.4.7.11
875. Kerodon 5.4.2.8
876. Kerodon 5.4.3.4
877. Kerodon 5.5.4.2
878. Kerodon 5.5.5.9
879. Kerodon 5.5.5.11
880. Kerodon 5.6.2.18
881. Kerodon 5.5.5.12
882. Kerodon 5.5.5.17
883. Kerodon 5.6.2.16
884. Kerodon 5.6.8.9
885. Kerodon 3.1.7.7
886. Kerodon 5.2.2.12
887. Kerodon 5.2.2.8
888. Kerodon 5.2.4.2
889. Kerodon 5.2.8.1
890. Kerodon 5.6.8.2
891. Kerodon 3.1.5.7
892. Kerodon 3.1.7.9
893. Kerodon 3.2.4.2
894. Kerodon 3.5.1.19
895. Kerodon 3.1.7.23
896. Kerodon 3.1.8.2
897. Kerodon 3.5.1.29
898. Kerodon 3.5.1.31
899. Kerodon 3.5.1.32
900. Kerodon 3.5.1.33
901. Kerodon 4.5.5.8
902. Kerodon 5.3.2.11
903. Kerodon 11.9.8.5
904. Kerodon 5.5.3.1
905. Kerodon 5.4.5.1
906. Kerodon 5.5.5.10
907. Kerodon 5.6.2.2
908. Kerodon 5.6.2.14
909. Kerodon 11.9.9.1
910. Kerodon 4.5.1.18
911. Kerodon 4.5.1.10
912. Kerodon 5.5.3.7
913. Kerodon 5.4.7.12
914. Kerodon 5.5.5.16
915. Kerodon 11.9.9.4
916. Kerodon 5.6.5.13
917. Kerodon 4.4.1.11; Kerodon 4.4.3.8; Kerodon 4.6.7.8; Kerodon 4.6.7.23; Kerodon 4.6.7.24; Kerodon 4.6.7.25; Kerodon 4.6.7.26; Kerodon 4.7.1.16; Kerodon 4.7.6.11; Kerodon 4.7.6.15; Kerodon 4.7.6.18; Kerodon 4.7.6.19; Kerodon 4.7.6.24; Kerodon 4.7.6.25; Kerodon 4.8.2.16; Kerodon 4.8.2.18; Kerodon 4.8.4.1; Kerodon 4.8.4.5; Kerodon 4.8.4.6; Kerodon 4.8.5.8; Kerodon 4.8.8.7; Kerodon 4.8.8.11; Kerodon 4.8.8.13; Kerodon 4.8.8.14; Kerodon 5.1.2.1; Kerodon 5.1.2.3; Kerodon 5.1.3.11; Kerodon 5.1.6.1; Kerodon 5.1.6.2; Kerodon 5.1.6.5; Kerodon 5.1.6.6; Kerodon 5.1.6.7; Kerodon 5.1.6.8; Kerodon 5.1.7.9; Kerodon 5.1.7.14; Kerodon 5.1.7.15; Kerodon 5.2.4.1; Kerodon 5.3.5.7; Kerodon 5.3.6.5; Kerodon 5.3.6.6; Kerodon 5.4.9.2; Kerodon 5.5.5.14; Kerodon 5.6.0.2; Kerodon 5.6.2.17; Kerodon 5.6.2.19; Kerodon 5.6.2.22; Kerodon 5.6.2.24; Kerodon 5.6.5.3; Kerodon 5.6.5.5; Kerodon 5.6.5.10; Kerodon 5.6.5.12; Kerodon 5.6.5.15; Kerodon 5.6.7.1; Kerodon 5.6.7.2; Kerodon 5.6.7.3; Kerodon 5.6.7.5; Kerodon 5.6.8.3; Kerodon 5.6.8.5; Kerodon 5.6.8.6; Kerodon 5.6.8.7; Kerodon 5.6.8.10; Kerodon 5.6.9.1; Kerodon 5.6.9.2; Kerodon 11.5.0.111; Kerodon 11.9.8.7; Kerodon 11.9.9.2; Kerodon 11.9.9.3; Kerodon 11.9.9.6; Kerodon 11.9.9.7; Kerodon 11.9.9.8 （相互参照）
918. Kerodon 5.1.6.4
919. Kerodon 7.1.6.1
920. Kerodon 1.5.4.14
921. Kerodon 3.1.1.1
922. Kerodon 3.1.2.7
923. Kerodon 4.5.4.4
924. Kerodon 4.5.6.8
925. Kerodon 4.5.6.20
926. Kerodon 5.1.7.16
927. Kerodon 7.1.5.16
928. Kerodon 7.1.6.8
929. Kerodon 4.6.6.8
930. Kerodon 4.5.3.33
931. Kerodon 4.6.2.8
932. Kerodon 4.6.4.9
933. Kerodon 5.1.2.6
934. Kerodon 5.1.1.6
935. Kerodon 5.3.7.1
936. Kerodon 5.3.7.2
937. Kerodon 5.3.7.4
938. Kerodon 5.3.7.5
939. Kerodon 7.1.5.9
940. Kerodon 7.1.5.19
941. Kerodon 7.1.6.13
942. Kerodon 7.1.6.19
943. Kerodon 7.1.6.20
944. Kerodon 3.5.7.6
945. Kerodon 4.7.1.12
946. Kerodon 7.1.3.11
947. Kerodon 4.3.6.10
948. Kerodon 4.5.3.21
949. Kerodon 4.5.3.29
950. Kerodon 4.5.3.34
951. Kerodon 4.6.4.4
952. Kerodon 4.6.4.19
953. Kerodon 4.6.4.21
954. Kerodon 4.8.4.13
955. Kerodon 4.8.4.17
956. Kerodon 7.1.5.4
957. Kerodon 7.1.6.4
958. Kerodon 7.1.5.6
959. Kerodon 7.1.6.10
960. Kerodon 7.1.6.11
961. Kerodon 4.6.4.1
962. Kerodon 7.1.7.1
963. Kerodon 7.1.7.6
964. Kerodon 4.3.6.9
965. Kerodon 7.1.5.17
966. Kerodon 7.1.8.7
967. Kerodon 7.1.8.10
968. Kerodon 7.1.8.11
969. Kerodon 7.1.8.12
970. Kerodon 7.1.9.2
971. Kerodon 7.1.9.3
972. Kerodon 7.1.9.4
973. Kerodon 7.1.1.9
974. Kerodon 7.1.1.10
975. Kerodon 4.6.4.15
976. Kerodon 7.1.1.1
977. Kerodon 5.2.8.6
978. Kerodon 5.2.8.7
979. Kerodon 1.4.6.1
980. Kerodon 4.6.4.20
981. Kerodon 3.5.9.2
982. Kerodon 4.7.2.5
983. Kerodon 3.5.9.12
984. Kerodon 4.6.5.5
985. Kerodon 4.6.8.16
986. Kerodon 4.6.8.18
987. Kerodon 4.7.2.1
988. Kerodon 4.7.2.7
989. Kerodon 4.7.3.9
990. Kerodon 4.7.3.20
991. Kerodon 5.2.8.12
992. Kerodon 5.6.6.10
993. Kerodon 3.1.6.1
994. Kerodon 4.6.7.7
995. Kerodon 5.6.6.1
996. Kerodon 5.6.6.11
997. Kerodon 4.7.3.1
998. Kerodon 4.3.6.4
999. Kerodon 4.7.3.12
1000. Kerodon 4.7.3.21
1001. Kerodon 4.7.3.22
1002. Kerodon 5.6.6.19
1003. Kerodon 5.6.6.21
1004. Kerodon 7.1.3.1
1005. Kerodon 7.1.3.4
1006. Kerodon 7.1.3.6
1007. Kerodon 7.1.3.18
1008. Kerodon 7.1.9.6
1009. Kerodon 7.1.9.7
1010. Kerodon 7.1.9.8
1011. Kerodon 4.9.5.2
1012. Kerodon 4.9.2.3
1013. Kerodon 4.9.3.4
1014. Kerodon 4.9.4.8
1015. Kerodon 4.9.5.14
1016. Kerodon 4.9.5.16
1017. Kerodon 3.6.1.6
1018. Kerodon 4.9.2.5
1019. Kerodon 4.9.1.24
1020. Kerodon 4.9.2.9
1021. Kerodon 4.9.3.5
1022. Kerodon 4.9.4.7
1023. Kerodon 3.6.1.7
1024. Kerodon 4.9.3.6
1025. Kerodon 4.9.4.10
1026. Kerodon 4.9.4.12
1027. Kerodon 4.9.4.14
1028. Kerodon 4.9.5.17
1029. Kerodon 4.9.5.18
1030. Kerodon 4.4.3.21
1031. Kerodon 4.5.3.20
1032. Kerodon 4.6.4.22
1033. Kerodon 4.9.5.19
1034. Kerodon 4.4.2.10
1035. Kerodon 4.4.2.12
1036. Kerodon 7.1.4.22
1037. Kerodon 7.1.4.24
1038. Kerodon 4.7.1.13
1039. Kerodon 4.7.3.14
1040. Kerodon 4.7.3.16
1041. Kerodon 7.1.4.20
1042. Kerodon 7.1.4.25
1043. Kerodon 4.7.3.19
1044. Kerodon 7.1.3.17
1045. Kerodon 7.1.4.26
1046. Kerodon 7.1.4.27
1047. Kerodon 7.1.9.1
1048. Kerodon 7.1.6.3
1049. Kerodon 4.6.2.9
1050. Kerodon 4.2.1.8
1051. Kerodon 4.6.2.14
1052. Kerodon 4.6.4.13
1053. Kerodon 4.6.4.14
1054. Kerodon 5.1.7.1
1055. Kerodon 5.6.0.6
1056. Kerodon 7.2.1.1
1057. Kerodon 7.2.1.15
1058. Kerodon 7.2.2.1
1059. Kerodon 7.2.2.2
1060. Kerodon 7.2.2.3
1061. Kerodon 4.3.6.3
1062. Kerodon 4.3.7.1
1063. Kerodon 4.3.7.9
1064. Kerodon 4.3.7.10
1065. Kerodon 7.1.6.12
1066. Kerodon 4.3.7.6
1067. Kerodon 7.1.7.3
1068. Kerodon 7.1.7.4
1069. Kerodon 7.1.7.5
1070. Kerodon 4.3.3.16
1071. Kerodon 4.3.3.17
1072. Kerodon 4.3.3.21
1073. Kerodon 4.9.4.13
1074. Kerodon 9.1.1.14
1075. Kerodon 9.1.1.16
1076. Kerodon 7.2.3.1
1077. Kerodon 4.1.4.2
1078. Kerodon 9.1.3.1
1079. Kerodon 9.1.3.8
1080. Kerodon 9.1.4.2
1081. Kerodon 3.1.1.6
1082. Kerodon 3.1.3.2
1083. Kerodon 3.1.3.4
1084. Kerodon 7.2.1.5
1085. Kerodon 9.1.1.17
1086. Kerodon 3.3.6.1
1087. Kerodon 3.3.6.7
1088. Kerodon 1.1.0.12
1089. Kerodon 3.6.1.2
1090. Kerodon 3.6.1.3
1091. Kerodon 3.6.1.4
1092. Kerodon 9.2.0.2
1093. Kerodon 3.6.1.9
1094. Kerodon 3.3.2.5
1095. Kerodon 3.3.3.1
1096. Kerodon 3.3.3.5
1097. Kerodon 3.3.4.3
1098. Kerodon 6.3.5.9
1099. Kerodon 6.3.1.15
1100. Kerodon 6.3.1.8
1101. Kerodon 6.3.2.4
1102. Kerodon 4.5.4.13
1103. Kerodon 6.3.1.14
1104. Kerodon 6.3.1.20
1105. Kerodon 1.4.6.7
1106. Kerodon 5.4.6.4
1107. Kerodon 5.4.6.5
1108. Kerodon 6.3.2.5
1109. Kerodon 6.3.2.7
1110. Kerodon 6.3.2.8
1111. Kerodon 6.3.2.9
1112. Kerodon 6.3.2.11
1113. Kerodon 6.3.2.12
1114. Kerodon 6.3.1.23
1115. Kerodon 6.3.5.1
1116. Kerodon 1.1.0.14
1117. Kerodon 1.2.1.1
1118. Kerodon 3.1.1.4
1119. Kerodon 3.4.1.16
1120. Kerodon 4.8.1.11
1121. Kerodon 4.8.4.4
1122. Kerodon 6.3.1.7
1123. Kerodon 6.3.1.9
1124. Kerodon 6.3.1.13
1125. Kerodon 6.3.5.3
1126. Kerodon 6.3.5.4
1127. Kerodon 6.3.5.13
1128. Kerodon 6.3.5.14
1129. Kerodon 6.3.6.2
1130. Kerodon 7.2.1.11
1131. Kerodon 9.1.3.2
1132. Kerodon 5.1.1.7
1133. Kerodon 5.1.4.7
1134. Kerodon 9.1.3.12
1135. Kerodon 7.1.2.12
1136. Kerodon 7.1.2.11
1137. Kerodon 7.3.1.5
1138. Kerodon 7.3.1.2
1139. Kerodon 7.3.1.7
1140. Kerodon 4.5.8.10
1141. Kerodon 4.5.8.14
1142. Kerodon 5.3.6.1
1143. Kerodon 5.6.7.6
1144. Kerodon 6.3.1.12
1145. Kerodon 4.2.5.2
1146. Kerodon 4.5.1.13
1147. Kerodon 1.5.6.6
1148. Kerodon 5.6.7.4
1149. Kerodon 6.3.1.1
1150. Kerodon 7.2.1.10
1151. Kerodon 7.2.1.13
1152. Kerodon 7.3.1.14
1153. Kerodon 5.1.1.16
1154. Kerodon 4.3.7.17
1155. Kerodon 5.1.1.15
1156. Kerodon 5.1.4.19
1157. Kerodon 5.1.4.20
1158. Kerodon 7.2.1.3
1159. Kerodon 7.2.1.6
1160. Kerodon 7.2.1.21
1161. Kerodon 7.2.1.22
1162. Kerodon 7.2.3.10
1163. Kerodon 7.3.1.10
1164. Kerodon 4.3.5.2
1165. Kerodon 4.3.5.12
1166. Kerodon 7.3.1.1
1167. Kerodon 7.3.2.1
1168. Kerodon 7.1.7.2
1169. Kerodon 7.2.2.5
1170. Kerodon 7.2.2.6
1171. Kerodon 7.2.3.6
1172. Kerodon 7.3.3.7
1173. Kerodon 7.3.2.3
1174. Kerodon 7.3.2.11
1175. Kerodon 4.5.5.5
1176. Kerodon 7.3.2.12
1177. Kerodon 7.3.6.7
1178. Kerodon 7.3.6.9
1179. Kerodon 7.3.8.1
1180. Kerodon 7.3.8.10
1181. Kerodon 7.3.8.12
1182. Kerodon 7.3.8.14
1183. Kerodon 7.3.8.24
1184. Kerodon 7.3.1.11
1185. Kerodon 7.3.5.5
1186. Kerodon 7.3.5.8
1187. Kerodon 7.3.1.12
1188. Kerodon 1.5.6.7
1189. Kerodon 6.2.2.6
1190. Kerodon 6.2.5.1
1191. Kerodon 7.3.6.1
1192. Kerodon 7.3.6.5
1193. Kerodon 7.3.6.6
1194. Kerodon 7.3.8.25
1195. Kerodon 7.3.8.26
1196. Kerodon 5.6.5.1
1197. Kerodon 7.4.2.15
1198. Kerodon 7.4.3.6
1199. Kerodon 7.6.6.17
1200. Kerodon 5.5.3.11
1201. Kerodon 5.5.3.13
1202. Kerodon 4.9.3.9
1203. Kerodon 4.9.4.5
1204. Kerodon 4.9.4.9
1205. Kerodon 1.5.6.9
1206. Kerodon 1.5.6.1
1207. Kerodon 4.5.2.12
1208. Kerodon 4.9.5.4
1209. Kerodon 4.5.2.15
1210. Kerodon 4.5.2.9
1211. Kerodon 4.5.2.10
1212. Kerodon 5.3.8.2
1213. Kerodon 4.5.2.13
1214. Kerodon 5.3.8.6
1215. Kerodon 5.3.8.11; Kerodon 5.3.8.12 （相互参照）
1216. Kerodon 4.9.8.10
1217. Kerodon 5.6.2.1
1218. Kerodon 7.4.3.8
1219. Kerodon 7.4.5.22
1220. Kerodon 7.6.6.11
1221. Kerodon 4.9.3.16
1222. Kerodon 4.9.3.17
1223. Kerodon 4.9.4.18
1224. Kerodon 4.9.4.19
1225. Kerodon 4.9.8.11
1226. Kerodon 7.4.1.15
1227. Kerodon 4.9.4.20
1228. Kerodon 4.9.4.21
1229. Kerodon 4.9.4.22
1230. Kerodon 4.9.5.13
1231. Kerodon 5.5.3.14
1232. Kerodon 5.1.4.16
1233. Kerodon 5.5.3.9
1234. Kerodon 5.6.2.15
1235. Kerodon 5.6.5.8
1236. Kerodon 5.6.2.20
1237. Kerodon 5.6.5.9
1238. Kerodon 5.1.7.11
1239. Kerodon 5.6.2.21
1240. Kerodon 5.6.5.11
1241. Kerodon 5.6.5.14
1242. Kerodon 5.6.5.16
1243. Kerodon 5.6.6.17
1244. Kerodon 7.1.0.1
1245. Kerodon 7.1.2.1
1246. Kerodon 7.1.2.3
1247. Kerodon 7.1.2.6
1248. Kerodon 7.1.2.9
1249. Kerodon 7.1.2.10
1250. Kerodon 7.1.3.19
1251. Kerodon 7.1.8.9
1252. Kerodon 7.1.8.15
1253. Kerodon 7.1.8.3
1254. Kerodon 7.4.1.1
1255. Kerodon 7.4.1.8
1256. Kerodon 7.4.1.9
1257. Kerodon 7.4.1.13
1258. Kerodon 4.2.4.11
1259. Kerodon 7.4.1.14
1260. Kerodon 7.4.1.16
1261. Kerodon 5.6.6.12
1262. Kerodon 5.6.6.13
1263. Kerodon 5.6.6.14
1264. Kerodon 7.4.1.22
1265. Kerodon 7.4.4.6
1266. Kerodon 4.3.7.11
1267. Kerodon 5.3.1.22
1268. Kerodon 5.3.1.23
1269. Kerodon 7.4.4.9
1270. Kerodon 7.4.4.11
1271. Kerodon 5.2.3.1
1272. Kerodon 5.3.1.17
1273. Kerodon 4.5.6.14
1274. Kerodon 5.3.1.15
1275. Kerodon 5.3.1.18
1276. Kerodon 5.3.1.19
1277. Kerodon 5.3.1.20
1278. Kerodon 5.3.1.21
1279. Kerodon 7.4.4.12
1280. Kerodon 7.4.4.13
1281. Kerodon 7.4.4.1
1282. Kerodon 7.4.4.14
1283. Kerodon 7.6.6.12
1284. Kerodon 3.4.0.6
1285. Kerodon 4.7.3.23
1286. Kerodon 6.2.1.17
1287. Kerodon 6.2.1.8
1288. Kerodon 6.2.2.23
1289. Kerodon 6.1.1.1
1290. Kerodon 6.1.2.8
1291. Kerodon 6.1.4.6
1292. Kerodon 6.2.1.1
1293. Kerodon 6.2.2.9
1294. Kerodon 6.2.2.24
1295. Kerodon 6.2.5.2
1296. Kerodon 5.2.2.15
1297. Kerodon 6.2.5.3
1298. Kerodon 6.2.5.4
1299. Kerodon 6.2.6.1
1300. Kerodon 6.2.6.2
1301. Kerodon 7.2.3.7
1302. Kerodon 7.6.2.40
1303. Kerodon 4.5.3.8
1304. Kerodon 7.5.4.6
1305. Kerodon 5.3.3.5
1306. Kerodon 7.5.2.3
1307. Kerodon 5.3.3.3
1308. Kerodon 5.3.3.4
1309. Kerodon 5.3.3.2
1310. Kerodon 5.3.3.7
1311. Kerodon 4.3.2.5
1312. Kerodon 5.3.3.9
1313. Kerodon 5.3.3.10
1314. Kerodon 5.3.3.12
1315. Kerodon 5.3.3.15
1316. Kerodon 5.3.3.16
1317. Kerodon 5.3.3.21
1318. Kerodon 7.5.2.8
1319. Kerodon 7.5.2.12
1320. Kerodon 7.5.5.1
1321. Kerodon 7.5.5.5
1322. Kerodon 7.5.5.7
1323. Kerodon 7.5.5.8
1324. Kerodon 3.4.0.3
1325. Kerodon 3.4.1.1
1326. Kerodon 7.5.1.1
1327. Kerodon 7.5.2.9
1328. Kerodon 7.5.2.13
1329. Kerodon 7.5.2.16
1330. Kerodon 7.5.2.17
1331. Kerodon 7.5.4.1
1332. Kerodon 7.5.4.8
1333. Kerodon 5.2.4.7
1334. Kerodon 5.3.3.8
1335. Kerodon 5.3.3.20
1336. Kerodon 7.5.1.3
1337. Kerodon 7.5.4.4
1338. Kerodon 3.4.2.11
1339. Kerodon 7.5.4.10
1340. Kerodon 7.5.4.11
1341. Kerodon 7.5.4.13
1342. Kerodon 7.5.5.10
1343. Kerodon 7.6.3.4
1344. Kerodon 1.5.2.9
1345. Kerodon 2.4.3.9
1346. Kerodon 7.6.3.6
1347. Kerodon 7.6.3.7
1348. Kerodon 7.6.3.8
1349. Kerodon 7.6.3.9
1350. Kerodon 7.6.3.12
1351. Kerodon 7.7.0.2
1352. Kerodon 7.7.0.4
1353. Kerodon 7.7.0.6
1354. Kerodon 7.7.7.4
1355. Kerodon 9.1.1.11
1356. Kerodon 7.2.3.9
1357. Kerodon 9.1.1.18
1358. Kerodon 7.4.3.1
1359. Kerodon 7.4.3.7
1360. Kerodon 8.1.1.11
1361. Kerodon 8.3.1.2
1362. Kerodon 4.6.8.19
1363. Kerodon 7.1.2.8
1364. Kerodon 8.3.1.7
1365. Kerodon 8.3.1.3
1366. Kerodon 5.3.1.10
1367. Kerodon 5.1.4.14
1368. Kerodon 8.2.1.7
1369. Kerodon 4.5.6.11
1370. Kerodon 4.5.8.1
1371. Kerodon 4.5.6.1
1372. Kerodon 4.5.6.4
1373. Kerodon 4.5.8.5
1374. Kerodon 4.5.8.18
1375. Kerodon 7.1.5.21
1376. Kerodon 7.3.3.6
1377. Kerodon 7.3.5.6
1378. Kerodon 7.3.5.7
1379. Kerodon 7.1.6.6
1380. Kerodon 7.1.6.9
1381. Kerodon 7.2.2.9
1382. Kerodon 7.2.2.14
1383. Kerodon 7.3.5.9
1384. Kerodon 6.2.2.10
1385. Kerodon 7.3.3.11
1386. Kerodon 7.3.3.13
1387. Kerodon 7.3.5.10
1388. Kerodon 7.3.5.11
1389. Kerodon 7.3.6.10
1390. Kerodon 7.3.6.11
1391. Kerodon 7.1.5.18
1392. Kerodon 7.3.6.8
1393. Kerodon 7.3.6.14
1394. Kerodon 7.3.7.10
1395. Kerodon 7.3.7.12
1396. Kerodon 7.3.7.13
1397. Kerodon 7.3.7.1
1398. Kerodon 7.3.7.6
1399. Kerodon 8.2.1.8; Kerodon 8.2.1.9 （相互参照）
1400. Kerodon 8.2.2.2
1401. Kerodon 8.2.2.3
1402. Kerodon 4.4.3.23
1403. Kerodon 6.3.1.4
1404. Kerodon 6.3.1.17
1405. Kerodon 6.3.1.21
1406. Kerodon 4.1.2.15
1407. Kerodon 5.1.1.5
1408. Kerodon 5.1.1.8
1409. Kerodon 5.1.4.17
1410. Kerodon 5.3.6.7; Kerodon 5.3.6.12; Kerodon 5.3.6.13 （相互参照）
1411. Kerodon 5.3.6.9
1412. Kerodon 6.3.4.2
1413. Kerodon 6.3.4.3
1414. Kerodon 8.2.2.9
1415. Kerodon 8.2.2.10
1416. Kerodon 8.2.2.11
1417. Kerodon 8.2.2.12
1418. Kerodon 8.2.2.13
1419. Kerodon 8.2.0.3
1420. Kerodon 8.2.3.1
1421. Kerodon 8.2.3.2
1422. Kerodon 8.2.1.3
1423. Kerodon 7.1.5.2
1424. Kerodon 8.1.2.7
1425. Kerodon 8.1.2.10
1426. Kerodon 8.1.2.22
1427. Kerodon 8.1.2.23
1428. Kerodon 8.1.1.6
1429. Kerodon 8.2.0.2
1430. Kerodon 8.2.1.5
1431. Kerodon 5.6.6.20
1432. Kerodon 8.2.2.4
1433. Kerodon 8.2.3.6
1434. Kerodon 8.2.3.7
1435. Kerodon 8.2.3.4
1436. Kerodon 8.2.3.5
1437. Kerodon 4.5.3.9
1438. Kerodon 8.2.3.9
1439. Kerodon 8.2.4.1
1440. Kerodon 8.2.4.3
1441. Kerodon 8.3.5.1
1442. Kerodon 8.3.5.3
1443. Kerodon 8.3.3.2
1444. Kerodon 8.3.4.2
1445. Kerodon 8.3.4.6
1446. Kerodon 5.6.6.2
1447. Kerodon 8.3.4.12
1448. Kerodon 8.3.4.13
1449. Kerodon 8.3.4.15
1450. Kerodon 8.3.2.3
1451. Kerodon 8.3.4.16
1452. Kerodon 8.4.2.5
1453. Kerodon 8.4.2.7
1454. Kerodon 8.4.2.8
1455. Kerodon 9.1.5.4
1456. Kerodon 4.2.5.1
1457. Kerodon 7.1.1.6
1458. Kerodon 7.2.2.12
1459. Kerodon 5.3.2.9
1460. Kerodon 5.3.4.1
1461. Kerodon 7.5.8.2
1462. Kerodon 7.5.8.5
1463. Kerodon 7.5.8.13
1464. Kerodon 7.6.2.41
1465. Kerodon 7.6.2.42
1466. Kerodon 9.1.5.6
1467. Kerodon 9.1.5.7
1468. Kerodon 9.1.3.13; Kerodon 9.1.5.10 （相互参照）
1469. Kerodon 9.1.3.14
1470. Kerodon 9.1.4.13
1471. Kerodon 9.1.4.14
1472. Kerodon 9.1.4.15
1473. Kerodon 9.1.4.17
1474. Kerodon 9.1.4.18
1475. Kerodon 9.1.4.19
1476. Kerodon 9.1.4.5; Kerodon 9.1.4.6 （相互参照）
1477. Kerodon 9.1.4.16
1478. Kerodon 4.9.1.22
1479. Kerodon 9.2.3.1
1480. Kerodon 4.3.6.13
1481. Kerodon 7.1.1.13
1482. Kerodon 7.2.2.10
1483. Kerodon 7.2.2.11
1484. Kerodon 3.2.8.4
1485. Kerodon 3.2.8.5
1486. Kerodon 4.9.1.26
1487. Kerodon 7.2.3.4
1488. Kerodon 9.2.4.5
1489. Kerodon 9.2.4.3
1490. Kerodon 8.5.1.12
1491. Kerodon 9.2.2.13
1492. Kerodon 9.2.5.18
1493. Kerodon 7.1.6.16
1494. Kerodon 7.1.6.17
1495. Kerodon 6.2.6.5
1496. Kerodon 6.1.3.4
1497. Kerodon 6.1.1.5
1498. Kerodon 6.1.3.1
1499. Kerodon 6.1.3.3
1500. Kerodon 6.1.3.5
1501. Kerodon 6.1.3.7
1502. Kerodon 6.1.3.8
1503. Kerodon 5.2.8.11
1504. Kerodon 5.2.8.13
1505. Kerodon 8.1.2.12
1506. Kerodon 8.1.2.14
1507. Kerodon 8.1.2.11
1508. Kerodon 8.1.2.15
1509. Kerodon 8.1.2.19
1510. Kerodon 8.3.5.4
1511. Kerodon 8.3.3.3
1512. Kerodon 8.3.3.7
1513. Kerodon 5.6.6.3
1514. Kerodon 5.6.6.4
1515. Kerodon 5.6.6.6
1516. Kerodon 8.3.2.17
1517. Kerodon 8.3.2.9
1518. Kerodon 8.3.2.18
1519. Kerodon 8.3.2.20
1520. Kerodon 8.2.6.2
1521. Kerodon 8.2.6.1
1522. Kerodon 8.2.1.1
1523. Kerodon 8.3.2.7
1524. Kerodon 8.3.2.8
1525. Kerodon 8.3.2.19
1526. Kerodon 8.3.3.8
1527. Kerodon 8.3.3.13
1528. Kerodon 8.3.4.1
1529. Kerodon 8.2.0.4
1530. Kerodon 8.2.1.4
1531. Kerodon 8.2.4.5
1532. Kerodon 8.2.4.8
1533. Kerodon 8.2.4.6
1534. Kerodon 4.7.3.10
1535. Kerodon 8.2.5.2
1536. Kerodon 8.2.5.1
1537. Kerodon 5.6.2.9
1538. Kerodon 8.2.0.1
1539. Kerodon 8.3.2.1
1540. Kerodon 8.3.2.4
1541. Kerodon 8.3.2.5
1542. Kerodon 7.1.1.8
1543. Kerodon 7.2.2.7
1544. Kerodon 7.3.4.1
1545. Kerodon 7.4.2.13
1546. Kerodon 8.3.5.2
1547. Kerodon 8.3.5.6
1548. Kerodon 11.9.6.1
1549. Kerodon 7.3.1.9
1550. Kerodon 7.2.1.4
1551. Kerodon 7.2.1.9
1552. Kerodon 5.1.4.21
1553. Kerodon 5.1.4.22
1554. Kerodon 5.3.1.12
1555. Kerodon 7.2.3.14
1556. Kerodon 4.7.3.11
1557. Kerodon 8.1.1.15
1558. Kerodon 8.1.2.1
1559. Kerodon 8.2.4.9
1560. Kerodon 8.3.4.19
1561. Kerodon 8.3.4.20
1562. Kerodon 11.9.6.2
1563. Kerodon 11.9.6.3
1564. Kerodon 11.9.6.4
1565. Kerodon 11.9.6.5
1566. Kerodon 8.3.4.9
1567. Kerodon 8.3.4.10
1568. Kerodon 6.2.1.19
1569. Kerodon 7.1.1.18
1570. Kerodon 7.1.6.18
1571. Kerodon 7.1.8.2
1572. Kerodon 7.7.7.1
1573. Kerodon 9.2.2.17
1574. Kerodon 9.2.5.24
1575. Kerodon 4.7.6.12
1576. Kerodon 5.3.4.7
1577. Kerodon 5.3.4.11
1578. Kerodon 5.3.2.22
1579. Kerodon 5.3.2.1
1580. Kerodon 5.3.4.2
1581. Kerodon 5.3.4.10
1582. Kerodon 4.5.7.1
1583. Kerodon 5.3.5.1
1584. Kerodon 5.3.5.2
1585. Kerodon 5.3.1.5
1586. Kerodon 5.3.4.8
1587. Kerodon 5.3.5.8
1588. Kerodon 4.5.5.14
1589. Kerodon 5.3.2.18
1590. Kerodon 5.3.5.9
1591. Kerodon 5.3.5.6
1592. Kerodon 5.6.2.13
1593. Kerodon 5.6.4.1
1594. Kerodon 5.6.4.3
1595. Kerodon 5.3.3.1
1596. Kerodon 5.6.4.6
1597. Kerodon 5.6.4.7
1598. Kerodon 5.6.4.8
1599. Kerodon 5.6.5.7
1600. Kerodon 5.6.5.18
1601. Kerodon 7.1.3.5
1602. Kerodon 7.5.7.3
1603. Kerodon 4.3.1.4
1604. Kerodon 5.2.6.5
1605. Kerodon 5.2.6.1
1606. Kerodon 5.3.2.5
1607. Kerodon 5.3.2.6
1608. Kerodon 5.3.2.19
1609. Kerodon 5.3.2.20
1610. Kerodon 2.4.2.2
1611. Kerodon 5.3.3.23
1612. Kerodon 5.3.3.24
1613. Kerodon 5.3.3.26
1614. Kerodon 7.5.1.6
1615. Kerodon 7.5.1.7
1616. Kerodon 7.5.2.11
1617. Kerodon 1.2.3.1
1618. Kerodon 1.4.2.5
1619. Kerodon 1.2.1.28
1620. Kerodon 3.1.7.21
1621. Kerodon 3.2.4.17
1622. Kerodon 3.4.2.9
1623. Kerodon 3.4.2.1
1624. Kerodon 3.3.2.3
1625. Kerodon 3.3.2.2
1626. Kerodon 3.3.2.4
1627. Kerodon 3.3.2.9
1628. Kerodon 3.3.1.2
1629. Kerodon 3.3.1.5
1630. Kerodon 3.3.2.10
1631. Kerodon 3.3.5.1
1632. Kerodon 3.4.5.2
1633. Kerodon 3.4.5.3
1634. Kerodon 3.1.7.12
1635. Kerodon 3.4.5.1
1636. Kerodon 3.4.5.4
1637. Kerodon 3.4.5.5
1638. Kerodon 3.3.5.2
1639. Kerodon 3.4.5.7
1640. Kerodon 3.4.5.8
1641. Kerodon 3.4.6.7
1642. Kerodon 3.4.6.6
1643. Kerodon 3.4.6.1; Kerodon 3.4.6.2 （相互参照）
1644. Kerodon 1.1.3.9
1645. Kerodon 3.6.1.13
1646. Kerodon 3.6.1.11
1647. Kerodon 3.1.5.2
1648. Kerodon 3.6.1.12
1649. Kerodon 3.6.2.7
1650. Kerodon 3.6.2.9
1651. Kerodon 3.6.2.1
1652. Kerodon 3.6.2.2
1653. Kerodon 3.1.5.5
1654. Kerodon 3.1.5.6
1655. Kerodon 3.1.7.3
1656. Kerodon 3.6.3.3
1657. Kerodon 3.6.4.1
1658. Kerodon 7.5.4.12
1659. Kerodon 7.5.2.7
1660. Kerodon 7.5.5.6
1661. Kerodon 7.5.5.13
1662. Kerodon 7.5.5.14
1663. Kerodon 7.5.5.15
1664. Kerodon 7.5.8.4
1665. Kerodon 7.5.8.9
1666. Kerodon 7.5.6.1
1667. Kerodon 7.5.8.6
1668. Kerodon 7.5.3.3
1669. Kerodon 5.3.1.3
1670. Kerodon 5.3.1.14
1671. Kerodon 5.3.1.7
1672. Kerodon 5.3.1.1
1673. Kerodon 7.5.3.1
1674. Kerodon 7.5.3.2
1675. Kerodon 7.5.3.4
1676. Kerodon 7.5.3.8
1677. Kerodon 7.5.3.9
1678. Kerodon 7.5.3.10
1679. Kerodon 7.5.3.7
1680. Kerodon 7.5.3.11
1681. Kerodon 7.5.3.12
1682. Kerodon 7.5.4.2
1683. Kerodon 4.5.6.19
1684. Kerodon 7.5.6.6
1685. Kerodon 7.5.8.7
1686. Kerodon 4.5.7.2
1687. Kerodon 9.1.6.8
1688. Kerodon 9.1.6.9
1689. Kerodon 1.5.5.3
1690. Kerodon 9.1.6.10
1691. Kerodon 9.1.6.11
1692. Kerodon 9.1.6.12
1693. Kerodon 9.1.6.7
1694. Kerodon 9.1.6.1
1695. Kerodon 9.1.6.3
1696. Kerodon 9.1.8.1
1697. Kerodon 9.1.9.1
1698. Kerodon 1.4.0.9
1699. Kerodon 4.9.4.1
1700. Kerodon 3.6.1.1
1701. Kerodon 9.2.0.5
1702. Kerodon 9.2.5.25
1703. Kerodon 9.2.5.9
1704. Kerodon 9.2.5.10
1705. Kerodon 9.1.9.6
1706. Kerodon 9.1.9.7
1707. Kerodon 9.1.9.5
1708. Kerodon 9.1.9.8
1709. Kerodon 7.1.9.5
1710. Kerodon 4.5.3.10
1711. Kerodon 4.6.4.2
1712. Kerodon 8.3.7.4
1713. Kerodon 8.1.1.16
1714. Kerodon 8.1.2.16
1715. Kerodon 8.1.2.17
1716. Kerodon 8.3.7.3
1717. Kerodon 8.3.7.6
1718. Kerodon 5.3.3.18
1719. Kerodon 5.6.5.6
1720. Kerodon 7.1.8.13
1721. Kerodon 4.3.6.7
1722. Kerodon 1.5.4.5
1723. Kerodon 1.5.5.2
1724. Kerodon 7.2.1.19
1725. Kerodon 7.3.4.3
1726. Kerodon 7.3.8.4
1727. Kerodon 7.3.8.5
1728. Kerodon 7.3.8.6
1729. Kerodon 7.3.8.8
1730. Kerodon 8.3.7.7
1731. Kerodon 8.3.7.1
1732. Kerodon 8.3.7.2
1733. Kerodon 9.2.8.3
1734. Kerodon 9.2.8.5
1735. Kerodon 9.3.2.5
1736. Kerodon 4.9.8.12
1737. Kerodon 4.9.3.19
1738. Kerodon 4.6.1.15
1739. Kerodon 4.8.3.6
1740. Kerodon 4.8.3.7
1741. Kerodon 4.9.8.5
1742. Kerodon 4.9.5.5
1743. Kerodon 4.9.5.10
1744. Kerodon 5.2.2.19
1745. Kerodon 4.9.6.1
1746. Kerodon 3.2.6.2
1747. Kerodon 4.9.6.2
1748. Kerodon 4.9.7.4
1749. Kerodon 4.9.7.7
1750. Kerodon 4.9.8.6
1751. Kerodon 4.9.8.1
1752. Kerodon 4.9.8.7
1753. Kerodon 5.1.5.14
1754. Kerodon 5.1.5.15
1755. Kerodon 5.1.5.16
1756. Kerodon 5.6.7.7
1757. Kerodon 7.3.5.1
1758. Kerodon 4.9.4.6
1759. Kerodon 4.9.5.7
1760. Kerodon 7.1.1.17
1761. Kerodon 7.6.6.14
1762. Kerodon 7.6.6.19
1763. Kerodon 8.4.1.20
1764. Kerodon 8.4.1.21
1765. Kerodon 8.4.1.22
1766. Kerodon 8.4.2.4
1767. Kerodon 7.3.6.15
1768. Kerodon 8.3.3.14
1769. Kerodon 7.1.1.11
1770. Kerodon 7.3.1.13
1771. Kerodon 8.4.1.19
1772. Kerodon 8.4.6.6
1773. Kerodon 7.6.6.21
1774. Kerodon 8.3.3.15
1775. Kerodon 8.3.3.16
1776. Kerodon 8.3.3.17
1777. Kerodon 8.4.3.4
1778. Kerodon 7.1.5.10
1779. Kerodon 7.1.5.12
1780. Kerodon 7.3.3.17
1781. Kerodon 7.3.6.12
1782. Kerodon 7.3.6.13
1783. Kerodon 7.3.2.6
1784. Kerodon 8.4.1.5
1785. Kerodon 8.4.1.15
1786. Kerodon 8.4.1.16
1787. Kerodon 8.4.1.18
1788. Kerodon 8.4.2.2
1789. Kerodon 8.4.3.5
1790. Kerodon 8.4.3.2
1791. Kerodon 8.4.6.9
1792. Kerodon 8.4.6.10
1793. Kerodon 8.4.6.8
1794. Kerodon 9.2.1.3
1795. Kerodon 9.2.2.6
1796. Kerodon 9.3.1.7
1797. Kerodon 8.5.5.5
1798. Kerodon 8.5.5.4
1799. Kerodon 7.2.3.13
1800. Kerodon 3.3.1.6
1801. Kerodon 3.3.1.7
1802. Kerodon 3.3.1.9
1803. Kerodon 3.3.1.11
1804. Kerodon 3.4.5.9
1805. Kerodon 8.5.3.4
1806. Kerodon 8.5.4.5
1807. Kerodon 8.5.6.3
1808. Kerodon 8.5.6.10
1809. Kerodon 8.5.6.15
1810. Kerodon 8.5.6.16
1811. Kerodon 8.5.6.17
1812. Kerodon 8.5.6.19
1813. Kerodon 8.5.2.7
1814. Kerodon 9.1.0.1
1815. Kerodon 8.5.2.9
1816. Kerodon 9.1.1.10
1817. Kerodon 7.2.2.8
1818. Kerodon 9.1.5.13
1819. Kerodon 9.1.8.11
1820. Kerodon 9.1.1.6
1821. Kerodon 9.3.4.11
1822. Kerodon 7.4.5.1
1823. Kerodon 9.1.3.11
1824. Kerodon 9.1.5.15
1825. Kerodon 9.1.5.16
1826. Kerodon 8.6.4.3
1827. Kerodon 4.9.8.2
1828. Kerodon 8.3.2.21
1829. Kerodon 8.6.4.12
1830. Kerodon 8.6.4.13
1831. Kerodon 8.3.1.8
1832. Kerodon 8.3.1.9
1833. Kerodon 5.2.4.4
1834. Kerodon 5.3.6.10
1835. Kerodon 6.2.5.5
1836. Kerodon 6.2.5.6
1837. Kerodon 6.2.5.7
1838. Kerodon 7.3.6.3
1839. Kerodon 8.6.5.9
1840. Kerodon 8.6.5.10
1841. Kerodon 8.6.5.12
1842. Kerodon 8.6.5.6
1843. Kerodon 8.6.5.7
1844. Kerodon 4.5.8.4
1845. Kerodon 4.5.8.19
1846. Kerodon 7.3.7.9
1847. Kerodon 8.6.5.11
1848. Kerodon 8.6.5.13
1849. Kerodon 8.6.5.14
1850. Kerodon 8.6.5.15
1851. Kerodon 8.6.5.8
1852. Kerodon 8.6.5.16
1853. Kerodon 8.6.5.17
1854. Kerodon 8.6.5.18
1855. Kerodon 8.6.5.1
1856. Kerodon 8.6.5.2
1857. Kerodon 8.6.1.4
1858. Kerodon 8.6.2.1
1859. Kerodon 8.6.2.2
1860. Kerodon 8.6.2.6
1861. Kerodon 8.6.2.7
1862. Kerodon 8.6.1.1
1863. Kerodon 8.6.1.13
1864. Kerodon 8.6.2.8
1865. Kerodon 8.6.2.3
1866. Kerodon 8.6.2.4
1867. Kerodon 8.1.1.7
1868. Kerodon 8.1.1.2
1869. Kerodon 8.1.1.4
1870. Kerodon 8.1.3.5
1871. Kerodon 8.1.3.7
1872. Kerodon 8.6.3.9
1873. Kerodon 8.1.3.6
1874. Kerodon 6.3.5.5
1875. Kerodon 6.3.5.2
1876. Kerodon 8.1.1.14
1877. Kerodon 8.1.2.4
1878. Kerodon 8.1.7.1
1879. Kerodon 8.1.6.3
1880. Kerodon 8.1.7.9
1881. Kerodon 8.1.6.12
1882. Kerodon 8.1.3.9
1883. Kerodon 8.1.6.1
1884. Kerodon 8.1.7.4
1885. Kerodon 8.1.7.11
1886. Kerodon 8.1.7.12
1887. Kerodon 8.1.7.13
1888. Kerodon 8.1.7.6
1889. Kerodon 8.1.7.14
1890. Kerodon 8.6.3.1
1891. Kerodon 8.6.3.4
1892. Kerodon 8.1.6.5
1893. Kerodon 8.1.6.6
1894. Kerodon 8.1.9.8
1895. Kerodon 8.1.9.5
1896. Kerodon 8.1.10.6
1897. Kerodon 8.1.10.8
1898. Kerodon 7.6.2.9
1899. Kerodon 7.6.2.38
1900. Kerodon 7.6.2.39
1901. Kerodon 8.1.4.6
1902. Kerodon 1.3.5.4
1903. Kerodon 5.4.6.6
1904. Kerodon 5.4.5.12
1905. Kerodon 5.4.7.4
1906. Kerodon 5.4.7.5
1907. Kerodon 8.1.2.6
1908. Kerodon 8.1.3.10
1909. Kerodon 8.1.3.11
1910. Kerodon 2.3.2.3
1911. Kerodon 8.1.4.2
1912. Kerodon 8.1.3.4
1913. Kerodon 8.1.4.3
1914. Kerodon 8.1.4.4
1915. Kerodon 8.1.4.7
1916. Kerodon 8.1.6.2
1917. Kerodon 8.1.6.4; Kerodon 8.1.6.7; Kerodon 8.1.6.8 （相互参照）
1918. Kerodon 8.1.6.10
1919. Kerodon 8.1.9.10
1920. Kerodon 8.1.9.9
1921. Kerodon 8.1.9.11
1922. Kerodon 8.1.10.9
1923. Kerodon 2.3.2.4
1924. Kerodon 8.1.7.5
1925. Kerodon 8.1.10.11
1926. Kerodon 8.6.3.6
1927. Kerodon 8.6.3.7
1928. Kerodon 8.6.3.8
1929. Kerodon 8.6.3.10
1930. Kerodon 8.6.3.11
1931. Kerodon 8.6.3.5
1932. Kerodon 8.6.3.14
1933. Kerodon 4.2.3.1
1934. Kerodon 8.1.0.2
1935. Kerodon 8.1.0.5
1936. Kerodon 8.6.6.7
1937. Kerodon 8.6.6.10
1938. Kerodon 8.6.6.12
1939. Kerodon 8.6.6.11
1940. Kerodon 8.6.6.13
1941. Kerodon 8.6.6.14
1942. Kerodon 8.6.6.1
1943. Kerodon 8.6.6.3
1944. Kerodon 8.6.8.3
1945. Kerodon 9.1.1.4
1946. Kerodon 9.3.4.7
1947. Kerodon 9.3.4.13
1948. Kerodon 5.3.7.3
1949. Kerodon 6.3.1.16
1950. Kerodon 6.3.4.4
1951. Kerodon 6.3.4.1
1952. Kerodon 7.4.5.8
1953. Kerodon 6.3.1.11
1954. Kerodon 7.4.5.10
1955. Kerodon 6.3.2.1
1956. Kerodon 7.4.5.18
1957. Kerodon 6.3.2.10
1958. Kerodon 6.3.2.13
1959. Kerodon 7.4.5.19
1960. Kerodon 4.3.3.25
1961. Kerodon 4.6.1.6
1962. Kerodon 7.4.5.11
1963. Kerodon 7.4.5.12
1964. Kerodon 7.4.6.1
1965. Kerodon 7.4.6.2
1966. Kerodon 7.4.6.3
1967. Kerodon 7.4.5.13; Kerodon 7.4.5.16 （相互参照）
1968. Kerodon 9.3.4.19
1969. Kerodon 9.3.4.20
1970. Kerodon 9.3.4.14; Kerodon 9.3.4.15; Kerodon 9.3.4.21 （相互参照）
1971. Kerodon 9.3.2.1
1972. Kerodon 9.3.2.3
1973. Kerodon 9.3.7.2
1974. Kerodon 7.3.8.3
1975. Kerodon 7.4.3.11
1976. Kerodon 8.4.6.3
1977. Kerodon 8.4.6.5
1978. Kerodon 8.4.6.11
1979. Kerodon 9.3.1.12
1980. Kerodon 9.3.1.14
1981. Kerodon 9.3.7.10
1982. Kerodon 9.3.7.11
1983. Kerodon 9.4.5.9
1984. Kerodon 9.4.5.10
1985. Kerodon 9.4.8.15
1986. Kerodon 9.4.9.9
1987. Kerodon 3.3.7.4
1988. Kerodon 4.3.7.2
1989. Kerodon 4.3.6.6
1990. Kerodon 4.5.3.12
1991. Kerodon 5.1.7.7
1992. Kerodon 7.2.3.2
1993. Kerodon 7.2.3.11
1994. Kerodon 7.4.2.14
1995. Kerodon 7.4.3.13
1996. Kerodon 7.4.3.14
1997. Kerodon 3.2.4.15
1998. Kerodon 3.3.3.6
1999. Kerodon 4.9.4.16
2000. Kerodon 9.1.3.5
2001. Kerodon 9.1.3.6
2002. Kerodon 9.1.3.7
2003. Kerodon 9.1.5.14
2004. Kerodon 9.4.4.15
2005. Kerodon 9.4.4.4
2006. Kerodon 9.4.4.6
2007. Kerodon 9.4.9.4
2008. Kerodon 9.5.4.4
2009. Kerodon 9.5.4.5
2010. Kerodon 9.5.4.6
2011. HTT 5.5.3.12
2012. HA 1.4.4.11
2013. HA 4.6.2.2
2014. HA 4.6.2.18
2015. HA 2.4.1.6
2016. HA 4.1.7.10
2017. HTT 3.1.0.1
2018. HA 4.8.1.2
2019. HTT 5.3.6.1
2020. HTT 5.3.6.2
2021. HTT 5.3.6.11
2022. HA 4.8.1.3
2023. HA 4.8.1.4
2024. HA 4.1.1.18
2025. HA 4.2.4.9
2026. HTT 3.3.4.5
2027. HTT 4.1.2.13
2028. HTT 4.1.2.14
2029. HTT 4.1.2.16
2030. HTT 4.1.2.17
2031. HTT 4.1.2.18
2032. HTT 4.3.3.10
2033. HTT 3.3.2.2
2034. HTT 5.1.5.2
2035. HTT 5.1.3.1
2036. HTT 5.1.5.3
2037. HTT 3.3.3.4
2038. HTT 5.1.3.2
2039. HTT 5.1.5.4
2040. HTT 5.1.5.5
2041. HTT 5.3.1.7
2042. HTT 5.3.5.9
2043. HA 4.8.5.2
2044. HA 4.8.4.8
2045. HTT 4.2.3.4
2046. HTT 4.2.3.1
2047. HTT 4.2.3.5
2048. HTT 4.2.3.6
2049. HTT 4.2.3.8
2050. HTT 4.1.1.8
2051. HTT A.2.6.3
2052. HTT 4.2.3.10
2053. HTT 4.2.3.11
2054. HTT 5.1.6.4
2055. HTT 5.1.6.8
2056. HTT 5.1.6.10
2057. HTT 5.3.4.5
2058. HTT 3.3.2.6
2059. HTT 4.4.4.5
2060. HTT 3.3.2.7
2061. HTT 5.3.3.3
2062. HTT 5.3.5.2
2063. HTT 5.3.5.3
2064. HTT 5.3.5.4
2065. HTT 5.3.5.5
2066. HTT 5.3.5.11
2067. HTT 4.3.2.16
2068. HTT 5.1.5.6
2069. HTT 5.3.4.14
2070. HTT 5.3.4.15
2071. HTT 5.3.4.16
2072. HTT 5.3.4.17
2073. HTT 5.3.5.10
2074. HTT 5.2.7.5
2075. HTT 5.2.4.1
2076. HTT 5.2.4.2
2077. HTT 5.3.4.18
2078. HTT 5.3.5.12
2079. HTT 5.4.2.2
2080. HTT 5.3.1.10
2081. HTT 5.5.1.3
2082. HTT 5.5.1.4
2083. HTT 5.5.1.1
2084. HTT 5.5.1.9
2085. HA 7.2.4.2
2086. DAGXIII 2.2.5
2087. HA 3.2.2.1
2088. HA 3.2.2.5
2089. HA 5.1.1.3
2090. HTT 1.1.5.5
2091. HA 2.1.1.23
2092. HA 5.1.1.9
2093. HA 5.1.1.10
2094. HA 5.1.1.11
2095. HA A.3.2
2096. HTT 4.2.4.1
2097. HA A.3.1; HA A.3.8; HA A.3.10 （相互参照）
2098. HA 5.1.1.1
2099. HA 5.1.1.4
2100. HTT 2.3.4.1
2101. HTT 2.3.4.18
2102. HA 5.1.1.7
2103. HA 1.1.2.5
2104. HA 1.1.3.4
2105. HTT 4.4.2.2
2106. HTT 4.4.2.4
2107. HTT 4.4.2.6
2108. HTT 4.4.3.1
2109. HTT 4.4.3.2
2110. HTT 5.3.2.10
2111. HA 1.1.4.1
2112. HA 1.4.2.17
2113. HA 1.1.2.7
2114. HA 1.1.2.11
2115. HA 1.1.2.14
2116. HA 1.1.3.3
2117. HA 1.4.2.1
2118. HA 1.4.2.12
2119. HA 1.4.2.15
2120. HA 1.4.2.11; HA 1.4.2.13 （相互参照）
2121. HTT 5.5.4.18
2122. HTT 5.5.4.19
2123. HA 1.4.2.4
2124. HA 1.4.2.3
2125. HA 1.4.2.10
2126. HA 1.4.2.16
2127. HA 1.4.2.23
2128. HTT 5.2.7.4
2129. HTT 5.2.7.7
2130. HTT 5.5.4.11
2131. HTT 5.5.4.15
2132. HTT 5.5.4.20
2133. HTT 5.5.7.2
2134. HTT 5.5.7.3
2135. HA 1.4.2.26
2136. HTT 5.4.2.1
2137. HTT 5.4.7.17
2138. HTT 5.5.3.15
2139. HTT 5.5.3.16
2140. HTT 5.5.4.17
2141. HTT 5.5.3.17
2142. HTT 5.5.3.18
2143. HA 1.4.2.24
2144. HA 1.2.1.17
2145. HA 1.2.1.19
2146. HA 4.2.1.5
2147. HA 4.2.1.9
2148. HA 4.2.1.17
2149. HA 4.2.3.3
2150. HA 7.1.1.13
2151. HA 2.2.1.6
2152. HA 2.2.1.1
2153. HA 2.2.1.3
2154. HA 2.2.1.8
2155. HA 2.2.1.11
2156. HA 2.2.1.9
2157. HA 7.1.3.10
2158. HA 7.1.3.15
2159. HA 7.1.2.13
2160. HA 7.1.3.16
2161. HA 7.1.3.18
2162. DAGXIII 2.2.6
2163. DAGXIII 2.2.7
2164. NS A.5
2165. HA 6.1.6.3
2166. HA 6.1.6.10
2167. HA 6.1.6.11
2168. HA 6.1.6.12
2169. HA 6.1.6.13
2170. NS I.1.1
2171. NS I.1.5
2172. HTT 4.3.2.12
2173. HTT 5.2.2.8
2174. HTT 4.3.2.17
2175. HTT 5.2.2.6
2176. HTT 5.2.4.3
2177. HTT 4.3.3.5; HTT 4.3.3.7 （相互参照）
2178. NS I.1.6
2179. NS I.1.7
2180. HA 6.1.6.4
2181. HA 6.1.6.5
2182. HA 6.1.6.6
2183. HA 6.1.6.7
2184. NS I.1.8
2185. NS I.1.9
2186. NS I.1.10
2187. NS I.1.11
2188. NS I.1.12
2189. NS I.1.13
2190. HTT 5.2.7.2
2191. HTT 5.5.2.9
2192. HTT 5.3.4.9
2193. HTT 5.3.4.10
2194. HTT 5.3.4.12
2195. HTT 5.4.5.7
2196. HTT 5.3.4.13
2197. HTT 4.3.1.11
2198. HTT 5.4.1.2
2199. HTT 5.4.4.1
2200. HTT 5.4.4.2
2201. HTT 5.4.4.3
2202. HTT 5.5.3.6
2203. NS I.3.3
2204. NS I.3.5
2205. HA 7.3.2.5
2206. HA 7.3.2.6
2207. HA 7.3.2.7
2208. NS I.3.6
2209. HA 1.1.3.1
2210. HA 1.4.2.6
2211. HA 1.4.2.19
2212. HA 1.4.2.21
2213. HA 1.4.2.22
2214. HA 1.4.2.18
2215. HA 1.4.2.25
2216. HTT 1.2.13.8
2217. HTT 4.4.2.8
2218. HTT 4.4.2.9
2219. HTT 5.4.5.9
2220. HTT 2.2.2.7
2221. HTT 5.4.5.10
2222. HTT 5.4.5.11
2223. HTT 5.4.5.12
2224. HTT 5.4.5.13
2225. HTT 5.4.5.14
2226. HTT 5.4.5.15
2227. HTT 5.4.5.16
2228. HTT 5.5.3.11
2229. HA 1.4.4.4
2230. HA 1.4.4.5
2231. NS II.2.8
2232. NS II.2.14
2233. NS I.3.1; NS I.3.8; NS I.4.1; NS II.2.13 （相互参照）
2234. NS III.1.1
2235. NS III.1.2
2236. NS III.1.4
2237. HA 2.2.5.1
2238. HA 2.4.3.19
2239. HA 3.2.1.3
2240. HA 3.2.1.4
2241. HA 3.2.1.5
2242. HA 3.2.1.10
2243. HA 3.2.1.8
2244. HA 3.2.1.9
2245. HA 3.2.4.1
2246. HA 3.2.4.2
2247. HA 3.2.4.3
2248. HA 3.2.4.4
2249. HA 3.2.4.7
2250. NS IV.1.1
2251. HA 7.5.0.1
2252. HA 7.5.0.4
2253. NS IV.1.2

## 上限による未展開キュー

0項目。review停止点を除く採用経路の探索キューは空。未解決証明は上記の一覧に残る。

<details>
<summary>刈り込みで外れた項目（v2比）</summary>

- HTT 1.1.2.2
- HTT 1.2.12.9
- HTT 2.1.1.4
- HTT 2.1.1.5
- HTT 2.1.1.6
- HTT 2.1.3.2
- HTT 3.2.2.11
- HTT 3.3.1.3
- HTT 4.1.2.7
- HTT 4.2.3.13
- HTT 4.2.3.14
- HTT 4.2.3.15
- HTT 4.2.3.16
- HTT 4.2.4.7
- HTT 4.4.5.2
- HTT 4.4.5.9
- HTT 4.4.5.10
- HTT 4.4.5.11
- HTT 4.4.5.12
- HTT 4.4.5.15
- HTT 5.1.6.3
- HTT 5.2.1.3
- HTT 5.2.1.5
- HTT 5.2.2.3
- HTT 5.2.3.1
- HTT 5.2.3.2
- HTT 5.2.3.3
- HTT 5.2.3.4
- HTT 5.3.1.9
- HTT 5.3.1.12
- HTT 5.3.1.17
- HTT 5.3.1.18
- HTT 5.3.5.7
- HTT 5.3.5.15
- HTT 5.4.1.8
- HTT 5.4.2.4
- HTT 5.4.2.5
- HTT 5.4.6.6
- HTT 5.4.7.7
- HTT 5.5.2.7
- HTT 5.5.4.2
- HTT 5.5.4.4
- HTT 5.5.4.5
- HTT 5.5.4.6
- HTT 5.5.4.10
- HTT 5.5.4.13
- HTT 5.5.5.9
- HTT 5.5.5.11
- HTT 5.5.5.12
- HTT 5.5.5.13
- HTT 5.5.5.14
- HTT 6.5.3.7
- Kerodon 1.2.1.3
- Kerodon 1.2.1.4
- Kerodon 1.2.1.5
- Kerodon 1.2.1.6
- Kerodon 1.2.1.7
- Kerodon 1.2.1.8
- Kerodon 1.2.1.10
- Kerodon 1.2.1.11
- Kerodon 1.2.1.12
- Kerodon 1.2.1.13
- Kerodon 1.2.1.18
- Kerodon 1.2.1.19
- Kerodon 1.2.1.22
- Kerodon 1.2.1.23
- Kerodon 1.2.5.10
- Kerodon 1.3.1.4
- Kerodon 1.4.6.6
- Kerodon 1.4.6.8
- Kerodon 1.4.6.13
- Kerodon 1.5.3.1
- Kerodon 1.5.4.8
- Kerodon 1.5.4.12
- Kerodon 1.5.4.15
- Kerodon 1.5.5.1
- Kerodon 1.5.5.6
- Kerodon 1.5.5.7
- Kerodon 2.4.5.11
- Kerodon 2.4.5.12
- Kerodon 3.1.1.8
- Kerodon 3.1.2.1
- Kerodon 3.1.2.9
- Kerodon 3.2.3.1
- Kerodon 3.2.5.3
- Kerodon 3.2.5.4
- Kerodon 3.3.1.8
- Kerodon 3.3.2.1
- Kerodon 3.3.3.10
- Kerodon 3.3.3.11
- Kerodon 3.3.3.13
- Kerodon 3.3.3.17
- Kerodon 3.3.3.18
- Kerodon 3.3.3.19
- Kerodon 3.3.4.2
- Kerodon 3.3.4.8
- Kerodon 3.3.5.3
- Kerodon 3.3.5.4
- Kerodon 3.3.5.6
- Kerodon 3.3.5.7
- Kerodon 3.3.5.8
- Kerodon 3.3.5.9
- Kerodon 3.6.1.5
- Kerodon 4.1.1.3
- Kerodon 4.1.2.16
- Kerodon 4.2.1.6
- Kerodon 4.2.1.11
- Kerodon 4.2.4.2
- Kerodon 4.2.4.4
- Kerodon 4.2.4.5
- Kerodon 4.2.4.6
- Kerodon 4.2.4.7
- Kerodon 4.2.4.10
- Kerodon 4.3.2.1
- Kerodon 4.3.3.7
- Kerodon 4.3.3.14
- Kerodon 4.3.3.18
- Kerodon 4.3.3.23
- Kerodon 4.3.3.27
- Kerodon 4.3.3.28
- Kerodon 4.4.1.1
- Kerodon 4.4.1.3
- Kerodon 4.4.1.7
- Kerodon 4.4.1.8
- Kerodon 4.4.1.10
- Kerodon 4.4.2.3
- Kerodon 4.4.2.4
- Kerodon 4.4.2.5
- Kerodon 4.4.2.7
- Kerodon 4.4.3.14
- Kerodon 4.4.3.20
- Kerodon 4.5.4.1
- Kerodon 4.5.4.3
- Kerodon 4.5.4.16
- Kerodon 4.5.6.3
- Kerodon 4.5.6.13
- Kerodon 4.6.1.10
- Kerodon 4.6.2.4
- Kerodon 4.6.2.10
- Kerodon 4.6.2.11
- Kerodon 4.6.3.10
- Kerodon 4.6.3.11
- Kerodon 4.6.4.11
- Kerodon 4.6.4.16
- Kerodon 4.6.4.25
- Kerodon 4.6.6.4
- Kerodon 4.6.6.7
- Kerodon 4.7.1.14
- Kerodon 4.9.1.5
- Kerodon 4.9.1.14
- Kerodon 4.9.1.15
- Kerodon 4.9.1.16
- Kerodon 4.9.1.17
- Kerodon 4.9.1.18
- Kerodon 4.9.1.21
- Kerodon 4.9.1.23
- Kerodon 4.9.1.34
- Kerodon 5.2.3.4
- Kerodon 5.2.3.9
- Kerodon 5.3.4.12
- Kerodon 5.3.4.13
- Kerodon 5.3.4.14
- Kerodon 5.3.4.15
- Kerodon 6.1.2.11
- Kerodon 6.2.1.14
- Kerodon 7.1.8.1
- Kerodon 7.2.1.14
- Kerodon 7.3.3.3
- Kerodon 7.3.3.9
- Kerodon 7.3.3.15
- Kerodon 7.3.3.20
- Kerodon 7.3.4.7
- Kerodon 7.5.4.5
- Kerodon 8.5.1.8
- Kerodon 8.5.1.9
- Kerodon 8.5.1.10
- Kerodon 8.5.1.11
- Kerodon 9.4.9.10
- Kerodon 9.4.9.11

</details>
