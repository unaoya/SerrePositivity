# P⁰の項目単位の閉包 v2（⑤d、2026-11-16）

基準 main `deb58367a` を枝 `codex/p0-item-closure` に fast-forward で取り込んだ。`formalization-plans/stage-ii/p0/p0-section-map.md` §8–§10 と今回のユーザー指定を適用する。旧1,014項目の3ファイルは `v1/` にバイト単位で保存し、300節の `../section-closure/` は変更していない。

## 停止点：2,000項目、閉包は未完成

**指定上限の2,000項目に達したため、項目・依存先の追加を停止した。完成・固定点ではない。** 辺は位置ごとに重複を統合して **5,180件**、位置を区別しない項目対は **4,962対**。未解決の証明は51項目（HTT 36、HA 15）。採取済みの出辺を持つ項目1,818、停止時の項目1、未展開キュー181である。出辺採取済みでも、後述の未同定参照・暗黙の定義入力の照合は完了していない。

最後に収録した項目は Kerodon Theorem 8.2.2.11（Tag 044K）。Kerodon 8.2.3.4 の4番目（0始まりの添字3）の参照を処理した時点で停止し、この項目の明示タグ参照の残りは0。走査済みフラグの確定前なので、181項目のキューとは別に停止中の1項目として数える。

| 文献 | 項目数 |
|---|---:|
| DAGXIII | 27 |
| NS | 25 |
| HA | 275 |
| HTT | 273 |
| Kerodon | 1400 |
| 合計 | 2000 |

到達元は採用した辺全体で再計算した。`items.csv` の `reached_from` の先頭は、DAG-only（DAG根だけ）、DAG+NS（両方）、NS-only（NS根だけ）。その後に根の印と直接の親項目を記録する。未展開部分を足した後には分類が変わることがある。

| 到達元 | 項目数 |
|---|---:|
| DAG-only | 263 |
| DAG+NS | 1647 |
| NS-only | 90 |

## 13個の根

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

節の他の項目を自動的に含めてはいない。各項目の主張・証明にある番号つき引用に加えて、主張が使う定義・記法、別の位置に置かれた証明、内容を項目に同定できた節参照を採取する。一般性をP⁰の利用例に縮めてはいない。

## モデル圏を使う証明の扱い

数学的な主張は元のHA・HTTの番号のまま保持する。原証明がモデル圏を経由する場合、その証明の出辺を採用せず、全仮定・全結論を比較できた次の4項目のみKerodonへ差し替えた。`edges.csv` の `kind=kerodon-proof` は5辺。対応表の類似項目や共通するLean宣言だけをもって同じ主張と判定していない。

| 元の項目 | 採用する証明 | 一般性・残りの結論の確認 |
|---|---|---|
| HTT 4.1.3.1 | [Kerodon 7.2.3.1, Tag 02NY](https://kerodon.net/tag/02NY) | 任意の単体集合 C→D、D は∞圏。右共終性とcosliceの弱可縮性。左右のうち右側を使う。 |
| HTT 3.3.1.3 | [Kerodon 5.6.7.6, Tag 029H](https://kerodon.net/tag/029H) | 底も任意の単体集合。coCartesian版をoppositeに移す。exponentiableの定義4.5.8.10（Tag02TX）により、任意のbase changeでのcategorical equivalence保存を得る。底の∞圏性を仮定しない。 |
| HTT 5.4.6.6 | [Kerodon 9.4.9.11, Tag 06LP](https://kerodon.net/tag/06LP) | accessibleな三圏と二関手のpullback。圏・射影のaccessibilityだけでなく、accessibleな域からの関手を両射影で判定する結論まで。 |
| HTT 5.5.3.12 | [Kerodon 9.5.4.6, Tag 06PA](https://kerodon.net/tag/06PA) と [7.1.9.8, Tag 06AJ](https://kerodon.net/tag/06AJ) | 三つのpresentable∞圏、両脚はcolimit保存。前者でpresentability、後者で射影のcolimit保存と両射影による判定も得る。presentabilityだけへの弱化をしない。 |

将来Leanを実装する場合のdocstringには、元のHTT番号、採用したKerodon番号・Tag、元のモデル圏を使う証明から差し替えた旨、および上のopposite／二つの補題の併用を記す。今回は紙のみでdocstring・Leanの変更はしていない。

### 未解決の51項目

以下は `items.csv` の `reason` にも `unresolved:` として記録した。主張を消したり特別な場合へ縮めたりせず、同じ一般性のモデル圏なし証明が未確認の箇所として残す。原証明の出辺を外したことは、代替証明が済んだことを意味しない。一般の `[ModelCategory SSet]` を仮定する実装を認めるものでもない。

| 文献 | 番号 | 未解決の理由 |
|---|---|---|
| HA | 2.4.1.8 | 元の証明にモデル圏の使用（直接、またはモデル圏についての補題への参照）がある。同じ全主張・全仮定のモデル圏なしKerodon証明は今回の対応表・原典検索では確認できなかった |
| HA | 3.1.2.3 | 元の証明にモデル圏の使用（直接、またはモデル圏についての補題への参照）がある。同じ全主張・全仮定のモデル圏なしKerodon証明は今回の対応表・原典検索では確認できなかった |
| HA | 3.2.2.1 | 元の証明にモデル圏の使用（直接、またはモデル圏についての補題への参照）がある。同じ全主張・全仮定のモデル圏なしKerodon証明は今回の対応表・原典検索では確認できなかった |
| HA | 3.2.2.8 | 元の証明にモデル圏の使用（直接、またはモデル圏についての補題への参照）がある。同じ全主張・全仮定のモデル圏なしKerodon証明は今回の対応表・原典検索では確認できなかった |
| HA | 3.2.4.3 | 元の証明にモデル圏の使用（直接、またはモデル圏についての補題への参照）がある。同じ全主張・全仮定のモデル圏なしKerodon証明は今回の対応表・原典検索では確認できなかった |
| HA | 3.4.1.4 | 元の証明にモデル圏の使用（直接、またはモデル圏についての補題への参照）がある。同じ全主張・全仮定のモデル圏なしKerodon証明は今回の対応表・原典検索では確認できなかった |
| HA | 3.4.4.3 | 元の証明にモデル圏の使用（直接、またはモデル圏についての補題への参照）がある。同じ全主張・全仮定のモデル圏なしKerodon証明は今回の対応表・原典検索では確認できなかった |
| HA | 4.2.2.12 | 主張はAlg_LMとLMod_A∞の数学的な同値。原証明のモデル圏経由を避ける代替証明が未解決 |
| HA | 4.2.3.1 | 元の証明にモデル圏の使用（直接、またはモデル圏についての補題への参照）がある。同じ全主張・全仮定のモデル圏なしKerodon証明は今回の対応表・原典検索では確認できなかった |
| HA | 4.4.1.11 | 元の証明にモデル圏の使用（直接、またはモデル圏についての補題への参照）がある。同じ全主張・全仮定のモデル圏なしKerodon証明は今回の対応表・原典検索では確認できなかった |
| HA | 4.4.1.28 | 元の証明にモデル圏の使用（直接、またはモデル圏についての補題への参照）がある。同じ全主張・全仮定のモデル圏なしKerodon証明は今回の対応表・原典検索では確認できなかった |
| HA | 4.8.1.2 | 主張・定義自体がモデル圏の構造・対象を使う。採用経路がstatementの入力の場合は未解決として主張を保持 |
| HA | 5.1.3.2 | 元の証明にモデル圏の使用（直接、またはモデル圏についての補題への参照）がある。同じ全主張・全仮定のモデル圏なしKerodon証明は今回の対応表・原典検索では確認できなかった |
| HA | 7.1.2.13 | 元の証明にモデル圏の使用（直接、またはモデル圏についての補題への参照）がある。同じ全主張・全仮定のモデル圏なしKerodon証明は今回の対応表・原典検索では確認できなかった |
| HA | A.3.2 | 元の証明にモデル圏の使用（直接、またはモデル圏についての補題への参照）がある。同じ全主張・全仮定のモデル圏なしKerodon証明は今回の対応表・原典検索では確認できなかった |
| HTT | 2.1.1.4 | 元の証明にモデル圏の使用（直接、またはモデル圏についての補題への参照）がある。同じ全主張・全仮定のモデル圏なしKerodon証明は今回の対応表・原典検索では確認できなかった |
| HTT | 2.3.4.18 | 元の証明にモデル圏の使用（直接、またはモデル圏についての補題への参照）がある。同じ全主張・全仮定のモデル圏なしKerodon証明は今回の対応表・原典検索では確認できなかった |
| HTT | 3.2.2.12 | 元の証明にモデル圏の使用（直接、またはモデル圏についての補題への参照）がある。同じ全主張・全仮定のモデル圏なしKerodon証明は今回の対応表・原典検索では確認できなかった |
| HTT | 3.3.1.2 | 元の証明にモデル圏の使用（直接、またはモデル圏についての補題への参照）がある。同じ全主張・全仮定のモデル圏なしKerodon証明は今回の対応表・原典検索では確認できなかった |
| HTT | 3.3.1.5 | 元の証明にモデル圏の使用（直接、またはモデル圏についての補題への参照）がある。同じ全主張・全仮定のモデル圏なしKerodon証明は今回の対応表・原典検索では確認できなかった |
| HTT | 3.3.3.1 | 元の証明にモデル圏の使用（直接、またはモデル圏についての補題への参照）がある。同じ全主張・全仮定のモデル圏なしKerodon証明は今回の対応表・原典検索では確認できなかった |
| HTT | 3.3.4.5 | 元の証明にモデル圏の使用（直接、またはモデル圏についての補題への参照）がある。同じ全主張・全仮定のモデル圏なしKerodon証明は今回の対応表・原典検索では確認できなかった |
| HTT | 4.1.1.8 | 元の証明にモデル圏の使用（直接、またはモデル圏についての補題への参照）がある。同じ全主張・全仮定のモデル圏なしKerodon証明は今回の対応表・原典検索では確認できなかった |
| HTT | 4.1.2.7 | 元の証明にモデル圏の使用（直接、またはモデル圏についての補題への参照）がある。同じ全主張・全仮定のモデル圏なしKerodon証明は今回の対応表・原典検索では確認できなかった |
| HTT | 4.1.2.13 | 元の証明にモデル圏の使用（直接、またはモデル圏についての補題への参照）がある。同じ全主張・全仮定のモデル圏なしKerodon証明は今回の対応表・原典検索では確認できなかった |
| HTT | 4.1.2.14 | 元の証明にモデル圏の使用（直接、またはモデル圏についての補題への参照）がある。同じ全主張・全仮定のモデル圏なしKerodon証明は今回の対応表・原典検索では確認できなかった |
| HTT | 4.1.2.17 | 元の証明にモデル圏の使用（直接、またはモデル圏についての補題への参照）がある。同じ全主張・全仮定のモデル圏なしKerodon証明は今回の対応表・原典検索では確認できなかった |
| HTT | 4.2.2.4 | 元の証明にモデル圏の使用（直接、またはモデル圏についての補題への参照）がある。同じ全主張・全仮定のモデル圏なしKerodon証明は今回の対応表・原典検索では確認できなかった |
| HTT | 4.2.4.7 | 元の証明にモデル圏の使用（直接、またはモデル圏についての補題への参照）がある。同じ全主張・全仮定のモデル圏なしKerodon証明は今回の対応表・原典検索では確認できなかった |
| HTT | 4.3.1.7 | 元の証明にモデル圏の使用（直接、またはモデル圏についての補題への参照）がある。同じ全主張・全仮定のモデル圏なしKerodon証明は今回の対応表・原典検索では確認できなかった |
| HTT | 4.3.1.9 | 元の証明にモデル圏の使用（直接、またはモデル圏についての補題への参照）がある。同じ全主張・全仮定のモデル圏なしKerodon証明は今回の対応表・原典検索では確認できなかった |
| HTT | 4.3.2.7 | 元の証明にモデル圏の使用（直接、またはモデル圏についての補題への参照）がある。同じ全主張・全仮定のモデル圏なしKerodon証明は今回の対応表・原典検索では確認できなかった |
| HTT | 4.3.2.12 | 元の証明にモデル圏の使用（直接、またはモデル圏についての補題への参照）がある。同じ全主張・全仮定のモデル圏なしKerodon証明は今回の対応表・原典検索では確認できなかった |
| HTT | 4.3.3.10 | 元の証明にモデル圏の使用（直接、またはモデル圏についての補題への参照）がある。同じ全主張・全仮定のモデル圏なしKerodon証明は今回の対応表・原典検索では確認できなかった |
| HTT | 4.4.4.5 | 元の証明にモデル圏の使用（直接、またはモデル圏についての補題への参照）がある。同じ全主張・全仮定のモデル圏なしKerodon証明は今回の対応表・原典検索では確認できなかった |
| HTT | 5.1.3.1 | 候補Kerodon8.3.3.13（Tag03NJ）はlocally small∞圏が域。HTTは任意の単体集合K。一般Kからの移送・旧式Yoneda構成との比較をモデル圏なしに検収していない |
| HTT | 5.1.5.2 | 元の証明にモデル圏の使用（直接、またはモデル圏についての補題への参照）がある。同じ全主張・全仮定のモデル圏なしKerodon証明は今回の対応表・原典検索では確認できなかった |
| HTT | 5.2.1.3 | 元の証明にモデル圏の使用（直接、またはモデル圏についての補題への参照）がある。同じ全主張・全仮定のモデル圏なしKerodon証明は今回の対応表・原典検索では確認できなかった |
| HTT | 5.2.8.22 | 元の証明にモデル圏の使用（直接、またはモデル圏についての補題への参照）がある。同じ全主張・全仮定のモデル圏なしKerodon証明は今回の対応表・原典検索では確認できなかった |
| HTT | 5.3.3.3 | 元の証明にモデル圏の使用（直接、またはモデル圏についての補題への参照）がある。同じ全主張・全仮定のモデル圏なしKerodon証明は今回の対応表・原典検索では確認できなかった |
| HTT | 5.3.4.9 | 元の証明にモデル圏の使用（直接、またはモデル圏についての補題への参照）がある。同じ全主張・全仮定のモデル圏なしKerodon証明は今回の対応表・原典検索では確認できなかった |
| HTT | 5.3.4.10 | 元の証明にモデル圏の使用（直接、またはモデル圏についての補題への参照）がある。同じ全主張・全仮定のモデル圏なしKerodon証明は今回の対応表・原典検索では確認できなかった |
| HTT | 5.3.4.12 | 元の証明にモデル圏の使用（直接、またはモデル圏についての補題への参照）がある。同じ全主張・全仮定のモデル圏なしKerodon証明は今回の対応表・原典検索では確認できなかった |
| HTT | 5.3.4.14 | 元の証明にモデル圏の使用（直接、またはモデル圏についての補題への参照）がある。同じ全主張・全仮定のモデル圏なしKerodon証明は今回の対応表・原典検索では確認できなかった |
| HTT | 5.3.5.3 | 元の証明にモデル圏の使用（直接、またはモデル圏についての補題への参照）がある。同じ全主張・全仮定のモデル圏なしKerodon証明は今回の対応表・原典検索では確認できなかった |
| HTT | 5.4.1.2 | 元の証明にモデル圏の使用（直接、またはモデル圏についての補題への参照）がある。同じ全主張・全仮定のモデル圏なしKerodon証明は今回の対応表・原典検索では確認できなかった |
| HTT | 5.4.4.1 | 元の証明にモデル圏の使用（直接、またはモデル圏についての補題への参照）がある。同じ全主張・全仮定のモデル圏なしKerodon証明は今回の対応表・原典検索では確認できなかった |
| HTT | 5.4.5.7 | 候補Kerodon9.2.9.1（06F6）は(κ,λ)-compactness、µ-smallなdiagramのlimit。HTTのκ-filtered colimit・κ-compactnessとの全てのcardinal/universe条件の比較は未検収 |
| HTT | 5.4.5.13 | 候補Kerodon9.2.8.11（06N1）は(κ,λ)-compactness。HTTの全regular κでのκ-compactnessとの比較を未検収 |
| HTT | 5.5.2.7 | 元の証明にモデル圏の使用（直接、またはモデル圏についての補題への参照）がある。同じ全主張・全仮定のモデル圏なしKerodon証明は今回の対応表・原典検索では確認できなかった |
| HTT | 5.5.4.4 | 元の証明にモデル圏の使用（直接、またはモデル圏についての補題への参照）がある。同じ全主張・全仮定のモデル圏なしKerodon証明は今回の対応表・原典検索では確認できなかった |

HA 4.2.2.12 は Alg_LM と LMod_A の∞圏の同値という数学的主張であり、隣接するモデル圏での言い換えから「主張そのものがモデル圏」とする分類は修正した。HA 4.8.1.2 は Cat∞ の対称モノイダル構造の記法をモデル圏から導入する入力で、採用した主張側の経路があるため除外せず未解決として残した。後者の記法を内在的構成に置き換える入力の同定も未了である。

候補の一般性が不足する例：HTT 5.1.3.1 は任意の単体集合 K についてのYonedaで、Kerodon 8.3.3.13（Tag03NJ）はlocally smallな∞圏を域とする。この差を埋めるモデル圏なしの構成比較を検収していない。HTT 5.4.5.7・5.4.5.13 とKerodon 9.2.9.1（06F6）・9.2.8.11（06N1）は、(κ,λ)-compactnessと全regular κの仮定・universeの比較が未了なので置換済みとしない。

### モデル圏の単語だけでは除外しない

Kerodon 7.5.8.7・9.1.6.1・9.1.6.7 に現れる projectively cofibrant は、[Definition 7.5.6.1, Tag03C4](https://kerodon.net/tag/03C4) のlevelwise trivial Kan fibrationに対する持ち上げ性である。[Remark 7.5.6.6, Tag03CA](https://kerodon.net/tag/03CA) のisofibrancyによる直接議論も確認した。モデル構造の存在やModelCategoryのinstanceを仮定する記述ではないため、語の一致で付いていた未解決候補3件は解除した。これらの定義項目自体の追加は、上限後の依存展開になるため行っていない。

## 除外表の範囲

`excluded-model.csv` は、旧v1のDAG根からの経路について、モデル圏を使う原証明の辺を切ると到達しなくなり、かつ現在の2,000項目にもないことを確認した **387項目**。109項目は主張自体がモデル圏に関わるもの、278項目は切った原証明だけから届いていた補助項目である。各行の `cut_from` と `evidence_location` に最初に切れる証明の項目・位置と除外項目自身の位置を示す。後者の278項目の主張自体をモデル圏的と判定したわけではない。

旧1,014項目のうち530項目は現在も収録し、387項目は上の経路判定で除外した。残る **97項目は除外理由を認証できていない**。上限で未展開の経路、未解決の記法入力などから到達するかもしれず、除外表には入れていない。387項目の判定も、まだ展開していないNS・Kerodonから別の主張側の経路が見つかれば再検討する。この表は現時点の採用経路に対する判定であり、最終閉包からの永久除外を意味しない。

## 上限時点の未同定・暗黙入力

次は上限後の検収で記録した残件で、2,001項目目として追加していない。明示的な番号引用だけで全定義入力の照合も終わったとは報告しない。

- NS I.1.1 の HA §6.1.6 への節参照（NS PDF p.11、text L507）：preadditive/semiadditiveの記法は HA Definition 6.1.6.13（HA text L53740）に具体化すべき入力として同定したが、未収録。
- Kerodonの主張に反復する語の定義：1.4.0.1（003A、∞圏）、1.1.0.6（000H、単体集合）、1.2.5.1（002H、Kan complex）、5.1.4.1（01UA、Cartesian/coCartesian fibration）、5.1.1.1（01T5、Cartesian/coCartesian edge）、7.5.6.1（03C4、projectively cofibrant diagram）。これら6項目は現集合外。各使用箇所からの定義辺の確定・追加を再開時に行う。
- Kerodonの非項目タグ参照159出現について、既取得HTML内の式のidを含む項目へ戻した。自分自身の式への参照は119種類、別項目への式参照は既収録の行先への3辺として記録した（`kind=kerodon-equation-owner`）。残る4種類は所属項目が未確定。式のTagを新しい定理番号にして数えていない。

| 引用元Kerodon項目 | 未確定Tag | 残件 |
|---|---|---|
| 4.6.2.3 | [01HQ](https://kerodon.net/tag/01HQ) | 所属項目未確定（未取得または節・式タグ）。次回、番号つき項目へ戻す |
| 5.6.5.12 | [029S](https://kerodon.net/tag/029S) | 所属項目未確定（未取得または節・式タグ）。次回、番号つき項目へ戻す |
| 5.6.5.12 | [029T](https://kerodon.net/tag/029T) | 所属項目未確定（未取得または節・式タグ）。次回、番号つき項目へ戻す |
| 4.8.2.16 | [06SQ](https://kerodon.net/tag/06SQ) | 所属項目未確定（未取得または節・式タグ）。次回、番号つき項目へ戻す |

## 文献・章ごとの内訳

章は番号の最初の成分（HA/HTTの付録はA・B、NSはローマ数字）で集計する。実装状態の own・mathlib・partial・none は写していない。

| 文献 | 章 | 項目数 |
|---|---|---:|
| DAGXIII | 1 | 1 |
| DAGXIII | 2 | 26 |
| NS | A | 1 |
| NS | I | 16 |
| NS | II | 3 |
| NS | III | 3 |
| NS | IV | 2 |
| HA | 1 | 42 |
| HA | 2 | 60 |
| HA | 3 | 45 |
| HA | 4 | 83 |
| HA | 5 | 14 |
| HA | 6 | 8 |
| HA | 7 | 19 |
| HA | A | 4 |
| HTT | 1 | 13 |
| HTT | 2 | 42 |
| HTT | 3 | 27 |
| HTT | 4 | 59 |
| HTT | 5 | 129 |
| HTT | 6 | 1 |
| HTT | A | 2 |
| Kerodon | 1 | 99 |
| Kerodon | 2 | 16 |
| Kerodon | 3 | 176 |
| Kerodon | 4 | 412 |
| Kerodon | 5 | 250 |
| Kerodon | 6 | 35 |
| Kerodon | 7 | 222 |
| Kerodon | 8 | 96 |
| Kerodon | 9 | 94 |

<details>
<summary>節ごとの項目数</summary>

| 文献 | 節 | 項目数 |
|---|---|---:|
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
| HA | 6.1.6 | 8 |
| HA | 7.1 | 1 |
| HA | 7.1.1 | 1 |
| HA | 7.1.2 | 1 |
| HA | 7.1.3 | 6 |
| HA | 7.2.4 | 2 |
| HA | 7.3.2 | 6 |
| HA | 7.5 | 2 |
| HA | A.3 | 4 |
| HTT | 1.1.2 | 3 |
| HTT | 1.1.4 | 1 |
| HTT | 1.1.5 | 4 |
| HTT | 1.2.4 | 1 |
| HTT | 1.2.9 | 1 |
| HTT | 1.2.12 | 1 |
| HTT | 1.2.13 | 2 |
| HTT | 2.0.0 | 1 |
| HTT | 2.1.1 | 3 |
| HTT | 2.1.2 | 7 |
| HTT | 2.1.3 | 3 |
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
| HTT | 3.2.2 | 4 |
| HTT | 3.3.1 | 4 |
| HTT | 3.3.2 | 3 |
| HTT | 3.3.3 | 3 |
| HTT | 3.3.4 | 1 |
| HTT | 4.1.1 | 3 |
| HTT | 4.1.2 | 7 |
| HTT | 4.1.3 | 1 |
| HTT | 4.2.2 | 2 |
| HTT | 4.2.3 | 11 |
| HTT | 4.2.4 | 2 |
| HTT | 4.3.1 | 5 |
| HTT | 4.3.2 | 9 |
| HTT | 4.3.3 | 3 |
| HTT | 4.4.2 | 5 |
| HTT | 4.4.3 | 2 |
| HTT | 4.4.4 | 3 |
| HTT | 4.4.5 | 6 |
| HTT | 5.1.2 | 2 |
| HTT | 5.1.3 | 2 |
| HTT | 5.1.5 | 5 |
| HTT | 5.1.6 | 4 |
| HTT | 5.2.1 | 2 |
| HTT | 5.2.2 | 5 |
| HTT | 5.2.3 | 5 |
| HTT | 5.2.4 | 3 |
| HTT | 5.2.7 | 6 |
| HTT | 5.2.8 | 4 |
| HTT | 5.3.1 | 7 |
| HTT | 5.3.2 | 1 |
| HTT | 5.3.3 | 1 |
| HTT | 5.3.4 | 10 |
| HTT | 5.3.5 | 11 |
| HTT | 5.3.6 | 3 |
| HTT | 5.4.1 | 2 |
| HTT | 5.4.2 | 4 |
| HTT | 5.4.4 | 3 |
| HTT | 5.4.5 | 9 |
| HTT | 5.4.6 | 1 |
| HTT | 5.4.7 | 4 |
| HTT | 5.5.0 | 1 |
| HTT | 5.5.1 | 4 |
| HTT | 5.5.2 | 3 |
| HTT | 5.5.3 | 7 |
| HTT | 5.5.4 | 12 |
| HTT | 5.5.5 | 5 |
| HTT | 5.5.7 | 2 |
| HTT | 5.5.8 | 1 |
| HTT | 6.5.3 | 1 |
| HTT | A.1.2 | 1 |
| HTT | A.2.6 | 1 |
| Kerodon | 1.1.0 | 4 |
| Kerodon | 1.1.1 | 2 |
| Kerodon | 1.1.2 | 3 |
| Kerodon | 1.1.3 | 8 |
| Kerodon | 1.1.4 | 4 |
| Kerodon | 1.1.5 | 2 |
| Kerodon | 1.1.6 | 3 |
| Kerodon | 1.2.1 | 15 |
| Kerodon | 1.2.4 | 1 |
| Kerodon | 1.2.5 | 1 |
| Kerodon | 1.3.1 | 2 |
| Kerodon | 1.3.3 | 1 |
| Kerodon | 1.3.4 | 3 |
| Kerodon | 1.3.7 | 2 |
| Kerodon | 1.4.0 | 1 |
| Kerodon | 1.4.4 | 1 |
| Kerodon | 1.4.5 | 1 |
| Kerodon | 1.4.6 | 7 |
| Kerodon | 1.5.1 | 1 |
| Kerodon | 1.5.2 | 5 |
| Kerodon | 1.5.3 | 2 |
| Kerodon | 1.5.4 | 10 |
| Kerodon | 1.5.5 | 7 |
| Kerodon | 1.5.6 | 6 |
| Kerodon | 1.5.7 | 7 |
| Kerodon | 2.1.2 | 1 |
| Kerodon | 2.1.7 | 1 |
| Kerodon | 2.4.3 | 2 |
| Kerodon | 2.4.4 | 3 |
| Kerodon | 2.4.5 | 7 |
| Kerodon | 2.4.6 | 2 |
| Kerodon | 3.1.1 | 6 |
| Kerodon | 3.1.2 | 7 |
| Kerodon | 3.1.3 | 7 |
| Kerodon | 3.1.5 | 6 |
| Kerodon | 3.1.6 | 1 |
| Kerodon | 3.1.7 | 11 |
| Kerodon | 3.1.8 | 5 |
| Kerodon | 3.2.1 | 2 |
| Kerodon | 3.2.2 | 3 |
| Kerodon | 3.2.3 | 7 |
| Kerodon | 3.2.4 | 10 |
| Kerodon | 3.2.5 | 5 |
| Kerodon | 3.2.6 | 7 |
| Kerodon | 3.2.7 | 2 |
| Kerodon | 3.2.8 | 4 |
| Kerodon | 3.3.1 | 3 |
| Kerodon | 3.3.2 | 4 |
| Kerodon | 3.3.3 | 9 |
| Kerodon | 3.3.4 | 4 |
| Kerodon | 3.3.5 | 7 |
| Kerodon | 3.3.6 | 9 |
| Kerodon | 3.3.7 | 7 |
| Kerodon | 3.4.0 | 4 |
| Kerodon | 3.4.1 | 10 |
| Kerodon | 3.5.1 | 13 |
| Kerodon | 3.5.2 | 2 |
| Kerodon | 3.5.3 | 2 |
| Kerodon | 3.5.7 | 4 |
| Kerodon | 3.5.9 | 6 |
| Kerodon | 3.6.1 | 9 |
| Kerodon | 4.1.1 | 9 |
| Kerodon | 4.1.2 | 8 |
| Kerodon | 4.1.3 | 3 |
| Kerodon | 4.1.4 | 5 |
| Kerodon | 4.2.1 | 5 |
| Kerodon | 4.2.4 | 7 |
| Kerodon | 4.2.5 | 4 |
| Kerodon | 4.2.6 | 3 |
| Kerodon | 4.3.2 | 2 |
| Kerodon | 4.3.3 | 10 |
| Kerodon | 4.3.6 | 13 |
| Kerodon | 4.3.7 | 7 |
| Kerodon | 4.4.1 | 10 |
| Kerodon | 4.4.2 | 13 |
| Kerodon | 4.4.3 | 16 |
| Kerodon | 4.4.4 | 5 |
| Kerodon | 4.4.5 | 10 |
| Kerodon | 4.5.1 | 12 |
| Kerodon | 4.5.2 | 4 |
| Kerodon | 4.5.3 | 22 |
| Kerodon | 4.5.4 | 13 |
| Kerodon | 4.5.5 | 10 |
| Kerodon | 4.5.6 | 12 |
| Kerodon | 4.5.7 | 12 |
| Kerodon | 4.5.8 | 5 |
| Kerodon | 4.6.1 | 10 |
| Kerodon | 4.6.2 | 9 |
| Kerodon | 4.6.3 | 5 |
| Kerodon | 4.6.4 | 14 |
| Kerodon | 4.6.5 | 5 |
| Kerodon | 4.6.6 | 3 |
| Kerodon | 4.6.7 | 8 |
| Kerodon | 4.6.8 | 12 |
| Kerodon | 4.7.1 | 6 |
| Kerodon | 4.7.2 | 3 |
| Kerodon | 4.7.3 | 11 |
| Kerodon | 4.7.6 | 7 |
| Kerodon | 4.8.1 | 5 |
| Kerodon | 4.8.2 | 23 |
| Kerodon | 4.8.3 | 11 |
| Kerodon | 4.8.4 | 6 |
| Kerodon | 4.8.5 | 3 |
| Kerodon | 4.8.8 | 7 |
| Kerodon | 4.9.1 | 12 |
| Kerodon | 4.9.2 | 3 |
| Kerodon | 4.9.3 | 6 |
| Kerodon | 4.9.4 | 12 |
| Kerodon | 4.9.5 | 8 |
| Kerodon | 4.9.8 | 3 |
| Kerodon | 5.1.1 | 12 |
| Kerodon | 5.1.2 | 5 |
| Kerodon | 5.1.3 | 9 |
| Kerodon | 5.1.4 | 12 |
| Kerodon | 5.1.5 | 1 |
| Kerodon | 5.1.6 | 7 |
| Kerodon | 5.1.7 | 10 |
| Kerodon | 5.2.1 | 3 |
| Kerodon | 5.2.2 | 8 |
| Kerodon | 5.2.3 | 10 |
| Kerodon | 5.2.4 | 3 |
| Kerodon | 5.2.5 | 3 |
| Kerodon | 5.2.8 | 9 |
| Kerodon | 5.3.1 | 1 |
| Kerodon | 5.3.2 | 9 |
| Kerodon | 5.3.3 | 13 |
| Kerodon | 5.3.4 | 14 |
| Kerodon | 5.3.5 | 6 |
| Kerodon | 5.3.6 | 8 |
| Kerodon | 5.3.7 | 5 |
| Kerodon | 5.3.8 | 4 |
| Kerodon | 5.4.1 | 1 |
| Kerodon | 5.4.2 | 5 |
| Kerodon | 5.4.3 | 4 |
| Kerodon | 5.4.4 | 2 |
| Kerodon | 5.4.5 | 7 |
| Kerodon | 5.4.6 | 4 |
| Kerodon | 5.4.7 | 4 |
| Kerodon | 5.4.8 | 5 |
| Kerodon | 5.4.9 | 1 |
| Kerodon | 5.5.3 | 6 |
| Kerodon | 5.5.4 | 1 |
| Kerodon | 5.5.5 | 4 |
| Kerodon | 5.6.0 | 2 |
| Kerodon | 5.6.2 | 9 |
| Kerodon | 5.6.4 | 4 |
| Kerodon | 5.6.5 | 9 |
| Kerodon | 5.6.6 | 14 |
| Kerodon | 5.6.7 | 7 |
| Kerodon | 5.6.8 | 7 |
| Kerodon | 5.6.9 | 2 |
| Kerodon | 6.1.2 | 1 |
| Kerodon | 6.2.1 | 3 |
| Kerodon | 6.2.2 | 1 |
| Kerodon | 6.2.5 | 1 |
| Kerodon | 6.2.6 | 2 |
| Kerodon | 6.3.1 | 12 |
| Kerodon | 6.3.2 | 4 |
| Kerodon | 6.3.4 | 4 |
| Kerodon | 6.3.5 | 6 |
| Kerodon | 6.3.6 | 1 |
| Kerodon | 7.1.0 | 1 |
| Kerodon | 7.1.1 | 9 |
| Kerodon | 7.1.2 | 7 |
| Kerodon | 7.1.3 | 8 |
| Kerodon | 7.1.4 | 6 |
| Kerodon | 7.1.5 | 7 |
| Kerodon | 7.1.6 | 14 |
| Kerodon | 7.1.7 | 5 |
| Kerodon | 7.1.8 | 10 |
| Kerodon | 7.1.9 | 8 |
| Kerodon | 7.2.1 | 14 |
| Kerodon | 7.2.2 | 9 |
| Kerodon | 7.2.3 | 7 |
| Kerodon | 7.3.1 | 9 |
| Kerodon | 7.3.2 | 4 |
| Kerodon | 7.3.3 | 6 |
| Kerodon | 7.3.4 | 2 |
| Kerodon | 7.3.5 | 3 |
| Kerodon | 7.3.6 | 10 |
| Kerodon | 7.3.8 | 11 |
| Kerodon | 7.4.1 | 8 |
| Kerodon | 7.4.2 | 2 |
| Kerodon | 7.4.3 | 7 |
| Kerodon | 7.4.4 | 6 |
| Kerodon | 7.4.5 | 10 |
| Kerodon | 7.4.6 | 3 |
| Kerodon | 7.5.2 | 2 |
| Kerodon | 7.5.4 | 5 |
| Kerodon | 7.5.5 | 6 |
| Kerodon | 7.5.6 | 1 |
| Kerodon | 7.5.7 | 1 |
| Kerodon | 7.5.8 | 5 |
| Kerodon | 7.6.2 | 3 |
| Kerodon | 7.6.3 | 2 |
| Kerodon | 7.6.6 | 6 |
| Kerodon | 7.7.0 | 3 |
| Kerodon | 7.7.7 | 2 |
| Kerodon | 8.1.1 | 3 |
| Kerodon | 8.1.2 | 3 |
| Kerodon | 8.2.0 | 2 |
| Kerodon | 8.2.1 | 2 |
| Kerodon | 8.2.2 | 3 |
| Kerodon | 8.2.3 | 7 |
| Kerodon | 8.2.4 | 3 |
| Kerodon | 8.2.6 | 2 |
| Kerodon | 8.3.1 | 3 |
| Kerodon | 8.3.2 | 7 |
| Kerodon | 8.3.3 | 9 |
| Kerodon | 8.3.4 | 6 |
| Kerodon | 8.3.5 | 2 |
| Kerodon | 8.3.7 | 6 |
| Kerodon | 8.4.1 | 6 |
| Kerodon | 8.4.2 | 6 |
| Kerodon | 8.4.3 | 3 |
| Kerodon | 8.4.6 | 7 |
| Kerodon | 8.5.1 | 5 |
| Kerodon | 8.5.2 | 2 |
| Kerodon | 8.5.5 | 2 |
| Kerodon | 8.5.6 | 3 |
| Kerodon | 8.6.5 | 1 |
| Kerodon | 8.6.6 | 2 |
| Kerodon | 8.6.8 | 1 |
| Kerodon | 9.1.1 | 8 |
| Kerodon | 9.1.3 | 10 |
| Kerodon | 9.1.4 | 10 |
| Kerodon | 9.1.5 | 8 |
| Kerodon | 9.1.6 | 5 |
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
| Kerodon | 9.4.9 | 4 |
| Kerodon | 9.5.4 | 3 |

</details>

## 原典と採取位置

PDFは以下の版の項目本文・証明を使用した。`edges.csv` の `PDF p.` は物理ページ、`text L` は当該PDFの `pdftotext -layout` 出力の1始まりの行。前の節閉包の引用元位置訂正を反映した辺は、元の位置付き引用として保持した。

| 文献 | 版・原典 | PDF SHA256 |
|---|---|---|
| DAGXIII | [2011-12-15](https://www.math.ias.edu/~lurie/papers/DAG-XIII.pdf) | `75a4d6d9e5e22c8f1261a09e499c6668ceacb90d6cfaf4a2de4a10e2fe0cd535` |
| NS | [arXiv:1707.01799v2](https://arxiv.org/abs/1707.01799v2) | `12b6cdbd0d8ebb506284bd13f183affe80e41cc8890fef5fa21c922c2f80cec3` |
| HA | [2017-09-18](https://www.math.ias.edu/~lurie/papers/HA.pdf) | `112b145a95a62daefb8275851cac9ab6430004cfc8f751a33a8d981fd7ad68c3` |
| HTT | [2017-04-09](https://www.math.ias.edu/~lurie/papers/HTT.pdf) | `58855f3a0ad6d9c470ded74a38938b9468927592e9ae1209bab6a068e67ede6e` |

番号・種類は既存の各文献目録のメタデータを使用し、実装状態の判定は読取り結果へ転記していない。Kerodonは `research/kerodon-coverage/item-tags.csv` の番号・種類・Tagを用い、主張と付随する証明のHTML article内の引用を採取した。ナビゲーションや節導入の文章を出辺としていない。到達した項目に対応する取得済みHTMLと目録の番号・種類の不一致は0件。

Kerodonの一括PDFは検索の手掛かりだけに使用した。Tag02QEは一括PDFでは10.1.1.1、現在のTagページと既存目録では9.7.2.1であり、PDFの番号を現在の表に流用しなかった。これはPDFとHTMLの版の差で、既存対応表への修正は行っていない。HA/HTTの対応候補も、原典の全仮定・結論が一致しなければproofの置換とは数えない。

2026-11-16の採取で本文を参照したKerodonページは1246件。取得件数と収録1,400項目は異なり、上限時点では未取得・未展開の項目がある。`Tag number HTML-SHA256\n` をTag順に並べた採取記録のSHA256は `c8d7d832d52ca50e0c268528c09ea9a3961b2791dca50442b461ca3034cdb9f6`。原典本文やPDFをリポジトリへ複製していない。差替え5辺の行先のHTML指紋は次のとおり。

| Tag | HTML SHA256 |
|---|---|
| 02NY | `cce877039dc88795d1bd4a481b44ecd5afb446c0bd1907c3dfaefd75ef0aebb1` |
| 029H | `154a41a8716011d9e6c5d061c70c4c472751c0c48119e48d1d7d9c31b8fabb5b` |
| 06LP | `a1a206554a045c0ab11c0a24b8cf2a60097dcfd78c783ac5d423096c3e0ca51f` |
| 06PA | `ff112ea7178a0ecd1c776011c7f3220a989f698a42fd10620165ff9af3ab61cb` |
| 06AJ | `9b56e420d5e8bbfe7b9ed99d74c535e886ac87515d8d716b74da05de34f896f8` |

## 小さい検収

CSVの列・一意な項目キー2,000件・13根・辺の両端・根からの到達・到達元分類・差替え5辺／元4項目・未解決51項目の保持・除外表との非交差・章別総和・依存順を検査した。v1の3ファイルは基準mainの旧版とバイト一致を確認した。既存の対応表・地図・Leanファイルを変更せず、Leanの追加・ビルドは行っていない。

## 依存の順（現在の採用辺による強連結成分）

辺は「使う項目 → 前提」。強連結成分を縮約したDAGで前提を先に並べた。1771成分、うち複数項目を含むもの21成分。相互に参照する成分内には線形の証明順を主張しない。未解決証明の辺や未展開の辺を追加すると、この順序も変わる。

1. HTT 1.1.2.1
2. HTT 1.1.2.2
3. HTT 1.1.2.4
4. DAGXIII 1.1.5
5. DAGXIII 2.1.1
6. DAGXIII 2.1.2
7. DAGXIII 2.1.3
8. DAGXIII 2.1.4
9. DAGXIII 2.1.5
10. DAGXIII 2.1.6
11. DAGXIII 2.1.7
12. DAGXIII 2.1.9
13. HTT 1.2.12.9
14. HA 1.1.1.1
15. DAGXIII 2.1.10
16. DAGXIII 2.1.11
17. DAGXIII 2.1.12
18. DAGXIII 2.1.14
19. HA 1.1.2.1
20. DAGXIII 2.1.15
21. HA 1.1.1.9
22. HTT 2.0.0.3
23. HTT 2.1.2.9
24. HTT 2.1.2.5
25. HTT 5.2.3.1
26. HTT 2.4.1.1
27. HTT 2.4.2.1
28. HTT 2.1.1.4
29. HTT A.1.2.2
30. HTT 2.1.2.6
31. HTT 2.4.1.6
32. HTT 2.4.1.8
33. HTT 5.2.3.2
34. HTT 5.2.3.3
35. HTT 5.2.3.4
36. HTT 5.2.3.5
37. HA 1.1.1.8
38. HTT 1.2.13.4
39. HTT 2.4.4.2
40. HTT 2.4.4.7
41. HTT 2.4.4.8
42. HTT 2.4.4.9
43. HTT 4.2.2.7
44. HTT 2.1.1.5
45. HTT 2.1.1.6
46. HTT 1.1.4.1
47. HTT 1.1.5.14
48. HTT 2.4.4.4
49. HTT 2.4.4.5
50. HTT 2.1.3.2
51. HTT 2.1.3.3
52. HTT 2.1.2.3
53. HTT 2.1.2.4
54. HTT 1.2.4.3; HTT 1.2.9.3; HTT 2.1.2.1; HTT 2.1.2.2; HTT 2.4.5.1 （相互参照）
55. HTT 2.1.3.4
56. HTT 3.1.1.1
57. HTT 2.4.1.7
58. HTT 3.1.1.6
59. HTT 3.1.1.10
60. HTT 3.1.1.4
61. HTT 3.1.1.5
62. HTT 3.1.1.7
63. HTT 3.1.2.3
64. HTT 3.1.2.1
65. HTT 3.1.3.2
66. HTT 3.1.3.3
67. HTT 3.3.1.5
68. HTT 4.2.2.4
69. HTT 5.1.2.1
70. HTT 5.1.2.2
71. HA 1.1.2.9
72. DAGXIII 2.1.16
73. DAGXIII 2.1.17
74. DAGXIII 2.1.18
75. DAGXIII 2.1.21
76. DAGXIII 2.1.23
77. DAGXIII 2.1.25
78. HA 2.0.0.2
79. HA 2.0.0.3
80. HA 2.0.0.7
81. HA 2.1.1.8
82. HA 2.1.1.10
83. HA 2.1.2.10
84. HA 2.1.3.1
85. HA 4.1.1.10
86. HA 2.4.2.4
87. HA 2.4.1.3
88. HTT 3.2.2.12
89. HTT 3.2.2.13
90. HTT 4.3.2.15
91. HA 2.4.1.5
92. HA 2.4.1.7
93. HA 2.4.1.8
94. HA 2.4.1.9
95. HA 2.4.2.5
96. HA 2.4.2.6
97. DAGXIII 2.2.1
98. DAGXIII 2.2.2
99. DAGXIII 2.2.3
100. HA 3.3.1.9
101. HA 3.4.1.10
102. HTT 3.2.2.7
103. HTT 4.1.1.1
104. HTT 4.1.1.3
105. HTT 4.1.2.15
106. Kerodon 4.1.1.2
107. Kerodon 4.1.1.8
108. Kerodon 4.1.1.9
109. Kerodon 3.1.3.6
110. Kerodon 3.1.7.6
111. Kerodon 1.5.4.5
112. Kerodon 1.5.4.9
113. Kerodon 1.5.4.10
114. Kerodon 1.5.4.12
115. Kerodon 1.5.4.14
116. Kerodon 1.5.5.1
117. Kerodon 1.1.4.1
118. Kerodon 1.1.3.8
119. Kerodon 1.1.4.12
120. Kerodon 1.5.4.8
121. Kerodon 1.5.4.4
122. Kerodon 1.5.4.7
123. Kerodon 1.5.4.13
124. Kerodon 1.5.4.15
125. Kerodon 4.9.1.34
126. Kerodon 1.5.5.14
127. Kerodon 1.5.5.4
128. Kerodon 1.5.5.5
129. Kerodon 3.1.7.10
130. Kerodon 3.1.7.14
131. Kerodon 3.1.8.1
132. Kerodon 4.1.3.2
133. Kerodon 3.1.2.10
134. Kerodon 3.1.2.11
135. Kerodon 3.1.2.12
136. Kerodon 3.1.2.9
137. Kerodon 4.2.5.3
138. Kerodon 4.2.1.4
139. Kerodon 4.1.3.1
140. Kerodon 4.2.4.5
141. Kerodon 4.3.3.16
142. Kerodon 4.3.3.17
143. Kerodon 4.3.3.18
144. Kerodon 4.3.6.3
145. Kerodon 4.2.4.2
146. Kerodon 4.3.2.1
147. Kerodon 4.3.3.7
148. Kerodon 4.3.3.14
149. Kerodon 4.3.6.16
150. Kerodon 4.3.6.4
151. Kerodon 4.3.6.8
152. Kerodon 4.3.6.12
153. Kerodon 4.3.6.1
154. Kerodon 4.5.4.4
155. Kerodon 4.6.4.1
156. Kerodon 1.4.6.1
157. Kerodon 4.6.4.20
158. Kerodon 3.1.1.2
159. Kerodon 3.1.1.10
160. Kerodon 3.1.1.11
161. Kerodon 3.1.7.13
162. Kerodon 3.1.3.3
163. Kerodon 3.1.2.3
164. Kerodon 3.1.7.16
165. Kerodon 3.3.7.5
166. Kerodon 3.1.1.1
167. Kerodon 3.1.2.7
168. Kerodon 3.1.3.1
169. Kerodon 4.2.1.5
170. Kerodon 4.2.5.1
171. Kerodon 4.2.5.4
172. Kerodon 4.2.6.1
173. Kerodon 4.2.6.2
174. Kerodon 3.1.5.3
175. Kerodon 1.1.3.6
176. Kerodon 1.1.0.14
177. Kerodon 1.2.1.1
178. Kerodon 1.2.1.6
179. Kerodon 1.2.1.8
180. Kerodon 3.1.5.1
181. Kerodon 3.1.7.1
182. Kerodon 3.2.4.1
183. Kerodon 3.2.4.8
184. Kerodon 3.2.4.12
185. Kerodon 1.1.1.7
186. Kerodon 1.1.4.13
187. Kerodon 1.2.4.7
188. Kerodon 3.2.3.4
189. Kerodon 3.2.3.5
190. Kerodon 3.2.3.6
191. Kerodon 3.2.3.7
192. Kerodon 3.2.3.8
193. Kerodon 3.2.3.9
194. Kerodon 3.2.2.10
195. Kerodon 3.2.4.10
196. Kerodon 3.2.4.11
197. Kerodon 3.2.4.13
198. Kerodon 3.2.4.14
199. Kerodon 3.5.1.12
200. Kerodon 3.2.6.3
201. Kerodon 3.2.6.8
202. Kerodon 3.2.6.9
203. Kerodon 3.3.6.2
204. Kerodon 3.2.5.1
205. Kerodon 3.2.5.2
206. Kerodon 3.2.5.5
207. Kerodon 1.1.5.2
208. Kerodon 1.2.1.7
209. Kerodon 1.2.1.3
210. Kerodon 1.2.1.4
211. Kerodon 1.2.1.5
212. Kerodon 1.2.1.11
213. Kerodon 1.2.1.13
214. Kerodon 1.2.1.18
215. Kerodon 1.2.1.10
216. Kerodon 1.2.1.12
217. Kerodon 1.2.1.19
218. Kerodon 1.2.1.22
219. Kerodon 1.2.1.23
220. Kerodon 1.2.5.10
221. Kerodon 1.4.6.13
222. Kerodon 3.2.3.1
223. Kerodon 3.2.5.4
224. Kerodon 3.2.5.3
225. Kerodon 3.2.6.4
226. Kerodon 3.2.6.5
227. Kerodon 3.2.6.6
228. Kerodon 3.2.6.7
229. Kerodon 1.1.5.10
230. Kerodon 3.3.4.6
231. Kerodon 3.3.6.3
232. Kerodon 3.3.2.7
233. Kerodon 3.3.6.4
234. Kerodon 3.3.6.5
235. Kerodon 3.1.1.8
236. Kerodon 3.3.1.5
237. Kerodon 3.3.1.7
238. Kerodon 3.3.1.8
239. Kerodon 1.1.3.9
240. Kerodon 3.3.3.10
241. Kerodon 3.3.3.11
242. Kerodon 3.3.3.13
243. Kerodon 3.3.3.19
244. Kerodon 3.3.3.17
245. Kerodon 3.3.5.9
246. Kerodon 3.3.5.3
247. Kerodon 3.3.5.4
248. Kerodon 3.3.6.6
249. Kerodon 3.2.1.14
250. Kerodon 3.2.1.13
251. Kerodon 3.2.2.16
252. Kerodon 3.2.2.17
253. Kerodon 3.2.4.3
254. Kerodon 3.2.7.2
255. Kerodon 3.2.8.3
256. Kerodon 3.3.2.2
257. Kerodon 3.3.2.5
258. Kerodon 3.3.3.1
259. Kerodon 3.3.4.2
260. Kerodon 3.3.4.3
261. Kerodon 3.3.4.8
262. Kerodon 3.3.5.6
263. Kerodon 3.3.5.7
264. Kerodon 3.3.3.18
265. Kerodon 3.3.5.8
266. Kerodon 3.3.5.1
267. Kerodon 3.3.6.7
268. Kerodon 3.3.6.8
269. Kerodon 3.3.2.1
270. Kerodon 3.3.6.9
271. Kerodon 3.5.1.1
272. Kerodon 3.5.1.5
273. Kerodon 3.5.1.13
274. Kerodon 3.5.1.14
275. Kerodon 3.5.1.15
276. Kerodon 3.1.8.10; Kerodon 3.2.7.1; Kerodon 3.2.8.1; Kerodon 3.3.7.1; Kerodon 3.3.7.6; Kerodon 3.3.7.7; Kerodon 3.5.1.22; Kerodon 3.5.2.1 （相互参照）
277. Kerodon 3.5.9.2
278. Kerodon 4.7.2.5
279. Kerodon 3.4.0.2
280. Kerodon 3.4.0.7
281. Kerodon 3.4.0.9
282. Kerodon 3.5.7.1
283. Kerodon 3.5.9.1
284. Kerodon 3.5.9.8
285. Kerodon 3.4.1.2
286. Kerodon 3.4.1.4
287. Kerodon 3.5.7.8
288. Kerodon 3.3.7.2
289. Kerodon 3.3.7.3
290. Kerodon 3.5.9.9
291. Kerodon 3.5.9.11
292. Kerodon 3.5.9.12
293. Kerodon 1.4.6.6
294. Kerodon 4.4.2.11
295. Kerodon 1.5.1.6
296. Kerodon 4.2.1.11
297. Kerodon 4.3.6.13
298. Kerodon 4.3.6.14
299. Kerodon 3.4.1.11
300. Kerodon 5.1.1.13
301. Kerodon 3.4.1.5
302. Kerodon 3.3.7.4
303. Kerodon 3.4.1.9
304. Kerodon 3.4.1.10; Kerodon 3.4.1.13 （相互参照）
305. Kerodon 1.4.6.7
306. Kerodon 1.4.6.8
307. Kerodon 1.4.6.10
308. Kerodon 4.6.2.3
309. Kerodon 4.6.4.11
310. Kerodon 4.6.4.15
311. Kerodon 4.6.5.7
312. Kerodon 3.1.3.4
313. Kerodon 3.1.5.4
314. Kerodon 3.1.5.10
315. Kerodon 4.5.1.1
316. Kerodon 4.5.1.4
317. Kerodon 3.1.7.5
318. Kerodon 4.5.1.16
319. Kerodon 4.5.1.6
320. Kerodon 4.4.3.1
321. Kerodon 4.4.3.5
322. Kerodon 4.4.4.5
323. Kerodon 4.5.1.7
324. Kerodon 4.5.1.19
325. Kerodon 4.5.1.22
326. Kerodon 3.4.1.6
327. Kerodon 4.4.4.7
328. Kerodon 3.4.1.3
329. Kerodon 4.1.1.5
330. Kerodon 4.1.1.1
331. Kerodon 4.4.1.4
332. Kerodon 1.4.6.3
333. Kerodon 4.1.1.3
334. Kerodon 4.4.1.3
335. Kerodon 4.4.1.1
336. Kerodon 4.4.1.7
337. Kerodon 4.4.1.8
338. Kerodon 4.4.3.17
339. Kerodon 1.5.5.6
340. Kerodon 1.5.5.7
341. Kerodon 1.5.6.7
342. Kerodon 1.5.6.9
343. Kerodon 1.5.6.1
344. Kerodon 1.5.3.7
345. Kerodon 1.5.7.5
346. Kerodon 4.1.4.1
347. Kerodon 4.1.4.2
348. Kerodon 4.5.3.28
349. Kerodon 4.5.4.8
350. Kerodon 1.5.7.6
351. Kerodon 4.5.1.10
352. Kerodon 4.5.4.1
353. Kerodon 4.5.4.3
354. Kerodon 4.5.5.9
355. Kerodon 4.5.4.7
356. Kerodon 4.5.5.8
357. Kerodon 4.5.5.10
358. Kerodon 4.5.5.12
359. Kerodon 4.5.5.13
360. Kerodon 3.6.1.8
361. Kerodon 4.5.4.5
362. Kerodon 4.6.2.4
363. Kerodon 4.6.2.7
364. Kerodon 4.4.1.14
365. Kerodon 4.5.3.1
366. Kerodon 4.8.2.13
367. Kerodon 4.5.1.13
368. Kerodon 4.6.1.10
369. Kerodon 4.8.1.7
370. Kerodon 4.8.2.14
371. Kerodon 4.4.5.10
372. Kerodon 4.8.2.1
373. Kerodon 4.8.3.1
374. Kerodon 4.8.3.8
375. Kerodon 4.8.3.9
376. Kerodon 4.8.3.16
377. Kerodon 4.2.6.3
378. Kerodon 4.7.1.2
379. Kerodon 3.1.8.12
380. Kerodon 3.5.1.10
381. Kerodon 3.5.1.17
382. Kerodon 3.5.2.2
383. Kerodon 3.5.7.20
384. Kerodon 3.5.3.17
385. Kerodon 3.5.3.18
386. Kerodon 4.7.6.17
387. Kerodon 4.7.6.18
388. Kerodon 4.7.6.19
389. Kerodon 4.8.1.6
390. Kerodon 4.4.3.10
391. Kerodon 4.4.5.11
392. Kerodon 4.6.1.13
393. Kerodon 4.8.1.4
394. Kerodon 4.8.2.6
395. Kerodon 4.8.2.7
396. Kerodon 4.8.2.19
397. Kerodon 4.8.2.20
398. Kerodon 4.8.2.21
399. Kerodon 4.8.2.22
400. Kerodon 4.1.3.3
401. Kerodon 4.8.2.12
402. Kerodon 4.8.5.11
403. Kerodon 4.8.8.10
404. Kerodon 4.6.8.5
405. Kerodon 5.1.1.14
406. Kerodon 3.1.8.11
407. Kerodon 1.5.6.4
408. Kerodon 1.5.7.3
409. Kerodon 1.3.7.5
410. Kerodon 1.5.6.8
411. Kerodon 1.1.0.9
412. Kerodon 1.3.7.2
413. Kerodon 1.5.7.1
414. Kerodon 1.5.7.7
415. Kerodon 1.3.1.4
416. Kerodon 1.3.1.3; Kerodon 1.3.3.1; Kerodon 1.5.7.4; Kerodon 1.5.7.8 （相互参照）
417. Kerodon 1.1.3.1
418. Kerodon 1.3.4.1; Kerodon 1.3.4.2; Kerodon 1.3.4.3 （相互参照）
419. Kerodon 4.1.1.10
420. Kerodon 4.4.1.6
421. Kerodon 4.5.1.20
422. Kerodon 4.5.6.10
423. Kerodon 4.1.1.13
424. Kerodon 5.1.3.4
425. Kerodon 5.1.3.5
426. Kerodon 5.1.1.12
427. Kerodon 1.5.2.4
428. Kerodon 1.1.2.6
429. Kerodon 1.1.3.2
430. Kerodon 1.1.3.3
431. Kerodon 1.1.3.4
432. Kerodon 1.1.3.11
433. Kerodon 1.1.6.8
434. Kerodon 1.1.6.9
435. Kerodon 1.1.6.10
436. Kerodon 1.5.2.5
437. Kerodon 1.5.2.6
438. Kerodon 1.5.2.8
439. Kerodon 1.5.2.10
440. Kerodon 4.8.1.10
441. Kerodon 4.8.3.19
442. Kerodon 4.8.2.29
443. Kerodon 4.8.2.5
444. Kerodon 4.4.2.7
445. Kerodon 4.8.3.5
446. Kerodon 4.8.3.38
447. Kerodon 4.6.1.16
448. Kerodon 4.6.1.18
449. Kerodon 4.6.8.1
450. Kerodon 4.1.4.4
451. Kerodon 4.6.8.4
452. Kerodon 5.1.3.10
453. Kerodon 4.6.8.9
454. Kerodon 1.4.4.1
455. Kerodon 4.6.8.10
456. Kerodon 4.6.8.15
457. Kerodon 5.1.7.4
458. Kerodon 4.1.1.6
459. Kerodon 2.4.5.10
460. Kerodon 2.4.5.11
461. Kerodon 2.4.5.12
462. Kerodon 2.4.5.1
463. Kerodon 5.5.3.1
464. Kerodon 4.5.4.6
465. Kerodon 5.3.4.9
466. Kerodon 5.3.2.1
467. Kerodon 5.3.2.3
468. Kerodon 5.3.2.2
469. Kerodon 5.3.2.4
470. Kerodon 5.3.2.7
471. Kerodon 5.3.2.8
472. Kerodon 5.3.2.12
473. Kerodon 5.3.6.3
474. Kerodon 1.1.4.4
475. Kerodon 4.5.1.17
476. Kerodon 4.5.4.10
477. Kerodon 4.8.2.11
478. Kerodon 4.8.5.10
479. Kerodon 4.8.8.9
480. Kerodon 4.3.6.5
481. Kerodon 4.3.2.5
482. Kerodon 4.3.3.27
483. Kerodon 4.3.3.28
484. Kerodon 4.3.7.8
485. Kerodon 4.5.4.9
486. Kerodon 4.5.5.1
487. Kerodon 5.2.3.14
488. Kerodon 4.3.3.24
489. Kerodon 5.2.3.12
490. Kerodon 5.2.3.13
491. Kerodon 5.2.3.16
492. Kerodon 5.2.3.4
493. Kerodon 5.2.3.9
494. Kerodon 5.3.1.5
495. Kerodon 5.3.4.7
496. Kerodon 5.3.4.6
497. Kerodon 5.3.3.3
498. Kerodon 5.3.3.4
499. Kerodon 5.3.3.2
500. Kerodon 5.3.3.7
501. Kerodon 4.3.3.23
502. Kerodon 5.2.3.1
503. Kerodon 5.3.3.9
504. Kerodon 5.3.3.10
505. Kerodon 5.3.3.12
506. Kerodon 5.3.4.2
507. Kerodon 5.3.4.11
508. Kerodon 5.3.3.1
509. Kerodon 5.3.4.12
510. Kerodon 5.3.3.8
511. Kerodon 5.3.4.13
512. Kerodon 5.3.4.14
513. Kerodon 5.3.4.15
514. Kerodon 4.5.7.3
515. Kerodon 4.5.7.8
516. Kerodon 4.5.7.16
517. Kerodon 4.5.7.17
518. Kerodon 4.1.2.2
519. Kerodon 1.4.5.4
520. Kerodon 4.1.2.10
521. Kerodon 4.1.2.11
522. Kerodon 4.1.2.4
523. Kerodon 4.1.2.6
524. Kerodon 4.4.1.12
525. Kerodon 4.4.3.2
526. Kerodon 4.4.3.6
527. Kerodon 4.1.4.3
528. Kerodon 5.2.5.5
529. Kerodon 4.1.2.16
530. Kerodon 4.1.2.17
531. Kerodon 5.2.1.3
532. Kerodon 5.2.2.10
533. Kerodon 4.4.2.9
534. Kerodon 5.2.2.4
535. Kerodon 5.2.2.12
536. Kerodon 2.1.2.17
537. Kerodon 2.1.7.1
538. Kerodon 4.6.1.1
539. Kerodon 1.1.1.4
540. Kerodon 1.1.2.1
541. Kerodon 4.6.8.11
542. Kerodon 4.6.8.12
543. Kerodon 4.6.8.13
544. Kerodon 2.4.3.1
545. Kerodon 2.4.4.15
546. Kerodon 4.6.5.1
547. Kerodon 4.6.5.2
548. Kerodon 4.6.7.3
549. Kerodon 4.6.7.22
550. Kerodon 4.6.7.23
551. Kerodon 4.6.7.25
552. Kerodon 4.6.7.26
553. Kerodon 4.6.7.8
554. Kerodon 5.1.3.3
555. Kerodon 5.1.1.10
556. Kerodon 5.4.2.1
557. Kerodon 5.4.2.2
558. Kerodon 5.4.7.1
559. Kerodon 5.4.2.4
560. Kerodon 5.4.3.8
561. Kerodon 5.4.8.7
562. Kerodon 2.4.6.9
563. Kerodon 3.1.5.12
564. Kerodon 4.6.8.20
565. Kerodon 5.5.3.5
566. Kerodon 5.5.3.6
567. Kerodon 1.1.2.8
568. Kerodon 5.4.1.1
569. Kerodon 5.4.5.2
570. Kerodon 5.4.3.1
571. Kerodon 5.4.5.7
572. Kerodon 5.4.2.6
573. Kerodon 5.4.5.9
574. Kerodon 5.4.6.10
575. Kerodon 5.4.3.9
576. Kerodon 5.4.6.8
577. Kerodon 5.4.2.8
578. Kerodon 5.4.3.4
579. Kerodon 2.4.5.4
580. Kerodon 2.4.5.2
581. Kerodon 2.4.5.5
582. Kerodon 2.4.3.8
583. Kerodon 5.4.8.3
584. Kerodon 2.4.4.10
585. Kerodon 2.4.4.16
586. Kerodon 5.4.8.4
587. Kerodon 2.4.6.13
588. Kerodon 5.4.8.5
589. Kerodon 5.6.2.18
590. Kerodon 5.6.2.16
591. Kerodon 5.6.2.17
592. Kerodon 5.6.2.19
593. Kerodon 5.6.2.24
594. Kerodon 5.6.8.9
595. Kerodon 3.1.7.7
596. Kerodon 5.2.8.1
597. Kerodon 5.6.8.2
598. Kerodon 3.1.5.7
599. Kerodon 3.1.7.9
600. Kerodon 3.2.4.2
601. Kerodon 3.5.1.19
602. Kerodon 3.1.7.23
603. Kerodon 3.1.8.2
604. Kerodon 3.5.1.31
605. Kerodon 3.5.1.32
606. Kerodon 3.5.1.33
607. Kerodon 5.6.5.13
608. Kerodon 5.4.5.1
609. Kerodon 5.5.5.10
610. Kerodon 4.4.1.11; Kerodon 4.4.2.1; Kerodon 4.4.2.6; Kerodon 4.4.2.13; Kerodon 4.4.2.14; Kerodon 4.4.2.15; Kerodon 4.4.3.7; Kerodon 4.4.3.8; Kerodon 4.4.3.11; Kerodon 4.4.3.18; Kerodon 4.4.3.19; Kerodon 4.4.3.20; Kerodon 4.4.4.4; Kerodon 4.4.4.8; Kerodon 4.4.4.9; Kerodon 4.4.5.1; Kerodon 4.4.5.3; Kerodon 4.4.5.4; Kerodon 4.4.5.5; Kerodon 4.4.5.6; Kerodon 4.4.5.7; Kerodon 4.4.5.8; Kerodon 4.4.5.9; Kerodon 4.5.1.21; Kerodon 4.5.3.2; Kerodon 4.5.3.6; Kerodon 4.5.3.7; Kerodon 4.5.3.15; Kerodon 4.5.3.19; Kerodon 4.5.3.22; Kerodon 4.5.3.23; Kerodon 4.5.3.24; Kerodon 4.5.3.27; Kerodon 4.5.3.30; Kerodon 4.5.3.31; Kerodon 4.5.3.35; Kerodon 4.5.4.11; Kerodon 4.5.4.12; Kerodon 4.5.4.14; Kerodon 4.5.4.16; Kerodon 4.5.5.4; Kerodon 4.5.5.11; Kerodon 4.5.5.15; Kerodon 4.5.6.2; Kerodon 4.5.6.7; Kerodon 4.5.6.18; Kerodon 4.5.7.11; Kerodon 4.5.7.12; Kerodon 4.5.7.13; Kerodon 4.5.7.18; Kerodon 4.5.7.20; Kerodon 4.5.7.21; Kerodon 4.5.7.22; Kerodon 4.5.7.23; Kerodon 4.6.1.11; Kerodon 4.6.1.14; Kerodon 4.6.1.22; Kerodon 4.6.1.24; Kerodon 4.6.2.8; Kerodon 4.6.2.9; Kerodon 4.6.2.10; Kerodon 4.6.2.11; Kerodon 4.6.2.12; Kerodon 4.6.2.14; Kerodon 4.6.4.13; Kerodon 4.6.5.10; Kerodon 4.7.1.16; Kerodon 4.7.6.11; Kerodon 4.7.6.24; Kerodon 4.7.6.25; Kerodon 4.8.2.4; Kerodon 4.8.2.15; Kerodon 4.8.2.16; Kerodon 4.8.2.17; Kerodon 4.8.2.18; Kerodon 4.8.2.24; Kerodon 4.8.2.25; Kerodon 4.8.2.28; Kerodon 4.8.2.30; Kerodon 4.8.2.31; Kerodon 4.8.3.26; Kerodon 4.8.3.29; Kerodon 4.8.3.32; Kerodon 4.8.3.39; Kerodon 4.8.4.1; Kerodon 4.8.4.5; Kerodon 4.8.4.6; Kerodon 4.8.5.8; Kerodon 4.8.8.7; Kerodon 4.8.8.11; Kerodon 4.8.8.12; Kerodon 4.8.8.13; Kerodon 4.8.8.14; Kerodon 5.1.1.4; Kerodon 5.1.1.6; Kerodon 5.1.1.9; Kerodon 5.1.1.11; Kerodon 5.1.2.1; Kerodon 5.1.2.3; Kerodon 5.1.2.4; Kerodon 5.1.2.5; Kerodon 5.1.2.6; Kerodon 5.1.3.6; Kerodon 5.1.3.7; Kerodon 5.1.3.8; Kerodon 5.1.3.9; Kerodon 5.1.3.11; Kerodon 5.1.4.5; Kerodon 5.1.4.6; Kerodon 5.1.4.8; Kerodon 5.1.4.9; Kerodon 5.1.4.12; Kerodon 5.1.4.13; Kerodon 5.1.4.15; Kerodon 5.1.6.1; Kerodon 5.1.6.2; Kerodon 5.1.6.5; Kerodon 5.1.6.6; Kerodon 5.1.6.7; Kerodon 5.1.6.8; Kerodon 5.1.7.5; Kerodon 5.1.7.8; Kerodon 5.1.7.9; Kerodon 5.1.7.13; Kerodon 5.1.7.14; Kerodon 5.1.7.15; Kerodon 5.2.1.1; Kerodon 5.2.1.5; Kerodon 5.2.2.5; Kerodon 5.2.2.8; Kerodon 5.2.2.9; Kerodon 5.2.2.11; Kerodon 5.2.2.13; Kerodon 5.2.3.15; Kerodon 5.2.3.17; Kerodon 5.2.3.18; Kerodon 5.2.4.1; Kerodon 5.2.4.2; Kerodon 5.2.4.5; Kerodon 5.2.5.1; Kerodon 5.2.5.2; Kerodon 5.2.8.4; Kerodon 5.2.8.5; Kerodon 5.2.8.8; Kerodon 5.2.8.9; Kerodon 5.2.8.10; Kerodon 5.3.3.15; Kerodon 5.3.3.16; Kerodon 5.3.4.17; Kerodon 5.3.4.18; Kerodon 5.3.5.7; Kerodon 5.3.6.5; Kerodon 5.3.6.6; Kerodon 5.4.4.1; Kerodon 5.4.4.2; Kerodon 5.4.5.6; Kerodon 5.4.5.10; Kerodon 5.4.5.14; Kerodon 5.4.6.11; Kerodon 5.4.6.14; Kerodon 5.4.7.9; Kerodon 5.4.7.10; Kerodon 5.4.7.11; Kerodon 5.4.8.1; Kerodon 5.4.9.2; Kerodon 5.5.3.3; Kerodon 5.5.4.2; Kerodon 5.5.5.9; Kerodon 5.5.5.11; Kerodon 5.5.5.14; Kerodon 5.6.0.2; Kerodon 5.6.2.2; Kerodon 5.6.2.22; Kerodon 5.6.5.3; Kerodon 5.6.5.10; Kerodon 5.6.5.12; Kerodon 5.6.5.15; Kerodon 5.6.7.1; Kerodon 5.6.7.2; Kerodon 5.6.7.3; Kerodon 5.6.7.5; Kerodon 5.6.8.3; Kerodon 5.6.8.5; Kerodon 5.6.8.6; Kerodon 5.6.8.7; Kerodon 5.6.8.10; Kerodon 5.6.9.1; Kerodon 5.6.9.2 （相互参照）
611. Kerodon 4.2.1.8
612. Kerodon 4.4.2.3
613. Kerodon 4.6.5.5
614. Kerodon 4.6.8.16
615. Kerodon 4.6.8.18
616. Kerodon 4.7.1.1
617. Kerodon 4.7.2.1
618. Kerodon 4.7.2.7
619. Kerodon 4.7.1.13
620. Kerodon 4.7.1.14
621. Kerodon 4.7.3.9
622. Kerodon 4.7.3.20
623. Kerodon 4.6.4.16
624. Kerodon 4.6.3.3
625. Kerodon 1.5.3.1
626. Kerodon 3.1.3.7
627. Kerodon 3.1.3.11
628. Kerodon 4.1.4.6
629. Kerodon 4.4.3.15
630. Kerodon 4.6.3.6
631. Kerodon 4.6.3.8
632. Kerodon 4.6.3.10
633. Kerodon 4.6.3.11
634. Kerodon 4.6.4.25
635. Kerodon 4.6.4.19
636. Kerodon 5.1.7.7
637. Kerodon 4.5.3.33
638. Kerodon 4.5.8.10
639. Kerodon 5.3.6.1
640. Kerodon 5.3.7.1
641. Kerodon 5.3.7.2
642. Kerodon 5.3.7.3
643. Kerodon 4.4.3.23
644. Kerodon 4.8.1.11
645. Kerodon 4.8.4.4
646. Kerodon 6.3.1.7
647. Kerodon 6.3.1.9
648. Kerodon 6.3.1.13
649. Kerodon 6.3.1.4
650. Kerodon 6.3.1.17
651. Kerodon 6.3.1.20
652. Kerodon 6.3.1.21
653. Kerodon 4.5.8.1
654. Kerodon 4.1.2.15
655. Kerodon 5.1.1.5
656. Kerodon 5.1.1.8
657. Kerodon 5.1.4.17
658. Kerodon 4.4.3.14
659. Kerodon 4.5.6.3
660. Kerodon 4.5.6.1
661. Kerodon 4.5.6.4
662. Kerodon 4.5.8.5
663. Kerodon 4.5.8.18
664. Kerodon 4.5.6.14
665. Kerodon 5.3.6.7; Kerodon 5.3.6.12; Kerodon 5.3.6.13 （相互参照）
666. Kerodon 5.3.6.9
667. Kerodon 6.3.4.2
668. Kerodon 6.3.4.3
669. Kerodon 3.1.2.1
670. Kerodon 4.2.1.6
671. Kerodon 4.2.4.6
672. Kerodon 4.2.4.4
673. Kerodon 4.4.2.4
674. Kerodon 4.4.2.5
675. Kerodon 7.2.1.3
676. Kerodon 3.1.1.6
677. Kerodon 3.1.3.2
678. Kerodon 3.1.7.17
679. Kerodon 7.2.1.5
680. Kerodon 7.2.1.6
681. Kerodon 4.2.5.2
682. Kerodon 1.5.6.6
683. Kerodon 5.6.7.4
684. Kerodon 6.3.1.1
685. Kerodon 7.2.1.10
686. Kerodon 4.2.4.7
687. Kerodon 6.3.1.12
688. Kerodon 7.2.1.13
689. Kerodon 7.2.1.14
690. Kerodon 7.2.1.15
691. Kerodon 5.6.0.6
692. Kerodon 7.2.1.21
693. Kerodon 7.2.1.22
694. Kerodon 7.2.3.10
695. Kerodon 7.2.3.1
696. HTT 4.1.3.1
697. HA 3.4.1.11
698. HA 2.3.2.1
699. HA 2.3.2.10
700. HTT 2.4.1.3
701. HTT 4.3.2.2
702. HTT 4.3.2.7
703. HTT 4.3.1.7
704. HTT 4.3.2.8
705. HTT 4.3.2.12
706. HTT 4.3.2.13
707. HA 2.3.2.11
708. HA 2.3.2.5
709. HTT 4.3.1.5
710. HA 3.4.3.13
711. HA 3.4.3.14
712. HA 3.4.3.15
713. HA 3.4.1.12
714. HTT 5.2.7.6
715. HTT 5.2.7.8
716. HTT 5.2.8.19
717. HTT 5.2.8.22
718. HTT 5.2.8.17
719. HTT 5.2.8.18
720. HA 3.4.1.3
721. HA 3.4.1.4
722. HTT 1.1.5.5
723. HTT 1.1.5.10
724. HTT 1.1.5.12
725. HA 5.1.0.2
726. HA 4.2.1.19
727. HA 4.2.3.1
728. HA 4.2.3.2
729. HA 4.3.1.12
730. HA 4.3.2.1
731. HA 2.1.1.20
732. HA 2.1.2.7
733. HA 2.1.2.9
734. HA 2.1.2.6
735. HA 2.1.2.11
736. HA 2.1.3.5
737. HA 4.3.2.6
738. HA 5.3.1.19
739. HA 4.8.3.9
740. HA 4.8.3.19
741. HA 3.2.2.8
742. HA 3.2.2.9
743. HTT 4.4.4.9
744. HTT 4.4.4.10
745. HA 2.3.3.23
746. HA 2.4.2.11
747. HA 2.4.2.1
748. HA 2.1.1.1
749. HA 2.1.1.7
750. HA 2.1.1.18
751. HA 2.1.1.19
752. HA 2.1.1.21
753. HA 4.1.1.3
754. HA 4.1.2.5
755. HA 4.1.2.9
756. HA 2.3.3.6
757. HA 4.1.2.11
758. HA 4.1.1.1
759. HA 4.2.1.2
760. HA 4.2.1.10
761. HA 4.2.2.8
762. HA 4.2.2.26
763. HA 4.2.2.12
764. HA 4.2.2.16
765. HA 4.2.2.17
766. HA 4.2.3.5
767. HA 4.6.2.7
768. HA 4.7.4.13
769. HA 4.2.1.13
770. HA 4.2.4.8
771. HA 4.6.2.9
772. HA 4.7.3.5
773. HA 4.7.3.14
774. HA 4.7.3.16
775. HA 4.8.1.1
776. HA 7.3.2.1
777. HA 7.3.2.2
778. HTT 5.2.2.1
779. HA 7.3.2.3
780. HA 4.8.4.10
781. HA 4.8.4.13
782. HA 4.8.4.3
783. HA 2.1.2.16
784. HA 2.1.3.4
785. HA 4.2.2.6
786. HA 4.3.2.2
787. HA 4.8.4.4
788. HA 4.8.4.5
789. HA 4.8.4.6
790. HA 2.4.2.8
791. HA 4.1.2.10
792. HA 4.2.2.2
793. HA 4.2.2.9
794. HA 4.8.4.12
795. HTT 5.4.7.15
796. HTT 5.4.7.11
797. HTT 4.3.2.9
798. HTT 5.5.2.3
799. HA 4.8.4.1; HA 4.8.4.14 （相互参照）
800. HA 4.8.3.13
801. HTT 2.4.2.7
802. HTT 2.4.2.8
803. HTT 5.2.2.4
804. HA 4.6.2.1; HA 4.6.2.10; HA 4.6.2.12; HA 4.6.2.13; HA 4.6.2.17; HA 4.8.3.15; HA 4.8.3.21 （相互参照）
805. HA 2.3.1.1
806. HA 3.3.2.1
807. HA 5.1.3.1
808. HA 5.1.3.2
809. HA 5.1.4.12
810. HTT 5.5.8.4
811. HA 5.1.4.10
812. HA 1.4.2.8; HA 1.4.3.1 （相互参照）
813. HA 4.8.2.19
814. HA 5.1.1.5
815. HA 7.1.0.1
816. HA 7.1.3.5
817. HA 7.1.3.8
818. DAGXIII 2.2.4
819. HTT 2.4.4.1
820. HTT 2.4.4.3
821. HA 2.2.4.11
822. HA 2.2.4.12
823. HA 2.1.2.2
824. HA 2.1.2.4
825. HA 2.2.4.13
826. HA 2.2.4.14
827. HTT 2.4.7.2
828. HTT 2.4.7.5
829. HTT 2.4.7.10
830. HTT 2.4.7.11
831. HTT 2.4.7.12
832. HA 2.2.4.15
833. HA 2.2.4.16
834. HA 2.2.4.4
835. HA 2.2.4.8
836. HA 2.2.4.5
837. HA 2.2.4.6
838. HA 3.1.1.2
839. HTT 2.4.1.4
840. HTT 2.4.2.4
841. HTT 2.4.4.6
842. HA 3.1.1.5
843. HTT 3.1.1.11
844. HA 3.1.1.15
845. HA 3.1.1.16
846. HA 3.1.1.20
847. HA 3.4.4.3
848. HA 3.4.4.4
849. HA 3.4.4.5
850. HA 3.1.1.18
851. HA 3.1.2.3
852. HA 4.3.1.1
853. HA 4.4.1.1
854. HA 4.4.1.8
855. HA 4.4.1.11
856. HA 4.4.1.9
857. HA 4.4.1.12
858. HA 4.4.2.4
859. HA 4.4.2.5
860. HA 4.4.2.8
861. HA 4.4.1.28
862. HA 4.4.2.10
863. HA 4.4.3.12
864. HA 4.5.1.2
865. HA 3.1.1.4
866. HA 3.1.1.6
867. HA 3.1.1.9
868. HA 3.1.1.8
869. HA 3.1.1.11
870. HA 3.1.1.12
871. HA 3.1.1.10
872. HA 3.1.1.14
873. HTT 4.3.1.9
874. HTT 3.3.1.2
875. HTT 3.3.1.7
876. HTT 4.3.1.10
877. HA 3.1.1.13
878. HA 3.2.1.1
879. HA 4.5.2.2
880. HA 4.5.2.1
881. HA 7.2.4.1
882. HA 1.2.1.4
883. HA 1.2.1.1
884. HTT 3.3.3.1
885. HTT 3.3.3.2
886. HA 1.2.1.16
887. HTT 5.3.1.7
888. HTT 5.3.1.20
889. HTT 3.3.4.5
890. HTT 4.1.2.13
891. HTT 4.1.2.14
892. HTT 4.1.2.16
893. HTT 4.1.2.17
894. HTT 4.1.2.18
895. HTT 4.3.3.10
896. HTT 3.3.2.2
897. HTT 5.1.5.2
898. HTT 5.1.3.1
899. HTT 5.1.5.3
900. HTT 3.3.3.4
901. HTT 4.1.1.8
902. HTT 4.2.3.4
903. HTT 4.2.3.1
904. HTT 4.2.3.5
905. HTT 4.2.3.6
906. HTT 4.2.3.8
907. HTT 4.2.3.13
908. HTT 4.2.3.14
909. HTT 4.2.4.1
910. HTT 4.2.4.7
911. HTT 5.1.3.2
912. HTT 5.1.5.4
913. HTT 5.1.5.5
914. HTT 3.3.2.6
915. HTT 4.4.4.5
916. HTT 3.3.2.7
917. HTT 5.3.3.3
918. HTT 5.3.1.17
919. HTT 5.3.5.2
920. HTT 5.3.5.3
921. HTT 5.3.5.4
922. HTT 5.3.5.7
923. HTT 5.3.5.8
924. HTT 5.5.0.1
925. Kerodon 5.1.6.4
926. Kerodon 7.1.6.1
927. Kerodon 4.5.6.8
928. Kerodon 4.5.6.20
929. Kerodon 5.1.7.16
930. Kerodon 7.1.5.16
931. Kerodon 7.1.6.8
932. Kerodon 4.6.6.4
933. Kerodon 4.6.6.7
934. Kerodon 4.6.6.8
935. Kerodon 4.6.4.9
936. Kerodon 5.3.7.4
937. Kerodon 5.3.7.5
938. Kerodon 7.1.5.9
939. Kerodon 7.1.5.19
940. Kerodon 7.1.6.13
941. Kerodon 7.1.6.19
942. Kerodon 7.1.6.20
943. Kerodon 3.5.7.6
944. Kerodon 4.7.1.12
945. Kerodon 7.1.3.11
946. Kerodon 4.3.6.10
947. Kerodon 4.5.3.21
948. Kerodon 4.5.3.29
949. Kerodon 4.5.3.34
950. Kerodon 4.6.4.4
951. Kerodon 4.6.4.21
952. Kerodon 4.8.4.13
953. Kerodon 4.8.4.17
954. Kerodon 7.1.5.4
955. Kerodon 7.1.6.4
956. Kerodon 7.1.5.6
957. Kerodon 7.1.6.10
958. Kerodon 7.1.6.11
959. Kerodon 7.1.7.1
960. Kerodon 7.1.7.6
961. Kerodon 4.3.6.9
962. Kerodon 7.1.5.17
963. Kerodon 7.1.8.7
964. Kerodon 7.1.8.10
965. Kerodon 7.1.8.11
966. Kerodon 7.1.8.12
967. Kerodon 7.1.9.2
968. Kerodon 7.1.9.3
969. Kerodon 7.1.9.4
970. Kerodon 7.1.1.9
971. Kerodon 7.1.1.10
972. Kerodon 7.1.1.1
973. Kerodon 5.2.8.6
974. Kerodon 5.2.8.7
975. Kerodon 5.2.8.12
976. Kerodon 5.6.6.10
977. Kerodon 3.1.6.1
978. Kerodon 4.6.7.6
979. Kerodon 4.6.7.7
980. Kerodon 5.6.6.1
981. Kerodon 5.6.6.11
982. Kerodon 4.7.3.1
983. Kerodon 4.7.3.11
984. Kerodon 4.7.3.12
985. Kerodon 4.7.3.21
986. Kerodon 4.7.3.22
987. Kerodon 5.6.6.19
988. Kerodon 5.6.6.21
989. Kerodon 7.1.3.1
990. Kerodon 7.1.3.4
991. Kerodon 7.1.3.6
992. Kerodon 7.1.3.18
993. Kerodon 7.1.9.6
994. Kerodon 7.1.9.7
995. Kerodon 7.1.9.8
996. Kerodon 4.9.5.2
997. Kerodon 4.9.1.5
998. Kerodon 4.9.1.14
999. Kerodon 4.9.1.15
1000. Kerodon 4.9.1.17
1001. Kerodon 4.9.1.21
1002. Kerodon 4.9.2.3
1003. Kerodon 4.9.3.4
1004. Kerodon 4.9.4.8
1005. Kerodon 4.9.5.14
1006. Kerodon 4.9.5.16
1007. Kerodon 3.6.1.6
1008. Kerodon 4.9.2.5
1009. Kerodon 4.9.1.23
1010. Kerodon 4.9.1.24
1011. Kerodon 4.9.2.9
1012. Kerodon 4.9.3.5
1013. Kerodon 4.9.4.7
1014. Kerodon 3.6.1.1
1015. Kerodon 3.6.1.2
1016. Kerodon 3.6.1.4
1017. Kerodon 3.6.1.5
1018. Kerodon 3.6.1.7
1019. Kerodon 4.9.3.6
1020. Kerodon 4.9.4.10
1021. Kerodon 4.9.4.12
1022. Kerodon 4.9.4.14
1023. Kerodon 4.9.5.17
1024. Kerodon 4.9.5.18
1025. Kerodon 4.5.6.13
1026. Kerodon 4.4.1.10
1027. Kerodon 4.4.3.21
1028. Kerodon 4.5.3.20
1029. Kerodon 4.6.4.22
1030. Kerodon 4.9.5.19
1031. Kerodon 4.4.2.10
1032. Kerodon 4.4.2.12
1033. Kerodon 7.1.4.22
1034. Kerodon 7.1.4.24
1035. Kerodon 4.7.3.14
1036. Kerodon 4.7.3.16
1037. Kerodon 7.1.4.20
1038. Kerodon 7.1.4.25
1039. Kerodon 4.7.3.19
1040. Kerodon 7.1.3.17
1041. Kerodon 7.1.4.26
1042. Kerodon 7.1.4.27
1043. Kerodon 7.1.9.1
1044. Kerodon 7.1.6.3
1045. Kerodon 4.6.4.14
1046. Kerodon 5.1.7.1
1047. Kerodon 7.2.1.1
1048. Kerodon 7.2.2.1
1049. Kerodon 7.2.2.2
1050. Kerodon 7.2.2.3
1051. Kerodon 4.3.7.1
1052. Kerodon 4.3.7.9
1053. Kerodon 4.3.7.10
1054. Kerodon 7.1.6.12
1055. Kerodon 4.3.7.6
1056. Kerodon 7.1.7.3
1057. Kerodon 7.1.7.4
1058. Kerodon 7.1.7.5
1059. Kerodon 4.3.3.21
1060. Kerodon 4.9.4.13
1061. Kerodon 9.1.1.14
1062. Kerodon 9.1.1.16
1063. Kerodon 9.1.3.1
1064. Kerodon 9.1.3.8
1065. Kerodon 9.1.4.2
1066. Kerodon 9.1.1.17
1067. Kerodon 3.3.6.1
1068. Kerodon 1.1.0.8
1069. Kerodon 1.1.0.12
1070. Kerodon 3.6.1.3
1071. Kerodon 9.2.0.2
1072. Kerodon 3.6.1.9
1073. Kerodon 3.3.3.5
1074. Kerodon 6.3.5.9
1075. Kerodon 6.3.2.11
1076. Kerodon 6.3.2.12
1077. Kerodon 6.3.1.23
1078. Kerodon 6.3.5.1
1079. Kerodon 3.4.1.16
1080. Kerodon 6.3.5.3
1081. Kerodon 6.3.5.4
1082. Kerodon 6.3.5.13
1083. Kerodon 6.3.5.14
1084. Kerodon 6.3.6.2
1085. Kerodon 7.2.1.11
1086. Kerodon 9.1.3.2
1087. Kerodon 5.1.1.7
1088. Kerodon 5.1.4.7
1089. Kerodon 9.1.3.12
1090. Kerodon 7.1.2.12
1091. Kerodon 7.1.2.11
1092. Kerodon 7.3.1.1
1093. Kerodon 7.3.1.5
1094. Kerodon 7.3.1.2
1095. Kerodon 7.3.1.7
1096. Kerodon 4.5.8.14
1097. Kerodon 5.6.7.6
1098. Kerodon 7.3.1.14
1099. Kerodon 5.1.1.16
1100. Kerodon 5.1.4.19
1101. Kerodon 5.1.4.20
1102. Kerodon 7.1.1.8
1103. Kerodon 7.3.1.10
1104. Kerodon 7.3.2.1
1105. Kerodon 7.3.2.3
1106. Kerodon 7.3.2.11
1107. Kerodon 4.5.5.5
1108. Kerodon 7.3.2.12
1109. Kerodon 7.3.3.15
1110. Kerodon 7.1.6.9
1111. Kerodon 7.2.2.5
1112. Kerodon 7.2.2.9
1113. Kerodon 7.3.3.17
1114. Kerodon 7.3.4.3
1115. Kerodon 7.3.4.7
1116. Kerodon 7.3.5.5
1117. Kerodon 7.3.6.7; Kerodon 7.3.6.8 （相互参照）
1118. Kerodon 7.3.6.9
1119. Kerodon 7.3.8.1
1120. Kerodon 7.3.8.10
1121. Kerodon 7.3.8.12
1122. Kerodon 7.3.8.14
1123. Kerodon 7.3.8.24
1124. Kerodon 7.3.1.11
1125. Kerodon 7.3.5.8
1126. Kerodon 7.3.6.5
1127. Kerodon 7.3.6.6
1128. Kerodon 7.3.8.25
1129. Kerodon 7.3.8.26
1130. Kerodon 5.6.5.1
1131. Kerodon 7.4.2.15
1132. Kerodon 7.4.3.6
1133. Kerodon 7.6.6.17
1134. Kerodon 5.5.3.11
1135. Kerodon 5.5.3.13
1136. Kerodon 4.9.3.9
1137. Kerodon 4.9.4.5
1138. Kerodon 4.9.4.9
1139. Kerodon 4.5.2.12
1140. Kerodon 4.9.5.4
1141. Kerodon 4.5.2.15
1142. Kerodon 4.5.2.9
1143. Kerodon 4.5.2.10
1144. Kerodon 5.3.8.2
1145. Kerodon 5.3.8.6
1146. Kerodon 5.3.8.11; Kerodon 5.3.8.12 （相互参照）
1147. Kerodon 4.9.8.10
1148. Kerodon 5.6.2.1
1149. Kerodon 7.4.3.8
1150. Kerodon 7.4.5.22
1151. Kerodon 7.6.6.11
1152. Kerodon 4.9.3.16
1153. Kerodon 4.9.4.18
1154. Kerodon 4.9.4.19
1155. Kerodon 4.9.8.11
1156. Kerodon 7.4.1.15
1157. Kerodon 7.4.4.6
1158. Kerodon 7.4.4.11
1159. Kerodon 7.4.4.12
1160. Kerodon 7.4.4.13
1161. Kerodon 7.4.4.1
1162. Kerodon 7.4.4.14
1163. Kerodon 7.6.6.12
1164. Kerodon 3.4.0.6
1165. Kerodon 7.6.2.40
1166. Kerodon 7.6.3.12
1167. Kerodon 7.7.0.2
1168. Kerodon 7.7.0.4
1169. Kerodon 7.7.0.6
1170. Kerodon 7.7.7.4
1171. Kerodon 9.1.1.11
1172. Kerodon 7.2.3.2
1173. Kerodon 7.2.3.9
1174. Kerodon 9.1.1.18
1175. Kerodon 7.4.3.1
1176. Kerodon 4.7.3.23
1177. Kerodon 7.4.3.7
1178. Kerodon 8.1.1.6
1179. Kerodon 8.1.1.11
1180. Kerodon 6.2.2.6
1181. Kerodon 6.2.5.1
1182. Kerodon 7.2.3.6
1183. Kerodon 7.3.3.7
1184. Kerodon 7.3.6.1
1185. Kerodon 8.3.1.2
1186. Kerodon 7.1.2.8
1187. Kerodon 7.1.2.3
1188. Kerodon 7.1.2.6
1189. Kerodon 7.1.2.9
1190. Kerodon 7.1.2.10
1191. Kerodon 8.3.1.7
1192. Kerodon 8.3.1.3
1193. Kerodon 8.2.2.13
1194. Kerodon 8.2.0.3
1195. Kerodon 8.2.3.1
1196. Kerodon 8.2.3.2
1197. Kerodon 8.2.1.3
1198. Kerodon 8.2.2.11
1199. Kerodon 8.2.3.7
1200. Kerodon 8.2.3.4
1201. Kerodon 8.2.3.5
1202. Kerodon 8.2.3.9
1203. Kerodon 8.2.4.1
1204. Kerodon 8.2.4.3
1205. Kerodon 8.3.5.3
1206. Kerodon 8.3.3.2
1207. Kerodon 8.3.4.2
1208. Kerodon 8.3.4.6
1209. Kerodon 5.6.6.2
1210. Kerodon 8.3.4.12
1211. Kerodon 8.3.4.13
1212. Kerodon 8.3.4.15
1213. Kerodon 8.3.2.3
1214. Kerodon 8.3.4.16
1215. Kerodon 8.3.5.1
1216. Kerodon 8.4.2.5
1217. Kerodon 8.4.2.7
1218. Kerodon 8.4.2.8
1219. Kerodon 9.1.5.4
1220. Kerodon 4.3.7.11
1221. Kerodon 7.1.0.1
1222. Kerodon 7.1.3.19
1223. Kerodon 7.1.8.9
1224. Kerodon 7.1.8.15
1225. Kerodon 7.1.8.3
1226. Kerodon 7.4.1.1
1227. Kerodon 7.4.1.8
1228. Kerodon 7.4.1.9
1229. Kerodon 7.4.1.13
1230. Kerodon 4.2.4.10
1231. Kerodon 4.2.4.11
1232. Kerodon 7.4.1.14
1233. Kerodon 7.4.1.16
1234. Kerodon 7.1.1.6
1235. Kerodon 7.2.2.12
1236. Kerodon 7.6.2.41
1237. Kerodon 7.6.2.42
1238. Kerodon 9.1.5.6
1239. Kerodon 9.1.5.7
1240. Kerodon 9.1.3.13; Kerodon 9.1.5.10 （相互参照）
1241. Kerodon 9.1.3.14
1242. Kerodon 9.1.4.13
1243. Kerodon 9.1.4.14
1244. Kerodon 9.1.4.15
1245. Kerodon 9.1.4.17
1246. Kerodon 9.1.4.18
1247. Kerodon 9.1.4.19
1248. Kerodon 9.1.4.5; Kerodon 9.1.4.6 （相互参照）
1249. Kerodon 9.1.4.16
1250. Kerodon 4.9.1.16
1251. Kerodon 4.9.1.18
1252. Kerodon 4.9.1.22
1253. Kerodon 9.2.3.1
1254. Kerodon 7.1.1.13
1255. Kerodon 7.2.2.10
1256. Kerodon 7.2.2.11
1257. Kerodon 3.2.8.4
1258. Kerodon 3.2.8.5
1259. Kerodon 4.9.1.26
1260. Kerodon 7.2.3.4
1261. Kerodon 9.2.4.5
1262. Kerodon 9.2.4.3
1263. Kerodon 4.3.6.7
1264. Kerodon 7.3.3.9
1265. Kerodon 7.2.1.19
1266. Kerodon 7.3.3.3
1267. Kerodon 7.3.3.20
1268. Kerodon 8.5.1.8
1269. Kerodon 8.5.1.9
1270. Kerodon 8.5.1.10
1271. Kerodon 8.5.1.11
1272. Kerodon 8.5.1.12
1273. Kerodon 9.2.2.13
1274. Kerodon 9.2.5.18
1275. Kerodon 5.6.6.12
1276. Kerodon 5.6.6.13
1277. Kerodon 5.6.6.14
1278. Kerodon 7.4.1.22
1279. Kerodon 7.1.5.18
1280. Kerodon 7.1.6.16
1281. Kerodon 7.1.6.17
1282. Kerodon 6.1.2.11
1283. Kerodon 6.2.1.14
1284. Kerodon 6.2.1.17
1285. Kerodon 6.2.6.1
1286. Kerodon 6.2.6.5
1287. Kerodon 6.2.1.19
1288. Kerodon 7.1.1.18
1289. Kerodon 7.1.6.18
1290. Kerodon 7.1.8.1
1291. Kerodon 7.1.8.2
1292. Kerodon 7.7.7.1
1293. Kerodon 9.2.2.17
1294. Kerodon 9.2.5.24
1295. Kerodon 4.7.6.12
1296. Kerodon 5.3.3.20
1297. Kerodon 5.3.4.10
1298. Kerodon 5.3.5.1
1299. Kerodon 5.3.5.2
1300. Kerodon 5.3.4.8
1301. Kerodon 5.3.5.8
1302. Kerodon 5.3.2.18
1303. Kerodon 5.3.5.9
1304. Kerodon 5.3.5.6
1305. Kerodon 5.6.2.14
1306. Kerodon 5.6.4.3
1307. Kerodon 5.6.4.6
1308. Kerodon 5.6.4.7
1309. Kerodon 5.6.4.8
1310. Kerodon 5.6.5.7
1311. Kerodon 5.6.5.18
1312. Kerodon 7.1.3.5
1313. Kerodon 5.6.6.17
1314. Kerodon 7.5.4.5
1315. Kerodon 7.5.4.6
1316. Kerodon 5.3.2.9
1317. Kerodon 7.5.7.3
1318. Kerodon 7.5.2.8
1319. Kerodon 7.5.2.11
1320. Kerodon 7.5.4.1
1321. Kerodon 7.5.5.1
1322. Kerodon 7.5.5.15
1323. Kerodon 7.5.8.4
1324. Kerodon 7.5.8.9
1325. Kerodon 5.3.4.1
1326. Kerodon 7.5.8.2
1327. Kerodon 7.5.5.6
1328. Kerodon 7.5.8.6
1329. Kerodon 7.5.4.2
1330. Kerodon 7.5.6.6
1331. Kerodon 7.5.8.7
1332. Kerodon 9.1.6.9
1333. Kerodon 9.1.6.12
1334. Kerodon 9.1.6.7
1335. Kerodon 9.1.6.1
1336. Kerodon 9.1.6.3
1337. Kerodon 9.1.8.1
1338. Kerodon 9.1.9.1
1339. Kerodon 1.4.0.9
1340. Kerodon 1.5.5.3
1341. Kerodon 4.9.4.1
1342. Kerodon 8.3.3.1
1343. Kerodon 8.3.3.9
1344. Kerodon 8.4.2.1
1345. Kerodon 9.2.0.5
1346. Kerodon 9.2.5.25
1347. Kerodon 9.2.5.9
1348. Kerodon 9.2.5.10
1349. Kerodon 9.1.9.6
1350. Kerodon 9.1.9.7
1351. Kerodon 9.1.9.5
1352. Kerodon 9.1.9.8
1353. Kerodon 7.1.9.5
1354. Kerodon 4.5.3.10
1355. Kerodon 4.5.6.11
1356. Kerodon 4.6.4.2
1357. Kerodon 8.3.7.4
1358. Kerodon 8.1.1.16
1359. Kerodon 8.1.2.15
1360. Kerodon 8.1.2.16
1361. Kerodon 8.1.2.17
1362. Kerodon 8.2.0.2
1363. Kerodon 5.6.6.20
1364. Kerodon 8.2.2.4
1365. Kerodon 8.2.3.6
1366. Kerodon 8.2.4.8
1367. Kerodon 8.3.7.3
1368. Kerodon 8.3.7.6
1369. Kerodon 5.3.3.18
1370. Kerodon 5.6.5.6
1371. Kerodon 7.1.8.13
1372. Kerodon 7.3.8.5
1373. Kerodon 7.3.8.6
1374. Kerodon 7.3.8.8
1375. Kerodon 4.5.3.8
1376. Kerodon 7.5.5.7
1377. Kerodon 7.5.5.8
1378. Kerodon 7.5.4.13
1379. Kerodon 7.5.5.10
1380. Kerodon 7.6.3.4
1381. Kerodon 8.3.7.7
1382. Kerodon 8.3.7.1
1383. Kerodon 8.3.7.2
1384. Kerodon 9.2.8.3
1385. Kerodon 9.2.8.5
1386. Kerodon 9.3.2.5
1387. Kerodon 4.9.8.12
1388. Kerodon 4.9.3.19
1389. Kerodon 7.3.1.12
1390. Kerodon 5.1.5.16
1391. Kerodon 5.6.7.7
1392. Kerodon 7.3.5.1
1393. Kerodon 4.9.5.7
1394. Kerodon 7.1.1.17
1395. Kerodon 7.6.6.14
1396. Kerodon 7.6.6.19
1397. Kerodon 5.6.6.3
1398. Kerodon 5.6.6.4
1399. Kerodon 5.6.6.6
1400. Kerodon 8.3.2.17
1401. Kerodon 8.3.2.9
1402. Kerodon 8.3.2.18
1403. Kerodon 8.3.2.20
1404. Kerodon 8.2.1.5
1405. Kerodon 8.2.6.2
1406. Kerodon 8.2.6.1
1407. Kerodon 8.3.2.8
1408. Kerodon 8.3.2.19
1409. Kerodon 8.3.3.8
1410. Kerodon 8.3.3.13
1411. Kerodon 8.4.1.20
1412. Kerodon 8.4.1.21
1413. Kerodon 8.4.1.22
1414. Kerodon 8.4.2.4
1415. Kerodon 7.3.6.14
1416. Kerodon 7.3.6.15
1417. Kerodon 8.3.3.14
1418. Kerodon 7.1.1.11
1419. Kerodon 7.3.1.13
1420. Kerodon 8.4.1.19
1421. Kerodon 8.4.6.6
1422. Kerodon 7.6.6.21
1423. Kerodon 8.3.3.15
1424. Kerodon 8.3.3.16
1425. Kerodon 8.3.3.17
1426. Kerodon 8.4.3.4
1427. Kerodon 7.3.6.12
1428. Kerodon 7.3.6.13
1429. Kerodon 8.4.1.16
1430. Kerodon 8.4.1.18
1431. Kerodon 8.4.2.2
1432. Kerodon 8.4.3.5
1433. Kerodon 8.4.3.2
1434. Kerodon 8.4.6.9
1435. Kerodon 8.4.6.10
1436. Kerodon 8.4.6.8
1437. Kerodon 9.2.1.3
1438. Kerodon 9.2.2.6
1439. Kerodon 9.3.1.7
1440. Kerodon 8.5.5.5
1441. Kerodon 7.2.1.4
1442. Kerodon 7.2.1.9
1443. Kerodon 8.5.5.4
1444. Kerodon 8.5.6.16
1445. Kerodon 8.5.6.17
1446. Kerodon 8.5.6.19
1447. Kerodon 8.5.2.7
1448. Kerodon 8.5.2.9
1449. Kerodon 9.1.1.10
1450. Kerodon 7.2.2.8
1451. Kerodon 9.1.5.13
1452. Kerodon 9.1.8.11
1453. Kerodon 9.1.1.6
1454. Kerodon 9.3.4.11
1455. Kerodon 7.4.5.1
1456. Kerodon 9.1.3.11
1457. Kerodon 9.1.5.15
1458. Kerodon 9.1.5.16
1459. Kerodon 8.6.5.2
1460. Kerodon 8.6.6.1
1461. Kerodon 8.6.6.3
1462. Kerodon 8.6.8.3
1463. Kerodon 9.1.1.4
1464. Kerodon 9.3.4.7
1465. Kerodon 9.3.4.13
1466. Kerodon 6.3.1.16
1467. Kerodon 6.3.4.4
1468. Kerodon 6.3.4.1
1469. Kerodon 7.4.5.8
1470. Kerodon 6.3.1.11
1471. Kerodon 7.4.5.10
1472. Kerodon 6.3.2.1
1473. Kerodon 7.4.5.18
1474. Kerodon 6.3.2.13
1475. Kerodon 7.4.5.19
1476. Kerodon 4.6.1.6
1477. Kerodon 5.1.4.14
1478. Kerodon 7.4.5.11
1479. Kerodon 7.4.5.12
1480. Kerodon 7.4.6.1
1481. Kerodon 7.4.6.2
1482. Kerodon 7.4.6.3
1483. Kerodon 7.4.5.13; Kerodon 7.4.5.16 （相互参照）
1484. Kerodon 9.3.4.19
1485. Kerodon 9.3.4.20
1486. Kerodon 9.3.4.14; Kerodon 9.3.4.15; Kerodon 9.3.4.21 （相互参照）
1487. Kerodon 9.3.2.1
1488. Kerodon 9.3.2.3
1489. Kerodon 9.3.7.2
1490. Kerodon 7.3.8.3
1491. Kerodon 7.4.3.11
1492. Kerodon 8.4.6.3
1493. Kerodon 8.4.6.5
1494. Kerodon 8.4.6.11
1495. Kerodon 9.3.1.12
1496. Kerodon 9.3.1.14
1497. Kerodon 9.3.7.10
1498. Kerodon 9.3.7.11
1499. Kerodon 9.4.5.9
1500. Kerodon 9.4.5.10
1501. Kerodon 9.4.8.15
1502. Kerodon 9.4.9.9
1503. Kerodon 4.3.7.2
1504. Kerodon 4.3.6.6
1505. Kerodon 4.5.3.12
1506. Kerodon 7.2.3.11
1507. Kerodon 7.4.2.14
1508. Kerodon 7.4.3.13
1509. Kerodon 7.4.3.14
1510. Kerodon 3.2.4.15
1511. Kerodon 3.3.3.6
1512. Kerodon 4.9.4.16
1513. Kerodon 9.1.3.5
1514. Kerodon 9.1.3.6
1515. Kerodon 9.1.3.7
1516. Kerodon 9.1.5.14
1517. Kerodon 9.4.4.15
1518. Kerodon 9.4.4.4
1519. Kerodon 9.4.4.6
1520. Kerodon 9.4.9.4
1521. Kerodon 9.5.4.4
1522. Kerodon 9.5.4.5
1523. Kerodon 9.5.4.6
1524. HTT 5.5.3.12
1525. HA 1.4.4.11
1526. HA 4.6.2.2
1527. HA 4.6.2.18
1528. HA 2.4.1.6
1529. HA 4.1.7.10
1530. HTT 3.1.0.1
1531. HA 4.8.1.2
1532. HTT 5.3.6.1
1533. HTT 5.3.6.2
1534. HTT 5.3.6.11
1535. HA 4.8.1.3
1536. HA 4.8.1.4
1537. HA 4.1.1.18
1538. HA 4.2.4.9
1539. HTT 5.3.5.9
1540. HA 4.8.5.2
1541. HA 4.8.4.8
1542. HTT A.2.6.3
1543. HTT 4.2.3.10
1544. HTT 4.2.3.11
1545. HTT 5.1.6.3
1546. HTT 5.1.6.4
1547. HTT 5.1.6.8
1548. HTT 5.1.6.10
1549. HTT 5.3.4.5
1550. HTT 5.3.5.5
1551. HTT 5.3.5.11
1552. HTT 4.3.2.16
1553. HTT 5.1.5.6
1554. HTT 5.3.4.14
1555. HTT 5.3.4.15
1556. HTT 5.3.4.16
1557. HTT 5.3.4.17
1558. HTT 5.3.5.10
1559. HTT 5.2.7.5
1560. HTT 5.2.4.1
1561. HTT 5.2.4.2
1562. HTT 5.3.4.18
1563. HTT 5.3.5.12
1564. HTT 5.4.1.8
1565. HTT 4.4.5.15
1566. HTT 4.4.5.2
1567. HTT 4.4.5.9
1568. HTT 5.3.1.9
1569. HTT 5.3.1.10
1570. HTT 5.4.2.4
1571. HTT 5.4.2.2
1572. HTT 5.5.1.3
1573. HTT 5.5.1.4
1574. HTT 5.5.1.1
1575. HTT 5.5.1.9
1576. HA 7.2.4.2
1577. DAGXIII 2.2.5
1578. HA 3.2.2.1
1579. HA 3.2.2.5
1580. HA 5.1.1.3
1581. HA 2.1.1.23
1582. HA 5.1.1.9
1583. HA 5.1.1.10
1584. HA 5.1.1.11
1585. HA A.3.2
1586. HA A.3.1; HA A.3.8; HA A.3.10 （相互参照）
1587. HA 5.1.1.1
1588. HA 5.1.1.4
1589. HTT 2.3.4.1
1590. HTT 2.3.4.18
1591. HA 5.1.1.7
1592. HA 1.1.2.5
1593. HA 1.1.2.7
1594. HA 1.1.2.11
1595. HA 1.1.2.14
1596. HA 1.1.3.3
1597. HTT 4.4.2.2
1598. HTT 4.4.2.4
1599. HTT 4.4.2.6
1600. HTT 4.4.3.1
1601. HTT 4.4.3.2
1602. HTT 5.3.2.10
1603. HA 1.1.3.4; HA 1.1.4.1 （相互参照）
1604. HA 1.4.2.17
1605. HA 1.4.2.1
1606. HA 1.4.2.12
1607. HA 1.4.2.15
1608. HA 1.4.2.11; HA 1.4.2.13 （相互参照）
1609. HTT 5.5.4.18
1610. HTT 5.5.4.19
1611. HA 1.4.2.4
1612. HA 1.4.2.3
1613. HA 1.4.2.10
1614. HA 1.4.2.16
1615. HA 1.4.2.23
1616. HTT 5.2.7.4
1617. HTT 5.2.7.7
1618. HTT 5.5.4.5
1619. HTT 5.5.4.10
1620. HTT 5.5.4.11
1621. HTT 5.3.1.18
1622. HTT 5.4.7.7
1623. HTT 5.5.4.4
1624. HTT 5.5.4.2
1625. HTT 4.4.5.10
1626. HTT 4.4.5.11
1627. HTT 4.4.5.12
1628. HTT 5.5.4.6
1629. HTT 3.3.1.3
1630. HTT 5.4.2.1
1631. HTT 5.4.2.5
1632. Kerodon 9.4.9.10
1633. Kerodon 9.4.9.11
1634. HTT 5.4.6.6
1635. HTT 5.3.4.9
1636. HTT 6.5.3.7
1637. HTT 4.2.3.15
1638. HTT 4.1.2.7
1639. HTT 4.2.3.16
1640. HTT 5.3.1.12
1641. HTT 5.3.4.10
1642. HTT 5.3.4.12
1643. HTT 5.4.5.7
1644. HTT 5.3.4.13
1645. HTT 5.3.5.15
1646. HTT 5.5.4.13
1647. HTT 5.5.5.9
1648. HTT 4.4.2.8
1649. HTT 4.4.2.9
1650. HTT 5.5.5.11
1651. HTT 5.5.5.12
1652. HTT 5.5.5.13
1653. HTT 5.5.5.14
1654. HTT 5.5.4.15
1655. HTT 5.5.4.20
1656. HTT 5.5.7.2
1657. HTT 5.5.7.3
1658. HA 1.4.2.26
1659. HTT 5.4.7.17
1660. HTT 5.5.3.15
1661. HTT 5.5.3.16
1662. HTT 5.5.4.17
1663. HTT 5.5.3.17
1664. HTT 5.5.3.18
1665. HA 1.4.2.24
1666. HA 1.2.1.17
1667. HA 1.2.1.19
1668. HA 4.2.1.5
1669. HA 4.2.1.9
1670. HA 4.2.1.17
1671. HA 4.2.3.3
1672. HA 7.1.1.13
1673. HA 2.2.1.6
1674. HA 2.2.1.1
1675. HA 2.2.1.3
1676. HA 2.2.1.8
1677. HA 2.2.1.11
1678. HA 2.2.1.9
1679. HA 7.1.3.10
1680. HA 7.1.3.15
1681. HA 7.1.2.13
1682. HA 7.1.3.16
1683. HA 7.1.3.18
1684. DAGXIII 2.2.6
1685. DAGXIII 2.2.7
1686. NS A.5
1687. NS I.1.1
1688. NS I.1.5
1689. HTT 5.2.1.3
1690. HTT 5.2.2.8
1691. HTT 4.3.2.17
1692. HTT 3.2.2.11
1693. HTT 5.2.1.5
1694. HTT 5.2.2.3
1695. HTT 5.2.2.6
1696. HTT 5.2.4.3
1697. HTT 4.3.3.5; HTT 4.3.3.7 （相互参照）
1698. NS I.1.6
1699. HA 6.1.6.3
1700. NS I.1.7
1701. HA 6.1.6.4
1702. HA 6.1.6.5
1703. HA 6.1.6.6
1704. HA 6.1.6.7
1705. NS I.1.8
1706. HA 6.1.6.10
1707. HA 6.1.6.11
1708. HA 6.1.6.12
1709. NS I.1.9
1710. NS I.1.10
1711. NS I.1.11
1712. NS I.1.12
1713. NS I.1.13
1714. HTT 5.2.7.2
1715. HTT 5.5.2.7
1716. HTT 5.5.2.9
1717. HTT 4.3.1.11
1718. HTT 5.4.1.2
1719. HTT 5.4.4.1
1720. HTT 5.4.4.2
1721. HTT 5.4.4.3
1722. HTT 5.5.3.6
1723. NS I.3.3
1724. NS I.3.5
1725. HA 7.3.2.5
1726. HA 7.3.2.6
1727. HA 7.3.2.7
1728. NS I.3.6
1729. HA 1.1.3.1
1730. HA 1.4.2.6
1731. HA 1.4.2.19
1732. HA 1.4.2.21
1733. HA 1.4.2.22
1734. HA 1.4.2.18
1735. HA 1.4.2.25
1736. HTT 1.2.13.8
1737. HTT 5.4.5.9
1738. HTT 2.2.2.7
1739. HTT 5.4.5.10
1740. HTT 5.4.5.11
1741. HTT 5.4.5.12
1742. HTT 5.4.5.13
1743. HTT 5.4.5.14
1744. HTT 5.4.5.15
1745. HTT 5.4.5.16
1746. HTT 5.5.3.11
1747. HA 1.4.4.4
1748. HA 1.4.4.5
1749. NS II.2.8
1750. NS II.2.14
1751. NS I.3.1; NS I.3.8; NS I.4.1; NS II.2.13 （相互参照）
1752. NS III.1.1
1753. NS III.1.2
1754. NS III.1.4
1755. HA 2.2.5.1
1756. HA 2.4.3.19
1757. HA 3.2.1.3
1758. HA 3.2.1.4
1759. HA 3.2.1.5
1760. HA 3.2.1.10
1761. HA 3.2.1.8
1762. HA 3.2.1.9
1763. HA 3.2.4.1
1764. HA 3.2.4.2
1765. HA 3.2.4.3
1766. HA 3.2.4.4
1767. HA 3.2.4.7
1768. NS IV.1.1
1769. HA 7.5.0.1
1770. HA 7.5.0.4
1771. NS IV.1.2

## 再開する場合の未展開キュー

上限のためこのキューは処理しない。証明未解決51項目と暗黙入力の照合は別の残件であり、この181項目だけを処理すれば完成するという意味ではない。停止中のKerodon8.2.3.4のフラグ確認と、上記の定義・式の所属項目の残件も必要。

1. Kerodon 8.2.3.5
2. Kerodon 8.2.2.13
3. Kerodon 8.2.3.2
4. Kerodon 8.2.3.9
5. Kerodon 3.1.6.1
6. Kerodon 7.1.2.8
7. Kerodon 4.5.2.10
8. Kerodon 4.5.2.9
9. Kerodon 5.3.8.6
10. Kerodon 4.9.3.9
11. Kerodon 5.1.5.16
12. Kerodon 7.4.4.12
13. Kerodon 7.4.4.6
14. Kerodon 7.4.4.11
15. Kerodon 7.1.1.17
16. Kerodon 4.9.5.7
17. Kerodon 7.3.2.1
18. Kerodon 7.3.2.3
19. Kerodon 7.2.3.6
20. Kerodon 6.2.2.6
21. Kerodon 7.1.1.8
22. Kerodon 8.4.6.3
23. Kerodon 7.3.3.15
24. Kerodon 4.9.4.18
25. Kerodon 5.1.1.7
26. Kerodon 7.6.2.41
27. Kerodon 7.2.2.12
28. Kerodon 7.1.1.6
29. Kerodon 5.5.3.13
30. Kerodon 5.5.3.11
31. Kerodon 7.4.5.22
32. Kerodon 7.7.0.4
33. Kerodon 3.4.0.6
34. Kerodon 7.6.3.12
35. Kerodon 7.7.0.2
36. Kerodon 7.6.2.40
37. Kerodon 6.2.1.19
38. Kerodon 6.2.1.17
39. Kerodon 6.2.6.1
40. Kerodon 6.1.2.11
41. Kerodon 6.2.1.14
42. Kerodon 4.2.4.10
43. Kerodon 4.6.7.6
44. Kerodon 7.1.2.3
45. Kerodon 7.1.2.6
46. Kerodon 7.1.8.9
47. Kerodon 7.1.8.15
48. Kerodon 7.1.3.19
49. Kerodon 4.9.1.15
50. Kerodon 7.1.6.9
51. Kerodon 2.1.2.17
52. Kerodon 1.1.2.1
53. Kerodon 1.1.1.4
54. Kerodon 1.5.6.8
55. Kerodon 1.3.7.5
56. Kerodon 4.3.3.23
57. Kerodon 3.3.1.5
58. Kerodon 3.3.1.7
59. Kerodon 3.3.3.13
60. Kerodon 3.3.5.9
61. Kerodon 4.1.2.10
62. Kerodon 1.4.5.4
63. Kerodon 4.4.2.7
64. Kerodon 4.8.2.5
65. Kerodon 4.8.2.7
66. Kerodon 4.8.1.4
67. Kerodon 4.8.2.6
68. Kerodon 4.8.2.19
69. Kerodon 4.6.1.13
70. Kerodon 3.5.3.18
71. Kerodon 4.7.6.17
72. Kerodon 4.7.6.18
73. Kerodon 3.5.3.17
74. Kerodon 3.5.1.17
75. Kerodon 3.1.8.12
76. Kerodon 3.5.1.10
77. Kerodon 4.7.1.2
78. Kerodon 4.2.6.3
79. Kerodon 1.1.6.8
80. Kerodon 3.1.7.23
81. Kerodon 3.5.1.31
82. Kerodon 3.1.5.7
83. Kerodon 3.1.5.12
84. Kerodon 2.4.6.9
85. Kerodon 4.6.8.20
86. Kerodon 5.5.3.5
87. Kerodon 2.4.3.1
88. Kerodon 5.4.8.7
89. Kerodon 5.6.2.16
90. Kerodon 2.4.4.15
91. Kerodon 4.6.5.1
92. Kerodon 4.6.5.2
93. Kerodon 4.6.7.25
94. Kerodon 4.6.7.26
95. Kerodon 4.6.7.22
96. Kerodon 4.6.7.23
97. Kerodon 2.4.3.8
98. Kerodon 2.4.5.2
99. Kerodon 2.4.4.10
100. Kerodon 2.4.4.16
101. Kerodon 2.4.6.13
102. Kerodon 1.2.1.3
103. Kerodon 1.2.1.5
104. Kerodon 1.2.1.4
105. Kerodon 5.6.4.6
106. Kerodon 5.6.4.7
107. Kerodon 5.6.4.3
108. Kerodon 5.6.2.14
109. Kerodon 7.5.5.7
110. Kerodon 7.5.5.1
111. Kerodon 7.5.4.13
112. Kerodon 7.1.8.13
113. Kerodon 7.3.8.5
114. Kerodon 8.1.2.15
115. Kerodon 8.2.2.4
116. Kerodon 5.6.6.20
117. Kerodon 7.3.6.5
118. Kerodon 7.3.8.10
119. Kerodon 4.5.5.5
120. Kerodon 5.1.4.19
121. Kerodon 5.1.1.16
122. Kerodon 3.3.5.6
123. Kerodon 3.3.4.8
124. Kerodon 3.3.3.18
125. Kerodon 6.3.1.23
126. Kerodon 6.3.2.11
127. Kerodon 3.4.1.16
128. Kerodon 5.3.5.1
129. Kerodon 5.3.3.20
130. Kerodon 5.3.4.10
131. Kerodon 5.3.2.18
132. Kerodon 5.3.4.8
133. Kerodon 5.3.2.9
134. Kerodon 7.5.4.1
135. Kerodon 7.5.2.11
136. Kerodon 7.5.5.15
137. Kerodon 7.5.2.8
138. Kerodon 5.6.6.17
139. Kerodon 7.5.4.5
140. Kerodon 5.3.4.1
141. Kerodon 9.1.6.12
142. Kerodon 9.1.6.9
143. Kerodon 7.5.5.6
144. Kerodon 7.5.6.6
145. Kerodon 7.5.4.2
146. Kerodon 7.2.1.19
147. Kerodon 8.5.1.8
148. Kerodon 7.3.3.20
149. Kerodon 7.1.1.11
150. Kerodon 8.3.2.9
151. Kerodon 8.2.6.1
152. Kerodon 8.3.2.8
153. Kerodon 8.2.1.5
154. Kerodon 7.3.4.7
155. Kerodon 7.3.4.3
156. Kerodon 7.2.2.5
157. Kerodon 7.3.3.17
158. Kerodon 8.3.3.15
159. Kerodon 8.4.1.16
160. Kerodon 8.4.1.18
161. Kerodon 7.3.6.12
162. Kerodon 8.5.2.7
163. Kerodon 8.5.2.9
164. Kerodon 8.5.5.4
165. Kerodon 8.5.6.16
166. Kerodon 8.5.6.17
167. Kerodon 5.1.4.14
168. Kerodon 7.4.5.11
169. Kerodon 7.4.5.12
170. Kerodon 7.4.6.1
171. Kerodon 4.6.1.6
172. Kerodon 6.3.2.1
173. Kerodon 6.3.2.13
174. Kerodon 6.3.1.16
175. Kerodon 8.6.6.1
176. Kerodon 8.6.5.2
177. Kerodon 8.3.5.3
178. Kerodon 8.2.0.3
179. Kerodon 8.2.1.3
180. Kerodon 8.2.3.7
181. Kerodon 8.2.2.11

<details>
<summary>旧版の不在97項目：除外理由を未認証</summary>

- HA 2.1.4.4
- HA 2.1.4.6
- HA B.0.19
- HA B.0.20
- HA B.0.26
- HA B.1.1
- HA B.1.2
- HA B.1.4
- HA B.1.5
- HA B.1.6
- HA B.1.7
- HA B.1.9
- HA B.1.10
- HA B.1.11
- HA B.1.12
- HA B.1.13
- HA B.1.14
- HA B.2.2
- HA B.2.3
- HA B.2.4
- HA B.2.7
- HA B.2.9
- HA B.2.11
- HA B.3.1
- HA B.3.2
- HA B.3.4
- HA B.3.5
- HA B.3.6
- HA B.3.7
- HA B.3.14
- HA B.3.15
- HA B.3.17
- HA B.3.18
- HA B.3.19
- HA B.3.20
- HA B.3.21
- HA B.4.1
- HA B.4.2
- HA B.4.5
- HA B.4.8
- HA B.4.9
- HA B.4.10
- HA B.4.11
- HA B.4.12
- HTT 2.1.2.7
- HTT 2.3.2.1
- HTT 2.3.2.4
- HTT 2.4.1.5
- HTT 2.4.2.10
- HTT 2.4.3.2
- HTT 3.1.3.5
- HTT 3.1.3.6
- HTT 3.1.3.7
- HTT 3.3.4.6
- HTT 4.1.3.2
- HTT 4.2.1.5
- HTT 5.4.6.2
- HTT 5.4.6.3
- HTT 5.4.7.1
- HTT 5.4.7.2
- HTT 5.4.7.10
- HTT A.1.2.5
- HTT A.1.2.7
- HTT A.1.2.8
- HTT A.1.5.3
- HTT A.1.5.5
- HTT A.1.5.6
- HTT A.1.5.7
- HTT A.1.5.8
- HTT A.1.5.9
- HTT A.1.5.10
- HTT A.1.5.11
- HTT A.1.5.12
- HTT A.1.5.13
- HTT A.2.1.1
- HTT A.2.3.1
- HTT A.2.4.2
- HTT A.2.4.4
- HTT A.2.6.1
- HTT A.2.6.2
- HTT A.2.6.5
- HTT A.2.6.6
- HTT A.2.6.7
- HTT A.2.6.8
- HTT A.2.6.9
- HTT A.2.6.10
- HTT A.2.6.12
- HTT A.2.6.14
- HTT A.2.6.15
- HTT A.2.8.2
- HTT A.2.9.26
- HTT A.2.9.27
- HTT A.3.1.1
- HTT A.3.1.7
- HTT A.3.3.3
- HTT A.3.7.1
- HTT A.3.7.3

</details>
