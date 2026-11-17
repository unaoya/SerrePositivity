# Archive の数学的内容の確認（AR-W1）

2026-11-17。Archive を変更せず、数学を残す必要と旧経路の保存を分けて検討した紙。Lean・ビルド・kernel 検証は行っていない。

## 集計

全1,871本・109,913行、85群。FilteredExchange は1,726本・96,551行、70群。

| 推奨 | 群 | 本数 | 行数 |
| --- | ---: | ---: | ---: |
| 戻す | 2 | 5 | 320 |
| 材料として残す | 10 | 161 | 13,171 |
| 消してよい | 6 | 69 | 5,780 |
| 判断できない | 67 | 1,636 | 90,642 |
| 計 | 85 | 1,871 | 109,913 |

「判断できない」が大半である。主要型を読んで群の数学を記述したが、特定の古いモデルを保持する比較式を現 API に完全に翻訳できるか、未照合の補助定理に再利用価値があるかを確定できなかった。参照がないこと・行数・sorry がないことを削除の根拠にはしていない。この67群について削除可能と結論した紙ではない。

## ファイル

- `groups.csv`：指定12列。各群3〜7個、計420個の主要宣言/匿名 example を取り上げ、仮定と結論を日本語で記した。`live_counterpart` の同じ主張・一方向・関連する一般定理を区別する。空欄は同じ型の対応を確定できなかった意味。
- `filtered-exchange-inventory.md`：FilteredExchange の群分けと主要宣言のソース位置。全ファイルの所属は git 外の inventory.json にある。
- `kerodon-rows.md`：Archive を指す4行と、理由だけの言及1行。9.1.1.20 の own を partial とする案。他3行と9.1.8.11は partial 維持の案。対応表は変更していない。

## 判断の要点

### 戻す候補は5本

`FE/FilteredCriterionCore` の3本は、filtered/κ-filtered の判定の逆向きと Kan 複体の filtered ⇔ 可縮を含む。P⁰ 閉包の Kerodon 9.1.1.18・9.1.5.7 を補う候補。本体の対角 cofinality と coslice の弱可縮性は必要方向で、Archive の iff と同じではない。κ版では正則性の仮定があり、原典の任意の無限κの全同値に達したとはしていない。

`FE/SliceRestriction` の2本は、準圏内の図式を単射で制限した slice の right fibration 性と固定頂点の錐空間の Kan fibration 性。P⁰ 閉包の Kerodon 4.3.6.12 の右側を補う。本体の coslice/left 側を同じ主張とは数えない。

復帰先はそれぞれ `Kerodon/LargeInfinityCategories/FilteredInfinityCategories/`、`Kerodon/TheHomotopyTheoryOfInfinityCategories/TheSliceAndJoinConstructions/` の現在の名前空間を想定する。これは置き場所の提案であって、import 修復・復帰・コンパイルを行ったものではない。

### 旧交換経路を一括で戻す根拠はない

本体の `smallSpaceFilteredColimit_map_isLimit_finite` は一般の filtered 準圏Bと全有限形状の極限錐の保存を扱い、`coherentFilteredLimitExchangeShape_finite` は元の指定された点ごとの錐族へ戻す。Archive の多くは、旧 unstraightening・pointed fiber・native/coherent colimit モデルの間の具体的な同型と座標等式である。

たとえば `coherentCompletedLimit_iff_colimitFunctor` は、点ごとの余極限性 hc を仮定した二つの完成方法の極限性の同値で、これだけで有限極限保存を証明する定理ではない。一方 `coherentCospanNativeLimitCone_isLimit` は、filtered B と各点の極限性の下で元の余極限頂点を持つ native cospan の極限錐を作る、実質的な交換の一部分。単なる全件の接頭辞処理で同じ評価にはしなかった。

`Cospan`・`PullbackFiber`・`CoherentCospanNative`・`FiberwisePullback` の4群は、[Kerodon 9.1.5.7](https://kerodon.net/tag/05XW) の引き戻し交換の証明に対し、有限族を同じ fiber へ移す・境界を固定する・指定頂点の錐を輸送する材料として残す案。現在の一般交換を得るための不足とはしていない。旧モデルの比較に必要な依存部品が別群にあるので、この4群だけを取り出して今すぐビルドできるとは言えない。

### DG の68本は一般論の本体と検査を区別する

`Archive/DifferentialGraded/Checks/U12e/` の68本には、匿名 example 261個と名前付き定理17個がある。example は本体の dg cell・導来拡大/制限・中間圏変更・単位/結合子・tria の型を検査する。名前付き17個も ZMod 2、特定次数、自然変換の成分への特殊化であり、使っている本体の一般定理の型と並べて確認した。標数2の例があることを、一般論が Archive だけにあることと取り違えない。

これら5群は数学の喪失という観点では「消してよい」。例の組や公理表示を検査資産として保持する運用価値は別にある。WIP の RelativeFiller 1本も、本体の任意の単射に対する相対ホモトピー比較を pushout-product に適用する wrapper なので、同じ観点で消してよい。

### 条件付き降下と診断・WIP

DescentConditional 67本は、モデル圏・cofibrantly generated・テンソル Quillen 条件や cofibration=mono、既に満たす Čech 降下を入力した比較である。`FiniteZariskiCechDescent` は法則を要求する Prop であり、その法則を任意の前層について証明してはいない。本論文補題3.2・3.3等の docstring を、BS や K の番号の定理の証明と置き換えない。K 地図の maps/paper/items.csv で3.2・3.3は required だが none とされており、係数 L 自身の転送とその階数式・降下の構成が不足する。そこで6群は、この2補題の計算材料として残す案とした。一般枠の仮定を L について供給できるとは言っていない。既存の instance 合成失敗の記録から、模型構造の仮定が論理的に矛盾するとまでは言えない。

DGκ診断4本は実際の native nerve 上の関手作用を記述するが、P⁰・BS・K に不可欠な項目を確定できない。`scripts/refactor/check_cleanup_c2.lean` に import があり、利用者ゼロとは書かない。DescentConditional は `scripts/archive/audit_kst_descent_conditional.lean` が import する。WIP の6本は保存元と内容を WIP/README でも照合したが、保存経緯だけで数学の必要性を決めていない。

## 調べ方

1. `.lean` を対象として、各ファイルを一群に割り当てた。初回の途中コミット `258ca0023` は83群・うち FilteredExchange 68群。その後、数学的に復帰候補となる3本と2本を混合群から分離し、最終85群・70群にした。分離前の `FilteredCriteria` から `FilteredCriterionCore`、`ConeLimit` と `SliceOpposite` から `SliceRestriction` を切り出した。本数・行数の総計は変わらない。
2. CoherentColimit と CoherentCospan は三語目の接頭辞まで分け、その他は接頭辞と同じ F2 名前空間・import の依存、共通の数学的操作でまとめた。各群の3〜7個の主要型と周囲の variable・型クラス・定義の右辺を読み、型が無条件か、条件付きか、同型か単なる等式かを区別した。全1,871本の証明を逐行で査読したものではない。
3. 現本体33,542ファイルを読み取り、主要名の宣言・import を検索した。同名は候補とするだけで、`relativeFunctorPost_overPre` や一般的な `comparison` のような別の型を自動的に対応させていない。重要箇所は別名の一般定理も探して型を並べた。既存対応表、P⁰ 閉包、BS の items と K の maps の正本の範囲を照合した。K の紙の3.2・3.3が required であることは確認したが、Archive がその主張を無条件に供給するとは判定しなかった。BS の個別必須項目は確定していない。
4. `literature` はソースの番号/Tag と既存 review の番号、または確認した原典の証明への対照に限る。直接引用と証明材料としての対照をセル内で区別し、番号のない群は空欄のまま。`targets` の関連・必須・未確定も区別する。9.1.1.20は既存表にあるが今回のP⁰閉包にはない。
5. コメントと文字列を外した字句上の `sorry` は全群0、`axiom` 宣言も検出0。`#print axioms` の文字は実際の新しい公理宣言と数えない。これは推移的な公理依存がないことや、古い型が現在も通ることを示さない。

## import の読み方

`imports_live` は群内から参照する **ユニークなモジュール名** を数える。同じ import が複数ファイルにあっても一つ。現本体とロックに対応する隣接 worktree の Mathlib ソースを別に数え、Archive 間は別記した。

- 「現名あり」：そのパスにソースがある。中の API の型やコンパイルの互換性までは保証しない。
- 「改名候補あり」：旧パスはなく、現在の本体に同じ末尾のモジュール名がある。候補全件とパスは証拠の imports-status.json にある。名前だけで改名確定とはせず、本文復帰の際の追従調査が要る。
- 「所在未確定」：旧パスも同じ末尾の候補もない。消失と断定しない。Descent の `Mathlib.CategoryTheory.WideSubcategory` が1件、WIP/SpectraUncurry に元の KST/Spectra の3件があり、後者は Archive/WIP に本文が保存されている。

現本体の33,542ファイルには Archive の直接 import は見つからなかったが、上記2つの監査スクリプトは別。現在の entrypoint からの import 閉包・推移的依存の kernel 検証を実行した結果ではない。

## 証拠と限界

大きい抽出結果は `~/serre-evidence/cited/archive-review/`。目録だけを `evidence/cited/archive-review/manifest.json` にコミットする。ファイルごとの割当て・行数・ハッシュ・宣言の型、選んだ型の文脈、現本体との比較、17個のDG特殊化の比較、import の候補、原典取得結果・検査結果を保存した。

同じ主張が見つからなかったことは存在しないことの証明ではない。67群の未知の価値を「旧経路だから不要」とは処理せず、対象となる型と判定できない理由を残した。Archive・本体・対応表は未変更。この紙は削除や復帰の実行指示ではなく、調整役とユーザーの判断材料である。
