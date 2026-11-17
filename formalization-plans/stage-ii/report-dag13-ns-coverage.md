# DAG XIII・NS の対応表：完了報告

2026-11-16、⑤a。指示：`p0-section-map.md` §1、`p0-plan-draft.md` §6。
main **55f6cfbea** から枝 `research/dag13-ns-coverage`、worktree `../SerrePositivity-dag13-ns-coverage` を作成。
main・旧 `math/bs-impl` では編集・ビルドしていない。M14 の Lean は再開していない。

## 1. 出力と範囲

- [DAG XIII](../../research/dag13-coverage/README.md)：[全見出し](../../research/dag13-coverage/toc.md)、[全項目](../../research/dag13-coverage/items.csv)、[照合集計](../../research/dag13-coverage/review/summary.md)。
- [NS](../../research/ns-coverage/README.md)：[全見出し](../../research/ns-coverage/toc.md)、[全項目](../../research/ns-coverage/items.csv)、[照合集計](../../research/ns-coverage/review/summary.md)。
- `research/bibliography.json` に **DAGXIII**・**NS** を追加し、`bulk_citation_registry.py --write` で `Util/Citation.lean` を生成。

両文献を別々の項目として保持し、同じ内容でも統合していない。P⁰ 関係の DAG XIII §1.1・§2.1・§2.2（59 項目）、NS I.1・I.3・III.1・IV.1（53 項目）を先に、その後は残り 431 項目を照合した。各文献の照合順は claim-evidence.json に保存。

HA と同じ CSV の列を使用。items.csv は原項目の台帳、**状態の正本は review/*.csv**。items の status・declarations・reason は空欄のままとし、状態を二重管理しない。kerodon 列には確認した同内容の他文献の番号を記入し、特殊化・片方向・成分の場合はその範囲も記した。証明の依存先はこの列へ混ぜていない。

## 2. 版と採取

| 文献 | 指定版 | PDF 頁 | 番号付き項目 |
| --- | --- | ---: | ---: |
| DAG XIII | 2011-12-15 | 106 | 290 |
| NS | arXiv:1707.01799v2 | 169 | 253 |

原典：[Lurie, DAG XIII](https://www.math.ias.edu/~lurie/papers/DAG-XIII.pdf)、[Nikolaus–Scholze v2](https://arxiv.org/pdf/1707.01799v2)。PDF の SHA-256 は toc.md・edition.json・bibliography.json に記録。PDF と全抽出テキストはコミットしない。
NS は arXiv ヘッダが 2018-09-07、本文の Date が 2018-09-10 で、両方を記した。

採取上の確認：

- DAG XIII の章導入の番号は **1.0.1〜3、2.0.5〜7、3.0.18**。原典にない欠番を埋めない。
- DAG XIII の 3.5.15・3.6.5 は番号の直後に人名が続く項目。本文の再掲・引用・Proof of … を追加の項目として数えない。
- NS の導入 **1.1〜1.7** と **I.1.1〜I.1.13** を区別。Appendix は A・B・C の項目番号を採用。
- NS **I.3.7 は Definition**。pdftotext の読み順で番号が前の行へ分離する箇所を原頁 24 と照合した。
- 各項目の PDF 頁・layout 行・kind を source-items.csv に記録。別の raw 抽出ともラベルを突き合わせ、番号付き環境以外の引用を除いた。

## 3. 照合の集計と意味

| 文献 | own | mathlib | both | partial | none | 合計 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| DAG XIII | 0 | 1 | 0 | 13 | 276 | 290 |
| NS | 0 | 0 | 0 | 5 | 248 | 253 |
| 合計 | 0 | 1 | 0 | 18 | 524 | 543 |

未照合・unsure は 0。これは原典と**宣言ソースの型の紙の照合**であり、追加の kernel probe・公理監査は行っていない。依頼が登録生成以外の Lean 実行を範囲外としているためで、axioms は空欄。found はソースの宣言・型を確認した意味で使用した。型の断片・セクション変数の文脈・パス・行・SHA を source-types.json に保存し、kernel が展開した完全な型や公理一覧とは区別する。

partial は原典の成分・特殊化・強い仮定での結論が直接得られるものに限った。たとえば：

- DAG XIII 2.1.16：安定準圏の hC の加法性と有限双積。全相対 norm による半加法性との比較は含まれない。
- DAG XIII 2.1.22：通常の線形表現の作用の和と左右不変性。原典第二段落のこの主張の成分で、指定された相対 norm との一致ではない。
- DAG XIII 3.2.10：Mathlib の profinite 群と連続群準同型の圏が一致。3.2.12 は有限商の逆極限表示の部分までで、Pro(FinGp) との全圏同値ではない。
- NS I.1.5：厳密 Ω スペクトル作用から来る図式について、元の hG が native な極限。全 coherent 作用・全関手版・orbit は含まれない。
- NS A.2：底上の coCartesian 辺保存条件とその全部分関手圏。inert のみを保つ lax 条件と対称モノイダル構造の全定義は含まれない。

`cyclicTateComplex`・誘導周期複体の消滅・混合色の自由性・May の P⁰ は、native な norm/Tate・DAG の指定 P⁰ との比較定理を持たない。そのため、たとえば DAG XIII 2.1.23・2.1.25・2.2.2〜7、NS I.1.13・III.1.1 の対応をそれだけで partial にしていない。原典の一般性を計算模型で置き換える計画にもしていない。

原典の問題提起・注意・文献への帰属も番号付き項目として残した。none は記録した範囲の対応宣言を確認できなかったという判定で、数学的に証明できないという意味ではない。検索語・候補の型と不一致の理由を review/check/ に保存した。

直接の文献名付きの言及は DAG XIII が Lean 58 件・計画 94 件、NS が Lean 0 件・計画 32 件。節だけの参照や省略された文献名を推測で項目へ配っていない。この限定した採取範囲で、原典にない引用番号は両文献とも 0 件。

## 4. 既存の表との食い違い・検収の候補

既存の **HA・HTT・Kerodon の対応表、旧 P⁰ 地図は変更していない**。

1. HA 6.1.6.1・6.1.6.2 は旧 review で none。一方、今回の DAG XIII 1.1.1・2.1.1 / NS I.1.2 は、通常圏の nerve の場合の Fun の表示だけを component とした。左右 Kan 随伴があるという判定ではない。DAG XIII 2.1.2 / NS I.1.5 では native Sp の厳密作用図式の極限の特殊な場合も記録した。同内容の旧 HA 行の成分の数え方・更新要否は調整役の検収に渡す。
2. 旧 `research/p0-lurie/map/（data.json・template.html）` の DAG XIII 2.1.12 は preadditive_ho を根拠に partial。しかし、その型は定義に必要な全相対 norm の可逆性を述べないので、今回の定義行は none。hC の加法性は原典が明記する 2.1.16 の成分に付けた。
3. 旧 P⁰ 地図の DAG XIII 2.2.4・2.2.7 の partial は、BE の arity 作用・May の別演算の計算を指す。今回の原典対応では、指定された DAG の構成との一致がないため none。2.2.1 の partial も、今回対応させた成分は EG の underlying Čech 模型で、全拡大冪の構成ではない。
4. 旧 P⁰ 地図の NS I.1.1 の proved は定義全体を覆うと読めるが、今回確認した直接の成分は (i) の pointed/zero object。NS が (iv) で使う additivity・全有限極限余極限・loop 同値という定義全体との比較を含めず partial とした。
5. 旧地図の chain/ref は今回の status の語彙ではない。鎖模型を紹介する行を原典項目の partial へ機械的に変換しない。
6. B3 による行番号の移動がある。例：HA review の preadditive_ho は旧行 35、現ソースは 37。hasFiniteBiproducts_ho は旧行 28、現ソースは 30。今回の宣言欄は現パス・行で採取した。
7. DAG XIII 本文の `A.…` は 2011 年当時の HA を指す。現在の 2017 年 HA の同じ数字にそのまま結ばない。とくに Example 2.2.5 が引く A.7.1.2.4 と現 HA 4.8.4.1 の関係は、証明の引用と原項目そのものの同内容対応を区別し、未確認の番号翻訳を kerodon 列へ足していない。

## 5. 登録と検証

文献レジストリは 25 → **27 keys**。Citation.lean の差分は生成ブロックへの **4 行追加だけ**。

対象ビルド：

```sh
zsh scripts/refactor/with_build_lock.sh --class impl --wait 3600 -- \
  lake build SerrePositivity.Util.Citation \
    SerrePositivity.CommutativeAlgebra.DeRham.Graded
```

**成功**。Lake は依存を含め 1,278 jobs と表示し、変更した Citation と直接 import する Graded の二本をビルドした。鍵はこの一回の build だけに使用し、終了時に返した。root ビルド・大きな監査・常駐セッションは行っていない。
Citation.lean:201 と Graded.lean:68 の既存の 100 字超 linter 警告が残る。Citation の該当行は今回の生成ブロック外で、Graded は未変更。依頼の Lean 変更範囲を広げていない。

以下も成功：

- `bulk_citation_registry.py --check`：27 keys が一致。
- `extract_inventory.py --book dag13 --pdf …`：指定 SHA の PDF から 290 個の番号・kind・節・頁・行が一致。
- `extract_inventory.py --book ns --pdf …`：同じく 253 個が一致。
- `audit.py`：全 543 番号の一意性、台帳と review の全件一致、正しい節の範囲、理由・宣言の参照、ソース SHA、引用件数、優先節の照合順、登録以外の Lean 差分 0、既存三表の差分 0 を確認。
- `git diff --check`：空白エラーなし。

これらの Python 検査は表と証拠の整合性の検査であり、none の数学的な判定を自動証明するものではない。

## 6. 取り込み点・停止

この報告と新しい二つの対応表、bibliography.json、生成された Citation.lean を一つのコミットへまとめる。
新しいモジュールの入口・BS 監査への登録は不要。既存表・HTML 地図の更新は調整役の持ち分として残す。
依頼された報告をコミットしたところで停止し、次の指示を待つ。
