# P⁰閉包の未掲載Kerodon項目を追加（⑤d、2026-11-16）

ユーザー指示11-16に従い、main `671f6eafe` から枝 `codex/kerodon-p0-inventory` を作った。P⁰の `research/p0-lurie/item-closure/items.csv` のKerodon行のうち、基準mainの `research/kerodon-coverage/items.csv` と `review/*.csv` のどちらにもない番号だけを対象とする。

## 結果と範囲

未掲載 **531項目**を追加し、`items.csv` は既存3,553項目＋未照合531項目＝ **4,084項目**になった。既存3,553行はヘッダ・順序・全フィールド・引用符・改行を含めてバイト単位で保持した。reviewの3,553行は追加・変更していない。

| 種類 | 追加項目数 |
|---|---|
| Construction | 1 |
| Corollary | 2 |
| Example | 170 |
| Exercise | 15 |
| Lemma | 4 |
| Proposition | 5 |
| Remark | 332 |
| Warning | 2 |
| 合計 | 531 |

追加したのは書誌情報だけである。状態、宣言、confidence、lean_citationsは空欄。空欄を `none`・`partial` と判定したわけではない。③-a・③-bの取り込み後の対応表更新でまとめて照合する。Leanの追加・変更・ビルド、宣言検索、実装状態の判定は行っていない。

## 既存の列構成を保つ方法

- `items.csv` の既存8列を変更せず末尾に531行を追記した。見出しは既存の `note` に置き、`subsection_tag` には原典パンくずのSubsection Tagだけを置く。Section直下の項目ではこの欄を空のままにする。
- 書誌5列の `p0-added-items.csv` を追加した。列は `number,kind,title,section,tag`。`section` は原典パンくずの直近のSubsection、なければSectionの番号。`tag` は項目自身のTagである。状態・宣言の複製は持たない。
- 項目Tagの目録 `item-tags.csv` では531項目中516項目は既掲載のため変更せず、未掲載15項目の `number,kind,tag` だけを末尾に追加した。既存6,613行をバイト単位で保持し、計6,628行となった。
- `review/`、既存の集計、閉包とその過去版、地図、Leanは変更しない。既存の集計3,553項目は従来の照合対象についての集計で、新規531項目は含まない。

## 原典と検収

見出し・種類・番号は各公式ページ `https://kerodon.net/tag/<tag>` の番号つき環境の見出しから採取した。見出しに名前がない場合は原典どおり「Remark 1.1.0.8」等とし、本文の要約や新しい標題を作っていない。節とそのTagは同じページのパンくずから得た。項目Tagは既存目録、未掲載15件は前回閉包で原典から得たTagを照合した。原典本文・証明は表に複製しない。

確認に用いた531ページの `number tag HTML-SHA256` のLF区切り採取記録のSHA256は `cdac1e28922b2a5f68fea6d69033079394197f60fd990f8188a0c21e449c8cbf`。既存 `items.csv` のSHA256は `2cfc90d4f272da35d039e06590191a50243137ac410207fa54af8645668787e1`、既存 `item-tags.csv` は `4df5702571b08c9d39ef7e5ce22ace983d7457ad343e77aea59704ffe266fbf2`。

CSVの列数・番号の一意性・追加番号集合の完全一致・531項目の種類と原典番号・Tag・節の一致・追加行の判定欄の空欄・既存行とreviewの不変を小さい検査で確認した。以下の「データ行」はヘッダを除く1始まりの通し番号であり、引用符内改行を含み得るCSVの物理行番号ではない。

## 追加した全531行

| items.csvデータ行 | 番号 | 種類 | 原典の見出し | 節 | 項目Tag |
|---|---|---|---|---|---|
| 3554 | 1.1.0.8 | Remark | Remark 1.1.0.8 | 1.1 | [000J](https://kerodon.net/tag/000J) |
| 3555 | 1.1.0.9 | Example | Example 1.1.0.9 (The Standard Simplex) | 1.1 | [04Z6](https://kerodon.net/tag/04Z6) |
| 3556 | 1.1.0.14 | Remark | Remark 1.1.0.14 (Simplicial Subsets) | 1.1 | [000P](https://kerodon.net/tag/000P) |
| 3557 | 1.1.1.7 | Remark | Remark 1.1.1.7 (Relations Among Face Operators) | 1.1.1 | [04FP](https://kerodon.net/tag/04FP) |
| 3558 | 1.1.2.6 | Remark | Remark 1.1.2.6 | 1.1.2 | [04ZN](https://kerodon.net/tag/04ZN) |
| 3559 | 1.1.2.8 | Example | Example 1.1.2.8 (Degenerate $2$-Simplices) | 1.1.2 | [04ZP](https://kerodon.net/tag/04ZP) |
| 3560 | 1.1.3.2 | Example | Example 1.1.3.2 | 1.1.3 | [04ZT](https://kerodon.net/tag/04ZT) |
| 3561 | 1.1.3.3 | Remark | Remark 1.1.3.3 | 1.1.3 | [04ZU](https://kerodon.net/tag/04ZU) |
| 3562 | 1.1.3.4 | Remark | Remark 1.1.3.4 | 1.1.3 | [04ZV](https://kerodon.net/tag/04ZV) |
| 3563 | 1.1.3.13 | Remark | Remark 1.1.3.13 | 1.1.3 | [002D](https://kerodon.net/tag/002D) |
| 3564 | 1.1.4.4 | Remark | Remark 1.1.4.4 | 1.1.4 | [0016](https://kerodon.net/tag/0016) |
| 3565 | 1.1.4.5 | Remark | Remark 1.1.4.5 | 1.1.4 | [0017](https://kerodon.net/tag/0017) |
| 3566 | 1.1.6.10 | Remark | Remark 1.1.6.10 | 1.1.6 | [001P](https://kerodon.net/tag/001P) |
| 3567 | 1.2.1.28 | Warning | Warning 1.2.1.28 | 1.2.1 | [00GY](https://kerodon.net/tag/00GY) |
| 3568 | 1.3.1.3 | Remark | Remark 1.3.1.3 | 1.3.1 | [002Q](https://kerodon.net/tag/002Q) |
| 3569 | 1.3.7.2 | Example | Example 1.3.7.2 | 1.3.7 | [00HL](https://kerodon.net/tag/00HL) |
| 3570 | 1.3.7.9 | Example | Example 1.3.7.9 | 1.3.7 | [00HT](https://kerodon.net/tag/00HT) |
| 3571 | 1.4.0.9 | Remark | Remark 1.4.0.9 | 1.4 | [01G8](https://kerodon.net/tag/01G8) |
| 3572 | 1.4.2.5 | Example | Example 1.4.2.5 | 1.4.2 | [003R](https://kerodon.net/tag/003R) |
| 3573 | 1.4.6.3 | Remark | Remark 1.4.6.3 (Two-out-of-three) | 1.4.6 | [004U](https://kerodon.net/tag/004U) |
| 3574 | 1.4.6.7 | Remark | Remark 1.4.6.7 | 1.4.6 | [004Y](https://kerodon.net/tag/004Y) |
| 3575 | 1.5.1.6 | Remark | Remark 1.5.1.6 | 1.5.1 | [005D](https://kerodon.net/tag/005D) |
| 3576 | 1.5.2.4 | Example | Example 1.5.2.4 (Non-Commuting Squares) | 1.5.2 | [005M](https://kerodon.net/tag/005M) |
| 3577 | 1.5.2.8 | Example | Example 1.5.2.8 (Commutative Squares in a Category) | 1.5.2 | [005Q](https://kerodon.net/tag/005Q) |
| 3578 | 1.5.2.9 | Example | Example 1.5.2.9 (Square Diagrams in an $\infty $-Category) | 1.5.2 | [005R](https://kerodon.net/tag/005R) |
| 3579 | 1.5.2.10 | Exercise | Exercise 1.5.2.10 | 1.5.2 | [005S](https://kerodon.net/tag/005S) |
| 3580 | 1.5.5.2 | Remark | Remark 1.5.5.2 | 1.5.5 | [006X](https://kerodon.net/tag/006X) |
| 3581 | 1.5.5.3 | Remark | Remark 1.5.5.3 | 1.5.5 | [02L0](https://kerodon.net/tag/02L0) |
| 3582 | 1.5.6.6 | Exercise | Exercise 1.5.6.6 | 1.5.6 | [01C3](https://kerodon.net/tag/01C3) |
| 3583 | 1.5.7.4 | Remark | Remark 1.5.7.4 | 1.5.7 | [00J7](https://kerodon.net/tag/00J7) |
| 3584 | 1.5.7.7 | Example | Example 1.5.7.7 (The Spine of a Simplex) | 1.5.7 | [00JA](https://kerodon.net/tag/00JA) |
| 3585 | 1.5.7.8 | Remark | Remark 1.5.7.8 (The Generalized Associative Law) | 1.5.7 | [00JB](https://kerodon.net/tag/00JB) |
| 3586 | 1.5.7.10 | Remark | Remark 1.5.7.10 | 1.5.7 | [01C4](https://kerodon.net/tag/01C4) |
| 3587 | 2.1.3.2 | Example | Example 2.1.3.2 (Cartesian Products) | 2.1.3 | [00CR](https://kerodon.net/tag/00CR) |
| 3588 | 2.1.5.16 | Example | Example 2.1.5.16 | 2.1.5 | [00DR](https://kerodon.net/tag/00DR) |
| 3589 | 2.1.7.2 | Example | Example 2.1.7.2 (Categories Enriched Over Sets) | 2.1.7 | [00EF](https://kerodon.net/tag/00EF) |
| 3590 | 2.1.7.4 | Remark | Remark 2.1.7.4 (Functoriality) | 2.1.7 | [00EH](https://kerodon.net/tag/00EH) |
| 3591 | 2.1.7.5 | Example | Example 2.1.7.5 (The Underlying Category of an Enriched Category) | 2.1.7 | [00EJ](https://kerodon.net/tag/00EJ) |
| 3592 | 2.2.0.3 | Remark | Remark 2.2.0.3 | 2.2 | [00EP](https://kerodon.net/tag/00EP) |
| 3593 | 2.2.0.6 | Example | Example 2.2.0.6 (Ordinary Categories) | 2.2 | [007W](https://kerodon.net/tag/007W) |
| 3594 | 2.2.4.14 | Example | Example 2.2.4.14 | 2.2.4 | [008P](https://kerodon.net/tag/008P) |
| 3595 | 2.2.5.4 | Example | Example 2.2.5.4 | 2.2.5 | [008Z](https://kerodon.net/tag/008Z) |
| 3596 | 2.2.5.7 | Example | Example 2.2.5.7 | 2.2.5 | [0093](https://kerodon.net/tag/0093) |
| 3597 | 2.3.1.8 | Remark | Remark 2.3.1.8 | 2.3.1 | [00A1](https://kerodon.net/tag/00A1) |
| 3598 | 2.3.1.15 | Example | Example 2.3.1.15 ($2$-Simplices of the Duskin Nerve) | 2.3.1 | [00A8](https://kerodon.net/tag/00A8) |
| 3599 | 2.3.2.4 | Example | Example 2.3.2.4 | 2.3.2 | [00AE](https://kerodon.net/tag/00AE) |
| 3600 | 2.4.1.4 | Example | Example 2.4.1.4 (The Underlying Category of a Simplicial Category) | 2.4.1 | [00JU](https://kerodon.net/tag/00JU) |
| 3601 | 2.4.1.12 | Remark | Remark 2.4.1.12 | 2.4.1 | [00K2](https://kerodon.net/tag/00K2) |
| 3602 | 2.4.2.2 | Example | Example 2.4.2.2 (Functor Categories) | 2.4.2 | [0323](https://kerodon.net/tag/0323) |
| 3603 | 2.4.2.4 | Example | Example 2.4.2.4 (Ordinary Categories as Simplicial Categories) | 2.4.2 | [00K6](https://kerodon.net/tag/00K6) |
| 3604 | 2.4.2.8 | Example | Example 2.4.2.8 (Strict Bicategories as Simplicial Categories) | 2.4.2 | [00KA](https://kerodon.net/tag/00KA) |
| 3605 | 2.4.2.9 | Remark | Remark 2.4.2.9 | 2.4.2 | [00KB](https://kerodon.net/tag/00KB) |
| 3606 | 2.4.3.2 | Remark | Remark 2.4.3.2 | 2.4.3 | [00KP](https://kerodon.net/tag/00KP) |
| 3607 | 2.4.3.8 | Remark | Remark 2.4.3.8 (Comparison with the Nerve) | 2.4.3 | [00KV](https://kerodon.net/tag/00KV) |
| 3608 | 2.4.3.9 | Example | Example 2.4.3.9 (Vertices and Edges of the Homotopy Coherent Nerve) | 2.4.3 | [00KW](https://kerodon.net/tag/00KW) |
| 3609 | 2.4.3.10 | Example | Example 2.4.3.10 ($2$-Simplices of the Homotopy Coherent Nerve) | 2.4.3 | [00KX](https://kerodon.net/tag/00KX) |
| 3610 | 2.4.3.11 | Example | Example 2.4.3.11 (Comparison with the Duskin Nerve) | 2.4.3 | [00KY](https://kerodon.net/tag/00KY) |
| 3611 | 2.4.4.6 | Example | Example 2.4.4.6 (The Path Category of a Simplex) | 2.4.4 | [00L6](https://kerodon.net/tag/00L6) |
| 3612 | 2.4.4.11 | Remark | Remark 2.4.4.11 | 2.4.4 | [00LB](https://kerodon.net/tag/00LB) |
| 3613 | 2.4.4.17 | Remark | Remark 2.4.4.17 | 2.4.4 | [00LG](https://kerodon.net/tag/00LG) |
| 3614 | 2.4.6.11 | Example | Example 2.4.6.11 | 2.4.6 | [00M6](https://kerodon.net/tag/00M6) |
| 3615 | 3.1.1.2 | Example | Example 3.1.1.2 | 3.1.1 | [00T2](https://kerodon.net/tag/00T2) |
| 3616 | 3.1.1.4 | Example | Example 3.1.1.4 | 3.1.1 | [01GE](https://kerodon.net/tag/01GE) |
| 3617 | 3.1.1.6 | Remark | Remark 3.1.1.6 | 3.1.1 | [00T5](https://kerodon.net/tag/00T5) |
| 3618 | 3.1.1.10 | Remark | Remark 3.1.1.10 | 3.1.1 | [00T7](https://kerodon.net/tag/00T7) |
| 3619 | 3.1.1.11 | Remark | Remark 3.1.1.11 | 3.1.1 | [01C5](https://kerodon.net/tag/01C5) |
| 3620 | 3.1.2.3 | Remark | Remark 3.1.2.3 | 3.1.2 | [00UK](https://kerodon.net/tag/00UK) |
| 3621 | 3.1.2.7 | Remark | Remark 3.1.2.7 | 3.1.2 | [00UN](https://kerodon.net/tag/00UN) |
| 3622 | 3.1.3.11 | Remark | Remark 3.1.3.11 | 3.1.3 | [01GJ](https://kerodon.net/tag/01GJ) |
| 3623 | 3.1.5.3 | Remark | Remark 3.1.5.3 (Homotopy Extension Lifting Property) | 3.1.5 | [014F](https://kerodon.net/tag/014F) |
| 3624 | 3.1.5.5 | Example | Example 3.1.5.5 | 3.1.5 | [00TV](https://kerodon.net/tag/00TV) |
| 3625 | 3.1.5.6 | Example | Example 3.1.5.6 | 3.1.5 | [00TW](https://kerodon.net/tag/00TW) |
| 3626 | 3.1.5.7 | Example | Example 3.1.5.7 | 3.1.5 | [00ZX](https://kerodon.net/tag/00ZX) |
| 3627 | 3.1.5.12 | Remark | Remark 3.1.5.12 | 3.1.5 | [02L1](https://kerodon.net/tag/02L1) |
| 3628 | 3.1.7.3 | Example | Example 3.1.7.3 | 3.1.7 | [00U3](https://kerodon.net/tag/00U3) |
| 3629 | 3.1.7.5 | Remark | Remark 3.1.7.5 | 3.1.7 | [00V1](https://kerodon.net/tag/00V1) |
| 3630 | 3.1.7.7 | Remark | Remark 3.1.7.7 (Two-out-of-Three) | 3.1.7 | [00U7](https://kerodon.net/tag/00U7) |
| 3631 | 3.1.7.16 | Remark | Remark 3.1.7.16 (Two-out-of-Three) | 3.1.7 | [00UD](https://kerodon.net/tag/00UD) |
| 3632 | 3.1.7.21 | Exercise | Exercise 3.1.7.21 | 3.1.7 | [00UE](https://kerodon.net/tag/00UE) |
| 3633 | 3.1.8.10 | Example | Example 3.1.8.10 (Path Fibrations) | 3.1.8 | [0101](https://kerodon.net/tag/0101) |
| 3634 | 3.1.8.11 | Exercise | Exercise 3.1.8.11 | 3.1.8 | [00UY](https://kerodon.net/tag/00UY) |
| 3635 | 3.2.2.16 | Remark | Remark 3.2.2.16 (Functoriality) | 3.2.2 | [00VZ](https://kerodon.net/tag/00VZ) |
| 3636 | 3.2.2.17 | Remark | Remark 3.2.2.17 (Homotopy Invariance) | 3.2.2 | [04GE](https://kerodon.net/tag/04GE) |
| 3637 | 3.2.4.2 | Example | Example 3.2.4.2 | 3.2.4 | [00XA](https://kerodon.net/tag/00XA) |
| 3638 | 3.2.4.8 | Exercise | Exercise 3.2.4.8 | 3.2.4 | [050S](https://kerodon.net/tag/050S) |
| 3639 | 3.2.4.10 | Remark | Remark 3.2.4.10 | 3.2.4 | [02L9](https://kerodon.net/tag/02L9) |
| 3640 | 3.2.4.17 | Remark | Remark 3.2.4.17 | 3.2.4 | [00WZ](https://kerodon.net/tag/00WZ) |
| 3641 | 3.3.1.2 | Exercise | Exercise 3.3.1.2 | 3.3.1 | [00XV](https://kerodon.net/tag/00XV) |
| 3642 | 3.3.2.2 | Remark | Remark 3.3.2.2 (Functoriality) | 3.3.2 | [00XK](https://kerodon.net/tag/00XK) |
| 3643 | 3.3.2.4 | Remark | Remark 3.3.2.4 (Functoriality) | 3.3.2 | [00XM](https://kerodon.net/tag/00XM) |
| 3644 | 3.3.2.7 | Remark | Remark 3.3.2.7 | 3.3.2 | [00XQ](https://kerodon.net/tag/00XQ) |
| 3645 | 3.3.2.9 | Example | Example 3.3.2.9 | 3.3.2 | [00XS](https://kerodon.net/tag/00XS) |
| 3646 | 3.3.3.5 | Example | Example 3.3.3.5 | 3.3.3 | [00YA](https://kerodon.net/tag/00YA) |
| 3647 | 3.3.3.6 | Remark | Remark 3.3.3.6 | 3.3.3 | [05P0](https://kerodon.net/tag/05P0) |
| 3648 | 3.3.4.6 | Example | Example 3.3.4.6 | 3.3.4 | [00YX](https://kerodon.net/tag/00YX) |
| 3649 | 3.3.6.3 | Example | Example 3.3.6.3 | 3.3.6 | [00ZD](https://kerodon.net/tag/00ZD) |
| 3650 | 3.3.7.2 | Example | Example 3.3.7.2 | 3.3.7 | [0511](https://kerodon.net/tag/0511) |
| 3651 | 3.3.7.3 | Remark | Remark 3.3.7.3 | 3.3.7 | [0512](https://kerodon.net/tag/0512) |
| 3652 | 3.4.0.6 | Remark | Remark 3.4.0.6 (Homotopy Fibers) | 3.4 | [0328](https://kerodon.net/tag/0328) |
| 3653 | 3.4.1.3 | Example | Example 3.4.1.3 | 3.4.1 | [010U](https://kerodon.net/tag/010U) |
| 3654 | 3.4.1.4 | Example | Example 3.4.1.4 | 3.4.1 | [010S](https://kerodon.net/tag/010S) |
| 3655 | 3.4.1.10 | Remark | Remark 3.4.1.10 | 3.4.1 | [010Z](https://kerodon.net/tag/010Z) |
| 3656 | 3.4.2.12 | Example | Example 3.4.2.12 | 3.4.2 | [011D](https://kerodon.net/tag/011D) |
| 3657 | 3.4.5.2 | Remark | Remark 3.4.5.2 | 3.4.5 | [0122](https://kerodon.net/tag/0122) |
| 3658 | 3.4.5.3 | Remark | Remark 3.4.5.3 | 3.4.5 | [0123](https://kerodon.net/tag/0123) |
| 3659 | 3.4.6.2 | Remark | Remark 3.4.6.2 | 3.4.6 | [012D](https://kerodon.net/tag/012D) |
| 3660 | 3.5.1.5 | Remark | Remark 3.5.1.5 (Homotopy Invariance) | 3.5.1 | [04GP](https://kerodon.net/tag/04GP) |
| 3661 | 3.5.1.10 | Example | Example 3.5.1.10 | 3.5.1 | [0519](https://kerodon.net/tag/0519) |
| 3662 | 3.5.1.14 | Remark | Remark 3.5.1.14 | 3.5.1 | [04H0](https://kerodon.net/tag/04H0) |
| 3663 | 3.5.1.17 | Example | Example 3.5.1.17 | 3.5.1 | [051C](https://kerodon.net/tag/051C) |
| 3664 | 3.5.1.19 | Remark | Remark 3.5.1.19 | 3.5.1 | [04HJ](https://kerodon.net/tag/04HJ) |
| 3665 | 3.5.3.21 | Remark | Remark 3.5.3.21 | 3.5.3 | [052L](https://kerodon.net/tag/052L) |
| 3666 | 3.5.7.6 | Remark | Remark 3.5.7.6 | 3.5.7 | [054U](https://kerodon.net/tag/054U) |
| 3667 | 3.5.9.2 | Example | Example 3.5.9.2 | 3.5.9 | [0560](https://kerodon.net/tag/0560) |
| 3668 | 3.5.9.9 | Remark | Remark 3.5.9.9 | 3.5.9 | [0567](https://kerodon.net/tag/0567) |
| 3669 | 3.6.1.2 | Example | Example 3.6.1.2 | 3.6.1 | [0132](https://kerodon.net/tag/0132) |
| 3670 | 3.6.1.3 | Remark | Remark 3.6.1.3 | 3.6.1 | [0133](https://kerodon.net/tag/0133) |
| 3671 | 3.6.1.4 | Remark | Remark 3.6.1.4 | 3.6.1 | [0134](https://kerodon.net/tag/0134) |
| 3672 | 3.6.1.6 | Remark | Remark 3.6.1.6 | 3.6.1 | [0136](https://kerodon.net/tag/0136) |
| 3673 | 3.6.1.8 | Remark | Remark 3.6.1.8 | 3.6.1 | [0138](https://kerodon.net/tag/0138) |
| 3674 | 3.6.2.7 | Remark | Remark 3.6.2.7 | 3.6.2 | [013K](https://kerodon.net/tag/013K) |
| 3675 | 3.6.3.3 | Example | Example 3.6.3.3 | 3.6.3 | [013S](https://kerodon.net/tag/013S) |
| 3676 | 4.1.1.2 | Example | Example 4.1.1.2 | 4.1.1 | [01BB](https://kerodon.net/tag/01BB) |
| 3677 | 4.1.1.5 | Remark | Remark 4.1.1.5 | 4.1.1 | [01BE](https://kerodon.net/tag/01BE) |
| 3678 | 4.1.1.6 | Remark | Remark 4.1.1.6 | 4.1.1 | [01BF](https://kerodon.net/tag/01BF) |
| 3679 | 4.1.1.8 | Remark | Remark 4.1.1.8 | 4.1.1 | [01BH](https://kerodon.net/tag/01BH) |
| 3680 | 4.1.1.9 | Remark | Remark 4.1.1.9 | 4.1.1 | [01BJ](https://kerodon.net/tag/01BJ) |
| 3681 | 4.1.1.13 | Remark | Remark 4.1.1.13 | 4.1.1 | [01BL](https://kerodon.net/tag/01BL) |
| 3682 | 4.1.2.4 | Example | Example 4.1.2.4 | 4.1.2 | [01CH](https://kerodon.net/tag/01CH) |
| 3683 | 4.1.2.6 | Remark | Remark 4.1.2.6 (Pullbacks of Subcategories) | 4.1.2 | [01CK](https://kerodon.net/tag/01CK) |
| 3684 | 4.1.2.7 | Remark | Remark 4.1.2.7 | 4.1.2 | [01CL](https://kerodon.net/tag/01CL) |
| 3685 | 4.1.2.8 | Remark | Remark 4.1.2.8 | 4.1.2 | [01CM](https://kerodon.net/tag/01CM) |
| 3686 | 4.1.2.9 | Remark | Remark 4.1.2.9 | 4.1.2 | [01CN](https://kerodon.net/tag/01CN) |
| 3687 | 4.2.1.4 | Remark | Remark 4.2.1.4 | 4.2.1 | [01GU](https://kerodon.net/tag/01GU) |
| 3688 | 4.2.1.5 | Example | Example 4.2.1.5 | 4.2.1 | [014L](https://kerodon.net/tag/014L) |
| 3689 | 4.2.1.8 | Remark | Remark 4.2.1.8 | 4.2.1 | [014N](https://kerodon.net/tag/014N) |
| 3690 | 4.2.6.3 | Remark | Remark 4.2.6.3 (The Homotopy Extension Lifting Property) | 4.2.6 | [00TB](https://kerodon.net/tag/00TB) |
| 3691 | 4.3.2.5 | Example | Example 4.3.2.5 (Cones) | 4.3.2 | [0165](https://kerodon.net/tag/0165) |
| 3692 | 4.3.3.16 | Remark | Remark 4.3.3.16 | 4.3.3 | [016Z](https://kerodon.net/tag/016Z) |
| 3693 | 4.3.3.17 | Remark | Remark 4.3.3.17 | 4.3.3 | [0170](https://kerodon.net/tag/0170) |
| 3694 | 4.3.3.21 | Remark | Remark 4.3.3.21 | 4.3.3 | [02LH](https://kerodon.net/tag/02LH) |
| 3695 | 4.3.5.2 | Remark | Remark 4.3.5.2 | 4.3.5 | [017X](https://kerodon.net/tag/017X) |
| 3696 | 4.3.6.7 | Example | Example 4.3.6.7 | 4.3.6 | [02VL](https://kerodon.net/tag/02VL) |
| 3697 | 4.3.7.10 | Example | Example 4.3.7.10 | 4.3.7 | [0198](https://kerodon.net/tag/0198) |
| 3698 | 4.3.7.11 | Example | Example 4.3.7.11 | 4.3.7 | [02LJ](https://kerodon.net/tag/02LJ) |
| 3699 | 4.4.1.6 | Example | Example 4.4.1.6 | 4.4.1 | [01GV](https://kerodon.net/tag/01GV) |
| 3700 | 4.4.1.12 | Example | Example 4.4.1.12 (Replete Subcategories) | 4.4.1 | [01EX](https://kerodon.net/tag/01EX) |
| 3701 | 4.4.1.14 | Example | Example 4.4.1.14 | 4.4.1 | [01EY](https://kerodon.net/tag/01EY) |
| 3702 | 4.4.2.9 | Example | Example 4.4.2.9 | 4.4.2 | [02QX](https://kerodon.net/tag/02QX) |
| 3703 | 4.4.2.10 | Remark | Remark 4.4.2.10 | 4.4.2 | [019J](https://kerodon.net/tag/019J) |
| 3704 | 4.4.3.2 | Remark | Remark 4.4.3.2 | 4.4.3 | [01D1](https://kerodon.net/tag/01D1) |
| 3705 | 4.4.3.5 | Remark | Remark 4.4.3.5 (Functoriality) | 4.4.3 | [01D3](https://kerodon.net/tag/01D3) |
| 3706 | 4.4.4.5 | Remark | Remark 4.4.4.5 | 4.4.4 | [01DL](https://kerodon.net/tag/01DL) |
| 3707 | 4.5.1.4 | Remark | Remark 4.5.1.4 | 4.5.1 | [01DT](https://kerodon.net/tag/01DT) |
| 3708 | 4.5.1.7 | Remark | Remark 4.5.1.7 | 4.5.1 | [01DW](https://kerodon.net/tag/01DW) |
| 3709 | 4.5.1.13 | Example | Example 4.5.1.13 | 4.5.1 | [01E2](https://kerodon.net/tag/01E2) |
| 3710 | 4.5.1.17 | Remark | Remark 4.5.1.17 | 4.5.1 | [023B](https://kerodon.net/tag/023B) |
| 3711 | 4.5.1.18 | Remark | Remark 4.5.1.18 (Two-out-of-Three) | 4.5.1 | [01E5](https://kerodon.net/tag/01E5) |
| 3712 | 4.5.1.19 | Remark | Remark 4.5.1.19 | 4.5.1 | [01E6](https://kerodon.net/tag/01E6) |
| 3713 | 4.5.1.20 | Remark | Remark 4.5.1.20 | 4.5.1 | [01HB](https://kerodon.net/tag/01HB) |
| 3714 | 4.5.1.21 | Remark | Remark 4.5.1.21 | 4.5.1 | [01HC](https://kerodon.net/tag/01HC) |
| 3715 | 4.5.2.9 | Remark | Remark 4.5.2.9 | 4.5.2 | [03T6](https://kerodon.net/tag/03T6) |
| 3716 | 4.5.2.10 | Remark | Remark 4.5.2.10 | 4.5.2 | [03T7](https://kerodon.net/tag/03T7) |
| 3717 | 4.5.3.2 | Remark | Remark 4.5.3.2 | 4.5.3 | [0330](https://kerodon.net/tag/0330) |
| 3718 | 4.5.3.6 | Remark | Remark 4.5.3.6 | 4.5.3 | [0333](https://kerodon.net/tag/0333) |
| 3719 | 4.5.3.7 | Remark | Remark 4.5.3.7 | 4.5.3 | [0334](https://kerodon.net/tag/0334) |
| 3720 | 4.5.3.9 | Remark | Remark 4.5.3.9 | 4.5.3 | [0337](https://kerodon.net/tag/0337) |
| 3721 | 4.5.3.10 | Remark | Remark 4.5.3.10 | 4.5.3 | [069E](https://kerodon.net/tag/069E) |
| 3722 | 4.5.4.5 | Remark | Remark 4.5.4.5 (Two-out-of-Three) | 4.5.4 | [01ED](https://kerodon.net/tag/01ED) |
| 3723 | 4.5.4.6 | Remark | Remark 4.5.4.6 | 4.5.4 | [02R1](https://kerodon.net/tag/02R1) |
| 3724 | 4.5.4.7 | Remark | Remark 4.5.4.7 | 4.5.4 | [01EE](https://kerodon.net/tag/01EE) |
| 3725 | 4.5.5.12 | Example | Example 4.5.5.12 | 4.5.5 | [01FJ](https://kerodon.net/tag/01FJ) |
| 3726 | 4.5.5.13 | Remark | Remark 4.5.5.13 | 4.5.5 | [01HE](https://kerodon.net/tag/01HE) |
| 3727 | 4.5.6.7 | Remark | Remark 4.5.6.7 | 4.5.6 | [01FX](https://kerodon.net/tag/01FX) |
| 3728 | 4.5.6.8 | Example | Example 4.5.6.8 | 4.5.6 | [01FY](https://kerodon.net/tag/01FY) |
| 3729 | 4.5.6.10 | Remark | Remark 4.5.6.10 | 4.5.6 | [01G0](https://kerodon.net/tag/01G0) |
| 3730 | 4.5.6.11 | Remark | Remark 4.5.6.11 | 4.5.6 | [01G1](https://kerodon.net/tag/01G1) |
| 3731 | 4.5.7.2 | Remark | Remark 4.5.7.2 | 4.5.7 | [0348](https://kerodon.net/tag/0348) |
| 3732 | 4.5.7.8 | Example | Example 4.5.7.8 (Isofibrant Towers) | 4.5.7 | [034E](https://kerodon.net/tag/034E) |
| 3733 | 4.5.7.18 | Example | Example 4.5.7.18 | 4.5.7 | [034R](https://kerodon.net/tag/034R) |
| 3734 | 4.5.8.4 | Example | Example 4.5.8.4 | 4.5.8 | [02TS](https://kerodon.net/tag/02TS) |
| 3735 | 4.5.8.14 | Remark | Remark 4.5.8.14 | 4.5.8 | [02U0](https://kerodon.net/tag/02U0) |
| 3736 | 4.6.1.6 | Example | Example 4.6.1.6 | 4.6.1 | [01J9](https://kerodon.net/tag/01J9) |
| 3737 | 4.6.1.13 | Example | Example 4.6.1.13 (Loop Spaces) | 4.6.1 | [01JE](https://kerodon.net/tag/01JE) |
| 3738 | 4.6.1.15 | Remark | Remark 4.6.1.15 (Morphism Spaces in Homotopy Fiber Products) | 4.6.1 | [046R](https://kerodon.net/tag/046R) |
| 3739 | 4.6.1.18 | Example | Example 4.6.1.18 | 4.6.1 | [01P4](https://kerodon.net/tag/01P4) |
| 3740 | 4.6.2.7 | Remark | Remark 4.6.2.7 | 4.6.2 | [01HU](https://kerodon.net/tag/01HU) |
| 3741 | 4.6.3.6 | Example | Example 4.6.3.6 | 4.6.3 | [01K8](https://kerodon.net/tag/01K8) |
| 3742 | 4.6.4.4 | Remark | Remark 4.6.4.4 (Homotopy Invariance) | 4.6.4 | [03PN](https://kerodon.net/tag/03PN) |
| 3743 | 4.6.4.9 | Example | Example 4.6.4.9 | 4.6.4 | [05YH](https://kerodon.net/tag/05YH) |
| 3744 | 4.6.5.2 | Remark | Remark 4.6.5.2 | 4.6.5 | [01KY](https://kerodon.net/tag/01KY) |
| 3745 | 4.6.7.6 | Remark | Remark 4.6.7.6 | 4.6.7 | [01LF](https://kerodon.net/tag/01LF) |
| 3746 | 4.6.7.7 | Example | Example 4.6.7.7 | 4.6.7 | [06QR](https://kerodon.net/tag/06QR) |
| 3747 | 4.6.7.11 | Example | Example 4.6.7.11 | 4.6.7 | [01LK](https://kerodon.net/tag/01LK) |
| 3748 | 4.6.7.13 | Remark | Remark 4.6.7.13 | 4.6.7 | [01LM](https://kerodon.net/tag/01LM) |
| 3749 | 4.6.7.14 | Remark | Remark 4.6.7.14 | 4.6.7 | [01LN](https://kerodon.net/tag/01LN) |
| 3750 | 4.6.8.10 | Remark | Remark 4.6.8.10 | 4.6.8 | [01PR](https://kerodon.net/tag/01PR) |
| 3751 | 4.7.1.2 | Remark | Remark 4.7.1.2 | 4.7.1 | [05ED](https://kerodon.net/tag/05ED) |
| 3752 | 4.7.1.12 | Example | Example 4.7.1.12 (Truncated Objects of Products) | 4.7.1 | [069L](https://kerodon.net/tag/069L) |
| 3753 | 4.7.1.13 | Remark | Remark 4.7.1.13 (Isomorphism Invariance) | 4.7.1 | [05EG](https://kerodon.net/tag/05EG) |
| 3754 | 4.7.2.5 | Example | Example 4.7.2.5 | 4.7.2 | [05FD](https://kerodon.net/tag/05FD) |
| 3755 | 4.7.6.4 | Remark | Remark 4.7.6.4 | 4.7.6 | [0586](https://kerodon.net/tag/0586) |
| 3756 | 4.7.6.11 | Remark | Remark 4.7.6.11 | 4.7.6 | [06RL](https://kerodon.net/tag/06RL) |
| 3757 | 4.7.6.12 | Remark | Remark 4.7.6.12 | 4.7.6 | [05YQ](https://kerodon.net/tag/05YQ) |
| 3758 | 4.8.1.4 | Example | Example 4.8.1.4 | 4.8.1 | [01JV](https://kerodon.net/tag/01JV) |
| 3759 | 4.8.1.6 | Remark | Remark 4.8.1.6 | 4.8.1 | [06S0](https://kerodon.net/tag/06S0) |
| 3760 | 4.8.1.10 | Remark | Remark 4.8.1.10 | 4.8.1 | [01PE](https://kerodon.net/tag/01PE) |
| 3761 | 4.8.2.4 | Remark | Remark 4.8.2.4 | 4.8.2 | [06S4](https://kerodon.net/tag/06S4) |
| 3762 | 4.8.2.5 | Remark | Remark 4.8.2.5 | 4.8.2 | [05A0](https://kerodon.net/tag/05A0) |
| 3763 | 4.8.2.6 | Exercise | Exercise 4.8.2.6 | 4.8.2 | [05A1](https://kerodon.net/tag/05A1) |
| 3764 | 4.8.2.11 | Remark | Remark 4.8.2.11 (Coproducts) | 4.8.2 | [06S7](https://kerodon.net/tag/06S7) |
| 3765 | 4.8.2.12 | Remark | Remark 4.8.2.12 | 4.8.2 | [06S8](https://kerodon.net/tag/06S8) |
| 3766 | 4.8.2.13 | Example | Example 4.8.2.13 | 4.8.2 | [06S9](https://kerodon.net/tag/06S9) |
| 3767 | 4.8.2.14 | Remark | Remark 4.8.2.14 (Composition) | 4.8.2 | [05AA](https://kerodon.net/tag/05AA) |
| 3768 | 4.8.2.15 | Remark | Remark 4.8.2.15 (Change of Target) | 4.8.2 | [05AB](https://kerodon.net/tag/05AB) |
| 3769 | 4.8.2.16 | Example | Example 4.8.2.16 | 4.8.2 | [06SA](https://kerodon.net/tag/06SA) |
| 3770 | 4.8.2.17 | Remark | Remark 4.8.2.17 (Isomorphism Invariance) | 4.8.2 | [05AC](https://kerodon.net/tag/05AC) |
| 3771 | 4.8.2.18 | Remark | Remark 4.8.2.18 (Change of Source) | 4.8.2 | [05AD](https://kerodon.net/tag/05AD) |
| 3772 | 4.8.2.19 | Remark | Remark 4.8.2.19 | 4.8.2 | [05AE](https://kerodon.net/tag/05AE) |
| 3773 | 4.8.2.21 | Remark | Remark 4.8.2.21 | 4.8.2 | [05AG](https://kerodon.net/tag/05AG) |
| 3774 | 4.8.2.29 | Exercise | Exercise 4.8.2.29 | 4.8.2 | [05AT](https://kerodon.net/tag/05AT) |
| 3775 | 4.8.2.31 | Remark | Remark 4.8.2.31 | 4.8.2 | [05AV](https://kerodon.net/tag/05AV) |
| 3776 | 4.8.3.6 | Remark | Remark 4.8.3.6 | 4.8.3 | [046S](https://kerodon.net/tag/046S) |
| 3777 | 4.8.3.16 | Remark | Remark 4.8.3.16 | 4.8.3 | [06SE](https://kerodon.net/tag/06SE) |
| 3778 | 4.8.3.19 | Remark | Remark 4.8.3.19 (Monotonicity) | 4.8.3 | [05B2](https://kerodon.net/tag/05B2) |
| 3779 | 4.8.3.26 | Remark | Remark 4.8.3.26 (Transitivity) | 4.8.3 | [05B3](https://kerodon.net/tag/05B3) |
| 3780 | 4.8.3.29 | Remark | Remark 4.8.3.29 | 4.8.3 | [05B4](https://kerodon.net/tag/05B4) |
| 3781 | 4.8.5.8 | Remark | Remark 4.8.5.8 | 4.8.5 | [05C6](https://kerodon.net/tag/05C6) |
| 3782 | 4.8.5.10 | Remark | Remark 4.8.5.10 (Coproducts) | 4.8.5 | [06SV](https://kerodon.net/tag/06SV) |
| 3783 | 4.8.5.11 | Remark | Remark 4.8.5.11 | 4.8.5 | [06SW](https://kerodon.net/tag/06SW) |
| 3784 | 4.8.8.7 | Remark | Remark 4.8.8.7 | 4.8.8 | [06SZ](https://kerodon.net/tag/06SZ) |
| 3785 | 4.8.8.9 | Remark | Remark 4.8.8.9 (Coproducts) | 4.8.8 | [06T1](https://kerodon.net/tag/06T1) |
| 3786 | 4.9.2.9 | Remark | Remark 4.9.2.9 | 4.9.2 | [03R5](https://kerodon.net/tag/03R5) |
| 3787 | 4.9.3.4 | Remark | Remark 4.9.3.4 | 4.9.3 | [03RF](https://kerodon.net/tag/03RF) |
| 3788 | 4.9.3.17 | Remark | Remark 4.9.3.17 | 4.9.3 | [03RU](https://kerodon.net/tag/03RU) |
| 3789 | 4.9.3.19 | Remark | Remark 4.9.3.19 | 4.9.3 | [03UQ](https://kerodon.net/tag/03UQ) |
| 3790 | 4.9.4.5 | Remark | Remark 4.9.4.5 (Coproducts) | 4.9.4 | [03S6](https://kerodon.net/tag/03S6) |
| 3791 | 4.9.4.6 | Remark | Remark 4.9.4.6 (Colimits) | 4.9.4 | [03S7](https://kerodon.net/tag/03S7) |
| 3792 | 4.9.4.7 | Remark | Remark 4.9.4.7 | 4.9.4 | [03S8](https://kerodon.net/tag/03S8) |
| 3793 | 4.9.4.8 | Remark | Remark 4.9.4.8 | 4.9.4 | [03S9](https://kerodon.net/tag/03S9) |
| 3794 | 4.9.4.9 | Remark | Remark 4.9.4.9 | 4.9.4 | [05P6](https://kerodon.net/tag/05P6) |
| 3795 | 4.9.4.22 | Remark | Remark 4.9.4.22 | 4.9.4 | [0614](https://kerodon.net/tag/0614) |
| 3796 | 4.9.5.2 | Remark | Remark 4.9.5.2 | 4.9.5 | [03SK](https://kerodon.net/tag/03SK) |
| 3797 | 4.9.5.10 | Remark | Remark 4.9.5.10 (Products) | 4.9.5 | [03SR](https://kerodon.net/tag/03SR) |
| 3798 | 4.9.5.13 | Remark | Remark 4.9.5.13 | 4.9.5 | [03ST](https://kerodon.net/tag/03ST) |
| 3799 | 4.9.7.4 | Example | Example 4.9.7.4 | 4.9.7 | [03TS](https://kerodon.net/tag/03TS) |
| 3800 | 4.9.8.5 | Example | Example 4.9.8.5 | 4.9.8 | [05PC](https://kerodon.net/tag/05PC) |
| 3801 | 4.9.8.6 | Remark | Remark 4.9.8.6 | 4.9.8 | [047E](https://kerodon.net/tag/047E) |
| 3802 | 5.1.1.5 | Example | Example 5.1.1.5 | 5.1.1 | [01T9](https://kerodon.net/tag/01T9) |
| 3803 | 5.1.1.6 | Remark | Remark 5.1.1.6 | 5.1.1 | [01TA](https://kerodon.net/tag/01TA) |
| 3804 | 5.1.1.7 | Remark | Remark 5.1.1.7 (Products) | 5.1.1 | [05PH](https://kerodon.net/tag/05PH) |
| 3805 | 5.1.1.8 | Remark | Remark 5.1.1.8 | 5.1.1 | [02R4](https://kerodon.net/tag/02R4) |
| 3806 | 5.1.1.12 | Remark | Remark 5.1.1.12 | 5.1.1 | [01TD](https://kerodon.net/tag/01TD) |
| 3807 | 5.1.1.13 | Remark | Remark 5.1.1.13 | 5.1.1 | [01TE](https://kerodon.net/tag/01TE) |
| 3808 | 5.1.3.3 | Remark | Remark 5.1.3.3 | 5.1.3 | [01U0](https://kerodon.net/tag/01U0) |
| 3809 | 5.1.3.4 | Remark | Remark 5.1.3.4 | 5.1.3 | [01U1](https://kerodon.net/tag/01U1) |
| 3810 | 5.1.3.5 | Remark | Remark 5.1.3.5 | 5.1.3 | [01U2](https://kerodon.net/tag/01U2) |
| 3811 | 5.1.3.6 | Example | Example 5.1.3.6 | 5.1.3 | [01U3](https://kerodon.net/tag/01U3) |
| 3812 | 5.1.3.8 | Remark | Remark 5.1.3.8 (Uniqueness of Locally Cartesian Lifts) | 5.1.3 | [01U5](https://kerodon.net/tag/01U5) |
| 3813 | 5.1.4.5 | Remark | Remark 5.1.4.5 | 5.1.4 | [01UE](https://kerodon.net/tag/01UE) |
| 3814 | 5.1.4.6 | Remark | Remark 5.1.4.6 | 5.1.4 | [01UF](https://kerodon.net/tag/01UF) |
| 3815 | 5.1.4.7 | Remark | Remark 5.1.4.7 (Products) | 5.1.4 | [05PJ](https://kerodon.net/tag/05PJ) |
| 3816 | 5.1.6.8 | Remark | Remark 5.1.6.8 | 5.1.6 | [023S](https://kerodon.net/tag/023S) |
| 3817 | 5.1.7.4 | Remark | Remark 5.1.7.4 (Functoriality) | 5.1.7 | [0284](https://kerodon.net/tag/0284) |
| 3818 | 5.1.7.7 | Example | Example 5.1.7.7 | 5.1.7 | [02LQ](https://kerodon.net/tag/02LQ) |
| 3819 | 5.2.2.11 | Remark | Remark 5.2.2.11 | 5.2.2 | [02R9](https://kerodon.net/tag/02R9) |
| 3820 | 5.2.2.12 | Example | Example 5.2.2.12 | 5.2.2 | [02RA](https://kerodon.net/tag/02RA) |
| 3821 | 5.2.3.14 | Remark | Remark 5.2.3.14 (Morphism Spaces in the Relative Join) | 5.2.3 | [024F](https://kerodon.net/tag/024F) |
| 3822 | 5.2.5.5 | Remark | Remark 5.2.5.5 | 5.2.5 | [02RD](https://kerodon.net/tag/02RD) |
| 3823 | 5.2.6.5 | Example | Example 5.2.6.5 | 5.2.6 | [01QC](https://kerodon.net/tag/01QC) |
| 3824 | 5.2.8.5 | Remark | Remark 5.2.8.5 (Functoriality) | 5.2.8 | [02RR](https://kerodon.net/tag/02RR) |
| 3825 | 5.2.8.10 | Remark | Remark 5.2.8.10 (Functoriality) | 5.2.8 | [02RU](https://kerodon.net/tag/02RU) |
| 3826 | 5.2.8.13 | Example | Example 5.2.8.13 | 5.2.8 | [02GY](https://kerodon.net/tag/02GY) |
| 3827 | 5.3.1.3 | Remark | Remark 5.3.1.3 | 5.3.1 | [035G](https://kerodon.net/tag/035G) |
| 3828 | 5.3.1.12 | Remark | Remark 5.3.1.12 | 5.3.1 | [03LM](https://kerodon.net/tag/03LM) |
| 3829 | 5.3.1.14 | Example | Example 5.3.1.14 | 5.3.1 | [035Q](https://kerodon.net/tag/035Q) |
| 3830 | 5.3.1.15 | Remark | Remark 5.3.1.15 | 5.3.1 | [02T3](https://kerodon.net/tag/02T3) |
| 3831 | 5.3.1.17 | Remark | Remark 5.3.1.17 (Functoriality) | 5.3.1 | [02T4](https://kerodon.net/tag/02T4) |
| 3832 | 5.3.1.18 | Remark | Remark 5.3.1.18 | 5.3.1 | [02T5](https://kerodon.net/tag/02T5) |
| 3833 | 5.3.1.19 | Remark | Remark 5.3.1.19 | 5.3.1 | [02T6](https://kerodon.net/tag/02T6) |
| 3834 | 5.3.1.20 | Remark | Remark 5.3.1.20 | 5.3.1 | [02T7](https://kerodon.net/tag/02T7) |
| 3835 | 5.3.2.4 | Example | Example 5.3.2.4 (Constant Diagrams) | 5.3.2 | [035Y](https://kerodon.net/tag/035Y) |
| 3836 | 5.3.2.5 | Example | Example 5.3.2.5 (Set-Valued Functors) | 5.3.2 | [035Z](https://kerodon.net/tag/035Z) |
| 3837 | 5.3.2.6 | Example | Example 5.3.2.6 (Corepresentable Functors) | 5.3.2 | [0360](https://kerodon.net/tag/0360) |
| 3838 | 5.3.2.7 | Remark | Remark 5.3.2.7 | 5.3.2 | [0361](https://kerodon.net/tag/0361) |
| 3839 | 5.3.2.8 | Remark | Remark 5.3.2.8 (Functoriality) | 5.3.2 | [0362](https://kerodon.net/tag/0362) |
| 3840 | 5.3.2.9 | Remark | Remark 5.3.2.9 (Comparison with the Colimit) | 5.3.2 | [0363](https://kerodon.net/tag/0363) |
| 3841 | 5.3.3.2 | Example | Example 5.3.3.2 | 5.3.3 | [025Y](https://kerodon.net/tag/025Y) |
| 3842 | 5.3.3.3 | Remark | Remark 5.3.3.3 (Vertices of the Weighted Nerve) | 5.3.3 | [0267](https://kerodon.net/tag/0267) |
| 3843 | 5.3.3.4 | Remark | Remark 5.3.3.4 (Edges of the Weighted Nerve) | 5.3.3 | [0268](https://kerodon.net/tag/0268) |
| 3844 | 5.3.3.5 | Remark | Remark 5.3.3.5 | 5.3.3 | [036J](https://kerodon.net/tag/036J) |
| 3845 | 5.3.3.7 | Remark | Remark 5.3.3.7 (Functoriality in $\operatorname{\mathcal{C}}$) | 5.3.3 | [0261](https://kerodon.net/tag/0261) |
| 3846 | 5.3.3.8 | Example | Example 5.3.3.8 (Fibers of the Weighted Nerve) | 5.3.3 | [0263](https://kerodon.net/tag/0263) |
| 3847 | 5.3.3.9 | Example | Example 5.3.3.9 (The Weighted Nerve of a Constant Diagram) | 5.3.3 | [0262](https://kerodon.net/tag/0262) |
| 3848 | 5.3.3.10 | Remark | Remark 5.3.3.10 (Functoriality in $\mathscr {F}$) | 5.3.3 | [0266](https://kerodon.net/tag/0266) |
| 3849 | 5.3.3.12 | Example | Example 5.3.3.12 (The Weighted Nerve of a Cone) | 5.3.3 | [036M](https://kerodon.net/tag/036M) |
| 3850 | 5.3.3.21 | Example | Example 5.3.3.21 | 5.3.3 | [036Q](https://kerodon.net/tag/036Q) |
| 3851 | 5.3.4.6 | Remark | Remark 5.3.4.6 (Change of $\operatorname{\mathcal{E}}$) | 5.3.4 | [036Z](https://kerodon.net/tag/036Z) |
| 3852 | 5.3.4.10 | Remark | Remark 5.3.4.10 (Universality) | 5.3.4 | [0372](https://kerodon.net/tag/0372) |
| 3853 | 5.3.8.2 | Example | Example 5.3.8.2 | 5.3.8 | [05PP](https://kerodon.net/tag/05PP) |
| 3854 | 5.3.8.6 | Remark | Remark 5.3.8.6 | 5.3.8 | [05PT](https://kerodon.net/tag/05PT) |
| 3855 | 5.3.8.12 | Remark | Remark 5.3.8.12 (Uniqueness of Minimal Models) | 5.3.8 | [05PZ](https://kerodon.net/tag/05PZ) |
| 3856 | 5.4.2.2 | Example | Example 5.4.2.2 | 5.4.2 | [01WH](https://kerodon.net/tag/01WH) |
| 3857 | 5.4.2.4 | Remark | Remark 5.4.2.4 | 5.4.2 | [01WK](https://kerodon.net/tag/01WK) |
| 3858 | 5.4.5.2 | Remark | Remark 5.4.5.2 | 5.4.5 | [01XC](https://kerodon.net/tag/01XC) |
| 3859 | 5.4.5.9 | Remark | Remark 5.4.5.9 | 5.4.5 | [01XK](https://kerodon.net/tag/01XK) |
| 3860 | 5.4.6.4 | Remark | Remark 5.4.6.4 | 5.4.6 | [01XU](https://kerodon.net/tag/01XU) |
| 3861 | 5.4.6.10 | Remark | Remark 5.4.6.10 | 5.4.6 | [01XZ](https://kerodon.net/tag/01XZ) |
| 3862 | 5.4.7.4 | Remark | Remark 5.4.7.4 (Functoriality) | 5.4.7 | [01Y8](https://kerodon.net/tag/01Y8) |
| 3863 | 5.4.7.5 | Remark | Remark 5.4.7.5 | 5.4.7 | [047S](https://kerodon.net/tag/047S) |
| 3864 | 5.4.8.3 | Example | Example 5.4.8.3 | 5.4.8 | [01YN](https://kerodon.net/tag/01YN) |
| 3865 | 5.5.3.5 | Remark | Remark 5.5.3.5 | 5.5.3 | [020F](https://kerodon.net/tag/020F) |
| 3866 | 5.5.3.6 | Remark | Remark 5.5.3.6 | 5.5.3 | [020D](https://kerodon.net/tag/020D) |
| 3867 | 5.5.3.7 | Remark | Remark 5.5.3.7 | 5.5.3 | [020E](https://kerodon.net/tag/020E) |
| 3868 | 5.5.3.14 | Remark | Remark 5.5.3.14 | 5.5.3 | [03UW](https://kerodon.net/tag/03UW) |
| 3869 | 5.5.5.12 | Example | Example 5.5.5.12 (Objects and Morphisms of $\operatorname{\mathcal{QC}}_{\operatorname{Obj}}$) | 5.5.5 | [0214](https://kerodon.net/tag/0214) |
| 3870 | 5.5.5.16 | Remark | Remark 5.5.5.16 | 5.5.5 | [0215](https://kerodon.net/tag/0215) |
| 3871 | 5.5.5.17 | Example | Example 5.5.5.17 ($2$-Simplices of $\operatorname{ \pmb {\mathcal{QC}} }_{\operatorname{Obj}}$) | 5.5.5 | [0216](https://kerodon.net/tag/0216) |
| 3872 | 5.6.2.13 | Example | Example 5.6.2.13 (Morphisms of the $\infty $-Category of Elements) | 5.6.2 | [026W](https://kerodon.net/tag/026W) |
| 3873 | 5.6.2.14 | Remark | Remark 5.6.2.14 (Cocartesian Morphisms of the $\infty $-Category of Elements) | 5.6.2 | [026X](https://kerodon.net/tag/026X) |
| 3874 | 5.6.2.15 | Remark | Remark 5.6.2.15 | 5.6.2 | [05Q2](https://kerodon.net/tag/05Q2) |
| 3875 | 5.6.2.16 | Example | Example 5.6.2.16 ($2$-Simplices of the $\infty $-Category of Elements) | 5.6.2 | [026Z](https://kerodon.net/tag/026Z) |
| 3876 | 5.6.2.17 | Example | Example 5.6.2.17 | 5.6.2 | [0270](https://kerodon.net/tag/0270) |
| 3877 | 5.6.2.18 | Remark | Remark 5.6.2.18 | 5.6.2 | [0271](https://kerodon.net/tag/0271) |
| 3878 | 5.6.2.19 | Example | Example 5.6.2.19 (Fibers of the $\infty $-Category of Elements) | 5.6.2 | [0272](https://kerodon.net/tag/0272) |
| 3879 | 5.6.2.20 | Example | Example 5.6.2.20 (Elements of Diagram $\infty $-Categories) | 5.6.2 | [05Q3](https://kerodon.net/tag/05Q3) |
| 3880 | 5.6.4.3 | Example | Example 5.6.4.3 (The Comparison Map on Edges) | 5.6.4 | [027D](https://kerodon.net/tag/027D) |
| 3881 | 5.6.4.6 | Remark | Remark 5.6.4.6 | 5.6.4 | [027G](https://kerodon.net/tag/027G) |
| 3882 | 5.6.4.7 | Example | Example 5.6.4.7 | 5.6.4 | [027H](https://kerodon.net/tag/027H) |
| 3883 | 5.6.5.3 | Remark | Remark 5.6.5.3 | 5.6.5 | [028X](https://kerodon.net/tag/028X) |
| 3884 | 5.6.5.5 | Example | Example 5.6.5.5 (Fibrations over a Point) | 5.6.5 | [0290](https://kerodon.net/tag/0290) |
| 3885 | 5.6.5.6 | Example | Example 5.6.5.6 (Weighted Nerves) | 5.6.5 | [0385](https://kerodon.net/tag/0385) |
| 3886 | 5.6.5.7 | Example | Example 5.6.5.7 (Strict Transport) | 5.6.5 | [0386](https://kerodon.net/tag/0386) |
| 3887 | 5.6.5.8 | Example | Example 5.6.5.8 | 5.6.5 | [05Q4](https://kerodon.net/tag/05Q4) |
| 3888 | 5.6.5.9 | Example | Example 5.6.5.9 | 5.6.5 | [05Q5](https://kerodon.net/tag/05Q5) |
| 3889 | 5.6.5.10 | Remark | Remark 5.6.5.10 | 5.6.5 | [0291](https://kerodon.net/tag/0291) |
| 3890 | 5.6.5.11 | Remark | Remark 5.6.5.11 | 5.6.5 | [0292](https://kerodon.net/tag/0292) |
| 3891 | 5.6.6.3 | Remark | Remark 5.6.6.3 | 5.6.6 | [038C](https://kerodon.net/tag/038C) |
| 3892 | 5.6.6.4 | Remark | Remark 5.6.6.4 | 5.6.6 | [038D](https://kerodon.net/tag/038D) |
| 3893 | 5.6.6.6 | Remark | Remark 5.6.6.6 | 5.6.6 | [038E](https://kerodon.net/tag/038E) |
| 3894 | 5.6.6.11 | Remark | Remark 5.6.6.11 | 5.6.6 | [038H](https://kerodon.net/tag/038H) |
| 3895 | 5.6.6.12 | Remark | Remark 5.6.6.12 | 5.6.6 | [02FT](https://kerodon.net/tag/02FT) |
| 3896 | 5.6.7.4 | Remark | Remark 5.6.7.4 | 5.6.7 | [02LR](https://kerodon.net/tag/02LR) |
| 3897 | 5.6.8.2 | Example | Example 5.6.8.2 | 5.6.8 | [02SB](https://kerodon.net/tag/02SB) |
| 3898 | 6.1.1.5 | Remark | Remark 6.1.1.5 (Isomorphism Invariance) | 6.1.1 | [02CL](https://kerodon.net/tag/02CL) |
| 3899 | 6.2.2.9 | Example | Example 6.2.2.9 | 6.2.2 | [02F9](https://kerodon.net/tag/02F9) |
| 3900 | 6.2.2.10 | Example | Example 6.2.2.10 | 6.2.2 | [02SS](https://kerodon.net/tag/02SS) |
| 3901 | 6.2.5.3 | Remark | Remark 6.2.5.3 | 6.2.5 | [02FM](https://kerodon.net/tag/02FM) |
| 3902 | 6.3.1.4 | Example | Example 6.3.1.4 | 6.3.1 | [01MJ](https://kerodon.net/tag/01MJ) |
| 3903 | 6.3.1.7 | Remark | Remark 6.3.1.7 | 6.3.1 | [01MM](https://kerodon.net/tag/01MM) |
| 3904 | 6.3.1.8 | Remark | Remark 6.3.1.8 | 6.3.1 | [01MN](https://kerodon.net/tag/01MN) |
| 3905 | 6.3.1.11 | Exercise | Exercise 6.3.1.11 | 6.3.1 | [02SW](https://kerodon.net/tag/02SW) |
| 3906 | 6.3.1.12 | Example | Example 6.3.1.12 | 6.3.1 | [01MR](https://kerodon.net/tag/01MR) |
| 3907 | 6.3.1.14 | Example | Example 6.3.1.14 | 6.3.1 | [01MT](https://kerodon.net/tag/01MT) |
| 3908 | 6.3.1.15 | Remark | Remark 6.3.1.15 (Coproducts) | 6.3.1 | [05ZC](https://kerodon.net/tag/05ZC) |
| 3909 | 6.3.1.16 | Remark | Remark 6.3.1.16 | 6.3.1 | [038T](https://kerodon.net/tag/038T) |
| 3910 | 6.3.1.17 | Remark | Remark 6.3.1.17 | 6.3.1 | [01MU](https://kerodon.net/tag/01MU) |
| 3911 | 6.3.1.20 | Remark | Remark 6.3.1.20 | 6.3.1 | [01MX](https://kerodon.net/tag/01MX) |
| 3912 | 6.3.2.10 | Remark | Remark 6.3.2.10 (Sizes of Localization) | 6.3.2 | [05ZN](https://kerodon.net/tag/05ZN) |
| 3913 | 6.3.5.2 | Example | Example 6.3.5.2 | 6.3.5 | [047T](https://kerodon.net/tag/047T) |
| 3914 | 7.1.1.6 | Example | Example 7.1.1.6 | 7.1.1 | [02JR](https://kerodon.net/tag/02JR) |
| 3915 | 7.1.1.8 | Remark | Remark 7.1.1.8 | 7.1.1 | [02W1](https://kerodon.net/tag/02W1) |
| 3916 | 7.1.1.9 | Remark | Remark 7.1.1.9 | 7.1.1 | [02W2](https://kerodon.net/tag/02W2) |
| 3917 | 7.1.1.10 | Remark | Remark 7.1.1.10 | 7.1.1 | [02W3](https://kerodon.net/tag/02W3) |
| 3918 | 7.1.1.11 | Remark | Remark 7.1.1.11 | 7.1.1 | [02W4](https://kerodon.net/tag/02W4) |
| 3919 | 7.1.1.17 | Remark | Remark 7.1.1.17 | 7.1.1 | [03U1](https://kerodon.net/tag/03U1) |
| 3920 | 7.1.2.3 | Remark | Remark 7.1.2.3 | 7.1.2 | [03F0](https://kerodon.net/tag/03F0) |
| 3921 | 7.1.2.6 | Remark | Remark 7.1.2.6 (Powers as Limits) | 7.1.2 | [03F3](https://kerodon.net/tag/03F3) |
| 3922 | 7.1.2.9 | Example | Example 7.1.2.9 | 7.1.2 | [03F7](https://kerodon.net/tag/03F7) |
| 3923 | 7.1.2.10 | Example | Example 7.1.2.10 | 7.1.2 | [03F8](https://kerodon.net/tag/03F8) |
| 3924 | 7.1.2.12 | Exercise | Exercise 7.1.2.12 | 7.1.2 | [05QB](https://kerodon.net/tag/05QB) |
| 3925 | 7.1.3.6 | Remark | Remark 7.1.3.6 | 7.1.3 | [02WA](https://kerodon.net/tag/02WA) |
| 3926 | 7.1.3.11 | Example | Example 7.1.3.11 | 7.1.3 | [069M](https://kerodon.net/tag/069M) |
| 3927 | 7.1.4.20 | Remark | Remark 7.1.4.20 | 7.1.4 | [02K5](https://kerodon.net/tag/02K5) |
| 3928 | 7.1.4.24 | Remark | Remark 7.1.4.24 | 7.1.4 | [02K9](https://kerodon.net/tag/02K9) |
| 3929 | 7.1.5.2 | Example | Example 7.1.5.2 | 7.1.5 | [02WF](https://kerodon.net/tag/02WF) |
| 3930 | 7.1.5.4 | Example | Example 7.1.5.4 | 7.1.5 | [02WG](https://kerodon.net/tag/02WG) |
| 3931 | 7.1.5.6 | Remark | Remark 7.1.5.6 (Transitivity) | 7.1.5 | [02WJ](https://kerodon.net/tag/02WJ) |
| 3932 | 7.1.5.9 | Remark | Remark 7.1.5.9 | 7.1.5 | [02WM](https://kerodon.net/tag/02WM) |
| 3933 | 7.1.6.3 | Example | Example 7.1.6.3 | 7.1.6 | [02KK](https://kerodon.net/tag/02KK) |
| 3934 | 7.1.6.4 | Example | Example 7.1.6.4 | 7.1.6 | [02KM](https://kerodon.net/tag/02KM) |
| 3935 | 7.1.6.6 | Remark | Remark 7.1.6.6 | 7.1.6 | [02WY](https://kerodon.net/tag/02WY) |
| 3936 | 7.1.6.8 | Remark | Remark 7.1.6.8 | 7.1.6 | [02KJ](https://kerodon.net/tag/02KJ) |
| 3937 | 7.1.6.18 | Remark | Remark 7.1.6.18 (Limit Functors) | 7.1.6 | [05QJ](https://kerodon.net/tag/05QJ) |
| 3938 | 7.1.7.2 | Example | Example 7.1.7.2 | 7.1.7 | [02KL](https://kerodon.net/tag/02KL) |
| 3939 | 7.1.7.3 | Example | Example 7.1.7.3 | 7.1.7 | [02KN](https://kerodon.net/tag/02KN) |
| 3940 | 7.1.8.12 | Example | Example 7.1.8.12 | 7.1.8 | [06A6](https://kerodon.net/tag/06A6) |
| 3941 | 7.1.9.6 | Remark | Remark 7.1.9.6 | 7.1.9 | [06AG](https://kerodon.net/tag/06AG) |
| 3942 | 7.2.3.2 | Remark | Remark 7.2.3.2 | 7.2.3 | [02NZ](https://kerodon.net/tag/02NZ) |
| 3943 | 7.3.1.7 | Example | Example 7.3.1.7 | 7.3.1 | [02YE](https://kerodon.net/tag/02YE) |
| 3944 | 7.3.1.9 | Example | Example 7.3.1.9 (Cofinality and Kan Extensions) | 7.3.1 | [05QL](https://kerodon.net/tag/05QL) |
| 3945 | 7.3.1.11 | Remark | Remark 7.3.1.11 | 7.3.1 | [02YH](https://kerodon.net/tag/02YH) |
| 3946 | 7.3.1.12 | Remark | Remark 7.3.1.12 | 7.3.1 | [02YJ](https://kerodon.net/tag/02YJ) |
| 3947 | 7.3.1.13 | Remark | Remark 7.3.1.13 (Change of Target) | 7.3.1 | [02YK](https://kerodon.net/tag/02YK) |
| 3948 | 7.3.2.3 | Exercise | Exercise 7.3.2.3 | 7.3.2 | [02YS](https://kerodon.net/tag/02YS) |
| 3949 | 7.3.2.12 | Warning | Warning 7.3.2.12 | 7.3.2 | [02Z0](https://kerodon.net/tag/02Z0) |
| 3950 | 7.3.3.6 | Example | Example 7.3.3.6 | 7.3.3 | [043F](https://kerodon.net/tag/043F) |
| 3951 | 7.3.3.17 | Remark | Remark 7.3.3.17 | 7.3.3 | [02ZD](https://kerodon.net/tag/02ZD) |
| 3952 | 7.3.5.6 | Example | Example 7.3.5.6 | 7.3.5 | [043H](https://kerodon.net/tag/043H) |
| 3953 | 7.3.6.6 | Remark | Remark 7.3.6.6 | 7.3.6 | [030E](https://kerodon.net/tag/030E) |
| 3954 | 7.3.6.8 | Remark | Remark 7.3.6.8 | 7.3.6 | [030H](https://kerodon.net/tag/030H) |
| 3955 | 7.3.7.12 | Remark | Remark 7.3.7.12 | 7.3.7 | [0487](https://kerodon.net/tag/0487) |
| 3956 | 7.4.3.7 | Example | Example 7.4.3.7 (Colimits of Corepresentable Functors) | 7.4.3 | [05RS](https://kerodon.net/tag/05RS) |
| 3957 | 7.4.4.11 | Remark | Remark 7.4.4.11 | 7.4.4 | [02TF](https://kerodon.net/tag/02TF) |
| 3958 | 7.4.4.13 | Remark | Remark 7.4.4.13 | 7.4.4 | [02TH](https://kerodon.net/tag/02TH) |
| 3959 | 7.4.5.11 | Example | Example 7.4.5.11 | 7.4.5 | [02US](https://kerodon.net/tag/02US) |
| 3960 | 7.4.5.12 | Remark | Remark 7.4.5.12 | 7.4.5 | [02UT](https://kerodon.net/tag/02UT) |
| 3961 | 7.4.5.16 | Exercise | Exercise 7.4.5.16 | 7.4.5 | [02UW](https://kerodon.net/tag/02UW) |
| 3962 | 7.4.5.19 | Remark | Remark 7.4.5.19 | 7.4.5 | [02UY](https://kerodon.net/tag/02UY) |
| 3963 | 7.5.1.3 | Remark | Remark 7.5.1.3 (Homotopy Invariance) | 7.5.1 | [03A2](https://kerodon.net/tag/03A2) |
| 3964 | 7.5.1.6 | Remark | Remark 7.5.1.6 | 7.5.1 | [03A5](https://kerodon.net/tag/03A5) |
| 3965 | 7.5.1.7 | Example | Example 7.5.1.7 (Duality with Homotopy Colimits) | 7.5.1 | [03A6](https://kerodon.net/tag/03A6) |
| 3966 | 7.5.2.3 | Remark | Remark 7.5.2.3 | 7.5.2 | [03AA](https://kerodon.net/tag/03AA) |
| 3967 | 7.5.2.7 | Remark | Remark 7.5.2.7 (Homotopy Invariance) | 7.5.2 | [03AC](https://kerodon.net/tag/03AC) |
| 3968 | 7.5.2.8 | Example | Example 7.5.2.8 (Homotopy Limits of Cores) | 7.5.2 | [03AD](https://kerodon.net/tag/03AD) |
| 3969 | 7.5.2.9 | Remark | Remark 7.5.2.9 | 7.5.2 | [03AE](https://kerodon.net/tag/03AE) |
| 3970 | 7.5.2.11 | Example | Example 7.5.2.11 (Duality with Homotopy Colimits) | 7.5.2 | [03AG](https://kerodon.net/tag/03AG) |
| 3971 | 7.5.2.12 | Remark | Remark 7.5.2.12 (Comparison with the Limit) | 7.5.2 | [03AH](https://kerodon.net/tag/03AH) |
| 3972 | 7.5.2.16 | Example | Example 7.5.2.16 | 7.5.2 | [03AM](https://kerodon.net/tag/03AM) |
| 3973 | 7.5.2.17 | Example | Example 7.5.2.17 | 7.5.2 | [03AN](https://kerodon.net/tag/03AN) |
| 3974 | 7.5.3.9 | Remark | Remark 7.5.3.9 | 7.5.3 | [03AY](https://kerodon.net/tag/03AY) |
| 3975 | 7.5.3.11 | Remark | Remark 7.5.3.11 | 7.5.3 | [03B0](https://kerodon.net/tag/03B0) |
| 3976 | 7.5.4.2 | Example | Example 7.5.4.2 (Limits of Isofibrant Diagrams) | 7.5.4 | [03B7](https://kerodon.net/tag/03B7) |
| 3977 | 7.5.5.5 | Remark | Remark 7.5.5.5 | 7.5.5 | [03BR](https://kerodon.net/tag/03BR) |
| 3978 | 7.5.5.6 | Remark | Remark 7.5.5.6 (Homotopy Invariance) | 7.5.5 | [03BS](https://kerodon.net/tag/03BS) |
| 3979 | 7.5.6.6 | Remark | Remark 7.5.6.6 (Relationship to Isofibrant Diagrams) | 7.5.6 | [03CA](https://kerodon.net/tag/03CA) |
| 3980 | 7.6.2.9 | Remark | Remark 7.6.2.9 | 7.6.2 | [048D](https://kerodon.net/tag/048D) |
| 3981 | 7.6.3.4 | Example | Example 7.6.3.4 | 7.6.3 | [03G7](https://kerodon.net/tag/03G7) |
| 3982 | 7.6.3.6 | Remark | Remark 7.6.3.6 (Homotopy Coherent Squares) | 7.6.3 | [03G9](https://kerodon.net/tag/03G9) |
| 3983 | 7.6.3.7 | Example | Example 7.6.3.7 (Square Diagrams in $\operatorname{\mathcal{QC}}$) | 7.6.3 | [03GA](https://kerodon.net/tag/03GA) |
| 3984 | 7.6.3.12 | Example | Example 7.6.3.12 | 7.6.3 | [03GJ](https://kerodon.net/tag/03GJ) |
| 3985 | 7.6.6.11 | Example | Example 7.6.6.11 | 7.6.6 | [03UK](https://kerodon.net/tag/03UK) |
| 3986 | 7.6.6.12 | Example | Example 7.6.6.12 | 7.6.6 | [03UG](https://kerodon.net/tag/03UG) |
| 3987 | 7.6.6.14 | Remark | Remark 7.6.6.14 | 7.6.6 | [03UH](https://kerodon.net/tag/03UH) |
| 3988 | 7.6.6.17 | Exercise | Exercise 7.6.6.17 | 7.6.6 | [03J4](https://kerodon.net/tag/03J4) |
| 3989 | 7.6.6.21 | Remark | Remark 7.6.6.21 | 7.6.6 | [048G](https://kerodon.net/tag/048G) |
| 3990 | 7.7.0.2 | Remark | Remark 7.7.0.2 (Distributivity) | 7.7 | [05SF](https://kerodon.net/tag/05SF) |
| 3991 | 8.1.0.2 | Remark | Remark 8.1.0.2 | 8.1 | [00B1](https://kerodon.net/tag/00B1) |
| 3992 | 8.1.0.5 | Example | Example 8.1.0.5 | 8.1 | [00B2](https://kerodon.net/tag/00B2) |
| 3993 | 8.1.2.14 | Exercise | Exercise 8.1.2.14 | 8.1.2 | [03K4](https://kerodon.net/tag/03K4) |
| 3994 | 8.1.3.4 | Remark | Remark 8.1.3.4 (Symmetry) | 8.1.3 | [03KR](https://kerodon.net/tag/03KR) |
| 3995 | 8.1.3.6 | Example | Example 8.1.3.6 (Tautological Cospans) | 8.1.3 | [048N](https://kerodon.net/tag/048N) |
| 3996 | 8.1.3.9 | Remark | Remark 8.1.3.9 | 8.1.3 | [048P](https://kerodon.net/tag/048P) |
| 3997 | 8.1.6.2 | Remark | Remark 8.1.6.2 (Symmetry) | 8.1.6 | [0491](https://kerodon.net/tag/0491) |
| 3998 | 8.1.6.3 | Remark | Remark 8.1.6.3 | 8.1.6 | [0492](https://kerodon.net/tag/0492) |
| 3999 | 8.1.6.4 | Remark | Remark 8.1.6.4 | 8.1.6 | [0493](https://kerodon.net/tag/0493) |
| 4000 | 8.1.6.6 | Example | Example 8.1.6.6 | 8.1.6 | [0495](https://kerodon.net/tag/0495) |
| 4001 | 8.1.7.11 | Remark | Remark 8.1.7.11 | 8.1.7 | [049S](https://kerodon.net/tag/049S) |
| 4002 | 8.1.9.8 | Example | Example 8.1.9.8 | 8.1.9 | [04A3](https://kerodon.net/tag/04A3) |
| 4003 | 8.1.9.11 | Remark | Remark 8.1.9.11 | 8.1.9 | [04AA](https://kerodon.net/tag/04AA) |
| 4004 | 8.1.10.8 | Example | Example 8.1.10.8 | 8.1.10 | [04AK](https://kerodon.net/tag/04AK) |
| 4005 | 8.1.10.11 | Remark | Remark 8.1.10.11 | 8.1.10 | [04AP](https://kerodon.net/tag/04AP) |
| 4006 | 8.2.0.2 | Example | Example 8.2.0.2 (The Twisted Arrow Coupling) | 8.2 | [043R](https://kerodon.net/tag/043R) |
| 4007 | 8.2.1.4 | Remark | Remark 8.2.1.4 (Symmetry) | 8.2.1 | [0441](https://kerodon.net/tag/0441) |
| 4008 | 8.2.1.5 | Example | Example 8.2.1.5 | 8.2.1 | [0442](https://kerodon.net/tag/0442) |
| 4009 | 8.2.1.9 | Remark | Remark 8.2.1.9 | 8.2.1 | [0446](https://kerodon.net/tag/0446) |
| 4010 | 8.2.2.3 | Remark | Remark 8.2.2.3 (Functor Couplings) | 8.2.2 | [044B](https://kerodon.net/tag/044B) |
| 4011 | 8.2.2.4 | Remark | Remark 8.2.2.4 | 8.2.2 | [044C](https://kerodon.net/tag/044C) |
| 4012 | 8.2.2.12 | Example | Example 8.2.2.12 | 8.2.2 | [044L](https://kerodon.net/tag/044L) |
| 4013 | 8.2.3.2 | Remark | Remark 8.2.3.2 | 8.2.3 | [044S](https://kerodon.net/tag/044S) |
| 4014 | 8.2.4.8 | Example | Example 8.2.4.8 | 8.2.4 | [045L](https://kerodon.net/tag/045L) |
| 4015 | 8.2.6.2 | Example | Example 8.2.6.2 | 8.2.6 | [045Y](https://kerodon.net/tag/045Y) |
| 4016 | 8.3.2.3 | Remark | Remark 8.3.2.3 (Symmetry) | 8.3.2 | [03MD](https://kerodon.net/tag/03MD) |
| 4017 | 8.3.2.4 | Example | Example 8.3.2.4 (From Profunctors to Couplings) | 8.3.2 | [0463](https://kerodon.net/tag/0463) |
| 4018 | 8.3.2.5 | Remark | Remark 8.3.2.5 (From Couplings to Profunctors) | 8.3.2 | [0464](https://kerodon.net/tag/0464) |
| 4019 | 8.3.2.8 | Remark | Remark 8.3.2.8 | 8.3.2 | [0467](https://kerodon.net/tag/0467) |
| 4020 | 8.3.2.19 | Remark | Remark 8.3.2.19 | 8.3.2 | [046A](https://kerodon.net/tag/046A) |
| 4021 | 8.3.3.3 | Remark | Remark 8.3.3.3 | 8.3.3 | [03MX](https://kerodon.net/tag/03MX) |
| 4022 | 8.3.3.16 | Remark | Remark 8.3.3.16 | 8.3.3 | [03V6](https://kerodon.net/tag/03V6) |
| 4023 | 8.3.4.6 | Remark | Remark 8.3.4.6 | 8.3.4 | [046D](https://kerodon.net/tag/046D) |
| 4024 | 8.3.4.13 | Remark | Remark 8.3.4.13 | 8.3.4 | [046F](https://kerodon.net/tag/046F) |
| 4025 | 8.3.5.2 | Remark | Remark 8.3.5.2 | 8.3.5 | [03MZ](https://kerodon.net/tag/03MZ) |
| 4026 | 8.3.5.3 | Remark | Remark 8.3.5.3 | 8.3.5 | [03N1](https://kerodon.net/tag/03N1) |
| 4027 | 8.3.5.4 | Remark | Remark 8.3.5.4 | 8.3.5 | [03MV](https://kerodon.net/tag/03MV) |
| 4028 | 8.3.7.2 | Remark | Remark 8.3.7.2 | 8.3.7 | [06C1](https://kerodon.net/tag/06C1) |
| 4029 | 8.4.1.16 | Example | Example 8.4.1.16 | 8.4.1 | [03VQ](https://kerodon.net/tag/03VQ) |
| 4030 | 8.4.1.18 | Remark | Remark 8.4.1.18 (Change of Source) | 8.4.1 | [03VT](https://kerodon.net/tag/03VT) |
| 4031 | 8.4.1.19 | Remark | Remark 8.4.1.19 (Change of Target) | 8.4.1 | [03VU](https://kerodon.net/tag/03VU) |
| 4032 | 8.4.1.20 | Remark | Remark 8.4.1.20 | 8.4.1 | [03VV](https://kerodon.net/tag/03VV) |
| 4033 | 8.4.1.21 | Remark | Remark 8.4.1.21 | 8.4.1 | [03VW](https://kerodon.net/tag/03VW) |
| 4034 | 8.4.6.5 | Remark | Remark 8.4.6.5 | 8.4.6 | [05ZY](https://kerodon.net/tag/05ZY) |
| 4035 | 8.5.2.9 | Exercise | Exercise 8.5.2.9 | 8.5.2 | [03ZQ](https://kerodon.net/tag/03ZQ) |
| 4036 | 8.5.3.4 | Remark | Remark 8.5.3.4 | 8.5.3 | [03ZW](https://kerodon.net/tag/03ZW) |
| 4037 | 8.5.4.5 | Example | Example 8.5.4.5 | 8.5.4 | [0409](https://kerodon.net/tag/0409) |
| 4038 | 8.5.6.3 | Remark | Remark 8.5.6.3 | 8.5.6 | [060D](https://kerodon.net/tag/060D) |
| 4039 | 8.5.6.19 | Remark | Remark 8.5.6.19 (Cofinal Idempotents) | 8.5.6 | [060L](https://kerodon.net/tag/060L) |
| 4040 | 8.6.1.4 | Remark | Remark 8.6.1.4 (Base Change) | 8.6.1 | [04CA](https://kerodon.net/tag/04CA) |
| 4041 | 8.6.3.4 | Remark | Remark 8.6.3.4 (Base Change) | 8.6.3 | [04EG](https://kerodon.net/tag/04EG) |
| 4042 | 8.6.3.7 | Remark | Remark 8.6.3.7 | 8.6.3 | [04EM](https://kerodon.net/tag/04EM) |
| 4043 | 8.6.3.10 | Remark | Remark 8.6.3.10 | 8.6.3 | [04F1](https://kerodon.net/tag/04F1) |
| 4044 | 8.6.4.3 | Remark | Remark 8.6.4.3 (Symmetry) | 8.6.4 | [04D3](https://kerodon.net/tag/04D3) |
| 4045 | 8.6.5.7 | Remark | Remark 8.6.5.7 | 8.6.5 | [04DZ](https://kerodon.net/tag/04DZ) |
| 4046 | 8.6.5.10 | Remark | Remark 8.6.5.10 | 8.6.5 | [04E2](https://kerodon.net/tag/04E2) |
| 4047 | 8.6.5.17 | Example | Example 8.6.5.17 | 8.6.5 | [04E9](https://kerodon.net/tag/04E9) |
| 4048 | 8.6.6.10 | Example | Example 8.6.6.10 | 8.6.6 | [05JX](https://kerodon.net/tag/05JX) |
| 4049 | 8.6.6.11 | Remark | Remark 8.6.6.11 | 8.6.6 | [05JY](https://kerodon.net/tag/05JY) |
| 4050 | 8.6.6.13 | Remark | Remark 8.6.6.13 | 8.6.6 | [05K0](https://kerodon.net/tag/05K0) |
| 4051 | 9.1.1.6 | Example | Example 9.1.1.6 | 9.1.1 | [02PD](https://kerodon.net/tag/02PD) |
| 4052 | 9.1.1.10 | Example | Example 9.1.1.10 | 9.1.1 | [0617](https://kerodon.net/tag/0617) |
| 4053 | 9.1.1.11 | Remark | Remark 9.1.1.11 (Monotonicity) | 9.1.1 | [05X3](https://kerodon.net/tag/05X3) |
| 4054 | 9.1.1.14 | Remark | Remark 9.1.1.14 | 9.1.1 | [02PF](https://kerodon.net/tag/02PF) |
| 4055 | 9.1.3.7 | Remark | Remark 9.1.3.7 | 9.1.3 | [05XB](https://kerodon.net/tag/05XB) |
| 4056 | 9.1.3.13 | Remark | Remark 9.1.3.13 | 9.1.3 | [05XU](https://kerodon.net/tag/05XU) |
| 4057 | 9.1.4.2 | Example | Example 9.1.4.2 | 9.1.4 | [06CL](https://kerodon.net/tag/06CL) |
| 4058 | 9.1.4.6 | Remark | Remark 9.1.4.6 | 9.1.4 | [06CQ](https://kerodon.net/tag/06CQ) |
| 4059 | 9.1.6.9 | Example | Example 9.1.6.9 | 9.1.6 | [03DN](https://kerodon.net/tag/03DN) |
| 4060 | 9.1.6.10 | Example | Example 9.1.6.10 | 9.1.6 | [03DP](https://kerodon.net/tag/03DP) |
| 4061 | 9.1.6.11 | Remark | Remark 9.1.6.11 | 9.1.6 | [03DQ](https://kerodon.net/tag/03DQ) |
| 4062 | 9.2.2.13 | Remark | Remark 9.2.2.13 (Retracts) | 9.2.2 | [06DS](https://kerodon.net/tag/06DS) |
| 4063 | 9.2.2.17 | Remark | Remark 9.2.2.17 | 9.2.2 | [062J](https://kerodon.net/tag/062J) |
| 4064 | 9.2.5.9 | Example | Example 9.2.5.9 | 9.2.5 | [064J](https://kerodon.net/tag/064J) |
| 4065 | 9.2.5.18 | Remark | Remark 9.2.5.18 (Retracts) | 9.2.5 | [064Z](https://kerodon.net/tag/064Z) |
| 4066 | 9.3.1.14 | Remark | Remark 9.3.1.14 ($\operatorname{Ind}$-Extensions as Kan Extensions) | 9.3.1 | [063Y](https://kerodon.net/tag/063Y) |
| 4067 | 9.3.4.11 | Example | Example 9.3.4.11 (Corepresentable Functors) | 9.3.4 | [065U](https://kerodon.net/tag/065U) |
| 4068 | 9.3.4.13 | Remark | Remark 9.3.4.13 | 9.3.4 | [065W](https://kerodon.net/tag/065W) |
| 4069 | 9.5.4.5 | Remark | Remark 9.5.4.5 | 9.5.4 | [06P9](https://kerodon.net/tag/06P9) |
| 4070 | 11.5.0.111 | Proposition | Proposition 11.5.0.111 | 11.5 | [025C](https://kerodon.net/tag/025C) |
| 4071 | 11.9.6.1 | Proposition | Proposition 11.9.6.1 (Functoriality of $\operatorname{Hom}$-Functors) | 11.9.6 | [03PB](https://kerodon.net/tag/03PB) |
| 4072 | 11.9.6.2 | Proposition | Proposition 11.9.6.2 | 11.9.6 | [03PE](https://kerodon.net/tag/03PE) |
| 4073 | 11.9.6.3 | Corollary | Corollary 11.9.6.3 | 11.9.6 | [03PF](https://kerodon.net/tag/03PF) |
| 4074 | 11.9.6.4 | Remark | Remark 11.9.6.4 | 11.9.6 | [03PG](https://kerodon.net/tag/03PG) |
| 4075 | 11.9.6.5 | Proposition | Proposition 11.9.6.5 | 11.9.6 | [03PH](https://kerodon.net/tag/03PH) |
| 4076 | 11.9.8.5 | Proposition | Proposition 11.9.8.5 | 11.9.8 | [025B](https://kerodon.net/tag/025B) |
| 4077 | 11.9.8.7 | Corollary | Corollary 11.9.8.7 | 11.9.8 | [025F](https://kerodon.net/tag/025F) |
| 4078 | 11.9.9.1 | Remark | Remark 11.9.9.1 (Functoriality) | 11.9.9 | [026Y](https://kerodon.net/tag/026Y) |
| 4079 | 11.9.9.2 | Construction | Construction 11.9.9.2 | 11.9.9 | [029M](https://kerodon.net/tag/029M) |
| 4080 | 11.9.9.3 | Lemma | Lemma 11.9.9.3 | 11.9.9 | [029N](https://kerodon.net/tag/029N) |
| 4081 | 11.9.9.4 | Lemma | Lemma 11.9.9.4 | 11.9.9 | [029P](https://kerodon.net/tag/029P) |
| 4082 | 11.9.9.6 | Lemma | Lemma 11.9.9.6 | 11.9.9 | [029R](https://kerodon.net/tag/029R) |
| 4083 | 11.9.9.7 | Lemma | Lemma 11.9.9.7 | 11.9.9 | [029S](https://kerodon.net/tag/029S) |
| 4084 | 11.9.9.8 | Remark | Remark 11.9.9.8 | 11.9.9 | [029T](https://kerodon.net/tag/029T) |

## item-tags.csvへの追加15行

| データ行 | 番号 | 種類 | Tag |
|---|---|---|---|
| 6614 | 11.5.0.111 | Proposition | [025C](https://kerodon.net/tag/025C) |
| 6615 | 11.9.6.1 | Proposition | [03PB](https://kerodon.net/tag/03PB) |
| 6616 | 11.9.6.2 | Proposition | [03PE](https://kerodon.net/tag/03PE) |
| 6617 | 11.9.6.3 | Corollary | [03PF](https://kerodon.net/tag/03PF) |
| 6618 | 11.9.6.4 | Remark | [03PG](https://kerodon.net/tag/03PG) |
| 6619 | 11.9.6.5 | Proposition | [03PH](https://kerodon.net/tag/03PH) |
| 6620 | 11.9.8.5 | Proposition | [025B](https://kerodon.net/tag/025B) |
| 6621 | 11.9.8.7 | Corollary | [025F](https://kerodon.net/tag/025F) |
| 6622 | 11.9.9.1 | Remark | [026Y](https://kerodon.net/tag/026Y) |
| 6623 | 11.9.9.2 | Construction | [029M](https://kerodon.net/tag/029M) |
| 6624 | 11.9.9.3 | Lemma | [029N](https://kerodon.net/tag/029N) |
| 6625 | 11.9.9.4 | Lemma | [029P](https://kerodon.net/tag/029P) |
| 6626 | 11.9.9.6 | Lemma | [029R](https://kerodon.net/tag/029R) |
| 6627 | 11.9.9.7 | Lemma | [029S](https://kerodon.net/tag/029S) |
| 6628 | 11.9.9.8 | Remark | [029T](https://kerodon.net/tag/029T) |
