# BS（Prisms）の項目ごとの対応表（2026-11-07）

作成：段階 II の調整役。読み取りだけのエージェント 6 本で調べた。対象は Bhatt–Scholze "Prisms and prismatic cohomology" の著者版（`paper/refs/BS-prisms-author.pdf`）の番号つきの項目 211 個。抜き出しで拾った偽の項目 2 件（6.17 と 9.12。他の文献の引用だった）は除いた。

- `items.csv` の列：
  - `number`、`kind`、`title`
  - `status`：`proved`（本体に原典どおり、sorry なし）、`proved_special`（本体に特別な場合だけ）、`parts_in_body`（11-10 追加：証明の主な部品は本体、主張の組み立ては drafts または他の単位待ち）、`e3_input`（E3 の界面の欄として、今は Inputs の引用）、`drafts`（drafts に型だけ、sorry）、`design_only`（設計書だけ）、`none`
  - `goal`：今の目標（段階 II の目標 A、E3 を消して主定理の閉包の sorry を 0 にする）に必要か。`required`（必要）、`special`（一部だけ必要）、`not_required`（不要）、`unknown`（未確定）
  - `declarations`、`design`（設計書と D 番号）、`note`、`confidence`
- 判定の方法：宣言名・主張・docstring・設計書（a0〜a9-design、design-status、citations-survey）の照合。**Lean を動かしての確認はしていない**。
- 集計（11-10 更新：BS-W11〜W13 と BS-D68 の段 2 が入った後。新しいファイル 113 本の docstring の原典番号から候補を出し、読むだけのエージェントが宣言の型を読んで判定、調整役が主な宣言の実在を確かめた。変わったのは 16 項目）：
  - status：none 99、proved_special 35、drafts 30、proved 28、parts_in_body 8、e3_input 7、design_only 4
  - 目標に必要な 105 項目の status：proved_special 31、drafts 29、proved 28、parts_in_body 8、e3_input 6、design_only 2、none 1
- 11-11 の更新（BS-W15 の停止点 1・2、BS-D69 の停止点 1 の後）：2.21・2.36・2.38・2.39・3.4 を本体（証明済み）、2.37・2.42 を本体（特別な場合）、4.18・6.4 を本体に部品に。
- 11-12 朝の更新（BS-W17 停止点 4 の後）：7.10 を本体に部品に（有限 T の場合）。目標に必要な 105 項目：proved_special 37、proved 35、drafts 12、parts_in_body 13、e3_input 6、design_only 2
- 11-11 夜の更新（BS-W17 停止点 1〜3 の後）：4.17 を本体（特別な場合）に、4.19・6.1・6.2 を本体に部品に。1.4・1.6 は本体に名前つきであったのを訂正。目標に必要な 105 項目：proved_special 37、proved 35、drafts 13、parts_in_body 12、e3_input 6、design_only 2
- 11-11 の更新（BS-W15 停止点 4 の後）：7.8 を本体に、7.7・7.9 を本体に部品に（δ 構造・始性・envelope の側は本体、Δ_R/A との同一視は drafts）。目標に必要な 105 項目：proved_special 35、proved 34、drafts 17、parts_in_body 11、e3_input 6、design_only 2
- 11-10 の 2 回目の更新（BS-D68 停止点 3 の後）：4.9・4.10・5.5 を本体（特別な場合）に、4.11 を本体に部品に。目標に必要な 105 項目：proved_special 34、proved 28、drafts 26、parts_in_body 8、e3_input 6、design_only 2、none 1
- 11-07 の集計：
  - status：none 97、drafts 40、proved_special 34、proved 27、e3_input 8、design_only 5
  - 目標：必要 73、一部だけ必要 32、不要 105、未確定 1（11-07 の訂正の後）
  - 目標に必要な 105 項目の status：drafts 39、proved_special 29、proved 27、e3_input 7、design_only 3
- 一覧のページ（非公開の Artifact）：https://claude.ai/artifact/YWUyntvwsGb2aX39kZnMyT

調査で見つかった、設計の側で直す点：

- D68 の改訂（結晶の黒箱を、対象ごとの HT の命題の直接証明に置き換える）が drafts にまだ入っていない。Lemma 5.4 は drafts にも宣言がない。
- E3 の経路で要るのに、主張の型が drafts にもないもの：Lemma 4.20・4.22（A0-4）、Lemma 3.7(2)(3) の一般形（A0-3b）、Cor 3.12 の (b)〜(e)（A0-3d）。
- 資料どうしの食い違い：Cor 3.12（勉強ノートでは不要、a0-design では要る）、Rem 4.5（a0-design では不要、drafts では使っている）。
- 訂正（11-07、調整役）：Rem 10.7 の「引用のずれの疑い」は誤り（原典に「J_perfd,n は R/pⁿ の冪等イデアル」の一文があり、本体はその J=(g) の場合）。Rem 2.13・2.14・Lemma 2.32 は André の経路（Thm 7.14 → Thm 7.4）の証明済みの部品なので「目標に必要」に直した。未確定は Example 8.3 だけ（a4-design §5 の 5）。
