# BS（Prisms）の項目ごとの対応表（2026-11-07）

作成：段階 II の調整役。読み取りだけのエージェント 6 本で調べた。対象は Bhatt–Scholze "Prisms and prismatic cohomology" の著者版（`paper/refs/BS-prisms-author.pdf`）の番号つきの項目 211 個。抜き出しで拾った偽の項目 2 件（6.17 と 9.12。他の文献の引用だった）は除いた。

- `items.csv` の列：
  - `number`、`kind`、`title`
  - `status`：`proved`（本体に原典どおり、sorry なし）、`proved_special`（本体に特別な場合だけ）、`e3_input`（E3 の界面の欄として、今は Inputs の引用）、`drafts`（drafts に型だけ、sorry）、`design_only`（設計書だけ）、`none`
  - `goal`：今の目標（段階 II の目標 A、E3 を消して主定理の閉包の sorry を 0 にする）に必要か。`required`（必要）、`special`（一部だけ必要）、`not_required`（不要）、`unknown`（未確定）
  - `declarations`、`design`（設計書と D 番号）、`note`、`confidence`
- 判定の方法：宣言名・主張・docstring・設計書（a0〜a9-design、design-status、citations-survey）の照合。**Lean を動かしての確認はしていない**。
- 集計：
  - status：none 97、drafts 40、proved_special 34、proved 27、e3_input 8、design_only 5
  - 目標：必要 70、一部だけ必要 32、不要 105、未確定 4
  - 目標に必要な 102 項目の status：drafts 39、proved_special 28、proved 25、e3_input 7、design_only 3
- 一覧のページ（非公開の Artifact）：https://claude.ai/artifact/YWUyntvwsGb2aX39kZnMyT

調査で見つかった、設計の側で直す点：

- D68 の改訂（結晶の黒箱を、対象ごとの HT の命題の直接証明に置き換える）が drafts にまだ入っていない。Lemma 5.4 は drafts にも宣言がない。
- E3 の経路で要るのに、主張の型が drafts にもないもの：Lemma 4.20・4.22（A0-4）、Lemma 3.7(2)(3) の一般形（A0-3b）、Cor 3.12 の (b)〜(e)（A0-3d）。
- 資料どうしの食い違い：Cor 3.12（勉強ノートでは不要、a0-design では要る）、Rem 4.5（a0-design では不要、drafts では使っている）。
- 本体が「Remark 10.7」として引いている中身が、原典の Rem 10.7 とずれている疑いがある。
- 目標が未確定のもの：Rem 2.13・2.14、Lemma 2.32。André の経路（Thm 7.14 → Thm 7.4）で間接に使われているが、設計書に記述がない。
