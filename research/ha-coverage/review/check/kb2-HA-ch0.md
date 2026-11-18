# KB-W2 HA 第0章

原典の版を目次記載SHA-256と照合したPDFの本文と、現在のソースの宣言の型を読み比べた。kernel実行・Lean変更・ビルド・鍵はなし。

対象2行。旧状態：{'partial': 1, 'none': 1}。新状態：{'partial': 1, 'none': 1}。partial_kind：{'component': 1}。

既存own・mathlibなど対象外1行は全フィールド・引用符・改行をそのまま保存。対象行でもstatus/declarations/reason/partial_kind以外は不変。axioms/checkは旧記録であり今回のkernel確認結果ではない。

## 全対象行

| 番号 | 旧→新 | partial_kind | 理由 |
| --- | --- | --- | --- |
| 0.0.0.2 | partial → partial | component | KB-W2型再照合：通常圏Eのnerveが準圏であるという原文の同じ数学的成分を、Nerve.quasicategoryの型が直接返す。weak Kanという歴史的呼称と文献紹介は含まない。 |
| 0.0.0.3 | none → none |  | KB-W2再検索：原文はJoyalらの文献案内と前提知識の説明。準圏・Kan複体の一般的な宣言はあるが、この文献案内を数学的主張の形式化と数えない。 |

## 読取りと再検索

原文・候補の型・現在の引用番号索引・小節ごとの現本体とロックMathlibの再検索はgit外の章別証拠。OE-W1 module-mapと宣言索引を使って移動後の名前・所在・行を確認した。ArchiveとBS draftsの宣言は正の根拠にしない。検索の全ヒットを形式検証したという意味ではない。
