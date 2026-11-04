# S4：篩包含に限定した G8 自然性への BS 側接続

2026-11-05。基準 main `9f59541d3`。作業ブランチ `codex/bs-s4-sieve-comparison`。
CA の BS-W10 取り込みブランチには混ぜていない。草稿の編集のみで、ビルド・`lake env lean` は行っていない。

## 合意した範囲

S4 の生成辺は `S.functorInclusion` に係数圏の生成系の対象 M をテンソルしたものだけである。G2 の自然性は任意の篩、任意の前層 F、指定された極限錐 cS・cU に限定したものを先に使う。縦は `tensorSpaceFunctor_setWeightHomNatural`。一般の φ の自然性は S8-5 用に後回し。

## 記述した接続（未検証）

- `SetSections.lean` 草稿を新設。`sectionsOfDiagram`・`sectionsOfCone`・`sectionsOf`・`sectionsOf_map`・`sectionsOf_representable` を `SpaceValued.lean` から移し、同じ名前・引数を保った。S4 の `GlobalSections` が S8 の層化に依存する循環を避けるため。F2 の一般 API の置き場所を変える提案ではなく、BS 側のラッパーと比較の配置。
- `sectionsOf_map` に G2 の指定錐版 `sectionsMap` を接続。実際の引数順は P の錐、Q の錐。G2 の実在ソース `F2/Tensor/SetSectionsNaturality.lean` を読み、main 未取り込みの import はコメント付きで区別した。
- `sieveElementsToCategory`・逆関手・`sieveElementsEquivalence` の本文を記述。射影の一致と、S1 の制限図式への添字変更の式も記述。
- `representableElementsCone` を作り、篩に制限した 1 圏の錐が `sieveCone` に一致する式を記述。S1 の `sieveCone` の自然性も `Over.w` で記述した。
- `representableSectionsCone` とその頂点の式を記述。`sectionsOf_representable` はその標準錐との `limitVertexIso` として記述。
- `coneComparison_isInvertible_iff` は右ファイブレーションが可逆辺を反映することと、錐の圏の終対象性で記述。頂点同型だけから錐の同型を推論していない。
- これを指定錐版の `sectionsMap` に適用し、`sieveSectionsMap_isInvertible_iff` と `isSheaf_iff_sieveSectionsMap_isInvertible` まで接続する本文を記述した。S4 の証明コメントもこの入口に合わせた。

## 残る作業

新しい `SetSections.lean` に明示的な `sorry` は 2 件ある。

1. `representableSectionsCone_isLimit`：元の圏の始対象 `(U,id)` への制限と、恒等脚を持つ一点錐の極限性。宇宙持ち上げ後の全錐を比較する必要がある。
2. `sieveRestrictCone_isLimit_iff`：指定された cU と標準錐の錐同型を制限し、篩の元の圏の同値で添字変更し、全錐を S1 の `restrictionCone` に同定する。

これは完成報告ではない。本文を記述したほかの箇所も型検査前。G2 の篩包含版自然性と、生成系による同値検出を使う `exists_sheafGeneratingEdges` 本体は引き続き未完了。新しい axiom は追加していない。

## 継続：全錐の比較の本文

`uliftNerveCone_whisker_val` と `sieveRestrictCanonicalCone_reindex_val` を記述した。`nerveCone_whisker` と `ulift_restrictJoinCone_val` で、篩へ制限した表現可能標準錐の全射を `restrictionCone` の全射へ結び付ける。

これを用いて `sieveRestrictCone_isLimit_iff` の本文も記述した。まず `limitConeIso` を錐の制限関手で送り、次に元の圏の同値の nerve とその ulift による制限で極限性を移し、最後に全錐の射の等式で S1 の指定錐へ戻す。`nerveMap_comp` という存在しない補題名も除去し、合成の定義と `Functor.map_comp` による図式比較へ直した。

新しい草稿に残る明示的な `sorry` は `representableSectionsCone_isLimit` の **1 件**。前節の「2 件」はこの追加前の状態。今回の本文も未ビルドであり、型検査の成功・S4 の完成は主張しない。
