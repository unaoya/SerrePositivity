# Lean の docstring からノートへの参照（2026-11-12）

作成：ノートのチャット。ユーザーの方針（11-12）：**Lean の docstring は論文（原典の番号、例「BS 著者版 Lemma 2.15」）を引き、ノートが Lean を引く。Lean からノートへの参照は置かない。** ノートは加筆で番号が動くため。

以下は main で docstring・コメントがノート（`exposition/` の勉強ノート、その番号・節・課題番号 T・リファクタ番号 BR）を引いている箇所の一覧。grep で拾ったもので、置き換え先（原典の番号）は書いていない。扱いは形式化の調整役。

- 拾い方：「ノート」「exposition/」「BRn」「Tn-n」を含む行。ノートの番号（「命題 2.1.5」など）は、Delta の 7 ファイルが「勉強ノート第 2 章の命題 …」の形で引くもので、「ノート」に含まれる。Hovey・CLMST・HTT などの原典の三段の番号は除いた。
- ∞ の R 番号（`R27` など、109 ファイル・313 か所）は台帳 `refactor-ledger.md` の番号でノートへの参照ではないので、ここには入れていない（工程のラベルとしての扱いは台帳の BR25 と同じ問題）。
- 2026-11-12 にノート 02 章の §2.1 の番号を原典の順に振り直した（旧 2.1.6〜2.1.14 → 新 2.1.9〜2.1.17、新しい三項目が 2.1.6〜2.1.8）。下の Delta の docstring が引く番号は旧番号で、今のノートとはずれている。

計 22 か所（22 ファイル）。

| 種類 | 場所 | 行の中身 |
| --- | --- | --- |
| ノート | `SerrePositivity/BhattScholze/Almost/Lemma103.lean:20` | Tor 独立性を平坦な全射表示で示す（原典の単体的証明の代わり、ノート D13）。 |
| T・ノート | `SerrePositivity/BhattScholze/Andre/Envelope/JetKoszul.lean:17` | BS 著者版 Corollary 2.44・BS 著者版 Proposition 3.13 の平坦性を Koszul 複体の帰納法で得る部分（ノート §2.6 の課題 T2-3 の材料）。 |
| T・ノート | `SerrePositivity/BhattScholze/Andre/Envelope/PDivision.lean:30` | 原典の BS 著者版 Corollary 2.39 を r = 1 で、生の包そのものが p ねじれなしで pd 包と同型という原典の形で示す。二元の場合は r 元への一般化（ノート §2.5 の課題 T2-1・T2-2）の足がかり。 |
| ノート | `SerrePositivity/BhattScholze/Delta/Basic/DeltaColimit.lean:10` | δ 両立な遷移を持つ有向系の環余極限の δ 構造と普遍性。勉強ノート第 2 章の命題 2.1.6 の有向の場合。 |
| ノート | `SerrePositivity/BhattScholze/Delta/Basic/DeltaQuotient.lean:12` | 勉強ノート第 2 章の命題 2.1.8・2.1.9。 |
| ノート | `SerrePositivity/BhattScholze/Delta/Basic/DeltaRing.lean:14` | 勉強ノート第 2 章の定義 2.1.1〜命題 2.1.5。 |
| ノート | `SerrePositivity/BhattScholze/Delta/Basic/DeltaWitt.lean:15` | 環準同型 A → W(A) を与える。低次の係数、自然性、Witt の Frobenius との両立。勉強ノート第 2 章の定義 2.1.13。 |
| BR・ノート | `SerrePositivity/BhattScholze/Delta/DividedPower/PDivisionCompletion.lean:17` | §2.5 の主張そのものではなく、生の包の p 完備化（BS 著者版 Corollary 2.44・BS 著者版 Proposition 3.13 の対象）の部品（ノート BR32）。 |
| T・ノート | `SerrePositivity/BhattScholze/Delta/DividedPower/PrincipalDP.lean:22` | 原典の BS 著者版 Lemma 2.38 を r = 1 で、離散性・p ねじれなし・pd 包との同一視・底変換・mod p の自由性まで示す。r 元への一般化はノート §2.5 の課題 T2-1。 |
| BR・ノート | `SerrePositivity/BhattScholze/Delta/DividedPower/RankOneDP.lean:36` | BS 固有ではない分冪代数の一般論（BS の外へ出す候補、ノート BR32）。 |
| ノート | `SerrePositivity/BhattScholze/Delta/Free/FreeDeltaFrobeniusFlat.lean:19` | （L/(p,z) → L/(p,φ(z)) の忠実平坦性、(p,φ(z)) の正則性）。勉強ノート第 2 章の命題 2.1.11 (2)。 |
| ノート | `SerrePositivity/BhattScholze/Delta/Free/FreeDeltaRing.lean:16` | 系として任意の δ 環で φ と δ が可換、すなわち φ は δ 射（勉強ノート第 2 章の命題 2.1.5 (4)、命題 2.1.11 (1)）。 |
| ノート | `SerrePositivity/BhattScholze/Delta/Free/RelativeFreeDelta.lean:16` | 勉強ノート第 2 章の命題 2.1.7・2.1.10。 |
| ノート | `SerrePositivity/BhattScholze/Prism/Basic/OrientedPrism.lean:22` | 一般の局所単項なイデアルは扱わない（ノート D5）。 |
| T・ノート | `SerrePositivity/BhattScholze/Prism/Basic/Rigidity.lean:22` | BS 著者版 Lemma 3.5 の後半（B[I] = 0 なら (B, IB) は prism）は扱わない（ノート課題 T3-5）。 |
| BR・ノート | `SerrePositivity/BhattScholze/Prism/Perfection/PrismPerfection.lean:22` | 原典の形（prism の完全化が普遍な完全 prism）の一つの定理にはまとめていない（ノート BR28）。 |
| BR・ノート | `SerrePositivity/BhattScholze/Prism/Perfectoid/PerfectPrismPerfectoid.lean:25` | 圏同値ではなく三つの事実（商の perfectoid 性、perfectoid 環の prism 表示、射の持ち上げ）として述べる（ノート D8、BR29）。 |
| ノート | `SerrePositivity/BhattScholze/Prismatic/PrismOver.lean:48` | /-! ## 濃度の切り落とし（ノート D16） -/ |
| exposition | `SerrePositivity/CommutativeAlgebra/KoszulMultiplicity/FrobeniusGrowth.lean:44` | Roberts の引用の代わりに使う（解説の注意「Roberts の定理を使わない消滅」（`exposition/ja/exposition-ja.tex` の `rem:koszul-elementary`））。 |
| exposition | `SerrePositivity/HomologicalAlgebra/KoszulTorLength.lean:24` | 解説の注意「Roberts の定理を使わない消滅」（`exposition/ja/exposition-ja.tex` の `rem:koszul-elementary`）の手順 2。 |
| exposition | `SerrePositivity/HomologicalAlgebra/TorFiniteLengthBound.lean:23` | 解説の注意「Roberts の定理を使わない消滅」（`exposition/ja/exposition-ja.tex` の `rem:koszul-elementary`）の手順 4。 |
| exposition | `SerrePositivity/HomologicalAlgebra/TorUniformAnnihilator.lean:24` | 解説の注意「Roberts の定理を使わない消滅」（`exposition/ja/exposition-ja.tex` の `rem:koszul-elementary`）の手順 3。 |
