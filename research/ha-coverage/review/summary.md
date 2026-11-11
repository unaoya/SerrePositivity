# Higher Algebra 全巻照合の要約（停止点4）

段0–4の全2,866項目の照合を完了した。序章3件、第1–7章、付録A・Bを含み、重複・欠番・unsureは0件。`citations.csv`と`plan-citations.csv`の参照番号は、節単位の引用を含め、すべて原典の一覧に存在する。

## 原典・照合元

- Lurie, *Higher Algebra*, **2017-09-18版**。取得元・版・全目次は[toc.md](../toc.md)。PDFはリポジトリに含めない。
- PDFのSHA-256：`112b145a95a62daefb8275851cac9ab6430004cfc8f751a33a8d981fd7ad68c3`。
- Lean：`leanprover/lean4:v4.35.0-rc4`。Mathlib：`e6bbacd0e1b7307ff6e17da09cd2455f60804fa6`。
- 段4はmain `7bf1c5fbb`を専用枝`research/ha-review`へ取り込んで照合した。その後の本レーンのコミットは`research/ha-coverage/`だけであり、Leanの本体を変更していない。既存段の証拠はそれぞれの記録コミットを保持する。

## 全巻の件数

| 範囲 | own | mathlib | both | partial | none | unsure | 合計 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 序章 | 0 | 1 | 0 | 1 | 1 | 0 | 3 |
| 第1章 | 32 | 23 | 0 | 121 | 124 | 0 | 300 |
| 第2章 | 0 | 0 | 0 | 28 | 253 | 0 | 281 |
| 第3章 | 0 | 0 | 0 | 12 | 154 | 0 | 166 |
| 第4章 | 1 | 4 | 0 | 151 | 496 | 0 | 652 |
| 第5章 | 3 | 3 | 0 | 35 | 459 | 0 | 500 |
| 第6章 | 0 | 0 | 0 | 23 | 333 | 0 | 356 |
| 第7章 | 1 | 6 | 0 | 77 | 321 | 0 | 405 |
| 付録A | 0 | 2 | 0 | 10 | 123 | 0 | 135 |
| 付録B | 1 | 0 | 0 | 7 | 60 | 0 | 68 |
| 全巻 | 38 | 39 | 0 | 465 | 2324 | 0 | 2866 |

この件数は番号付きの定義・構成・注・例・警告・記法・質問・予想も含む。`own`等を定理の証明率、`none`を未証明定理の数としては使わない。全巻にはRemark 886件、Definition 334件、Question 7件、Conjecture 2件がある。

`partial`は原典の結論を直接与える特殊例・片方向・追加仮定の下の結果・明示的な成分に限定した。単なる証明の部品、異なる対象についての類似結果、未構成の比較を使った推論は`none`に残し、近い候補と足りない比較を理由に記した。通常の導来圏や有界な模型で直接得られる結果は部分対応として区別する。模型の違いについては依頼文§4(5)に従い、同じ主張の模型間比較だけが不足する場合はpartialとして、欠けた比較を明記した。

partial_kindの全巻内訳：component 190・stronger-hyp 70・special 184・direction 21。

## 段4の件数と見つかった対応

| 範囲 | own | mathlib | both | partial | none | unsure | 合計 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 0 | 0 | 1 | 0 | 1 | 1 | 0 | 3 |
| 5 | 3 | 3 | 0 | 35 | 459 | 0 | 500 |
| 6 | 0 | 0 | 0 | 23 | 333 | 0 | 356 |
| A | 0 | 2 | 0 | 10 | 123 | 0 | 135 |
| B | 1 | 0 | 0 | 7 | 60 | 0 | 68 |
| 段4 | 4 | 6 | 0 | 76 | 976 | 0 | 1062 |

段4のpartial 76件を四分類ですべて見直した。第5章の詳細は[ch5-notes.md](ch5-notes.md)、第6章は[ch6-notes.md](ch6-notes.md)、付録は[appendices-notes.md](appendices-notes.md)にある。

- **第5章**：twisted arrowの模型と左右の規約、通常のcenter・Drinfeld braiding、strict monoidの群完備化の一方向、通常の可換代数の単位化・tensor余積、通常の層の一部は使える。全Eₖ認識、Dunn additivity、factorization homology、空間値層とそのVerdier双対の理論は未対応。KSTのVerdier quotientを層のVerdier双対と取り違えない。
- **第6章**：一次切除の懸垂判定の一方向、空間のfiltered余極限による有限極限保存、安定圏の有限双積、通常表現のnormの和の不変性などは使える。Pnの反射とTaylor塔、cross-effect、homogeneous関手の分類、derivative/differential、相対安定化とchain ruleの全理論は未対応。通常のTate複体を任意stable ∞圏のnorm cofiberと同一視しない。
- **付録A**：昇鎖条件のwell-founded性との同値2件はMathlibに一致する。通常層の定数性・stalk判定、upper-set位相、sd/ex、底上の関手空間の式は部分対応する。shape、hypercompletion、conical exit path、constructible sheaf分類、任意recollementの圏同値は未対応。
- **付録B**：任意のSSetの射のpullbackの右随伴がB.4.4の依存積の普遍性を与える。coCartesian/left fibrationでのhornと逆像同値、定数束のfiberwise Homには部分対応がある。一般categorical pattern、P-anodyne、marked model構造、一般flat fibrationのfactorization圏によるiffは未対応。

## 既存段の再点検と訂正

- **第1章**：旧partial 156件を本文・型と再比較し、121件を残し、35件をnoneに変更した。`partial_kind`を補った。局所化前の全複体と導来圏、有界圏と非有界圏、異なるcollage、一般判定と未確認の適用条件を分けた。全変更番号と理由は[ch1-review-notes.md](ch1-review-notes.md)。1.2.3.21の対応を複体のtensor構成そのものへ差し替え、追加で型検査した。通常導来圏・有界入射模型の直接の特殊例を残す検収方針は維持した。
- **3.2.4.7**：通常の可換R代数のtensorが余積、Rが始対象というMathlibの直接の特殊例を確認し、noneからpartial/specialへ訂正した。一般のCAlg(D(R))の構成・比較はなお必要。
- **4.4.1.15・16**：段2の検収時に確定したnoneを維持した。
- **第7章・BS**：[ch7-notes.md](ch7-notes.md)の境界を維持する。調整役の確認では、7.1.3.18はBS界面で埋め込みだけを使い、7.2.2.10はD20がホモロジーの形で定義しているため、この2項目についてBS側の追加作業はない。他の一般的な比較の不足を解消したという意味ではない。

## E∞の経路とKerodon

E∞の不足一覧は[einfinity-gaps.md](einfinity-gaps.md)。∞-operadとoperadic nerve、Alg/CAlg、モノイダル∞局所化、自由代数と色ごとの(余)極限・presentability、既存BE模型との比較が引き続き必要。通常のtensor余積・dg自由代数・相対Kan拡張はそれぞれの限定範囲で再利用できる。

2017年版の**∞-categorical Barr–Beck定理は4.7.3.5**である。6.2.2.14は局所Cartesianなfibrationの相対安定化についての系であり、以前の不足メモのモナド性への引用を訂正した。指定の15項目のE∞印は保持し、4.7.3.5にも追加して計16項目とした。4.7.3.5の現対応は通常圏のG-split余等化子の場合だけpartial/stronger-hyp。Hinich論文が参照する版との番号対応は未確認。

`kerodon`の非空行は全巻**33項目**（段3終了時13→段4で20追加）。同じdocstringの併記を拾う方法に加え、確認済みKerodon表のdeclarations_newと照合し、HA本文でも同じ結論・適用範囲であることを確認した。単に同じ一般補題が使われるというだけの番号は入れていない。

## 保存した証拠と監査

- `review/ch<N>.csv`が判定の正本。`items.csv`のstatus・declarations・reason・confidenceは段0の設計どおり空欄を保ち、目録・引用数・title・goal・kerodonを管理する。
- 各肯定・partial行に`#check @...`の型と`#print axioms`を保存し、対応するソースのコミット・SHA-256を記録した。使用公理は`propext`・`Classical.choice`・`Quot.sound`の部分集合で、追加公理はない。モデル圏を仮定する候補は実instanceと適用範囲を区別した。
- 各none行に引用・同節・隣節、SerrePositivity/Mathlibの検索語・件数、実読ソースと理由を保存した。段4の節単位の一括none（依頼文§4の3′）の使用は0節。
- 第1章の古いnone記録でパスだけだった241のソース参照には、記録当時のコミットからSHA-256を補った。当時の検索結果・理由・分類はこの補完では変更していない。35件の分類変更の新証拠とはファイルを分けた。
- 各JSONは2 MB未満。生のkernel出力・PDF・scratchのビルド生成物はコミットしない。共有のビルド鍵は整理券1枚、`--wait 3600`、各取得580秒上限で使った。

全巻監査では、542肯定・partial行、2324none行、715の宣言・ソース版の組、1028のソースハッシュ記録を確認した。番号の網羅・一意性、statusと証拠の一対一対応、partial_kind、公理、引用数、各証拠の記録コミットでのハッシュを検査した。段4は現ソースとのハッシュ一致も確認した。

再実行方法は[check/README.md](check/README.md)。[check/audit.py](check/audit.py)はLeanやビルドを実行せず、保存済み証拠と記録時のgitオブジェクトを検査する。[check/audit-result.json](check/audit-result.json)に最終結果を保存した。
