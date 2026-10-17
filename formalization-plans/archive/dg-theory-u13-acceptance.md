# U13 全体の受入記録

> **アーカイブ（2026-10-18）**：M5（dg 理論）は 2026-10-17 に完了（中心作用・群作用は M9 へ）。現状と再開点は [M5 の完了状況](../dg-theory-m5-status.md)。将来は削除する予定で、以下は当時の計画と実施記録のまま。


正本は `dg-theory.md` §15.3 と §17.86–17.113。
任意可換環、非有界cochain複体、dの次数+1、ホモトピー次数−1、Mathlib Enrichedを維持する。
**U13a〜eを受け入れる（2026-10-17）。** 一対象環の導来retractの有界有限射影代表、
元のPerfectHomotopyのホモトピー冪等分裂と、Karoubi包絡を介さない元の比較の同値を証明した。
以下のU13e.27–40は各単位の実装記録であり、途中段階の保留は最終照合で解消した。

## 要件の棚卸し（2026-10-17）

| 項目 | 現在の証拠・判定 |
| --- | --- |
| U13a：指定生成元のfinite cell、有限support、全Hom射影性 | 既存証明あり。`FiniteCell`, `FiniteCellProjective`。§17.74–75で受入済み |
| U13b：主導来圏内のfinite cellのretractとしてのPerf、thick閉性、Karoubi比較 | 既存証明あり。`Basic`, `Triangulated`, `KaroubiEquivalence`, `UniversalProperty`。§17.76–80・87 |
| U13c：代表加群のcompact性、Perf⇒compact、小さいcompact生成族 | 既存証明あり。`RepresentableHomology*`, `RepresentableCoproduct*`, `PerfectCompact`, `Generators`。§17.81–86 |
| U13d：compact⇒Perf | 現在は引用なしの証明あり。`CompactConverse.moduleCompact_iff_perfect`。§17.113以前の未完記録は現状の判定に使わない。U14c.11でも実際に適用・公理監査済み |
| U13e：全Homを持つ射影的perfect dg enhancement、H⁰の線形同値 | 既存証明あり。`Enhancement`, `EnhancementLinear`。§17.88 |
| U13e：finite cellの小さい代表系、Perfの本質的小性、小さいdg enhancement | 既存証明あり。`SmallStages`, `SmallStageCover`, `EssentiallySmall`, `SmallEnhancement`。§17.89–90 |
| U13e：実際の整数shift、零・加法coherence、標準dg cone三角形との一致 | 既存証明あり。`EnhancementShift*`, `EnhancementTriangulated`, `EnhancementConeComparison`。§17.91–98 |
| U13e：小さい代表系へのshift・三角構造と包含の整合性 | 既存証明あり。`SmallEnhancementTriangulated`。§17.94 |
| U13e：一対象Aと非有界複体・既存PerfectHomotopyの全Hom・線形・shift・三角比較 | 既存証明あり。`StrictComplex*`, `RingPerfectComparison`, `RingPerfectTriangulated`。§17.99–110 |
| U13e：finite cellの有限射影評価、主Perfの比較像へのretract表示 | 既存証明あり。`RingFiniteCell`, `RingRetract`。§17.108・111 |
| U13e：Karoubi実現・元の比較へのfactorと導来・三角図式の整合性 | 既存証明あり。`RingKaroubi`, `RingKaroubiFactors`。§17.112–113 |
| U13e：実際の射影的perfect dg enhancement内でのホモトピー冪等分裂 | 今回証明。以下U13e.27。分裂対象は実際の射影的perfect dg加群である |
| U13e：既存PerfectHomotopy自身のホモトピー冪等分裂 | 今回証明。U13e.39–40。分裂対象は有界有限射影複体であり、実際の閉零射と境界関係の版も構成 |
| U13e：主Perfのretractの有界有限射影代表、Karoubiなしの本質的全射 | 今回証明。U13e.37–39。通常DerivedCategoryと主dg導来圏の両方で有限射影代表を構成し、元の比較の同値・実際のdg比較の準同値を証明 |
| U13e：新同値と元のretract・線形・shift・三角比較の接続 | 今回証明。U13e.39–40。順関手は元の比較そのもの。導来包含・三角形関手の自然同型、unit/counitのshift整合性、retractの二式を監査。既存Karoubi factor図式も合同再検証 |

## U13e.27：実際のenhancementのホモトピー冪等分裂

- `Perfect/EnhancementIdempotents.lean`：主Perfの既存冪等完備性を既存U13同値で運び、
  全射影的perfect H⁰と小さい代表系のH⁰の冪等完備性を証明した。
- `perfectDGModule_homotopyIdempotent_splits` は、閉零射pに対する
  `boundaryRelation (p ≫ p) p` から実際の射影的perfect dg加群Yと閉零射i,rを構成する。
  i≫rと恒等射、r≫iとpの一致を同じ全Hom複体の境界関係で証明した。
  strict chain idempotentであることを仮定していない。
- `Perfect.ChecksEnhancementIdempotents` 対象ビルド成功（2490 jobs）。
  主要4宣言の公理は `propext`, `Classical.choice`, `Quot.sound` のみ。
  既存のPerfectファイル・PerfectComplex・Idempotent一般論を編集していない。

## U13e.28：導来retractの最上ホモロジーの有限生成性

- `Perfect/RingRetractTopHomology.lean`：複体Pの上端nでdが零なら、cyclesとP.X nの同型と
  ホモロジーへの全射からHⁿ(P)の有限生成性を証明した。
- 主dg導来ホモロジーと通常複体のホモロジーの比較を実際の一対象評価自然同型から構成し、
  Pの主導来像の任意のretractの最上ホモロジーも有限生成であることを証明した。
  Noetherian性は不要。任意の次数のホモロジーの有限生成性を主張していない。
- `Perfect.ChecksRingRetractTopHomology` 対象ビルド成功（3163 jobs）。
  主要5宣言の公理監査は標準3公理のみ。次数幅の帰納法の入力であり、有限射影代表の完成はまだ主張しない。

## U13e.29：有限自由singleによるホモロジー被覆

- `Perfect/RingFiniteHomologyCover.lean`：任意の非有界複体PについてHⁿ(P)が有限生成なら、
  有限自由加群を次数nだけに置いたsingleからPへの実際のchain mapでHⁿ上全射となるものを構成した。
- 有限自由加群の射影性で、ホモロジーへの有限自由全射をcyclesへ持ち上げる。
  singleのcyclesの標準同型とホモロジー射の自然性を使って全射性を証明した。
  Pの各項の有限生成性や有界性を要求しない。
- `Perfect.ChecksRingFiniteHomologyCover` 対象ビルド成功（3164 jobs）。
  主要4宣言の公理監査は標準3公理のみ。

## U13e.30：最上のacyclic射影項を切り詰める有限射影モデル

- `Perfect/RingTopTruncation.lean`：隣接微分dが全射で標的項が射影的な場合、
  そのsectionからcycles包含のretractionを構成した。始域項が有限射影ならcyclesも有限射影となる。
- 良い切断 `P.truncLE n` のn未満の項は元の項、nの項はcycles、nより上は零という
  Mathlibの同型を使い、切断の有限射影性と下端範囲の保存を証明した。
- Pの項がn+1より上で零、Pがn+1でexactなら、nへの切断は有限射影であり、
  元のPへの標準包含がquasiIsoである。`ringComplex_topTruncation` として公開した。
- `Perfect.ChecksRingTopTruncation` 対象ビルド成功（3165 jobs）。
  主要6宣言の公理監査は標準3公理のみ。既存の切断・PerfectComplexのファイルは編集していない。

## U13e.31：有限射影上端被覆のconeの短縮

- `Perfect/RingHomologyCoverCone.lean`：Hᵇ上全射のchain mapと始域Hᵇ⁺¹の零性から、
  既存cone長完全列を使ってconeのbでのexact性を証明した。
- 次数bだけに置いた有限射影加群から、[a,b]にある有限射影複体Pへの上端被覆に対し、
  a<bならconeを[a,b−1]の有限射影複体で表す標準quasiIsoを構成した。
  U13e.30の良い切断を適用し、上下の次数範囲も明示的に保持する。
- `Perfect.ChecksRingHomologyCoverCone` 対象ビルド成功（3166 jobs）。
  主要5宣言の公理監査は標準3公理のみ。
  retract対象と補対象の被覆をこの操作へ同時に接続する帰納ステップを引き続き実装する。

## U13e.32：任意の導来対象の有限自由被覆と有限射影始域の射の持ち上げ

- `Perfect/RingDerivedFiniteCover.lean`：有限射影複体Pから任意の複体Kへの
  既存DerivedCategoryの射が実際のchain mapで表されることを、MathlibのK-projective局所化Hom計算と
  ホモトピー商の充満性から証明した。
- 任意の導来対象XのHⁿが有限生成なら、有限自由singleのQ像からXへのHⁿ上全射の射を構成した。
  元の複体での全射性を既存ホモロジー比較の自然同型で運ぶ。
  導来retractの上端ホモロジーの有限生成性にも通常DerivedCategory上の版を与えた。
- 任意の `HasDerivedCategory.{w} (ModuleCat.{u} A)` を明示して使い、主導来圏を再定義していない。
  `Perfect.ChecksRingDerivedFiniteCover` 対象ビルド成功（3168 jobs）。主要4宣言の公理監査は標準3公理のみ。

## U13e.33：retract・補対象の三角形と有限射影coneの比較

- `Perfect/RingRetractTriangle.lean`：既存の分裂三角形からretract X⊂Yの補対象Zと
  Y≅X⊞Zを構成した。retractの存在を仮定しているため、ここでは冪等完備性の追加仮定は不要。
- X・Zを終域とする二つのdistinguished三角形の直和を取り、始域が有限射影singleのQ像、
  終域がQ(P)である場合に、第一射を実際のchain mapへ持ち上げてconeを比較した。
  第一射のHᵇ上全射性を保ち、元の片方の第三頂点をそのconeのQ像のretractとして表した。
- ホモロジーと二項直和の比較には既存のhomological functorのbiproduct保存を用いた。
  `Perfect.ChecksRingRetractTriangle` 対象ビルド成功（3170 jobs）。主要4宣言の公理監査は標準3公理のみ。

## U13e.34：導来retractの次数幅を下げる帰納ステップ

- `Perfect/RingRetractRangeReduction.lean`：有限射影複体Pが[a,b]にありa<bのとき、
  Q(P)のretract Xとその補対象の上端ホモロジーを有限自由singleで同時に覆った。
  二つのdistinguished三角形の直和をU13e.33でP上の実際のconeへ比較し、U13e.31で上端を切り詰めた。
- その結果、有限自由single→X→Yのdistinguished三角形と、Yが[a,b−1]の有限射影複体の
  Q像のretractになる証拠を構成した。元のXを表す有限射影代表は、帰納結果と逆回転三角形から戻す。
- `Perfect.ChecksRingRetractRangeReduction` 対象ビルド成功（3171 jobs）。主要宣言の公理監査は標準3公理のみ。

## U13e.35：一次数の有限射影複体の導来retractのモデル

- `Perfect/RingRetractSingle.lean`：有限射影加群FのsingleのQ像へのretractが与える冪等元を、
  既存single関手の完全忠実性で加群Fの冪等元へ戻し、ModuleCatで分裂した。
  分裂加群Gの有限生成性・射影性とQ(single G)≅Xを証明した。
- [n,n]にある任意の有限射影複体Pを実際のsingleと同型で比較することで、
  Q(P)の任意の導来retractにも[n,n]の有限射影代表を与えた。次数幅帰納法の基底ケースである。
- `Perfect.ChecksRingRetractSingle` 対象ビルド成功（3174 jobs）。主要2宣言の公理監査は標準3公理のみ。

## U13e.36：逆回転三角形からの有限射影代表の復元

- `Perfect/RingTriangleFiniteModel.lean`：single→X→Kのdistinguished三角形で、
  singleが次数b、Kが[a,b−1]の有限射影複体で表される場合、Xを[a,b]の有限射影複体で表した。
- 逆回転三角形の第一射をK[−1]からsingleへの実際のchain mapへ持ち上げ、coneを取る。
  既存Qのshift比較とdistinguished三角形の比較を使い、得たconeのQ像がXと同型であることを証明した。
- `Perfect.ChecksRingTriangleFiniteModel` 対象ビルド成功（3175 jobs）。主要宣言の公理監査は標準3公理のみ。

## U13e.37：有限射影複体の任意の導来retractの有限射影代表

- `Perfect/RingRetractFiniteRepresentative.lean`：`ringDerivedRetract_finiteRange` を次数幅の
  帰納法で証明した。[a,a+width]の有限射影複体PのQ像の任意のretract Xについて、
  同じ次数範囲の有限射影複体KとQ(K)≅Xを構成する。
- 基底はU13e.35、帰納ステップはU13e.34の短い範囲のretractとU13e.36の逆回転三角形である。
  任意のstrictlyPerfectComplexに対する `ringDerivedRetract_finiteProjective` も証明した。
- 任意可換環、任意の既存 `HasDerivedCategory.{w}` で成立し、Noetherian性・flat性・引用を使わない。
  `Perfect.ChecksRingRetractFiniteRepresentative` 対象ビルド成功（3176 jobs）。主要2宣言の公理監査は標準3公理のみ。

## U13e.38：一対象主Perfの全対象の有界有限射影代表

- `Perfect/RingPerfectRepresentatives.lean`：既存の一対象主導来圏と通常DerivedCategoryの同値で
  U13e.37のretractの有限射影代表を主dg導来圏へ戻した。
- `modulePerfect_ring_has_strictlyPerfectRepresentative` は一対象Aの任意の主perfect対象Xに対して、
  有界有限射影複体Kと、実際の定数dg加群の主局所化像Q(ringModule K)≅Xを返す。
  finite cellの評価の有限射影性と、元の加群の厳密な復元を使用している。
- 証明内の通常DerivedCategoryは標準宇宙u+1で選び、結論にはその選択を仮定として残さない。
  `Perfect.ChecksRingPerfectRepresentatives` 対象ビルド成功（3177 jobs）。主要3宣言の公理監査は標準3公理のみ。

## U13e.39：元のPerfectHomotopyの同値・有限射影冪等分裂

- `Perfect/RingPerfectEquivalence.lean`：U13e.38の有限射影代表を元の
  `perfectHomotopyToDGPerfect` の本質像として表し、本質的全射性を証明した。
  既存の完全忠実性と合わせ、Karoubi包絡を介さない `ringPerfectHomotopyEquivalence` を構成した。
  その順関手は元の比較そのものであり、既存の線形性・整数shift・三角性を保持する。
- 元の `PerfectHomotopy` 自体の冪等完備性を証明した。
  `perfectHomotopy_idempotent_splits_complex` は任意のホモトピー冪等元を分裂し、
  分裂対象の有界有限射影複体Kと元のホモトピー圏の分裂射・二つの等式を返す。
- 実際のdg比較 `strictPerfectDGComplexToPerfectDG` について、全Homの擬同型と
  H⁰の本質的全射を別に証明し、準同値を構成した。
- `Perfect.ChecksRingPerfectEquivalence` 対象ビルド成功（3206 jobs）。
  主要17宣言の公理監査は標準3公理のみ。追加の環の仮定・引用はない。

## U13e.40：実際の閉零冪等分裂とretract・導来・三角図式

- `Perfect/RingPerfectCoherence.lean`：有限射影dg複体のH⁰の冪等完備性と、
  閉零射pが境界まで冪等な場合の実際の有界有限射影複体Y・閉零分裂射を構成した。
  分裂の二式は全Hom複体の境界関係で成立し、strict冪等性の追加仮定を置かない。
- 元のPerfectHomotopyでの分裂は、元の主Perf比較の下でも同じ冪等元と分裂等式を与える。
  新同値の順関手は元の比較そのものであるため、主導来包含との既存の自然同型・整数shift整合性を保持し、
  三角形関手の比較自然同型も構成した。同値のunit/counitのshift整合性も監査した。
- `Perfect.ChecksRingPerfectCoherence` 対象ビルド成功（3207 jobs）。
  主要8宣言の公理監査は標準3公理のみ。
- 既存 `Perfect/RingKaroubiFactors.lean` への変更は、この新ファイルのpublic import一行だけ。
  既存のKaroubi factor・shift・導来・三角比較と新しい元の同値を同じ入口から利用できる。

## 既存項目の再検証

- finite cell・全Hom射影性・PerfとKaroubi・compact生成・compact⇒Perf・
  小さいenhancement・標準cone比較・既存PerfectHomotopy比較・retract表示・Karoubi factorの
  17既存監査対象を合同ビルドし、3240 jobsで成功した。
- 274件の公理監査出力はすべて標準3公理のみ。
  この初回再検証は既存項目の証拠であり、有限射影代表・元の比較の本質的全射の証明はU13e.37–40による。

## 最終合同検証（2026-10-17）

- 上記17既存対象、新規14単位の各公理監査対象、U14cの入力除去版と既存Compatibilityの
  計33対象を合同ビルドした。3512 jobs、終了コード0、警告・エラー0件。
- 357宣言の公理監査はすべて `propext`, `Classical.choice`, `Quot.sound` のみ。
  新規U13単位の監査宣言は計66件。既存宣言の名前・型は変更していない。
- 新規実装は `DifferentialGraded/Perfect/` 内に置いた。
  既存Perfectファイルの変更は `RingKaroubiFactors.lean` のpublic import一行だけ。
  既存PerfectComplex・Idempotent一般論、共有ルート・Stage・README、他担当系列は編集していない。
- 新規sorry・axiom・引用は0件。有限射影代表の証明は次数幅帰納法であり、
  DG-PER・Brown表現性・Noetherian性を仮定しない。
- U14cの `compactToPerfect` 入力除去は `DerivedEquivalenceCompactGenerator.lean` と
  `dg-theory-u14.md` のU14c.11に記録した。元の入力付きAPIは保持し、thick生成・compact生成の仮定を残す。
- 各実装単位を自分のパスだけで個別コミットし、各commit後のstatを確認した。
  U13e.33の直後は別チャットのcommitがHEADになったため、自分のhash `e56a1d30` も個別照合した。
  他人のファイルの取り込みはない。

## 範囲の区別

- 元の各chain代表そのものへのstrict idempotentの持ち上げは受入条件にしない。
  必要なのは、ホモトピー圏で分裂し、分裂対象が有界有限射影複体で表されること。
  同じ複体上のstrict冪等元であることとホモトピー冪等性を同一視しない。
- 任意dg圏の各評価成分が有界有限射影であることは要求しない。一般dg圏のU13eは
  実際の射影的perfect dg加群の全Hom enhancementを使い、有界有限射影代表の照合は一対象環Aの場合である。
- 任意の可換環のPerfectHomotopyに通常のtruncationが閉じるとは仮定しない。
  有界t構造の冪等完備性を適用するためのt構造を、証明なしに置かない。
- D4mのモデル比較、U14–17のMorita・商の作業はU13全体の今回の受入範囲外。
  他担当のQuotient・Verdier・Bimodule・Tensor・Resolution・指定Derived系列は編集しない。
- DG-PER等の引用は採用していない。必要となれば、採用せず停止・報告する。

## 最終判定

U13a〜dの既存証拠とU13eの全要件を照合した。§17.112–113で残っていた
元のPerfectHomotopyのホモトピー冪等分裂・retractの有限射影代表・元の比較の本質的全射は解消した。
U13の受入範囲内の未完項目はない。正本 `dg-theory.md` §15.3への変更は本記録の参照一行のみ。
