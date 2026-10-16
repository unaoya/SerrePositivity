# 完備化の共通基盤と二つの適用の統合計画

> **アーカイブ（2026-10-17）**：この計画は完了したか、ほかへ吸収された。内容の要約先：共通の完備化 API の docstring（`CommutativeAlgebra/` の完備化・平坦性のファイル）。将来は削除する予定で、以下は当時の計画と実施記録のまま。


更新日：2026-10-13。対象は CLMST の根の塔と、外部引用1の剰余体拡大の完備化。
状態（2026-10-16 追記）：引用1・3の解消に使われ、役目を終えた。以下は当時の計画と実施記録で、冒頭の「未着手」等の表現はその時点のもの。
現在のコードと別チャット「可換環の形式化」の進捗を照合した計画である。
この文書を、二つの流れで共有する工程・公開API・分担・完了条件の正本とする。
2026-10-13のコードレビューを反映した計画更新であり、以下の未完部分の実装にはまだ着手していない。
未完の定理を証明済みとは扱わない。固有の証明課題と実装の到達点は各計画に残す。

## 1. 重複の確認

二つの作業の間で、同じ主張・同じ仮定の証明を重ねている公開定理は、確認した範囲ではない。
同じ Mathlib の完備化を使っていることと、同じ結果を独立に再実装していることは区別する。

| 既存モジュール | 主張 | 役割 |
| --- | --- | --- |
| `AdicCompletionInjective` | 一様な誘導フィルトレーション比較から完備化写像の単射性。有限終域への Artin–Rees の比較 | 共通の写像・フィルトレーションの一般論 |
| `AdicCompletionExact` | 一様な比較の下、右全射な完全列の完備化後の完全性 | 共通の完全性 |
| `FlatTensorFiltration` | 平坦テンソル積への比較の移送、有限な中間加群の短完全列の完備化後の完全性 | 共通の平坦性証明の準備 |
| `AdicCompletionQuotient` | 完備化の評価の核と、元の環との全冪商の同型 | 共通の環・商の一般論 |
| `AdicCompletionBaseQuotient` | 上の同型を基底の冪商上の代数同型にする | 係数の両立を含む拡張 |
| `AdicCompletionFlatQuotient` | 平坦代数の完備化の各冪商の平坦性 | 商ごとの平坦性。環全体の平坦性とは別 |
| `AdicCompletionResidue` | 完備化の剰余体と指定体の同定、係数写像の両立 | 局所的な適用の共通 API |
| `AdicCompletionChangeIdeal` | 二つの完備化が相手のイデアルについても完備なら、元の加群の像を保つ線形同型。元の加群の有限性は不要 | 二つのイデアル進完備化を比較する共通API。Cohen–Gabberのパラメータ進・極大イデアル進微分へ適用済み（2026-10-14） |
| `AdicApproximationLifting` | 次数のずれを持つ近似を、前完備な係数加群の極限で実際の像へ持ち上げる | 完備環の Noether 性の準備 |
| `RootTower/CompletionFlat` | 主イデアル完備化での生成元の正則性、未完備塔の平坦性 | 一般正則性と塔への適用が同居 |
| `ResidueFieldGeneralCompletion` | 指定剰余体を持つ完備局所環と、全冪商の平坦性の構成 | 剰余体拡大への適用 |

`AdicCompletionExact` と `AdicApproximationLifting` はともに Cauchy 列を使うが、
前者は逆極限への持上げ、後者は元の前完備加群での極限と分離性を使う。
同一の定理ではない。係数列の小さな共通処理は統合候補だが、現時点で削除対象にはしない。
`AdicCompletionQuotient` は Mathlib の評価の核の定理を使い、環の商同型へ接続する。
核の主張自体を再証明しているわけではない。

進行中の別作業のファイルは未コミットのものも含む。取得したスナップショットの状態であり、
そのファイルの編集・移動・ステージングをこの計画の作成だけでは行わない。

## 2. 統合する中心定理

Noether 基底環 A、イデアル I、平坦 A 加群 P に対し、
I 進完備化 P̂ が A 上平坦であることを、共通層で一度だけ証明する。
P の有限性は要求しない。P が代数 S の場合には、S の Noether 性も要求しない。

加群版の目標の形：

```lean
[CommRing A] [IsNoetherianRing A]
[AddCommGroup P] [Module A P] [Module.Flat A P]
(I : Ideal A) : Module.Flat A (AdicCompletion I P)
```

代数版では A の I を S に拡張して環の完備化を取る。
A 加群としての I 進完備化との比較を証明してから、上の定理を適用する。
二つの完備化の定義が一致すると、比較なしに扱ってはいけない。

```lean
[CommRing A] [IsNoetherianRing A]
[CommRing S] [Algebra A S] [Module.Flat A S]
(I : Ideal A) :
  Module.Flat A (AdicCompletion (I.map (algebraMap A S)) S)
```

二つの適用では、基底がNoether、未完備の代数が平坦、完備化のイデアルが基底からの拡張である。
したがって、上の代数版の完成とイデアル・作用の同定を共通の採用経路とする。
別作業で予定していた「Noether 局所拡大について、全冪商の平坦性から環全体の平坦性を導く判定」
（Stacks 0523による旧案）は、今回の二つの適用の必須工程から外す。
全冪商の結果は保存し、別の対象で必要になった場合に一般の判定を検討する。
この判定を上の定理と並行して独立に実装しない。

## 3. 実装順序と完了条件

1. **既存 API の固定。** 上表の定理を共通層の入口として採用する。
   定義や普遍写像、代数作用を新たに選び直さない。Mathlib との重複を先に確認する。
   `FlatTensorFiltration` の一様な比較と完備化後の完全性は既に証明済み。
2. **有限表示加群とのテンソル比較。** Noether A、平坦 P、有限表示 N に対して、
   次の比較を、下の2a〜2cの順で構成する。P̂の平坦性を先に仮定しない。

   ```lean
   comparison : N ⊗[A] AdicCompletion I P →ₗ[A] AdicCompletion I (N ⊗[A] P)
   ```

   - **2a：標準写像・自然性・有限自由の場合。** 元の加群の元について
     `comparison (n ⊗ of I P p) = of I (N ⊗[A] P) (n ⊗ p)`を証明する。
     N方向の線形写像fに対し、`comparison`と`f.rTensor`・`AdicCompletion.map`の可換図式を証明する。
     有限自由NではMathlibの`AdicCompletion.piEquivOfFintype`とテンソル積の有限直和／積の比較を再利用する。
     Mathlibの`ofTensorProduct`はÂ⊗Nの比較であり、ここで必要なN⊗P̂の同型をそのまま与えるとは扱わない。
   - **2b：有限加群の比較の全射性。** 有限自由F₁からNへの全射を選ぶ。
     テンソル積の右完全性、完備化した写像の全射性
     （Mathlibの`map_surjective_of_mkQ_comp_surjective`）、2aの有限自由での同型から、
     Nの比較写像の全射性を導く。Nへの全射の核で単射性を要求しない。
   - **2c：核を挟んだ余核の比較。** 有限自由全射q:F₀→Nを選び、K=ker qとする。
     Noether Aと有限なF₀からKの有限性を供給する。短完全列K↪F₀→Nに
     `adicCompletion_rTensor_exact_of_finite`を適用し、Kの比較の全射性（2b）、
     F₀の比較の同型（2a）、包含K↪F₀についての自然性から余核を比較する。
     これによりNの比較の単射性と同型を導く。Kの比較の同型を先に要求しない。

   一般の有限自由表示F₁→F₀→Nでは最初の写像は単射とは限らない。
   現在の`FlatTensorFiltration`の完全性定理は左の単射性を要求するため、
   その写像へ直接適用しない。完了条件はNの比較同型、元の加群からの写像との両立、
   N方向の自然性の三つ。型や定義を選んだだけで2を完了扱いしない。
3. **加群版の平坦性。** イデアルJの包含J→AをPとテンソルして完備化する。
   `adicCompletion_rTensor_injective_of_finite`で完備化後の単射性を供給し、
   段2の自然性と同型でJ⊗P̂→A⊗P̂の単射性に移す。
   Mathlibの`Module.Flat.tfae_equational_criterion`の「全イデアルの包含についての単射性」を使う。
   Noether Aから各Jの有限性・有限表示性を確認して段2を適用する。
   PやP̂の有限性、P̂のNoether性・既知の平坦性は追加しない。
   完了条件は上の加群版の型を満たす引用非依存の定理。
4. **代数版と作用の比較。** I^n Sと拡張イデアル(IS)^nの一致を、係数をAへ制限して確認し、
   `AdicCompletion (I.map (algebraMap A S)) S ≃ₗ[A] AdicCompletion I S`を構成する。
   比較そのものには局所性・SのNoether性・平坦性を要求しない方針とする。
   Mathlibの`IsAdicComplete.map_algebraMap_iff`等は既存の完備性の条件の移送に使うが、
   それだけで二つの完備化の型を同一視したとは扱わない。
   元のSからの標準写像、各次数の評価、Aの係数作用の両立を証明する。
   そのA線形同型を使って、代数版の平坦性を段3の加群版から導く。
5. **二つの適用。** 次節の根の塔と剰余体拡大へ、それぞれ同じ代数版を適用する。
   適用ごとに完備化のイデアルの一致と作用を確認する。
6. **配置と文書の整理。** 一般正則性を `RootTower/CompletionFlat` から
   共通の完備化モジュールへ移し、旧 import・宣言名を互換入口で保つ。
   証明内容を変える工程とは分ける。小さな共通処理の抽出は実際の重複が確認できたものだけ行う。

全体の平坦性が完成する前に、段2・3・4を単なる系として完了扱いしない。
新しい sorry・公理や、結論に相当する不透明な条件を追加して進捗としない。

## 4. 二つの適用先と独立した残作業

### CLMST の根の塔

基底のI=`Ideal.span {(p : A)}`を塔へ拡張すると`Ideal.span {(p : Tower A t p)}`になることを確認する。
`flat_tower_over_base` と代数版の完備化の平坦性を合成して、
`Module.Flat A (CompletedTower A t p)` を証明する。完備化のイデアルは (p)。
その後、`CLMST/TensorIsogeny` へ平坦性を供給し、
完備塔⊗_A D の g・p の正則性、有界ねじれ、perfectoid 化写像の単射性と余核の冪零化を得る。
塔の Noether 性は仮定しない。perfectoid 性と isogeny の文献入力は別の境界として保持する。

### 指定剰余体拡大の完備化

`exists_flat_local_extension_of_residueField` が構成する未完備環 S の平坦性を使う。
m_A S=m_S の等式で完備化のイデアルを合わせ、同じ代数版から C の A 上の平坦性を導く。
この部分に C の Noether 性を先に要求しない。
平坦性は、具体的な`let C := AdicCompletion (maximalIdeal S) S`が見える構成の中で適用する。
既存の`exists_complete_local_extension_with_flat_quotients`は、Cがこの完備化であるという
同定を結論に公開していない。その存在定理からCだけを取り出して、完備化として扱わない。
必要なら具体的な完備化の性質を供給する補題を先に分離し、
既存の剰余体・極大イデアルのAPIを再利用して、同じCに平坦性とA4を接続する。

C の Noether 性は独立した共通定理として進める。
有限生成な極大イデアルと完備性から、随伴次数環の有限生成・Noether 性を使って導く。
一般の指定剰余体拡大に、A→C/m の全射や C への係数体の埋込みを勝手に仮定しない。
平坦性と Noether 性が揃って初めて、外部引用1の既存ステートメントを置換する。

## 5. 作業境界と検証

| 作業 | 主担当 | 主な所有ファイル・成果物 | 他方との接続 |
| --- | --- | --- | --- |
| 2a〜2c：比較写像・全射性・同型・自然性 | CLMST側の一般完全性の流れ | 新設候補`AdicCompletionTensor`、既存`AdicCompletionInjective`・`AdicCompletionExact`・`FlatTensorFiltration` | 有限NでPの有限性を要求しない公開APIを両方で利用 |
| 3：加群版の完備化の平坦性 | CLMST側 | 新設候補`AdicCompletionFlat` | Noether基底と平坦Pだけの定理を供給 |
| 4：係数制限の比較と代数版 | CLMST側 | 新設候補`AdicCompletionScalarRestriction`、代数版は`AdicCompletionFlat` | 比較は一般の代数、平坦性の適用で基底のNoether性を使用 |
| A4：完備局所環のNoether性 | 可換環論側（このチャット） | `GradedReesNoetherian`・`ReesIdealLifts`・`AdicApproximationLifting`、既存`AdicCompletionNoetherian`。一般判定は実装済み`AdicNoetherianCriterion` | 各Jの近似の供給・A4・具体的な完備局所環へのNoether性の適用は完了 |
| 冪商・剰余体・極大イデアル | 可換環論側が既存APIを保守 | `AdicCompletionQuotient`・`AdicCompletionBaseQuotient`・`AdicCompletionFlatQuotient`・`AdicCompletionResidue` | CLMST側は既存の宣言・代数作用を再利用 |
| 完備塔とisogenyへの適用 | CLMST側 | `RootTower/CompletionFlat`・`CLMST/TensorIsogeny`とその具体的利用先 | 共通の代数版を適用。塔のNoether性を要求しない |
| 剰余体拡大への適用・引用1の置換 | 可換環論側 | `ResidueFieldGeneralCompletion`・`Inputs/ResidueFieldExtension`とその利用先 | 同じS・その完備化Cに共通平坦性とA4を適用 |
| 6：一般正則性の配置整理 | CLMST側 | `RootTower/CompletionFlat`から新設候補`AdicCompletionRegular`へ抽出 | 平坦性の証明とは別の変更単位。互換入口を保持 |

新設候補名は計画上の名前であり、ファイルや定理を実装済みとは扱わない。
担当は既存の二つの作業の分担であり、この更新から別チャットへの指示送信や新しい作業の起動はしていない。
共通の平坦性とA4は並行できる。A4が共通平坦性を先に使う依存、
共通平坦性がCのNoether性を先に使う依存は作らない。
共通平坦性の受入条件を満たした後、二つの具体的適用をそれぞれの担当で接続する。
外部引用1の置換は、その平坦性とA4の双方が同じCで揃った後に行う。

同じ作業ツリーでは所有ファイルを区別し、他作業の未完コードを上書き・一括コミットしない。
共通層に Paper・CLMST・ResidueField の具体的適用を import させない。
既存共通APIの変更が必要な場合は、その所有側が型・作用・利用先への影響をこの正本に記録して変更する。
`SerrePositivity.lean`、計画一覧、監査の入口は共有ファイルなので、各担当の追加だけを狭く編集・ステージする。
CLMST側は`audit_clmst.lean`、可換環論側は`audit_local_algebra.lean`の追加を担当し、
他方の進捗・検証結果・引用件数を一括で書き換えない。

共通定理は対象ビルドと `assert_no_sorry`、二つの適用は
`audit_clmst.lean` と `audit_local_algebra.lean` で別々に検証する。
全体ビルド・主定理の公理監査で既存の引用境界の変化も確認する。
計画の正本はこの文書とし、各計画は固有の適用・残作業を記し、共通工程はここを参照する。

## 6. 文書の役割と今回の更新範囲

- この正本：共通の目標、2a〜2cの証明手順、分担、公開APIの受入条件を更新する。
- [CLMSTの主計画](../clmst.md)と[実装境界](clmst-interfaces.md)：完備塔・isogenyへの適用、引用境界、CLMST固有の残作業を更新し、共通工程は正本へ参照する。
- [可換環論1〜3の計画](local-algebra-1-3.md)：A4の証明、剰余体・局所性・Noether性、引用1の置換条件を更新し、共通の平坦性工程は正本へ参照する。
- 旧0523経路は代替案の履歴として可換環論側に短く残す。今回の必須工程として並行実装しない。

計画のすり合わせに続く各工程の実施状況は、以下の記録と担当側の計画で更新する。

## 7. 実装の続き：テンソル比較と加群版の平坦性

2026-10-13、計画2a〜2cと3を実装した。
`AdicCompletionTensor` の比較写像は、各 n のテンソル写像の完備化で構成し、
元の加群からの標準写像との両立と N 方向の自然性を証明した。
有限自由加群では比較は同型、有限加群では比較は全射であり、
これらには基底の Noether 性・P の平坦性は不要。
Noether 基底で有限 N・平坦 P の場合には、核を挟んだ短完全列から単射性も導き、
`adicCompletionTensorEquiv` を構成した。P̂ の平坦性を前提にしていない。

`AdicCompletionFlat.flat_adicCompletion_of_flat` は、イデアルの包含と自然性を使い、
Noether A 上の任意の平坦加群 P に対して `Module.Flat A (AdicCompletion I P)` を証明する。
P の有限性・前完備性は不要。新しい sorry・外部引用はない。

残る共通工程は段4の係数制限による完備化の比較と代数版の平坦性。
その後に二つの具体的適用を行う。加群版の証明だけで、
`CompletedTower` や指定剰余体拡大の環の完備化の平坦性を完成扱いしない。
A4は可換環論側で完成した。完備局所実現にCのNoether性を供給済みで、Cの基底上の平坦性の接続は別工程。

検証：全体ビルド3959ジョブと両公理監査が成功。新規の公開10宣言は sorry 非依存。
共通層に Paper への推移的 import はなく、主定理の未証明入力は13件のまま。

### 可換環論側：A4の完成

`ReesCoefficientApproximation`で有限なRees生成元から次数付き近似を構成し、
`AdicApproximationLifting`へ適用して全イデアルの有限生成性を証明した。
`AdicNoetherianCriterion`はI.FG・I進完備性・R/IのNoether性からRのNoether性を導く。
局所版と、元の環が非Noetherでも使える完備化版も供給した。
`ResidueFieldGeneralCompletion`の具体的な完備局所環CにもNoether性を適用した。
共通の代数版の平坦性や引用1の置換を、この成果だけで完了扱いしない。

## 8. 実装の続き：係数制限・代数版と二つの具体的適用

2026-10-13、計画4の共通部分を実装した。
`AdicCompletionScalarRestriction` は、拡張イデアルによる完備化と基底のイデアルによる
加群の完備化の A 線形同型を、各冪商の同型と遷移写像の両立から構成する。
元の加群からの標準写像、各次数の評価との両立も証明済み。
Noether 性・平坦性・局所性は比較の仮定にない。
`flat_adicCompletion_algebra_of_flat` はこの比較から代数版の平坦性を導く。
代数 S 自身の Noether 性・有限性は要求しない。

計画5の CLMST 側では、`flat_completedTower_over_base` で基底からの(p)の拡張を確認し、
完備化した根の塔の A 上の平坦性を証明した。
`CLMST/CompletedTensorIsogeny` はこれを具体的なテンソル代数へ適用し、
標数零の有限整域拡大と係数写像の単射性の下で g・p の正則性を供給する。
非零 g の選択も一般の有限エタール性から導き、同じ選択された perfectoid 化への
標準写像の単射性・余核の g 冪による零化を証明した。
存在と命題2.4.7の文献入力への依存は保持する。

剰余体側でも、別作業の `ResidueFieldGeneralCompletion` が同じ代数版を実際の C へ適用し、
Noether 性の判定と合わせ、外部引用1の入口を証明へ置き換えたことを作業ツリーで確認した。
剰余体側の接続をこちらに重複実装せず、その入口を採用する。
この側の進行中のファイル・コミットは可換環論側が保守する。

計画6の一般正則性の配置整理も実施。`AdicCompletionRegular` を共通層とし、
`RootTower/CompletionFlat` は同じ宣言名を import して塔への適用だけを行う。
残る CLMST の後続工程は余核の作用の比較と Koszul・長さへの接続、命題4.0.14の証明。
完備化の共通平坦性と、これらの深い文献結果の証明は区別する。

検証：全体ビルド3964ジョブ、CLMST・可換環論の監査と主定理の公理監査が成功。
新しい共通比較・平坦性・正則性に sorry 依存はない。
共通層および新しい CLMST 入口に Paper への推移的 import はない。
統合した作業ツリーで主定理の未証明入力は12件（外部入力10件と保留K理論2件）となった。
引用1の置換とその検証は、可換環論側の変更を含む状態での結果である。

### 可換環論側：引用1の解消

共通の`flat_adicCompletion_algebra_of_flat`を、m_B S=m_Sに沿って同じ具体的なCへ適用した。
`adicCompletion_local_residue_properties`により、そのCのNoether性・完備性・指定剰余体を供給する。
`exists_complete_flat_local_extension_of_residueField`で既存引用1の一般形を証明し、
`Inputs.exists_complete_flat_local_extension`を型を保った適用へ置換した。
補題2.1への接続も引用非依存。CLMST側の具体的適用の進捗とは分けて記録する。

### 可換環論側：混標数Cohen正規化（引用3）の解消

Witt係数写像と剰余体の両立、pを含むパラメータ、標準冪級数基底の構造を実構成した。
小さいイデアルへの完備性の移行と、係数・変数の和に沿う完備性を使い、
同じ冪級数評価について閉ファイバーの有限性と評価の有限性を確認した。
基底と対象の次元一致から単射性も供給し、引用3の既存型を証明済みの構成へ置換した。
一般Cohen環や完備化の平坦性を新たな引用へ移したのではない。
全体ビルド4002ジョブと公理監査が成功。外部引用9件・保留K理論2件が残る。
詳細と可換環論側の次の課題は [1〜3の計画](local-algebra-1-3.md) を参照。
