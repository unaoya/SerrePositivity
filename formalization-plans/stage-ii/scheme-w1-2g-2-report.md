# SC-W1 2g-2：G3〜G5 の実装記録

2026-11-15。2g-1 の数学 e5b3e411f・停止点報告56ea849a3 の後、既承認の G3 へ進む。G1・G2 は17／17完了。2g-2 の外枠16,000行は別計上し、最終の AugmentedRingCechExact と利用側の型は変えない。root・下流全ビルドを行わず、対象と直接 importer、小監査を共有鍵 --class impl --wait 3600 で別々に検証する。

## 主項目の一覧

| ID | 型・出口 | 状態 | 追加 |
| --- | --- | --- | --- |
| G3 | BS17 Lemma 2.6 の帰納的レベルの有限性と、射影版の入力に使うブローアップ・有限ファイバー冪の表示 | 未完 | |
| G4 | B1 の二重 Čech の API と 2f の射影 Čech 四角形を使う、Thm 2.9 十分性のこのレーンの係数への実装 | 未完 | |
| G5 | 実際の有限型模型・Frobenius 係数と filtered な Čech 完全性の移送、最終型への入口 | 未完 | |

一覧：済み0／全体3（うち追加0）。

## G3 の最初の束：帰納的レベルと精密化の法則（着手前の型）

原典 [BS17 Definition 2.5・Lemma 2.6](https://arxiv.org/pdf/1507.06490#page=5) を再照合した。零段は有限表示 nilimmersion と proper fppf の合成による実際の細分。正段は nilimmersion・閉中心外で同型な固有全射・proper fppf の合成による実際の細分と、閉中心への底変換の一段低いレベル。後続の存在証明では一般の固有射の四角形の完全性を追加せず、2d が供給するブローアップを選ぶ。

- `ProperInductiveLevel n f`：スキームと実際の射を保持する再帰的命題。nilimmersion は閉埋め込み・全射・局所有限表示を明示し、正段の中心は IdealSheafData とその閉部分スキームで表す。余分な固有性・模型の存在を最終の主張の仮定にしない。見込み60〜140行。
- `ProperInductiveLevel.of_proper_fppf`：固有・平坦・全射・局所有限表示の f のレベル0。nilimmersion に恒等射を選ぶ構成の単位の法則。
- `ProperInductiveLevel.of_refinement`：h:X→Y のレベルn、a:X→Z、g:Z→Y、a≫g=h なら g のレベルn。既にある精密化の射と a を合成するだけで、元の f の性質を弱めた存在定理にはしない。前項と合わせ見込み50〜120行。
- 次の束で底変換の法則、有限型 F_p 基底の次元の減少、2d の実際の細分への適用、Rees・有限ファイバー冪の射影表示を順に扱う。各束の型を先に追記する。現時点の G3〜G5 の全体の見込みは既承認の約5,500〜12,000行、外枠16,000行を維持する。

導来関手の H^i との比較は作らず、2e〜2f と同じ Čech 版を使う。G3 のレベルの存在はまだ証明していない。G4 の二重複体の可換性を、被覆ごとの H の同型を並べるだけで代用しない。


## G3：最初の定義と精密化の法則の検証

`ProperInductiveLevel`（59行）：`ProperInductiveLevel` は原典 Definition 2.5 の実際の因子分解を保持する再帰的命題。`ProperInductiveLevel.of_proper_fppf` は proper fppf のレベル0。`ProperInductiveLevel.of_refinement` は実際の細分の射の合成による消去の法則。

本体59行・入口1行。最初の単独検証、ソース完全一致、対象・直接 importer のビルド5,067ジョブ、小監査8宣言・標準三公理のみ、終了状態0。追加公理・sorry・既存宣言の型変更・200行超の宣言なし。鍵は各検証中だけ使用。ログ `2g-proper-inductive-level-check.log`・`2g-proper-inductive-level-native.log`・`2g-proper-inductive-level-audit.log`。G3 のレベルの存在は未完。

2g-2 本体59行・入口込み60行。外枠16,000行。全体の見込み約5,500〜12,000行を維持。

一覧：済み0／全体3（うち追加0）。

### 次の法則の分割（着手前の型、G3 の内数）

- `ProperInductiveLevel.zero_baseChange`：レベル0の f:X→Y と任意の g:T→Y から、実際の pullback.snd f g のレベル0を返す。nilimmersion と proper fppf の二段の pullback を、既存の closedRestrictionBaseChangeMap と Cartesian square の貼り合わせで保持する。見込み50〜100行。
- `ProperInductiveLevel.iso_source_iff`：始域の同型による移送。実際の細分からの消去を二方向に使う。見込み10〜30行。

正段の底変換・次元帰納・射影表示はなお残る。これらの法則だけで Lemma 2.6 を完成としない。


## G3：零段の任意の底変換と始域の同型の法則

`ProperInductiveLevelZeroBaseChange`（59行）：`ProperInductiveLevel.iso_source_iff` は始域の同型によるレベルの移送。`ProperInductiveLevel.zero_baseChange` はレベル0の実際の二段の細分を任意の基底変更に沿って移す。nilimmersion は実際の pullback、proper fppf は既存の closedRestrictionBaseChangeMap の Cartesian 正方形で保持する。底変換に平坦性を要求しない。

本体59行・入口1行。最初の単独検証、ソース完全一致、対象・直接 importer のビルド5,068ジョブ、小監査2宣言・標準三公理のみ、終了状態0。追加公理・sorry・既存宣言の型変更・200行超の宣言なし。ログ `2g-proper-inductive-level-zero-base-change-check.log`・`2g-proper-inductive-level-zero-base-change-native.log`・`2g-proper-inductive-level-zero-base-change-audit.log`。鍵は各検証中だけ使用。

2g-2 は2モジュール本体118行・入口込み120行、小監査10宣言・標準三公理のみ。G3〜G5 は未完。外枠16,000行、全体の見込み約5,500〜12,000行は不変。

一覧：済み0／全体3（うち追加0）。

### 次の正段の法則（着手前の型、G3 の内数）

`ProperInductiveLevel.baseChange`：任意の n、実際の f:X→Y、g:T→Y に対し、ProperInductiveLevel n f から ProperInductiveLevel n (pullback.snd f g) を返す（見込み150〜350行、Cartesian 比較は分割）。正段では nilimmersion の pullback と r,q の合成の二段の底変換、J.comap の閉中心・補開集合を保持する。閉中心への pullback の比較を、帰納仮定と始域の同型の法則へ渡す。`preimage_centerComplement_comap` と既存のイデアル層の comap の Cartesian 比較を再利用する。基底変更の平坦性を仮定しない。次元帰納と存在定理はこの法則の後に続ける。


正段の底変換の Cartesian 比較の分割（上記150〜350行の内数、着手前の型）：`inductiveCenterBaseChangeProjection J h` は (J.comap h).subscheme→J.subscheme、`isPullback_inductiveCenterBaseChangeProjection` は J.comap の実際の閉包含との Cartesian 正方形。`inductiveCenterRestrictionBaseChangeMap r h J` は r の底変換の閉中心上の射から元の閉中心上の射への実際の射。`isPullback_inductiveCenterRestrictionBaseChangeMap` はその正方形の Cartesian 性を返す。これにより中心上の新しい射を、元の中心上の射の底変換と canonical に比較する。いずれも既存の comapIso・pullback の貼り合わせの法則で、新しい独立した存在定理に数えない。


## G3：閉中心と中心上の射の Cartesian 比較

`InductiveCenterBaseChange`（63行）：`inductiveCenterBaseChangeProjection` は逆像中心から元の中心への実際の射、`isPullback_inductiveCenterBaseChangeProjection` は逆像中心の Cartesian 比較。`inductiveCenterRestrictionBaseChangeMap` は中心に制限した新しい射から元の射への比較射、`isPullback_inductiveCenterRestrictionBaseChangeMap` はその Cartesian 性。中心の被約化・底変換の平坦性は要求しない。

本体63行・入口1行。合成の括弧の照合を修正して単独検証、ソース完全一致、対象・直接 importer のビルド5,069ジョブ、小監査9宣言・標準三公理のみ、終了状態0。追加公理・sorry・既存宣言の型変更・200行超の宣言なし。ログ `2g-inductive-center-base-change-check-2.log`・`2g-inductive-center-base-change-native.log`・`2g-inductive-center-base-change-audit.log`。鍵は検証中だけ使用。

2g-2 本体181行・入口込み184行、小監査19宣言・標準三公理のみ。G3〜G5 は未完。外枠16,000行、見込み約5,500〜12,000行は不変。

一覧：済み0／全体3（うち追加0）。


## G3：全レベルの任意の底変換

`ProperInductiveLevelBaseChange`（90行）：`ProperInductiveLevel.baseChange` は任意の n、f:X→Y、g:T→Y に対し、f のレベルnから実際の pullback.snd f g のレベルnを返す。正段の nilimmersion・proper fppf と固有全射は実際の底変換で保持し、閉中心上の帰納仮定を Cartesian 比較の同型で移す。中心外の同型性も制限した Cartesian 正方形で移す。基底の Noether 性・底変換の平坦性を要求しない。

本体90行・入口1行。略記と中心外開集合の逆像の等式を明示して単独検証、ソース完全一致、対象・直接 importer のビルド5,070ジョブ、小監査1宣言・標準三公理のみ、終了状態0。追加公理・sorry・既存宣言の型変更・200行超の宣言なし。ログ `2g-proper-inductive-level-base-change-check-3.log`・`2g-proper-inductive-level-base-change-native.log`・`2g-proper-inductive-level-base-change-audit.log`。鍵は各検証中だけ使用。

2g-2 本体271行・入口込み275行、小監査20宣言・標準三公理のみ。G3〜G5 は未完。外枠16,000行、見込み約5,500〜12,000行は不変。

一覧：済み0／全体3（うち追加0）。

## G3 の存在証明の組み立てと次の法則（着手前の型）

Lemma 2.6 に必要な出口は `∃ n, ProperInductiveLevel n f`。原典の次元によるより精密な上界は、この出口・G4 の消去には使わない。Mathlib `Topology/NoetherianSpace.lean` には Noether 空間の閉集合の WellFoundedLT がある。したがって Noether な周辺 S の閉部分スキーム Y→S について、その閉像に関する整礎帰納で同じ存在の出口を証明する経路を使う。各段で Y を被約化し、2d の細分で得る稠密開の閉補集合が閉像の真部分集合になる。帰納仮定が返す n に1を足すので、一般の Noether スキームに有限 Krull 次元を仮定する必要はない。これは有限型 F_p の場合を含む同じ出口の証明の組み立てで、最終の v 降下の主張を変更しない。存在の完成はまだ未証明。

- `ProperInductiveLevel.of_isPullback`：Cartesian な正方形でレベルを移送。実際の pullback との同型と baseChange の法則を使う。見込み10〜25行。
- `ProperInductiveLevel.comp_nilimmersion`：有限表示・全射閉埋め込み i:Y→Z と f:X→Y のレベルnから f≫i のレベルn。既に選んだ nilimmersion に i を合成する法則。見込み25〜60行。
- `ProperInductiveLevel.of_nilimmersion_baseChange`：上と任意の底変換、実際の細分からの消去を組み合わせ、f の i による底変換のレベルnから元の f のレベルnを得る。見込み10〜30行。
- 被約化の供給の分割：既存の `Y.nilradical.subscheme` に IsReduced を与え、その包含の全射性・Noether 基底上の局所有限表示性を示す。既存の nilradical・subschemeCover を使う（見込み50〜160行）。これは G3 の既承認の nilimmersion の零段と存在証明の分割で、TIC や新しい模型の存在を追加しない。


## G3：nilimmersion の合成・消去と実際の被約化

`ProperInductiveLevelTransport`（57行）：`ProperInductiveLevel.of_isPullback` は Cartesian な正方形による移送。`ProperInductiveLevel.comp_nilimmersion` は既に選んだ有限表示 nilimmersion の合成。`ProperInductiveLevel.of_nilimmersion_baseChange` は nilimmersion 上の実際の底変換に得たレベルを元の射へ戻す。

`SchemeNilradicalReduction`（49行）：`schemeNilradicalSubscheme_isReduced` は既存の nilradical の閉部分スキームの被約性。`schemeNilradicalSubscheme_surjective` はその包含の全射性。`schemeNilradicalSubscheme_locallyOfFinitePresentation` は Noether 基底上の局所有限表示性。アフィン被覆上の根基イデアルによる商と既存の被覆による貼り合わせを使い、新たな被約化のデータを仮定しない。

本体106行・入口2行。依存する被覆添字を実際のアフィン開の型に明示して単独検証、ソース完全一致、対象二本・直接 importer のビルド5,072ジョブ、小監査6宣言（3・3）・標準三公理のみ、終了状態0。追加公理・sorry・既存宣言の型変更・200行超の宣言なし。ログ `2g-proper-inductive-level-transport-check.log`・`2g-scheme-nilradical-reduction-check-3.log`・`2g-inductive-level-transport-reduction-native.log`・`2g-inductive-level-transport-reduction-audit.log`。鍵は検証中だけ使用。

2g-2 本体377行・入口込み383行、小監査26宣言・標準三公理のみ。G3〜G5 は未完。外枠16,000行、見込み約5,500〜12,000行は不変。

一覧：済み0／全体3（うち追加0）。

### Noether 基底上の存在の具体的な出口（着手前の型、G3 の内数）

`exists_properInductiveLevel_noetherian`：任意の Noether スキーム Y、固有・全射・局所有限表示 f:X→Y に対し ∃n, ProperInductiveLevel n f（見込み120〜300行、必要なら比較を分割）。閉集合の整礎帰納の命題は「閉像が C である任意の閉部分スキーム Y→S と、その上の任意の固有全射のレベルの存在」。被約化は同じ閉像を保ち、2d が供給する中心の閉像は C の真部分集合。中心上の帰納仮定を正段の証人へ入れ、最後に nilimmersion の消去で戻す。空な基底はレベル0。これは前節の同じ存在の証明の具体化であり、有限 Krull 次元という仮定や新しい存在の公理を追加しない。G3 の射影表示と G4〜G5 は別途残る。


## G3：Noether 基底上の有限の帰納的レベルの存在

`NoetherianProperInductiveLevel`（103行）：`exists_properInductiveLevel_noetherian` は任意の Noether 基底上の固有・全射・局所有限表示射に有限の帰納的レベルを供給する。閉部分スキームの閉像に関する整礎帰納で、空な基底、nilradical による被約化、2d の実際のブローアップ・proper fppf 細分、真に小さい閉中心への帰納を組み合わせる。Noether 基底に有限 Krull 次元は仮定せず、原典の次元による精密な上界は主張しない。

本体103行・入口1行。閉部分の準コンパクト性と支持を明示して単独検証、ソース完全一致、対象・直接 importer のビルド5,073ジョブ、小監査1宣言・標準三公理のみ、終了状態0。追加公理・sorry・既存宣言の型変更・200行超の宣言なし。ログ `2g-noetherian-proper-inductive-level-check-3.log`・`2g-noetherian-proper-inductive-level-native.log`・`2g-noetherian-proper-inductive-level-audit.log`。鍵は検証中だけ使用。

2g-2 本体480行・入口込み487行、小監査27宣言・標準三公理のみ。G3 の模型への移送と射影表示、G4〜G5 は未完。外枠16,000行、見込み約5,500〜12,000行は不変。

一覧：済み0／全体3（うち追加0）。

### 次の模型への移送（着手前の型、G3 の内数）

`exists_properInductiveLevel_affineBase`：任意の環 R、固有・全射・局所有限表示 f:X→Spec R に対し ∃n, ProperInductiveLevel n f（見込み35〜80行）。G2 の `exists_proper_surjective_finitePresentation_coefficient_model` に係数環 ℤ を取り、実際の有限生成係数模型を供給する。有限型 ℤ の係数環の Noether 性から上の存在を適用し、元の対象との Cartesian 正方形と `of_isPullback` で移す。元の R の Noether 性、模型の存在を追加仮定にしない。非アフィンな任意の qcqs 基底まで完成と呼ばない。

G4 の射影版への注意：`ProperInductiveLevel` は原典 Definition 2.5 と同じ一般の固有な modification を許すため、この命題だけから全ての一般の固有射の四角形の完全性を引き出してはならない。射影版だけを使う G4 は、上の整礎帰納と同じ各段で 2d が実際に供給するブローアップを保持して使う。G3 の残りの射影表示はその実際のブローアップと有限ファイバー冪を 2f の入力へ渡す部分。既存の帰納的レベルの定義を射影的な射に狭めない。


## G3：任意の affine 基底への実際の模型による移送

`AffineBaseProperInductiveLevel`（32行）：`exists_properInductiveLevel_affineBase` は任意の環 R 上の固有・全射・局所有限表示 f:X→Spec R に有限の帰納的レベルを返す。G2 の一般の固有全射の実際の係数模型を ℤ 上で構成し、その Noether な模型のレベルを Cartesian 正方形で戻す。元の R の Noether 性・模型の存在・係数射の忠実平坦性を仮定しない。BS17 Lemma 2.6 の affine 基底の場合であり、非アフィンな任意の qcqs 基底への模型まで完成と呼ばない。

本体32行・入口1行。最初の単独検証、ソース完全一致、対象・直接 importer のビルド5,074ジョブ、小監査1宣言・標準三公理のみ、終了状態0。追加公理・sorry・既存宣言の型変更・200行超の宣言なし。ログ `2g-affine-base-proper-inductive-level-check.log`・`2g-affine-base-proper-inductive-level-native.log`・`2g-affine-base-proper-inductive-level-audit.log`。鍵は検証中だけ使用。

2g-2 本体512行・入口込み520行、小監査28宣言・標準三公理のみ。G3 の射影表示と G4〜G5 は未完。外枠16,000行、見込み約5,500〜12,000行は不変。

一覧：済み0／全体3（うち追加0）。

## G3 の射影表示の最初の束（着手前の型）

- `reesDegreeOneLinearMap I`：中心イデアル I から Rees 代数への次数一の R-線形写像。既存の reesDegreeOne を線形射として扱う法則。
- `exists_rees_finite_degreeOne_generators I hI`：有限生成イデアル I に対し、ある n と a:Fin n→I が存在し、reesDegreeOne I ∘a が Rees 代数を R 上生成する。有限生成加群の有限族と、既存の rees_adjoin_degreeOne を使う。
- `exists_rees_degreeOne_polynomial_surjective I hI`：同じ n,a による MvPolynomial (Fin n) R→ₐ[R] reesAlgebra I の評価が全射。元の生成元は次数一で、有限な添字は Type 0 に置く。これを次数付きの作用・有限加群性・irrelevant ideal の標準開条件へ渡す。最初の三項の見込み100〜240行。G3 の既承認の Rees の射影表示の分割で、全体の外枠は変えない。


## G3：Rees 代数の有限な次数一表示

`ReesFiniteDegreeOnePresentation`（67行）：`reesDegreeOneLinearMap`・その apply の式は既存の次数一元の線形性。`exists_rees_finite_degreeOne_generators` は有限生成中心から Fin n を添字とする次数一の代数生成族を供給。`exists_rees_degreeOne_polynomial_surjective` は同じ族の MvPolynomial の実際の評価の全射性。Noether 性は不要で、空の生成族・零環を除外しない。

本体67行・入口1行。最初の単独検証、ソース完全一致、対象・直接 importer のビルド5,075ジョブ、小監査7宣言・標準三公理のみ、終了状態0。追加公理・sorry・既存宣言の型変更・200行超の宣言なし。ログ `2g-rees-finite-degree-one-presentation-check.log`・`2g-rees-finite-degree-one-presentation-native.log`・`2g-rees-finite-degree-one-presentation-audit.log`。鍵は検証中だけ使用。

2g-2 本体579行・入口込み588行、小監査35宣言・標準三公理のみ。G3 の次数付きの作用・標準開条件・有限ファイバー冪と G4〜G5 は未完。外枠16,000行、見込み約5,500〜12,000行は不変。

一覧：済み0／全体3（うち追加0）。

### 次数付きの多項式作用への係数移送（着手前の型、G3 の内数）

`reesDegreeOnePolynomialAlgebra I a` は有限な次数一族 a による実際の評価からの MvPolynomial 代数構造。`reesDegreeOnePolynomial_scalarTower` は R との塔、`reesDegreeOnePolynomial_finite` は評価が全射ならその多項式環上有限な加群であること。`reesDegreeOne_aeval_mem` は次数 d の斉次多項式の評価が reesGrade I d に入ること。`reesDegreeOnePolynomial_gradedSMul` はこの評価による SetLike.GradedSMul としての作用。単項式の次数と既存の graded な有限積の法則を使う。見込み100〜220行。これは 2f の射影入力へ実際の係数構造を合わせる法則で、新たな有限性の仮定を最終の主張に追加しない。


## G3：実際の次数付き多項式作用と有限加群性

`ReesDegreeOnePolynomialAction`（69行）：`reesDegreeOnePolynomialAlgebra` は選んだ次数一族による評価の代数構造。`reesDegreeOnePolynomial_scalarTower` は R との塔、`reesDegreeOnePolynomial_finite` は全射評価からの有限加群性。`reesDegreeOne_aeval_mem` は各斉次次数の保存、`reesDegreeOnePolynomial_gradedSMul` はその作用の次数付き性。生成族に依存する代数構造は型の letI で明示し、推論できない生成族を大域的な instance にしない。

本体69行・入口1行。評価の代数構造と次数の自然数の式を明示して単独検証、ソース完全一致、対象・直接 importer のビルド5,076ジョブ、小監査7宣言・標準三公理のみ、終了状態0。追加公理・sorry・既存宣言の型変更・200行超の宣言なし。ログ `2g-rees-degree-one-polynomial-action-check-2.log`・`2g-rees-degree-one-polynomial-action-native.log`・`2g-rees-degree-one-polynomial-action-audit.log`。鍵は検証中だけ使用。

2g-2 本体648行・入口込み658行、小監査42宣言・標準三公理のみ。G3 の標準開条件・有限ファイバー冪と G4〜G5 は未完。外枠16,000行、見込み約5,500〜12,000行は不変。

一覧：済み0／全体3（うち追加0）。

### 標準開条件への接続（着手前の型、G3 の内数）

`reesDegreeOneGradedHom I a` は実際の評価を GradedRingHom に束ねる。`exists_reesDegreeOne_homogeneous_lift` は評価が全射なら、各斉次元に同じ次数の多項式の原像を供給する（既存の decompose と graded map の可換性）。`reesDegreeOne_irrelevant_le_span` は irrelevant ideal が選んだ次数一元のイデアルで生成される条件を返す。`iSup_reesDegreeOne_basicOpen` はその標準開の被覆。見込み70〜160行。次数成分の比較と既存の Ideal.span_pow_eq_map_homogeneousSubmodule、Proj の基本開の被覆を使う。2f の入力の法則への接続で、被覆性を追加仮定にしない。


## G3：斉次原像・irrelevant ideal・標準開の被覆

`ReesDegreeOneStandardOpen`（65行）：`reesDegreeOneGradedHom` は実際の評価の graded な環準同型。`exists_reesDegreeOne_homogeneous_lift` は全射評価の各斉次元への同次数の原像。`reesDegreeOne_irrelevant_le_span` は選んだ次数一元が irrelevant ideal を生成する条件。`iSup_reesDegreeOne_basicOpen` はその標準開が実際の Rees Proj を被覆すること。斉次次数の比較は既存の graded map と decompose の可換性を使用。

本体65行・入口1行。Mathlib が局所登録を要求する MvPolynomial.gradedAlgebra を明示して単独検証。最初の欠けた instance に由来する elaboration timeout は上限を上げずこの登録で解消。ソース完全一致、対象・直接 importer のビルド5,077ジョブ、小監査5宣言・標準三公理のみ、終了状態0。追加公理・sorry・既存宣言の型変更・200行超の宣言なし。ログ `2g-rees-degree-one-standard-open-check-2.log`・`2g-rees-degree-one-standard-open-native.log`・`2g-rees-degree-one-standard-open-audit.log`。鍵は検証中だけ使用。

2g-2 本体713行・入口込み724行、小監査47宣言・標準三公理のみ。G3 の有限ファイバー冪・構造射の比較と G4〜G5 は未完。外枠16,000行、見込み約5,500〜12,000行は不変。

一覧：済み0／全体3（うち追加0）。

### 2f の入力の同時供給（着手前の型、G3 の内数）

`exists_rees_projective_cech_data I hI`：有限生成中心から n,a:Fin n→I と実際の評価の多項式代数構造を選び、IsScalarTower・GradedSMul・多項式環上の Module.Finite・その algebraMap の変数の像による irrelevant ideal の条件を同じ証人で返す（見込み30〜70行）。前の三モジュールの実際の構成を組み合わせるだけで、射影 Čech の仮定を追加しない。続いて schemeScalarMorphism と affineBlowupπ の一致、有限ファイバー冪の射影表示を照合する。


## G3：2f の射影 Čech 入力の同時供給

`ReesProjectiveCechInput`（37行）：`exists_rees_projective_cech_data` は有限生成中心から Fin n を添字とする次数一族と、その実際の評価による多項式代数構造・IsScalarTower・GradedSMul・Module.Finite・algebraMap の変数の像による irrelevant ideal の条件を同じ証人で返す。Noether 性と標準開の条件は追加仮定にしない。2f が使う Fin n の有限性・線形順序は既存の instance をそのまま利用できる。

本体37行・入口1行。最初の単独検証、ソース完全一致、対象・直接 importer のビルド5,078ジョブ、小監査1宣言・標準三公理のみ、終了状態0。追加公理・sorry・既存宣言の型変更・200行超の宣言なし。ログ `2g-rees-projective-cech-input-check.log`・`2g-rees-projective-cech-input-native.log`・`2g-rees-projective-cech-input-audit.log`。鍵は検証中だけ使用。

2g-2 本体750行・入口込み762行、小監査48宣言・標準三公理のみ。e33532643 の後は10モジュール632行＋入口10行、小監査38宣言。今回の区切りでは、全レベルの任意の底変換、nilimmersion の消去、Noether 基底・任意の affine 基底上のレベルの存在、Rees の実際の有限な次数一表示と 2f の係数条件まで到達した。G3 の構造射・有限ファイバー冪と G4〜G5 は未完。外枠16,000行、全体の見込み約5,500〜12,000行は不変。数学的な境界、型や最終の範囲の変更はない。停止点2g-2ではない。

一覧：済み0／全体3（うち追加0）。

### 次の構造射の比較（着手前の型、G3 の内数）

- `schemeScalarMorphism_projectiveScalar`：一般の次数付き R-代数 G で、schemeScalarMorphism (Proj G) (projectiveScalarToGlobalSections G) は Proj.toSpecZero G と Spec.map (projectiveScalarToZero G) の合成に等しい（見込み40〜120行）。既存の Γ–Spec 随伴・Proj の構造射・分母1の大域スカラーの自然性を照合する法則。
- Rees への特殊化：同じ schemeScalarMorphism が実際の affineBlowupπ I と等しい（見込み10〜30行）。reesZeroEquiv の逆と projectiveScalarToZero (reesGrade I) が同じ環準同型であることを使う。

この比較の後、2d の affine 局所模型と 2f の実際の四角形を合わせ、有限ファイバー冪の Segre 表示へ進む。一般の固有射の四角形の完全性を追加仮定にしない。

構造射の比較の証明分割：一般の Proj の比較と Rees の零次成分の式を先に検証し、Rees の構造射への特殊化を別モジュールへ分ける。必要なら `reesProjectiveScalarSections I : R→+*Γ(affineBlowup I,⊤)` を同じ大域スカラーの係数移送の略記として作る（見込み10〜30行、前記の内数）。同じ構造層の型を明示して照合し、既定の elaboration/kernel 上限を維持する。


## G3：一般の Proj のスカラーと実際の構造射

`ProjectiveScalarStructureMorphism`（45行）：`schemeScalarMorphism_projectiveScalar` は射影 Čech 側の大域スカラーの射と Proj.toSpecZero・projectiveScalarToZero の合成の一致。分母1の基本開・等しい開集合間の射と Γ–Spec の自然性を照合する。`rees_projectiveScalarToZero` は Rees の零次スカラーと reesZeroEquiv の逆の一致。零次成分が大域切断全体であるとは仮定しない。

本体45行・入口1行。環の射の包装・開集合の等式の射を明示して単独検証、ソース完全一致、対象・直接 importer のビルド5,079ジョブ、小監査2宣言・標準三公理のみ、終了状態0。Rees への特殊化は未検証の下書きのまま分割し、既定の上限を維持。追加公理・sorry・既存宣言の型変更・200行超の宣言なし。ログ `2g-projective-scalar-structure-morphism-check-3.log`・`2g-projective-scalar-structure-morphism-native.log`・`2g-projective-scalar-structure-morphism-audit.log`。鍵は検証中だけ使用。

2g-2 本体795行・入口込み808行、小監査50宣言・標準三公理のみ。G3 の Rees への構造射の特殊化・有限ファイバー冪と G4〜G5 は未完。外枠16,000行、全体の見込み約5,500〜12,000行は不変。

一覧：済み0／全体3（うち追加0）。


構造射の照合の追加の法則の分割（着手前の型、前記の内数）：`projectiveCechStructureMap G : Proj G→Spec R` は schemeScalarMorphism (Proj G) (projectiveScalarToGlobalSections G) という同じ合成を一般の G で名前付けする（見込み15〜35行）。Rees に特殊化する際、構造層の環の同一性を巨大な具体的な型で再推論せず、この一般の合成と証明をそのまま特殊化する。`projectiveCechStructureMap_eq` は前の一般の比較の適用。Rees の射との等式の内容を変えず、上限は上げない。


## G3：Rees の実際の構造射への特殊化

`ReesScalarStructureMorphism`（39行）：`projectiveCechStructureMap` は schemeScalarMorphism と projectiveScalarToGlobalSections の同じ合成を一般の G の下で名前付けしたもの。`projectiveCechStructureMap_eq` は前の一般の比較。`schemeScalarMorphism_rees` はこの定義上同じ射と affineBlowupπ の一致。

本体39行・入口1行。具体的な構造層の型の再推論で出た elaboration timeout は、一般の合成と証明をそのまま特殊化する分割で解消。局所的な次数分解の固定だけの案は未検証下書きで置き換えた。単独検証、ソース完全一致、対象・直接 importer のビルド5,080ジョブ、小監査5宣言・標準三公理のみ、終了状態0。上限の引き上げ・追加公理・sorry・既存宣言の型変更・200行超の宣言なし。ログ `2g-rees-scalar-structure-morphism-check-3.log`・`2g-rees-scalar-structure-morphism-native.log`・`2g-rees-scalar-structure-morphism-audit.log`。鍵は検証中だけ使用。

2g-2 本体834行・入口込み848行、小監査55宣言・標準三公理のみ。今回の区切りは2モジュール84行＋入口2行、小監査7宣言。G3 の有限ファイバー冪と G4〜G5 は未完。外枠16,000行、全体の見込み約5,500〜12,000行は不変。

一覧：済み0／全体3（うち追加0）。

## G3：有限ファイバー冪の Segre 表示の分割（着手前の型）

[Stacks 01WD（Segre embedding）](https://stacks.math.columbia.edu/tag/01WD) の座標積と標準開の組を照合した。以下は、その座標の計算を一般の有限な次数一表示の商へ組み立てる本実装の分割で、同 Tag が一般の次数付き商の場合の以下の全 API を直接供給しているという意味ではない。一般の射影的射のカテゴリー全体や線束の普遍性は新設しない。

- S01（見込み120〜300行）：`segreCoordinateMap a b : MvPolynomial (ι×κ) R→ₐ[R] B⊗[R]A`。変数 (i,j) は b j⊗a i。左因子 A の次数を B に底変換した grading の下で graded な射に束ねる。Mathlib GradedAlgebra.TensorProduct の baseChange は平坦性不要。まず一般の次数一評価の次数保存と、この座標写像の係数・変数の式を供給する。
- S02（150〜450行）：座標写像の核の斉次性、実際の商 S=R[Z]/ker とその次数分解・多項式環上の有限加群性・irrelevant ideal の条件。同じ多項式環の商なので次数一の有限表示を保持する。既存の HilbertSerre.isInternal_quotientGrade を使い、一般の二重次数付き環の理論を追加しない。
- S03（600〜1,400行）：各対 (i,j) について S_(Zij) の次数零の環と A_(ai)⊗[R]B_(bj) の同型、および重なりの局所化への自然性。分子分母を同じ次数へそろえる計算を使い、非零な分母・非自明な局所化を仮定しない。
- S04（500〜1,200行）：この標準開の組による Proj S と Proj A×_{Spec R}Proj B の実際の同型、構造射と二射影の式。既存のアフィン pullback の tensor 比較と開被覆の貼り合わせを使う。
- 有限冪への適用（150〜350行）：S01〜S04 を反復し、正の有限ファイバー冪に同じ有限な次数一表示と基底上の同型を供給する。増大次数の基底そのものは別扱いで、不要な Proj 表示を要求しない。中心への底変換と構造射の式を保持する。

これらは既承認の G3 の Rees・Segre・有限ファイバー冪の射影表示の分割。残りのこの部分は約1,520〜3,700行、G3〜G5 の全体は約5,500〜12,000行・外枠16,000行を維持する。一般の固有射のコホモロジー有限性・Stein 分解を追加せず、2f の射影 Čech 版に実際の入力を供給する。


S01 の最初の実装の型（着手前、上記の内数）：`degreeOne_aeval_mem_grade D hR x hx f hf` は D:ℕ→Submodule S C、D の graded monoid 構造、R→C の係数が D0 に入ること、x_i∈D1、f の次数dの斉次性から、実際の評価が Dd に入ること。R と S の係数は同一と仮定せず、定数の積と graded な有限積で証明する（見込み40〜80行）。`degreeOneGradedEvaluation` はこれを GradedRingHom に束ねる。`segreCoordinateMap a b` と C・X の式は B⊗[R]A の実際の座標評価（見込み30〜60行）。いずれも S01 の座標・次数保存の最初の分割で、S02 の模型の存在・Proj の比較を仮定にしない。


## G3・S01：次数一評価の一般の次数保存と実際の Segre 座標

`DegreeOneGradedEvaluation`（44行）：`degreeOne_aeval_mem_grade` は係数が次数零、変数が次数一なら実際の評価が斉次次数を保つ法則。係数環 R と部分加群の係数環 S を分け、graded な積を使う。`degreeOneGradedEvaluation` は同じ評価を GradedRingHom に束ねる。

`SegreCoordinates`（33行）：`segreCoordinateMap` は変数 (i,j) を b_j⊗a_i に送る実際の多項式評価。`segreCoordinateMap_X`・`segreCoordinateMap_C` は変数と係数の式。零環・空の添字を許し、平坦性を仮定しない。

本体77行・入口2行。次数零と次数一の仮定を宣言に明示して単独検証、ソース完全一致、対象二本・直接 importer のビルド5,082ジョブ、小監査6宣言（2・4）・標準三公理のみ、終了状態0。追加公理・sorry・既存宣言の型変更・200行超の宣言なし。ログ `2g-degree-one-graded-evaluation-check-2.log`・`2g-segre-coordinates-check.log`・`2g-degree-one-evaluation-segre-coordinates-native.log`・`2g-degree-one-evaluation-segre-coordinates-audit.log`。鍵は検証中だけ使用。

2g-2 本体911行・入口込み927行、小監査61宣言・標準三公理のみ。S01 の底変換 grading への適用、S02〜S04、G4〜G5 は未完。外枠16,000行、見込み約5,500〜12,000行は不変。

一覧：済み0／全体3（うち追加0）。

### S01 の底変換 grading と S02 の核の法則（着手前の型、前記の内数）

`segreLeftTensorGrade G n := (G n).baseChange B` に Mathlib の GradedAlgebra.baseChange を供給する。`segreLeftTensorGrade_algebraMap_zero` は R の係数がその次数零に入ること。`segreGradedCoordinateMap G a b ha` は a_i∈G1 なら実際の segreCoordinateMap をこの grading への GradedRingHom に束ねる（b の次数はこの左 grading には不要）。`segreCoordinateMap_kernel_homogeneous` は同じ写像の核の斉次性。既存の homogeneous ideal の comap を使い、次数分解と写像の可換性を再証明しない。見込み70〜150行。添字の DecidableEq は標準の grading のために明示し、最終の有限添字 Fin n では既存のものを使う。


## G3・S01：底変換 grading と Segre 座標の核の斉次性

`SegreGradedCoordinates`（59行）：`segreLeftTensorGrade` とその GradedRing は Mathlib の任意の底変換の grading。`segreLeftTensorGrade_algebraMap_zero` は元の係数の次数零。`segreGradedCoordinateMap` は実際の座標評価の graded な射、`segreGradedCoordinateMap_toRingHom` は元の環写像との一致。`segreCoordinateMap_kernel_homogeneous` は homogeneous ideal の comap を使う核の斉次性。平坦性・右の座標の次数は不要。添字の DecidableEq も Mathlib のこの grading には不要であることを検証し、仮定から除いた。

本体59行・入口1行。単独検証、ソース完全一致、対象・直接 importer のビルド5,086ジョブ、小監査15宣言・標準三公理のみ、終了状態0。追加公理・sorry・既存宣言の型変更・200行超の宣言なし。ログ `2g-segre-graded-coordinates-check-2.log`・`2g-segre-graded-coordinates-native.log`・`2g-segre-graded-coordinates-audit.log`。鍵は検証中だけ使用。

S01 は3モジュール136行＋入口3行、小監査21宣言・標準三公理のみで完了し、S02 の核の斉次性まで供給した。2g-2 本体970行・入口込み987行、小監査76宣言・標準三公理のみ。G3 の商の次数分解・標準開の比較・有限冪と G4〜G5 は未完。今回 834e6b8d5 の後は5モジュール220行＋入口5行、小監査28宣言。全体の見込み約5,500〜12,000行、外枠16,000行は不変。停止点2g-2ではない。

一覧：済み0／全体3（うち追加0）。

### S02 の実際の商の次数分解の法則（着手前の型、S02 の内数）

`homogeneousIdealQuotientGrade_isInternal J G hJ`：同次イデアル J と GradedRing G から、既存の projectiveRingQuotientGrade J G の内部直和を返す。`homogeneousIdealQuotientGradedRing J G hJ` はその同じ商の GradedRing。既存の HilbertSerre.isInternal_quotientGrade と Submodule.Quotient.restrictScalarsEquiv を使い、既存の ReesClosedRingGrading の証明の一般の法則への分割として実装する（見込み40〜90行）。これを実際の Segre 座標写像の核へ適用する。既存の Rees の宣言の型は変更しない。


## G3・S02：同次イデアルの実際の商の次数分解

`HomogeneousIdealQuotientGrading`（51行）：`homogeneousIdealQuotientGrade_isInternal` は同次イデアルの実際の環の商で、既存の projectiveRingQuotientGrade が内部直和であること。`homogeneousIdealQuotientGradedRing` は同じ商の積と分解を合わせる。HilbertSerre の商加群の分解と係数制限の商の同型を再利用し、既存の Rees の宣言は変更しない。

本体51行・入口1行。最初の単独検証、ソース完全一致、対象・直接 importer のビルド5,087ジョブ、小監査6宣言・標準三公理のみ、終了状態0。追加公理・sorry・既存宣言の型変更・200行超の宣言なし。ログ `2g-homogeneous-ideal-quotient-grading-check.log`・`2g-homogeneous-ideal-quotient-grading-native.log`・`2g-homogeneous-ideal-quotient-grading-audit.log`。鍵は検証中だけ使用。

2g-2 本体1,021行・入口込み1,039行、小監査82宣言・標準三公理のみ。S02 の実際の座標環への適用、S03〜S04、G4〜G5 は未完。外枠16,000行、見込み約5,500〜12,000行は不変。

一覧：済み0／全体3（うち追加0）。

### S02 の実際の Segre 座標環（着手前の型、S02 の内数）

`SegreCoordinateRing a b := MvPolynomial (ι×κ) R / ker(segreCoordinateMap a b)`、`segreCoordinateGrade a b` はその実際の商の次数成分。`segreCoordinateGradedRing G a b ha` は証明した核の斉次性からの次数分解。`segreCoordinateProjection` は実際の商写像。多項式環上の有限加群性、Noether な R と有限添字のときの座標環の Noether 性、商の多項式作用の GradedSMul、射影の次数保存を供給する（見込み80〜170行）。変数は Type 0 の有限添字に置き、2f の入力を保持する。Proj の積との同型と標準開の比較をこの環の定義だけで完成扱いにしない。


## G3・S02：実際の Segre 座標環とその次数分解・有限性

`SegreCoordinateRing`（68行）：`SegreCoordinateRing` は実際の座標写像の核による多項式環の商。`segreCoordinateGrade` はその既存の商の次数成分。`segreCoordinateProjection`・`segreCoordinateProjection_surjective` は実際の商写像と全射性。`segreCoordinateRing_finite` は同じ多項式環上の有限加群性。`segreCoordinateRing_noetherian` は Noether 基底と有限添字からの Noether 性。`segreCoordinateProjection_preservesPiece` は射影の次数保存、`segreCoordinateGradedSMul` は既存の商の次数付き作用、`segreCoordinateGradedRing` は証明した核の斉次性からの実際の次数分解。最後の構成の引数順は a,b,G,ha。

本体68行・入口1行。係数環を明示し、有限変数多項式環と商の Noether 性の専用 import を供給して単独検証、ソース完全一致、対象・直接 importer のビルド5,088ジョブ、小監査12宣言・標準三公理のみ、終了状態0。追加公理・sorry・既存宣言の型変更・200行超の宣言なし。ログ `2g-segre-coordinate-ring-check-4.log`・`2g-segre-coordinate-ring-native.log`・`2g-segre-coordinate-ring-audit.log`。鍵は検証中だけ使用。

2g-2 本体1,089行・入口込み1,108行、小監査94宣言・標準三公理のみ。834e6b8d5 の後は7モジュール339行＋入口7行、小監査46宣言。S01 完了、S02 は実際の商の次数分解まで到達したが、標準開条件と 2f の入力の同時供給は残る。S03〜S04 と有限冪、G4〜G5 も未完。全体の見込み約5,500〜12,000行、外枠16,000行は不変。root・下流全ビルド・全体監査は実行していない。停止点2g-2ではない。

一覧：済み0／全体3（うち追加0）。

### S02 の標準開条件の残り（着手前の型、S02 の内数）

`segreCoordinate_irrelevant_le_span a b G ha`：上の同じ GradedRing を局所供給した下で、irrelevant ideal は商写像の変数の像で生成される。商の次数成分の定義から同次数の原像を取り、既存の Ideal.span_pow_eq_map_homogeneousSubmodule の法則に渡す（見込み30〜70行）。`iSup_segreCoordinate_basicOpen` はこの有限な標準開の被覆。次いで 2f に必要な多項式作用・有限性・標準開条件を同じ商と次数分解で束ねる（20〜50行）。

S03 の二因子には、実際の次数一評価が全射な表示を使う。最初の Rees と、以後のこの多項式環の商は、いずれもその全射表示を既に持つ。単に多項式環上有限な加群であるという条件だけから、A0=R や全射評価を仮定してはならない。標準開の同型はこの実際の商と全射表示に沿って構成する。

S02 の同じ商写像の法則の追加の分割（着手前、前記の内数）：`segreCoordinate_aeval` は商写像が変数の像による実際の評価と等しいこと。`segreCoordinate_projective_cech_data` は同じ次数分解の下で IsScalarTower・GradedSMul・Module.Finite と algebraMap の変数の像による irrelevant ideal の条件を同時に返す。標準開の存在を仮定にせず、前記の商と全射性から導く。


## G3・S02：Segre 座標環の標準開被覆と Čech 入力

`SegreCoordinateStandardOpen`（73行）：`segreCoordinate_aeval` は商写像と変数の像による評価の一致。`segreCoordinate_irrelevant_le_span` は実際の同次数の原像から irrelevant ideal の生成条件を導く。`iSup_segreCoordinate_basicOpen` はその標準開の被覆、`segreCoordinate_projective_cech_data` は同じ商の作用・有限性・標準開条件の同時供給。

単独検証は初回成功、ソース完全一致。対象と直接 importer のビルド5,089ジョブ、小監査4宣言・標準三公理のみ、終了状態0。ログ `2g-segre-coordinate-standard-open-check.log`・`2g-segre-coordinate-standard-open-native.log`・`2g-segre-coordinate-standard-open-audit.log`。追加公理・sorry・既存宣言の型変更・200行超の宣言なし。鍵は検証中だけ使用。

S02 完了。2g-2 本体1,162行・入口込み1,182行、小監査98宣言・標準三公理のみ。S03〜S04・有限冪、G4〜G5 は未完。見込み約5,500〜12,000行・外枠16,000行は不変。停止点2g-2ではない。

一覧：済み0／全体3（うち追加0）。

### S03 の脱斉次化の法則への分割（着手前の型、S03 の内数）

次数一の f∈G1 に対し、次数 n の x を x/f^n に送る加法写像 `G n →+ HomogeneousLocalization.Away G f` を作り、直和の普遍性で `A →+* HomogeneousLocalization.Away G f` に束ねる。次数一の f は 1 に移る。続いて、この正規化と局所化の普遍性から `A / Ideal.span {f-1} ≃+* HomogeneousLocalization.Away G f`、係数環に関する整合性を供給する（最初の正規化40〜100行、商との比較100〜250行）。これは標準開比較の分割で、新たな最終仮定や平坦性は加えない。零環・零の分母も許す。Mathlib の斉次局所化・DirectSum の環の普遍性を再利用する。


## G3・S03：次数一の分母への脱斉次化

`HomogeneousDegreeOneNormalization`（60行）：`homogeneousDegreeOneNormalizePiece` は次数 n の x を x/f^n に送る加法写像。`homogeneousDegreeOneNormalize` は DirectSum の普遍性で束ねた実際の環写像。`homogeneousDegreeOneNormalize_of_mem` は斉次元の評価式、`homogeneousDegreeOneNormalize_self` は f が 1 に移る式。次数一生成・非零な分母・平坦性を仮定しない。係数環と加群の宇宙を分けたまま実装。

単独検証、ソース完全一致、対象と直接 importer のビルド5,090ジョブ、小監査14宣言・標準三公理のみ、終了状態0。ログ `2g-degree-one-normalization-check-3.log`・`2g-degree-one-normalization-native.log`・`2g-degree-one-normalization-audit.log`。追加公理・sorry・既存宣言の型変更・200行超の宣言なし。鍵は検証中だけ使用。

2g-2 本体1,222行・入口込み1,243行、小監査112宣言・標準三公理のみ。S03 の商との同型・Segre の二因子のチャート比較、S04 と有限冪、G4〜G5 は残る。全体の見込み約5,500〜12,000行、外枠16,000行は不変。停止点2g-2ではない。

一覧：済み0／全体3（うち追加0）。


S03 の商との比較の分割（着手前、前記100〜250行の内数）：`homogeneousDegreeOneSpecialize G hf φ hφ : Away G f →+* C` は環写像 φ:A→+*C と hφ:φ f=1 から局所化の普遍性で作る。斉次分数における式と `specialize (normalize x)=φ x` を示し、商写像を φ に使う。これは前記の脱斉次化の逆写像の法則の分割。


## G3・S03：斉次局所化の特殊化と正規化との合成

`HomogeneousDegreeOneSpecialization`（64行）：`homogeneousDegreeOneSpecialize` は φ(f)=1 の下で実際の局所化の普遍性を制限した環写像。`homogeneousDegreeOneSpecialize_mk` は斉次分数の評価式。`homogeneousDegreeOneSpecialize_normalize` は正規化との合成が φ に等しいこと、`homogeneousDegreeOneSpecialize_normalize_self` は正規化自身に特殊化したときの恒等性。係数と二つの環の宇宙を分離。

単独検証、ソース完全一致、対象と直接 importer のビルド5,091ジョブ、小監査10宣言・標準三公理のみ、終了状態0。ログ `2g-degree-one-specialization-check-3.log`・`2g-degree-one-specialization-native.log`・`2g-degree-one-specialization-audit.log`。追加公理・sorry・既存宣言の型変更・200行超の宣言なし。鍵は検証中だけ使用。

2g-2 本体1,286行・入口込み1,308行、小監査122宣言・標準三公理のみ。商との同型・Segre チャート比較以降は未完。見込み約5,500〜12,000行・外枠16,000行は不変。停止点2g-2ではない。

一覧：済み0／全体3（うち追加0）。


## G3・S03：脱斉次化の商と斉次局所化の実際の同型

`HomogeneousDegreeOneQuotient`（66行）：`homogeneousDegreeOneQuotientToAway` は正規化を A/(f−1) へ降ろした写像、`homogeneousDegreeOneQuotient_denominator` は商で f=1 となる式、`homogeneousDegreeOneAwayToQuotient` は商写像による特殊化。`homogeneousDegreeOneQuotientEquiv` はこれらの実際の環同型、`homogeneousDegreeOneQuotientEquiv_mk` は商の元上の式。次数一生成・平坦性・分母の非零性は不要。

単独検証、ソース完全一致、対象と直接 importer のビルド5,092ジョブ、小監査13宣言・標準三公理のみ、終了状態0。ログ `2g-degree-one-quotient-check-2.log`・`2g-degree-one-quotient-native.log`・`2g-degree-one-quotient-audit.log`。追加公理・sorry・既存宣言の型変更・200行超の宣言なし。鍵は検証中だけ使用。

2g-2 本体1,352行・入口込み1,375行、小監査135宣言・標準三公理のみ。S03 は商との環同型まで到達。係数環との整合性・Segre の二因子の比較・重なりの自然性、S04・有限冪、G4〜G5 は未完。見込み約5,500〜12,000行・外枠16,000行は不変。停止点2g-2ではない。

一覧：済み0／全体3（うち追加0）。

S03 の係数の法則の分割（着手前、S03 の内数、40〜90行）：既存の `projectiveHomogeneousAwayAlgebra G f` の下で正規化が R の係数を保つことを示し、同じ環同型を `A/(f−1) ≃ₐ[R] Away G f` に束ねる。既存の代数構造を置き換えず、係数環の一般化や最終の型の変更はしない。


## G3・S03：脱斉次化の同型の係数環との整合性

`HomogeneousDegreeOneQuotientAlgebra`（51行）：`homogeneousDegreeOneNormalize_algebraMap` は既存の projectiveHomogeneousAwayAlgebra の下で正規化が係数を保つこと。`homogeneousDegreeOneQuotientAlgEquiv` は同じ環同型を R 上の代数同型に束ねる。`homogeneousDegreeOneQuotientAlgEquiv_toRingEquiv` は忘却した環同型が元の同型であること。既存の代数構造を保持し、係数環と代数を同じ宇宙に置いた既存 API の実際の用途に接続した。前二モジュールの宇宙を分けた一般の環の法則はそのまま残る。

単独検証、ソース完全一致、対象と直接 importer のビルド5,093ジョブ、小監査9宣言・標準三公理のみ、終了状態0。ログ `2g-degree-one-quotient-algebra-check-5.log`・`2g-degree-one-quotient-algebra-native.log`・`2g-degree-one-quotient-algebra-audit.log`。追加公理・sorry・既存宣言の型変更・200行超の宣言なし。鍵は検証中だけ使用（--class impl --wait 3600、待ちは一つ）。root・下流全ビルド・全体監査は実行していない。

2g-2 本体1,403行・入口込み1,427行、小監査144宣言・標準三公理のみ。0476c334e の後の今回の束は5モジュール314行＋入口5行、小監査50宣言。S01〜S02 完了、S03 は次数一の標準開を脱斉次化の商と同じ基底上で比較するところまで到達した。残りは Segre の二因子のチャート比較と重なりの自然性、S04 の貼り合わせと有限冪、G4・G5 の主要三部分。全体の見込み約5,500〜12,000行・外枠16,000行は不変。停止点2g-2ではない。

一覧：済み0／全体3（うち追加0）。


### S03：正規化した二因子への写像の分割（着手前の型）

`homogeneousDegreeOneNormalizeAlgHom` と `homogeneousDegreeOneSpecializeAlgHom` は証明した係数の法則と合成の式により、同じ環写像を R 上の代数写像に束ねる（30〜70行）。二因子の正規化のテンソル積は環全体に定義されるので、その写像と実際の Segre 座標写像の合成は、座標写像の核を自動的に消す。これを商へ降ろした写像 `SegreCoordinateRing a b →ₐ[R] Away H (b j) ⊗[R] Away G (a i)` を作る。選んだ座標 Zij の像は 1 となり、特殊化により対応する Segre 標準開からの代数写像を得る（70〜140行）。逆向きの写像と重なりの自然性はこの後に証明し、この片方向だけでチャート比較の完成とはしない。すべて S03 の内数で、平坦性は不要。


## G3・S03：正規化と特殊化の同じ代数写像

`HomogeneousDegreeOneAlgebraMaps`（47行）：`homogeneousDegreeOneNormalizeAlgHom` と `homogeneousDegreeOneSpecializeAlgHom` は既存の代数構造上で同じ正規化・特殊化を束ねる。二つの `toRingHom` の式は元の環写像との一致。

単独検証、ソース完全一致、対象と直接 importer のビルド5,094ジョブ、小監査8宣言・標準三公理のみ、終了状態0。ログ `2g-degree-one-algebra-maps-check-2.log`・`2g-degree-one-algebra-maps-native.log`・`2g-degree-one-algebra-maps-audit.log`。追加公理・sorry・既存宣言の型変更・200行超の宣言なし。鍵は検証中だけ使用。

2g-2 本体1,450行・入口込み1,475行、小監査152宣言・標準三公理のみ。S03〜S04 と有限冪、G4〜G5 は未完。見込み約5,500〜12,000行・外枠16,000行は不変。

一覧：済み0／全体3（うち追加0）。


## G3・S03：Segre 標準開から二因子の標準開のテンソル積への写像

`SegreNormalizedCoordinates`（90行）：`segreCoordinateDescend` は実際の座標写像の後の任意の代数写像を同じ核の商へ降ろす。`segreCoordinateDescend_projection` は商写像との一致。`segreNormalizedCoordinateMap` は二因子の正規化のテンソル積を降ろした写像、`segreNormalizedCoordinateMap_X` は座標の式、`segreNormalizedCoordinateMap_denominator` は選んだ分母の像が 1 となる式。`segreCoordinate_denominator_mem` は同じ商の次数一への所属。`segreStandardOpenToTensor` は実際の Segre 標準開から二因子の標準開のテンソル積への代数写像。平坦性・次数一生成はこの順方向には不要。

単独検証、ソース完全一致、対象と直接 importer のビルド5,095ジョブ、小監査16宣言・標準三公理のみ、終了状態0。ログ `2g-segre-normalized-coordinates-check-2.log`・`2g-segre-normalized-coordinates-native.log`・`2g-segre-normalized-coordinates-audit.log`。追加公理・sorry・既存宣言の型変更・200行超の宣言なし。鍵は検証中だけ使用。

2g-2 本体1,540行・入口込み1,566行、小監査168宣言・標準三公理のみ。S03 の順方向に到達したが、逆写像・互いの逆・重なりの自然性は残る。S04・有限冪と G4〜G5 も未完。見込み約5,500〜12,000行・外枠16,000行は不変。

一覧：済み0／全体3（うち追加0）。

### S03：逆向きの写像の法則への分割（着手前の型、S03 の内数）

次数 d の斉次多項式 F について、同じ元 c をすべての変数に掛けた評価は `c^d * aeval x F` に等しい（40〜80行）。これを列・行の Segre 座標評価に使い、元の次数一評価の核が同次であることから、列・行の評価が同じ Segre 座標環へ降りることを示す（80〜180行）。元の次数一評価が全射なら A,B からの実際の代数写像を得る。選んだ座標で正規化し、A_(ai),B_(bj) から Segre 標準開へ特殊化してテンソル積の写像を作る（80〜150行）。その後に座標と斉次分数で互いの逆を照合する。斉次な核・全射性の条件は実際の Rees と座標環の商が持つ条件であり、新しい最終仮定ではない。


## G3・S03：斉次評価の拡大則

`HomogeneousEvaluationScaling`（30行）：`homogeneous_aeval_mul` は次数 d の斉次多項式の全変数を c 倍した評価が c^d 倍になる式。係数環と評価先の宇宙を分離し、c の非零性を仮定しない。

単独検証は初回成功、ソース完全一致、対象と直接 importer のビルド5,096ジョブ、小監査1宣言・標準三公理のみ、終了状態0。ログ `2g-homogeneous-evaluation-scaling-check.log`・`2g-homogeneous-evaluation-scaling-native.log`・`2g-homogeneous-evaluation-scaling-audit.log`。追加公理・sorry・既存宣言の型変更・200行超の宣言なし。

2g-2 本体1,570行・入口込み1,597行、小監査169宣言・標準三公理のみ。S03 の逆向き以降は未完、見込み約5,500〜12,000行・外枠16,000行は不変。

一覧：済み0／全体3（うち追加0）。


## G3・S03：Segre 座標の列における斉次関係式

`SegreColumnEvaluation`（53行）：`segreCoordinateMap_column` は一列への変数の代入について、次数 d の多項式の像が b_j^d と元の評価の純テンソルになる式。`segreCoordinateProjection_column_zero` は元の斉次関係式が同じ座標環の商で消えること。

単独検証、ソース完全一致、対象と直接 importer のビルド5,097ジョブ、小監査2宣言・標準三公理のみ、終了状態0。ログ `2g-segre-column-evaluation-check-2.log`・`2g-segre-column-evaluation-native.log`・`2g-segre-column-evaluation-audit.log`。追加公理・sorry・既存宣言の型変更・200行超の宣言なし。

2g-2 本体1,623行・入口込み1,651行、小監査171宣言・標準三公理のみ。S03 の一般の関係式への降下・逆写像以降は未完、見込み約5,500〜12,000行・外枠16,000行は不変。

一覧：済み0／全体3（うち追加0）。


## G3・S03：全関係式の列への降下

`SegreColumnDescent`（65行）：`segreColumnPolynomialMap` は一列への代入の実際の代数写像。`degreeOne_aeval_kernel_homogeneous` は次数一評価の核の斉次性。`segreColumnPolynomialMap_kernel_le` は次数分解により全関係式を消すこと。`segreColumnFromFactor` は実際の全射表示による因子 A からの降下、`segreColumnFromFactor_generator` は次数一生成元の像。grading と次数一への所属を引数に保持し、平坦性を仮定しない。

単独検証、ソース完全一致、対象と直接 importer のビルド5,098ジョブ、小監査7宣言・標準三公理のみ、終了状態0。ログ `2g-segre-column-descent-check-2.log`・`2g-segre-column-descent-native.log`・`2g-segre-column-descent-audit.log`。追加公理・sorry・既存宣言の型変更・200行超の宣言なし。

2g-2 本体1,688行・入口込み1,717行、小監査178宣言・標準三公理のみ。今回 de7b09089 の後は5モジュール285行＋入口5行、小監査34宣言。S03 の行側・逆写像の組立てと互いの逆・重なりの自然性、S04 と有限冪、G4〜G5 は未完。見込み約5,500〜12,000行・外枠16,000行は不変。

一覧：済み0／全体3（うち追加0）。
