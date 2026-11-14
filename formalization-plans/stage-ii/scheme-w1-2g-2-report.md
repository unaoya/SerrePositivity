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
