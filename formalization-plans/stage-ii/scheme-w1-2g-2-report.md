# SC-W1 2g-2：G3〜G5 の実装記録

2026-11-15。2g-1 の数学 e5b3e411f・停止点報告56ea849a3 の後、既承認の G3 へ進む。G1・G2 は17／17完了。2g-2 の外枠16,000行は別計上し、最終の AugmentedRingCechExact と利用側の型は変えない。root・下流全ビルドを行わず、対象と直接 importer、小監査を共有鍵 --class impl --wait 3600 で別々に検証する。

## 主項目の一覧

| ID | 型・出口 | 状態 | 追加 |
| --- | --- | --- | --- |
| G3 | BS17 Lemma 2.6 の帰納的レベルの有限性と、射影版の入力に使うブローアップ・有限ファイバー冪の表示 | 済み | 下記の有限レベルの存在・Rees と既存の Čech 各項の実際の表示 |
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


## G3・S03：テンソル積の交換による行側の評価と降下

`SegreRowDescent`（83行）：`segreCoordinateMap_row` は交換同型で列の斉次評価を使う行側の式。`segreCoordinateProjection_row_zero` は斉次関係式が消える式。`segreRowPolynomialMap`・`segreRowPolynomialMap_kernel_le` は全関係式の降下。`segreRowFromFactor` は全射表示からの因子 B の代数写像、`segreRowFromFactor_generator` は生成元の像。平坦性を仮定しない。

単独検証、ソース完全一致、対象と直接 importer のビルド5,099ジョブ、小監査8宣言・標準三公理のみ、終了状態0。ログ `2g-segre-row-descent-check-2.log`・`2g-segre-row-descent-native.log`・`2g-segre-row-descent-audit.log`。追加公理・sorry・既存宣言の型変更・200行超の宣言なし。

2g-2 本体1,771行・入口込み1,801行、小監査186宣言・標準三公理のみ。S03 の行・列の因子写像に到達したが、正規化したチャートの逆写像と互いの逆・重なりの自然性は未完。S04・有限冪、G4〜G5 も未完。見込み約5,500〜12,000行・外枠16,000行は不変。

一覧：済み0／全体3（うち追加0）。

S03 の逆の法則の追加の分割（着手前、S03 の内数、30〜80行）：実際の座標写像の核から `Z_kj * Z_il = Z_kl * Z_ij` を同じ商で示す。選んだ Zij による正規化の後に `normalize Z_kj * normalize Z_il = normalize Z_kl` を得る。次数一正規化の全射性は、任意の斉次分数 x/f^n が normalize x である既存の式の帰結として使う。


## G3・S03：実際の Segre 座標環の二次関係式

`SegreCoordinateMinors`（49行）：`segreCoordinate_minor` は実際の座標写像の核から得る 2×2 小行列式の関係式。`segreCoordinate_normalized_minor` は選んだ座標による正規化の後、同じ列と行の座標の積が元の座標になること。平坦性・非零な座標・非自明な局所化を仮定しない。

単独検証は初回成功、ソース完全一致、対象と直接 importer のビルド5,100ジョブ、小監査2宣言・標準三公理のみ、終了状態0。ログ `2g-segre-coordinate-minors-check.log`・`2g-segre-coordinate-minors-native.log`・`2g-segre-coordinate-minors-audit.log`。追加公理・sorry・既存宣言の型変更・200行超の宣言なし。鍵は検証中だけ使用（--class impl --wait 3600、待ちは一つ）。root・下流全ビルド・全体監査は行っていない。

2g-2 本体1,820行・入口込み1,851行、小監査188宣言・標準三公理のみ。de7b09089 の後の今回の束は7モジュール417行＋入口7行、小監査44宣言。S03 の順方向、二因子の行・列の写像と逆を照合する二次関係式に到達した。残りは特殊化した行・列を束ねる逆向きのテンソル積の写像、互いの逆、重なりの自然性、S04 の貼り合わせと有限冪、G4〜G5。見込み約5,500〜12,000行・外枠16,000行は不変。停止点2g-2ではない。

一覧：済み0／全体3（うち追加0）。


S03 の逆写像の組立て（着手前の型、前記80〜150行の内数）：`segreColumnChartMap` と `segreRowChartMap` は因子からの列・行の写像を Segre の標準開で正規化して特殊化した代数写像。二因子の次数一評価の全射性を引数に保持する。これらを `Algebra.TensorProduct.lift` で `segreTensorToStandardOpen` に束ね、正規化した二つの生成元の純テンソルの像が同じ Segre 座標の正規化になる式を示す。互いの逆の全元の照合と重なりの自然性は次の分割。


S03 の合成の全元への照合の法則の分割（着手前、S03 の内数、35〜75行）：`homogeneousDegreeOneNormalize_surjective` は各斉次分数の正規化による表示からの全射性。`degreeOneChart_algHom_ext` は次数一評価が全射のとき、正規化した次数一生成元で一致する二つのチャートの代数写像が等しいこと。これで合成の検証を座標の等式へ戻す。二因子のテンソル積では既存の TensorProduct の射の外延性を使い、全タプルの新しい複体を作らない。


S03 の順写像との合成の分割（着手前、S03 の内数、60〜120行）：順写像を Segre 座標環の正規化と合成すると `segreNormalizedCoordinateMap` に等しい。行・列の因子写像との合成は、それぞれ因子の正規化とテンソル積への includeLeft/includeRight の合成に等しい。この二つは全射な次数一表示を通じて生成元で照合し、一般の元へ移す。これを逆写像との二つの合成の証明に使う。


### S03：待ち時間に準備した下書きと検証順（未検証）

`scheme-drafts/SegreChartInverse.lean`：行・列を標準開で正規化して特殊化し、テンソル積の逆向きの写像と正規化した生成元の像を記述した。Segre の grading を型クラスから推論させず、実際の `segreCoordinateGradedRing a b G ha` を各宣言で明示供給する。初回の明示引数の問題を修正した後の検証は、共有鍵の一つの待ちにまとめている。

`scheme-drafts/DegreeOneChartExt.lean`：正規化の全射性と生成元による代数写像の外延性。`scheme-drafts/SegreChartForwardLaws.lean`：順写像と正規化・行・列の因子写像との合成。`scheme-drafts/SegreChartEquiv.lean`：前二つと逆向きの写像を使い、二つの合成と実際の代数同型を記述。いずれも未検証で、本体へ登録せずコミットの対象から外した。

検証順は逆向きの写像 → 外延性 → 順写像の合成則 → 二つの合成と代数同型。それぞれ通ったソースだけを本体へ移し、対象・直接 importer のビルドと小監査の後にコミットする。現在の検証済み実測は本体1,820行・入口込み1,851行、小監査188宣言・標準三公理のみのまま。未検証の下書きを実測や完成の証拠に含めない。

S04 への接続では、Mathlib `Proj.awayι_toSpecZero` と既存の `schemeScalarMorphism_projectiveScalar` を組み合わせ、チャートの構造射を同じ Spec R 上で比較する。局所同型の貼り合わせには既存の開被覆の `glueMorphisms` を用いる。重なりでは積の分母への局所化と二次関係式の自然性の証明が依然として必要であり、下書きの代数同型だけで S03・S04 の完成とはしない。

一覧：済み0／全体3（うち追加0）。


### S03 の重なりの自然性：既存 API の照合（紙、未証明）

Mathlib `HomogeneousLocalization.Away.isLocalization_mul` は、次数 d>0 の f と斉次 g に対し、`Away G (f*g)` が `Away G f` の `g^d/f^deg(g)` による通常の局所化であることを供給する。次数一同士ならこの元は g/f。`awayMap_mk` は同じ制限の分子・分母の式。したがって積の標準開ごとに新たな斉次分数の普遍性を証明する必要はない。

二因子の重なりは `Away H (b_j*b_l) ⊗[R] Away G (a_i*a_k)`。`IsLocalization.tensorProduct_tensorProduct_right` と `tensorProductEquivOfMapIncludeRight`（Mathlib RingTheory/Localization/BaseChange）は、片因子の局所化を元のテンソル積の includeRight の像での局所化へ移す。反対側は交換同型で移し、`IsLocalization.Away.mul'`（Away/Basic）で二つの局所化を積の元での局所化に合わせる。この計算に平坦性は要らない。

Segre チャートの同型では、追加の座標 Z_kl/Z_ij の像は、二因子の正規化した座標の純テンソルになる（検証済み `segreNormalizedCoordinateMap_X`）。上記の通常の局所化の比較をこの元に適用し、制限したチャート同型を作る予定。左右の選択の一致は局所化の射の外延性と同じ二次関係式に戻す。この自然性の Lean はまだ未証明である。

続く S04 は Mathlib `Proj.awayι_toSpecZero` と本体の `schemeScalarMorphism_projectiveScalar` で Spec R への構造射をそろえ、アフィン pullback のテンソル表示と `Scheme.Cover.glueMorphisms` を使う。上記は既承認の S03〜S04 の法則の分割で、追加の主項目・最終仮定を設けない。見込み約5,500〜12,000行・外枠16,000行は不変。

一覧：済み0／全体3（うち追加0）。


S04 の基底への構造射の法則の分割（着手前、S04 の内数、40〜90行）：`projectiveAway_scalarMap` は次数零のスカラーを fromZeroRingHom で標準開へ送る合成が、既存の projectiveHomogeneousAwayAlgebra の係数写像と等しいこと。`projectiveAway_structureMap` は `Proj.awayι G f hf hd ≫ projectiveCechStructureMap G = Spec.map(algebraMap R (Away G f))`。Mathlib の `awayι_toSpecZero` と既存の構造射の比較に渡し、新しい構造層・新しい基底上の対象を定義しない。


### S03 逆写像の単独検証の区切り（対象ビルド・監査前）

`SegreChartInverse` の118行は `2g-segre-chart-inverse-check-4.log` で単独検証成功（終了状態0）。行・列の標準開の写像、テンソル積への束ね方、正規化した二生成元の純テンソルが同じ Segre 座標に戻る式までを含む。ソース完全一致を確認して本体の新しいファイルへ移したが、対象・直接 importer のビルドと小監査は未了のため、この数学はまだコミットしていない。

同じ検証の束の残り3本では、正規化の環写像と代数写像の表示を明示する修正と、RingHom の外延性が斉次局所化の値まで進みすぎる箇所の修正を行った。次の待ちは一つで、外延性・順写像の合成則・基底構造射の修正検証を順に行い、最後に逆写像と直接 importer の対象ビルドを行う。未了の3本は drafts のまま。本体1,820行・入口込み1,851行、小監査188宣言という検証済み実測はまだ更新しない。

一覧：済み0／全体3（うち追加0）。


### G3 の射影表示から G4 への接続の再照合（紙）

`projectivePerfectCartesianSquare_acyclic` は任意の Cartesian な閉中心の始域 Y を引数に取り、閉厚化の制限・増大の辺を実際の構造層の写像と照合する（同名モジュールと ProjectivePerfectCartesianSquareEdges）。したがって閉中心に戻すために「Segre 座標写像の核が任意の底変換と可換」という誤った一般仮定を置かない。Proj の商の既存の Cartesian 比較を使う。

B1 の `isCechExact_of_comp` の追加条件は、細分した被覆 C/A 自身を B/A の正次数の各項に底変換したときの完全性である。細分の射 C/B が flat であることを要求する定理ではないし、細分した被覆自身の完全性だけから消去はできない。G4 はこの底変換後の条件も満たす形で組み立てる。

このため G3 の係数移送の法則には、有限な全射次数一表示の Proj の任意のアフィン底変換の表示も含める：R→R' に対し、次数付き環 R'⊗[R]A の Proj が元の Proj の実際の pullback となり、次数一表示・多項式環上有限性・標準開と構造射を保つ（既存の Proj の係数移送の法則の分割、見込み200〜500行）。R' の flat 性は仮定しない。次数一の標準開は A/(f−1) の同型と、テンソル積と商の既存の比較で任意の係数移送へ戻せるため、S03〜S04 の標準開と貼り合わせの手順を再利用する。2e の flat な Čech コホモロジーの底変換を、任意の底変換の定理として流用しない。

これは G3 の射影表示の係数移送の法則で、主項目や最終の仮定を追加しない。全体の見込み約5,500〜12,000行・外枠16,000行は維持するが、この法則はまだ未証明。

一覧：済み0／全体3（うち追加0）。


### S03〜S04 の単独検証と逆写像の対象ビルド（監査前）

`SegreChartForwardLaws`（75行）は `2g-segre-chart-forward-laws-check-2.log`、`ProjectiveAwayStructureMap`（49行）は `2g-projective-away-structure-map-check-2.log` で単独検証成功（終了状態0）。同じソースを本体へ移し登録したが、この2本の本体の対象ビルドはまだ行っていない。

`SegreChartInverse` は対象・直接 importer のビルドも成功（5,101ジョブ、終了状態0、`2g-segre-chart-inverse-native.log`）。小監査は未了のため数学のコミットはまだ保留。外延性は、多項式の変数 X の評価を先に書き換えてから正規化の環写像と代数写像を照合する修正を行い、`2g-degree-one-chart-ext-check-3.log` を出す一つの待機プロセスで再検証を待っている。4本の小監査の下書きも準備済み。

検証済み実測の本体1,820行・入口込み1,851行、小監査188宣言はまだ更新しない。これらを個別に対象ビルド・監査まで確認してからまとめて記録する。G3 の残り・G4〜G5 は引き続き未完。

一覧：済み0／全体3（うち追加0）。


S04 の係数移送のチャートの法則の分割（着手前、前記200〜500行の内数、50〜100行）：次数一 f∈G1 に対し `B ⊗[R] Away G f ≃ₐ[B] Away (fun n ↦ (G n).baseChange B) (1⊗f)` を、二つの脱斉次化の同型と Mathlib `Algebra.TensorProduct.tensorQuotientEquiv` で作る。延長したイデアル `(f−1)` が `(1⊗f−1)` である式も供給する。正規化した元の純テンソルの像を比較し、任意の係数環 B での標準開の比較へ使う。B の flat 性・Noether 性は不要。これは Proj の既存の係数移送のチャートの法則で、最終の主張や主項目は追加しない。


待ち時間の係数移送の下書き `scheme-drafts/HomogeneousDegreeOneBaseChange.lean`（49行）では、`degreeOneDehomogenizationIdeal_baseChange` と `homogeneousDegreeOneBaseChangeEquiv` の型・合成を記述した。Mathlib の `Algebra.TensorProduct.tensorQuotientEquiv` と `Ideal.quotientEquivAlgOfEq` を使い、標準開の任意の係数移送を脱斉次化の商へ戻す。未検証なので drafts のままコミットせず、自然性の式と Proj の貼り合わせも依然として未証明。検証順は現在待っている外延性 → 本体の対象ビルド → 4本の小監査 → チャートの二つの合成と同型 → 重なりとこの係数移送、を維持する。

一覧：済み0／全体3（うち追加0）。


S03〜S04 の正規化の自然性の法則の分割（着手前、同じ自然性の内数、40〜90行）：graded な環写像 g:G→H と次数一 f∈G1 について、`Away.map g f (normalize_G x) = normalize_H (g x)` を示す。係数環は別でもよく、Mathlib `Away.map_mk` と既存の正規化の斉次元での式を使い、直和の外延性で一般の x へ戻す。係数移送の 1⊗− と標準開の写像の自然性に使う。新しい主項目ではない。


## G3・S03〜S04：逆向きのチャート写像・外延性・合成則・基底構造射の検証

`SegreChartInverse`（118行）：
- `segreColumnChartMap`：列の因子写像を正規化し、因子の標準開から Segre 標準開へ特殊化する。
- `segreColumnChartMap_normalize`：列の写像と元の因子の正規化の合成の式。
- `segreRowChartMap`：同じ構成を行側で特殊化する。
- `segreRowChartMap_normalize`：行の写像と正規化の合成の式。
- `segreTensorToStandardOpen`：二因子の標準開のテンソル積から Segre 標準開への実際の代数写像。
- `segreTensorToStandardOpen_generators`：正規化した二生成元の純テンソルは、同じ Segre 座標の正規化に移る。

`DegreeOneChartExt`（54行）：
- `homogeneousDegreeOneNormalize_surjective`：次数一の分母による正規化は斉次局所化の全体へ全射。
- `degreeOneChart_algHom_ext`：全射な次数一表示では、正規化した生成元上の一致が標準開の代数写像を決める。

`SegreChartForwardLaws`（75行）：
- `segreStandardOpenToTensor_normalize`：Segre 座標環の正規化の後の順写像は、同じ正規化された座標写像。
- `segreNormalizedCoordinateMap_column`：列の因子写像との合成は右因子の正規化とテンソル積への包含。
- `segreNormalizedCoordinateMap_row`：行の因子写像との合成は左因子の正規化とテンソル積への包含。

`ProjectiveAwayStructureMap`（49行）：
- `projectiveAway_scalarMap`：次数零のスカラーを標準開へ送る合成は、既存の基底環の係数写像。
- `projectiveAway_structureMap`：標準開から Proj への射は、同じ Spec R 上の構造射と整合する。

本体と保存した下書きの一致を確認。各ファイルの単独検証に続く入口の同時 import で匿名 local instance の名前が衝突したため、この4本のローカル instance を固有名にした。数学の仮定・既存の代数構造を変更せず、4本と直接 importer `SerrePositivity.AlgebraicGeometry` を再ビルドして成功（5,104ジョブ、終了状態0）。小監査は4モジュール39宣言（21・5・9・4）すべて標準三公理のみ、終了状態0。

ログ `2g-segre-chart-inverse-check-4.log`・`2g-degree-one-chart-ext-check-3.log`・`2g-segre-chart-forward-laws-check-2.log`・`2g-projective-away-structure-map-check-2.log`・`2g-segre-chart-laws-native-2.log`・`2g-segre-chart-laws-audit.log`。追加公理・sorry・既存宣言の型変更・200行超の宣言なし。検証・ビルド・小監査は共有鍵 --class impl --wait 3600 の下で実行し、待ちは常に一つ。root SerrePositivity・下流全ビルド・全体監査は行っていない。

今回4モジュール296行＋入口4行。2g-2 本体2,116行・入口込み2,151行、小監査227宣言・標準三公理のみ。S03 の二つの合成と代数同型はまだ drafts のままで、重なりの自然性、S04 の貼り合わせ・有限冪・任意の係数移送、G4〜G5 も未完。見込み約5,500〜12,000行・外枠16,000行は不変。停止点2g-2ではない。

一覧：済み0／全体3（うち追加0）。


## G3・S03：Segre 標準開と二因子の標準開の実際の代数同型

`SegreChartEquiv`（107行）：
- `segreTensorToStandardOpen_leftInverse`：Segre 標準開の全元で、逆写像と順写像の合成は恒等写像。
- `segreTensorToStandardOpen_rightInverse`：二因子の標準開のテンソル積の全元でも、順写像と逆写像の合成は恒等写像。
- `segreStandardOpenTensorEquiv`：同じ Segre 標準開と二因子の標準開のテンソル積との実際の R 上の代数同型。

元の次数一評価の全射性を保持し、平坦性・Noether 性・非零な分母は仮定しない。最初の検証では左の合成の最後の恒等代数写像の評価だけが残り、`AlgHom.id_apply` を明示して解決した。本体と下書きのソース完全一致、単独検証、対象と直接 importer のビルド5,105ジョブ、小監査14宣言・標準三公理のみ、終了状態0。ログ `2g-segre-chart-equiv-check-2.log`・`2g-segre-chart-equiv-native.log`・`2g-segre-chart-equiv-audit.log`。追加公理・sorry・既存宣言の型変更・200行超の宣言なし。

2g-2 本体2,223行・入口込み2,259行、小監査241宣言・標準三公理のみ。この区切りまでの数学の束は5モジュール403行＋入口5行、小監査53宣言。S03 は実際のチャートの代数同型に到達したが、重なりの自然性は未完。S04 の大域の貼り合わせと有限冪・任意の係数移送、G4〜G5 も未完。見込み約5,500〜12,000行・外枠16,000行は不変。root SerrePositivity・下流全ビルド・全体監査は実行していない。停止点2g-2ではない。

一覧：済み0／全体3（うち追加0）。


## G3・S03〜S04：任意の係数移送の標準開と正規化の自然性

`HomogeneousDegreeOneBaseChange`（49行）：`degreeOneDehomogenizationIdeal_baseChange` は延長した (f−1) のイデアルが (1⊗f−1) になる式。`homogeneousDegreeOneBaseChangeEquiv` は `B ⊗[R] Away G f` と係数移送後の標準開との実際の B 上の代数同型。B の flat 性・Noether 性は不要。

`HomogeneousDegreeOneNormalizationNaturality`（45行）：`homogeneousDegreeOneNormalize_naturality` は任意の graded な環写像と正規化の可換性。二つの grading の係数環と宇宙は別でもよい。Mathlib の Away.map_mk と直和の環の外延性に渡す。

二つの保存した下書きから再構成した一つの Lean 検証ファイルとの一致を確認し、単独検証、各本体と直接 importer のビルド5,107ジョブ、小監査14宣言（13・1）・標準三公理のみ、終了状態0。最初の検証の恒等同型の引数と graded な環写像の coercion の照合を明示して解決した。ログ `2g-standard-chart-scalar-laws-check-2.log`・`2g-standard-chart-scalar-laws-native.log`・`2g-standard-chart-scalar-laws-audit.log`。追加公理・sorry・既存宣言の型変更・200行超の宣言なし。検証・ビルド・監査は共有鍵 --class impl --wait 3600、待ちは一つ。

今回2モジュール94行＋入口2行。2g-2 本体2,317行・入口込み2,355行、小監査255宣言・標準三公理のみ。任意の係数移送のチャートの環同型まで到達したが、その射の比較と Proj の大域の pullback はまだ未証明。S03 の重なりの自然性、S04 の貼り合わせと有限冪、G4〜G5 も未完。見込み約5,500〜12,000行・外枠16,000行は不変。停止点2g-2ではない。

一覧：済み0／全体3（うち追加0）。

S04 の係数移送の同型の式の分割（着手前、係数移送の内数、30〜70行）：`homogeneousDegreeOneBaseChangeEquiv_tmul_normalize` は b⊗normalize x の像が係数移送後の b⊗x の正規化になる式。商の同型の元上の式とテンソル積・商の同型の純テンソル上の式を用いる。新たな平坦性を仮定しない。


S04 の係数移送の大域の射の法則の分割（着手前、前記200〜500行の内数、50〜100行）：`projectiveCoefficientGradedMap` は Mathlib の includeRight の同じ環写像を、係数環 B の grading への graded な射に束ねる。`projectiveCoefficient_irrelevant_le_map` は移送後の irrelevant ideal が元の irrelevant ideal の像に入ること。各次数の baseChange の span の式で示し、Mathlib `Proj.map` に渡して実際の `Proj ((G ·).baseChange B) → Proj G` と標準開の逆像の式を供給する。flat 性・Noether 性・次数一生成はこの射の構成には不要。pullback の証明やスカラー構造射との整合性は後続の法則であり、この射だけで完了としない。


## G3・S04：係数移送のチャート同型における正規化した純テンソルの像

`HomogeneousDegreeOneBaseChangeFormula`（43行）：`homogeneousDegreeOneBaseChangeEquiv_tmul_normalize` は b⊗normalize x の像が、移送後の b⊗x の正規化になる式。任意の x に対して成り立ち、flat 性・Noether 性は不要。商の元上の式・テンソル積と商の同型の式を合成した。

単独検証は初回成功、本体と保存した下書きのソース完全一致、対象と直接 importer のビルド5,108ジョブ、小監査7宣言・標準三公理のみ、終了状態0。ログ `2g-degree-one-base-change-formula-check.log`・`2g-degree-one-base-change-formula-native.log`・`2g-degree-one-base-change-formula-audit.log`。追加公理・sorry・既存宣言の型変更・200行超の宣言なし。各確認は共有鍵 --class impl --wait 3600 の下で行い、待ちは一つ。

2g-2 本体2,360行・入口込み2,399行、小監査262宣言・標準三公理のみ。90649a8b1 の後の今回の束は3モジュール137行＋入口3行、小監査21宣言。任意の係数移送の大域の射は次の drafts にあり、Proj の pullback の証明・S03 の重なりの自然性・S04 の貼り合わせと有限冪・G4〜G5 は未完。見込み約5,500〜12,000行・外枠16,000行は不変。停止点2g-2ではない。

一覧：済み0／全体3（うち追加0）。


## G3・S04：任意の係数移送の Proj の実際の射

`ProjectiveCoefficientMap`（53行）：`projectiveCoefficientGradedMap` は includeRight の同じ環写像を B の次数成分への graded な射に束ねる。`projectiveCoefficient_irrelevant_le_map` は移送後の irrelevant ideal が元の irrelevant ideal の像に入ること。`projectiveCoefficientMap` は既存の Proj.map で作った実際の射。`projectiveCoefficientMap_preimage_basicOpen` は標準開の逆像の式。flat 性・Noether 性・次数一生成はいずれも不要。

単独検証は初回成功、本体と保存した下書きのソース完全一致、対象と直接 importer のビルド5,109ジョブ、小監査9宣言・標準三公理のみ、終了状態0。ログ `2g-projective-coefficient-map-check.log`・`2g-projective-coefficient-map-native.log`・`2g-projective-coefficient-map-audit.log`。追加公理・sorry・既存宣言の型変更・200行超の宣言なし。共有鍵 --class impl --wait 3600、待ちは一つ。

2g-2 本体2,413行・入口込み2,453行、小監査271宣言・標準三公理のみ。90649a8b1 の後の係数移送の束は4モジュール190行＋入口4行、小監査30宣言。大域の射に到達したが、基底への構造射との整合性と Proj の pullback、S03 の重なりの自然性、S04 の貼り合わせと有限冪、G4〜G5 は未完。見込み約5,500〜12,000行・外枠16,000行は不変。停止点2g-2ではない。

一覧：済み0／全体3（うち追加0）。

S04 の係数移送の標準開の射の法則の分割（着手前、係数移送の内数、40〜100行）：`projectiveCoefficientAwayMap_eq` は元の標準開からの Away.map が、テンソル積への includeRight と係数移送の同型の合成であること。正規化の全射性と純テンソルの像の式で照合する。`projectiveCoefficientMap_awayι` は対応する Spec の写像と Proj の射の四角形の可換性。Mathlib の awayι_comp_map に渡す。追加の flat 性や Noether 性を仮定しない。


S04 の構造射との整合性の法則の分割（着手前、係数移送の内数、60〜120行）：`projectiveCoefficientAwayMap_scalar` は任意の分母 f で、Away.map が元の R のスカラーを B のスカラーを通した同じ定数へ送る式。`projectiveCoefficientMap_structureMap` は `projectiveCoefficientMap G ≫ projectiveCechStructureMap G = projectiveCechStructureMap ((G ·).baseChange B) ≫ Spec.map (algebraMap R B)`。正次数の全標準開の被覆と既存の構造射の局所式で貼り合わせる。次数一生成・平坦性・Noether 性を追加しない。既存の射の自然性の法則で、主項目は増えない。


S04 の係数移送の局所 pullback の法則の分割（着手前、係数移送の内数、50〜110行）：`isPullback_projectiveCoefficientChart` は、次数一 f の移送後の標準開からの Spec の二つの実際の射が、Spec R・Spec B と元の標準開の pullback を与えること。既存の `affineTensorModelIso` に構成済みの B 上の標準開の同型を渡す。`isPullback_projectiveCoefficientAwayι` は、同じ標準開の四角形が Proj の係数移送の射の pullback であること。開埋め込みと基本開の逆像の式で示す。これらを全標準開上で貼り合わせる段は後続であり、この局所四角形だけで大域の pullback の完成としない。


S04 の係数移送の大域 pullback の法則の分割（着手前、係数移送の内数、50〜100行）：`isPullback_projectiveCoefficientMap` は、次数一の元 aᵢ の span が irrelevant ideal を含む場合に、`projectiveCoefficientMap G`・二つの既存の構造射・Spec(algebraMap R B) の四角形が実際の pullback であること。元の Proj の標準開被覆で局所判定し、局所の pullback の二つを貼り合わせる。Rees の既存の次数一被覆がこの仮定を供給する。B の平坦性や Noether 性、A の R 上の平坦性を追加しない。局所式・構造射・局所 pullback と合わせて係数移送の残りを4モジュール約230〜350行と見直す（前記200〜500行に対して、既存190行と合わせ約420〜540行）。全体の見込み・外枠は変更しない。


S03 の重なりの法則の分割（着手前、既存の自然性の内数、70〜140行）：`homogeneousAwayMulRestrictionAlgHom G hg hx` は既存の awayMap を元の R 上の代数写像に束ねる。`homogeneousDegreeOneNormalize_eq_isLocalizationElem` は次数一の正規化された g/f と Mathlib の交叉を切り出す元との一致。`isUnit_homogeneousDegreeOneNormalize_restrict` はその元が D(fg) で単元になる法則。`homogeneousDegreeOneRestriction_transition` は次数一 x に対する `res_g(x/g) * res_f(g/f) = res_f(x/f)`。非零性や平坦性を追加せず、既存の IsLocalization_mul と斉次分数の式で示す。Segre チャートの重なりで用いる法則の分割で、新しい主項目ではない。


## G3・S04：任意の係数移送の実際の Proj の pullback

`ProjectiveCoefficientChart`（58行）：`projectiveCoefficientAwayMap_eq` は標準開の射とテンソル積への包含・構成済みの代数同型の合成との一致。`projectiveCoefficientMap_awayι` はその Spec と Proj の標準開の可換性。

`ProjectiveCoefficientStructureMap`（67行）：`projectiveCoefficientAwayMap_scalar` は任意の分母の標準開の射が R のスカラーを保存すること。`projectiveCoefficientMap_structureMap` は元の Proj と移送後の Proj の構造射の実際の可換性。次数一生成も仮定しない。

`ProjectiveCoefficientChartPullback`（61行）：`isPullback_projectiveCoefficientChart` は次数一の標準開と Spec B の実際の Cartesian 四角形。`isPullback_projectiveCoefficientAwayι` は任意の正次数の標準開が Proj の係数移送の射の pullback であること。

`ProjectiveCoefficientPullback`（57行）：`isPullback_projectiveCoefficientMap` は、次数一の元の span が irrelevant ideal を含む場合に、移送後の Proj が元の Proj と Spec B の実際のファイバー積であること。元の Proj の開被覆で局所判定し、上の二つの Cartesian 四角形を移送した。Rees の既存の被覆がこの仮定を供給する。係数移送の平坦性・Noether 性・元の環の R 上の平坦性は不要。

保存した下書きと本体のソース完全一致、四つをまとめた単独検証、対象と直接 importer のビルド5,113ジョブ、小監査19宣言（5・6・7・1）・標準三公理のみ、終了状態0。最初の局所式では graded map の像と 1⊗f の照合、構造射では被覆の定義を明示し、対応する Mathlib の証明と同じ局所的な backward.isDefEq.respectTransparency false を三宣言に用いた。資源制限の引き上げなし。行長の警告を折り返した後も対象ビルドを再実行し成功。ログ `2g-coefficient-pullback-check-2.log`・`2g-projective-coefficient-pullback-native-2.log`・`2g-projective-coefficient-pullback-audit.log`。追加公理・sorry・既存宣言の型変更・200行超の宣言なし。検証・ビルド・監査は各回別の共有鍵 --class impl --wait 3600、待ちは一つ。root・下流全ビルド・全体監査は行っていない。

今回4モジュール243行＋入口4行。2g-2 本体2,656行・入口込み2,700行、小監査290宣言・標準三公理のみ。90649a8b1 の後の係数移送の束は8モジュール433行＋入口8行、小監査49宣言。次数一被覆を持つ Proj の任意の係数移送の大域 pullback に到達した。S03 の Segre の重なりの自然性、S04 の Segre の大域貼り合わせ・有限ファイバー冪の表示、G4〜G5 は未完。残りの主要な束はこの5つ。全体の見込み約5,500〜12,000行・外枠16,000行は不変。停止点2g-2ではない。

一覧：済み0／全体3（うち追加0）。


S03 の標準開の射の遷移の法則の分割（着手前、自然性の内数、100〜200行）：`exists_degreeOneChart_overlapMap` は、次数一評価が全射な表示について、二つの標準開から C への代数写像 φ・ψ と、単元 φ(g/f)、生成元ごとの遷移式 `ψ(aᵢ/g)*φ(g/f)=φ(aᵢ/f)` から、交叉の斉次局所化から C への同じ制限を持つ代数写像を返す。既存の IsLocalization.Away.liftAlgHom と外延性による延長の法則。`degreeOneChart_compat_of_transition` は、その二つの Spec の射を Proj へ合成すると一致すること。既存の SpecMap_awayMap_awayι に渡す。Segre の行・列の重なりを同じ法則で扱い、射影性や中心の存在を追加の仮定にしない。


S03 の Segre の重なりの座標の法則の分割（着手前、自然性の内数、100〜200行）：二つの座標 δ=Zᵢⱼ・δ′=Zₘₙ の交叉 D(δδ′) 上で、`segreOverlapFirstCoordinate`・`segreOverlapSecondCoordinate` は二つの正規化した座標の制限。`segreOverlapFirst_minor` は小行列式の関係式の制限。`segreOverlap_crossCoordinates_isUnit` は Zₘⱼ/δ と Zᵢₙ/δ の制限がともに単元になる法則。`segreOverlap_coordinate_transition` は一般の正規化の遷移式の適用。`segreOverlap_column_transition`・`segreOverlap_row_transition` は行・列の生成元に必要な遷移式。既存の小行列式と、交叉で δ′/δ が単元になる事実から導く。元の座標環の平坦性・零因子でないことは仮定しない。


S03 の Segre の局所射の重なりの法則の分割（着手前、自然性の内数、90〜180行）：`segreColumnChart_compat`・`segreRowChart_compat` は、D(Zᵢⱼ Zₘₙ) から Proj A・Proj B への、それぞれ二つの標準開を経由する実際の射の一致。構成済みの行・列の標準開写像を同じ交叉へ制限し、前記の単元と座標の遷移式を `degreeOneChart_compat_of_transition` へ渡す。大域の貼り合わせを行う前の可換性の法則。


S04 の Segre の大域の射の法則の分割（着手前、既存の貼り合わせの内数、140〜260行）：`segreProjectiveOpenCover` は既存の次数一の座標の被覆を束ねる。`segreGlueMorphisms` とその標準開への合成則は、実際の交叉 D(δδ′) での可換性を Mathlib の pullbackAwayιIso と glueMorphisms へ渡す貼り合わせの法則。`segreLeftProjection`・`segreRightProjection` は行・列の局所射を貼り合わせた Proj S→Proj A・Proj B の実際の射。標準開との二つの合成則も供給する。これだけで Proj S とファイバー積の同型を主張せず、その判定と有限冪は後続に残す。


S04 の貼り合わせ後の比較の紙の筋：二つの大域の射 πA・πB に対し、`πA ⁻¹ D(aᵢ) ∩ πB ⁻¹ D(bⱼ) = D(Zᵢⱼ)` を元の Segre の全標準開 D(Zₖₗ) 上で確認する。局所の二つの逆像は正規化された Zᵢₗ・Zₖⱼ の基本開で、その交叉は小行列式の式により正規化された Zᵢⱼ の基本開。次に二つの因子の標準開被覆で pullback を順に局所判定し、この逆像の式で現れる対象を同じ D(Zᵢⱼ) と同定する。局所の Cartesian 四角形は既存の `segreStandardOpenTensorEquiv` と二つの行・列の写像で供給する。これにより大域のファイバー積の比較を行い、その後に有限正次数のファイバー冪を帰納で供給する。現時点ではこの段は紙の筋であり、大域の pullback・有限冪は未検証。


## G3・S03：Segre の行・列の局所射の重なりでの一致

`HomogeneousDegreeOneOverlap`（72行）：`homogeneousAwayMulRestrictionAlgHom` は同じ awayMap の R 上の代数写像。`homogeneousDegreeOneNormalize_eq_isLocalizationElem` は比の同定。`isUnit_homogeneousDegreeOneNormalize_restrict` は交叉での単元性。`homogeneousDegreeOneRestriction_transition` は次数一の元の正規化の遷移式。

`DegreeOneChartCompatibility`（92行）：`exists_degreeOneChart_overlapMap` は、生成元ごとの遷移式と単元の条件を満たす二つの局所射の同じ交叉への延長。`degreeOneChart_compat_of_transition` はそれらを Proj へ合成した実際の射の一致。

`SegreOverlapCoordinates`（115行）：`segreOverlapFirstCoordinate`・`segreOverlapSecondCoordinate` は二つの正規化の同じ交叉への制限。`segreOverlapFirst_minor` は小行列式の制限。`segreOverlap_crossCoordinates_isUnit` は二つの交差する座標の比の単元性。`segreOverlap_coordinate_transition`・`segreOverlap_column_transition`・`segreOverlap_row_transition` は一般の座標・列・行の遷移式。

`SegreChartCompatibility`（106行）：`segreColumnChart_compat`・`segreRowChart_compat` は D(Zᵢⱼ Zₘₙ) から二つの標準開を通じる Proj A・Proj B への射の一致。次数一の評価の全射性を使い、平坦性・Noether 性・非零な座標は仮定しない。

四つをまとめた単独検証、下書きと本体のソース完全一致、対象と直接 importer のビルド5,117ジョブ、小監査36宣言（8・5・13・10）・標準三公理のみ、終了状態0。分母を固定する形で map_mul と小行列式の等式を合成し、依存する局所化の型の不要な書き換えを避けた。新しい四ファイルは既定の透明性・資源制限で通る。行長の折り返しの後も再ビルド成功。ログ `2g-segre-chart-compatibility-check-2.log`・`2g-segre-chart-compatibility-native-2.log`・`2g-segre-chart-compatibility-audit.log`。追加公理・sorry・既存宣言の型変更・200行超の宣言なし。検証・ビルド・監査は各回別の共有鍵 --class impl --wait 3600、待ちは一つ。root・下流全ビルド・全体監査は行っていない。

今回4モジュール385行＋入口4行。2g-2 本体3,041行・入口込み3,089行、小監査326宣言・標準三公理のみ。S03 はチャートの実際の代数同型と重なりの射の一致まで到達。S04 の大域の貼り合わせ・ファイバー積・有限冪、G4〜G5 は未完。大域射の下書き `SegreProjectiveProjections.lean` は未検証で drafts に保持。残りの主要な束は大域の貼り合わせとファイバー積、有限冪、G4、G5 の4つ。全体の見込み約5,500〜12,000行・外枠16,000行は不変。停止点2g-2ではない。B4′ の指示に従い、この検証済みの束を先にコミットして追従へ移る。

一覧：済み0／全体3（うち追加0）。


S04 の大域射の標準開の逆像の法則の分割（着手前、既存の貼り合わせの内数、90〜180行）：`segreLeftProjection_chart_preimage_basicOpen`・`segreRightProjection_chart_preimage_basicOpen` は、D(Zᵢⱼ) 上で因子の D(aₖ)・D(bₗ) の逆像が正規化した Zₖⱼ・Zᵢₗ の基本開になる式。`segreProjection_chart_preimage_pair` は、この二つの逆像の交叉が正規化した Zₖₗ の基本開になること。`segreProjection_preimage_pair` は大域の式 `πA⁻¹D(aₖ) ∩ πB⁻¹D(bₗ) = D(Zₖₗ)`。構成済みの大域射の制限式・Proj の基本開の逆像・小行列式の関係を用いる。平坦性・非零の座標・Noether 性は追加しない。ファイバー積の判定の前の、既存の射と開集合の法則である。


S04 の標準開の Cartesian 四角形の法則の分割（着手前、既存のチャート同型の内数、60〜130行）：`isPullback_segreStandardOpen` は、構成済みの列・行の標準開写像の Spec が、二つの因子の標準開の Spec R 上の pullback を与えること。`segreStandardOpenTensorEquiv` の逆写像の Spec の同型で `isPullback_specTensor` を移送し、二つの辺は TensorProduct.lift の単位元を含む純テンソルの式で照合する。Segre 標準開へ余分な因子側の代数構造を入れず、元の R 上の代数構造を保つ。大域の pullback の完成はこの局所四角形と前記の逆像の法則の後に残る。


## G3・S04：Segre の二つの実際の大域射

`SegreProjectiveProjections`（120行）：`segreProjectiveOpenCover` は全座標による実際の標準開被覆。`segreGlueMorphisms` は交叉 D(δδ′) 上の可換性を標準開の pullback の同型で Mathlib の貼り合わせへ渡す。`segreLeftProjection`・`segreRightProjection` は因子の Proj への実際の大域射。`segreLeftProjection_awayι`・`segreRightProjection_awayι` はそれぞれ構成済みの列・行の局所射に戻る制限式。元の次数一の全射表示を使い、平坦性・Noether 性・非零の座標の仮定はない。

単独検証、下書きと本体のソース完全一致、対象と入口だけのビルド5,118ジョブ、小監査29宣言・標準三公理のみ、終了状態0。実際の代数構造を名前付きの局所インスタンスで明示し、貼り合わせの補題では被覆の添字を元の積の型へ戻してから交叉を照合した。この補題だけに局所的な backward.isDefEq.respectTransparency false を使用。資源制限の引き上げ、追加公理、sorry、既存宣言の型変更、200行超の宣言はない。行長を折り返した後も対象ビルド成功。ログ `2g-segre-projective-projections-check-3.log`・`2g-segre-projective-projections-native-2.log`・`2g-segre-projective-projections-audit.log`。共有鍵 --class impl --wait 3600、待ちは常に一つ。root・下流全ビルド・全体監査は行っていない。

今回1モジュール120行＋入口1行。2g-2 本体3,161行・入口込み3,210行、小監査355宣言・標準三公理のみ。二つの大域射と制限式まで到達し、標準開の逆像・局所と大域のファイバー積・有限冪・G4〜G5 は未完。逆像と局所 Cartesian 四角形の未検証の下書きは drafts に保持したまま、今回のコミットには含めない。全体の見込み約5,500〜12,000行・外枠16,000行は不変。停止点2g-2ではない。

一覧：済み0／全体3（うち追加0）。


S04 の二つの開被覆による貼り合わせの法則の分割（着手前、既存の pullback の局所判定の内数、100〜220行）：`opensRange_iteratedPullbackFst` は、二つの因子の開を順に引き戻した開埋め込みの像が二つの逆像の交叉になる式。`isPullback_of_pairOpenCover` は、W→X・W→Y と X→Z・Y→Z に対し、X・Y の開被覆、各対 i,j に対応する W の開埋め込み Vᵢⱼ、像が二つの逆像の交叉になる式、Vᵢⱼ 上の実際の Cartesian 四角形から、元の四角形が Cartesian であることを返す。既存の `Scheme.isPullback_of_openCover` を二回使い、同じ像を持つ開埋め込みの同型で対応づける貼り合わせの法則。大域の可換性や全射性は追加の仮定にせず、局所四角形から得る。Segre に適用するときの Vᵢⱼ は構成済みの標準開で、前記の逆像の式と局所 Cartesian 四角形を渡す。


S04 の因子の標準開被覆の表示の法則の分割（着手前、既存の次数一表示の内数、60〜110行）：`exists_degreeOne_homogeneous_lift` は、次数一評価 R[X]→A が全射なら各斉次元に同じ次数の斉次原像があること。`degreeOne_irrelevant_le_span` は、その生成元のイデアルが irrelevant ideal を含むこと。既存の graded な評価の次数分解との整合性を使う。Rees で検証済みの同じ計算を一般の次数付き R 代数へ供給し、Segre の二つの因子の被覆条件を追加仮定にしない。


S04 の Segre の大域 pullback の法則の分割（着手前、既存の標準開比較の貼り合わせの内数、80〜170行）：`isPullback_segreProjectiveProjections` は、実際の二つの大域射と元の Proj のスカラー構造射が Spec R 上の Cartesian 四角形を与えること。二つの次数一の全射表示から因子の開被覆を作り、`isPullback_of_pairOpenCover` に Segre の標準開、制限式、逆像の交叉の式、局所 Cartesian 四角形を渡す。別の射影スキームや平坦性を仮定せず、元の構造層と実際の射のまま比較する。有限正次数のファイバー冪の表示はこの後に残る。


## G3・S04：標準開の逆像と局所の Cartesian 四角形

`SegreProjectivePreimage`（104行）：`segreLeftProjection_chart_preimage_basicOpen`・`segreRightProjection_chart_preimage_basicOpen` は因子の基本開の逆像の局所式。`segreProjection_chart_preimage_pair` はその交叉の正規化した座標による式。`segreProjection_preimage_pair` は全標準開の被覆を通して得た大域の等式 `πA⁻¹D(aₖ) ∩ πB⁻¹D(bₗ) = D(Zₖₗ)`。元の全射表示から作った大域射そのものに対する法則。

`SegreChartPullback`（75行）：`isPullback_segreStandardOpen` は列・行の二つの標準開写像の Spec が、Spec R 上の実際の Cartesian 四角形であること。既存のテンソル積との同型の逆写像の Spec で移送し、二つの辺を単位元を含む純テンソルで照合する。余分な因子上の代数構造を入れず、R 上の元の構造を保つ。

単独検証、下書きと本体の完全一致、対象と入口のビルド5,120ジョブ、小監査25宣言（16・9）・標準三公理のみ、終了状態0。行長の修正後も対象ビルド成功。局所化の値への外延性を進めすぎないよう環準同型の外延性を明示し、開集合の積の式は依存する型を不用意に書き換えず等式の合成で渡した。大域の逆像の法則と局所 pullback の法則だけに局所的な backward.isDefEq.respectTransparency false を使用。追加公理・sorry・既存の宣言の型変更・資源制限の変更・200行超の宣言はない。ログ `2g-segre-projective-preimage-check-3.log`・`2g-segre-chart-pullback-check-2.log`・`2g-segre-preimage-and-pullback-native-2.log`・`2g-segre-preimage-and-pullback-audit.log`。共有鍵 --class impl --wait 3600、待ちは一つ。root・下流全ビルド・全体監査なし。

今回2モジュール179行＋入口2行。2g-2 本体3,340行・入口込み3,391行、小監査380宣言・標準三公理のみ。大域のファイバー積、有限冪、G4〜G5 は未完。二つの被覆による貼り合わせと因子の被覆条件の下書きは単独検証済みだが、本体の対象ビルドと小監査はまだなので今回のコミットに含めない。全体の見込み約5,500〜12,000行・外枠16,000行は不変。停止点2g-2ではない。

一覧：済み0／全体3（うち追加0）。


S04 の Segre の構造射の法則の分割（着手前、既存の射の合成則の内数、70〜150行）：`segreLeftProjection_structureMap`・`segreRightProjection_structureMap` は、各射影と因子のスカラー構造射との合成が、Segre の Proj の元のスカラー構造射に一致する式。全標準開に制限し、構成済みの列・行の代数写像の R 上の可換性と `projectiveAway_structureMap` で照合する。有限ファイバー冪へ帰納する際も同じ Spec R 上の射を保つための法則で、追加の射影性や平坦性の仮定はない。


S04 の有限冪の射影の法則の分割（着手前、既存の有限 wide pullback の合成則の内数、70〜150行）：`isPullback_finiteFiberPowerSucc` は、f:X→S の n+2 個の wide pullback から、添字 Fin.succ で定めた末尾の n+1 個への射と、先頭の X への射が、S 上の pullback を与えること。既存の WidePullback.lift の普遍性で示し、同じ π・base を保つ。既存の Čech nerve の n 次が n+1 個の wide pullback なので、この法則で正の有限冪に Segre の表示を帰納できる。増大項 S と面・退化・増大写像は既存の Čech nerve のものに戻す必要があり、単なる再帰的な別の対象だけを最終出力にしない。


## G3・S04：実際の Segre の大域のファイバー積と構造射

`PairOpenCoverPullback`（78行）：`opensRange_iteratedPullbackFst` は二つの開の逆像を順に取った像の式。`isPullback_of_pairOpenCover` は、各対の同じ逆像の交叉上の局所 Cartesian 四角形を二つの因子の開被覆で貼り合わせる法則。同じ像の開埋め込みの同型と、既存の開被覆による判定を二回用いる。

`DegreeOneStandardOpen`（53行）：`exists_degreeOne_homogeneous_lift` は全射な次数一評価の斉次原像の存在。`degreeOne_irrelevant_le_span` は表示の生成元のイデアルに irrelevant ideal が入ること。graded な評価の次数分解との可換性から導き、被覆条件を追加仮定にしない。

`SegreProjectivePullback`（76行）：`isPullback_segreProjectiveProjections` は実際の二つの Segre 射影と、二つの因子の元のスカラー構造射が Spec R 上の Cartesian 四角形を与えること。前記の被覆・制限式・逆像・局所 Cartesian 四角形を同じ図式で貼り合わせる。平坦性・Noether 性・非零の座標の仮定はない。

`SegreProjectiveStructureMap`（77行）：`segreLeftProjection_structureMap`・`segreRightProjection_structureMap` は各射影と因子の構造射の合成が Segre の元の構造射に一致すること。全標準開上で R 上の代数写像の可換性を使う。

四本とも単独検証、下書きと本体のソース完全一致、対象と入口だけのビルド5,124ジョブ、小監査30宣言（3・2・12・13）・標準三公理のみ、終了状態0。開被覆の添字は書き換える前に元の型で明示した。`PairOpenCoverPullback` の貼り合わせと Segre の大域の三法則で局所的な backward.isDefEq.respectTransparency false を用い、他の既存ファイルの設定は変えていない。追加公理・sorry・既存宣言の型変更・資源制限の引き上げ・200行超の宣言はない。ログ `2g-pair-open-cover-pullback-check-2.log`・`2g-degree-one-standard-open-check-2.log`・`2g-segre-projective-pullback-check.log`・`2g-segre-projective-structure-check.log`・`2g-segre-projective-pullback-and-structure-native.log`・`2g-segre-projective-pullback-audit.log`。共有鍵 --class impl --wait 3600、待ちは一つ。root・下流全ビルド・全体監査なし。

今回4モジュール284行＋入口4行。2g-2 本体3,624行・入口込み3,679行、小監査410宣言・標準三公理のみ。Segre の大域のファイバー積と元の構造射の比較まで到達。有限ファイバー冪の射影表示、G4、G5 は未完。`FiniteFiberPowerSucc.lean` の58行の下書きは単独検証まで成功したが、本体の対象ビルド・小監査前なので今回のコミットに含めない。全体の見込み約5,500〜12,000行・外枠16,000行は不変。停止点2g-2ではない。

一覧：済み0／全体3（うち追加0）。


S04 の有限冪の単位の法則の分割（着手前、既存の wide pullback の単位の内数、40〜90行）：`finiteFiberPowerZeroIso f` は、Fin 1 で添字づけた f:X→S の一個の wide pullback と X の同型。`finiteFiberPowerZeroIso_hom_base` は、その射影の同型と f の合成が同じ base に等しいこと。既存の π・lift の法則と Fin 1 の一意性だけを使う。有限冪の表示の帰納の最初を、既存の Čech nerve の零次の同じ対象へ合わせる法則である。


S04 の有限な次数一表示の証人の束ね直し（着手前、既存の表示と係数移送の内数、80〜180行）：`DegreeOneProjectiveModel f` は、有限で順序のある添字、実際の R 代数 A、次数成分 G、次数一の全射評価、Y≅Proj G の同型、同型が元の射 f:Y→Spec R を保つ式を一つにまとめるデータ。存在を仮定する新しい命題を最終定理へ足さず、既に作った Rees・Segre の実際の証人を渡すための束ね直しである。`degreeOneProjectiveModelOfProj` は同じ Proj の表示の証人、`DegreeOneProjectiveModel.ofIso` は元の同型による移送の法則。後続で実際の pullback と有限冪にこの同じ表示を帰納する。多項式環上の作用・有限加群性・irrelevant ideal の条件は、証人の全射評価から導き、追加の仮定として残さない。


S04 の表示の pullback での合成則（着手前、既存の Segre の比較と表示の移送の内数、100〜220行）：`DegreeOneProjectiveModel.pullback` は、元の二つの射 f:X→Spec R・g:Y→Spec R の有限な次数一表示の証人から、実際の `pullback.fst f g ≫ f` の同じ種類の証人を返す。座標環は既に作った SegreCoordinateRing、次数分解・全射評価・大域の Cartesian 四角形も既存のもの。二つの同型を通して同じ図式を移送し、基底への射は構造射の合成則で照合する。添字の有限積に順序を選ぶだけで、元の環や射に条件を追加しない。この合成則を既存の有限冪の単位・後続段の法則へ渡す。


S04 の表示から 2f の係数構造への移送の法則の分割（着手前、既存の評価とスカラー移送の内数、80〜180行）：`degreeOnePolynomialAlgebra a` は元の評価による同じ多項式作用。`degreeOnePolynomial_scalarTower` は R 作用との塔、`degreeOnePolynomial_finite a hs` は全射評価からの有限加群性、`degreeOnePolynomial_gradedSMul G a ha` は次数を保つ作用。`degreeOne_projective_cech_data` はこれらと前記の irrelevant ideal の条件を同じ評価について同時に返す。既存の Rees の計算の一般形として、モデルの証人の全射性から導き、2f の入力を仮定に置き換えない。


## G3・S04：既存の有限ファイバー冪の単位と後続段の四角形

`FiniteFiberPowerSucc`（58行）：`isPullback_finiteFiberPowerSucc` は、既存の n+2 個の wide pullback の、末尾の n+1 個への lift と先頭への π が、同じ S 上の Cartesian 四角形になること。既存の lift・π・base の式と普遍性で証明し、新しい再帰的な別のファイバー冪を作っていない。

`FiniteFiberPowerUnit`（39行）：`finiteFiberPowerZeroIso` は Fin 1 で添字づけた一個の冪と元の X の同型。`finiteFiberPowerZeroIso_hom_base` は同じ基底への射を保つ式。

単独検証、下書きと本体のソース完全一致、対象と入口のビルド5,126ジョブ、小監査12宣言（3・9）・標準三公理のみ、終了状態0。一般の有限極限を持つ圏での普遍性の法則であり、スキームに余分な性質を仮定しない。既定の透明性・資源制限で通る。追加公理・sorry・既存の型変更・200行超の宣言なし。ログ `2g-finite-fiber-power-succ-check-2.log`・`2g-finite-fiber-power-unit-check.log`・`2g-finite-fiber-powers-native.log`・`2g-finite-fiber-powers-audit.log`。共有鍵 --class impl --wait 3600、待ちは一つ。root・下流全ビルド・全体監査なし。

今回2モジュール97行＋入口2行。2g-2 本体3,721行・入口込み3,778行、小監査422宣言・標準三公理のみ。有限冪の次数一表示の証人の帰納・2f への係数構造の接続と G4・G5 は未完。表示の証人とその pullback での合成、係数構造の一般形は未検証の下書きとして drafts に残し、今回のコミットには含めない。全体の見込み約5,500〜12,000行・外枠16,000行は不変。停止点2g-2ではない。

一覧：済み0／全体3（うち追加0）。


S04 の有限冪の表示の帰納（着手前、既存の表示の合成・単位・同型移送の内数、80〜180行）：`DegreeOneProjectiveModel.finiteFiberPower m n` は、元の射 f:X→Spec R の実際の表示 m から、既存の n+1 個の wide pullback の base の同じ種類の表示を返す。零次は一個の冪の同型、後続段は実際の pullback の表示とその Cartesian 四角形の同型を合成する。`DegreeOneProjectiveModel.cechTerm m n` の出口は `(Arrow.mk f).augmentedCechNerve.hom.app n` の表示そのもの。対象・基底への射は既存の Čech nerve のものを保つ。表示の各同型を通した自然性は既存の構造層の逆像と被覆比較を使い、最終の AugmentedRingCechExact の型を変えない。


S04 の Rees への戻しと 2f への入口（着手前、既存の Rees 表示・構造射・係数移送の内数、80〜170行）：`nonempty_affineBlowupDegreeOneProjectiveModel I hI` は、有限生成中心 I の実際の affineBlowupπ I の表示の証人の存在。既存の Fin n の Rees 全射評価と構造射の等式を渡す。`nonempty_affineBlowupCechTermModel I hI n` は、既存の増大 Čech nerve の n 次の射そのものの同じ証人の存在。`DegreeOneProjectiveModel.projectiveCechData m` は、選んだ表示の評価から 2f の IsScalarTower・GradedSMul・Module.Finite・irrelevant ideal の条件を同時に返す。表示の存在・多項式環上の有限性を最終の降下定理に仮定として残さない。Noether 基底上では中心の有限生成性は既存の Noether 性から得る。


## G3・S04：表示の実際の証人と pullback の合成、2f の入力

`DegreeOneProjectiveModel`（67行）：`DegreeOneProjectiveModel f` は有限で順序のある添字、元の R 代数・次数成分・全射な次数一評価、元の Y と Proj の同型、その同型が f を保つ式を束ねたもの。`degreeOneProjectiveModelOfProj` は同じ Proj の表示を束ねる単位。`DegreeOneProjectiveModel.ofIso` は元の同型による表示の移送。存在を最終の定理の新しい仮定にしていない。

`DegreeOnePolynomialAction`（66行）：`degreeOnePolynomialAlgebra` は元の評価による多項式作用。`degreeOnePolynomial_scalarTower` は R 作用との塔。`degreeOnePolynomial_finite` は全射評価からの有限加群性。`degreeOnePolynomial_gradedSMul` は同じ作用の次数保存。`degreeOne_projective_cech_data` はこれらと irrelevant ideal の条件を同じ評価から返す。

`DegreeOneProjectiveModelPullback`（61行）：`DegreeOneProjectiveModel.pullback` は、実際の二つの射の表示を、実際の pullback の base の表示へ合成する。座標環・全射評価・次数分解は既存の Segre のもの、同型は構成済みの Cartesian 四角形のもの。

`DegreeOneProjectiveModelCechData`（30行）：`DegreeOneProjectiveModel.projectiveCechData` は同じ証人から 2f の係数構造・有限性・標準開の被覆条件を供給する。

単独検証、下書きと本体のソース完全一致、対象と入口のビルド5,130ジョブ、小監査59宣言（35・5・18・1）・標準三公理のみ、終了状態0。依存する表示の型の中の f を直接書き換えず、同型の合成の等式を取り出して移送した。係数作用の新規二宣言は命題なので theorem とし、証明中の letI の警告も整理後に再検証・対象ビルドを行った。pullback の合成だけに局所的な backward.isDefEq.respectTransparency false を用いる。追加公理・sorry・既存宣言の型変更・資源制限の引き上げ・200行超の宣言はない。ログ `2g-degree-one-projective-model-check-2.log`・`2g-degree-one-polynomial-action-check-2.log`・`2g-degree-one-model-pullback-check-2.log`・`2g-degree-one-model-cech-data-check.log`・`2g-degree-one-model-pullback-and-data-native.log`・`2g-degree-one-projective-models-audit.log`。共有鍵 --class impl --wait 3600、待ちは一つ。root・下流全ビルド・全体監査なし。

今回4モジュール224行＋入口4行。2g-2 本体3,945行・入口込み4,006行、小監査481宣言・標準三公理のみ。既存の Čech nerve の各項への表示の帰納の43行の下書きは単独検証まで成功したが、本体ビルド・監査前なので今回のコミットには含めない。Rees の実際の blowup の各 Čech 項への特殊化と G4・G5 は未完。全体の見込み約5,500〜12,000行・外枠16,000行は不変。停止点2g-2ではない。

一覧：済み0／全体3（うち追加0）。


S04 の一般の blowup のアフィン開への移送の法則の分割（着手前、既存のアフィン開比較の内数、60〜140行）：`isPullback_blowupAffineOpenMap` は、既存の blowupAffineOpenMap と affineBlowupπ が、一般の blowupπ のアフィン開 j:Spec A→X への実際の pullback を与えること。既存の開埋め込み・像の式・基底への合成式を使う。`nonempty_blowupAffinePullbackProjectiveModel` は対応する中心の有限生成性から、この既存の pullback.snd の次数一表示を返す。`nonempty_blowupAffinePullbackCechTermModel` はその増大 Čech nerve の各項の同じ表示の存在。Stacks 080Y に対応する既存の比較を証人の同型移送に渡す法則で、新しい近似モデルの存在を追加しない。


G4 の表示の同型による係数移送の法則（着手前、既存の逆像・係数図式の同型の内数、80〜160行）：`schemeStructureRingPullbackCoefficient_isIso` はスキームの同型に沿う既存の切断環の引き戻しが係数図式の同型であること。`schemeStructurePerfectPullbackCoefficient_isIso` は同じ Frobenius 順極限後の係数図式の同型。`schemeStructurePerfectCechPullbackMap_isIso` は元の被覆 U とその逆像被覆について、既存の引き戻しの Čech 複体の射そのものが同型になること。原環・実際の app・既存の逆像の比較を保ち、導来関手の H との比較は追加しない。これにより表示の同型で射影版の計算を実際の構造層へ移し、後続で同じ逆像の射と細分の自然性を使う。


## G3・S04：実際の blowup の既存の Čech 各項の表示、G3 の区切り

`DegreeOneProjectiveModelFiberPowers`（43行）：`DegreeOneProjectiveModel.finiteFiberPower` は、既存の wide pullback の base に次数一表示を帰納する。`DegreeOneProjectiveModel.cechTerm` の出口は `(Arrow.mk f).augmentedCechNerve.hom.app n` の表示そのもの。

`ReesFiniteFiberPowerModel`（35行）：`nonempty_affineBlowupDegreeOneProjectiveModel` は、有限生成中心から実際の affineBlowupπ の表示の存在を供給。`nonempty_affineBlowupCechTermModel` は、その既存の増大 Čech nerve の各項の表示の存在。表示の存在は追加仮定ではなく既存の Rees 全射評価から導いた。

`BlowupAffineProjectiveModel`（47行）：`isPullback_blowupAffineOpenMap` は一般の blowup の既存のアフィン開比較が実際の Cartesian 四角形であること。`nonempty_blowupAffinePullbackProjectiveModel` は元の pullback.snd の表示の存在。`nonempty_blowupAffinePullbackCechTermModel` はその既存の Čech nerve の各項の表示の存在。入力の有限生成性は対応する環イデアルだけで、Noether 基底上では既存の Noether 性から得る。

三本とも単独検証、下書きと本体のソース完全一致、対象と入口のビルド5,133ジョブ、小監査17宣言（12・2・3）・標準三公理のみ、終了状態0。既定の透明性・資源制限で通る。追加公理・sorry・既存の型変更・200行超の宣言なし。ログ `2g-degree-one-model-fiber-powers-check-2.log`・`2g-rees-finite-fiber-power-model-check.log`・`2g-blowup-affine-projective-model-check.log`・`2g-blowup-cech-term-models-native.log`・`2g-blowup-cech-term-models-audit.log`。共有鍵 --class impl --wait 3600、待ちは一つ。root・下流全ビルド・全体監査なし。

今回3モジュール125行＋入口3行。2g-2 本体4,070行・入口込み4,134行、小監査498宣言・標準三公理のみ。2g-1 報告56ea849a3 の木と現在の本体のファイルを独立に比較しても、新規64モジュール・本体4,070行・入口64行と一致した。累計の宣言数はこれまでの各束の所有元による小監査の和であり、今回64モジュールの再監査は行っていない。

**G3 は済み**。一般の固有全射の有限レベルの存在、Rees の実際の全射表示、任意の係数移送の Proj の pullback、Segre のチャート・大域の実際のファイバー積、既存の Čech 各項への有限表示の帰納、一般の blowup のアフィン開の比較と 2f の係数入力まで揃った。

G4 では、一般の ProperInductiveLevel の証人の r が射影的であるとは仮定しない。射影版の F8 を当てる箇所では、2d が返す実際の blowup を保持して Noether 基底の閉集合上の帰納を進める。その局所射・各 Čech 項には前記の同じ表示を渡す。表示の同型による構造層の Čech 複体の移送の下書きはまだ未検証で、今回のコミットには含めない。G4・G5 と停止点2g-2は未完。残りの見込みは G4 が約1,300〜2,800行、G5 が約1,000〜2,500行に、同型・被覆の整合性の余裕を含め、全体の見込み約5,500〜12,000行・外枠16,000行を維持する。

一覧：済み1／全体3（うち追加0）。


G4 の忠実平坦なアフィン射と Frobenius 順極限（着手前、既承認の fppf の完全性の証明分割、100〜220行）：`affineRingCechExact_of_faithfullyFlat B` は忠実平坦な Under A の実際の増大 conerve の完全性。B1 の忠実平坦底変換による反映と、恒等射 B→B に沿う底変換の切断を用い、Amitsur の議論を再実装しない。`frobeniusArrowStep`・`frobeniusArrowDiagram` は既存の Frobenius 環写像を元の矢印の可換な反復図式として束ねる。`frobeniusArrowSmallDiagram` は同じ自然数系を AsSmall ℕ の同値で宇宙を合わせる。`isCechExact_frobeniusArrowColimit_of_faithfullyFlat` はその実際の Arrow の colimit の Čech 完全性。B1 の isCechExact_colimit を使う。各次数の環の Frobenius 順極限との自然な比較はこの完全性そのものとは別に接続し、最終の型をこの colimit の型へ置き換えない。


上記の忠実平坦な場合の底変換・標数の法則（着手前、同じ束の内数、40〜100行）：`underPrimeCast_eq_zero` は元の基底の p=0 を Under の射で押し出す式。Frobenius 余極限の完全性の入力は hA だけとし、hB はこの式で供給する。`affineRingCechExact_baseChange_of_faithfullyFlat` は任意の A 代数 D への底変換後の完全性で、D の平坦性を仮定しない。元の忠実平坦性の底変換の既存の instance を使う。`isCechExact_frobeniusArrowBaseChangeColimit_of_faithfullyFlat` は同じ底変換後の反復 Frobenius 系の余極限の完全性。各段の Frobenius の平坦性は仮定しない。


## G4：表示の同型による構造層の Čech の同型移送

`SchemeStructurePerfectCechIso`（58行）：`schemeStructureRingPullbackCoefficient_isIso` は同型の元の app を切断環の係数図式の同型にする。`schemeStructurePerfectPullbackCoefficient_isIso` は同じ Frobenius 順極限の係数図式の射そのものの同型性。`schemeStructurePerfectCechPullbackMap_isIso` は元の被覆とその逆像について、既存の Čech 引き戻しの射そのものが複体の同型であること。原環の app と逆像の射を保つ。

単独検証、下書きと本体のソース完全一致、対象と入口・必要な既存の B1 の二依存モジュールのビルド5,150ジョブ、小監査3宣言・標準三公理のみ、終了状態0。整数係数の型と任意の宇宙の切断加群を扱うため、既存の係数写像と fullCechComplexFunctor を直接用い、既存の API の宇宙や型は変更していない。新規三宣言の haveI の警告を整理後も単独検証・対象ビルドが成功。最後の複体の同型性だけに局所的な backward.isDefEq.respectTransparency false を使用。追加公理・sorry・資源制限の引き上げ・200行超の宣言なし。ログ `2g-scheme-perfect-cech-iso-check-4.log`・`2g-cech-iso-and-b1-dependencies-native.log`・`2g-scheme-perfect-cech-iso-audit.log`。共有鍵 --class impl --wait 3600、待ちは一つ。root・下流全ビルド・全体監査なし。

今回1モジュール58行＋入口1行。2g-2 本体4,128行・入口込み4,193行、小監査501宣言・標準三公理のみ。G4 の同型移送の最初の法則までで、fppf の完全性・射影四角形からの Noether 帰納・二重 Čech の判定、G5 は未完。忠実平坦な場合の元の conerve と Frobenius 反復系の余極限の完全性の下書きは単独検証まで成功し、任意の底変換・標数の押し出しを追加して再検証中。これらは今回のコミットに含めない。全体の見込み約5,500〜12,000行・外枠16,000行は不変。停止点2g-2ではない。

一覧：済み1／全体3（うち追加0）。


忠実平坦な底変換の係数移送の法則の補足（着手前、上の同じ束の内数、10〜30行）：`faithfullyFlat_mkUnder` は、元の R 代数 S の忠実平坦性を、同じ algebraMap から作った mkUnder R S の加群構造へ移す。`toAlgebra_algebraMap` による同じ代数構造の等式を使い、テンソル積の通常の加群構造と Under の射から復元した構造を照合する。新しい平坦性の仮定や存在は追加しない。


G4 の共通細分の cone の完全性の法則（着手前、既存の cone の準同型性と被覆比較の内数、80〜180行）：`cechRefinementCone_acyclic_of_quasiIso` は、非負次数の複体の実際の射 f:A→B と全次数の QuasiIsoAt f q から、既存の cechRefinementCone A B f の Acyclic を返す。既存の cechRefinementCone_cycle_boundary_of_homology と cechCycles_boundary_of_homology_injective を使い、零次の単射性と正次数の完全性を揃える。基底環と加群の宇宙は独立。これは既存の cone の完全性から準同型性を得る法則の逆向きで、導来関手の層の H との比較を追加しない。後続で実際の細分の cochain map と可換性を持つ CechAugmentedSquare.Map を使い、F8 の全複体の被覆による比較へ接続する。H の同型だけから四角形の可換性を仮定するものではない。


## G4：忠実平坦なアフィン射と、その任意の底変換の Frobenius 反復系

`AffineFrobeniusCechExact`（103行）：`affineRingCechExact_of_faithfullyFlat` は B1 の底変換による反映と恒等射での切断から、元の増大 conerve の完全性を得る。`faithfullyFlat_mkUnder` は同じ algebraMap から Under が復元する加群構造への忠実平坦性の移送。`affineRingCechExact_baseChange_of_faithfullyFlat` は任意の A 代数への底変換後の完全性で、底変換先の平坦性を仮定しない。`underPrimeCast_eq_zero` は元の基底の標数条件を押し出す式。

`frobeniusArrowStep` は既存の二つの Frobenius 環写像を元の矢印の可換な自己射にする。`frobeniusArrowDiagram` はその同じ矢印の反復系。`frobeniusArrowSmallDiagram` は同じ自然数系を AsSmall の同値で環と同じ宇宙へ移す。`isCechExact_frobeniusArrowColimit_of_faithfullyFlat` は実際の Arrow の余極限の完全性を B1 の filtered 余極限から得る。`isCechExact_frobeniusArrowBaseChangeColimit_of_faithfullyFlat` は任意の底変換後の同じ反復系の余極限の完全性。

単独検証、下書きと本体のソース完全一致、対象と入口のビルド5,151ジョブ、小監査12宣言・標準三公理のみ、終了状態0。通常のテンソル積と Under の構造射から復元した加群構造は toAlgebra_algebraMap で照合した。元の忠実平坦性を各段で使い、一般の Frobenius の平坦性は仮定していない。標数条件は元の基底の p=0 だけから供給する。追加公理・sorry・既存の型変更・透明性や資源制限の変更・200行超の宣言なし。ログ `2g-affine-frobenius-cech-exact-check-5.log`・`2g-affine-frobenius-cech-native.log`・`2g-affine-frobenius-cech-audit.log`。共有鍵 --class impl --wait 3600、待ちは一つ。root・下流全ビルド・全体監査なし。

今回1モジュール103行＋入口1行。2g-2 本体4,231行・入口込み4,297行、小監査513宣言・標準三公理のみ。完全性の出口はこの実際の反復系の Arrow の colimit であり、最終型をこれに置き換えるものではない。各次数の実際の Frobenius 係数との自然な比較、一般の fppf の二重 Čech、射影四角形からの Noether 帰納と G5 は未完。cone の準同型性からの完全性の下書きはまだ未検証で、今回のコミットには含めない。全体の見込み約5,500〜12,000行・外枠16,000行は不変。停止点2g-2ではない。

一覧：済み1／全体3（うち追加0）。


G4 の二重 cone の交換の成分の法則（着手前、既存の cone の合成・自然性の内数、80〜180行）：f:A→B・g:A′→B′・a:A→A′・b:B→B′ に対し、`cechDoubleConeSwapTerm` は、cone の射 K(f)→K(g) の cone の各項と、交換した K(a)→K(b) の cone の各項の線形写像。零次は恒等、一次は `(a′,(b,a)) ↦ (-b,(-a′,a))`、以後は `((b′,a′),(b,a)) ↦ ((-b′,-b),(-a′,a))`。`cechDoubleConeSwapTerm_involutive` は同じ交換を二回行うと恒等になる法則。微分との可換性と複体の同型は、この成分の後に別の法則として検証する。四角形の可換性を仮定した実際の cone の射を後続で使い、単に H の同型を並べる比較は行わない。


G4 の二重 cone の交換の微分と複体の法則（着手前、前記の同じ交換の内数、100〜220行）：可換な実際の四角形 h:f≫b=a≫g に対し、`cechDoubleConeSwapTerm_differential` は前記の符号付き成分が二つの cone の微分と可換であること。`cechDoubleConeSwapMap` はその余鎖写像、`cechDoubleConeSwapIso` は同じ交換を逆に用いた複体の同型。二重 cone は、`K(K(a,b;h):K(f)→K(g))` と `K(K(f,g;h.symm):K(a)→K(b))` の二つで、K は既存の cechRefinementCone。各項の恒等則を同じ実際の写像へ渡す。零次・一次・以後で符号を個別に照合する。ここでは全複体の完全性の移送はまだ主張しない。


## G4：各次数の H の同型から既存の cone の完全性

`CechConeQuasiIsoAcyclic`（62行）：`cechRefinementCone_acyclic_of_quasiIso` は、元の射 f:A→B が全次数で QuasiIsoAt なら、既存の明示的な cechRefinementCone A B f が Acyclic になること。既存のサイクルの境界への反映・持ち上げの法則を使い、零次の単射性と正次数の完全性を得る。係数環と加群の宇宙は独立なので、整数係数と大きい宇宙の切断にも使える。

単独検証、下書きと本体のソース完全一致、対象と入口のビルド5,152ジョブ、小監査1宣言・標準三公理のみ、終了状態0。短複体の項と元の複体の項を明示し、最後の零次の等式は型を保った等式の合成で渡した。既定の透明性・資源制限で通る。追加公理・sorry・既存の型変更・200行超の宣言なし。ログ `2g-cech-cone-quasi-iso-acyclic-check-3.log`・`2g-cech-cone-quasi-iso-native.log`・`2g-cech-cone-quasi-iso-audit.log`。共有鍵 --class impl --wait 3600、待ちは一つ。root・下流全ビルド・全体監査なし。

今回1モジュール62行＋入口1行。2g-2 本体4,293行・入口込み4,360行、小監査514宣言・標準三公理のみ。二重 cone の交換の成分・微分との可換性・四角形の増大全複体の比較は次の下書きで、まだ検証前。これらを今回のコミットには含めない。各次数の実際の Frobenius 係数との自然な比較、一般の fppf の二重 Čech、射影四角形からの Noether 帰納と G5 は未完。全体の見込み約5,500〜12,000行・外枠16,000行は不変。停止点2g-2ではない。

一覧：済み1／全体3（うち追加0）。


## G4：二重 cone の交換の成分と二回の交換

`CechDoubleConeSwapTerm`（71行）：`cechDoubleConeSwapTerm` は元の四つの余鎖写像に対する既存の二重 cone の各項を、前記の符号付きの直積の写像で交換する。`cechDoubleConeSwapTerm_involutive` は同じ交換を逆向きに二回適用すると恒等になること。零次・一次・以後を分け、直積の線形性と成分の恒等則を明示した。

単独検証、下書きと本体のソース完全一致、対象と入口のビルド5,153ジョブ、小監査8宣言・標準三公理のみ、終了状態0。ログ `2g-cech-double-cone-swap-term-check-5.log`・`2g-cech-double-cone-swap-term-native.log`・`2g-cech-double-cone-swap-term-audit.log`。新規モジュールの警告なし（入口は既存の依存の警告を再生）。追加公理・sorry・既存の型変更・透明性や資源制限の変更・200行超の宣言なし。共有鍵 --class impl --wait 3600、待ちは一つ。root・下流全ビルド・全体監査なし。

今回1モジュール71行＋入口1行。2g-2 本体4,364行・入口込み4,432行、小監査522宣言・標準三公理のみ。微分との可換性と複体の同型の下書きはまだ未検証で、今回のコミットには含めない。G4・G5 の残りと見込み約5,500〜12,000行・外枠16,000行は不変。停止点2g-2ではない。

一覧：済み1／全体3（うち追加0）。


G4 の明示的な複体の完全性の反映の法則（着手前、既存の CochainComplex.of の完全性判定の逆向き、40〜100行）：`cochainComplexOf_injective_exact_of_acyclic X d hdd hK` は、`hK : (CochainComplex.of X d hdd).Acyclic` から `Function.Injective (d 0).hom ∧ ∀ n, Function.Exact (d n).hom (d (n+1)).hom` を取り出す。既存の cochainComplexOf_acyclic_of_injective_exact と同じ型・宇宙で、短複体の完全性を各次数で読む法則。増大全複体と cone の既存の証明分割に使用する。


G4 の二重 cone の交換による完全性の法則（着手前、前記の四角形の比較の証明分割、35〜80行）：`cechRefinementConeMap_cone_acyclic f g a b h ha hb` は `h:f≫b=a≫g`・`ha:(cechRefinementCone A A′ a).Acyclic`・`hb:(cechRefinementCone B B′ b).Acyclic` から、実際の `cechRefinementConeMap a b h : K(f)→K(g)` の cone の Acyclic を返す。交換先の二複体の完全性からその射の QuasiIsoAt を得て、既存の cone の完全性の法則と交換の同型で戻す。元の四角形の射を保持し、まだ増大項の比較を主張しない。


G4 の零次項拡張の比較の法則（着手前、既存の拡張の係数移送の内数、80〜180行）：`cechZeroTermExtensionMap_cone_acyclic α q hα hq` は `hα:(cechRefinementCone C C′ α).Acyclic` と `hq:Function.Bijective q` から、既存の `cechZeroTermExtensionMap α q` の cone の完全性を返す。零次で q の単射性、一次の境界で q の全射性を使い、それ以後は元の cone の完全性をそのまま読む。新しい被覆や H の定義は導入しない。


## G4：明示的な複体の完全性から微分の完全性の反映

`CochainComplexOfExactnessReflection`（46行）：`cochainComplexOf_injective_exact_of_acyclic` は既存の CochainComplex.of の Acyclic から、最初の微分の単射性と各隣接微分の Function.Exact を取り出す。既存の逆向きの判定と同じ型で、係数環と加群の宇宙は独立。零次と正次数の短複体の完全性を直接読む。

単独検証、下書きと本体のソース完全一致、対象と入口のビルド5,154ジョブ、小監査1宣言・標準三公理のみ、終了状態0。ログ `2g-cochain-exactness-reflection-check-1.log`・`2g-cochain-exactness-reflection-native.log`・`2g-cochain-exactness-reflection-audit.log`。追加公理・sorry・既存の型変更・透明性や資源制限の変更・200行超の宣言なし。共有鍵 --class impl --wait 3600、待ちは一つ。root・下流全ビルド・全体監査なし。

今回1モジュール46行＋入口1行。2g-2 本体4,410行・入口込み4,479行、小監査523宣言・標準三公理のみ。二重 cone の交換の微分・完全性、零次項の拡張と増大項の比較は未検証の下書きで、本体には含めない。G4・G5 の残りと見込み約5,500〜12,000行・外枠16,000行は不変。停止点2g-2ではない。

一覧：済み1／全体3（うち追加0）。


G4 の増大 cone の完全性の判定の法則（着手前、既存の増大全複体の証明分割、45〜100行）：`augmentedCechCone_acyclic_iff_injective_exact A B f Z a hc` は既存の増大全複体の Acyclic と、a の単射性・a と cone の最初の微分の Function.Exact・cone の隣接微分全ての Function.Exact の同値。既存の CochainComplex.of の両向きの判定を、増大項・零次項・以後に分けて読む。増大項の比較を元の可換四角形の写像で示す際の法則で、新しい全複体や H の定義を導入しない。


## G4：二重 cone の交換の複体の同型と零次項拡張

`CechDoubleConeSwap`（103行）：`cechDoubleConeSwapTerm_differential` は、実際の可換四角 h:f≫b=a≫g に対し、前記の交換の成分と二つの cone の微分が可換であること。`cechDoubleConeSwapMap` はその実際の余鎖写像、`cechDoubleConeSwapIso` は同じ交換を逆に用いた複体の同型。零次・一次・それ以後を分け、可変次数の微分は CochainComplex.of_d を明示して読んだ。

`CechZeroTermExtensionConeAcyclic`（95行）：`cechZeroTermExtensionMap_cone_acyclic` は元の比較の cone の完全性と追加係数の全単射性から、実際の零次項拡張の比較の cone の完全性を返す。追加係数の単射性を零次で、全射性を一次の境界で使い、それ以後は元の cone の微分の完全性へ戻す。

各単独検証、下書きと本体のソース完全一致、対象と入口のビルド5,155・5,156ジョブ、所有元による各小監査6・30宣言（計36）・標準三公理のみ、終了状態0。ログ `2g-zero-term-extension-cone-check-4.log`・`2g-zero-term-extension-cone-native.log`・`2g-zero-term-extension-cone-audit.log` と `2g-cech-double-cone-swap-check-10.log`・`2g-cech-double-cone-swap-native.log`・`2g-cech-double-cone-swap-audit.log`。交換の congr の後の `<;>` について軽微なスタイル警告が2件ある。交換の微分の法則・余鎖写像の構成、および零次項拡張の完全性に限り、既存の cone と同じ局所的な backward.isDefEq.respectTransparency false を使う。追加公理・sorry・既存の型変更・資源制限の引き上げ・200行超の宣言なし。共有鍵 --class impl --wait 3600、待ちは一つ。対象ビルドと小監査は別の鍵の枠で行った。root・下流全ビルド・全体監査なし。

今回2モジュール198行＋入口2行。2g-2 本体4,608行・入口込み4,679行、小監査559宣言・標準三公理のみ。交換による比較の cone の完全性は単独検証まで成功しているが、本体への登録と対象ビルド・監査は次の束。増大項を含めた全複体の比較と、G4・G5 の幾何的な接続は未完。見込み約5,500〜12,000行・外枠16,000行は不変。停止点2g-2ではない。

一覧：済み1／全体3（うち追加0）。


G4 の増大項まで含む比較の法則（着手前、既存の全複体の共通細分による移送の内数、150〜280行、必要なら正向きと逆向きを分割）：f:A→B・g:A′→B′、a:Z→A⁰・a′:Z′→A′⁰ とそれぞれの cone の零次での閉性、実際の k:K(f)→K(g)、ζ:Z→Z′ に対し、`haug:(k.f 0).hom.comp a=a′.comp ζ`・`hk:(cechRefinementCone K(f) K(g) k).Acyclic`・`hζ:Function.Bijective ζ` から、`augmentedCechCone A B f Z a hc` と `augmentedCechCone A′ B′ g Z′ a′ hc′` の Acyclic の同値を示す。名前の案は正向き `augmentedCechCone_acyclic_of_comparison`・逆向き `augmentedCechCone_acyclic_reflected_of_comparison`・同値 `augmentedCechCone_acyclic_iff_of_comparison`。比較写像の cone のサイクルを持ち上げ、境界を反映して既存の微分の完全性判定へ渡す。正方向の零次は ζ の全射性と cone の最初の微分の単射性、逆方向の零次は ζ の単射性を使う。零次の完全性の反映では ζ の全射性も使う。層の導来 H の比較や別の全複体は導入しない。後続では k に実際の四角形の射からの coneMap を入れ、基底・中心・制限の自然性を保持する。


## G4：二重 cone の交換から比較の cone の完全性、および増大項の判定

`CechDoubleConeAcyclic`（36行）：`cechRefinementConeMap_cone_acyclic` は、元の可換四角の二辺の cone が完全なら、実際の cechRefinementConeMap の cone も完全になること。交換先の二つの完全な複体の間の射の QuasiIsoAt を Mathlib から得て、既存の cone の完全性と交換の同型を使う。元の射と可換性を保持する。

`AugmentedCechConeExactnessCriterion`（48行）：`augmentedCechCone_acyclic_iff_injective_exact` は、既存の増大 cone の完全性と、増大写像の単射性・増大写像と次の微分の完全性・その先の全ての隣接微分の完全性の同値。既存の CochainComplex.of の判定を増大項と以後に分けて読む。

各単独検証、下書きと本体のソース完全一致、対象と入口のビルド5,157・5,158ジョブ、小監査各1宣言（計2）・標準三公理のみ、終了状態0。ログ `2g-double-cone-acyclic-check-1.log`・`2g-double-cone-acyclic-native.log`・`2g-double-cone-acyclic-audit.log` と `2g-augmented-cone-criterion-check-1.log`・`2g-augmented-cone-criterion-native.log`・`2g-augmented-cone-criterion-audit.log`。前者は既定の透明性、後者の判定の法則にのみ局所的な backward.isDefEq.respectTransparency false を使用。追加公理・sorry・既存の型変更・資源制限の引き上げ・200行超の宣言なし。共有鍵 --class impl --wait 3600、待ちは一つ。対象ビルドと小監査は別の鍵の枠。root・下流全ビルド・全体監査なし。

今回2モジュール84行＋入口2行。2g-2 本体4,692行・入口込み4,765行、小監査561宣言・標準三公理のみ。増大項まで含む完全性の移送は、上記の型と紙の筋までで Lean は次の束。共通細分の実際の射の四角形への適用、Frobenius 係数との自然な比較、一般の fppf の二重 Čech、実際の blowup を保持した Noether 帰納と G5 は未完。全体の見込み約5,500〜12,000行・外枠16,000行は不変。停止点2g-2ではない。

一覧：済み1／全体3（うち追加0）。


上の増大項の移送の証明分割（着手前、同じ150〜280行の見込みの内数）：任意の非負次数の複体 C,D と実際の k:C→D、増大写像 a:Z→C⁰・a′:Z′→D⁰、全単射 ζ と k₀a=a′ζ に対し、`cochainAugmentation_exact_of_comparison` は source の `Injective a ∧ Exact a dC₀ ∧ ∀ n, Exact dCₙ dCₙ₊₁` を target の同じ性質へ移す。仮定は K(k) の Acyclic と a′ の閉性。これは新しい増大複体を定義せず、既存の augmentedCechCone の微分の判定へ渡す要素計算の分割である。逆方向も同じ型で、source の閉性を用いる。最終的には C=K(f), D=K(g) として前記の公開する増大 cone の比較へまとめる。


G4 の四角形の実際の射に沿う全複体の比較の法則（着手前、既存の CechAugmentedSquare.Map の自然性の内数、40〜100行）：`CechAugmentedSquare.Map.totalComplex_acyclic_iff_of_cones (m:Map s t)` は、`hC:(cechRefinementCone s.C t.C m.left).Acyclic`・`hE:(cechRefinementCone s.E t.E m.right).Acyclic` と m.base・m.center の全単射性から `s.totalComplex.Acyclic ↔ t.totalComplex.Acyclic` を返す。実際の零次項拡張の写像・差の写像の自然性・coneMap・増大写像の自然性を合成する。細分の H の同型を単に並べるのでなく、m の restriction・scalar・quotient・center_naturality の四条件を保持する。共通細分の実際の cochain map とその cone の完全性を供給する幾何への適用は、この法則の後に行う。


## G4：増大列の完全性の正向きの移送と反映

`CochainAugmentationComparisonForward`（93行）：`cochainAugmentation_exact_of_comparison` は、実際の比較 k:C→D の cone の完全性と増大項 ζ の全単射性・増大写像の自然性から、増大写像の単射性・零次の完全性・正次数の微分の完全性を source から target に移す。target の増大写像の閉性を明示し、正次数のサイクルは比較の cone の完全性で持ち上げる。

`CochainAugmentationComparisonBackward`（95行）：`cochainAugmentation_exact_reflected_of_comparison` は同じ入力で、source の増大写像の閉性を用い、target の増大列の完全性を反映する。零次のサイクルの差は cone の最初の微分の単射性で消し、正次数では `(-b,x)` の境界表示の第二成分から source の境界を得る。

各単独検証、下書きと本体のソース完全一致、対象と入口のビルド5,159・5,160ジョブ、小監査各1宣言（計2）・標準三公理のみ、終了状態0。ログ `2g-cochain-augmentation-forward-check-1.log`・`2g-cochain-augmentation-forward-native.log`・`2g-cochain-augmentation-forward-audit.log` と `2g-cochain-augmentation-backward-check-1.log`・`2g-cochain-augmentation-backward-native.log`・`2g-cochain-augmentation-backward-audit.log`。二つの法則に局所的な backward.isDefEq.respectTransparency false を使用。追加公理・sorry・既存の型変更・資源制限の引き上げ・200行超の宣言なし。共有鍵 --class impl --wait 3600、待ちは一つ。対象ビルドと小監査は別の枠。root・下流全ビルド・全体監査なし。

今回2モジュール188行＋入口2行。2g-2 本体4,880行・入口込み4,955行、小監査563宣言・標準三公理のみ。新しい増大複体は作っていない。元の augmentedCechCone の完全性の同値への接続と、四角形の実際の射への適用は下書きの検証中で、本体にはまだ含めない。G4・G5 は未完、見込み約5,500〜12,000行・外枠16,000行は不変。停止点2g-2ではない。

一覧：済み1／全体3（うち追加0）。


G4 の実際の有限アフィン細分の cone の完全性（着手前、既存の共通細分と H 比較の内数、50〜130行）：`schemeStructurePerfectCechRefinement_cone_acyclic Y p hp hY U V ρ hρ hU hV hcV` はアフィン対角の下、二つの有限アフィン族と target の被覆性から、実際の Frobenius 係数の `openCoverCechRefinementMap` の cone の Acyclic を返す。既存の schemeStructureFrobeniusCechRefinement_quasiIsoAt と cechRefinementCone_acyclic_of_quasiIso を使い、QuasiIsoAt を結論の追加仮定にしない。`schemeStructurePerfectCommonAffineCech_cones` は、二つの有限アフィン被覆の既存の schemeFiniteCommonOpenCover と既存の二つの射影の同じ写像に対し、両方の cone の完全性を同時に供給する。被覆性・アフィン性も既存の同じ共通被覆の法則から与える。


## G4：増大 cone・四角形の実際の射・有限共通アフィン細分

`AugmentedCechConeComparison`（108行）：`augmentedCechCone_acyclic_iff_of_comparison` は、元の二つの cone の実際の比較 k と自然な全単射の増大項、k の cone の完全性から、元の augmentedCechCone の完全性を両向きに移す。既存の微分を各次数で明示し、前束の要素計算を既存の完全性判定へ渡す。前束188行と合わせ、増大項の比較の実測は296行（当初見込み150〜280行から16行増）。外枠の変更はない。

`CechAugmentedSquareComparison`（44行）：`CechAugmentedSquare.Map.totalComplex_acyclic_iff_of_cones` は、四角形の実際の射 m の両辺の cone の完全性と基底・中心の全単射性から、二つの全複体の完全性の同値を返す。零次項拡張の写像、差の写像の自然性、coneMap と増大写像の自然性を同じ m で接続した。H の同型だけを並べた比較ではない。

`SchemePerfectCommonAffineCechCones`（68行）：`schemeStructurePerfectCechRefinement_cone_acyclic` はアフィン対角の下、有限アフィン細分の実際の Frobenius 係数の余鎖写像の cone が完全であること。`schemeStructurePerfectCommonAffineCech_cones` は二つの有限アフィン被覆から既存の同じ有限共通被覆への両写像について、cone の完全性を同時に供給する。被覆性・アフィン性は既存の同じ共通被覆から供給し、QuasiIsoAt や完全性を追加仮定にしていない。二つとも docstring に Čech 版と Stacks 30.2.6 の扱いを明記した。

各単独検証、下書きと本体のソース完全一致、対象と入口のビルド5,161・5,162・5,163ジョブ、所有元による小監査1・1・2宣言（計4）・標準三公理のみ、終了状態0。ログ `2g-augmented-cone-comparison-check-3.log`・`2g-augmented-cone-comparison-native.log`・`2g-augmented-cone-comparison-audit.log`、`2g-cech-square-comparison-check-1.log`・`2g-cech-square-comparison-native.log`・`2g-cech-square-comparison-audit.log`、`2g-scheme-perfect-common-affine-cones-check-1.log`・`2g-scheme-perfect-common-affine-cones-native.log`・`2g-scheme-perfect-common-affine-cones-audit.log`。前二つの法則は局所的な backward.isDefEq.respectTransparency false、共通細分の二法則は既定の透明性。共通細分の最初の法則には証明で使う Fintype 引数が型の表示に現れないという linter の警告がある。追加公理・sorry・既存の型変更・資源制限の引き上げ・200行超の宣言なし。共有鍵 --class impl --wait 3600、待ちは一つ。対象ビルドと小監査は別枠。root・下流全ビルド・全体監査なし。

今回3モジュール220行＋入口3行。2g-2 本体5,100行・入口込み5,178行、小監査567宣言・標準三公理のみ。増大項まで含めた四角形の比較の法則と、共通細分の実際の写像の cone の完全性まで。実際の閉中心の逆像被覆に沿う四角形への適用、Frobenius 係数とアフィン conerve の自然な比較、fppf の二重 Čech と実際の blowup を保持した Noether 帰納、G5 は未完。見込み約5,500〜12,000行・外枠16,000行は不変。停止点2g-2ではない。

一覧：済み1／全体3（うち追加0）。


### 次の増大写像の接続の前に：既存の6宣言だけの宇宙の一般化（着手前）

11-14 の条件付き承認に従い、⑥ が作った OpenCoverCechAugmentation の基礎部分だけで、`R : Type v` を `R : Type w` へ一般化し、係数の `ModuleCat.{v} R` はそのままにする。名前・引数名・仮定・結論の意味は保ち、旧来の w=v は特殊例として残す。OpenCoverCechAcyclic を使う injective・exact の二宣言は元の同宇宙の型のままで、別 section に置く。OpenCoverCechAcyclic 自体を一般化しない。

変更する型の一覧（X の宇宙 u、P の値の宇宙 v、R の宇宙 w は独立）：

- `openCoverCechZeroEquiv (P:(Opens X)ᵒᵖ ⥤ ModuleCat.{v} R) U : FullCechCochains (openCoverCechDiagram P U) 0 ≃ₗ[R] P.obj (op ⊤)`。
- `openCoverCechZeroEquiv_symm_apply P U x t`：上記の逆写像の値と、同じ前層の制限の値の等式。
- `openCoverCechAugmentation P U : P.obj (op ⊤) →ₗ[R] FullCechCochains (openCoverCechDiagram P U) 1`。
- `openCoverCechAugmentation_eq P U`：空タプルからの微分と上記の逆写像の合成が、同じ増大写像に等しい法則。
- `openCoverCechAugmentation_squared P U`：同じ増大写像と fullCechDifferential 1 の合成が零。
- `openCoverCechRefinement_augmentation P U V ρ hρ`：実際の細分の長さ一の写像と増大写像の合成が、V の増大写像に等しい法則。

各6名を識別子境界付きで `git grep -n -E` し、HEAD=d1e02db5b と math/bs-impl・math/inf-supply・math/inf-supply-b・math/bs-m15 の各枝について、AlgebraicGeometry の外の全追跡 Lean（BS・KST・drafts を含む）で利用0を確認した。各枝の固定コミット・コマンドの結果は `scheme-w1-2g-2-open-cover-augmentation-universe-usage.json` に保存。結果は全て終了状態1（該当なし）、標準エラー空。全追跡 Lean を対象とし、現行・旧配置の AlgebraicGeometry だけを除外した。未検証の作業用下書きは本体の利用側ではなく、この git grep には含めない。次に単独検証し、通ったら直接 importer と対象ビルド・所有元の小監査を行う。


G4 の実際の構造層の増大写像の係数移送の法則（着手前、既存の openCoverCechAugmentation と Frobenius 写像の合成の内数、50〜110行）：`schemeStructurePerfectCechAugmentation Y φ p hp hR hY U` は環の実際の大域スカラー φ:R→Γ(Y,⊤) の Frobenius 順極限と、既存の開被覆の増大写像との合成。`..._cycle` は Čech 微分との合成が零、`..._refinement` は実際の細分と増大写像の自然性、`..._apply` は各長さ一タプルで φ と実際の切断の制限の合成に同じ Frobenius 順極限を適用した式。射影・平坦性を仮定しない。これは別の増大複体の定義ではなく、F8 の既存の scalar・center の形を任意の有限アフィン細分へ渡す、同じ係数移送の略記と法則である。


宇宙を一般化する6宣言の型を、上の記述の補足として本体を省略して転記する。`P : (Opens X)ᵒᵖ ⥤ ModuleCat.{v} R`、`R : Type w`、U・V・ρ・hρ は元と同じ。

```lean
def openCoverCechZeroEquiv : FullCechCochains (openCoverCechDiagram P U) 0 ≃ₗ[R] P.obj (op ⊤)

theorem openCoverCechZeroEquiv_symm_apply (x : P.obj (op ⊤)) (t : Fin 0 → ι) :
    (openCoverCechZeroEquiv P U).symm x t =
      (P.map (homOfLE (show cechOpenIntersection U (cechTupleSupport t) ≤ ⊤ from le_top)).op).hom x

def openCoverCechAugmentation : P.obj (op ⊤) →ₗ[R]
    FullCechCochains (openCoverCechDiagram P U) 1

theorem openCoverCechAugmentation_eq :
    (fullCechDifferential (openCoverCechDiagram P U) 0).comp
      (openCoverCechZeroEquiv P U).symm.toLinearMap = openCoverCechAugmentation P U

theorem openCoverCechAugmentation_squared :
    (fullCechDifferential (openCoverCechDiagram P U) 1).comp
      (openCoverCechAugmentation P U) = 0

theorem openCoverCechRefinement_augmentation :
    (openCoverCechRefinementCochains P U V ρ hρ 1).comp
      (openCoverCechAugmentation P U) = openCoverCechAugmentation P V
```


G4 の引き戻しと増大写像の自然性（着手前、既存の係数移送・逆像被覆の自然性の内数、60〜150行）：`schemeCechCoefficientMap_augmentation η U` は同じ空間の係数前層の射について、fullCechComplexMap の零次と大域切断の増大写像の可換性。`schemeCechPreimageComplexIso_augmentation f Q U` は既存の逆像被覆の比較の零次と増大写像の可換性。`schemeCechPullbackMap_augmentation f Q η U` はその合成で、実際の引き戻しの零次と増大写像が η の全空間の成分と可換であること。係数環と加群の宇宙は元の SchemeCechPreimage と同じ独立な型。さらに Frobenius 係数の η と実際の大域スカラーを合成し、次の束で schemeStructurePerfectCechAugmentation の引き戻しとの可換性へ特殊化する。


## G4：開被覆の増大写像の6宣言の宇宙の一般化

`OpenCoverCechAugmentation` の上記6宣言だけで R の宇宙を独立にした。`openCoverCechAugmentation_injective`・`openCoverCechAugmentation_exact` は、元の同宇宙の型・引数名のまま別 section に置いた。OpenCoverCechAcyclic と最終の AugmentedRingCechExact は変更していない。既存の定義・証明を再利用し、増大写像を新しく実装し直していない。

単独検証と本体のソース完全一致、対象・直接 importer の OpenCoverCechRefinementConeExact と入口のビルド5,163ジョブ、小監査15宣言（所有元の非公開・生成宣言も全件）・標準三公理のみ、終了状態0。既存の利用側をこの型の一般化後に再ビルドし、元の使い方が通ることを確認した。外部利用の git grep の結果は前掲の固定した5枝の記録のとおり0。ログ `2g-open-cover-augmentation-universe-check-1.log`・`2g-open-cover-augmentation-universe-native.log`・`2g-open-cover-augmentation-universe-audit.log`。追加公理・sorry・仮定や結論の制限・Lean の資源制限の引き上げ・200行超の宣言なし。共有鍵 --class impl --wait 3600、待ちは一つ。ビルドは依存先の再検証を含めて30分以内の枠、監査は別枠。root・下流全ビルド・AlgebraicGeometry の全体監査なし。

既存1ファイルの差分は追加25行・削除14行（section の分割と既存二証明の位置の変更を含む）。新規78モジュール本体5,100行・入口込み5,178行は不変。外枠の計数には保守的にこの既存の追加25行も含め、本体5,125行・入口込み5,203行とする。新規モジュールの小監査567宣言に加え、今回の既存モジュール15宣言を別に監査した。G4・G5 は未完。見込み約5,500〜12,000行・外枠16,000行は不変。

一覧：済み1／全体3（うち追加0）。


G4 の Frobenius 係数への同じ自然性の特殊化（着手前、前記の引き戻しの法則の内数、35〜75行）：`schemeStructurePerfectCechPullbackMap_augmentation f φ ψ hψ p hp hR hY hX U` は実際の φ:R→Γ(Y,⊤)、ψ:R→Γ(X,⊤) と `hψ:ψ=f.appTop.hom.comp φ` から、`((schemeStructurePerfectCechPullbackMap f … U).f 0).hom.comp (schemeStructurePerfectCechAugmentation Y φ … U) = schemeStructurePerfectCechAugmentation X ψ … (fun i ↦ f ⁻¹ᵁ U i)` を返す。一般の引き戻しの増大写像の自然性と Frobenius の実際の環準同型の合成則を使う。平坦性を仮定せず、閉厚化にも同じ射を使う。


## G4：実際のスカラー・引き戻しと増大写像の自然性

`SchemeStructurePerfectCechAugmentation`（70行）：`schemeStructurePerfectCechAugmentation` は大域スカラー φ の実際の Frobenius 順極限を、既存の開被覆の増大写像へ合成したもの。`schemeStructurePerfectCechAugmentation_cycle` は Čech 微分の核に入ること。`schemeStructurePerfectCechAugmentation_refinement` は実際の被覆の細分が同じ増大写像を保つこと。`schemeStructurePerfectCechAugmentation_apply` は各長さ一タプルで、元のスカラーと実際の切断の制限の合成の Frobenius 順極限に一致する式。

`SchemeCechPullbackAugmentation`（64行）：`schemeCechCoefficientMap_augmentation` は係数前層の射の零次と大域切断の増大写像の可換性。`schemeCechPreimageComplexIso_augmentation` は既存の逆像被覆の比較と同じ増大写像の可換性。`schemeCechPullbackMap_augmentation` はそれらを合成し、既存の実際の Čech 引き戻しが係数の全空間の成分と増大写像の四角形を可換にすること。係数環と加群の宇宙は独立。

`SchemePerfectCechPullbackAugmentation`（43行）：`schemeStructurePerfectCechPullbackMap_augmentation` は、φ と ψ=f.appTop.comp φ が実際の大域スカラーであるとき、実際の構造層の Frobenius 係数の引き戻しが、上の二つの増大写像と可換であること。平坦性を仮定せず、閉中心にも同じ引き戻しの射を使える。

各単独検証、下書きと本体のソース完全一致、対象と入口のビルド5,165・5,166ジョブ、所有元による小監査11・3・1宣言（計15、非公開・生成宣言も含む）・標準三公理のみ、終了状態0。ログ `2g-scheme-perfect-cech-augmentation-check-2.log`・`2g-scheme-cech-pullback-augmentation-check-1.log`・`2g-perfect-and-pullback-augmentation-native.log`・`2g-scheme-perfect-cech-augmentation-audit.log`・`2g-scheme-cech-pullback-augmentation-audit.log`、および `2g-perfect-cech-pullback-augmentation-check-1.log`・`2g-perfect-cech-pullback-augmentation-native.log`・`2g-perfect-cech-pullback-augmentation-audit.log`。新規の定義の透明性は既定、自然性等の七法則には局所的な backward.isDefEq.respectTransparency false を用いた。追加公理・sorry・前節の6宣言以外の既存の型変更・資源制限の引き上げ・200行超の宣言なし。共有鍵 --class impl --wait 3600、待ちは一つ。対象ビルドと監査は別枠。root・下流全ビルド・全体監査なし。

今回3モジュール177行＋入口3行。2g-2 の新規81モジュール本体5,277行・入口込み5,358行。既存ファイルの追加25行を保守的に加えた外枠の計数は本体5,302行・入口込み5,383行。新規モジュールの小監査の累計582宣言に、前節の既存モジュール15宣言を別に監査した（累計は各束の所有元での小監査の和であり、今回全体を再監査した数ではない）。

G4 の増大項までの比較と、実際のスカラー・引き戻し・細分の自然性まで。閉中心の逆像被覆への四角形の適用、選んだ一つの被覆と nerve の整合性、Frobenius 係数とアフィン conerve の自然な比較、fppf の二重 Čech と実際の blowup を保持した Noether 帰納、G5 は未完。見込み約5,500〜12,000行・外枠16,000行は不変。次の幾何的な接続の紙の筋は作業メモに整理し、未検証の Lean の数学はこのコミットに含めない。停止点2g-2ではない。

一覧：済み1／全体3（うち追加0）。
