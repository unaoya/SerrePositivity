# SC-W1 2g-2：G3〜G5 の実装記録

**現在の外枠は20,000行（2026-11-16、ユーザーの明示承認）。以下の16,000・18,000行の記載は各時点の履歴。G3は済み、G4・G5は未完。18,000行の規模境界で停止後、同じ型・範囲での再開が承認された。**

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


G4 のスカラーの係数移送の合成則（着手前、既存の増大写像の合成の内数、25〜60行）：`schemeStructurePerfectCechAugmentation_comp Y φ q p hp hR hS hY U` は実際の q:R→S、φ:S→Γ(Y,⊤) に対し、`Aug(Y,φ.comp q,U) = Aug(Y,φ,U).comp (frobeniusDirectLimitMap … q).toAddMonoidHom.toIntLinearMap` を返す。既存の増大写像と Frobenius の環準同型の合成則だけを使う。

次の F8 の係数への適用（着手前、既存の CechAugmentedSquare への同じ係数・射の代入、50〜110行）：`schemeStructurePerfectCechSquare f q φ ψ hφ p hp hR hS hY hX U : CechAugmentedSquare.{u} ℤ`。既存の二つの複体に Y の U と X の f⁻¹U の実際の Frobenius 係数の Čech 複体を入れ、制限は schemeStructurePerfectCechPullbackMap。基底・中心は既存の R・S の Frobenius 順極限、スカラー・中心の増大写像は検証済みの schemeStructurePerfectCechAugmentation、商の辺は実際の q の Frobenius 順極限。`hφ:f.appTop.hom.comp φ=ψ.comp q` により可換性を、前束の引き戻しの自然性と上の合成則から供給する。これは新しい四角形の概念・全複体を定義するものでなく、F8 が使う既存の四角形の同じ構成への native な係数移送の明示。完全性はデータの仮定にしない。後続の比較の射・細分の単位と合成を同じ値で示し、既存の projectivePerfectCartesianAugmentedSquare から完全性を移す。


G4 の同じ四角形の細分の射（着手前、既存の CechAugmentedSquare.Map と細分の自然性の内数、55〜110行）：`schemeStructurePerfectCechSquare_refinement … U V ρ hρ : CechAugmentedSquare.Map (schemeStructurePerfectCechSquare … U) (schemeStructurePerfectCechSquare … V)`。left は Y の実際の細分の cochain map、right は X の f⁻¹U・f⁻¹V への実際の細分、base・center は恒等。制限の可換性は既存の schemeStructurePerfectCechPullbackMap_refinement の等式（Map の向きへ反転）、増大写像の可換性は検証済みの augmentation_refinement。完全性・被覆性・アフィン性はこの射の定義の仮定に足さない。


G4 の同じ四角形の有限アフィン細分・共通細分による完全性の比較（着手前、既存の被覆比較の法則の内数、65〜140行）：`schemeStructurePerfectCechSquare_refinement_acyclic_iff … U V ρ hρ hU hV hcV` は f のアフィン性と X・Y のアフィン対角の下で、同じスカラーの四角形の全複体の完全性を有限アフィン細分で両向きに移す。Y の cone は既存の有限アフィン細分から、X 側は実際の逆像のアフィン性 `(hU i).preimage f` と逆像の被覆性から供給する。完全性・QuasiIsoAt を仮定し直さない。`schemeStructurePerfectCechSquare_commonAffine_acyclic_iff … U V hU hV hcU hcV` は既存の同じ有限共通開被覆と二つの射影を使い、二つの任意の有限アフィン被覆での同値を返す。f が閉埋め込みである F8 への適用では、そのアフィン性を既存の instance から供給する。X・Y のアフィン対角も後の射影模型から供給し、最終出力の新しい仮定にはしない。


次の F8 の native な係数移送の分割（着手前、既存の projectivePerfectCartesianAugmentedSquare の辺の自然性の内数、80〜200行）：`projectivePerfectCartesianScalarCompatibility` は既存の Cartesian な閉中心の H.w から、`g.appTop.hom.comp (projectiveScalarToGlobalSections G) = (schemeScalarHom X iX).comp (Ideal.Quotient.mk (I^1))` を返す。schemeScalarHom_naturality と schemeScalarHom_scalarMorphism の既存の等式の特殊化。`projectivePerfectCartesianScalarSquare … V` は同じ G・I・実際の閉中心とスカラーを、上記の既存の四角形への native な係数の代入に渡す略記。`projectivePerfectCartesianToScalarSquare` は標準開被覆における old F8 四角形からこの値への実際の CechAugmentedSquare.Map。C・E・基底・中心の項の写像は恒等で、制限・スカラー・商・中心の四辺の一致を既存の Edges の等式と検証済みの増大写像の自然性で示す。四角形全体の依存的な等式を強制せず、この実際の射と cone の比較で既知の F8 の完全性を移す。完全性を追加仮定にせず、Noether・有限表示・中心外の同型・全射性は既存の F8 の適用条件のまま。必要な源・先の条件と主張は変えない。


## G4：同じ四角形への native な係数移送と有限アフィン被覆の比較

`SchemePerfectCechAugmentationComposition`（39行）：`schemeStructurePerfectCechAugmentation_comp` は、実際のスカラーの合成を、同じ既存の増大写像と Frobenius の係数写像の合成へ移す。

`SchemeStructurePerfectCechSquare`（47行）：`schemeStructurePerfectCechSquare` は、既存の CechAugmentedSquare の各項と辺に、実際の構造層の Frobenius 係数・逆像被覆・大域スカラー・基底の環準同型を入れた値。制限の可換性は検証済みの増大写像の引き戻しと上の合成則から供給し、閉性も既存の増大写像から供給する。新しい四角形の概念や全複体は作っていない。完全性はデータの仮定ではない。

`SchemePerfectCechSquareRefinement`（49行）：`schemeStructurePerfectCechSquare_refinement` は、同じスカラーと基底・中心の係数を保つ、実際の細分の四角形の射。left・right は両空間の実際の細分の cochain map、基底・中心の項は恒等。四つの辺の自然性を既存の等式から供給する。

`SchemePerfectCechSquareAffineComparison`（73行）：`schemeStructurePerfectCechSquare_refinement_acyclic_iff` は f がアフィン、両空間がアフィン対角を持つとき、有限アフィン細分で同じ四角形の全複体の完全性が保たれ反映されること。X 側の逆像のアフィン性と被覆性も明示的に供給する。`schemeStructurePerfectCechSquare_commonAffine_acyclic_iff` は既存の同じ有限共通被覆を介して、二つの有限アフィン被覆での同値を返す。完全性や QuasiIsoAt の追加仮定はなく、実際の四角形の射を使う。原典との対応を Čech 版と明記した。

各単独検証、下書きと本体のソース完全一致、対象と入口のビルド5,167・5,168・5,169・5,170ジョブ、小監査1・9・9・2宣言（計21、所有元の生成・非公開宣言も全件）・標準三公理のみ、終了状態0。ログ `2g-perfect-cech-augmentation-composition-check-1.log`・`2g-perfect-cech-augmentation-composition-native.log`・`2g-perfect-cech-augmentation-composition-audit.log`、`2g-scheme-structure-perfect-square-check-1.log`・`2g-scheme-structure-perfect-square-native.log`・`2g-scheme-structure-perfect-square-audit.log`、`2g-scheme-perfect-square-refinement-check-2.log`・`2g-scheme-perfect-square-refinement-native.log`・`2g-scheme-perfect-square-refinement-audit.log`、`2g-scheme-perfect-square-affine-comparison-check-1.log`・`2g-scheme-perfect-square-affine-comparison-native.log`・`2g-scheme-perfect-square-affine-comparison-audit.log`。合成則・既存の四角形への代入・細分の射・最初の有限アフィン比較に局所的な backward.isDefEq.respectTransparency false を使用。共通細分の比較は既定の透明性。有限性を証明で使うが型の表示には現れないという Fintype linter の警告がある。追加公理・sorry・既存の型変更・資源制限の引き上げ・200行超の宣言なし。共有鍵 --class impl --wait 3600、待ちは一つ。対象ビルドと小監査は別の枠。root・下流全ビルド・全体監査なし。

今回4モジュール208行＋入口4行。新規85モジュール本体5,485行・入口込み5,570行、既存の追加25行を保守的に含む外枠計数は本体5,510行・入口込み5,595行。新規モジュールの小監査の累計603宣言と、既存モジュール15宣言は別計上（全体の再監査ではなく各束の小監査の和）。

次は F8 の projectivePerfectCartesianAugmentedSquare から、標準開でのこの native な値への実際の四角形の射で、既知の完全性を移す。既存の各辺の等式とスカラーの自然性は照合済みで、上に型を記録した。F8 の完全性の任意のアフィン被覆への適用そのもの、nerve との整合性、Frobenius 係数とアフィン conerve の自然な比較、fppf の二重 Čech と Noether 帰納、G5 は未完。条件付きの部品だけで Thm 2.9 の十分性を完成と呼ばない。全体の見込み約5,500〜12,000行・外枠16,000行は不変。停止点2g-2ではない。

一覧：済み1／全体3（うち追加0）。


同じ F8 の完全性の移送の法則（着手前、前記80〜200行の見込みの内数）：`projectivePerfectCartesianScalarSquare_standard_acyclic` は、同じ Noether・有限性・中心外の同型・全射性・Cartesian な閉中心の入力の下、標準開での projectivePerfectCartesianScalarSquare の全複体の Acyclic を返す。前記の実際の射の恒等成分の cone の完全性を供給し、既存の projectivePerfectCartesianSquare_acyclic から移す。F8 の完全性を追加仮定にしない。


G4 の同じ F8 の任意の有限アフィン被覆への適用（着手前、前記の閉中心と被覆比較の法則の内数、65〜130行）：`projectivePerfectCartesianClosedImmersion` は H から g の閉埋め込み性を、商の Spec の射の閉埋め込み性と pullback で供給する。`projectivePerfectCartesianSeparated` はこれと Proj の分離性から閉中心 Y の分離性を供給する。`projectivePerfectCartesianScalarSquare_acyclic … V hV hcV` は、既存の F8 と同じ Noether・有限性・中心外同型・全射性・Cartesian な閉中心の下、任意の有限アフィン被覆 V での同じ native な四角形の全複体の Acyclic。標準開での既知の完全性を、実際の共通細分の比較で移す。g のアフィン性と両空間のアフィン対角は上の実際の幾何から供給し、追加仮定にしない。V のアフィン性と被覆性は選んだ被覆の性質として明示する。


F8 の比較の各辺の証明分割（着手前、同じ係数移送の内数）：`projectivePerfectCartesianScalarAugmentation_eq_native` は old 四角形の scalar と、Proj の実際の大域スカラーの native な増大写像の等式。`projectivePerfectCartesianQuotient_eq_native` は quotient が同じ商の Frobenius 順極限の整数線形写像に等しいこと。`projectivePerfectCartesianCenterAugmentation_eq_native` は center と閉中心の実際の大域スカラーの native な増大写像の等式。三つとも元の G・I・p・Cartesian な証人と F8 の入力を保つ。比較の射の入れ子の証明から分け、型を明示して既定の heartbeat 内で検証する。資源制限は上げない。この分割を含む比較の束の見込みは約200〜320行へ補正する（2g-2 の外枠は不変）。


比較の射の組み立ての追加の証明分割（着手前、同じ内数）：`projectivePerfectCartesianScalarMap_restriction`・`..._scalar`・`..._quotient`・`..._center` はそれぞれ、始域 s=old F8 四角形・終域 t=native な同じ四角形、left=𝟙s.C・right=𝟙s.E・base=center=LinearMap.id に対する Map の四条件そのものの型。すなわち `s.restriction≫𝟙s.E=𝟙s.C≫t.restriction`、`((𝟙s.C).f 0).hom.comp s.scalar=t.scalar.comp id`、`id.comp s.quotient=t.quotient.comp id`、`((𝟙s.E).f 0).hom.comp s.center=t.center.comp id`。各条件の型を独立して検証し、Map の項へ証明定数として渡して、構造体の組み立てで大きな辺の定義を再展開しない。主張・射・仮定は不変、heartbeat は既定のまま。


## G4：F8 の同じ Cartesian なスカラーの native な係数移送

`ProjectivePerfectCartesianScalarSquare`（49行）：`projectivePerfectCartesianScalarCompatibility` は元の H.w と既存の Γ–Spec の自然性から、Proj のスカラーを閉中心へ引き戻すと商を経たスカラーになること。`projectivePerfectCartesianScalarSquare` は同じ G・I・実際の閉中心とそのスカラーを、前束の既存の四角形への native な係数の代入へ渡した値。任意の被覆を渡せるが、全複体の完全性をこの値の仮定にはしていない。

単独検証、下書きと本体のソース完全一致、対象と入口のビルド5,171ジョブ、小監査7宣言（所有元の生成・非公開宣言も含む）・標準三公理のみ、終了状態0。ログ `2g-projective-perfect-cartesian-scalar-square-check-2.log`・`2g-projective-perfect-cartesian-scalar-square-native.log`・`2g-projective-perfect-cartesian-scalar-square-audit.log`。既定の透明性・資源制限で成功。追加公理・sorry・既存の型変更・200行超の宣言なし。共有鍵 --class impl --wait 3600、待ちは一つ。対象ビルドと監査は別の枠。root・下流全ビルド・全体監査なし。

今回1モジュール49行＋入口1行。新規86モジュール本体5,534行・入口込み5,620行、既存の追加25行を保守的に含む計数は本体5,559行・入口込み5,645行。新規モジュールの小監査の累計610宣言と、既存モジュール15宣言は別計上。比較写像と標準開での F8 の完全性の移送は次の下書きで、まだ本体には含めない。各辺の証明を独立した法則に分けて、既定の heartbeat 内で組み立てを検証中。任意の有限アフィン被覆での適用と降下の帰納、G5 は未完。全体の見込み約5,500〜12,000行・外枠16,000行は不変。

一覧：済み1／全体3（うち追加0）。


次の表示の同型への係数移送の合成則（着手前、既存の引き戻しの合成の内数、55〜120行）：`schemeStructurePerfectCechRefinedPullbackMap_comp` は f:B→A・g:C→B・k:C→A と he:g≫f=k、同じ添字の被覆 U,V,W と各逆像への包含から、`schemeStructurePerfectCechRefinedPullbackMap f … U V id hV ≫ schemeStructurePerfectCechRefinedPullbackMap g … V W id hW = schemeStructurePerfectCechRefinedPullbackMap k … U W id hUW` を返す。元の環の appLE の合成と Frobenius 順極限の合成則を使い、平坦性を仮定しない。既存の通常の引き戻しの合成を再定義せず、同じ射を Frobenius 係数へ渡す法則。G3 の表示の同型に沿い、実際のブローアップと閉中心の四角形へ今の F8 の完全性を移すときに使う。


## G4：F8 の既知の完全性を同じ native な四角形の任意の有限アフィン被覆へ移す

`ProjectivePerfectCartesianScalarComparison`（184行）の宣言：

- `projectivePerfectCartesianScalarAugmentation_eq_native`：old 四角形の scalar は、同じ Proj の大域スカラーの native な増大写像。
- `projectivePerfectCartesianQuotient_eq_native`：old 四角形の quotient は、同じ商の実際の Frobenius 順極限の整数線形写像。
- `projectivePerfectCartesianCenterAugmentation_eq_native`：old 四角形の center は、同じ閉中心の大域スカラーの native な増大写像。既存の中心の式を、逆像被覆の増大写像の自然性で戻す。
- `projectivePerfectCartesianScalarMap_restriction`：恒等な二つの複体の成分について、old・native の制限の辺が可換。
- `projectivePerfectCartesianScalarMap_scalar`：同じ恒等成分と基底の係数の恒等写像について、scalar の辺が可換。
- `projectivePerfectCartesianScalarMap_quotient`：基底・中心の恒等写像について、quotient の辺が可換。
- `projectivePerfectCartesianScalarMap_center`：同じ恒等成分と中心の係数の恒等写像について、center の辺が可換。
- `projectivePerfectCartesianToScalarSquare`：上記の同じ二複体・係数の恒等成分と四条件を持つ、old F8 から native な四角形への実際の Map。
- `projectivePerfectCartesianScalarSquare_standard_acyclic`：同じ native な四角形の全複体は標準開で完全。恒等成分の cone の完全性と実際の Map の比較に、既存の F8 の完全性を渡す。

`ProjectivePerfectCartesianAffineCover`（74行）の宣言：

- `projectivePerfectCartesianClosedImmersion`：同じ Cartesian な閉中心の g は閉埋め込み。商の Spec の射の閉埋め込み性を全射性の既存の定理から供給し、H.flip に沿って底変換する。
- `projectivePerfectCartesianSeparated`：その閉中心は、分離的な Proj の閉部分スキームとして分離的。
- `projectivePerfectCartesianScalarSquare_acyclic`：元の F8 と同じ Noether・有限性・中心外同型・全射性・Cartesian な閉中心の入力の下、任意の有限アフィン被覆 V で同じ native な四角形の全複体は完全。g のアフィン性と両空間のアフィン対角を内部で供給し、実際の共通細分の四角形の射で移す。完全性を追加仮定にしていない。

単独検証、下書きと本体のソース完全一致、対象と入口のビルド5,172・5,173ジョブ、小監査14・3宣言（計17、所有元の非公開・生成宣言と local instance も含む）・標準三公理のみ、終了状態0。ログ `2g-projective-perfect-cartesian-scalar-comparison-check-4.log`・`2g-projective-perfect-cartesian-scalar-comparison-native.log`・`2g-projective-perfect-cartesian-scalar-comparison-audit.log` と `2g-projective-perfect-cartesian-affine-cover-check-2.log`・`2g-projective-perfect-cartesian-affine-cover-native.log`・`2g-projective-perfect-cartesian-affine-cover-audit.log`。比較の各辺と Map の四条件を分割し、既定の heartbeat 内で成功。比較の法則と任意の被覆への適用に局所的な backward.isDefEq.respectTransparency false を使用。閉中心の二法則は既定の透明性。長い行と、有限性を証明で使うが型の表示に現れない Fintype の linter 警告がある。追加公理・sorry・既存の型変更・資源制限の引き上げ・200行超の宣言なし。共有鍵 --class impl --wait 3600、待ちは一つ。対象ビルドと小監査は別の枠。root・下流全ビルド・全体監査なし。

今回2モジュール258行＋入口2行。新規88モジュール本体5,792行・入口込み5,880行、既存の追加25行を保守的に含む計数は本体5,817行・入口込み5,905行。新規モジュールの小監査の累計627宣言と、既存モジュール15宣言は別計上（全体を再監査した数ではなく各束の小監査の和）。

F8 の射影的な場合について、実際の構造層の Frobenius 係数・スカラー・Cartesian な閉中心の射を持つ同じ四角形の完全性を、任意の有限アフィン被覆へ移す所まで済み。次は G3 の表示の同型に沿って実際のブローアップとその閉中心へ移し、一つの選んだ被覆と nerve の整合性、Frobenius 係数とアフィン conerve の自然な比較、fppf の二重 Čech と Noether 帰納、G5 を接続する。Thm 2.9 の十分性全体や停止点2g-2はまだ未完。約6,000行の途中報告は次の束の実測で行い、そこで G4・G5 の残りも出し直す。全体の見込み約5,500〜12,000行・外枠16,000行は不変。

一覧：済み1／全体3（うち追加0）。


同じ合成則の単位の分割（着手前、前記55〜120行の内数）：`schemeStructurePerfectCechPullbackMap_eq_refined f p hp hY hX U` は実際の Frobenius 係数の引き戻しと、同じ逆像被覆への恒等細分を合成した refinedPullback の等式。既存の細分の恒等則だけを用い、後続の表示の同型の比較を同じ射で扱う。


合成則の各タプルでの証明分割（着手前、同じ内数）：`schemeStructurePerfectCechRefinedPullbackMap_comp_apply … q a t` は上記の二段の refinedPullback を、次数 q の cochain a のタプル t で評価した式が、合成射の refinedPullback の同じ評価に等しいこと。各タプルの計算と複体の射の外延性を別宣言にし、環準同型を評価する lambda の型も明示する。既定の heartbeat を保ち、主張・射・仮定は変えない。


表示の同型の三角形で使う増大写像の自然性の分割（着手前、既存の引き戻し・細分の合成の内数、35〜85行）：`schemeStructurePerfectCechRefinedPullbackMap_augmentation f φ ψ hψ p hp hR hY hX U V ρ hρ` は、実際の大域スカラーの整合性 ψ=f.appTop.comp φ の下で、refinedPullback の零次と source の native な増大写像の合成が target の同じ増大写像に等しいこと。検証済みの通常の逆像への増大写像の自然性と、細分による増大写像の保存を合成する。既存の射とスカラーを保持し、平坦性・被覆性を追加しない。


同じ閉中心を保つ三角形の係数移送（着手前、既存の CechAugmentedSquare.Map の自然性の内数、80〜160行）：v:Y→Z、f:X→Y、g:X→Z、he:f≫v=g、被覆 U:ι→Z.Opens と V:ι→Y.Opens、hV:∀i,V i≤v⁻¹U i に対し、`schemePerfectCechTriangle_preimage_le` は `∀i,f⁻¹V i≤g⁻¹U i`。`schemeStructurePerfectCechSquare_triangleMap` は同じ基底 R・中心 S・q:R→S・ψ:S→Γ(X,⊤)、φY=v.appTop.comp φZ と二つのスカラーの可換性から、`Map (schemeStructurePerfectCechSquare g … φZ … U) (schemeStructurePerfectCechSquare f … φY … V)` を返す。left は v の実際の refinedPullback、right は同じ X 上の逆像被覆の実際の細分、base・center は恒等。制限の可換性は上の refinedPullback の合成、scalar は上の増大写像の自然性、center は既存の細分の増大写像の自然性。完全性を追加仮定にせず、表示の同型 v への適用で同じ四角形を実際のブローアップへ移す。


表示の同型の比較の次の分割（着手前、既存の被覆・四角形比較の法則の内数、70〜150行）：`openCoverCechRefinementMap_isIso_of_eq P U V h hV` は同じ添字で V=U の細分の射そのものが同型であること。`schemeStructurePerfectCechSquare_iso_acyclic_iff v f g he … U` は v がスキームの同型のとき、上の triangleMap で V=v⁻¹U として同じ native な四角形の全複体の完全性を両向きに移す。left は既存の実際の同型の引き戻し、right は he:f≫v=g によって等しい二つの逆像被覆の恒等細分。実際の両辺の同型から cone の完全性を供給し、完全性・quasi-isomorphism を追加仮定にしない。


## G4：実際の引き戻しの合成、増大写像、同じ閉中心の三角形

- `SchemePerfectCechPullbackComposition`（89行）：`schemeStructurePerfectCechPullbackMap_eq_refined` は通常の引き戻しと恒等細分付きの引き戻しの一致。`schemeStructurePerfectCechRefinedPullbackMap_comp_apply` は実際の appLE と Frobenius 順極限の合成を各タプルで計算した一致。`schemeStructurePerfectCechRefinedPullbackMap_comp` は既存の全タプル複体の外延性 API で同じ二段の射と合成射の一致を返す。
- `SchemePerfectCechRefinedAugmentation`（41行）：`schemeStructurePerfectCechRefinedPullbackMap_augmentation` は、実際の大域スカラー ψ=f.appTop.comp φ に沿って、細分を含む引き戻しの零次が同じ増大写像を保つこと。
- `SchemePerfectCechSquareTriangle`（74行）：`schemePerfectCechTriangle_preimage_le` は三角形から同じ閉中心の逆像被覆の包含を返す。`schemeStructurePerfectCechSquare_triangleMap` は left に実際の refinedPullback、right に同じ X の実際の細分、base・center に恒等を入れ、制限・スカラー・商・中心の四条件を持つ実際の四角形の射。完全性は仮定していない。

単独検証、下書きと本体のソース完全一致、対象と入口のビルド5,174・5,175・5,176ジョブ成功、小監査は所有元の全宣言5・1・8（計14、生成・非公開を含む）・標準三公理のみ、終了状態0。ログ `2g-perfect-cech-pullback-composition-check-3.log`・`2g-perfect-cech-pullback-composition-native.log`、`2g-perfect-cech-refined-augmentation-check-2.log`・`2g-perfect-cech-refined-augmentation-native.log`、`2g-perfect-cech-square-triangle-check-1.log`・`2g-perfect-cech-square-triangle-native.log`、`2g-perfect-cech-triangle-bundle-audit.log`。合成の点ごとの式と射の外延性を分割し、既定の heartbeat で成功。局所的な backward.isDefEq.respectTransparency false を使用。三角形の包含の補題に LinearOrder の未使用 section variable の linter 警告がある。追加公理・sorry・既存の型変更・資源制限の引き上げ・200行超の宣言なし。共有鍵 --class impl --wait 3600、待ちは一つ、ビルドと監査は別枠。root・下流全ビルド・全体監査なし。

## 約6,000行での途中報告（停止せず続行）

今回3モジュール204行＋入口3行。新規91モジュール本体5,996行・入口込み6,087行。既存 API の追加25行を保守的に含む外枠計数は本体6,021行・入口込み6,112行。新規モジュールの小監査の累計641宣言、既存モジュール15宣言は別計上。

G3 は完成。G4 は F8 の同じスカラー・実際の構造層の Frobenius 係数の四角形の完全性を、任意の有限アフィン被覆に移す所まで済み。実際の表示の同型による移送は、上の三角形の射を使う同型比較の下書きを検証中。残り G4 は同型移送・一つの被覆と nerve の整合性・Frobenius 係数と実際のアフィン conerve の比較・nilpotent な閉厚化・fppf の二重 Čech と Noether 帰納、約2,000〜4,000行。G5 は既存の有限型 F_p 被覆模型と filtered colimit への自然な移送、約1,000〜2,000行。合計の着地を約9,000〜12,100行へ補正し、外枠16,000行は不変。最終の AugmentedRingCechExact の型・仮定は変えない。G4・G5 と停止点2g-2は未完であり、条件付きの射影比較だけを Thm 2.9 の十分性全体の完成とは呼ばない。

一覧：済み1／全体3（うち追加0）。


実際の DegreeOneProjectiveModel の構造射の移送（着手前、既存の表示の同型・Cartesian square の法則の内数、65〜130行）：`DegreeOneProjectiveModel.scalarHom` は schemeScalarHom Y f が m.iso.hom による Proj の大域スカラーの引き戻しであること。`DegreeOneProjectiveModel.cartesian` は H:IsPullback g iX f q から同じ X・iX を保ち、上辺を g≫m.iso.hom、右辺を projectiveCechStructureMap m.grade とする Cartesian square を返す。`DegreeOneProjectiveModel.structure_surjective` は元の f の全射性から同じ Proj の構造射の全射性。`DegreeOneProjectiveModel.restrict_isIso` は任意の基底開 W に対し f∣W の同型性から Proj の構造射の W 上の同型性を返す。全て m.over と m.iso を使う移送で、新しい幾何学的仮定や模型の存在を要求しない。


同じ F8 の実際の模型への適用（着手前、既存の完全性の同型移送の法則の内数、85〜180行）：`DegreeOneProjectiveModel.perfectCartesianSquare_acyclic` は Noether 環 R、f:Y→Spec R の既存の表示 m、I:Ideal R、元の IsPullback g iX f (Spec.map quotient)、f の全射性と中心外同型性、p が素数かつ R 上で零、Y の任意の有限アフィン被覆 V から、実際の g・schemeScalarHom Y f・schemeScalarHom X iX・商の Frobenius 係数を持つ native な四角形の全複体の完全性を返す。m.projectiveCechData から同じ多項式環作用・有限性・標準開の被覆を供給し、m.iso.inv による V の逆像で Proj 版 F8 を適用して、上の実際の同型比較で戻す。R の標数から m.ring の標数も供給する。F8 の幾何学的入力は変えず、完全性・表示先の全射性などを仮定として追加しない。


## G4：表示の同型に沿う同じ四角形の完全性の比較

`SchemePerfectCechSquareIsoComparison`（73行）：`openCoverCechRefinementMap_isIso_of_eq` は等しい被覆の恒等添字の細分の射そのものが同型。`schemeStructurePerfectCechSquare_iso_acyclic_iff` は前記の実際の triangleMap の両辺の同型から cone の完全性を供給し、同じ閉中心とスカラーの native な四角形の全複体の完全性を表示の同型に沿って両向きに移す。完全性や QuasiIsoAt を仮定として追加しない。Čech 版と原典との対応を docstring に明記。

単独検証、本体ソース完全一致、対象と入口のビルド5,177ジョブ成功、小監査2宣言・標準三公理のみ、終了状態0。ログ `2g-perfect-cech-square-iso-comparison-check-3.log`・`2g-perfect-cech-square-iso-comparison-native.log`・`2g-perfect-cech-square-iso-comparison-audit.log`。局所的な backward.isDefEq.respectTransparency false を使用、既定の資源制限。追加公理・sorry・既存の型変更・200行超の宣言なし。共有鍵 --class impl --wait 3600、待ちは一つ、ビルドと監査は別枠。root・下流全ビルド・全体監査なし。

今回1モジュール73行＋入口1行。新規92モジュール本体6,069行・入口込み6,161行。既存追加25行を含む計数は本体6,094行・入口込み6,186行。新規の小監査累計643宣言、既存15宣言は別計上。残りの模型条件の移送と実際の模型への F8 の適用は drafts で検証中で、本体には含めない。残り G4 約2,000〜4,000行・G5 約1,000〜2,000行、外枠16,000行は不変。停止点2g-2は未完。

一覧：済み1／全体3（うち追加0）。


同じ一つの被覆から nerve の被覆を作る法則（着手前、G4 の既存の幾何的 Čech nerve と有限被覆の整合性の内数、85〜180行）：`schemeCechTupleOpen f U n t` は既存の nerve の全ての射影 π_j による U(t j) の逆像の有限交叉という開集合。`schemeCechTupleOpen_iSup` は U が被覆なら全タプル t のこれらの開集合も被覆であること。`schemeCechTupleOpen_map_le` は h:m→n という実際の nerve の射に対し source のタプル s の開が、target のタプル s∘h.unop.toOrderHom の開の逆像に含まれること。したがって各次数で独立な被覆を選ばず、同じ U の添字の前合成を使える。有限性は ι の有限性から供給し、アフィン性と閉中心への底変換の照合は次の分割に残す。


## G4：F8 を元の構造射・閉中心・任意の有限アフィン被覆へ戻す

`DegreeOneProjectiveModelScalar`（66行）の宣言：

- `DegreeOneProjectiveModel.scalarHom`：元の構造射の大域スカラーは、表示の同型による同じ Proj の大域スカラーの引き戻し。
- `DegreeOneProjectiveModel.cartesian`：同じ閉中心の空間・商の構造射を保ち、右上だけを表示の同型で Proj に移した Cartesian square。
- `DegreeOneProjectiveModel.structure_surjective`：元の構造射の全射性から、同じ表示の Proj の構造射の全射性。
- `DegreeOneProjectiveModel.restrict_isIso`：元の構造射の任意の基底開での同型性から、同じ表示の Proj の構造射のその開での同型性。

`DegreeOneProjectiveModelPerfectSquare`（77行）：`DegreeOneProjectiveModel.perfectCartesianSquare_acyclic` は、Noether 基底、元の構造射 f の全射性・中心外同型性・同じ Cartesian な閉中心・p の零化から、元の g と schemeScalarHom Y f、schemeScalarHom X iX、同じ商の Frobenius 係数の四角形の完全性を、任意の有限アフィン被覆で返す。多項式環作用・有限性・標準開の被覆条件は同じ既存の m.projectiveCechData、表示先の全射性・中心外同型性は上の二法則、m.ring の標数は元の R の標数から供給する。同じ V を逆同型で Proj に移して既存の F8 を適用し、実際の四角形の同型比較で戻す。完全性や表示先の幾何学的条件を追加仮定として要求しない。Čech 版と原典との対応を docstring に明記。

単独検証、本体とのソース完全一致、対象と入口のビルド5,178・5,179ジョブ成功、小監査4・2宣言（計6、所有元の全生成宣言を含む）・標準三公理のみ、終了状態0。ログ `2g-degree-one-projective-model-scalar-check-3.log`・`2g-degree-one-projective-model-scalar-native.log`・`2g-degree-one-projective-model-scalar-audit.log`、`2g-degree-one-projective-model-perfect-square-check-2.log`・`2g-degree-one-projective-model-perfect-square-native.log`・`2g-degree-one-projective-model-perfect-square-audit.log`。局所的な backward.isDefEq.respectTransparency false を使用、既定の資源制限。letI の代わりに let を勧める style 警告と長い行の警告がある。追加公理・sorry・既存の型変更・200行超の宣言なし。共有鍵 --class impl --wait 3600、待ちは一つ、対象ビルドと監査は別枠。root・下流全ビルド・全体監査なし。

今回2モジュール143行＋入口2行。新規94モジュール本体6,212行・入口込み6,306行。既存追加25行を含む外枠計数は本体6,237行・入口込み6,331行。新規小監査累計649宣言、既存15宣言は別計上。実際のブローアップとその有限ファイバー冪には既存の G3 の表示が供給されるので、この同じ定理を適用できる。ただし一つの被覆の nerve との整合性と Noether 帰納全体、G5 は未完。次のタプル被覆は drafts で検証中で、本体に含めない。外枠16,000行は不変。

一覧：済み1／全体3（うち追加0）。


タプル被覆のアフィン性に使う底変換の分割（着手前、同じ被覆の底変換の法則の内数、45〜110行）：`pullbackAffineOpen_inf` はアフィン基底 S、f:X→S・g:Y→S、アフィン開 U,V に対し、実際の pullback 上の fst⁻¹U∩snd⁻¹V がアフィンであること。制限した二つのアフィンの同じ pullback の開埋め込みの像を使う。`isPullbackAffineOpen_inf` は同じ主張を任意の H:IsPullback a b f g に実際の H.isoPullback で移す。次の有限ファイバー冪での帰納にはこの二つの既存の底変換・同型の法則を使い、射影をアフィン射と誤って仮定しない。


タプル被覆の有限交叉・アフィン性の分割（着手前、同じ被覆の法則の内数、65〜145行）：`schemePreimage_finite_iInf` は有限族の開の交叉がスキームの逆像と可換。`schemeCechTupleOpen_succ` は n+2 個のタプル開を、末尾 n+1 個の既存の lift の逆像と先頭の射影の逆像の交叉として表す。`schemeCechTupleOpen_isAffine` は基底 S がアフィンで U の全てがアフィン開なら、同じ既存の nerve の全てのタプル開もアフィンであること。既存の finiteFiberPowerZeroIso と isPullback_finiteFiberPowerSucc、直前の Cartesian square のアフィン開の法則で帰納し、射影にアフィン射の仮定を加えない。


## G4：一つの被覆から実際の nerve のタプル被覆を供給する

`SchemeCechTupleCover`（76行）の宣言：`schemeCechTupleOpen` は実際の nerve の全ての射影の逆像の有限交叉。`schemeCechTupleOpen_iSup` は元の被覆性から各 nerve 項のタプル被覆性。`schemeCechTupleOpen_map_le` はすべての実際の nerve の射について、同じタプルの添字の前合成に沿う被覆の細分の包含。各次数で無関係な被覆を選んでおらず、面・退化を含む全ての射を扱う。

`SchemePullbackAffineTupleOpen`（45行）：`pullbackAffineOpen_inf` はアフィン基底上の二つのアフィン開の実際のファイバー積が pullback 内でアフィン開であること。制限したアフィンのファイバー積の開埋め込みの像を使う。`isPullbackAffineOpen_inf` は同じ主張を H.isoPullback に沿って任意の Cartesian square に移す。元の射や pullback の射影のアフィン性を仮定しない。

単独検証、本体とのソース完全一致、対象と入口のビルド5,181ジョブ成功、小監査6・3宣言（計9、所有元の非公開・生成宣言を含む）・標準三公理のみ、終了状態0。ログ `2g-scheme-cech-tuple-cover-check-5.log`・`2g-scheme-pullback-affine-tuple-open-check-3.log`・`2g-scheme-cech-tuple-cover-native-2.log`・`2g-scheme-cech-tuple-cover-audit.log`。本体の module 可視性のため既存の Mathlib.AlgebraicGeometry.PullbackCarrier を明示 import した。局所的な backward.isDefEq.respectTransparency false を使用、既定の資源制限。追加公理・sorry・既存の型変更・200行超の宣言なし。共有鍵 --class impl --wait 3600、待ちは一つ、ビルドと監査は別枠。root・下流全ビルド・全体監査なし。

今回2モジュール121行＋入口2行。新規96モジュール本体6,333行・入口込み6,429行。既存追加25行を含む外枠計数は本体6,358行・入口込み6,454行。新規小監査累計658宣言、既存15宣言は別計上。タプル開の全次数でのアフィン性の帰納と有限交叉の公式は、次の未検証の下書きであり本体に含めない。閉中心への底変換の照合・二重 Čech・Noether 帰納と G5 は残る。外枠16,000行は不変。停止点2g-2ではない。

一覧：済み1／全体3（うち追加0）。


異なる次数のタプル添字への引き戻しの合成（着手前、既存の refinedPullback の合成則の内数、80〜150行）：`schemeStructurePerfectCechRefinedPullbackMap_compIndex_apply` と `..._compIndex` は、被覆 U:ι→A.Opens、V:κ→B.Opens、W:λ→C.Opens、ρ:κ→ι、σ:λ→κ と包含 hV,hW,hUW に対し、二段の実際の refinedPullback の合成が添字 ρ∘σ の合成射の refinedPullback に等しいこと。それぞれタプルごとの式と複体の射の式。先の同じ添字の合成の証明と同じ appLE・Frobenius 順極限の合成則を使う。既存の名前・型を変更せず、nerve の面・退化で添字型が異なる場合を同じ射の法則として供給する。


同じ引き戻しの単位の法則（着手前、nerve の実際の係数図式の単位則の内数、30〜75行）：`schemeStructurePerfectCechRefinedPullbackMap_id X p hp hX U` は恒等スキーム射と同じ被覆・恒等添字からの refinedPullback が既存の全タプル複体の恒等射に等しいこと。各タプルで id の appLE と Frobenius 順極限の恒等則を使い、複体の射の外延性でまとめる。次の nerve の係数図式の map_id へ使い、既存の宣言は変更しない。


合成の外延性の分割（着手前、同じ80〜150行の内数）：`fullCechComplex_hom_ext_index` は D:Finset ι→ModuleCat R と E:Finset ν→ModuleCat R の異なる添字型について、二つの複体の射の全ての target タプルでの評価が等しければ射が等しいこと。既存の同じ添字型の外延性と同じ証明の法則を別名で補い、既存の名前・型を変更しない。

## G4：同じタプル被覆の全次数のアフィン性

`SchemeCechTupleAffine`（74行）の宣言：`schemePreimage_finite_iInf` は有限交叉と逆像の可換性。`schemeCechTupleOpen_succ` は同じタプル開を、末尾の n+1 個への実際の lift の逆像と先頭の射影の逆像の交叉に分ける公式。`schemeCechTupleOpen_isAffine` はアフィン基底上で、元の U がアフィン開からなれば全ての nerve 項の同じタプル開もアフィンであること。既存の一個の冪の同型と先頭・末尾の Cartesian square の帰納を使用し、射影をアフィン射とは仮定しない。

単独検証、本体とのソース完全一致、対象と入口のビルド5,182ジョブ成功、小監査5宣言（所有元の全宣言）・標準三公理のみ、終了状態0。ログ `2g-scheme-cech-tuple-affine-check-2.log`・`2g-scheme-cech-tuple-affine-native.log`・`2g-scheme-cech-tuple-affine-audit.log`。既定の透明性・資源制限で成功。式内の let b を明示的に使っていないという linter 警告がある。追加公理・sorry・既存の型変更・200行超の宣言なし。共有鍵 --class impl --wait 3600、待ちは一つ、対象ビルドと監査は別枠。root・下流全ビルド・全体監査なし。

今回1モジュール74行＋入口1行。新規97モジュール本体6,407行・入口込み6,504行。既存追加25行を含む外枠計数は本体6,432行・入口込み6,529行。新規小監査累計663宣言、既存15宣言は別計上。一つの有限アフィン被覆から同じ nerve の被覆性・アフィン性・全ての射での包含を供給した。これを Frobenius の実際の係数の図式へ渡す単位・合成の法則は下書きで検証中。閉中心との底変換・二重 Čech・Noether 帰納と G5 は残る。外枠16,000行は不変。停止点2g-2は未完。

一覧：済み1／全体3（うち追加0）。


同じ nerve の係数図式の法則の束（着手前、G4 の既存の二重 Čech の係数の整合性の内数、90〜180行）：`schemePerfectCechTupleComplex f U p hp h n` は同じタプル被覆と実際の構造層の Frobenius 係数の既存の全タプル複体。`schemePerfectCechTupleMap … a` は幾何的 nerve の a.op の実際の refinedPullback とタプルの添字の前合成。`schemePerfectCechTupleMap_id` と `…_comp` は直前の単位・異なる添字の合成則をこの値へ渡す。`schemePerfectCechTupleFunctor` はこれら同じ値と射を SimplexCategory 上の既存の複体の関手にまとめる。h は各 nerve 項の全ての開での p の零化の証人を保持する引数であり、最終の入口で基底の標数から供給する。幾何的 nerve の反変な実際の切断の図式であり、各次数の無関係な H の同型を並べたものではない。まだ閉中心との底変換や B1 の二重 Čech の適用までは含まない。


単位則を実際の nerve の単位へ渡す分割（着手前、同じ単位則の内数、10〜25行）：`schemeStructurePerfectCechRefinedPullbackMap_eq_id_of_eq f hf p hp hX U ρ hρ hc` は f:X→X、hf:f=𝟙X、ρ:ι→ι、hρ:ρ=id から、同じ refinedPullback が恒等であること。既存の単位則を等式で移すだけで、新しい完全性は主張しない。nerve.map_id と添字の単位を個別に渡し、大きな実際の nerve と複体の定義を同時に展開しない。


## G4：異なる添字の引き戻しの合成と、実際の単位への移送

`SchemePerfectCechRefinedComposition`（93行）：`fullCechComplex_hom_ext_index` は異なる添字型の全タプル複体の二つの射を target の各タプルで検査する外延性。`schemeStructurePerfectCechRefinedPullbackMap_compIndex_apply` は異なる三つの添字型と二つの添字写像 ρ,σ について、二段の実際の引き戻しと合成射・添字 ρ∘σ の引き戻しの各タプルでの一致。`schemeStructurePerfectCechRefinedPullbackMap_compIndex` は同じ実際の余鎖写像の一致。既存の同じ添字の宣言の名前・型は変えていない。

`SchemePerfectCechRefinedIdentity`（59行）：`schemeStructurePerfectCechRefinedPullbackMap_id` は同じ被覆と恒等射・恒等添字の refinedPullback が複体の恒等射に等しいこと。`schemeStructurePerfectCechRefinedPullbackMap_eq_id_of_eq` は実際の射 f=𝟙、添字写像 ρ=id という二つの等式から同じ単位則を渡す。nerve の大きな定義を同時に展開せず、実際の map_id と添字の恒等性を分けて係数図式へ渡す。

単独検証、本体とのソース完全一致、対象と入口のビルド5,183・5,184ジョブ成功、小監査4・2宣言（計6、所有元の全宣言）・標準三公理のみ、終了状態0。ログ `2g-perfect-cech-refined-composition-check-3.log`・`2g-perfect-cech-refined-composition-native.log`、`2g-perfect-cech-refined-identity-check-6.log`・`2g-perfect-cech-refined-identity-native-2.log`、`2g-perfect-cech-refined-laws-audit.log`。局所的な backward.isDefEq.respectTransparency false を使用、既定の資源制限。単位則の change が冗長という linter 警告がある。追加公理・sorry・既存の型変更・200行超の宣言なし。共有鍵 --class impl --wait 3600、待ちは一つ、ビルドと監査は別枠。root・下流全ビルド・全体監査なし。

今回2モジュール152行＋入口2行。新規99モジュール本体6,559行・入口込み6,658行。既存追加25行を含む外枠計数は本体6,584行・入口込み6,683行。新規小監査累計669宣言、既存15宣言は別計上。これらの法則を使った同じタプル被覆の実際の係数の関手は単独検証に成功したが、まだ本体ビルド・監査前でこの束には含めない。残る閉中心の底変換・二重 Čech・Noether 帰納と G5 は未完。外枠16,000行は不変。

一覧：済み1／全体3（うち追加0）。


## G4：同じタプル被覆の実際の Frobenius 係数の関手

`SchemePerfectCechTupleFunctor`（78行）の宣言：

- `schemePerfectCechTupleComplex`：実際の nerve の同じタプル被覆における構造層の Frobenius 係数の既存の全タプル複体。
- `schemePerfectCechTupleMap`：幾何的 nerve の実際の a.op の refinedPullback と、同じタプルの添字の前合成の写像。
- `schemePerfectCechTupleMap_id`：実際の nerve.map_id と添字の単位を、検証済みの単位則へ個別に渡した単位。
- `schemePerfectCechTupleMap_comp`：実際の nerve.map_comp と異なる添字型の引き戻しの合成則による合成の保存。
- `schemePerfectCechTupleFunctor`：上の同じ複体と写像を SimplexCategory 上の複体の関手へまとめたもの。h は各項の切断環での p の零化の証人を保持し、最終の入口で基底の標数から供給する。

単独検証、本体とのソース完全一致、対象と入口のビルド5,185ジョブ成功、小監査9宣言（所有元の非公開・生成宣言を含む）・標準三公理のみ、終了状態0。ログ `2g-perfect-cech-tuple-functor-check-3.log`・`2g-perfect-cech-tuple-functor-native.log`・`2g-perfect-cech-tuple-functor-audit.log`。単位の移送を前記の型つきの等式に分割し、既定の heartbeat 内で成功。局所的な backward.isDefEq.respectTransparency false を使用。追加公理・sorry・既存の型変更・資源制限の引き上げ・200行超の宣言なし。共有鍵 --class impl --wait 3600、待ちは一つ、対象ビルドと監査は別枠。root・下流全ビルド・全体監査なし。

今回1モジュール78行＋入口1行。基準56ea849a3からの追加ファイルを独立に数え直して、新規100モジュール本体6,637行・入口込み6,737行で一致した。既存追加25行を含む外枠計数は本体6,662行・入口込み6,762行。新規小監査累計678宣言、既存15宣言は別計上。次は実際の有限ファイバー冪の全射性・中心外同型性、閉中心への自然な底変換、同じ図式の B1 への接続。二重 Čech の判定法や Noether 帰納、G5 はまだ完成していない。外枠16,000行は不変、停止点2g-2ではない。

一覧：済み1／全体3（うち追加0）。


実際の有限ファイバー冪の幾何学的入力の法則（着手前、G4 の同じ F8 の入力の底変換の内数、85〜180行）：`isPullback_restrict_left_isIso H W` は H:IsPullback a b f g と g∣W の同型性から a∣f⁻¹W の同型性を、既存の H.isPullback_resLE に沿う底変換で返す。`finiteFiberPowerBase_surjective f n` は元の f の全射性から同じ WidePullback.base の全射性を、実際の対角 lift と base の合成が f であることから返す。`finiteFiberPowerBase_restrict_isIso f W n` は f∣W の同型性から同じ base∣W の同型性を、既存の一個の冪の同型と先頭・末尾の Cartesian な帰納で返す。Noether 性・射影性は不要で、G3 の表示と同じ実際の有限冪を保つ。


閉中心と実際の nerve の底変換の法則（着手前、既存の幾何的 Čech nerve の底変換の内数、65〜155行）：`isPullback_cechNerve_base F H n` は既存の Arrow の射 F:f→g と H:IsPullback F.left f.hom g.hom F.right から、実際の Arrow.mapCechNerve F の n 次と二つの既存の WidePullback.base、F.right が Cartesian square であることを返す。既存の mapCechNerve の射そのものを使い、その自然性も既存の NatTrans のまま保持する。各点の全単射や無関係な各次数の表示の同型ではなく、元の H と同じ wide pullback の普遍性から示す。閉中心の基底変更への特殊化で、同じ係数の四角形と中心の nerve の項を照合する。


## G4：同じ有限ファイバー冪の全射性・中心外同型性

`FiniteFiberPowerGeometricInputs`（72行）の宣言：`isPullback_restrict_left_isIso` は元の Cartesian square の右辺の W 上の同型性から、左辺の f⁻¹W 上の同型性を既存の isPullback_resLE で供給する。`finiteFiberPowerBase_surjective` は対角 lift と同じ base の合成が元の f に等しいことと Surjective.of_comp による全射性。`finiteFiberPowerBase_restrict_isIso` は元の f∣W の同型性から、既存の一個の冪の同型と先頭・末尾の Cartesian な帰納で、同じ base∣W の同型性。全て G3 の表示と同じ有限 wide pullback の base を使い、Noether 性・射影性は仮定していない。

単独検証、本体とのソース完全一致、対象と入口のビルド5,186ジョブ成功、小監査3宣言・標準三公理のみ、終了状態0。ログ `2g-finite-fiber-power-geometric-inputs-check-2.log`・`2g-finite-fiber-power-geometric-inputs-native.log`・`2g-finite-fiber-power-geometric-inputs-audit.log`。局所的な backward.isDefEq.respectTransparency false を使用、既定の資源制限。追加公理・sorry・既存の型変更・200行超の宣言なし。共有鍵 --class impl --wait 3600、待ちは一つ、対象ビルドと監査は別枠。root・下流全ビルド・全体監査なし。

今回1モジュール72行＋入口1行。新規101モジュール本体6,709行・入口込み6,810行。既存追加25行を含む外枠計数は本体6,734行・入口込み6,835行。新規小監査累計681宣言、既存15宣言は別計上。次の実際の mapCechNerve の Cartesian な底変換の法則は drafts で検証中であり、本体に含めない。閉中心と同じ図式の係数の照合・二重 Čech・Noether 帰納と G5 は残る。外枠16,000行は不変。停止点2g-2ではない。

一覧：済み1／全体3（うち追加0）。


同じタプル被覆の Arrow の射による逆像（着手前、既存の被覆の底変換の法則の内数、30〜75行）：`schemeCechTupleOpen_mapCechNerve_preimage F U n t` は任意の実際の Arrow の射 F:f→g に対し、f の項上での F.left⁻¹U のタプル開が、既存の mapCechNerve F の n 次による g の同じタプル開の逆像に等しいこと。有限交叉と逆像の交換、同じ mapCechNerve の各射影との可換性を使う。Cartesian 性・平坦性は不要で、閉中心への適用ではその同じ実際の逆像被覆を供給する。


同じ二つの係数関手の自然な引き戻し（着手前、既存の係数移送の自然性の内数、90〜180行）：`schemePerfectCechTuplePullbackMap F U p hp hf hg n` は F:f→g の実際の mapCechNerve の n 次と、直前の同じ被覆の逆像の等式による恒等添字の refinedPullback。`schemePerfectCechTuplePullback_naturality … a` は元の自然変換 mapCechNerve F の naturality と、異なる添字の二つの compIndex を同じ合成射・同じ包含へ渡した自然性。`schemePerfectCechTuplePullback` はこれらを元の係数関手から閉中心側の係数関手への NatTrans にまとめる。Cartesian 性は不要で、各項の p の零化だけを保持し、後で実際の基底の標数から供給する。独立なコホモロジーの比較や全複体の完全性は仮定しない。


## G4：実際の nerve と同じタプル被覆の閉中心への底変換

`CechNerveCartesianBaseChange`（60行）：`isPullback_cechNerve_base` は Cartesian な Arrow の射 F:f→g とその元の証人 H から、既存の自然変換 mapCechNerve F の n 次・二つの同じ WidePullback.base・F.right が Cartesian square であること。元の H と同じ wide pullback の普遍性で示し、各次数の無関係な対象を選ばない。任意の有限極限を持つ圏での法則で、スキームの閉中心への特殊化に使う。

`SchemeCechTupleBaseChange`（37行）：`schemeCechTupleOpen_mapCechNerve_preimage` は元の U の F.left による逆像のタプル開と、同じ mapCechNerve の項による元のタプル開の逆像の一致。有限交叉と逆像の可換性と同じ射影の合成則を使う。Cartesian 性・平坦性は不要。

単独検証、本体とのソース完全一致、対象と入口のビルド5,187・5,188ジョブ成功、小監査各1宣言（計2、所有元の全宣言）・標準三公理のみ、終了状態0。ログ `2g-cech-nerve-cartesian-base-change-check-2.log`・`2g-cech-nerve-cartesian-base-change-native.log`、`2g-scheme-cech-tuple-base-change-check-1.log`・`2g-scheme-cech-tuple-base-change-native.log`、`2g-cech-nerve-and-tuple-base-change-audit.log`。被覆の等式に局所的な backward.isDefEq.respectTransparency false を使用、既定の資源制限。追加公理・sorry・既存の型変更・200行超の宣言なし。共有鍵 --class impl --wait 3600、待ちは一つ、対象ビルドと監査は別枠。root・下流全ビルド・全体監査なし。

今回2モジュール97行＋入口2行。新規103モジュール本体6,806行・入口込み6,909行。既存追加25行を含む外枠計数は本体6,831行・入口込み6,934行。新規小監査累計683宣言、既存15宣言は別計上。次の同じ係数関手の自然変換は drafts で検証する段であり、本体には含めない。二重 Čech・Noether 帰納と G5 は残る。外枠16,000行は不変。停止点2g-2ではない。

一覧：済み1／全体3（うち追加0）。


## G4：同じ二つの係数関手の実際の引き戻しの自然性

`SchemePerfectCechTupleNaturality`（73行）の宣言：`schemePerfectCechTuplePullbackMap` は任意の Arrow の射 F の既存の mapCechNerve の各項と、同じタプル被覆の逆像の等式による実際の refinedPullback。`schemePerfectCechTuplePullback_naturality` は元の自然変換の naturality と、同じ合成射・同じ包含に対する二つの compIndex による自然性。`schemePerfectCechTuplePullback` はこの同じ項と写像を、元の係数関手から逆像の被覆の係数関手への自然変換にまとめる。Cartesian 性・平坦性・完全性は仮定しない。各項の p の零化は保持し、最終の入口で基底の標数から供給する。

単独検証、本体とのソース完全一致、対象と入口のビルド5,189ジョブ成功、小監査7宣言（所有元の非公開・生成宣言を含む）・標準三公理のみ、終了状態0。ログ `2g-perfect-cech-tuple-naturality-check-3.log`・`2g-perfect-cech-tuple-naturality-native.log`・`2g-perfect-cech-tuple-naturality-audit.log`。局所的な backward.isDefEq.respectTransparency false を使用、既定の資源制限。自然変換の暗黙の対象名 m,n を明示的に使っていないという linter 警告がある。追加公理・sorry・既存の型変更・200行超の宣言なし。共有鍵 --class impl --wait 3600、待ちは一つ、対象ビルドと監査は別枠。root・下流全ビルド・全体監査なし。

今回1モジュール73行＋入口1行。新規104モジュール本体6,879行・入口込み6,983行。既存追加25行を含む外枠計数は本体6,904行・入口込み7,008行。新規小監査累計690宣言、既存15宣言は別計上。次は同じ大域スカラーの増大写像をこの実際の図式へ自然に接続し、アフィン conerve と Frobenius 係数の比較、B1 の二重 Čech、Noether 帰納を進める。G4・G5 と停止点2g-2は未完。外枠16,000行は不変。

一覧：済み1／全体3（うち追加0）。


大域スカラーと同じ nerve の増大写像の準備（着手前、既存のスカラー・係数移送の法則の内数、70〜150行）：`schemeScalarHom_over` は v:X→Y と iX:X→SpecR、iY:Y→SpecR、v≫iY=iX から iX のスカラーが iY のスカラーの引き戻しであること。`schemeScalarPresheaf_primeCast` は p の R 上の零化から任意の Y→SpecR の全ての開の切断環での零化。`schemeCechNerveScalarHom_naturality` は元の augmentedCechNerve.hom の naturality に前者を渡した式。`schemeCechNervePresheaf_primeCast` は同じ実際の nerve の基底への射から各項の零化を供給する。

有限な添字の順序の補助（着手前、既存の有限集合の同型による移送の内数、20〜45行）：`cechFiniteIndexOrder α` は Fintype.equivFin による既存の順序の引き戻しを使い、toDecidableEq を元の DecidableEq α のままにする。`cechFiniteIndexOrder_decidableEq` はこの投影が元のものに等しいこと（定義上）。既存の LinearOrder を要求する増大写像・F8 の API の型は変更せず、同じ全タプル複体のインスタンスを保って使う。


同じ係数関手への増大写像の接続（着手前、既存の増大写像の単位・自然性の内数、65〜140行）：`schemePerfectCechTupleAugmentation f U p hp hR n` は同じ実際の nerve の基底への射と schemeScalarHom に沿う既存の増大写像を、同じタプル複体の零次へ渡す。全ての切断環の標数は schemeCechNervePresheaf_primeCast で元の R から供給し、新しい仮定にしない。`…_cycle` は既存の増大写像のサイクル性。`…_naturality` は元の nerve の増大射の自然性と refinedPullback の増大写像の自然性を、同じ被覆・同じ添字・同じ等号判定で渡した式。有限添字の順序は cechFiniteIndexOrder を使い、既存 API の型を変更しない。


同じ増大写像を複体と余単体図式へ渡す分割（着手前、既存の Mathlib の single と増大余単体の法則の内数、80〜170行）：`schemePerfectCechTupleAugmentationHom n` は既存の HomologicalComplex.mkHomFromSingle に上記の増大写像とサイクル性を渡した射。`…_f_zero` はその零次成分、`…_naturality` は同じ全ての nerve の射に自然であること。`schemePerfectCechTupleAugmented` は左辺を同じ R の Frobenius 順極限の次数零の single、右辺を検証済みの係数関手とする既存の CosimplicialObject.Augmented の値。B1 の積の増大図式や二重複体の完全性をこれだけで主張せず、同じ辺を四角形へ接続するための増大軸の供給である。


## G4：実際のスカラーと標数から、同じ係数関手の増大写像を供給する

`SchemeCechNerveScalars`（55行）：`schemeScalarHom_over` は基底への射を保つ写像の大域スカラーの自然性。`schemeScalarPresheaf_primeCast` は元の基底の標数から全ての開の切断環の標数を供給する。`schemeCechNervePresheaf_primeCast` は同じ実際の nerve の全項でのこの零化。`schemeCechNerveScalarHom_naturality` は既存の増大射の naturality による同じスカラーの自然性。

`CechFiniteIndexOrder`（33行）：`cechFiniteIndexOrder` は有限集合と Fin の同型に沿う順序の移送で、toDecidableEq を元のものに保つ。compare の整合性も DecidableEq の一意性で供給。`cechFiniteIndexOrder_decidableEq` は投影の定義上の一致。既存の API の型は変更しない。

`SchemePerfectCechTupleAugmentation`（66行）：`schemePerfectCechTupleAugmentation` は同じ実際の nerve の基底への射から、既存の増大写像を同じタプル複体の零次に渡す値。`…_cycle` は同じ複体のサイクルへ入ること。`…_naturality` は同じ全ての nerve の射に沿う自然性。各項の標数を追加仮定にせず、元の R の p の零化から供給し、等号判定も保持する。

単独検証、本体とのソース完全一致、対象と入口のビルド5,190・5,191・5,192ジョブ成功、小監査4・4・5宣言（計13、所有元の非公開・生成宣言を含む）・標準三公理のみ、終了状態0。ログ `2g-scheme-cech-nerve-scalars-check-1.log`・`2g-scheme-cech-nerve-scalars-native.log`、`2g-cech-finite-index-order-check-2.log`・`2g-cech-finite-index-order-native.log`、`2g-perfect-cech-tuple-augmentation-check-1.log`・`2g-perfect-cech-tuple-augmentation-native.log`、`2g-nerve-scalar-augmentation-audit.log`。局所的な backward.isDefEq.respectTransparency false を使用、既定の資源制限。simp/letI の style 警告がある。追加公理・sorry・既存の型変更・200行超の宣言なし。共有鍵 --class impl --wait 3600、待ちは一つ、対象ビルドと監査は別枠。root・下流全ビルド・全体監査なし。

今回3モジュール154行＋入口3行。新規107モジュール本体7,033行・入口込み7,140行。既存追加25行を含む外枠計数は本体7,058行・入口込み7,165行。新規小監査累計703宣言、既存15宣言は別計上。次の既存の single からの射と増大余単体図式は単独検証に成功したが、本体ビルド・監査前なのでこの束には含めない。B1 の二重 Čech・Noether 帰納と G5 は未完、外枠16,000行は不変。

一覧：済み1／全体3（うち追加0）。


基底環の射に沿う同じ増大写像の係数移送（着手前、既存の自然性・スカラーの合成則の内数、70〜145行）：`schemeCechNerveMapScalarHom_naturality f g F q hq n` は f:X→SpecS、g:Y→SpecR、F:Arrow.mk f→Arrow.mk g、hq:F.right=Spec.map q に対し、実際の mapCechNerve の n 次の大域スカラーの可換性。`schemePerfectCechTuplePullback_augmentation` は、その同じ実際の引き戻しの零次と R の増大写像の合成が、S の増大写像と実際の Frobenius 順極限の q の写像の合成に等しいこと。既存の refinedPullback の増大写像の自然性とスカラーの合成則を使い、閉中心への適用では q を同じ商の写像とする。基底の二つの標数の証人を保持し、Cartesian 性・平坦性・完全性を仮定しない。


増大軸を保つ同じ係数の引き戻し（着手前、既存の single・増大余単体の射の自然性の内数、70〜160行）：`schemePerfectCechTupleAugmentationHom_pullback` は R と S の二つの既存の single からの増大写像について、同じ実際の nerve の引き戻しと single に渡した Frobenius の q の写像が可換であること。零次成分の外延性と上の線形な係数移送を使う。`schemePerfectCechTupleAugmentedPullback` は left に既存の single.map の q、right に検証済みの係数関手の自然変換を持つ既存の CosimplicialObject.Augmented の射。w は同じ可換性の式。完全性や別の図式の同型を仮定しない。


## G4：同じ増大写像を複体の増大余単体図式へ渡す

`SchemePerfectCechTupleAugmented`（78行）の宣言：`schemePerfectCechTupleAugmentationHom` は既存の HomologicalComplex.mkHomFromSingle に同じ増大写像とサイクル性を渡した射。`…_f_zero` は同じ零次成分。`…_naturality` は同じ全ての nerve の射への自然性。`schemePerfectCechTupleAugmented` は左辺を同じ R の Frobenius 順極限の次数零 single、右辺を検証済みの係数関手とする既存の CosimplicialObject.Augmented の値。新しい single や二重複体の判定法は作っていない。

単独検証、本体とのソース完全一致、対象と入口のビルド5,193ジョブ成功、小監査11宣言（所有元の非公開・生成宣言を含む）・標準三公理のみ、終了状態0。ログ `2g-perfect-cech-tuple-augmented-check-2.log`・`2g-perfect-cech-tuple-augmented-native.log`・`2g-perfect-cech-tuple-augmented-audit.log`。局所的な backward.isDefEq.respectTransparency false を使用、既定の資源制限。追加公理・sorry・既存の型変更・200行超の宣言なし。共有鍵 --class impl --wait 3600、待ちは一つ、対象ビルドと監査は別枠。root・下流全ビルド・全体監査なし。

今回1モジュール78行＋入口1行。新規108モジュール本体7,111行・入口込み7,219行。既存追加25行を含む外枠計数は本体7,136行・入口込み7,244行。新規小監査累計714宣言、既存15宣言は別計上。基底環の射に沿う線形な増大写像の係数移送は単独検証に成功したが、本体ビルド・監査前なのでこの束には含めない。この増大余単体図式だけで B1 の二重図式の完全性や Noether 帰納を完成とせず、同じ基底・中心の増大軸の供給として扱う。G4・G5 は未完、外枠16,000行は不変。

一覧：済み1／全体3（うち追加0）。


## G4：基底環の射に沿う同じ増大写像の係数移送

`SchemePerfectCechTupleScalarPullback`（76行）の宣言：`schemeCechNerveMapScalarHom_naturality` は F.right=Spec.map q を保つ実際の mapCechNerve の各項の大域スカラーの可換性。`schemePerfectCechTuplePullback_augmentation` は同じ引き戻しの零次と R の増大写像の合成が、S の増大写像と実際の Frobenius 順極限の q の写像の合成に等しいこと。元の増大射・同じ被覆の逆像・同じ切断の写像を使い、Cartesian 性・平坦性・完全性は仮定しない。

単独検証、本体とのソース完全一致、対象と入口のビルド5,194ジョブ成功、小監査2宣言・標準三公理のみ、終了状態0。ログ `2g-perfect-cech-tuple-scalar-pullback-check-2.log`・`2g-perfect-cech-tuple-scalar-pullback-native.log`・`2g-perfect-cech-tuple-scalar-pullback-audit.log`。局所的な backward.isDefEq.respectTransparency false を使用、既定の資源制限。letI の style 警告がある。追加公理・sorry・既存の型変更・200行超の宣言なし。共有鍵 --class impl --wait 3600、待ちは一つ、対象ビルドと監査は別枠。root・下流全ビルド・全体監査なし。

今回1モジュール76行＋入口1行。新規109モジュール本体7,187行・入口込み7,296行。既存追加25行を含む外枠計数は本体7,212行・入口込み7,321行。新規小監査累計716宣言、既存15宣言は別計上。次の既存の増大余単体の射の値と single からの射の可換性は単独検証に成功したが、本体ビルド・監査前で、この束には含めない。G4・G5 は未完、外枠16,000行は不変。

一覧：済み1／全体3（うち追加0）。


## G4：基底の係数写像・同じ引き戻し・増大軸を保つ射

`SchemePerfectCechTupleAugmentedPullback`（66行）の宣言：`schemePerfectCechTupleAugmentationHom_pullback` は元の R と S の single からの同じ増大写像、既存の single.map に渡した実際の Frobenius の q の写像、同じ nerve の実際の引き戻しの可換性。零次成分の外延性と前束の線形な係数移送で示す。`schemePerfectCechTupleAugmentedPullback` は left に同じ single.map の q、right に検証済みの実際の係数関手の自然変換を持つ既存の CosimplicialObject.Augmented の射。w も同じ可換性から供給する。最終出力の型や仮定は変えていない。

単独検証、本体とのソース完全一致、対象と入口のビルド5,195ジョブ成功、小監査7宣言（所有元の非公開・生成宣言を含む）・標準三公理のみ、終了状態0。ログ `2g-perfect-cech-tuple-augmented-pullback-check-2.log`・`2g-perfect-cech-tuple-augmented-pullback-native.log`・`2g-perfect-cech-tuple-augmented-pullback-audit.log`。局所的な backward.isDefEq.respectTransparency false を使用、既定の資源制限。長い行の style 警告がある。追加公理・sorry・既存の型変更・200行超の宣言なし。共有鍵 --class impl --wait 3600、待ちは一つ、対象ビルドと監査は別枠。root・下流全ビルド・全体監査なし。

今回1モジュール66行＋入口1行。基準56ea849a3からの追加ファイルを独立に数え直し、新規110モジュール本体7,253行・入口込み7,363行で一致。既存追加25行を含む外枠計数は本体7,278行・入口込み7,388行。新規小監査累計723宣言、既存15宣言は別計上。

増大軸の整合性まで実際の写像でそろった。次は、この同じ被覆・実際の制限の射を F8 の四角形へ自然に渡し、同じ四角形の各項の完全性を B1 の二重 Čech に接続する。アフィン conerve と実際の Frobenius 係数の自然な比較、Noether 帰納、G5 の模型と filtered colimit への移送は残る。G4 の残りを約2,000〜4,000行、G5 を約1,000〜2,000行と見て、全体の着地を約10,000〜13,500行へ補正する。外枠16,000行は不変。条件付きの構成だけで Thm 2.9 の十分性や停止点2g-2の完成とは呼ばない。

一覧：済み1／全体3（うち追加0）。


同じ中心の細分した被覆への四角形の移送（着手前、既存の CechAugmentedSquare の細分・係数移送の法則の内数、105〜200行）：`schemeStructurePerfectCechRefinedSquare f q φ ψ hφ … U V ρ hρ` は既存の四角形のデータへ、C を Y の U、E を X の V の同じ Frobenius 係数の複体、restriction を実際の refinedPullback、基底・中心・商を元の環のものとして渡した値。完全性は仮定しない。`…_map` は元の逆像被覆の native な四角形から、left は恒等、right は同じ実際の細分、base・center は恒等の射。`…_acyclic_iff_of_eq` は同じ添字で V=f⁻¹U のとき、実際の等しい被覆の細分の同型と検証済みの cone の比較による全複体の完全性の同値。閉中心のタプル被覆の既存の等式へ適用して、同じ自然な係数図式に F8 を渡す。新しい四角形の概念や二重複体の判定法は作らない。


同じ nerve の係数と増大軸の四角形への代入（着手前、既存の四角形への係数移送の法則の内数、75〜150行）：`schemePerfectCechTupleSquare f g F q hq U p hp hR hS n` は同じ mapCechNerve の n 次、同じ二つのタプル被覆と実際のスカラーを上の refined な四角形の値へ渡す。`…_C`・`…_E` は検証済みの二つの係数複体との定義上の一致、`…_restriction` は実際の係数関手の引き戻しとの一致、`…_scalar`・`…_center` は検証済みの増大写像との一致、`…_quotient` は同じ Frobenius の q の写像との一致。これらを個別に示し、四角形全体や無関係な H の同型で自然性を代用しない。完全性を仮定しない。


同じ nerve の各項への F8 の適用（着手前、既存の F8 と有限ファイバー冪の底変換・係数移送の法則の内数、75〜160行）：`DegreeOneProjectiveModel.perfectCechTupleSquare_acyclic` は Noether R、同じ元の g の表示 m、全射性と中心外同型性、同じ閉基底 Spec(R/I^1) と Cartesian な Arrow の射 F、その元の有限アフィン被覆 U から、全ての n の同じ schemePerfectCechTupleSquare の全複体の完全性を返す。m.cechTerm、既存の有限冪の全射性・中心外同型性、mapCechNerve の Cartesian な底変換、同じタプル被覆のアフィン性・被覆性を供給し、前記の等しい中心被覆での四角形の比較を使う。各項の完全性・射影表示・表示先の幾何学的条件を仮定し直さない。


同じ四角形の nerve の射への自然性（着手前、既存の四角形の射・係数の自然性の内数、80〜160行）：`CechAugmentedSquare.Map.ext_components` は既存の射の left・right・base・center の四つの成分の一致から射全体の一致。辺の条件は証明の一意性で保たれる。`schemePerfectCechTupleSquare_map a` は left・right に検証済みの二つの係数関手の実際の a の写像、base・center に恒等を持つ同じ四角形の射。restriction は実際の引き戻しの自然性、scalar・center は検証済みの増大写像の自然性、quotient は同じ元の係数写像の恒等性から供給する。完全性を射の仮定にしない。


同じ四角形の全複体の余単体図式（着手前、既存の射の単位・合成と全複体への自然性の内数、55〜125行）：`schemePerfectCechTupleSquare_map_id` と `…_map_comp` は上の四つの成分の外延性と、検証済みの二つの係数関手の単位・合成則による同じ四角形の射の法則。`schemePerfectCechTupleSquareFunctor` は各項を同じ四角形の totalComplex、各射を既存の Map.totalComplexMap とする SimplexCategory 上の複体の関手。単位・合成の保存も既存の totalComplexMap_id/comp に渡す。B1 の比較そのものや最終出力の型の変更は行わない。


## G4：同じ中心の細分と、同じ nerve の四角形

`SchemePerfectCechRefinedSquare`（100行）：`schemeStructurePerfectCechRefinedSquare` は既存の四角形のデータに中心の細分した被覆と実際の refinedPullback を渡した値。`…_map` は元の逆像被覆から、left は恒等、right は同じ実際の細分、base・center は恒等で全ての辺を保つ射。`…_acyclic_iff_of_eq` は等しい中心の被覆の場合に、実際の細分の同型と検証済みの cone 比較による全複体の完全性の同値。Čech 版と原典との対応を docstring に明記。

`SchemePerfectCechTupleSquare`（70行）：`schemePerfectCechTupleSquare` は同じ nerve の実際の係数・二つのスカラー・商・引き戻しを、上の既存の四角形の値へ代入する。`…_C`・`…_E` は二つの同じ係数複体、`…_restriction` は同じ実際の引き戻し、`…_scalar`・`…_center` は検証済みの増大写像、`…_quotient` は同じ Frobenius の q の写像との定義上の一致。完全性は値の仮定に含めない。

単独検証、本体とのソース完全一致、対象と入口のビルド5,196・5,197ジョブ成功、小監査17・11宣言（計28、所有元の非公開・生成宣言を含む）・標準三公理のみ、終了状態0。ログ `2g-perfect-cech-refined-square-check-1.log`・`2g-perfect-cech-refined-square-native.log`、`2g-perfect-cech-tuple-square-check-1.log`・`2g-perfect-cech-tuple-square-native.log`、`2g-refined-and-tuple-square-audit.log`。局所的な backward.isDefEq.respectTransparency false を使用、既定の資源制限。追加公理・sorry・既存の型変更・200行超の宣言なし。共有鍵 --class impl --wait 3600、待ちは一つ、対象ビルドと監査は別枠。root・下流全ビルド・全体監査なし。

今回2モジュール170行＋入口2行。新規112モジュール本体7,423行・入口込み7,535行。既存追加25行を含む外枠計数は本体7,448行・入口込み7,560行。新規小監査累計751宣言、既存15宣言は別計上。次の各項の F8 の完全性と同じ四角形の射の自然性は単独検証に成功したが、本体ビルド・監査前でこの束には含めない。G4・G5 は未完、外枠16,000行は不変。

一覧：済み1／全体3（うち追加0）。


## G4：同じ可換な nerve の四角形の各項へ F8 を渡す

`DegreeOneProjectiveCechTupleAcyclic`（73行）：`DegreeOneProjectiveModel.perfectCechTupleSquare_acyclic` は Noether R、元の g の表示 m・全射性・中心外同型性、同じ Spec(R/I^1) と Cartesian な Arrow の射、元の有限アフィン被覆 U から、全ての n における同じ schemePerfectCechTupleSquare の全複体の完全性を返す。表示は m.cechTerm、幾何学的条件は既存の有限冪の法則、Cartesian square は既存の実際の mapCechNerve の底変換、アフィン被覆条件は同じタプル被覆の法則で供給する。中心の逆像被覆とタプル被覆の同じ等式に沿い、実際の四角形の射で移す。各項の完全性や射影表示を仮定し直さない。Čech 版と原典との対応を docstring に明記。

`SchemePerfectCechTupleSquareMap`（77行）：`CechAugmentedSquare.Map.ext_components` は四つの実際の成分の一致から既存の射全体の一致。`schemePerfectCechTupleSquare_map` は left・right に検証済みの二つの係数関手の写像、base・center に恒等を持ち、restriction は同じ実際の引き戻しの自然性、scalar・center は同じ増大写像の自然性、quotient は元の係数写像の恒等性による射。

`SchemePerfectCechTupleSquareFunctor`（59行）：`schemePerfectCechTupleSquare_map_id`・`…_map_comp` は同じ四つの成分の外延性と係数関手の単位・合成則による法則。`schemePerfectCechTupleSquareFunctor` は各項を同じ四角形の全複体、各射を既存の totalComplexMap に渡した SimplexCategory 上の複体の関手。単位・合成の保存にも既存の totalComplexMap_id/comp を使う。

単独検証、本体とのソース完全一致、対象と入口のビルド5,199・5,200ジョブ成功、小監査1・6・6宣言（計13、所有元の非公開・生成宣言を含む）・標準三公理のみ、終了状態0。ログ `2g-degree-one-projective-cech-tuple-acyclic-check-2.log`・`2g-perfect-cech-tuple-square-map-check-1.log`・`2g-termwise-f8-and-square-map-native.log`、`2g-perfect-cech-tuple-square-functor-check-1.log`・`2g-perfect-cech-tuple-square-functor-native.log`、`2g-termwise-f8-square-functor-audit.log`。局所的な backward.isDefEq.respectTransparency false を使用、既定の資源制限。letI の style 警告がある。追加公理・sorry・既存の型変更・200行超の宣言なし。共有鍵 --class impl --wait 3600、待ちは一つ、対象ビルドと監査は別枠。root・下流全ビルド・全体監査なし。

今回3モジュール209行＋入口3行。基準56ea849a3からの追加ファイルを独立に再計数し、新規115モジュール本体7,632行・入口込み7,747行で一致。既存追加25行を含む外枠計数は本体7,657行・入口込み7,772行。新規小監査累計764宣言、既存15宣言は別計上。

各項の完全性と同じ余単体図式の自然性がそろったが、これだけで原典の Thm 2.9 十分性や v 降下全体を完成とは呼ばない。次は実際のアフィン conerve と Frobenius の係数の自然な比較、B1 の二重 Čech の適用、実際の 2d のブローアップを保つ Noether 帰納へ接続する。G5 の模型・二つの filtered colimit への移送も残る。全体の見込み約10,000〜13,500行・外枠16,000行は不変。G4・G5 と停止点2g-2は未完。

一覧：済み1／全体3（うち追加0）。


同じ代数的環の順極限と圏論的余極限の比較（着手前、既存の順極限の普遍性・係数移送の法則の内数、65〜145行）：`ringDirectSystemFunctor f` は実際の自然数添字の環準同型の系 f を CommRingCat の同じ図式へ渡す。`ringDirectSystemCocone f` は既存の DirectLimit.Ring.of の余錐、`ringDirectSystemIsColimit f` は既存の DirectLimit.Ring.lift/hom_ext によるその余極限の普遍性。`ringDirectLimitColimitIso f` と `…_ι` は同じ環の圏論的余極限への標準同型と標準写像の一致。整数加群への忘却で代用せず、環の射として比較する。後で実際の Frobenius の矢印と conerve の余極限へ自然に渡す。


同じ環の順極限の比較の自然性（着手前、前記の比較の自然性の内数、50〜115行）：`ringDirectSystemNatTrans f g a ha` は実際の有向系の可換な環準同型を同じ CommRingCat の図式の自然変換にする。`ringDirectLimitColimitIso_naturality` は既存の ringDirectLimitComparison を使い、有限段からの標準写像との合成で比較同型の自然性を示す。代数的な順極限の射は既存の RingDirectLimitIntNaturality のものを再利用し、環の射を別に作り直さない。


Frobenius の既存の矢印の図式の端点の照合（着手前、既存の反復系の単位・合成・自然性の内数、80〜165行）：`frobeniusArrowDiagram_map_left`・`…_map_right` は既存の Functor.ofSequence の Frobenius の矢印の図式の任意の自然数段の射の二つの成分が、同じ frobeniusDirectSystemMap i j (leOfHom a) であること。NatTrans.ofSequence の単位成分と後続射だけの可換性から全ての射の自然性へ渡す。図式の定義・名前は変更せず、後の余錐と環の普遍性で実際の矢印を照合する。


同じ比較の有限段評価の分割（着手前、前記の自然性の内数）：`ringDirectLimitColimitIso_of f n x` は既存の標準写像との合成の等式を各元で評価した式。自然性を同じ有限段の元で照合し、環の図式の対象の定義を圏の式全体で同時に展開しない。


## G4：実際の環の順極限の余錐と標準比較

`RingDirectLimitCocone`（81行）の宣言：`ringDirectSystemFunctor` は実際の自然数添字の環の有向系の同じ図式。`ringDirectSystemCocone` は既存の DirectLimit.Ring.of の余錐。`ringDirectSystemIsColimit` は既存の環の lift・hom_ext の普遍性による余極限の証人。`ringDirectLimitColimitIso` は同じ環の圏論的余極限への標準同型、`…_ι` は同じ有限段からの標準写像の一致。加群への忘却で代用せず、環の射を保持している。Mathlib の既存の Ring.Colimits を明示 import して HasColimit を供給し、新しい存在の仮定は置かない。

単独検証、本体とのソース完全一致、対象と入口のビルド5,201ジョブ成功、小監査14宣言（所有元の非公開・生成宣言を含む）・標準三公理のみ、終了状態0。ログ `2g-ring-direct-limit-cocone-check-2.log`・`2g-ring-direct-limit-cocone-native.log`・`2g-ring-direct-limit-cocone-audit.log`。既定の透明性・資源制限で成功。追加公理・sorry・既存の型変更・200行超の宣言なし。共有鍵 --class impl --wait 3600、待ちは一つ、対象ビルドと監査は別枠。root・下流全ビルド・全体監査なし。

今回1モジュール81行＋入口1行。新規116モジュール本体7,713行・入口込み7,829行。既存追加25行を含む外枠計数は本体7,738行・入口込み7,854行。新規小監査累計778宣言、既存15宣言は別計上。環としての自然性は単独検証に成功したが本体ビルド・監査前で、この束には含めない。実際の Frobenius の矢印・conerve との比較、B1・Noether 帰納・G5 は残る。外枠16,000行は不変。

一覧：済み1／全体3（うち追加0）。


同じ Frobenius の矢印の順極限の普遍性（着手前、既存の環・矢印の余極限と添字の同値による移送の法則の内数、115〜230行）：`frobeniusArrowCocone` は点を実際の Arrow.mk(frobeniusDirectLimitMap f.hom)、脚を同じ二つの frobeniusDirectLimitOf とする既存の反復図式の余錐。`frobeniusArrowIsColimit` は両端の既存の環の lift/hom_ext でこの余錐の普遍性を返す。`frobeniusArrowSmallCocone`・`…SmallIsColimit` は既存の AsSmall の同値で同じ余錐を移し、`frobeniusArrowSmallColimitIso` は B1 が使う同じ小さい反復図式の余極限への標準同型。端点だけの加群同型で矢印の可換性を代用しない。


## G4：環の標準比較の自然性と、元の Frobenius の矢印の端点

`RingDirectLimitNaturality`（57行）：`ringDirectSystemNatTrans` は実際の環の有向系の射の自然変換。`ringDirectLimitColimitIso_of` は同じ有限段の標準写像との評価、`ringDirectLimitColimitIso_naturality` は既存の ringDirectLimitComparison と圏論的余極限の射の自然性。既存の代数的な射を作り直さない。

`FrobeniusArrowDiagramMaps`（80行）：`frobeniusArrowDiagram_map_left`・`…_map_right` は既存の Functor.ofSequence の任意の自然数段の写像の端点と、同じ frobeniusDirectSystemMap の一致。後続射だけを照合する NatTrans.ofSequence から全ての段へ渡す。元の図式の定義・名前・型は変更しない。

単独検証、本体とのソース完全一致、対象と入口のビルド5,202・5,203ジョブ成功、小監査4・3宣言（計7、実際の所有元による生成・非公開宣言込み）・標準三公理のみ、終了状態0。ログ `2g-ring-direct-limit-naturality-check-2.log`・`2g-ring-direct-limit-naturality-native.log`、`2g-frobenius-arrow-diagram-maps-check-3.log`・`2g-frobenius-arrow-diagram-maps-native.log`、`2g-ring-naturality-arrow-maps-audit.log`。局所的な backward.isDefEq.respectTransparency false、既定の資源制限。行長の style 警告あり。追加公理・sorry・既存の型変更・200行超の宣言なし。共有鍵 --class impl --wait 3600、待ちは一つ、対象ビルドと小監査は別枠。root・下流全ビルド・全体監査なし。

今回2モジュール137行＋入口2行。新規118モジュール本体7,850行・入口込み7,968行。既存追加25行を含む外枠計数は本体7,875行・入口込み7,993行。新規小監査累計785宣言、既存15宣言は別計上。矢印全体の余錐は下書きの検証中でこの束には含めない。G4の実際の conerve 比較・B1・Noether帰納、G5は残る。全体の見込み約10,000〜13,500行・外枠16,000行は不変。

一覧：済み1／全体3（うち追加0）。


実際の Frobenius の矢印への完全性の移送（着手前、既存の filtered colimit と同型の自然な移送の法則の内数、40〜100行）：`isCechExact_frobeniusDirectLimit_of_faithfullyFlat` は元の Under の忠実平坦な射と標数条件から、実際の frobeniusDirectLimitMap の Arrow の IsCechExact を返す。上の標準同型を既存の augmentedCechConerve 関手で写し、B1 の ringCechExact_iff_of_iso と既存の同じ図式の余極限の完全性を使う。`…_baseChange_…` は元の任意の底変換の同じ射への適用。最終出力の型や Čech 完全性の定義は変更しない。


## G4：実際の Frobenius の矢印の余極限

`FrobeniusArrowCocone`（124行）：`frobeniusArrowCocone` は実際の frobeniusDirectLimitMap の矢印を点とし、両端の同じ有限段の標準写像を脚とする元の反復図式の余錐。`frobeniusArrowIsColimit` は環の lift・hom_ext と、脚の実際の可換な四角形からこの余錐の普遍性を返す。`frobeniusArrowSmallCocone`・`frobeniusArrowSmallIsColimit` は同じ余錐を既存の AsSmall の同値で移す。`frobeniusArrowSmallColimitIso` は実際の矢印と、B1 が使う同じ図式の圏論的余極限との標準同型。端点の加群同型だけではなく矢印全体の同型。

単独検証、本体とのソース完全一致、対象と入口のビルド5,204ジョブ成功、小監査18宣言（実際の所有元による生成・非公開宣言込み）・標準三公理のみ、終了状態0。ログ `2g-frobenius-arrow-cocone-check-2.log`・`2g-frobenius-arrow-cocone-native.log`・`2g-frobenius-arrow-cocone-audit.log`。局所的な backward.isDefEq.respectTransparency false、既定の資源制限。letIの style 警告あり。追加公理・sorry・既存の型変更・200行超の宣言なし。共有鍵 --class impl --wait 3600、待ちは一つ、対象ビルドと小監査は別枠。root・下流全ビルド・全体監査なし。

今回1モジュール124行＋入口2行（空行込み）。新規119モジュール本体7,974行・モジュール登録119行込み8,093行。既存追加25行を含む外枠計数は本体7,999行・登録込み8,118行。新規小監査累計803宣言、既存15宣言は別計上。追加の空行は登録行とは別で、数学の行数には含めない。次の実際の射への完全性の移送は未検証の下書きで、この束には含めない。標準比較の自然性と conerve への接続、B1・Noether帰納・G5は残る。見込み約10,000〜13,500行・外枠16,000行は不変。

一覧：済み1／全体3（うち追加0）。


同じ矢印の標準比較の自然性（着手前、既存の Frobenius の射・余極限の自然性の法則の内数、130〜250行）：`frobeniusDirectLimitArrowMap F` は元の可換な四角形 F の両端の同じ frobeniusDirectLimitMap からなる矢印の射。`frobeniusArrowDiagramMap F` と `frobeniusArrowSmallDiagramMap F` は元の各有限段の同じ F の自然変換。`frobeniusArrowSmallColimitIso_ι` は同じ標準脚の保存、`frobeniusArrowCocone_map` は脚と F の可換性、`frobeniusArrowSmallColimitIso_naturality` は実際の矢印の写像と、同じ図式の colim.map を標準同型が結ぶこと。端点の同型だけで代用せず、元の可換な四角形を保つ。個々の宣言は200行以内の予定。


同じ増大 conerve への比較の移送（着手前、前記の標準比較の自然性の内数、40〜90行）：`frobeniusAugmentedConerveColimitIso` は実際の frobeniusDirectLimitMap の増大 conerve と、元の矢印の反復図式の余極限の増大 conerve の標準同型。既存の augmentedCechConerve.mapIso に上の矢印の標準同型を渡すだけで、余極限の保存を別に定義し直さない。`…_naturality` は元の四角形 F の実際の増大 conerve の写像と、同じ colim.map の増大 conerve の写像が標準同型と可換なこと。増大項と全ての次数の自然性を同じ関手で保つ。


## G4：忠実平坦な射の実際の Frobenius 順極限の Čech 完全性

`FrobeniusDirectLimitCechExact`（48行）：`isCechExact_frobeniusDirectLimit_of_faithfullyFlat` は元の忠実平坦な Under の射から、実際の frobeniusDirectLimitMap の増大 Čech 完全性を返す。元の Arrow の余極限の完全性を、矢印全体の標準同型と既存の augmentedCechConerve 関手、B1 の ringCechExact_iff_of_iso で移す。`isCechExact_frobeniusDirectLimit_baseChange_of_faithfullyFlat` は元の任意の底変換の同じ射への適用。Frobenius 順極限の標準脚と環準同型を保つ。最終の AugmentedRingCechExact の型・定義や利用側の型は変更しない。

単独検証、本体とのソース完全一致、対象と入口のビルド5,205ジョブ成功、小監査3宣言（実際の所有元による生成・非公開宣言込み）・標準三公理のみ、終了状態0。ログ `2g-frobenius-direct-limit-cech-exact-check-2.log`・`2g-frobenius-direct-limit-cech-exact-native.log`・`2g-frobenius-direct-limit-cech-exact-audit.log`。既定の透明性・資源制限。letIの style 警告あり。追加公理・sorry・既存の型変更・200行超の宣言なし。共有鍵 --class impl --wait 3600、待ちは一つ、対象ビルドと小監査は別枠。root・下流全ビルド・全体監査なし。

今回1モジュール48行＋入口1行。基準56ea849a3から追加の本体を独立に再計数し、新規120モジュール本体8,022行。既存追加25行を含む外枠計数は本体8,047行・登録120行込み8,167行。新規小監査累計806宣言、既存15宣言は別計上。元の四角形と同じ conerve への標準比較の自然性は未検証の下書きで、この束には含めない。G4の二重 Čech・Noether帰納、G5は残る。見込み約10,000〜13,500行・外枠16,000行は不変。

一覧：済み1／全体3（うち追加0）。


## G4：元の可換な四角形に自然な、実際の矢印の標準比較

`FrobeniusArrowNaturality`（103行）の宣言：`frobeniusDirectLimitArrowMap` は元の F の両端の同じ順極限写像からなる可換な矢印の射。`frobeniusArrowDiagramMap`・`frobeniusArrowSmallDiagramMap` は同じ F を各有限段に置く自然変換。`frobeniusArrowSmallColimitIso_ι` は同じ標準脚の保存。`frobeniusArrowCocone_map` は標準脚と実際の順極限写像の可換性。`frobeniusArrowSmallColimitIso_naturality` は元の四角形による実際の矢印の射と、同じ colim.map を標準同型が結ぶこと。両端の同型を独立に選ぶのでなく、矢印全体の余極限の普遍性で照合した。

単独検証、本体とのソース完全一致、対象と入口のビルド5,206ジョブ成功、小監査12宣言（実際の所有元による生成・非公開宣言込み）・標準三公理のみ、終了状態0。ログ `2g-frobenius-arrow-naturality-check-2.log`・`2g-frobenius-arrow-naturality-native.log`・`2g-frobenius-arrow-naturality-audit.log`。局所的な backward.isDefEq.respectTransparency false、既定の資源制限。letIの style 警告あり。追加公理・sorry・既存の型変更・200行超の宣言なし。共有鍵 --class impl --wait 3600、待ちは一つ、対象ビルドと小監査は別枠。root・下流全ビルド・全体監査なし。

今回1モジュール103行＋入口1行。新規121モジュール本体8,125行。既存追加25行を含む外枠計数は本体8,150行・登録121行込み8,271行。新規小監査累計818宣言、既存15宣言は別計上。増大 conerve への同じ自然性の移送は下書きの検証中で、この束には含めない。G4の二重 Čech・Noether帰納、G5は残る。見込み約10,000〜13,500行・外枠16,000行は不変。

一覧：済み1／全体3（うち追加0）。


同じ増大係数図式の二重複体への代入（着手前、既存の augmentedCochain 関手と係数移送の法則の内数、65〜130行）：`schemePerfectCechTupleDouble` は検証済みの schemePerfectCechTupleAugmented に B1 の既存の augmentedCochain をそのまま適用した複体の複体。`…_zero`・`…_succ` は同じ基底の single と同じタプル複体の各項、`…_horizontal` は同じ増大・交代余面微分、`…_comm` は元の複体の射の comm による二方向の可換性。`schemePerfectCechTupleDoublePullback` は検証済みの同じ AugmentedPullback を同じ関手で写し、`…_zero`・`…_succ` は既存の同じ基底環の写像と各次数の実際の係数写像との一致。新しい水平複体や二重複体の判定法は作らず、完全性も仮定しない。


## G4：同じ増大 conerve の自然な標準比較

`FrobeniusAugmentedConerveComparison`（43行）：`frobeniusAugmentedConerveColimitIso` は実際の frobeniusDirectLimitMap の増大 conerve と、元の矢印の反復図式の余極限の増大 conerve の標準同型。`frobeniusAugmentedConerveColimitIso_naturality` は元の四角形 F の実際の増大 conerve の写像と、同じ colim.map の増大 conerve の写像が標準同型と可換なこと。検証済みの矢印の同型・自然性を既存の同じ関手で写し、増大項と全ての次数の自然性を同時に保持する。各係数の同型を独立に選ぶ方法や、被覆ごとの H の同型だけで代用しない。

単独検証、本体とのソース完全一致、対象と入口のビルド5,207ジョブ成功、小監査8宣言（実際の所有元による生成・非公開宣言込み）・標準三公理のみ、終了状態0。ログ `2g-frobenius-augmented-conerve-comparison-check-1.log`・`2g-frobenius-augmented-conerve-comparison-native.log`・`2g-frobenius-augmented-conerve-comparison-audit.log`。既定の透明性・資源制限。letIの style 警告あり。追加公理・sorry・既存の型変更・200行超の宣言なし。共有鍵 --class impl --wait 3600、待ちは一つ、対象ビルドと小監査は別枠。root・下流全ビルド・全体監査なし。

今回1モジュール43行＋入口1行。新規122モジュール本体8,168行。既存追加25行を含む外枠計数は本体8,193行・登録122行込み8,315行。新規小監査累計826宣言、既存15宣言は別計上。これは実際の矢印の増大 conerve への比較であり、各テンソル環の Frobenius 系との照合やスキームの二重 Čech の完成まで主張しない。G4の二重 Čech・Noether帰納、G5は残る。見込み約10,000〜13,500行・外枠16,000行は不変。

一覧：済み1／全体3（うち追加0）。


同じ conerve の有限段の Frobenius の照合（着手前、既存の有限余積の普遍性と係数の自然性の内数、60〜140行）：`frobeniusConerve_primeCast f p hA n` は同じ widePushout の head の環準同型から、各 conerve の環で p が零であることを供給する。`frobeniusConerve_step f p hp hA hB n` は元の frobeniusArrowStep が誘導する mapCechConerve の n 次が、その同じ環の frobeniusDirectSystemMap 0 1 と一致すること。実際の head と全ての脚で WidePushout.hom_ext により照合する。有限テンソル環や同型を新たに選ばず、零環も除外しない。これを各段の図式の比較に渡すのは後続の自然性の法則として別に扱う。


## G4：同じ実際の増大係数図式を B1 の二重複体へ渡す

`SchemePerfectCechTupleDouble`（79行）：`schemePerfectCechTupleDouble` は同じ実際の増大係数図式へ B1 の既存の augmentedCochain を適用した複体の複体。`…_zero` は同じ基底の single、`…_succ` は同じ nerve のタプル係数複体、`…_horizontal` は既存の増大・交代余面微分、`…_comm` は同じ複体の射の comm による二方向の可換性。`schemePerfectCechTupleDoublePullback` は既存の同じ増大係数の引き戻しを同じ関手で写した射。`…Pullback_zero`・`…Pullback_succ` は元の係数環の実際の Frobenius の写像と同じタプル係数の写像の保持。新しい水平複体や二重複体の判定法は作らず、完全性も仮定していない。

単独検証、本体とのソース完全一致、対象と入口のビルド5,208ジョブ成功、小監査9宣言（実際の所有元による生成・非公開宣言込み）・標準三公理のみ、終了状態0。ログ `2g-perfect-cech-tuple-double-check-2.log`・`2g-perfect-cech-tuple-double-native.log`・`2g-perfect-cech-tuple-double-audit.log`。既定の透明性・資源制限。行長の style 警告あり。追加公理・sorry・既存の型変更・200行超の宣言なし。共有鍵 --class impl --wait 3600、待ちは一つ、対象ビルドと小監査は別枠。root・下流全ビルド・全体監査なし。

今回1モジュール79行＋入口1行。基準56ea849a3から独立に再計数し、新規123モジュール本体8,247行。既存追加25行を含む外枠計数は本体8,272行。登録123行込み8,395行に加え、入口の追加の空行21行も全て含める保守的な物理行数は **8,416行**。従来の「登録込み」は各モジュール1行のimportの計数だったため、入口の空行をこの段で別に明示し、今後は外枠に含める。入口の二重importは0。新規小監査累計835宣言、既存15宣言は別計上。

各 conerve の有限余積の Frobenius の照合は未検証の下書きにあり、この束には含めない。G4の実際のアフィン比較・二重 Čech の完全性の判定・Noether帰納、G5は残る。全体の見込み約10,000〜13,500行・外枠16,000行は不変。

一覧：済み1／全体3（うち追加0）。


同じ conerve の反復図式への比較（着手前、既存の有限段・余極限の比較の自然性の内数、120〜300行）：`frobeniusConerveRingDiagramIso … n` は、同じ conerve の n 次の環の ringDirectSystemFunctor と、元の frobeniusArrowDiagram に既存の cechConerve 関手と n 次の評価を合成した図式との標準同型。各対象の成分は恒等、後続射は上の frobeniusConerve_step、任意の段は NatTrans.ofSequence による自然性から供給する。同じ n の射についても実際の conerve の環準同型の自然性を保持する。これを既存の conerve 関手の余極限保存と環・整数加群の標準比較で移す。係数ごとの任意の同型を新たに選ぶ方式にはしない。増大軸も同じ基底からの標準脚で照合し、最終の出力や利用側の型は変更しない。個々の宣言は200行以内の予定。


## G4：conerve の同じ有限余積上の Frobenius

`FrobeniusConerveStep`（59行）：`frobeniusConerve_primeCast` は同じ conerve の各環で p が零であることを、元の基底からの実際の WidePushout.head の環準同型で供給する。`frobeniusConerve_step` は元の frobeniusArrowStep が誘導する mapCechConerve の n 次が、同じ有限余積の環の frobeniusDirectSystemMap 0 1 と一致すること。実際の head と全ての脚で WidePushout.hom_ext と既存の Frobenius の自然性を使う。零環・空のスキームを除外しない。

単独検証、本体とのソース完全一致、対象と入口のビルド5,209ジョブ成功、小監査3宣言（実際の所有元による生成・非公開宣言込み）・標準三公理のみ、終了状態0。ログ `2g-frobenius-conerve-step-check-2.log`・`2g-frobenius-conerve-step-native.log`・`2g-frobenius-conerve-step-audit.log`。局所的な backward.isDefEq.respectTransparency false、既定の資源制限。追加公理・sorry・既存の型変更・200行超の宣言なし。共有鍵 --class impl --wait 3600、待ちは一つ、対象ビルドと小監査は別枠。root・下流全ビルド・全体監査なし。

今回1モジュール59行＋入口1行。新規124モジュール本体8,306行。既存追加25行を含む外枠計数は本体8,331行・登録124行と入口の追加空行21行を全て含めて **8,476行**。新規小監査累計838宣言、既存15宣言は別計上。次の同じ反復図式への標準比較は型を前節に記録したが、未実装。G4の実際のアフィン比較・二重 Čech の完全性の判定・Noether帰納、G5は残る。見込み約10,000〜13,500行・外枠16,000行は不変。停止点2g-2の完成とは呼ばない。

一覧：済み1／全体3（うち追加0）。


同じ反復図式の次数に対する自然性の分割（着手前、前記120〜300行の内数）：`frobeniusConerveRingSystemMap a` は実際の conerve の射の環準同型を既存の ringDirectSystemNatTrans に渡したもの。`frobeniusConerveRingDiagramIso_naturality a` はその射と、元の conerve の n 次の評価関手の自然変換が上の恒等成分の標準比較と可換なこと。`frobeniusConerveRingColimitIso n` は同じ実際の環の順極限と、元の矢印から評価した図式の余極限の標準同型。有限段の脚を保つ式 `…_ι`・`…_of` と、実際の Frobenius 順極限の写像に対する `…_naturality` を、同じ標準脚と既存の colimit.ι_map で示す。


## G4：同じ conerve の反復図式の標準比較

`FrobeniusConerveRingDiagram`（61行）：`frobeniusConerveRingDiagramIso` は各 conerve の同じ環の Frobenius 有向系と、元の矢印の反復図式を同じ次数で評価した環の図式の標準同型。成分は全て元の環の恒等射。後続射は検証済みの frobeniusConerve_step と実際の冪の式で照合し、任意の段へは NatTrans.ofSequence の自然性で渡す。`frobeniusConerveRingDiagramIso_hom_app` はその恒等成分との一致。

単独検証、本体とのソース完全一致、対象と入口のビルド5,210ジョブ成功、小監査7宣言（実際の所有元による生成・非公開宣言込み）・標準三公理のみ、終了状態0。ログ `2g-frobenius-conerve-ring-diagram-check-3.log`・`2g-frobenius-conerve-ring-diagram-native.log`・`2g-frobenius-conerve-ring-diagram-audit.log`。局所的な backward.isDefEq.respectTransparency false、既定の資源制限。unused simp の style 警告あり。追加公理・sorry・既存の型変更・200行超の宣言なし。共有鍵 --class impl --wait 3600、待ちは一つ、対象ビルドと小監査は別枠。root・下流全ビルド・全体監査なし。

今回1モジュール61行＋入口1行。新規125モジュール本体8,367行、既存追加25行を含む本体8,392行。登録125行・入口の追加空行21行を全て含む外枠計数 **8,538行**。新規小監査累計845宣言、既存15宣言は別計上。次数に対する自然性と余極限への同じ比較は下書きで、この束には含めない。G4・G5は未完。見込み約10,000〜13,500行・外枠16,000行は不変。

一覧：済み1／全体3（うち追加0）。


同じ実際の矢印の conerve への余極限の比較（着手前、既存の conerve の余極限保存と標準比較の法則の内数、100〜220行）：`frobeniusConerveCocone n` は検証済みの実際の矢印の余錐を、既存の cechConerve と n 次の評価で写した余錐。`frobeniusConerveIsColimit n` は同じ増大 conerve の随伴と既存の忘却・評価の余極限保存からその普遍性を供給する。`frobeniusConervePerfectIso n` は同じ環の Frobenius 順極限から、実際の frobeniusDirectLimitMap の conerve の n 次の環への標準同型。`…_ι`・`…_of` は元の矢印の有限段の標準脚を保つ式、`…_naturality` と `…_augmentation` は元の次数の射と基底からの実際の増大写像を保つ式。既存の写像の自然性の分割であり、出力型や幾何学的仮定は変更しない。反復図式から実際の conerve への比較全体は、これらの分割を合わせ約300〜500行の見込みへ具体化する。段全体の見込み・外枠は変えない。


## G4：同じ反復図式の比較の、conerve の次数に対する自然性

`FrobeniusConerveRingNaturality`（47行）：`frobeniusConerveRingSystemMap` は元の conerve の環準同型を、既存の ringDirectSystemNatTrans に渡した同じ有向系の射。`frobeniusConerveRingDiagramIso_naturality` は、元の次数の射と、同じ評価関手の自然変換が、前記の恒等成分の標準比較と可換なこと。元の面・退化写像を保ち、既存の図式や型は変更しない。

単独検証、本体とのソース完全一致、対象と入口のビルド5,211ジョブ成功、小監査5宣言（実際の所有元による生成・非公開宣言込み）・標準三公理のみ、終了状態0。ログ `2g-frobenius-conerve-ring-naturality-check-1.log`・`2g-frobenius-conerve-ring-naturality-native.log`・`2g-frobenius-conerve-ring-naturality-audit.log`。局所的な backward.isDefEq.respectTransparency false、既定の資源制限。letIの style 警告あり。追加公理・sorry・既存の型変更・200行超の宣言なし。共有鍵 --class impl --wait 3600、待ちは一つ、対象ビルドと小監査は別枠。root・下流全ビルド・全体監査なし。

今回1モジュール47行＋入口1行。新規126モジュール本体8,414行、既存追加25行を含む本体8,439行。登録126行・入口の追加空行21行を全て含む外枠計数 **8,586行**。新規小監査累計850宣言、既存15宣言は別計上。余極限と実際の conerve への比較は下書きで、この束には含めない。G4・G5は未完。見込み約10,000〜13,500行・外枠16,000行は不変。

一覧：済み1／全体3（うち追加0）。


## G4：同じ conerve の環の順極限と、実際の矢印の余錐の普遍性

`FrobeniusConerveRingColimit`（96行）：`frobeniusConerveRingColimitIso` は同じ係数環の実際の Frobenius 順極限と、元の矢印の図式を同じ次数で評価した余極限との標準同型。`…_ι` は同じ各有限段の標準脚の保存、`…_of` は各元での評価。`…_naturality` は実際の conerve の環準同型に対する同じ比較の自然性で、元の有限段の脚と colimit.ι_map により示す。

`FrobeniusConerveCocone`（43行）：`frobeniusConerveCocone` は検証済みの実際の矢印の余錐を、同じ conerve の n 次へ写した余錐。`frobeniusConerveIsColimit` は既存の増大 conerve の随伴、忘却・評価の余極限保存を使い、その同じ余錐の普遍性を供給する。忘却の Comma.snd の保存を明示し、存在を新たな仮定にしない。

単独検証、本体とのソース完全一致、対象2本と入口のビルド5,213ジョブ成功、小監査11・5宣言（計16、実際の所有元による生成・非公開宣言込み）・標準三公理のみ、終了状態0。ログ `2g-frobenius-conerve-colimit-cocone-check-2.log`・`2g-frobenius-conerve-colimit-cocone-native.log`・`2g-frobenius-conerve-colimit-cocone-audit.log`。局所的な backward.isDefEq.respectTransparency false、既定の資源制限。追加公理・sorry・既存の型変更・200行超の宣言なし。共有鍵 --class impl --wait 3600、待ちは一つ、対象ビルドと小監査は別枠。root・下流全ビルド・全体監査なし。

今回2モジュール139行＋入口2行。新規128モジュール本体8,553行、既存追加25行を含む本体8,578行。登録128行・入口の追加空行21行を全て含む外枠計数 **8,727行**。新規小監査累計866宣言、既存15宣言は別計上。次の実際の conerve への標準比較と増大の保存は下書きで、この束には含めない。G4・G5は未完。見込み約10,000〜13,500行・外枠16,000行は不変。

一覧：済み1／全体3（うち追加0）。


同じ Frobenius の係数の増大環図式への代入（着手前、既存の係数移送・同型の法則の内数、120〜220行）：`frobeniusRingConerve` は同じ元の conerve の各環の Frobenius 順極限と実際の環準同型を環の余単体図式にまとめたもの。`frobeniusAugmentedRingCoefficients` は同じ基底の順極限と元の head の順極限写像による増大。`frobeniusRingConerveIso`・`frobeniusAugmentedRingCoefficientsIso` は検証した同じ各次数の標準比較と増大の可換性を自然同型にまとめる。`frobeniusAugmentedRingCoefficients_exact_iff` は B1 の ringCechExact_iff_of_iso による同じ増大図式の完全性の同値。`…_exact_of_faithfullyFlat` と元の任意の底変換での版は、既存の実際の矢印の完全性をこの同じ比較で戻す。新しい完全性の定義・型を追加せず、同じ AugmentedRingCechExact を使う。完全性や比較を最終出力の追加仮定にしない。


## G4：実際の Frobenius の矢印の conerve への自然な比較

`FrobeniusConervePerfectIso`（57行）：`frobeniusConervePerfectIso` は同じ conerve の各環の実際の Frobenius 順極限と、実際の frobeniusDirectLimitMap の conerve の環との標準同型。二つの検証済みの同じ余極限の比較を合成する。`…_ι` は元の矢印の各有限段の標準脚の conerve の射を保つ式、`…_of` はその各元での評価。

`FrobeniusConervePerfectNaturality`（73行）：`frobeniusConervePerfectIso_naturality` は元の conerve の全ての次数の射との自然性。`frobeniusConervePerfectIso_augmentation` は元の基底の実際の Frobenius 順極限からの増大写像との可換性。同じ有限段の標準脚で、元の conerve の自然性と増大の可換性を評価して示す。独立な各係数の同型だけで代用しない。

単独検証、本体とのソース完全一致、対象2本と入口のビルド5,215ジョブ成功、小監査13・2宣言（計15、実際の所有元による生成・非公開宣言込み）・標準三公理のみ、終了状態0。ログ `2g-frobenius-conerve-perfect-comparison-check-1.log`・`2g-frobenius-conerve-perfect-comparison-native.log`・`2g-frobenius-conerve-perfect-comparison-audit.log`。局所的な backward.isDefEq.respectTransparency false、既定の資源制限。追加公理・sorry・既存の型変更・200行超の宣言なし。共有鍵 --class impl --wait 3600、待ちは一つ、対象ビルドと小監査は別枠。root・下流全ビルド・全体監査なし。

今回2モジュール130行＋入口2行。新規130モジュール本体8,683行、既存追加25行を含む本体8,708行。登録130行・入口の追加空行21行を全て含む外枠計数 **8,859行**。新規小監査累計881宣言、既存15宣言は別計上。同じ係数を増大環図式としてまとめた値と、その忠実平坦な完全性への適用は下書きで、この束には含めない。G4のスキームのアフィン比較・二重 Čech の完全性の判定・Noether帰納、G5は残る。見込み約10,000〜13,500行・外枠16,000行は不変。

一覧：済み1／全体3（うち追加0）。


同じ標準比較の元の矢印の射に対する自然性（着手前、既存の係数移送・自然性の内数、65〜140行）：`frobeniusConervePerfectIso_arrow_naturality F` は元の環の可換な四角形 F:f→g に対し、同じ元の mapCechConerve F の各環の Frobenius 順極限写像と、同じ実際の frobeniusDirectLimitArrowMap F の conerve の射を、上の標準比較が結ぶこと。既存の frobeniusArrowCocone_map を同じ conerve 関手で写し、同じ有限段の脚で評価する。これにより次数の自然性だけでなく、後続の有限型模型の射・filtered な図式の射にも標準比較を渡す。出力型や範囲は変更しない。


## G4：同じ増大環図式への係数比較と、忠実平坦な完全性の接続

`FrobeniusAugmentedRingCoefficients`（136行）の宣言：`frobeniusRingConerve` は元の conerve の各環の実際の Frobenius 順極限と同じ環準同型の余単体図式。`frobeniusAugmentedRingCoefficients` は同じ基底の順極限と元の head の順極限写像による増大環図式。`frobeniusRingConerveIso`・`frobeniusAugmentedRingCoefficientsIso` は検証した同じ標準比較と増大の可換性を余単体・増大図式の自然同型にまとめる。`frobeniusAugmentedRingCoefficients_exact_iff` は B1 の既存の同型不変性による、同じ AugmentedRingCechExact と実際の順極限の矢印の IsCechExact の同値。`frobeniusAugmentedRingCoefficients_exact_of_faithfullyFlat` は忠実平坦な元のアフィン射の係数の増大 Čech 完全性。`frobeniusAugmentedRingCoefficients_exact_baseChange_of_faithfullyFlat` は元の任意の底変換の同じ係数の完全性。新しい完全性の定義は導入しない。

単独検証、本体とのソース完全一致、対象と入口のビルド5,216ジョブ成功、小監査20宣言（実際の所有元による生成・非公開宣言込み）・標準三公理のみ、終了状態0。ログ `2g-frobenius-augmented-ring-coefficients-check-1.log`・`2g-frobenius-augmented-ring-coefficients-native.log`・`2g-frobenius-augmented-ring-coefficients-audit.log`。局所的な backward.isDefEq.respectTransparency false、既定の資源制限。letIの style 警告あり。追加公理・sorry・既存の型変更・200行超の宣言なし。共有鍵 --class impl --wait 3600、待ちは一つ、対象ビルドと小監査は別枠。root・下流全ビルド・全体監査なし。

今回1モジュール136行＋入口1行。基準56ea849a3から独立に再計数し、新規131モジュール本体8,819行。既存追加25行を含む本体8,844行、入口の追加152行（登録131・空行21）を全て含む外枠計数 **8,996行**。新規小監査累計901宣言、既存15宣言は別計上。

アフィンな忠実平坦な射と元の任意の底変換について、実際の元の conerve の各環の Frobenius 係数の増大完全性へ到達した。スキームの任意の有限アフィン被覆との自然な比較・非アフィンの proper fppf の二重 Čech・Noether帰納、G5の実際の模型と二つの filtered な移送はなお残る。この束だけで Thm 2.9 十分性や停止点2g-2の完成とは呼ばない。元の四角形に対する係数比較の自然性は下書きの検証中。見込み約10,000〜13,500行・外枠16,000行は不変。

一覧：済み1／全体3（うち追加0）。


## G4：同じ標準比較の、元の環の可換な四角形に対する自然性

`FrobeniusConerveArrowNaturality`（57行）：`frobeniusConervePerfectIso_arrow_naturality` は元の可換な四角形 F:f→g について、同じ元の mapCechConerve F の各環の実際の Frobenius 順極限写像と、同じ実際の frobeniusDirectLimitArrowMap F の conerve の射を、標準比較が結ぶこと。既存の frobeniusArrowCocone_map を同じ conerve 関手で写し、各有限段の同じ脚で評価する。模型の射や filtered な図式の射への比較に使う。次数だけの自然性を、元の矢印の射の自然性と取り違えない。

単独検証、本体とのソース完全一致、対象と入口のビルド5,217ジョブ成功、小監査1宣言（実際の所有元による非公開・生成宣言の有無も走査）・標準三公理のみ、終了状態0。ログ `2g-frobenius-conerve-arrow-naturality-check-1.log`・`2g-frobenius-conerve-arrow-naturality-native.log`・`2g-frobenius-conerve-arrow-naturality-audit.log`。局所的な backward.isDefEq.respectTransparency false、既定の資源制限。letIの style 警告あり。追加公理・sorry・既存の型変更・200行超の宣言なし。共有鍵 --class impl --wait 3600、待ちは一つ、対象ビルドと小監査は別枠。root・下流全ビルド・全体監査なし。

今回1モジュール57行＋入口1行。新規132モジュール本体8,876行。既存追加25行を含む本体8,901行、登録132行・入口の追加空行21行を全て含む外枠計数 **9,054行**。新規小監査累計902宣言、既存15宣言は別計上。

## 残りの規模の見込みの更新（2026-11-16、9,054行時点）

環の conerve と各係数環の Frobenius 系・標準脚・増大・次数と元の四角形の自然性、および同じ増大環図式の忠実平坦な完全性の接続まで検証済み。残りを具体化し、従来の合計約10,000〜13,500行を、**合計約12,000〜15,500行**へ更新する。外枠16,000行は変更しない。

| 残る既承認の仕事 | 残りの行数の見込み |
| --- | --- |
| 有限アフィン被覆での実際の Frobenius 係数の増大比較 | 300〜700 |
| 実際の affine nerve の大域切断と環の conerve の自然な比較 | 200〜500 |
| 非アフィンの proper fppf の相対二重 Čech と実際の被覆比較 | 400〜1,000 |
| 検証済み F8 四角形と二重複体の全複体の接続 | 600〜1,400 |
| アフィン交叉での nil 不変性と、実際のブローアップを保つ Noether 帰納 | 400〜900 |
| 同じ係数比較の二つの filtered 余極限との自然な整合性 | 500〜900 |
| G2 の実際の模型の代入と、G5 の最終型への移送・報告 | 500〜1,000 |
| 残り合計 | 2,900〜6,400 |

この表は既存の G4・G5 の分割と法則で、新しい主項目・型・主張の追加ではない。Mathlib `AffineScheme.lean` の `preservesLimit_rightOp_Γ`・`preservesColimit_Γ` は、対象がアフィンの同じ図式での比較に使える。さらに既存の `SerrePositivity.HomologicalAlgebra.bicomplexTotal_exactAt_of_rows`・`totalToRowZero_quasiIso`（`BicomplexRowQuasiIso.lean`）と列の版（`BicomplexColumnQuasiIso.lean`）があり、B1 の判定法を作り直さずに接続する材料がある。後者の全射擬同型版には成分の全射性が必要で、これを無条件の比較と読み替えない。係数環と加群の宇宙が同じ API なので、必要なら整数環の ULift と既存の係数制限で内部的に移送し、他のレーンの既存宣言の型は変えない。これらの AG への代入自体はまだ未検証。

G4・G5と停止点2g-2は未完。最終の AugmentedRingCechExact と利用側の型は不変。

一覧：済み1／全体3（うち追加0）。


長さ0を含む同じ Čech 微分と filtered 余極限（着手前、既存の係数移送と余極限比較の法則の内数、全体180〜350行）：`fullCechDifferentialNatTrans k` は既存の projectiveCechCochainsFunctor k から k+1 への、元の fullCechDifferential の自然変換。`fullCechFilteredDifferential_compare` は既存の各項の preservesColimitIso が同じ微分を保つ式。`fullCechFiltered_injective_zero` と `fullCechFiltered_exact` は各段の長さ0の単射性と全ての長さの完全性を、既存の加群の exact filtered colimit と同じ標準比較で移す。被覆の係数図式を代入して `openCoverCechAcyclic_filtered` を得る。整数加群の任意の宇宙へは既存の ULift ℤ の係数移送・AsSmall による添字移送を使い、既存宣言の型を変えない。最終の AugmentedRingCechExact や利用側の型も不変。新しい二重複体の判定法や微分は作らない。


同じ増大完全性の整数係数への移送の分割（着手前、前記の内数、80〜150行）：`fullCechIntSequential_augmentedExact D` は整数加群の有限交叉の図式の自然数系 D に対し、各段の長さ0の単射性と全長さの完全性から同じ余極限のそれらを返す。既存の projectiveIntCechLiftFunctor・その余極限保存・AsSmall の同値と既存の加法的係数比較を使い、同じ各項の加法群・微分を保つ。`openCoverCechAcyclic_intSequential P U` は実際の被覆の交叉の図式を代入し、同じ前層の余極限へ移す法則。

同じアフィン被覆での Frobenius 係数への代入（着手前、既存の係数移送の内数、35〜80行）：`affineSchemeStructurePerfectCech_acyclic` は任意のアフィンスキーム Y と有限アフィン被覆 U、同じ構造層の標数条件から OpenCoverCechAcyclic (frobeniusRingDiagram Y.presheaf p hp hY) U を返す。各有限段は既存の schemeStructureFrobeniusStageIso と構造層の準連接性から供給し、同じ係数の順極限の標準同型で移す。正次数だけでなく同じ増大項の単射性・零次の完全性を含める。原典の層コホモロジーとの比較を新しく作らず、名前・docstringで Čech 版を明示する。


## G4：増大項を含む同じ Čech 微分の filtered 比較

`CechFilteredAugmentedDifferential`（46行）：`fullCechDifferentialNatTrans` は長さ0を含む元の fullCechDifferential を、既存の各項の関手の間の自然変換にしたもの。`fullCechFilteredDifferential_compare` は元の同じ微分と既存の各項の preservesColimitIso が可換な式。有限段の同じ標準脚で照合している。

単独検証、本体とのソース完全一致、対象と入口のビルド5,218ジョブ成功、小監査3宣言（実際の所有元による非公開・生成宣言込み）・標準三公理のみ、終了状態0。ログ `2g-cech-filtered-augmented-differential-check-2.log`・`2g-cech-filtered-augmented-differential-native.log`・`2g-cech-filtered-augmented-differential-audit.log`。局所的な backward.isDefEq.respectTransparency false、既定の資源制限。unused Fintype の style 警告あり。追加公理・sorry・既存の型変更・200行超の宣言なし。共有鍵 --class impl --wait 3600、待ちは一つ、対象ビルドと小監査は別枠。root・下流全ビルド・全体監査なし。

今回1モジュール46行＋入口1行。新規133モジュール本体8,922行、既存追加25行を含む本体8,947行。登録133行・入口の追加空行21行を全て含む外枠計数 **9,101行**。新規小監査累計905宣言、既存15宣言は別計上。完全性・整数係数への移送・同じアフィン被覆への適用は下書きで、この束には含めない。G4・G5は未完。見込み約12,000〜15,500行・外枠16,000行は不変。

一覧：済み1／全体3（うち追加0）。


被覆への代入の型の明示（着手前、前記の内数）：`openCoverIntSequential_augmentedExact P U` は、各 P.obj n の同じ被覆 U での「長さ0の微分の単射性 ∧ 全ての長さ k の二つの微分の Function.Exact」から、同じ colimit P でのその二つの主張を返す。整数係数の任意の宇宙で、補助述語の二つの中身を直接返す分割であり、完全性の意味は変えない。アフィンへの出口 `affineSchemeStructurePerfectCech_augmentedExact` も、同じ元の構造層の Frobenius 係数について、この単射性と全長さの完全性を返す。既存の構造層の加群を、そのまま各有限段の同じ加法群と比較して供給する。最終の AugmentedRingCechExact と既存の利用側の型は変更しない。


宇宙の照合（2026-11-16、下書きの診断）：既存の OpenCoverCechAcyclic は `ModuleCat.{v,v} R` を使い、`ModuleCat.{u,0} ℤ` の一般の u には適用できないことを Lean の型で確認した（作業ログ `2g-cech-filtered-augmented-exact-probe-check-2.log` の末尾）。整数係数の新しい補助出口は、前節のとおり同じ増大微分の単射性と全長さの完全性を直接返す。この二つは元の補助述語の中身そのもので、主張を弱めていない。一般の u も含めて扱い、既存の型・他レーンのファイル・最終の AugmentedRingCechExact は変えない。


## G4：同じ増大項の単射性と全長さの filtered 完全性

`CechFilteredAugmentedExact`（92行）：`fullCechFiltered_injective_zero` は各有限段の同じ長さ0の微分の単射性を、既存の各項の比較と加群の exact filtered colimit で移す。`fullCechFiltered_exact` は同じ二つの微分の全ての長さの完全性を、既存の短複体の完全性の移送で示す。有限な添字には既存の cechFiniteIndexOrder を局所的に使い、元の DecidableEq を定義上保つ。新しい微分・二重複体の判定法は作らない。

単独検証、本体とのソース完全一致、対象と入口のビルド5,219ジョブ成功、小監査2宣言（実際の所有元による非公開・生成宣言の有無も走査）・標準三公理のみ、終了状態0。ログ `2g-cech-filtered-augmented-exact-check-4.log`・`2g-cech-filtered-augmented-exact-native.log`・`2g-cech-filtered-augmented-exact-audit.log`。局所的な backward.isDefEq.respectTransparency false、既定の資源制限。letI・haveI の style 警告あり。追加公理・sorry・既存の型変更・200行超の宣言なし。共有鍵 --class impl --wait 3600、待ちは一つ、対象ビルドと小監査は別枠。root・下流全ビルド・全体監査なし。

今回1モジュール92行＋入口1行。新規134モジュール本体9,014行、既存追加25行を含む本体9,039行。登録134行・入口の追加空行21行を全て含む外枠計数 **9,194行**。新規小監査累計907宣言、既存15宣言は別計上。整数係数・同じ被覆・同じアフィン構造層への代入は下書きで、この束には含めない。G4・G5は未完。見込み約12,000〜15,500行・外枠16,000行は不変。

一覧：済み1／全体3（うち追加0）。


同じ大域切断からの実際の増大写像への接続（着手前、既存の増大項の同定と係数移送の法則の内数、45〜90行）：`schemeStructurePerfectCechAugmentation_id` は元の大域切断環の恒等スカラーを選んだ増大写像と、同じ Frobenius 係数前層の openCoverCechAugmentation の一致。`affineSchemeStructurePerfectCechAugmentation_injective`・`…_exact` は同じ有限アフィン被覆で、その実際の増大写像の単射性と後続の微分との完全性を返す。上の長さ0の項と大域切断の既存の同型を使い、元の増大写像を別の写像に置き換えない。


## G4：同じ有限アフィン被覆の実際の Frobenius 係数の増大完全性

`CechIntSequentialAugmentedExact`（66行）：`fullCechIntSequential_augmentedExact` は、任意の宇宙の整数加群の有限交叉の図式の自然数系について、各有限段の増大項の単射性と全長さの完全性を、同じ余極限へ移す。既存の ULift ℤ の係数移送、AsSmall の同値と既存の加法的係数比較を使い、元の各項の加法群と微分を保つ。

`OpenCoverIntSequentialAugmentedExact`（36行）：`openCoverIntSequential_augmentedExact` は実際の前層の被覆の交叉を前記の法則に代入し、同じ colimit P の長さ0の単射性と全長さの完全性を返す。整数係数の任意の宇宙を扱い、完全性の意味は変更しない。

`AffinePerfectCechAugmentedExact`（57行）：`affineSchemeStructurePerfectCech_augmentedExact` はアフィンスキームの有限アフィン被覆について、実際の構造層の Frobenius 係数の同じ増大項の単射性と全長さの完全性を返す。各有限段は元の準連接な構造層の同じ計算から、同じ制限写像に可換な加法的係数比較で供給する。同じ実際の Frobenius 前層の順極限の標準同型を使って移す。名前・docstring は Čech 版を明示し、層 Hⁱ との比較は作らない。

単独検証、本体とのソース完全一致、対象3本と入口のビルド5,222ジョブ成功、小監査1・1・1宣言（計3、実際の所有元による非公開・生成宣言の有無も走査）・標準三公理のみ、終了状態0。ログ `2g-affine-perfect-cech-augmented-bundle-check-1.log`・`2g-affine-perfect-cech-augmented-bundle-native.log`・`2g-affine-perfect-cech-augmented-bundle-audit.log`。整数係数の移送だけ局所的な backward.isDefEq.respectTransparency false、既定の資源制限。letI の style 警告あり。追加公理・sorry・既存の型変更・200行超の宣言なし。共有鍵 --class impl --wait 3600、待ちは一つ、対象ビルドと小監査は別枠。root・下流全ビルド・全体監査なし。

今回3モジュール159行＋入口3行。新規137モジュール本体9,173行、既存追加25行を含む本体9,198行。登録137行・入口の追加空行21行を全て含む外枠計数 **9,356行**。新規小監査累計910宣言、既存15宣言は別計上。元の大域切断からの実際の増大写像の2つの完全性の出口への接続は下書きで、この束には含めない。アフィン nerve の環の自然な比較、相対 proper fppf の二重 Čech、F8 の全複体への接続と Noether帰納、G5はなお残る。G4・G5と停止点2g-2は未完。見込み約12,000〜15,500行・外枠16,000行は不変。

一覧：済み1／全体3（うち追加0）。


次の同じアフィン nerve の大域切断の比較（着手前、既存の有限極限・係数移送・自然性の法則の内数、200〜500行）：

- `affineGammaCechCocone f n` は f:Y→S、Y・S がアフィンの場合、同じ有限広義ファイバー積 Y_n の大域切断を点、元の各射影と基底への射の Γ を脚とする、Γ(S)→Γ(Y) の同じ wideSpan の余錐。`affineGammaCechIsColimit f n` は既存の `preservesLimit_rightOp_Γ` と反対圏・添字の同値による移送でその普遍性を供給する。
- `affineGammaCechConerveIso f` の型は `(Arrow.mk (Scheme.Γ.map f.op)).cechConerve ≅ (Arrow.mk f).cechNerve.rightOp ⋙ Scheme.Γ`。各有限余積の同じ普遍性で得た標準同型の脚・head の式を示し、元の nerve の射の射影の式で全ての次数への自然性を保つ。`.rightOp` が幾何的な反変 nerve から Schemeᵒᵖ への向きであり、`.leftOp` と取り違えない。
- S=Spec R のときは既存の ΓSpec の同型と schemeScalarHom を使い、元の R→Γ(Y) の矢印の conerve へ同じ比較を移す。増大とスキームの可換な四角形の射も、元の脚を保つ形で照合する。アフィン性以外の Noether 性・有限表示性・全射性は仮定しない。最終出力の型は変更しない。

この束は未実装。既存の `isColimitCoconeLeftOpOfCone`（F:J→Cᵒᵖ の極限から F.leftOp の余極限へ）と `widePullbackShapeOpEquiv` が使えることをソースで確認した。反対圏の向きと式の自然性は実装時に対象ビルドで確かめる。


## G4：実際の大域切断からの増大写像の単射性と零次の完全性

`AffinePerfectCechAugmentation`（65行）：`schemeStructurePerfectCechAugmentation_id` は、任意のスキームで大域切断の恒等スカラーを選んだ実際の増大写像と、同じ Frobenius 係数前層の対角の制限が一致すること。`affineSchemeStructurePerfectCechAugmentation_injective` は有限アフィン被覆でその実際の増大写像が単射であること。`affineSchemeStructurePerfectCechAugmentation_exact` はその同じ写像と元の複体の後続微分が完全であること。元の空タプルの項と大域切断の同型を使う。名前・docstring は Čech 版と原典 Stacks 30.2.6 との対応を明示し、層 Hⁱ との比較は形式化しない。

単独検証、本体とのソース完全一致、対象と入口のビルド5,223ジョブ成功、小監査3宣言（実際の所有元による非公開・生成宣言の有無も走査）・標準三公理のみ、終了状態0。ログ `2g-affine-perfect-cech-augmentation-check-2.log`・`2g-affine-perfect-cech-augmentation-native.log`・`2g-affine-perfect-cech-augmentation-audit.log`。恒等スカラーと零次完全性の証明に局所的な backward.isDefEq.respectTransparency false、既定の資源制限。unused Fintype の style 警告あり。追加公理・sorry・既存の型変更・200行超の宣言なし。共有鍵 --class impl --wait 3600、待ちは一つ、対象ビルドと小監査は別枠。root・下流全ビルド・全体監査なし。

今回1モジュール65行＋入口1行。基準56ea849a3から独立に再計数し、新規138モジュール本体9,238行。既存追加25行を含む本体9,263行、入口の追加159行（登録138・空行21）を全て含む外枠計数 **9,422行**。新規小監査累計913宣言、既存15宣言は別計上。

同じ有限アフィン被覆の実際の Frobenius 係数の長さ0の単射性と全長さの完全性、および実際の大域切断からの増大写像の単射性と零次の完全性まで検証した。アフィン nerve の環の自然な比較、相対 proper fppf の二重 Čech、F8 の全複体との接続と実際のブローアップを保つ Noether帰納、G5はなお残る。G4・G5と停止点2g-2は未完。最終の AugmentedRingCechExact と利用側の型は不変。見込み約12,000〜15,500行・外枠16,000行は不変。

一覧：済み1／全体3（うち追加0）。


同じ Γ 比較の各次数の分割（着手前、前記200〜500行の内数、45〜90行）：`affineGammaCechComponentIso f n` は、Γ(f) の環の conerve の n 次と、同じ幾何的 nerve の n 次の大域切断環の標準同型。`…_ι`・`…_head` は元の有限余積の各脚と head が、元の射影と基底への射の Γ に移る式。同じ二つの余錐の普遍性を使う。


同じ Γ 比較の次数と増大への自然性（着手前、前記200〜500行の内数、70〜130行）：`affineGammaCechComponentIso_naturality f a` は Γ(f) の環の conerve の射 a と、同じ幾何的 nerve の射 a.op の Γ を各次数の標準比較が結ぶこと。元の各射影・head の式を使う。`affineGammaCechConerveIso f` はそれを自然同型にまとめる。`affineGammaCechConerveIso_augmentation f n` は同じ基底 Γ(S) からの増大写像が元の基底への射の Γ に移る式。


## G4：同じアフィン nerve の Γ の余錐と普遍性

`AffineGammaCechCocone`（73行）：`affineGammaCechCocone` は任意の f:Y→S の同じ広義ファイバー積の大域切断を点とする、元の各射影・基底への射の Γ の余錐。`affineGammaCechIsColimit` は Y・S がアフィンの場合、その同じ余錐の普遍性を、既存の Γ のアフィン図式の極限保存と反対圏・添字の同値による移送で示す。図式の同定には既存の WidePushoutShape.diagramIsoWideSpan を使う。`affineGammaCechCocone_ι`・`…_head` は脚が元の射影と基底への射の Γ であること。新しい存在の仮定や Noether 性は要求しない。

単独検証、本体とのソース完全一致、対象と入口のビルド5,224ジョブ成功、小監査7宣言（実際の所有元による非公開・生成宣言込み）・標準三公理のみ、終了状態0。ログ `2g-affine-gamma-cech-cocone-check-2.log`・`2g-affine-gamma-cech-cocone-native.log`・`2g-affine-gamma-cech-cocone-audit.log`。余錐と普遍性の構成に局所的な backward.isDefEq.respectTransparency false、既定の資源制限。追加公理・sorry・既存の型変更・200行超の宣言なし。共有鍵 --class impl --wait 3600、待ちは一つ、対象ビルドと小監査は別枠。root・下流全ビルド・全体監査なし。

今回1モジュール73行＋入口1行。新規139モジュール本体9,311行、既存追加25行を含む本体9,336行。登録139行・入口の追加空行21行を全て含む外枠計数 **9,496行**。新規小監査累計920宣言、既存15宣言は別計上。各次数の標準同型と自然性・増大の保存は下書きで、この束には含めない。G4・G5と停止点2g-2は未完。見込み約12,000〜15,500行・外枠16,000行は不変。

一覧：済み1／全体3（うち追加0）。


同じ比較を元の基底環へ戻す分割（着手前、前記200〜500行の内数、45〜100行）：`schemeScalarArrowGammaIso Y f` は元の schemeScalarHom Y f の環の矢印から Γ(f) の矢印への、基底に ΓSpecIso の逆、先に恒等を使う標準同型。`affineScalarCechConerveIso f` はその conerve と上の同じ Γ 比較の合成。`affineScalarCechConerveIso_augmentation f n` は元の R からの増大写像を、ΓSpecIso の逆と同じ幾何的増大の Γ の合成へ移す式。元の R と Γ(Spec R) を黙って同一視しない。


## G4：同じアフィン nerve の Γ の自然な比較と元の基底環への移送

`AffineGammaCechComponent`（45行）：`affineGammaCechComponentIso f n` は同じアフィン nerve の n 次の大域切断と Γ(f) の環の conerve の標準同型。`…_ι`・`…_head` は各脚と head が元の射影・基底への射の Γ に移る式。

`AffineGammaCechNaturality`（84行）：`affineGammaCechComponentIso_naturality` は元の全ての単体の射に対する自然性。`affineGammaCechConerveIso` は同じ各次数の同型を自然同型にまとめる。`…_augmentation` は同じ増大写像を保つ式。元の有限広義ファイバー積の射影と基底への射の公式を使い、反対圏の合成を明示して照合した。

`AffineScalarCechConerve`（57行）：`schemeScalarArrowGammaIso Y f` は f:Y→Spec R の元のスカラー R→Γ(Y) の矢印と Γ(f) の矢印を ΓSpec の標準同型で結ぶ。`affineScalarCechConerveIso` は Y がアフィンの場合、元のスカラーの環の conerve と同じ幾何的 nerve の Γ の自然同型。`…_augmentation` は元の R からの増大が ΓSpec の逆と同じ幾何的増大の Γ の合成に移る式。R と Γ(Spec R) を黙って同一視せず、元の射を保持する。

三つをまとめた下書き検証成功、各本体は下書きと全バイト一致。新規三本と直接 importer の入口の対象ビルド5,227ジョブ成功、別の共有鍵の小監査は4＋5＋8＝17宣言・標準三公理のみ。非公開・生成宣言も実際の所有モジュールで全件走査した。終了状態は全て0。ログ `2g-affine-scalar-cech-comparison-check-2.log`・`2g-affine-gamma-scalar-cech-comparison-native.log`・`2g-affine-gamma-scalar-cech-comparison-audit.log`。自然性とスカラー移送の一部の証明に局所的な backward.isDefEq.respectTransparency false、資源上限は既定のまま。追加公理・sorry・既存の型変更・200行超の宣言なし。鍵 --class impl --wait 3600、同時の待ちは一つ、ビルドと監査は別枠。root・下流全ビルド・全体監査なし。

今回三本186行＋入口3行。基準56ea849a3から再計数し、新規142モジュール本体9,497行、既存ファイルへの追加25行（削除14行は相殺しない）、入口追加163行（登録142・空行21）を含む外枠計数 **9,685行**。新規小監査累計937宣言、既存15宣言は別計上。アフィン nerve の全ての次数と増大を保つ環の標準比較まで検証した。Frobenius 係数への同じ比較の接続、非アフィン基底での相対 proper fppf の二重 Čech、F8 の全複体と元のブローアップを保つ Noether 帰納、G5は未完。最終の AugmentedRingCechExact と利用側の型は変更していない。見込み約12,000〜15,500行・外枠16,000行は不変。停止点2g-2ではない。

一覧：済み1／全体3（うち追加0）。


次の同じ比較の Frobenius 係数への移送（着手前、既存の係数移送・増大の法則の内数、80〜160行）：`affineScalarCech_primeCast Y f p hR n` は元の環 R の p=0 を同じ conerve の増大と標準同型で同じ幾何的 nerve の Γ へ移す。`affineScalarPerfectCechIso Y f p hp hR` は同じ二つの環図式に既存の frobeniusRingDiagramIso を適用した、実際の整数加群の Frobenius 係数図式の自然同型。`…_augmentation` は元の R の実際の Frobenius 順極限からの増大写像が、ΓSpec の逆と同じ幾何的増大の Γ の合成の順極限写像へ移る式。標数条件を新しく仮定せず hR から供給し、全ての次数の射と元の R を保持する。


## G4：同じアフィン nerve の比較の実際の Frobenius 係数への接続

`AffineScalarPerfectCech`（75行）：`affineScalarCech_primeCast` は元の R の p=0 を元の conerve の増大と同じ標準自然同型で、同じ幾何的 nerve の大域切断環へ移す。`affineScalarPerfectCechIso` は同じ標準自然同型に既存の frobeniusRingDiagramIso を適用した、実際の Frobenius 順極限の整数加群の係数図式の自然同型。`…_augmentation` は元の R の同じ Frobenius 順極限からの増大が、ΓSpec の逆と同じ幾何的増大の Γ の合成の順極限写像へ移る式。有限段の同じ元と直前の環の増大の一致から示した。標数条件は hR だけから供給し、全ての次数の射・元の環と写像を保持する。

下書き単独検証成功、下書きと本体全バイト一致。対象と直接 importer の入口のビルド5,228ジョブ成功、別の共有鍵の小監査7宣言・標準三公理のみ。実際の所有元で非公開・生成宣言も全件走査した。終了状態は全て0。ログ `2g-affine-scalar-perfect-cech-check-2.log`・`2g-affine-scalar-perfect-cech-native.log`・`2g-affine-scalar-perfect-cech-audit.log`。増大の証明に局所的な backward.isDefEq.respectTransparency false、資源上限は既定、長い行のstyle警告あり。追加公理・sorry・既存の型変更・200行超の宣言なし。鍵 --class impl --wait 3600、同時の待ちは一つ。root・下流全ビルド・全体監査なし。

今回一本75行＋入口1行。新規143モジュール本体9,572行、既存追加25行、入口追加164行（登録143・空行21）を含む外枠計数 **9,761行**。新規小監査累計944宣言、既存15宣言は別計上。アフィン nerve の環の自然な比較と実際の Frobenius 係数への移送が同じ増大を保つ所まで検証した。非アフィン基底の相対 proper fppf の二重 Čech、F8 全複体と元のブローアップを保つ Noether帰納、G5はなお残る。G4・G5と停止点2g-2は未完。最終の AugmentedRingCechExact と利用側の型は不変。見込み約12,000〜15,500行・外枠16,000行は不変。

一覧：済み1／全体3（うち追加0）。


次の大域切断から同じタプル被覆複体への増大の接続（着手前、既存の増大・係数移送・自然性の法則の内数、180〜380行）：

- `schemeStructurePerfectCechRefinedPullbackMap_globalAugmentation` は f:X→Y と U,V,ρ の実際の refined pullback で、Γ(Y) の恒等スカラーの増大を、実際の Γ(f) の Frobenius 係数写像と Γ(X) の恒等スカラーの増大の合成へ移す式。既存の同じ R の増大の自然性で R=Γ(Y), φ=id, ψ=f.appTop と取り、元のスカラーの定義で照合する。
- `schemePerfectCechTupleGlobalAugmentationHom f U p hp h n` は同じ nerve 項 Y_n の Γ(Y_n) の実際の Frobenius 係数の次数零 single から、同じ既存の schemePerfectCechTupleComplex の n 項への、恒等スカラーの増大を零次成分とする射。`…_f_zero` はその式、`…_naturality` は元の nerve の大域切断の係数写像と同じタプル複体の射との可換性。これを `schemePerfectCechTupleGlobalAugmentation` として、同じ係数図式を single へ移した関手から既存のタプル複体の関手への自然変換にまとめる。新しいコホモロジーや完全性の述語は作らない。
- `affineCechNerve_isAffine` はアフィン Y,S 上の同じ実際の nerve 項のアフィン性。既存の Scheme.isAffine_of_isLimit を元の wideCospan に適用する。この事実と元のタプル開のアフィン性・被覆性で、同じ各項の実際の大域増大の単射性・零次完全性・正次数の完全性を、既存のアフィン Čech 版から供給する。元の非アフィン proper fppf 射の大域切断に忠実平坦性を仮定するものではない。


## G4：同じ nerve 項の大域切断からタプル複体への自然な増大

`SchemePerfectCechGlobalAugmentation`（39行）：`schemeStructurePerfectCechRefinedPullbackMap_globalAugmentation` は実際の refined pullback が Γ(Y) の恒等スカラーの増大を、同じ Γ(f) の Frobenius 係数写像と Γ(X) の恒等スカラーの増大の合成へ移す式。既存の同じ R の増大の自然性と元のスカラーの定義を用いる。

`SchemePerfectCechTupleGlobalAugmentation`（104行）：`schemePerfectCechTupleGlobalAugmentationHom` は各 nerve 項の実際の大域切断の Frobenius 係数の次数零 single から、元のタプル複体への増大。`…_f_zero` は恒等スカラーの実際の増大が零次成分である式。`…_naturality` は元の nerve の Γ の係数写像と同じタプル被覆の射の可換性。`schemePerfectCechTupleGlobalAugmentation` は同じ大域切断の係数図式を single へ移した関手から、元のタプル複体の関手への自然変換。Y,S と元の射にアフィン性・平坦性を仮定せず、既存の係数・タプル・等号判定・全ての射を保持する。

まとめた下書き検証成功、各本体は下書きと全バイト一致。二本と直接 importer の入口の対象ビルド5,230ジョブ成功、別の共有鍵の小監査1＋13＝14宣言・標準三公理のみ。非公開・生成宣言も実際の所有元で全件走査。終了状態全て0。ログ `2g-scheme-perfect-cech-tuple-global-augmentation-check-2.log`・`…-native.log`・`…-audit.log`。一部の定義・自然性の証明に局所的な backward.isDefEq.respectTransparency false、既定の資源制限。letI のstyleと未使用simp引数の警告あり。追加公理・sorry・既存の型変更・200行超の宣言なし。鍵 --class impl --wait 3600、待ちは一つ、ビルドと監査は別枠。root・下流全ビルド・全体監査なし。

今回二本143行＋入口2行。新規145モジュール本体9,715行、既存追加25行、入口追加166行（登録145・空行21）を含む外枠計数 **9,906行**。新規小監査累計958宣言、既存15宣言は別計上。各列のアフィン性と同じ増大の完全性への接続は下書きで、この束には含めない。相対 proper fppf の二重 Čech、F8 全複体と元のブローアップを保つ Noether帰納、G5は未完。最終の AugmentedRingCechExact と利用側の型は不変。見込み約12,000〜15,500行・外枠16,000行は不変。

一覧：済み1／全体3（うち追加0）。


次の同じ増大射の準同型性への接続（着手前、既存の single・増大・完全性の法則の内数、100〜230行）：`cechSingleAugmentation_quasiIsoAt_zero` は任意の加群 A、非負複体 C、元の射 f:single₀(A)→C で、f.f 0 の単射性と (f.f 0,C.d 0 1) の Function.Exact から、同じ f の零次の QuasiIsoAt を示す。既存の ShortComplex.quasiIso_iff_isIso_liftCycles を使い、元の cycles への写像の全単射を同じ単射性と完全性で示す。`cechSingleAugmentation_quasiIsoAt` は C の正次数の既存の ExactAt と合わせて全次数の QuasiIsoAt にまとめる。基底環と加群の宇宙は独立、既存の API の型は変更しない。これを同じ schemePerfectCechTupleGlobalAugmentationHom と検証済みの各列の増大完全性に適用する。


## G4：同じアフィン nerve 項のタプル増大の完全性

`AffineCechNerveTupleExact`（102行）：`affineCechNerve_isAffine` は Y,S がアフィンなら同じ実際の nerve の各項がアフィンであることを、元の wideCospan に Scheme.isAffine_of_isLimit を適用して示す。`affineCechNerveTuple_augmentation_injective`・`…_augmentation_exact` は、元の有限アフィン被覆から作った同じタプル被覆で、実際の大域切断の恒等スカラーの増大の単射性と同じ零次微分との完全性。`…_augmentedExact` は同じ各項の全タプル長さの完全性。既存のタプル開のアフィン性と被覆性を元の被覆から供給しており、新しい被覆の完全性を仮定しない。Čech 版と Stacks 30.2.6 との関係を docstring に明記し、導来関手の H との比較は作っていない。

下書き検証成功、下書きと本体は全バイト一致。対象と直接 importer の入口のビルド5,231ジョブ成功、別の共有鍵の小監査4宣言・標準三公理のみ。実際の所有元で生成・非公開宣言の有無も全件走査。終了状態全て0。ログ `2g-affine-cech-nerve-tuple-exact-check-2.log`・`…-native.log`・`…-audit.log`。一部の証明に局所的な backward.isDefEq.respectTransparency false、既定の資源制限。letI/haveI と unused Fintype のstyle警告あり。追加公理・sorry・既存の型変更・200行超の宣言なし。鍵 --class impl --wait 3600、待ちは一つ、対象ビルドと監査は別枠。root・下流全ビルド・全体監査なし。

今回一本102行＋入口1行。新規146モジュール本体9,817行、既存追加25行、入口追加167行（登録146・空行21）を含む外枠計数 **10,009行**。新規小監査累計962宣言、既存15宣言は別計上。各列の増大完全性までは到達。同じ single からの増大射の準同型性への接続、非アフィン基底の相対 proper fppf の二重 Čech、F8 全複体と元のブローアップを保つ Noether帰納、G5は未完。見込み約12,000〜15,500行・外枠16,000行は不変。最終の AugmentedRingCechExact と利用側の型は不変。停止点2g-2ではない。

一覧：済み1／全体3（うち追加0）。


同じアフィン平坦全射の Γ の係数への接続（着手前、既存のアフィン判定と係数移送の法則の内数、35〜80行）：`affineGammaFrobeniusCech_exact_of_flat_surjective f p hp hS` は Y,S がアフィン、元の f:Y→S が平坦全射、Γ(S) で p=0 のとき、元の Γ(f) の矢印の実際の frobeniusAugmentedRingCoefficients の AugmentedRingCechExact。Mathlib の Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine から同じ Γ(f) の忠実平坦性を供給し、既存の環の係数の完全性へ渡す。非アフィン上の大域切断の平坦性を主張せず、最終出力の型・仮定は変更しない。


同じ基底の増大の大域切断を経る分解（着手前、既存のスカラー合成・single の法則の内数、40〜80行）：`schemePerfectCechTupleAugmentationHom_factor_global` は f:Y→Spec R の元の増大射 schemePerfectCechTupleAugmentationHom が、元の各 nerve 項の基底への射の schemeScalarHom の実際の Frobenius 係数写像の single と、同じ大域切断の schemePerfectCechTupleGlobalAugmentationHom の合成に等しいこと。各次数で元の R、nerve の増大、タプル複体と射を全て保持し、独立な H の同型を並べない。


## G4：同じ大域増大の準同型性と元の基底の増大の分解

`CechSingleAugmentationQuasiIso`（76行）：`cechSingleAugmentation_quasiIsoAt_zero` は任意の加群 A と元の射 f:single₀(A)→C について、f.f 0 の単射性と同じ零次の完全性から同じ f の零次の QuasiIsoAt を示す。Mathlib の ShortComplex.quasiIso_iff_isIso_liftCycles に元の cycles の写像の全単射を渡す。`…_quasiIsoAt` は同じ C の正次数の完全性と合わせて全次数へ渡す。基底環と加群の宇宙は独立、既存宣言の型は変更していない。

`AffineCechNerveTupleQuasiIso`（67行）：`affineCechNerveTupleGlobalAugmentation_quasiIsoAt` は直前に検証した同じアフィン nerve 項の単射性・零次完全性・全長さの完全性を、元の schemePerfectCechTupleGlobalAugmentationHom に適用する。`…_quasiIso` は同じ射の全次数の準同型性。元の single の零次の標準同型と実際の微分を使い、独立な H の同型を選んでいない。Čech 版と Stacks 30.2.6 の関係を docstring に記載し、層の H との比較は形式化しない。

`AffineGammaFrobeniusCechExact`（33行）：`affineGammaFrobeniusCech_exact_of_flat_surjective` は Y,S がアフィン、f:Y→S が平坦全射なら、元の Γ(f) の矢印の実際の Frobenius 係数の AugmentedRingCechExact。Mathlib の Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine から同じ Γ(f) の忠実平坦性を供給し、既存の係数の完全性へ渡す。非アフィン基底の大域切断の平坦性を仮定するものではない。

`SchemePerfectCechTupleAugmentationFactor`（49行）：`schemePerfectCechTupleAugmentationHom_factor_global` は f:Y→Spec R の元の R からのタプル増大が、元の nerve 項の基底への射の大域スカラーの Frobenius 係数写像の single と、同じ大域切断の増大の合成に等しいこと。元の R と実際の増大写像を保持する。

四本をまとめた下書き検証成功、各本体は下書きと全バイト一致。新規四本と直接 importer の入口の対象ビルド5,235ジョブ成功、別の共有鍵の小監査3＋2＋1＋1＝7宣言・標準三公理のみ。実際の所有元で生成・非公開宣言も全件走査した。終了状態全て0。ログ `2g-affine-cech-global-comparison-check-3.log`・`…-native.log`・`…-audit.log`。一部の証明に局所的な backward.isDefEq.respectTransparency false、既定の資源制限、letI/haveI のstyle警告あり。追加公理・sorry・既存の型変更・200行超の宣言なし。鍵 --class impl --wait 3600、待ちは一つ、対象ビルドと小監査は別枠。root・下流全ビルド・全体監査なし。

今回四本225行＋入口4行。新規150モジュール本体10,042行、既存追加25行、入口追加171行（登録150・空行21）を含む外枠計数 **10,238行**。新規小監査累計969宣言、既存15宣言は別計上。同じ自然な大域増大の各成分の準同型性と元の基底の増大の分解まで到達した。非アフィン基底の相対 proper fppf の二重 Čech、F8 全複体と元のブローアップを保つ Noether帰納、G5は未完。最終の AugmentedRingCechExact と利用側の型は不変。見込み約12,000〜15,500行・外枠16,000行は不変。停止点2g-2ではない。

一覧：済み1／全体3（うち追加0）。


次の有限アフィン開族と同じ環の conerve の接続（着手前、既存の被覆合成・有限余積・係数移送の法則の内数、60〜130行）：f:Y→S が平坦全射、S がアフィン、有限アフィン族 gᵢ:Zᵢ→Y が開埋め込みで Y を覆うとき、`finiteOpenFamilyComposite_surjective` は同じ合成族の余積射 Sigma.desc (gᵢ≫f) の全射性。`finiteAffineOpenFamilyFrobeniusCech_exact` は有限余積のアフィン性と同じ合成射の平坦全射性を使い、その実際の Γ の矢印の Frobenius 係数の AugmentedRingCechExact。非アフィンな Y の Γ に平坦性を仮定せず、元の族と合成射を保持する。各行の矩形タプルとの自然な同定はこの宣言だけでは完了しない。


## G4：有限アフィン開族の合成の実際の係数の完全性

`FiniteAffineOpenFamilyCechExact`（47行）：`finiteOpenFamilyComposite_surjective` は元の族 gᵢ:Zᵢ→Y が覆い、f:Y→S が全射なら、同じ合成族の余積射 Sigma.desc (gᵢ≫f) が全射であること。`finiteAffineOpenFamilyFrobeniusCech_exact` は有限アフィン族、各 gᵢ が開埋め込み、S がアフィン、f が平坦全射なら、同じ合成射の Γ の矢印の実際の Frobenius 係数が AugmentedRingCechExact であること。Mathlib の有限アフィン余積と各成分からの余積射の平坦性を使い、全射性は元の被覆から供給する。非アフィンな Y の Γ の平坦性・被覆合成の完全性を新しい仮定にしない。

下書き単独検証成功、下書きと本体全バイト一致。対象と入口のビルド5,236ジョブ成功、別の共有鍵の所有宣言の小監査2宣言・標準三公理のみ、生成・非公開宣言も走査。終了状態全て0。ログ `2g-finite-affine-open-family-cech-exact-check-1.log`・`…-native.log`・`…-audit.log`。既定の資源制限、haveI のstyle警告あり。追加公理・sorry・既存の型変更・200行超の宣言なし。鍵 --class impl --wait 3600、待ちは一つ、対象ビルドと小監査は別枠。root・下流全ビルド・全体監査なし。

今回一本47行＋入口1行。新規151モジュール本体10,089行、既存追加25行、入口追加172行（登録151・空行21）を含む外枠計数 **10,286行**。新規小監査累計971宣言、既存15宣言は別計上。同じ余積射の係数の完全性まで到達し、元の二重 Čech の矩形タプルとの自然な比較はなお必要。相対 proper fppf、F8 全複体と元のブローアップを保つ Noether帰納、G5は未完。最終出力の型は不変。見込み約12,000〜15,500行・外枠16,000行は不変。

一覧：済み1／全体3（うち追加0）。


次の同じ余積の切断の標準比較（着手前、既存の余積・積・係数移送と自然性の法則の内数、55〜120行）：`schemeGammaSigmaIso Z` は Γ(∐Zᵢ) と ∏ᶜΓ(Zᵢ) の、元の余積入射を射影に持つ標準同型。Γ は ΓSpec.adjunction.rightOp の右随伴で極限を保ち、既存の opCoproductIsoProduct と PreservesProduct.iso を合成する。`…_π` は元の入射の Γ との一致、`…_naturality` は同じ族の写像と自然であること。全ての射を元の余積の普遍性で照合し、個別の切断や H の同型を選ばない。有限アフィン族の nerve の各次数の比較へ使う。


次の同じ有限積の Frobenius 係数への接続（着手前、既存の有限極限・係数移送の法則の内数、100〜210行）：`frobeniusDirectLimitPiMap` は元の各評価環準同型から得る、FrobeniusDirectLimit (ΠᵢAᵢ)→+*ΠᵢFrobeniusDirectLimit Aᵢ。有限の添字では各成分の有限段を同じ最大の段へそろえて全射性、各成分の冪零次数の有限上界で単射性を示し、`frobeniusDirectLimitPiEquiv` にまとめる。評価と元の成分ごとの環の射への自然性を同じ有限段の元で確認する。矩形タプルの係数比較に使い、無限積と順極限の交換は主張しない。最終出力の型や既存 API は変更しない。


同じ余積の切断の比較の増大の式（着手前、直前の55〜120行の内数）：`schemeGammaSigmaIso_desc Z f` は元の合成族の余積射 Sigma.desc f の Γ を同じ標準同型で移すと、元の各 fᵢ の Γ を成分とする積への射になること。元の基底の環からの増大を保つ式として使う。


次の有限ファイバー積と同じ有限余積の比較（着手前、既存の有限極限・余積の分配と射影・自然性の法則の内数、200〜440行）：族 fᵢ:Zᵢ→S と t:Fin(n+1)→ι について `finiteFamilyCechComponent f n t` は同じ widePullback S (Z∘t) (f∘t)。`finiteFamilyCechInclusion f n t` は各射影の後に元の余積入射を合成する、同じ Arrow.mk(Sigma.desc f) の nerve 項への標準射。射影と基底への合成の式、および単体の射 a に沿う t∘a と元の nerve の射との自然性を示す。その有限余積の標準射 `finiteFamilyCechMap` の同型性は、Mathlib の FinitaryPreExtensive.isPullback_sigmaDesc と既存の有限ファイバー冪の Cartesian square を使って帰納する。元の nerve を別の模型に置き換えず、全ての射影・増大を保つ標準比較を供給する。


同じ混合ファイバー積の帰納の分割（着手前、直前200〜440行の内数、80〜150行）：`finiteFamilyFiberZeroIso` は Fin 1 で添字づけた任意の元の族の widePullback と零番の対象との、射影と基底への射を保つ同型。`isPullback_finiteFamilyFiberSucc` は任意の Fin(n+2) の族の混合 widePullback を、同じ末尾の mixed widePullback と先頭の一個の基底上の Cartesian square として表す。既存の有限ファイバー冪の法則と同じ普遍性を、元の各対象が異なる場合へ適用する。既存宣言の型変更は行わない。


同じ分配の単位段の分割（着手前、上の200〜440行の内数、45〜85行）：`finiteFamilyCechMap_zero_isIso` は同じ標準射 finiteFamilyCechMap f ⦋0⦌ の同型性。各成分の同じ単位同型、Fin 1 のタプルの評価による余積の再添字付け、元の余積射の一個のファイバー冪の単位同型を合成し、元の各入射と射影への合成で標準射そのものに一致することを確認する。


同じ成分比較の再添字付けの法則（着手前、既存の射・係数移送の自然性の内数、30〜70行）：`schemeGammaSigmaIso_reindex_naturality` は ρ:ι→κ と Zᵢ→Wρᵢ の元の成分の射に対し、元の余積射 Sigma.desc(fᵢ≫Sigma.ι(W,ρᵢ)) の Γ と、同じ積の各射影 ρᵢ の後の Γ(fᵢ) の自然性。`frobeniusDirectLimitPiMap_reindex_naturality` は任意の添字写像 ρ:κ→ι と成分の環の射 Aρⱼ→Bⱼ について、実際の積環の射と Frobenius 係数の比較が同じ成分の式で可換であること。単体の射で添字型が変わる場合にも同じ写像で接続し、同じ添字型の場合だけの自然性で代用しない。


同じ分配の後続段の分割（着手前、直前200〜440行の内数、130〜220行）：`finiteFamilyCechMap_base` は元の標準射と基底への射の一致。`finiteFamilyCechMap_succ_isIso` は同じ n 次の標準射の同型性から n+1 次の同型性を、混合積の Cartesian square と Mathlib の有限余積の分配で示す。`finiteFamilyCechMap_isIso` は有限な成分の族の全ての次数への帰納。中間の同型の合成が元の標準射と一致することを、同じ各入射・先頭の射影・末尾への射で確認する。既存の nerve の対象や写像を別のものへ置き換えない。


## G4：同じ有限族の切断・Frobenius 係数・混合ファイバー積の標準比較

`SchemeGammaSigma`（71行）：`schemeGammaSigmaIso` は元の余積の Γ と成分の Γ の積の標準同型。`…_π` は各射影が元の入射の Γ である式。`…_desc` は元の族の余積射の Γ が各成分の Γ を持つ積への射へ移る式。`…_naturality` は同じ添字の族の射に自然であること。`…_reindex_naturality` は添字を変える元の成分の射にも自然であること。既存の Γ の右随伴性による極限保存と opCoproductIsoProduct を使う。

`FrobeniusDirectLimitPi`（119行）：`frobeniusPi_primeCast` は元の成分の条件から積環の標数条件を供給する。`frobeniusDirectLimitPiMap` は元の各評価からの実際の Frobenius 係数写像、`…_of` は同じ有限段での評価。`…_naturality`・`…_reindex_naturality` は同じ成分の環の射と、添字を変える成分の環の射への自然性。`…_injective` は有限な成分の冪零次数の上界で単射性、`…_surjective` は成分の有限段を同じ最大の段へ移して全射性を示す。`frobeniusDirectLimitPiEquiv` はその同じ写像の環同型。空の族も除外しない。写像と自然性は任意の族、全単射性は Fintype の仮定の下で示し、無限積との交換は主張しない。

`FiniteFamilyCechComponents`（108行）：`finiteFamilyCechComponent` は元の族の混合 widePullback。`finiteFamilyCechInclusion` は元の各射影と余積入射による、元の余積射の nerve への標準射。`…_π`・`…_base` は各射影と基底への射を保つ式。`finiteFamilyCechComponentMap` は単体の射による元の射影の再添字付け。`finiteFamilyCechInclusion_naturality` はそれが元の nerve の全ての射と可換であること。`finiteFamilyCechMap` はその同じ標準射の余積。

`FiniteFamilyFiberRecursion`（78行）：`finiteFamilyFiberZeroIso` は同じ一個の混合ファイバー積の、元の零番の射影を持つ単位同型。`isPullback_finiteFamilyFiberSucc` は元の混合した n+2 個のファイバー積を、同じ末尾と先頭の基底上の Cartesian square として表す。任意の有限極限を持つ圏の法則で、既存の一定の対象の有限ファイバー冪の API は変更していない。

`FiniteFamilyCechUnit`（54行）：`finiteFamilyCechMap_zero_isIso` は元の標準射 finiteFamilyCechMap の零次の同型性。元の単位同型、Fin 1 のタプルの零番での評価による再添字付け、元の余積射の一個のファイバー冪の単位同型を合成し、同じ入射・射影で元の標準射への一致を示した。

五本をまとめた下書き検証成功、各本体は下書きと全バイト一致。新規五本と直接 importer の入口のビルド5,241ジョブ成功、別の共有鍵の所有宣言の小監査10＋17＋15＋8＋2＝52宣言・標準三公理のみ。生成・非公開宣言も実際の所有元で全件走査。終了状態全て0。ログ `2g-finite-family-coefficient-comparison-check-4.log`・`…-native.log`・`…-audit.log`。一部の射影・自然性と単位の証明に局所的な backward.isDefEq.respectTransparency false、既定の資源制限。長い行と unused Fintype のstyle警告あり。追加公理・sorry・既存の型変更・200行超の宣言なし。鍵 --class impl --wait 3600、待ちは一つ、ビルドと小監査は別枠。root・下流全ビルド・全体監査なし。

今回五本430行＋入口5行。基準56ea849a3から独立に再計数し、新規156モジュール本体10,519行、既存追加25行（削除14行は相殺しない）、入口追加177行（登録156・空行21）を含む外枠計数 **10,721行**。新規小監査累計1,023宣言、既存15宣言は別計上。有限余積と元の nerve との標準比較の後続次数の同型性は下書きで、この束には含めない。相対 proper fppf の実際の行の完全性、F8 全複体と元のブローアップを保つ Noether帰納、G5は未完。最終の AugmentedRingCechExact と利用側の型は不変。見込み約12,000〜15,500行・外枠16,000行は不変。停止点2g-2ではない。

一覧：済み1／全体3（うち追加0）。


## G4：同じ有限余積と元の nerve の全次数の分配

`FiniteFamilyCechDistribution`（195行）：`finiteFamilyCechMap_base` は同じ標準射と元の基底への射の一致。`finiteFamilyCechMap_succ_isIso` は同じ n 次の標準射の同型性から n+1 次へ進む。元の混合ファイバー積の Cartesian square、Mathlib の FinitaryPreExtensive.isIso_sigmaDesc_map、元の n 次の標準射による pullback.map、既存の有限ファイバー冪の Cartesian square を合成し、その同型と元の標準射の一致を各余積入射・先頭の射影・末尾への射・基底への射で確認する。`finiteFamilyCechMap_isIso` は単位段と後続段から、有限族の元の標準射の全次数の同型性を示す。単体の射との整合性は既存の finiteFamilyCechInclusion_naturality と同じ標準射を使う。

下書き単独検証成功、下書きと本体全バイト一致。対象と直接 importer の入口のビルド5,242ジョブ成功、別の共有鍵の所有宣言の小監査3宣言・標準三公理のみ。非公開・生成宣言の有無も実際の所有元で全件走査。終了状態全て0。ログ `2g-finite-family-cech-distribution-check-5.log`・`…-native.log`・`…-audit.log`。後続段の証明に局所的な backward.isDefEq.respectTransparency false、既定の資源制限。haveI と未使用simp引数のstyle警告あり。追加公理・sorry・既存の型変更・200行超の宣言なし。鍵 --class impl --wait 3600、待ちは一つ、ビルドと監査は別枠。root・下流全ビルド・全体監査なし。

今回一本195行＋入口1行。新規157モジュール本体10,714行、既存追加25行、入口追加178行（登録157・空行21）を含む外枠計数 **10,917行**。新規小監査累計1,026宣言、既存15宣言は別計上。有限余積と元の nerve の幾何的な標準比較まで到達した。実際の矩形タプルの係数図式への代入、相対 proper fppf の行の完全性、F8 の全複体と Noether帰納、G5は未完。停止点2g-2の完成ではない。

残りを宣言の用途別に照合したところ、非アフィン始域・基底の相対二重 Čech の接続を従来の見込みで過小評価していた。更新後の残り約2,900〜6,200行、全体約13,800〜17,100行は外枠16,000行の上端を超える見込み。この検証済みの束をコミットした後、/goal の外枠による停止規則に従って2g-2の Lean を止め、規模境界報告と2h段0の紙へ移る。型・範囲・外枠を独断で変えない。

一覧：済み1／全体3（うち追加0）。


## 規模境界での停止と2h段0の紙

上の再見積もりの内訳、検証済み先端 `8510a94c6`、停止規則を [規模境界報告](scheme-w1-2g-2-size-boundary.md) にまとめた。残り2,900〜6,200行、現在の10,917行と合わせて13,817〜17,117行。上端が外枠16,000行を超える見込みのため、2g-2のLeanを停止した。数学的な行き詰まりではなく、最終の主張や仮定・型も変更していない。

代わりの [2h段0の紙](scheme-w1-2h-route.md) §10を現状の宣言で更新した。H02相当は既存の同じ増大余単体環の自然同型を再利用し、2hで作り直さない。H01・H03・H04は未実装。G4・G5の未供給の入口を最終定理の仮定に押し込まず、2hのLeanも開始していない。

一覧：済み1／全体3（うち追加0）。停止点2g-2は未完であり、goalの達成や2g-2の外枠の独断の変更とは扱わない。


## 規模境界の解除（2026-11-16、ユーザー承認）

外枠18,000行への拡張と、同じ型・範囲での再開の承認を受領した。有限族の幾何的比較から、同じ環の積への比較と単体の射・増大の自然性を進める。最終出力と利用側の型は不変。

着手前の型つきの法則（既存の係数移送の内数、100〜180行）：`finiteFamilyCechGammaIso` は Γ(元の余積射の nerve の n 次) と Π_t Γ(元の混合ファイバー積) の同型。`…_eval` は同じ成分の評価が元の標準入射の Γ である式。`…_naturality` は単体の射によるタプルの再添字付けと元の成分の射への自然性。`…_augmentation` は元の基底からの Γ の写像が元の各混合積の基底写像に移る式。積の比較で環と添字の宇宙を同一視しない。

同じ比較の分割（上の100〜180行の内数）：`smallCommRingPiIso`・`…_eval` は小さい添字と任意の宇宙の環の関数積への標準比較とその射影の式。Mathlibの同じ普遍性を用い、宇宙を狭めない。`finiteFamilyCechGammaDiagram` は同じ元の nerve の Γ を標準同型で移した余単体環で、`…_map_eval` は各射を元のタプルの再添字付けと混合積の Γ で表す。`finiteFamilyCechGammaDiagramIso` は全ての射を同時に保つ自然同型。

次の Frobenius への同じ係数移送（既存の法則の内数、100〜180行）：`frobeniusDirectLimitRingIso` は元の環の同型を同じ実際のFrobenius順極限の環同型へ移す（既存の加群版と同じ射）。`finiteFamilyCechComponent_primeCast` は元の標準入射から成分の標数条件を供給する。`finiteFamilyCechFrobeniusEquiv` は有限族の同じ Γ の標準比較と検証済みの有限積の Frobenius 比較を合成し、`…_of`・`…_naturality`・`…_augmentation` で同じ有限段・単体の射・増大を照合する。無限積との交換や新しい完全性の仮定は加えない。


## G4：元の有限族の Γ と実際の Frobenius 係数の自然な比較

`FiniteFamilyCechGamma`（129行）：`smallCommRingPiIso` は小さい添字と任意の宇宙の環について圏論的な積と実際の関数環の積の標準同型、`…_eval` は元の射影との一致。`finiteFamilyCechGammaIso` は元の余積射の nerve の Γ と元の混合積の切断の関数環の同型。`…_eval` は元の標準入射の Γ、`…_naturality` は単体の射による再添字付けと元の混合積の射への自然性、`…_augmentation` は元の基底からの増大を保つ式。`finiteFamilyCechGammaDiagram` はその同じ関数環へ移した余単体環、`…_map_eval` は各射の実際の成分の式、`finiteFamilyCechGammaDiagramIso` は元の nerve の rightOp⋙Γ との自然同型。

`FrobeniusDirectLimitRingIso`（46行）：`frobeniusDirectLimitRingIso` は元の環の正逆の射を実際の Frobenius 順極限に適用した環同型。既存の加群版と同じ射で、有限段の元から逆の法則を示す。`…_of` は元の有限段への評価式。

`FiniteFamilyCechFrobenius`（105行）：`finiteFamilyCechComponent_primeCast` は元の標準入射の Γ により成分の標数条件を供給する。`finiteFamilyCechFrobeniusEquiv` は同じ Γ の標準同型と検証済みの有限積の Frobenius 同型の合成。`…_of` は元の入射の Γ を各有限段に適用する式、`…_naturality` は元の全ての単体の射と同じタプルの再添字付けを保つ式、`…_augmentation` は元の基底からの増大の Frobenius 写像を保つ式。空の有限族を除外せず、無限積との交換は主張しない。

次の同じ混合積とタプル開の接続（既存の被覆・制限の射の法則の内数、180〜300行、上の残り300〜650行の内数）：`openFamilyCechInclusion` は Uᵢ.ι≫f の元の混合積から、f の元の nerve への標準射。`…_π`・`…_base` は元の各射影・基底への式。`openFamilyCechIso` は同じ混合積と schemeCechTupleOpen f U n t のスキームとの同型で、元の開の入射との合成が標準射に一致する。正逆を元の射影と開埋め込みの一意な持ち上げで作り、単体の射・制限の射の比較に渡す。アフィン性や元の f の滑らかさは仮定しない。

検証：三本をまとめた下書き検証成功（`2g-finite-family-frobenius-gamma-check-9.log`）、本体は各下書きと全バイト一致。三本と直接importerの入口のビルド5,245ジョブ成功（`2g-finite-family-gamma-frobenius-native.log`）。別の共有鍵で実際の所有モジュールの非公開・生成宣言を含めて全件監査し、24＋9＋18＝51宣言、標準三公理のみ（`2g-finite-family-gamma-frobenius-audit.log`）。全て終了0。局所的なbackward.isDefEq.respectTransparency falseのみ、既定の資源上限、追加公理・sorry・200行超の宣言・既存宣言の型変更なし。共有鍵 --class impl --wait 3600、待ちは一つ、ビルドと監査は別枠。root・下流全ビルド・全体監査なし。

再開後の今回三本280行＋登録3行＝283行。基準56ea849a3から再計数し、新規160モジュール本体10,994行、既存追加25行、入口追加181行を含む外枠計数 **11,200行**。新規所有宣言の小監査累計1,077、既存15宣言は別計上。元の有限族の同じ係数比較と単体の射・増大の自然性は閉じた。混合積と元のタプル開の同定は未検証の下書き。相対proper fppf、F8の全複体とNoether帰納、G5は未完。完成見込みの幅は引き続き約13,800〜17,100行（ユーザー承認の外枠18,000行内）。最終のAugmentedRingCechExactと利用側の型は不変。停止点2g-2ではない。

一覧：済み1／全体3（うち追加0）。

同じ矩形タプルの行の分割（既存G4の被覆・係数の法則の内数、70〜140行）：`schemeCechTupleOpen_iInf` は元の nerve のタプル開と有限交叉の交換で、同じ添字の行列の転置を実際の開の等号として与える。`openIntersectionFamily_iSup` は非空有限交叉を全タプルで取ると元の被覆と同じ全体を覆う式、`…_isAffine` はアフィン対角の下のアフィン性。`finiteAffineOpenIntersectionFamilyFrobeniusCech_exact` は元の平坦全射とその同じ交叉の族に、検証済みの有限アフィン族の完全性を代入した式。非アフィン始域の Γ の平坦性は仮定せず、同じ族の余積射を用いる。

同じ開の係数への移送の分割（上の混合積・係数比較の内数、70〜130行）：`openFamilyCechOpenMap_eq_resLE` は同じ制限写像が Mathlib の resLE と一致する式。`openFamilyCechSectionsIso` は元の nerve のタプル開の実際の構造層の切断環と、同じ混合積の Γ の同型。`…_naturality` は元の nerve の appLE と混合積の全ての射の Γ を同じ自然同型で照合する。Mathlib の Opens.topIso と resLE_app_top を使い、単独の H の同型で代用しない。


## G4：元のタプル開と混合積、同じ矩形の平坦な行

`OpenFamilyCechComparison`（223行）：`openFamilyCechInclusion` は元の開の族 Uᵢ.ι≫f の混合積から f の元の nerve への標準射。`…_π`・`…_base` は元の射影・基底の式、`…_range` は同じタプル開への像の包含。`openFamilyCechToOpen`・`…_fac` はその開の入射による因子化。`openFamilyCechProjection`・`…_fac` はタプル開の各射影の元の Uᵢ への持ち上げ。`openFamilyCechFromOpen` はそれらを脚とする元の混合積への射。`openFamilyCechIso` はこの二つが互いに逆である標準同型、`…_hom_fac` は元の入射との合成の式。`openFamilyCechInclusion_naturality` は単体の射と混合積の再添字付けへの自然性。`openFamilyCechOpenMap`・`…_fac` は元の nerve の射の同じタプル開への制限、`openFamilyCechIso_naturality` は同じ標準同型がこの制限と全ての単体の射に自然であること。アフィン性・滑らかさ・固有性を仮定しない。

`RectangularCechOpenRows`（70行）：`schemeCechTupleOpen_iInf` は有限交叉とタプル開の交換を、同じ矩形タプルの転置による元の開の等号で与える。`openIntersectionFamily_iSup` は非空有限交叉を全タプルで取る族が元の被覆と同じ全体を覆う式、`openIntersectionFamily_isAffine` は同じ交叉のアフィン性をアフィン対角と元の被覆から供給する。`finiteAffineOpenIntersectionFamilyFrobeniusCech_exact` は元の平坦全射と同じ有限交叉族の余積射について、既存の有限アフィン族の完全性を適用した増大環 Čech の完全性。非アフィンな始域の Γ の平坦性を推論しない。有限族が空の場合も除外せず、交叉を取る添字は非空有限（実際の正次数の Fin(k+1)）とする。

検証：二本をまとめた下書き検証成功（`2g-open-family-rectangular-cech-check-4.log`）、本体と下書きは全バイト一致。対象二本と直接importerの入口のビルド5,247ジョブ成功（`2g-open-family-rectangular-cech-native.log`）。別の共有鍵で実際の所有宣言を非公開・生成分も含めて全件監査し、28＋4＝32宣言・標準三公理のみ（`2g-open-family-rectangular-cech-audit.log`）。各終了0。局所的なbackward.isDefEq.respectTransparency false、既定資源上限、haveIのstyle警告のみ。追加公理・sorry・既存宣言の型変更・200行超の宣言なし。共有鍵 --class impl --wait 3600、待ちは一つ。root・下流全ビルド・全体監査なし。

今回293行＋登録2行＝295行。外枠計数は **11,495行**（新規162モジュール本体11,287行、既存追加25行、入口183行）。新規所有宣言の小監査累計1,109、既存15宣言は別計上。タプル開との標準同型と元の単体の射への自然性、同じ矩形の開の等号と同じ交叉族への平坦な行の代入まで到達した。構造層のappLEとの同じ係数比較は下書き検証成功・本体ビルド前。相対proper fppfの二重複体への代入、F8全複体・Noether帰納、G5は未完。外枠18,000行、完成見込み約13,800〜17,100行。最終出力と利用側の型は不変。

一覧：済み1／全体3（うち追加0）。


## G4：元の構造層の係数と混合積の Γ

`OpenFamilyCechCoefficients`（68行）：`openFamilyCechOpenMap_eq_resLE` は同じタプル開への制限の射が元の nerve の射の Mathlib の resLE と一致する式。`openFamilyCechSectionsIso` は元の nerve のタプル開上の実際の構造層の切断環と、同じ混合積の Γ の環同型。Mathlib の Opens.topIso と元の混合積の標準同型を合成する。`…_naturality` は元の構造層の appLE と全ての単体の射を同じ環同型で保つこと。resLE_app_top と元のスキームの同型の自然性を使い、独立な H の同型を選ばない。

下書き単独検証成功（`2g-open-family-cech-coefficients-check-1.log`）、本体と下書きは全バイト一致。対象と直接importerの入口のビルド5,248ジョブ成功（`2g-open-family-cech-coefficients-native.log`）。別の共有鍵で非公開・生成分を含む実際の所有宣言を全件監査し、5宣言・標準三公理のみ（`2g-open-family-cech-coefficients-audit.log`）。全て終了0。局所的なbackward.isDefEq.respectTransparency false、資源上限は既定。追加公理・sorry・既存宣言の型変更・200行超の宣言なし。入口のビルドでは既存のhaveIのstyle警告が再掲される。鍵 --class impl --wait 3600、待ちは一つ、ビルドと監査は別枠。root・下流全ビルド・全体監査なし。

今回68行＋登録1行＝69行。基準56ea849a3から再計数し、新規163モジュール本体11,355行、既存追加25行、入口184行を含む外枠計数 **11,564行**。新規所有宣言の小監査累計1,114、既存15宣言は別計上。再開後の六本は641行＋登録6行＝647行、監査51＋32＋5＝88宣言。外枠18,000行、完成見込み約13,800〜17,100行。

次は同じ開の構造層の増大の式、同じFrobenius係数への移送、実際の矩形タプルの二重 Čech の行への代入。非アフィンな中間基底の相対proper fppf、F8全複体と元のブローアップを保持するNoether帰納、G2の模型と二つのfiltered colimitの代入、G5は未完。最終のAugmentedRingCechExactと利用側の型は不変。停止点2g-2ではない。

一覧：済み1／全体3（うち追加0）。


次の同じ増大の係数の式（既存の制限・係数移送の法則の内数、50〜100行）：`openSections_appLE_top` は v:X→S と O:X.Opens に対し v.appLE ⊤ O ≫ O.topIso.inv が元の O.ι≫v の Γ に一致する式。`openFamilyCechSectionsIso_augmentation` は元の基底からタプル開への appLE と同じ混合積の基底の Γ が標準同型で一致すること。既存の appLE の合成則と元の入射・基底への射の式だけを使う。最終型・仮定は変更しない。

同じ Frobenius 局所係数への移送（既存の係数移送の法則の内数、100〜180行）：`openFamilyCechMixed_primeCast` は元のタプル開の標数条件を同じ環同型で混合積へ送る。`openFamilyCechPerfectSectionsEquiv` は同じ実際の Frobenius 順極限の環同型、`…_of` は有限段の元への式、`…_naturality`・`…_augmentation` は元の appLE と全ての単体の射・基底の増大との自然性。元の標数条件から供給し、独立の混合積の条件を仮定に加えない。

同じ行の実際の添字と増大列の比較（既存G4の証明分割の内数）：`cechOpenIntersection_tupleSupport_eq_iInf` は fullCechComplex が使うタプルの有限像の交叉と、元の全座標の交叉の等号。`schemeCechTupleIntersection_rectangular` はその実際の fullCech の交叉を、同じ有限交叉族のタプル開へ同定する（35〜70行）。行の完全性を全複体へ渡すときは、正の縦次数にもRを持つ定数余単体の列を中間に置く。その列と零次single Rの既存の比較を用い、正の縦次数で0→行が完全だとは主張しない。最終の増大項や出力の型は変更しない。

同じ増大列の比較の分割（上のG4の証明分割の内数、45〜90行）：`fullCechConstantAugmentation` は元の係数図式 D の空集合の値を定数余単体図式とし、全てのタプルの有限像への元の制限写像で fullCechCosimplicial D へ増大する自然変換。`…_apply` は同じ有限像への成分の式。これは単体の全ての射を保つ既存の増大・制限の法則であり、single の増大写像や最終の型を置き換えない。


## G4：元の基底の増大と実際の Frobenius 局所係数

`OpenFamilyCechAugmentation`（47行）：`openSections_appLE_top` は v:X→S と O:X.Opens の元の appLE を Opens.topIso.inv で大域切断に移すと、元の O.ι≫v の Γ に一致する式。元の開の appLE の同定と既存の合成則を使う。`openFamilyCechSectionsIso_augmentation` は元の基底からタプル開への実際の appLE が、同じ環同型で元の混合積の基底の Γ に移ること。元の標準入射と基底の射の式で照合する。

`OpenFamilyCechPerfectCoefficients`（100行）：`openFamilyCechMixed_primeCast` は元のタプル開の標数条件を同じ環同型で混合積に供給する。`openFamilyCechPerfectSectionsEquiv` は実際の Frobenius 順極限の環同型。`…_of` は元の同じ有限段の切断への式。`…_naturality` は元の appLE と全ての単体の射との自然性、`…_augmentation` は元の基底からの増大との自然性。混合積の標数を独立の仮定にせず、零環・空の開・重複タプルを除外しない。

二本をまとめた下書き検証成功（`2g-open-family-perfect-augmentation-check-3.log`）、本体は各下書きと全バイト一致。対象二本と直接importerの入口のビルド5,250ジョブ成功（`2g-open-family-perfect-augmentation-native.log`）。別の共有鍵で非公開・生成分を含む実際の所有宣言を全件小監査し、4＋7＝11宣言・標準三公理のみ（`2g-open-family-perfect-augmentation-audit.log`）。各終了0。局所的なbackward.isDefEq.respectTransparency false、資源上限は既定。追加公理・sorry・既存宣言の型変更・200行超の宣言なし。入口で既存のhaveIのstyle警告が再掲される。共有鍵 --class impl --wait 3600、待ちは一つ。root・下流全ビルド・全体監査なし。

今回147行＋登録2行＝149行。外枠計数 **11,713行**（新規165モジュール本体11,502行、既存追加25行、入口186行）。新規所有宣言の小監査累計1,125、既存15宣言は別計上。外枠18,000行、完成見込み約13,800〜17,100行。次は実際のfull Čech の有限像の交叉への代入と、全縦次数に元の増大を持つ定数余単体列の比較。相対proper fppf・F8全複体・Noether帰納・G5は未完。最終型と利用側の型は不変。停止点2g-2ではない。

一覧：済み1／全体3（うち追加0）。

同じ矩形の実際の係数の移送の分割（既存G4の係数移送の内数、45〜100行）：`rectangularCechSectionsIso` は fullCechComplex の実際の有限像の交叉上の切断環と、転置した同じ有限交叉族の混合積の Γ の同型。`…_augmentation` は元の基底からその実際の交叉への appLE と混合積の基底の Γ の一致。同じ開の等号による前層の移送と、検証済みの openFamilyCechSectionsIso を合成し、別の被覆や同型なHは選ばない。

同じ二重図式の縦方向の係数移送（既存の細分・係数移送の法則の内数、100〜200行）：ρ:κ→ι と Vⱼ≤Uρⱼ に対し、`openFamilyCechRefinementOpen_le` は元の各タプル開の包含、`openFamilyCechRefinementMap` は元の開の包含を脚とする混合積の標準射。`…_π`・`…_base`・`…_inclusion` は元の各射影・基底・nerveへの入射を保つ式、`…_iso` は同じタプル開の包含との自然性。有限交叉の次数を動かす場合も、この同じ標準射で接続する。

同じ細分の切断への移送（直前100〜200行の内数）：`openSections_homOfLE` は元の開の包含の Γ と元の前層の制限を Opens.topIso で照合する式。`openFamilyCechSectionsIso_refinement` は元のタプル開の包含による実際の制限と、元の混合積の細分の射の Γ が標準同型で可換であること。resLE_app_top の恒等射の場合と、元の開の標準同型の自然性から示す。

同じ Frobenius 環同型の自然性の共通化（既存の係数移送の法則の内数、30〜55行）：`frobeniusDirectLimitRingIso_naturality` は元の環同型の可換四角を、実際の Frobenius 順極限の環同型と元の射の順極限の可換性へ送る。既存の整数加群版と同じ有限段の計算で、開の細分・矩形の係数比較にも同じ式を使う。

同じ行の各次数の係数同型の合成（既存G4の係数移送の内数、90〜160行）：`rectangularPerfectRowEquiv` は元の交叉族の余積射の nerve の Γ の Frobenius 係数と、元の二重 full Čech の矩形の交叉上の Frobenius 係数の積との環同型。有限族の同じ係数比較、行列の転置、実際の矩形の切断環の標準同型の逆を合成する。`…_apply`・`…_of` で元の各成分と同じ有限段への一致を示す。これは各次数の係数移送の段階であり、単独で全複体の完全性とは主張しない。

同じ定数増大列とsingleの比較の分割（既存G4の増大・全複体への証明分割の内数、100〜170行）：`cechConstantComplex` は定数余単体図式を既存の交代余面複体関手で写した列。`…_d` は元の微分が0と恒等を交互に取る式、`…_exact` は正次数の完全性。`cechConstantSingleAugmentation` と `…_f_zero` は元の零次singleからの包含、`…_quasiIso` はその同じ包含の準同型性。各成分の全射性は主張しない。元の加群と係数環の宇宙を分けたまま、既存のsingle増大の判定を使う。

同じ細分の Frobenius 係数での可換性（既存の係数移送の法則の内数、45〜90行）：`openFamilyCechPerfectSectionsEquiv_refinement` は元のタプル開の制限のFrobenius写像と、元の混合積の細分のΓのFrobenius写像が、同じ環同型で可換であること。元の切断環の可換四角に共通化したFrobenius環同型の自然性を適用し、縦方向の係数の射も保持する。

同じ縦次数の再添字付けの法則：`openIntersectionFamily_refinement` は任意の添字の写像 a:κ→λ と元のタプル t:λ→ι に対し、全座標の交叉が t∘a の交叉に含まれる式。これを同じ開の細分の自然性に代入し、縦の余面・退化でも同じ係数の制限を使う（既存の細分の内数、10行以内）。


## G4 の下書きと次の検証の状況（2026-11-16 昼）

検証済みの数学は `415b27a9b`、型つきの次の法則の記録は `5f939452f`。追加の最新下書きは上記の九本、本体相当584行。まだ本体へ移しておらず、コミットにも含めない。検証済みの外枠計数11,713行と合計すると12,297行（将来の登録9行を含めると12,306行相当）。承認済みの外枠18,000行内。完成見込み約13,800〜17,100行は、これらも含むG4・G5の見込みとして維持する。

共有鍵は一つの待ちを継続中。先に投入した原版の係数比較二本の検証が終了してから、最新の自然性・細分・定数列の比較を含む九本の依存順の束を、新しい検証用出力で確認する。原版の成功を、後から追加した自然性の検証として使わない。原版の有限像の交叉と定数余単体の増大は下書き検証を通っているが、最新九本の対象ビルド・所有宣言監査が済んだとは主張しない。

全複体への比較では、正の縦次数にもRを持つ中間の定数余単体列を使う。元のsingleから定数列への包含は正次数で全射ではない。既存の各成分の全射性を仮定する比較補題を、この包含へ適用してはならない。また逆向きの射影と正の水平列の恒等は、一般には増大と可換でない。同じ包含の余核が一列に集中する可縮な複体になることを使って、元の全複体へ戻す部分は未実装。

Noether帰納では、G3の最新の閉集合の整礎帰納を使い、有限Krull次元の古い案へ戻さない。帰納命題には元の閉像上の固有全射と、その任意のNoetherアフィン底変換のdescentを含める形を準備している。2dの実際のブローアップを保持し、その底変換の射影性と中心外同型性を使う。底変換をブローアップそのものと同定したり、generic ProperInductiveLevelから射影性を推論したりしない。正次数の各項への底変換の条件も元の中心上の帰納仮定へ渡す。これはG4の証明の型の準備であり、Noether帰納が完成したという報告ではない。

G4・G5は未完。最終のAugmentedRingCechExactと利用側の型は不変。停止点2g-2ではない。

一覧：済み1／全体3（うち追加0）。

同じ行の係数同型の水平の自然性（既存G4の係数移送の法則の内数、100〜180行）：`rectangularPerfectRowEquiv_naturality` は元の交叉族の余積射の nerve の全ての射の Γ の Frobenius 写像が、同じ行の環同型で元の full Čech の矩形の実際の appLE の Frobenius 写像へ移ること。各成分の標準同型の単射性で照合し、有限族の自然性と同じ矩形の切断の自然性を合成する。各次数の同型だけで全複体の比較を済みとはしない。

同じ整数係数の宇宙の移送（既存の係数移送・全複体の法則の内数、60〜100行）：`cechIntegerLiftFunctor` は ULift ℤ≃+*ℤ による Mathlib のスカラー制限の同値。元の準同型の関数は変わらない。`cechIntegerLiftBicomplex` は同じ既存の複体関手を二度適用する値。`cechIntegerLiftTotalComponentIso` は同じ全複体の各直和項の標準比較、`…_ι` は元の直和入射との一致。既存のHA宣言の宇宙を変更せず、最終の係数や型も変更しない。全複体の微分との比較は別途必要。

同じ整数係数の移送の法則の補足：MathlibのrestrictScalars自体は異なる環の宇宙を許すが、便利なRingEquiv同値の入口は共通の宇宙を要求するため、`cechIntegerLiftEquivalence` で正逆・単位・余単位を既存のrestrictScalarsComp'とrestrictScalarsIdから明示する。基礎の既存宣言は変更しない（上記60〜100行の内数）。

同じ整数係数の移送の完全性の法則：`cechIntegerLiftComplex_exactAt_iff` は、元の複体の各次数の完全性を保ち反映する式。元の準同型の関数が変わらないことを加群の短複体の既存の完全性判定へ渡す（同じ60〜100行の内数）。

同じ整数係数の全複体への移送（既存の係数移送・全複体の法則の内数、100〜170行）：`cechIntegerLiftTotalComponentIso_d` は元の直和入射と二方向の符号付き微分を保つ式。`cechIntegerLiftTotalIso` はその同じ全複体の同型、`cechIntegerLiftTotal_acyclic_iff` は元の全複体の完全性の保存と反映。`cechIntegerLiftTotal_acyclic_of_rows` は、同型な大きい整数環上で既存のHAの行の完全性の判定を使って、元の整数係数の全複体の完全性へ戻す。既存のHAの対角線の議論を作り直さず、型・資源上限・既存宣言は変更しない。


## 最新の係数比較と全複体への移送の下書き（2026-11-16 午後）

上記の九本に、行の水平自然性と、同じ整数係数を大きい同型な整数環へ移す全複体の比較二本を加え、現在十二本・本体相当823行。元の全複体への移送には、Mathlibのスカラー制限の同値、元の直和入射を保つ標準比較、各次数の完全性の保存・反映を用いる。その上で既存HAの行の完全性から全複体の完全性を得る判定を再利用する。HAの既存宣言の型の変更や、対角線の議論の作り直しは行わない。元の環・加群の型と準同型の関数を保つ比較を確認する段階である。

これらはまだ下書きであり、本体への登録・対象ビルド・所有宣言監査は未了。各下書きと生成した検証用束のSHA256を保存し、原版の検証やその後の編集の成功を取り違えない。先の原版の待ちは鍵未取得のまま終了75を確認した。最新の束の依存を確認したところ、既存HA二本の成果物がこのworktreeで未取得だったため、自分の最新の待ち一件だけをSIGINTで終了し、終了130を確認した。現在は共有鍵一件の中で既存依存の対象ビルドを行い、その後に同じ固定済みの下書きを検証するコマンドを --class impl --wait 3600 で待っている。他のレーンやmainのビルドは中断していない。

検証済み11,713行に検証前823行・登録予定12行を加えると12,548行相当。係数比較の残り、元の全複体との比較、射影四角形への代入、元の中心を保持するNoether帰納、二つのfiltered colimitとG2の実際の模型をG5へ渡す部分を含め、完成見込みを **約14,600〜17,300行** に更新する。元の約13,800〜17,100行の下端は、実際の自然性・全複体の係数の宇宙の移送の分を十分含めていなかった。ユーザー承認の外枠18,000行は不変。未実装の帰納やG5を完成扱いにしたり、必要な自然性や元の最終型を省いて見込みを縮めたりしない。

G4・G5は未完。検証済みの数学の先端は `415b27a9b` のまま。未検証Leanはコミットしない。停止点2g-2ではない。

一覧：済み1／全体3（うち追加0）。

同じ行の増大環の図式の単位・合成の法則（既存G4の自然性の内数、70〜120行）：`frobeniusArrowDiagramMap_id`・`…_comp`、`frobeniusArrowSmallDiagramMap_id`・`…_comp`、`frobeniusDirectLimitArrowMap_id`・`…_comp` は、既存の同じ矢印の有限段の図式と実際の順極限の写像が元の単位・合成を保つこと。縦の交叉族を動かす図式に用い、G5でも同じ法則を再利用する。現在固定済みの十二本には含めず、別の下書きとして保持する。

同じ矩形の行の増大の法則（既存G4の増大・係数移送の内数、70〜120行）：`rectangularPerfectRowEquiv_augmentation` は、元の交叉族の余積射のnerveへの基底のΓのFrobenius写像を、同じ行の環同型で、元の矩形の実際の交叉上のappLEのFrobenius写像へ送る式。各成分の標準同型へ戻し、有限族の増大と元の構造層の増大の一致から示す。固定済みの十二本の後で検証する別の下書きとする。

同じ矩形の行の図式への束ね方（既存G4の自然性・係数移送の内数、90〜140行）：`rectangularPerfectRowFunctor` は元の schemePerfectCechTupleFunctor の縦次数を固定した図式。`…_map_apply` はその写像が元の矩形の実際のappLEである式。`…FunctorIso` は元の交叉族の余積射のnerveの実際のFrobenius係数から、その同じ図式への自然同型。別の係数図式を同型によって定義して元の射との照合を省略しない。現在固定済みの十二本とは別の未検証下書きとする。

同じ全縦次数の増大を実際の全タプル複体へ渡す分割（既存G4の増大・全複体の内数、70〜120行）：`fullCechConstantComplexAugmentation` は A→D(∅) と元の空集合からの制限から、同じ定数余単体の交代複体 C(A)→fullCechComplex D を作る。`…_apply` は各次数が元の有限像への制限である式、`…_single_zero` は元のsingleからの包含との合成の零次が同じ増大であること。正次数も同じAを持ち、0→行の完全性や包含の各成分の全射性は仮定しない。固定済みの十二本に加えず、別の未検証下書きとする。

全複体の比較の紙の補足：定数列からsingleへの成分ごとの射影は増大と可換でないが、全複体の零水平・正偶数縦次数vの成分を、負の増大で水平1・縦v−1へ補正すると、同じsingleの全複体への射影Pを作れる見通しを得た。正奇数vは0、正の水平次数は恒等、零次は元のsingleの標準同型。この向きは定数列の0/id微分とtotalの水平次数による符号で照合する。同じ包含iとのi≫P=idを示せば、行が完全な定数増大列のtotalから、元のsingleのtotalのacyclicityへretractで戻せる。各列の包含の全射性を仮定しない。まだ実装・検証済みではなく、G4の既存の全複体の比較の証明分割の候補として記録する。

同じ補正付き射影の入力の分割（既存G4の全複体の比較の内数、80〜130行）：A:Module、F:Δ→Cochain、ε:const(C(A))→F に対して `cechConstantAugmentedObject` と `cechSingleAugmentedObject` は元のεとj≫εを増大射に持つ二つの図式。`cechSingleToConstantAugmented` は左で同じj、右で恒等の射。`cechSingleToConstantDouble` はそれを既存B1のaugmentedCochainで写した二重複体の射。零水平成分は元のj、正の水平成分は同じFの恒等である式を含める。補正付き射影Pの構成自体はこの分割の後であり、ここだけでacyclicityの比較が済んだとはしない。

検証待ち中の追加分の計数（2026-11-16 16:18）：固定した十二本823行はSHA256一致を再確認し、同じ検証一件の待ちを維持している。その後に別の下書きとして加えた五本は、FrobeniusArrowMapLaws 91行、RectangularPerfectRowAugmentation 65行、RectangularPerfectRowFunctor 82行、CechConstantComplexAugmentation 63行、CechConstantAugmentedDouble 69行、計370行。いずれも本体未登録・未検証・未コミット。検証済み11,713行に全十七本1,193行と将来の登録17行を加えた見込み上の現物は **12,923行相当**。完成見込み14,600〜17,300行にはこれらも含める。補正付き全複体の射影そのもの・相対proper fppf・F8四角形・Noether帰納・G5は未完。

一覧：済み1／全体3（うち追加0）。

同じ全複体上の補正付き射影の成分の分割（既存G4の全複体の比較の内数、80〜140行）：`cechConstantTotalRetractionComponent` は前記の同じ各直和項の式で、定数増大列のtotalの次数nからsingle増大列の同じtotalの次数nへの射を作る。`…_ι_succ`・`…_ι_zero_zero`・`…_ι_zero_succ` は元の各直和入射での式。ここではまだ微分との可換性やretractionを結論しない。微分との可換性と、同じ包含との合成が恒等である式を次の分割で示す。

同じ補正付き射影の微分の法則（直前の全複体の比較の内数）：`cechConstantAugmentation_vertical` は ε₀.f q とF₀の縦微分の合成が、qの偶奇により0またはε₀.f(q+1)である式。`cechConstantAugmentation_horizontal` は同じε₀.f qの後の水平微分が0である式。前者は元のεの複体の射の法則と定数列の0/id微分、後者は既存B1の増大複体のd²=0の各成分を使う。

同じ補正付き射影の単位の法則（直前の全複体の比較の内数、35〜60行）：`cechConstantTotalRetractionComponent_section` は、元の包含iの実際のtotalの各次数の写像にPの成分を合成すると恒等になる式。正の水平成分は同じ恒等、零次は元のsingleの標準同型の正逆、零水平・正縦次数はsingleの零対象の一意性を使う。Pが複体の射となることを省略せず、その可換性は別途必要。

同じretractから完全性を戻す法則（既存G4の全複体の比較の内数、25〜45行）：C,D:Cochain(Module R)、i:C→D、r:D→C、i≫r=id と D.Acyclic から C.Acyclic を得る `cechComplex_acyclic_of_retraction`。各次数の元のhomologyの射へ単位の式を送り、Dのhomologyが零である既存の判定を使う。導来層コホモロジーとの比較ではなく、同じcochainの内部の既存のhomologyの法則。


## G4：元の矩形の行の自然な係数比較と整数係数の全複体への移送
`CechConstantAugmentation`（41行）：
- `fullCechConstantAugmentation`：同じ空集合の係数から、全てのタプルの有限像への制限による増大。
- `fullCechConstantAugmentation_apply`：同じ全次数の増大の評価は、元の有限像への制限。

`CechIntegerLiftTotalComponents`（88行）：
- `cechIntegerLiftFunctor`：同じ整数係数を、同型な大きい整数環によるスカラー制限で移す同値関手。
- `cechIntegerLiftEquivalence`：同じスカラー制限の正逆と単位を、整数環の異なる宇宙を保って明示した同値。
- `cechIntegerLiftFunctor_map_apply`：同じスカラー制限は、元の準同型の関数を変えない。
- `cechIntegerLiftComplex_exactAt_iff`：同じスカラー制限は、元の複体の各次数の完全性を保ち、反映する。
- `cechIntegerLiftBicomplex`：元の二重複体に、同じ既存の係数関手を二方向へ適用した値。
- `cechIntegerLiftTotalComponentIso`：同じ全複体の各直和と係数移送との、元の余積を保つ標準同型。
- `cechIntegerLiftTotalComponentIso_ι`：同じ直和の標準比較は、元の全複体の各入射を保つ。
- `cechIntegerLiftFunctor.IsEquivalence` のinstance：同じ正逆・単位・余単位から同値を供給する。
- `cechIntegerLiftFunctor.Additive` のinstance：同じスカラー制限の加法性を供給する。

`CechIntegerLiftTotal`（84行）：
- `cechIntegerLiftTotalComponentIso_d`：同じ直和の標準比較は、元の二方向の符号付き微分と可換。
- `cechIntegerLiftTotalIso`：元の全複体を、同じ整数係数の同値関手で移した全複体との標準同型。
- `cechIntegerLiftTotal_acyclic_iff`：同じ整数係数の移送は、元の全複体の完全性を保ち反映する。
- `cechIntegerLiftTotal_acyclic_of_rows`：元の整数係数の行が完全なら、既存のHAの判定により元の全複体も完全。

`CechConstantComplex`（93行）：
- `cechConstantComplex`：定数余単体図式を、同じ既存の交代余面複体関手で写した列。
- `cechConstantComplex_d`：同じ定数列の微分は、元の交代和により0と恒等を交互に取る。
- `cechConstantComplex_exact`：同じ定数列は、元の0/恒等の微分により正次数で完全。
- `cechConstantSingleAugmentation`：同じ零次 single から、元の定数列への標準的な包含。
- `cechConstantSingleAugmentation_f_zero`：同じ包含の零次成分は、元の single の標準同型。
- `cechConstantSingleAugmentation_quasiIso`：同じ零次 single から定数列への包含は、元の増大を保つ準同型。

`RectangularCechTupleIntersection`（50行）：
- `cechOpenIntersection_tupleSupport_eq_iInf`：タプルの有限像の交叉は、重複も含む同じ全座標の交叉。
- `schemeCechTupleIntersection_rectangular`：元の full Čech の交叉を、同じ矩形タプルの転置で表す。
- `openIntersectionFamily_refinement`：元の全座標の交叉は、同じタプルの再添字付けによる交叉に含まれる。

`RectangularCechCoefficients`（92行）：
- `rectangularCechSectionsIso`：元の full Čech の実際の交叉と、同じ矩形の混合積の切断環の標準同型。
- `rectangularCechSectionsIso_augmentation`：元の交叉上への増大は、同じ矩形の混合積の基底の Γ へ移る。
- `rectangularCechMap_le`：元の nerve の射は、同じ有限像の交叉による矩形の開を保つ。
- `rectangularCechSectionsIso_naturality`：同じ矩形の係数比較は、元の交叉上の appLE と全ての単体の射に自然。

`OpenFamilyCechRefinement`（90行）：
- `openFamilyCechRefinementOpen_le`：同じ開の細分は、元のタプル開の包含を与える。
- `openFamilyCechRefinementMap`：同じ開の包含と元の各射影を脚に持つ、混合積の細分の射。
- `openFamilyCechRefinementMap_π`：同じ細分の射の射影は、元の開の包含を持つ。
- `openFamilyCechRefinementMap_base`：同じ細分の射は、元の基底の射を保つ。
- `openFamilyCechRefinementMap_inclusion`：同じ細分の射は、元の nerve への入射を保つ。
- `openFamilyCechRefinementMap_iso`：元のタプル開との標準同型は、同じ開の細分に自然。

`OpenFamilyCechRefinementCoefficients`（63行）：
- `openSections_homOfLE`：同じ開の包含の Γ は、元の前層の制限と標準的に一致する。
- `openFamilyCechSectionsIso_refinement`：同じタプル開の切断と混合積の比較は、元の開の細分の制限に自然。

`FrobeniusDirectLimitRingIsoNaturality`（33行）：
- `frobeniusDirectLimitRingIso_naturality`：同じ元の可換四角に、実際の Frobenius 順極限の環同型は自然。

`OpenFamilyCechPerfectRefinement`（48行）：
- `openFamilyCechPerfectSectionsEquiv_refinement`：同じ開の細分に、元のタプル開と混合積の Frobenius 係数の比較は自然。

`RectangularPerfectRowEquiv`（94行）：
- `rectangularPerfectRowEquiv`：同じ余積射の係数を、元の矩形タプルの実際の係数の積へ移す標準環同型。
- `rectangularPerfectRowEquiv_of`：同じ行の係数比較を有限段で評価すると、元の入射と同じ切断環の逆同型を使う。
- `rectangularPerfectRowEquiv_apply`：元の矩形の切断環の標準比較に戻すと、同じ転置した成分の評価になる。

`RectangularPerfectRowNaturality`（72行）：
- `rectangularPerfectRowEquiv_naturality`：同じ行の係数同型は、元の余積射の nerve と実際の矩形の appLE に自然。


検証：十二本をまとめた下書き検証 `2g-g4-rectangular-refinement-check-5.log` 成功。モジュールごとの直接importも対象ビルドで確認し、整数係数の移送の入口に必要な Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex を追加した。修正した下書きと本体は十二本とも全バイト一致、固定manifestとも照合済み。対象十二本と直接importerの入口のビルドは `2g-g4-rectangular-refinement-native-2.log`、**5,270ジョブ・終了0**。別の共有鍵で、非公開・生成分を含め実際のモジュールの所有宣言を全件監査し、**107宣言・標準三公理のみ・終了0**（`2g-g4-rectangular-refinement-audit.log`）。内訳は上のモジュール順に4、22、12、14、3、9、10、3、1、1、27、1。追加公理・sorry・既存宣言の型変更・資源上限の変更・200行超の宣言なし。unused simp と長行のstyle警告、および入口の既存haveIのstyle警告は残る。鍵は各回 --class impl --wait 3600 で一件ずつ、ビルドと監査は別枠。root・下流全ビルド・AlgebraicGeometry全体監査は行わない。

今回848行＋登録12行＝860行。基準56ea849a3から再計数した外枠計数は **12,573行**（新規177モジュール本体12,350行、既存追加25行、入口198行）。新規所有宣言の小監査累計 **1,232**、既存15宣言は別計上。後続の別下書き七本は525行・登録予定7行で、これらも含めると13,105行相当。完成見込み14,600〜17,300行、承認済み外枠18,000行は不変。

到達点は、元の矩形の各行の実際の係数と水平の全ての単体の射を保つ自然な環の比較、および同じ整数係数の全複体を既存HAの行の完全性へ渡す移送。元の定数列とsingleの包含も準同型であることまで。後続の行の図式への束ね方と増大、補正付き射影の成分と単位はまだ下書き。微分との可換性・相対proper fppf・F8全複体・元の中心を保持するNoether帰納・G5は未完。最終のAugmentedRingCechExactと利用側の型は不変。停止点2g-2ではない。

11-16 16:25の調整役の連絡に従い、略号表の変更を含むmainは取り込んでいない。今の停止点までは現在の枝で継続する。

一覧：済み1／全体3（うち追加0）。

同じ行の図式の束ね方の表記の分割：`rectangularPerfectRowGammaFunctor` は元の交叉族の余積射のnerve.rightOp⋙Γを明示する入口。元の同じ図式を名前で保持し、自然同型の型の elaboration が同じ深い式の照合を繰り返すのを避ける。資源上限は変更しない（同じ係数移送の内数）。

同じ行の自然同型の各次数の分割：`rectangularPerfectRowComponentIso` は既存の同じ環同型を、元の二つの整数加群のModule構造を明示して加群同型へ移す。既存MathlibのAddEquiv.toIntLinearEquivを再利用し、自然同型の組み立てと各次数の照合を別の宣言へ分ける。計算量上限は既定のまま（同じ係数移送の内数）。

同じ補正付き射影の微分との可換性の分割（既存G4の全複体の比較の内数、80〜140行）：`cechConstantTotalRetractionComponent_comm_succ` は正の水平成分で、`…_comm_zero` は零水平・零縦成分で、同じPの成分が元のtotalの微分と可換である式。前者は元の二重複体の正の水平列が同じFであること、後者は元のsingleの標準同型と同じ増大の零次を使う。元の各入射でのtotalの微分の式は、既存HAの同じ補題をimport allで再利用する。正の縦次数の偶奇と全次数の射はさらに必要であり、この二場合だけで比較を完成扱いにしない。

同じ行の各次数の同型の評価の法則：`rectangularPerfectRowComponentIso_hom_apply` はその同じ加群同型の各タプルでの値が、元の矩形の環同型の値と一致する式。自然性の照合はこの評価を介して、検証済みの元の環の自然性へ戻す（同じ係数移送の内数、15〜25行）。

同じ補正付き射影の全次数の分割（既存G4の全複体の比較の内数、140〜220行）：`cechConstantTotalRetractionComponent_comm_zero_succ` は正の縦次数で、定数列の0/idと元の増大の縦・水平の法則によりPとtotalの微分を照合する。`…Component_comm` で各入射から全次数の可換性を得て、`cechConstantTotalRetraction` を元の二つのtotal間の複体の射にする。`…_section` は元の包含との合成が恒等である式、`cechSingleTotal_acyclic_of_constant` は同じretractから元のsingleのtotalの完全性を戻す法則。これは既存G4の同じ増大の比較の分割であり、正次数で包含の全射性を仮定せず、別の最終型へ置き換えない。現在の七本の検証には含めない未検証下書きとする。

同じ射影の各直和項の補助定義の公開：`cechConstantTotalRetractionSummand` は (a,b,n,h:a+b=n) に対し、定数増大列の(a,b)項から元のsingleのtotalの次数nへ、既に記述した同じ成分の式を与える。公開された計算可能な成分定義から参照するため、Leanのmodule可視性に合わせて同じ補助定義も公開する。別の構成や型の変更は行わない（同じ射影成分の分割の内数、20〜30行）。


## G4：同じ行の増大・図式と定数増大列の比較の入力
`FrobeniusArrowMapLaws`（91行）：
- `frobeniusArrowDiagramMap_id`：同じ矢印の有限段の図式の写像は、元の恒等射を保つ。
- `frobeniusArrowDiagramMap_comp`：同じ矢印の有限段の図式の写像は、元の合成を保つ。
- `frobeniusArrowSmallDiagramMap_id`：同じ小さい添字の図式の写像は、元の恒等射を保つ。
- `frobeniusArrowSmallDiagramMap_comp`：同じ小さい添字の図式の写像は、元の合成を保つ。
- `frobeniusDirectLimitArrowMap_id`：同じ実際の Frobenius 順極限の矢印の写像は、元の恒等射を保つ。
- `frobeniusDirectLimitArrowMap_comp`：同じ実際の Frobenius 順極限の矢印の写像は、元の合成を保つ。

`RectangularPerfectRowAugmentation`（68行）：
- `rectangularPerfectRowEquiv_augmentation`：同じ行の標準比較は、元の基底からの増大を元の矩形のappLEへ送る。

`RectangularPerfectRowFunctor`（112行）：
- `rectangularPerfectRowFunctor`：元の二重 Čech の縦次数 k を固定した、同じ実際の水平図式。
- `rectangularPerfectRowFunctor_map_apply`：固定した縦次数の元の写像は、矩形の交叉上の実際の appLE。
- `rectangularPerfectRowGammaFunctor`：元の同じ交叉族の余積射の nerve の実際のΓの図式。
- `rectangularPerfectRowComponentIso`：同じ各次数の環同型を、元の二つの整数加群の構造を明示して移す。
- `rectangularPerfectRowComponentIso_hom_apply`：同じ各次数の加群同型の評価は、元の矩形の係数の同じ環同型。
- `rectangularPerfectRowFunctorIso`：同じ交叉族の nerve の係数と、元の実際の水平図式の自然同型。

`CechConstantComplexAugmentation`（66行）：
- `fullCechConstantComplexAugmentation`：全ての縦次数で、同じ基底の係数を元の有限像への制限で増大する。
- `fullCechConstantComplexAugmentation_apply`：同じ全次数の増大の評価は、元の空集合から有限像への制限。
- `fullCechConstantComplexAugmentation_single_zero`：元のsingleからの包含との合成の零次は、同じ元の増大。

`CechConstantAugmentedDouble`（93行）：
- `cechConstantAugmentedObject`：全ての縦次数に同じAを持つ、元の増大射の図式。
- `cechSingleAugmentedObject`：元の零次singleからの包含を合成した、同じ増大の図式。
- `cechSingleToConstantAugmented`：同じ包含と正の水平列の恒等を持つ、元の増大図式の射。
- `cechSingleToConstantDouble`：同じ包含をB1の既存の増大複体関手で写した二重複体の射。
- `cechSingleToConstantDouble_zero`：零水平成分は、同じ零次singleから定数列への包含。
- `cechSingleToConstantDouble_succ`：正の水平成分は、同じ元のFの恒等写像。
- `cechConstantAugmentation_vertical`：同じ全次数の増大と縦微分の合成は、定数列の元の0/id微分に一致する。
- `cechConstantAugmentation_horizontal`：同じ増大の後の水平微分は、既存B1の二回の微分の零性による。

`CechConstantTotalRetractionComponents`（106行）：
- `cechConstantTotalRetractionSummand`：元の各直和項から、同じ補正付き成分の式でsingleのtotalへ送る。
- `cechConstantTotalRetractionComponent`：同じ各直和項の補正付きの式による、全複体の次数nの射。
- `cechConstantTotalRetractionComponent_ι_succ`：正の水平列では、元の同じ直和入射を保持する。
- `cechConstantTotalRetractionComponent_ι_zero_zero`：零次の基底項は、元のsingleの標準同型で送る。
- `cechConstantTotalRetractionComponent_ι_zero_succ`：正の縦次数では、偶数の場合だけ負の元の増大で隣の水平成分へ補正する。
- `cechConstantTotalRetractionComponent_section`：元の包含のtotalの各次数の射に、同じ補正付き成分を合成すると恒等。

`CechComplexRetractionExact`（31行）：
- `cechComplex_acyclic_of_retraction`：同じ複体のretractは、元の各次数の完全性を保つ。


検証：七本をまとめた下書き検証 `2g-g4-rectangular-extensions-check-7.log` 成功、errorとsorry警告なし。本体のmodule形式でも確認し、公開された計算用の成分が参照する同じ補助定義を公開した。修正後の下書きと本体は七本とも全バイト一致、固定manifestとも照合済み。対象七本と直接importerの入口のビルドは **5,277ジョブ・終了0**（`2g-g4-rectangular-extensions-native-2.log`）。別の共有鍵で非公開・生成分を含む実際の所有宣言を全件小監査し、**70宣言・標準三公理のみ・終了0**（`2g-g4-rectangular-extensions-audit.log`）。上のモジュール順に6、2、21、5、13、22、1。資源上限は既定のまま、各次数のModule構造と評価を明示して自然性の照合を分割した。既存宣言の型変更・追加公理・sorry・200行超の宣言なし。unused section variable、unused simp、unused variable、長行のstyle警告と入口の既存haveIのstyle警告は残る。鍵 --class impl --wait 3600 で一件ずつ、対象ビルドと小監査は別枠。root・下流全ビルド・AlgebraicGeometry全体監査なし。

今回567行＋登録7行＝574行。基準56ea849a3からの外枠計数は **13,147行**（新規184モジュール本体12,917行、既存追加25行、入口205行）。新規所有宣言の小監査累計 **1,302**、既存15宣言は別計上。次の微分との可換性・同じretractからの完全性への接続の二本は196行・登録予定2行で、これらを含めると13,345行相当。完成見込み14,600〜17,300行、承認済み外枠18,000行は不変。

到達点は、元の矩形の各行の全ての水平の射と増大を保つ実際の図式の同型、定数列から全タプル複体への全次数の増大、同じsingleとの包含、および元の全複体上の補正付き射影の各成分と単位則まで。補正付き射影の微分との可換性と、それによる元のsingleのtotalの完全性への接続はまだ未検証の二本。二本の最初の束はmoduleなしでimport allを読めず入口で終了したため、module形式へ直してから証明を検証する。この入口での失敗を証明の検証とは数えない。相対proper fppfへの代入・F8全複体・元の中心を保持するNoether帰納・G5は未完。最終のAugmentedRingCechExactと利用側の型は不変。mainは取り込んでいない。停止点2g-2ではない。

一覧：済み1／全体3（うち追加0）。

同じ全次数の増大を元の開の係数へ代入する法則（既存G4の増大・係数移送の内数、40〜80行）：P:Opens(X)ᵒᵖ→Module R、U、A→P(⊤)に対して `openCoverCechConstantComplexAugmentation` は同じ定数列C(A)から元のfullCechComplex(openCoverCechDiagram P U)へ、元の空交叉と制限の写像で増大する。`…_apply` は各タプルで元の⊤からその実際の交叉への制限を取る式。被覆のアフィン性や平坦性を新たに仮定せず、後で元の構造層のFrobenius図式と同じ基底のスカラーを代入する。現在検証中の二本とは別の未検証下書きとする。

同じ全微分の法則の終域次数の分割（既存G4の全複体の比較の内数、25〜45行）：`cechBicomplex_total_d_summand_to` は元の全微分の各入射での式を、n+1=m という等式を持つ実際の終域mで述べる。総次数を後から式の一部だけで書き換えると、既存HAの非公開の生成された証明項の依存が残るため、mを量化した法則の証明の中で等式を消去して元の同じHAの補題を使う。全複体や選択した余積を変更せず、別の微分を作らない。

調整役の11-16 16:25の連絡を反映：mainのcd79e9cc5は略号表の変更を含み、root未確認である。現在の停止点まではmath/schemeにmainを取り込まない。取り込みを行う場合も、夜のrootビルド完了後とする。現在の検証では枝にある共有鍵を使い、対象ビルドのみを行う。

元の構造層の全次数の増大への代入（既存G4の係数移送・増大の法則、50〜100行）：`schemeStructurePerfectCechConstantAugmentation` はY上の元の大域スカラーφ:R→Γ(Y,⊤)をFrobenius順極限に送り、同じ開被覆の全タプル複体へ定数列C(Rperf)から増大する。`…_apply` は各タプルで、元のφと実際の交叉への制限を合成した環準同型のFrobenius順極限そのものになる式。`…_single_zero` は元のsingleからの包含との合成の零次が既存の増大写像と等しい式。被覆のアフィン性・平坦性や別の最終型を加えない。この代入は別の未検証下書きであり、先行二本の検証済み宣言数には数えない。


## G4：定数増大列から元のsingleへの全複体の射影

検証済みの三本を追加した。元の二つのtotal、同じ直和入射と増大を保持し、補正付き射影が微分を保つことと包含との合成が恒等になることを示した。包含の正次数での全射性は仮定しない。

`CechConstantTotalRetractionDifferential`（81行）：
- `cechBicomplex_total_d_summand_to`：既存HAの同じ全微分の各入射での式を、n+1=mを満たす実際の終域次数mで述べる。
- `cechConstantTotalRetractionComponent_comm_succ`：正の水平成分で、同じ補正付き射影は元のtotalの微分を保つ。
- `cechConstantTotalRetractionComponent_comm_zero`：零水平・零縦成分で、元のsingleの標準同型と同じ増大は全微分と可換。

`CechConstantTotalRetraction`（154行）：
- `cechConstantTotalRetractionComponent_comm_zero_succ`：正の縦次数の偶奇を、元の定数列の0/id微分と増大の縦・水平の法則で照合する。
- `cechConstantTotalRetractionComponent_comm`：元の各直和入射の照合から、同じ補正付き成分は全次数でtotalの微分を保つ。
- `cechConstantTotalRetraction`：元の定数増大列のtotalから同じsingle増大列のtotalへの補正付きの複体の射。
- `cechConstantTotalRetraction_section`：元の包含のtotalに同じ補正付き射影を合成すると、元のsingleのtotalの恒等になる。
- `cechSingleTotal_acyclic_of_constant`：同じretractから、定数増大列のtotalの完全性を元のsingleのtotalへ戻す。

`OpenCoverCechConstantComplexAugmentation`（45行）：
- `openCoverCechConstantComplexAugmentation`：元の大域係数から空交叉への制限を使い、同じ全タプル複体へ全次数で増大する。
- `openCoverCechConstantComplexAugmentation_apply`：各タプルでの評価は、元の全空間から実際の有限交叉への制限。

検証：二本のmodule形式でのまとめた下書き検証 `2g-g4-constant-total-retraction-check-14.log` は終了0。開被覆の一法則も `2g-g4-open-constant-augmentation-check-1.log` で終了0。error・sorry警告なし。二本と入口の対象ビルドは **5,279ジョブ・終了0**（`2g-g4-constant-total-retraction-native.log`）、開被覆の一本と入口は **5,280ジョブ・終了0**（`2g-g4-open-constant-augmentation-native.log`）。下書き・本体・固定manifestのSHA256と全バイト一致を三本とも再確認した。別の共有鍵で非公開・生成分を含む実際の所有宣言を監査し、**36宣言・標準三公理のみ・終了0**（`2g-g4-constant-total-retraction-audit.log`）。上の順に10、23、3宣言。既定の資源上限のまま、同じ式の型の照合をconvertで明示し、元の総複体の選択は変更していない。unused simp・unused tactic・長行等のstyle警告は残る。追加公理・sorry・既存宣言の型変更・200行超の宣言なし。共有鍵は --class impl --wait 3600、一件ずつ。対象ビルドと所有宣言の小監査は別枠。root・下流全ビルド・AlgebraicGeometry全体監査なし。

今回280行＋登録3行＝283行。基準56ea849a3からの外枠計数は **13,430行**（新規187モジュール本体13,197行、既存追加25行、入口208行）。新規所有宣言の小監査累計 **1,338**、既存15宣言は別計上。完成見込み14,600〜17,300行、承認済み外枠18,000行は不変。

到達点は同じ定数増大列から元のsingleのtotalへのretractによる完全性の移送と、元の開被覆の全次数の増大まで。構造層への代入の別下書きは、評価式が通り零次の照合の最後が未検証であり、今回の三本の宣言数に含めない。相対proper fppfへの代入・F8全複体・元の中心を保持するNoether帰納・G5は未完。最終のAugmentedRingCechExactと利用側の型は不変。mainは取り込んでいない。停止点2g-2ではない。

一覧：済み1／全体3（うち追加0）。

同じ全次数の増大の引き戻しの法則（既存G4の自然性の内数、70〜130行）：`schemeStructurePerfectCechConstantAugmentation_naturality` はX→Y、元のφ:R→Γ(Y,⊤)、ψ=f.appTop∘φ、被覆U・Vとその細分ρに対し、元の定数増大と既存refinedPullbackの複体の射の合成が、X側の同じ定数増大と等しい式。全次数を各タプルの評価へ落とし、既存のappLEの自然性とFrobenius順極限の合成則を使う。零次の結果だけを全次数へ拡張したと扱わず、同じ制限の環準同型を照合する。最終型・幾何の仮定は変えない。

同じタプル被覆への全次数の増大の束ね方（既存G4の自然性・増大の法則、90〜170行）：`schemePerfectCechTupleConstantAugmentation` は元の各nerveの基底への射の大域スカラーを前記の増大へ代入し、`…_naturality` は全ての単体の射で元のタプルの前合成を保つ。`…_single` は同じsingleからの包含との合成が既存の零次singleの増大と等しい複体の射である式。`…Hom` は元の関手へ全次数の増大をまとめた自然変換、`…Hom_single` は元の増大図式の同じhomとの一致。元の係数と最終型を保つ法則の分割であり、別の完全性を仮定しない。

元の増大図式と全複体への係数移送の法則（既存G4の同型・増大の内数、65〜115行）：`schemePerfectCechTupleSingleAugmentedIso` は前記の同じsingleの増大と元の増大図式の、左・右で恒等の同型。`schemePerfectCechTupleConstantDouble` は元の全次数の増大をB1の同じ関手に代入したもの。`schemePerfectCechTupleDouble_acyclic_of_constant` は同じ定数増大列のtotalの完全性を、retractと同じ恒等比較で元の `schemePerfectCechTupleDouble` のtotalへ戻す。仮定の完全性を一般のproper fppf射について供給するのは後続であり、ここをその完成とは数えない。

整数加群の係数移送の法則（既存G4の係数移送の内数、70〜130行）：`ringToCechIntegerModule` は元の環・環準同型を同じ整数加群・準同型に見た図式であり、加法群への忘却は既存B1のringToAbと恒等成分で比較する。`cechIntegerAugmented_acyclic_iff` は同じ整数加群の増大余単体図式の完全性が、加法群への忘却後の完全性と同値である法則。`ringCechExact_iff_integer_acyclic` は既存B1のringCechExact_iff_acyclicとmapAugmentedCochainIsoを使い、元のAugmentedRingCechExactを同じ整数加群の複体へ渡す。B1の増大の完全性の証明を作り直さず、元の最終型も変えない。

元のアフィンnerveの増大係数の移送（既存G4の係数・増大・同型の法則、100〜180行）：`affineGammaPerfectAugmentedCoefficients` は元の環のconerveのFrobenius増大係数を、既存のaffineGammaCechConerveIsoで元の幾何的nerveのΓの係数へ移す。`…Iso` は同じ基底で恒等の増大図式の同型。`…_hom_app_apply` は各増大成分が元の基底への射のΓのFrobenius順極限そのものである式。`…_acyclic` はアフィン間の元の平坦全射に対し、既存のAugmentedRingCechExactと整数係数への移送を同じ同型で渡す。一般の非アフィン源のΓの平坦性は仮定しない。

同じ増大二重複体の各行への評価（既存G4の自然性・全複体への移送の内数、40〜80行）：`cechAugmentedDoubleRowIso` はE:Augmented(Cochain(Module ℤ))の同じ縦次数bを評価する操作と、B1のaugmentedCochainの交換同型。`cechIntegerAugmentedDouble_acyclic_of_rows` はその各行の完全性を、検証済みcechIntegerLiftTotal_acyclic_of_rowsに渡して元のtotalの完全性を結論する。新たな対角線の議論は作らず、B1/HAの既存の判定を元の行の係数へ代入する法則。

同じ矩形の増大行への評価（既存G4の増大・係数移送の内数、50〜100行）：`rectangularPerfectAugmentedRow` は元の定数増大図式を縦次数kで評価した同じ増大余単体図式で、`…_left` は元の基底のFrobenius順極限、`…_right` は検証済みの同じ矩形の行の関手である式。`…_hom_app_apply` は各タプルで元の大域スカラーと実際の交叉への制限を合成したFrobenius写像となる。行の係数の完全性の仮定を追加する新しい定理ではなく、同じ増大の評価式。


## G4：元のタプル被覆への全次数の増大と同じ二重複体への移送

検証済みの五本を追加した。元のスカラーと実際の制限の射で全次数に増大し、既存のsingleの増大と同じ射であることを示した。元の増大図式の左右で恒等の同型を使い、定数増大列のtotalの完全性を元の `schemePerfectCechTupleDouble` へ戻す。

`SchemeStructurePerfectCechConstantAugmentation`（63行）：
- `schemeStructurePerfectCechConstantAugmentation`：元の大域スカラーと実際の開への制限による、構造層の全次数の定数増大。
- `schemeStructurePerfectCechConstantAugmentation_apply`：各タプルの値は、同じスカラーと実際の制限の合成のFrobenius順極限。
- `schemeStructurePerfectCechConstantAugmentation_single_zero`：singleの包含との合成の零次は、既存の同じスカラー増大の零次。

`SchemePerfectCechConstantNaturality`（62行）：
- `schemeStructurePerfectCechConstantAugmentation_naturality`：同じスカラーに沿う元の引き戻し・細分は、全次数の増大と可換。

`SchemePerfectCechTupleConstantAugmentation`（88行）：
- `schemePerfectCechTupleConstantAugmentation`：元の各nerveの基底への射に沿う大域スカラーを、同じタプル複体の全次数へ増大する。
- `schemePerfectCechTupleConstantAugmentation_naturality`：元の全ての単体の射に沿うタプルの前合成と同じ増大は可換。
- `schemePerfectCechTupleConstantAugmentation_single`：同じsingleの包含との合成は、既存のsingleの増大写像そのもの。
- `schemePerfectCechTupleConstantAugmentationHom`：元のタプル係数関手への、同じ全次数の増大の自然変換。
- `schemePerfectCechTupleConstantAugmentationHom_single`：元のsingleの包含との合成は、既存の増大図式の同じ自然変換。

`SchemePerfectCechTupleConstantTotal`（62行）：
- `schemePerfectCechTupleSingleAugmentedIso`：元の同じ増大の一致を、左・右で恒等の増大図式の同型にまとめる。
- `schemePerfectCechTupleConstantDouble`：元の全次数の増大をB1の同じ二重複体の関手に代入する。
- `schemePerfectCechTupleDouble_acyclic_of_constant`：同じretractと恒等の比較により、定数増大列のtotalの完全性を元のsingleのタプル複体のtotalへ戻す。

`CechRingIntegerCoefficients`（69行）：
- `ringToCechIntegerModule`：元の環と環準同型を同じ整数加群・準同型に見た係数移送。
- `ringToCechIntegerModuleForgetIso`：元の加法群の係数図式ringToAbとの、恒等成分の同じ比較。
- `cechIntegerAugmented_acyclic_iff`：同じ整数加群の増大複体の完全性は、加法群への忘却で保たれ反映される。
- `ringCechExact_iff_integer_acyclic`：B1の既存の完全性の判定を使い、元のAugmentedRingCechExactを同じ整数加群の複体へ移す。

検証：五本の下書き検証は `2g-g4-scheme-constant-augmentation-check-3.log`、`2g-g4-scheme-constant-naturality-check-1.log`、`2g-g4-tuple-constant-augmentation-check-1.log`、`2g-g4-tuple-constant-total-check-1.log`、`2g-g4-ring-integer-coefficients-check-1.log` が全て終了0。対応する対象と入口の本体ビルドは順に **5,281・5,282・5,283・5,284・5,285ジョブ、全て終了0**（同じ語幹の `-native.log`）。固定manifest・下書き・本体のSHA256と全バイト一致を五本とも確認した。対象ビルドと別の共有鍵で実際の所有宣言を非公開・生成分も含め監査し、**38宣言・標準三公理のみ・終了0**。順に10、2、10、9、7宣言。監査ログは `2g-g4-scheme-constant-augmentation-audit.log`、`2g-g4-tuple-constant-augmentation-audit.log`、`2g-g4-original-tuple-coefficients-audit.log`。追加公理・sorry・既存宣言の型変更・資源上限の引き上げ・200行超の宣言なし。入口と一部ファイルの長行・letI等のstyle警告は残る。共有鍵 --class impl --wait 3600、一件ずつ。root・下流全ビルド・AlgebraicGeometry全体監査なし。

今回344行＋登録5行＝349行。基準56ea849a3からの外枠計数は **13,779行**（新規192モジュール本体13,541行、既存追加25行、入口213行）。新規所有宣言の小監査累計 **1,376**、既存15宣言は別計上。後続の元のアフィンnerveのΓの増大係数と同じ行の評価の二本は、下書き検証のみが成功し、本体ビルド・監査の検証数にはまだ含めない。

完成見込み14,600〜17,300行、承認済み外枠18,000行は不変。残る主要な接続はG4の行の係数比較・相対proper fppf・F8・元の中心を保持するNoether帰納、およびG5の模型の極限・Frobeniusとの交換・元のv被覆への移送。G4・G5は未完で、停止点2g-2ではない。最終のAugmentedRingCechExactと利用側の型は不変。mainは取り込んでいない。

一覧：済み1／全体3（うち追加0）。

Γ–Specの同じ基底のスカラー移送（既存G4の係数移送の内数、45〜85行）：`schemeScalarPerfectRestriction_cancel` はN→Spec Rと開Wに対し、元のRのスカラーをWへ制限したFrobenius写像にΓSpecIso.homのFrobenius写像を合成すると、元の構造射のappLE ⊤ WのFrobenius写像になる式。元のΓ–Specの単位・余単位と環準同型の合成則だけを用い、基底の係数を同じものへ戻す。

同じ増大行の基底を含む係数比較（既存G4の同型・増大の内数、70〜140行）：`rectangularPerfectAugmentedRowIso` は有限交叉族の余積のアフィン性の下で、元の幾何的nerveのΓの増大係数と、元の矩形の増大行との同型。右では検証済みのrectangularPerfectRowFunctorIso、左では同じΓSpecIsoのFrobenius比較を使い、増大はrectangularPerfectRowEquiv_augmentationとschemeScalarPerfectRestriction_cancelで照合する。交叉族の幾何の仮定は既存の有限アフィン族の部品から後で供給し、この同型だけを一般のproper fppfの完全性と呼ばない。

元の有限アフィン被覆の平坦全射への代入（既存G4の行の完全性への代入、75〜150行）：`schemePerfectCechTupleDouble_acyclic_of_augmented_rows` は同じ増大行の完全性を、検証済みの行の評価とretractに渡す。`schemePerfectCechTupleDouble_acyclic_of_flat_surjective` はアフィン対角を持つ源と元の有限アフィン開被覆に対し、平坦全射の同じタプル二重Čechのtotalの完全性を結論する。各非空有限交叉の余積のアフィン性を既存部品で供給し、既存のfiniteAffineOpenIntersectionFamilyFrobeniusCech_exactを前記の同じ増大行の比較に渡す。proper fppfの場合は有限アフィン被覆とアフィン対角を既存の幾何から選ぶ。最終型・被覆によらないことの条件を変えず、非アフィン源のΓの平坦性を仮定しない。


## G4：元の幾何的nerveのΓと同じ増大行

検証済みの三本を追加した。

`AffineGammaPerfectAugmentedCoefficients`（85行）：
- `affineGammaPerfectCoefficientIso`：元の環のconerveと幾何的nerveのΓを、既存の自然同型で同じFrobenius係数へ比較する。
- `affineGammaPerfectAugmentedCoefficients`：同じ基底の係数を保ち、元の幾何的nerveのΓへ移した増大余単体図式。
- `affineGammaPerfectAugmentedCoefficientsIso`：元の環の増大係数との、基底で恒等の標準同型。
- `affineGammaPerfectAugmentedCoefficients_hom_app_apply`：各増大成分は、元の幾何的nerveの基底への射のΓのFrobenius順極限。
- `affineGammaPerfectAugmentedCoefficients_acyclic`：アフィン間の元の平坦全射は、同じ幾何的nerveのΓの増大係数を完全にする。

`CechAugmentedDoubleRows`（43行）：
- `cechAugmentedDoubleRowIso`：同じ縦次数の評価をB1の増大複体と交換し、元の二重複体の各行へ比較する。
- `cechIntegerAugmentedDouble_acyclic_of_rows`：元の各行の完全性を、既存HAの行の判定で同じtotalの完全性へ渡す。

`RectangularPerfectAugmentedRow`（59行）：
- `rectangularPerfectAugmentedRow`：元の定数増大図式を同じ縦次数で評価した、実際の矩形の増大行。
- `rectangularPerfectAugmentedRow_left`：同じ増大行の基底項は、元の基底環のFrobenius順極限。
- `rectangularPerfectAugmentedRow_right`：同じ増大行の右の関手は、元の矩形の行の係数関手。
- `rectangularPerfectAugmentedRow_hom_app_apply`：各増大成分は、元の大域スカラーと実際の交叉への制限の合成のFrobenius写像。

検証：下書きは `2g-g4-affine-gamma-perfect-augmentation-check-1.log`、`2g-g4-augmented-double-rows-check-1.log`、`2g-g4-rectangular-augmented-row-check-1.log` が全て終了0。二本と入口の対象ビルドは **5,287ジョブ・終了0**（`2g-g4-affine-gamma-and-rows-native.log`）、後続の増大行と入口は **5,288ジョブ・終了0**（`2g-g4-rectangular-augmented-row-native.log`）。三本の固定manifest・下書き・本体のSHA256と全バイト一致を再確認した。対象ビルドと別の共有鍵で非公開・生成分も含む実際の所有宣言を小監査し、**25宣言・標準三公理のみ・終了0**（`2g-g4-actual-augmented-rows-audit.log`）。順に11、8、6宣言。追加公理・sorry・既存宣言の型変更・資源上限の引き上げ・200行超の宣言なし。letI・長行等のstyle警告は残る。鍵 --class impl --wait 3600、一件ずつ。root・下流全ビルド・AlgebraicGeometry全体監査なし。

今回187行＋登録3行＝190行。基準56ea849a3からの外枠計数は **13,969行**（新規195モジュール本体13,728行、既存追加25行、入口216行）。新規所有宣言の小監査累計 **1,401**、既存15宣言は別計上。実測と残る接続に合わせ、完成見込みの下端を更新し **15,400〜17,300行** とした。承認済み外枠18,000行は不変。

後続のΓ–Specの同じ基底の係数移送は単独の下書き検証 `2g-g4-scalar-perfect-restriction-check-1.log` が終了0。三本をまとめた後続の下書き検証 `2g-g4-augmented-row-total-check-1.log` は、行の増大を含む同型の型の展開で既定の200,000 heartbeatsに達した。後続の平坦全射のtotalの宣言はその未登録の名前に依存するため、検証済みとは数えない。上限を上げず、同じ係数加群と関手の型を明示して分割する。後続三本は本体未登録・未コミット。

到達点は、元のアフィンnerveのΓの増大係数の完全性と、同じ増大二重複体の各行の自然な比較まで。増大を保つ矩形の行の同型・相対proper fppfへの代入・F8全複体・元の中心を保持するNoether帰納・G5は未完。最終のAugmentedRingCechExactと利用側の型は不変。mainは取り込んでいない。停止点2g-2ではない。

一覧：済み1／全体3（うち追加0）。

同じ増大の可換性の証明の分割（既存G4の増大・係数移送の内数、45〜85行）：`rectangularPerfectAugmentedRow_augmentation` は、元のΓ–SpecのFrobenius写像で基底を戻した増大と、有限交叉族のnerveのΓの増大を矩形の行へ送った値が各タプルで等しい式。元の二つの評価式を先に単独で合成し、その式を行の同型の可換性に渡す。関手の同型と評価式の同時展開による既定heartbeatsの超過を、資源上限を上げず証明を分割して避ける。

同じ行の関手の同型の評価の分割（既存G4の係数移送の内数、30〜55行）：`rectangularPerfectRowFunctorIso_hom_apply` は同じ各成分の評価式を関手の同型の成分へ渡す法則。行の増大の同型の証明では元のΓの大きい比較の定義を展開せず、この同じ評価式と基底の係数移送の評価を使う。

後続F8・帰納への接続の再確認：射影四角形の既存の入口は `projectivePerfectCartesianSquare_acyclic` および同じnativeなスカラーへの `projectivePerfectCartesianScalarSquare_standard_acyclic`。被覆を変えるときは、既存の `CechAugmentedSquare.Map.totalComplex_acyclic_iff_of_cones` に同じ二辺のconeの完全性と基底・中心の全単射性を渡す。別の二重複体の判定を作り直さない。Noether帰納では、一般のProperInductiveLevelのrを射影的と仮定せず、元の閉像に関するwell-foundedな帰納の中で2dの実際のblowup rを選ぶ。任意のNoetherなアフィンTへの底変換後も同じr_Tの射影性と中心外の同型を保持し、中心上の全ての正次数の底変換を同じ厳密に小さい元の閉像の帰納仮定に渡す。T自身の次元が減るとは主張しない。これらの後続のLeanは未実装であり、今回の検証数には含めない。


## G4：同じ増大行の比較と平坦全射のタプル全複体

検証済みの五本を追加した。元の基底のΓ–Specの係数移送と同じ増大行の係数比較をつなぎ、アフィン対角と元の有限アフィン被覆を入力に取る平坦全射の、既存のタプル二重Čechのtotalが完全であることを示した。各有限交叉族の元の環の完全性は既存の有限アフィン族の部品から取り、非アフィンな源のΓの平坦性を仮定しない。

`SchemeScalarPerfectRestriction`（50行）：
- `schemeScalarPerfectRestriction_cancel`：元のスカラーを開Wへ制限したFrobenius写像にΓSpecIso.homのFrobenius写像を合成すると、同じ構造射のappLE ⊤ WのFrobenius写像になる。

`RectangularPerfectAugmentedRowAugmentation`（49行）：
- `rectangularPerfectAugmentedRow_augmentation`：元のΓ–Specで基底を戻した増大と、有限交叉族のnerveのΓの増大を同じ矩形の行へ送った値は、各タプルで等しい。

`RectangularPerfectRowFunctorEvaluation`（33行）：
- `rectangularPerfectRowFunctorIso_hom_apply`：同じ行の関手の同型の評価は、元の各成分の矩形の環同型の評価。

`RectangularPerfectAugmentedRowIso`（76行）：
- `rectangularPerfectAugmentedRowIso`：有限交叉族の余積のアフィン性の下で、同じ幾何的nerveのΓの増大係数と元の矩形の増大行を、基底のΓ–Specの比較と同じ行の係数同型で比較する。

`SchemePerfectCechTupleFlatTotal`（61行）：
- `schemePerfectCechTupleDouble_acyclic_of_augmented_rows`：同じ各増大行の完全性を、既存の行の評価と同じretractで元のsingleのタプル全複体の完全性へ戻す。
- `schemePerfectCechTupleDouble_acyclic_of_flat_surjective`：アフィン対角を持つ源、元の有限アフィン被覆と平坦全射を入力に、同じタプル二重Čechのtotalの完全性を得るČech版。

検証：五本をまとめたmodule形式の下書き検証 `2g-g4-augmented-row-total-check-10.log` は終了0、error・sorry警告なし。下書き・本体・固定manifestのSHA256と全バイト一致を五本とも再確認した。対象五本と直接importerの入口のビルドは **5,293ジョブ・終了0**（`2g-g4-augmented-row-total-native.log`、依存はキャッシュからの再生を含む）。別の共有鍵で非公開・生成分も含む実際の全所有宣言を小監査し、**18宣言・標準三公理のみ・終了0**（`2g-g4-augmented-row-total-audit.log`）。上の順に2、1、1、9、5宣言。大きい関手の定義の展開とゴールの書き換えを避け、同じ評価式を型付けして推移律で直接つなぐことで、既定の200,000 heartbeatsのまま通した。追加公理・sorry・既存宣言の型変更・資源上限の引き上げ・200行超の宣言なし。letIと入口・既存ファイルの長行等のstyle警告は残る。共有鍵 --class impl --wait 3600、一件ずつ。対象ビルドと所有宣言の小監査は別枠。root・下流全ビルド・AlgebraicGeometry全体監査なし。

今回269行＋登録5行＝274行。基準56ea849a3からの外枠計数は **14,243行**（新規200モジュール本体13,997行、既存追加25行、入口221行）。新規所有宣言の小監査累計 **1,419**、既存15宣言は別計上。今回の再開以降の四つの数学の束は、合計16モジュール・本体1,080行＋登録16行、所有宣言117件で、全件が対象ビルドと小監査を通った。

完成見込み15,400〜17,300行、承認済み外枠18,000行は不変。残りの主要な接続は **G4のF8・元の中心を保持するNoether帰納と、G5の模型の極限・Frobeniusとの交換・元のv被覆への移送（計5接続）**。今回の平坦全射の結果は同じ選択した有限アフィン被覆での全複体の完全性であり、一般の固有全射の降下や最終のv被覆の完全性を完成扱いにしない。G4・G5は未完で、停止点2g-2ではない。最終のAugmentedRingCechExactと利用側の型は不変。mainは取り込んでいない。

一覧：済み1／全体3（うち追加0）。

同じF8の可換な図式の全複体への代入（既存G4の係数・全複体の法則、着手前の型）：
- `cechIntegerLiftTotal_acyclic_of_columns`：K:HC₂(Module ℤ,up,up)、各K.X aの完全性から、同じK.totalの完全性を得る（25〜50行）。既存の行の判定をK.flipへ渡し、Mathlibの同じtotalFlipIsoで戻す。新しい対角線・境界消去の証明を作らない。
- `schemePerfectCechTupleSquarePositiveDouble`：既存のschemePerfectCechTupleSquareFunctorを、既存の交代余面複体の関手に代入する。同じ各F8の全複体と実際の単体の射を外方向へまとめる。
- `DegreeOneProjectiveModel.perfectCechTupleSquarePositiveTotal_acyclic`：同じ射影表示、中心のCartesianな四角形、全射性・中心外同型、有限アフィン被覆に対し、前記の同じ外方向の全複体の完全性を得る（前の定義と合わせ50〜90行）。既存のperfectCechTupleSquare_acyclicを各列へ代入する。これだけで元のproper全射の降下を完成扱いにせず、中心側との全複体の比較とNoether帰納は残る。

同じ全複体の係数移送の自然性（既存G4の自然性・係数移送の法則、着手前の型、二本計100〜180行）：
- `cechIntegerLiftBicomplexMap`：既存の整数係数の同値関手を二方向の同じ複体の射へ適用する。
- `cechIntegerLiftTotalComponentIso_naturality`・`cechIntegerLiftTotalIso_naturality`：元の全複体の各直和入射を保つ既存の比較は、同じ二重複体の射に自然。各入射で既存のιTotal_mapと関手の合成則を使う。
- `cechIntegerLiftTotal_quasiIso_iff`：同じ自然な比較と同値関手によって、実際のtotalの射の擬同型性を保ち反映する。
- `cechIntegerLiftTotal_quasiIso_of_columns`：各列が擬同型で各成分が全射の同じ射は、元のtotalでも擬同型。既存HAの同じ定理をULift整数の同じ係数へ適用して戻す。元のHAの型や最終出力の型を変更せず、対角線や核の完全性を証明し直さない。

同じ全複体への短完全性の移送（既存G4の係数移送・有限cone比較の法則、着手前の型、70〜130行）：`cechIntegerLiftTotalShortComplex` は元の短複体の三つの二重複体と同じ二つの射にtotalを取った短複体。`cechIntegerLiftTotal_shortExact` は元の短完全性を同じtotalへ渡す。既存HAのtotalShortExactをULift整数の同じ係数へ適用し、前記の自然なtotalの比較で移す。元の係数へ戻す際は同じ加群の関数の単射性・完全性・全射性で反映する。直和の境界消去やHAの既存の短完全性の証明を作り直さず、元のHAの型も変えない。

同じ定数列の零次への射影（既存G4の単位・係数・有限cone比較の法則、着手前の型、60〜110行）：`cechConstantSingleProjection` は元の定数余単体の複体から同じ零次singleへの標準射影。`cechConstantSingleAugmentation_projection` は元の包含との合成が恒等である式、`cechConstantSingleProjection_quasiIso` は既存の包含の擬同型性から同じ射影の擬同型性を消去で得る。`cechConstantSingleProjection_surjective` は同じ各次数の成分が全射である式。元の定数列の正次数の余分な基底項を除く短完全な比較への供給であり、対角線の境界消去や既存の定数列の完全性の証明を作り直さない。


## G4：F8 の正方向の全複体と係数移送の自然性

検証済みの五本を追加した。元の各F8の全複体と実際の単体の射を保持し、外方向の同じ全複体の完全性を得た。係数の同値による同じtotalの比較は射に自然で、擬同型性と短完全性を元の整数係数へ戻せる。元のHAの型は変更していない。

`CechIntegerLiftTotalColumns`（32行）：
- `cechIntegerLiftTotal_acyclic_of_columns`：各列の完全性を既存の転置・行の判定・totalFlipIsoで同じ整数係数のtotalへ渡す。

`SchemePerfectCechTupleSquarePositiveTotal`（55行）：
- `schemePerfectCechTupleSquarePositiveDouble`：既存のF8の全複体の余単体関手を、同じ交代余面複体の関手へ代入する。
- `DegreeOneProjectiveModel.perfectCechTupleSquarePositiveTotal_acyclic`：元の射影表示、中心のCartesianな四角形、全射性・中心外同型、有限アフィン被覆に対し、実際の外方向の全複体が完全となるČech版。docstringにBST13 Lemma 3.9・BS17 Lemma 4.6(i)、Stacks 30.2.6の比較を形式化しないことを明記した。

`CechIntegerLiftTotalNaturality`（66行）：
- `cechIntegerLiftBicomplexMap`：既存の整数係数の同値関手を同じ二重複体の射へ適用する。
- `cechIntegerLiftTotalComponentIso_naturality`：同じ直和の標準比較は元の射の各成分に自然。
- `cechIntegerLiftTotalIso_naturality`：同じtotalの比較は元の二重複体の射に自然。
- `cechIntegerLiftTotal_quasiIso_iff`：自然な同じ比較と同値関手により、実際のtotalの射の擬同型性を保ち反映する。

`CechIntegerLiftTotalQuasiIso`（36行）：
- `cechIntegerLiftTotal_quasiIso_of_columns`：元の各列の擬同型と各成分の全射性から、既存HAの判定を同じ係数へ適用し、元のtotalの擬同型性へ戻す。

`CechIntegerLiftTotalShortExact`（68行）：
- `cechIntegerLiftTotalShortComplex`：元の短複体の三つの二重複体と同じ二つの射にtotalを取った短複体。
- `cechIntegerLiftTotal_shortExact`：元の短完全性を既存HAのtotalShortExactと同じ自然な比較で元のtotalへ渡す。元の係数への反映は同じ関数の単射性・完全性・全射性による。

検証：二本と三本をまとめたmodule形式の下書き検証は `2g-g4-square-positive-total-check-4.log`・`2g-g4-integer-total-naturality-check-4.log` が終了0。五本と直接importerの入口の対象ビルドは **5,300ジョブ・終了0**（`2g-g4-integer-total-naturality-native.log`、依存のキャッシュ再生を含む）。固定manifest・下書き・本体のSHA256と全バイト一致を五本とも再確認した。対象ビルドと別の共有鍵で、非公開・生成分も含む実際の全所有宣言を監査し **36宣言・標準三公理のみ・終了0**（`2g-g4-integer-total-naturality-audit.log`）。上の順に4、6、10、5、11宣言。追加公理・sorry・既存宣言の型変更・資源上限の引き上げ・200行超の宣言なし。letI等のstyle警告は残る。共有鍵 --class impl --wait 3600、待ちは一件。root・下流全ビルド・AlgebraicGeometry全体監査なし。

今回257行＋登録5行＝262行。基準56ea849a3からの外枠計数は **14,505行**（新規205モジュール本体14,254行、既存追加25行、入口226行）。新規所有宣言の小監査累計 **1,455**、既存15宣言は別計上。完成見込み15,400〜17,300行、承認済み外枠18,000行は不変。

到達点はF8の各項から同じ正方向の全複体への代入と、既存の全複体の自然な係数・擬同型・短完全性の比較まで。中心側との同じ有限coneの全複体の比較・Noether帰納と、G5の模型の極限・Frobeniusとの交換・元のv被覆への移送は残る。一般のproper降下や最終のv被覆の完全性を完成扱いにしない。G4・G5は未完、停止点2g-2ではない。最終のAugmentedRingCechExactと利用側の型は不変。

11-16 16:25の調整役の指示に従い、Citationの変更を含むmain cd79e9cc5は取り込んでいない。次の定数列の射影は未検証の下書きに置き、本体へ登録・コミットしていない。

一覧：済み1／全体3（うち追加0）。

同じ定数列の正次数の比較（既存G4の有限cone・係数移送の法則、着手前の型、90〜150行）：`cechConstantPositiveTail` は元の定数列の零次だけを零加群に置き換え、正次数と微分を保つ複体。`cechConstantPositiveTail_acyclic` は既存の定数列の正次数完全性とd1=idから同じtailの完全性を得る。`cechConstantPositiveTailProjection` と各成分の全射性は、元の列から同じ正次数の商を取り出す。F8の実際の定数基底列の正次数を除く比較の内部の法則であり、新しい降下の仮定を置かない。

同じF8の基底・中心への射影（既存G4の四角形の射・有限cone比較の法則、着手前の型、55〜100行）：`CechAugmentedSquare.baseSquare` は元のCとEを零複体にし、base・centerBase・quotientを保持した同じ四角形。`CechAugmentedSquare.Map.baseProjection` は二つの複体の射を零、基底と中心の射を恒等に取る元の四角形の射。`baseProjection_totalComplexMap_surjective` は、既存のtotalComplexMapの各成分が全射である式。元の構成の射を再利用し、二項複体の微分の可換性を作り直さない。

同じ基底への射影の自然性（既存G4の自然性・合成則の法則、着手前の型、45〜90行）：`CechAugmentedSquare.Map.onBaseSquare` は元の四角形の射mのbaseとcenterを保ち、二つの零複体の射を零に取る同じbaseSquare間の射。`baseProjection_naturality` は m.comp(baseProjection t) = (baseProjection s).comp(onBaseSquare m)。元の四つの成分と合成則だけで示し、実際の余単体図式から定数基底図式への射に渡す。実装・検証の到達点は後続の検証結果の節に記録する。


## G4：定数列の商とF8の基底・中心への自然な射影

元の定数列の零次singleと正次数の商への射影を示し、各F8の四角形の二つの複体を零にした同じ基底・中心への射影を、元の四角形の射に自然にした。基底・中心・その間の商写像を保持し、元の四角形のtotalComplexMapをそのまま使う。次の実際の余単体図式と短完全列への組み立ては、この四本にはまだ含まない。

`CechConstantSingleProjection`（70行）：
- `cechConstantSingleProjection`：元の定数列から同じ零次singleへの標準射影。
- `cechConstantSingleProjection_f_zero`：零次成分は同じsingleの標準同型の逆。
- `cechConstantSingleAugmentation_projection`：元の包含と同じ射影の合成はsingleの恒等。
- `cechConstantSingleProjection_quasiIso`：既存の包含の擬同型性と消去から、同じ射影の擬同型性を得る。
- `cechConstantSingleProjection_surjective`：同じ射影の各成分は全射。

`CechConstantPositiveTail`（96行）：
- `cechConstantPositiveTailTerm`：元の定数列の零次だけを零加群へ置き換えた各項。
- `cechConstantPositiveTailD`：正次数では元の定数列の微分を保つ。
- `cechConstantPositiveTailD_squared`：同じ微分の二乗は零。
- `cechConstantPositiveTail`：同じ正次数の各項と微分を持つ複体。
- `cechConstantPositiveTail_acyclic`：元の定数列の正次数の完全性とd1=idから、同じ商の完全性を得る。
- `cechConstantPositiveTailProjectionComponent`：元の列から同じ商への各成分の射影。
- `cechConstantPositiveTailProjection`：同じ射影は微分を保つ。
- `cechConstantPositiveTailProjection_surjective`：同じ射影の各成分は全射。

`CechAugmentedSquareBaseProjection`（70行）：
- `CechAugmentedSquare.baseSquare`：元のCとEを零複体にし、同じ基底・中心・商写像を保持した四角形。
- `CechAugmentedSquare.Map.baseProjection`：元の四角形から同じ基底四角形への、基底と中心で恒等の射影。
- `CechAugmentedSquare.baseProjection_totalComplexMap_surjective`：既存の同じtotalComplexMapの各成分は全射。

`CechAugmentedSquareBaseProjectionNaturality`（37行）：
- `CechAugmentedSquare.Map.onBaseSquare`：元の四角形の射の基底・中心を、そのまま基底四角形間の射へ渡す。
- `CechAugmentedSquare.baseProjection_naturality`：同じ射影は、元の四角形の射とその合成に自然。


検証：四本をまとめたmodule形式の下書き検証 `2g-g4-constant-quotients-check-1.log` は終了0。四本と直接importerの入口の対象ビルドは **5,304ジョブ・終了0**（`2g-g4-constant-quotients-native.log`、依存のキャッシュ再生を含む）。固定manifest・下書き・本体のSHA256と全バイト一致を四本とも再確認した。対象ビルドと別の共有鍵で、非公開・生成分も含む実際の全所有宣言を監査し **39宣言・標準三公理のみ・終了0**（`2g-g4-constant-quotients-audit.log`）。上の順に9、12、12、6宣言。選ばれた零対象の要素の一意性は、IsZeroから明示して使う。追加公理・sorry・既存宣言の型変更・資源上限の引き上げ・200行超の宣言なし。haveI等のstyle警告は残る。共有鍵 --class impl --wait 3600、待ちは一件。root・下流全ビルド・AlgebraicGeometry全体監査なし。

今回273行＋登録4行＝277行。基準56ea849a3からの外枠計数は **14,782行**（新規209モジュール本体14,527行、既存追加25行、入口230行）。新規所有宣言の小監査累計 **1,494**、既存15宣言は別計上。今回の二つの数学の束は合計9モジュール、本体530行＋登録9行、所有宣言75件で、全件が対象ビルドと小監査を通った。

実測と残る組み立てに合わせ、完成見込みの下端を更新し **16,300〜17,300行** とした。承認済み外枠18,000行は不変。残りは **G4の実際のF8余単体図式への射影・有限coneの短完全列の比較と元の中心を保持するNoether帰納、およびG5の模型の極限・Frobeniusとの交換・元のv被覆への移送**。今回の射影の自然性は各四角形の射に対する法則までで、元の図式への組み立てや一般のproper降下を完成扱いにしない。G4・G5は未完、停止点2g-2ではない。最終のAugmentedRingCechExactと利用側の型は不変。

mainの取り込みは11-16 16:25の指示どおり保留したまま。検証済みはmath/schemeのみにコミットする。

一覧：済み1／全体3（うち追加0）。

実際のF8余単体図式への基底射影（既存G4の自然性・係数移送の法則、着手前の型、75〜140行）：`schemePerfectCechTupleSquareBaseComplex` は同じR・S・qを持つ基底四角形の全複体。`schemePerfectCechTupleSquareBaseProjectionComponent` は各nerve次数の元のF8の全複体からこの同じ複体への射影。`schemePerfectCechTupleSquareBaseProjection` は元のschemePerfectCechTupleSquareFunctorから定数基底図式への自然変換。各単体の射のbase/centerが恒等であることと既存のtotalComplexMap_compを使う。`schemePerfectCechTupleSquareBaseProjection_surjective` は実際の全ての各項の成分の全射性。中心外の同型やNoether帰納の仮定をここでは加えない。

同じ定数基底列の正次数の全複体比較（既存G4の有限cone・係数移送の法則、着手前の型、三本計180〜290行）：`cechConstantCochainComplex A` は複体Aを定数余単体図式として交代余面複体へ写した二重複体。`cechConstantCochainComplex_d_f` は各縦次数の微分を元の定数加群列へ比較する。`cechConstantPositiveDouble A` は外次数0に明示的な零複体を置き、正次数は同じAと元の微分を保つ。`cechConstantPositiveDoubleProjection` は同じ定数二重複体からの各成分全射の射影。`cechConstantPositiveDoubleRowIso` はその各行とcechConstantPositiveTail(A.X b)の同じ項・微分を比較する同型。`cechConstantPositiveDouble_total_acyclic` は既存の行の判定で同じtotalの完全性へ渡す。層コホモロジーの比較や新しい対角線の境界消去は作らない。

同じF8の余分な定数列を除く短完全列（既存G4の有限cone・全複体の法則、着手前の型、100〜180行）：`schemePerfectCechTupleSquarePositiveBaseProjection` は実際のF8の正方向の二重複体から、同じ基底全複体の正次数の商への射。`schemePerfectCechTupleSquarePositiveBaseProjection_surjective` は全成分の全射性。`schemePerfectCechTupleSquareReducedDouble` はこの同じ射の核。`schemePerfectCechTupleSquareReducedShortComplex`・`schemePerfectCechTupleSquareReduced_shortExact` は既存の核の短完全列。`DegreeOneProjectiveModel.perfectCechTupleSquareReducedTotal_acyclic` は元の射影F8の完全性と商の完全性から、同じ核のtotalの完全性を得るČech版。既存のtotalの短完全性とMathlibのHomologySequenceLemmas.acyclic_X₁を使う。中心側との比較とNoether帰納そのものはこの法則だけでは閉じない。


## G4：実際のF8図式から正次数の定数基底列を除く

元のschemePerfectCechTupleSquareFunctorから同じ基底図式への自然変換を作り、同じ定数列の正次数の商へ写した。射影は全ての外次数・縦次数の成分で全射。その実際の核の短完全列と、同じtotalの短完全性を使い、射影F8の完全性をこの核のtotalへ渡した。中心側との比較とNoether帰納を完了したという主張ではない。

`SchemePerfectCechTupleSquareBaseProjection`（73行）：
- `schemePerfectCechTupleSquareBaseComplex`：同じR・S・qだけを保持する基底四角形の全複体。
- `schemePerfectCechTupleSquareBaseProjectionComponent`：各nerve次数の元のF8の全複体から同じ基底全複体への射影。
- `schemePerfectCechTupleSquareBaseProjection_naturality`：実際の単体の射の後に射影すると、元の射影と一致する。
- `schemePerfectCechTupleSquareBaseProjection`：元の実際のF8余単体図式から同じ定数基底図式への自然変換。
- `schemePerfectCechTupleSquareBaseProjection_surjective`：同じ自然変換の各項の全次数の成分は全射。

`CechConstantCochainComplex`（48行）：
- `cechConstantCochainComplex`：同じ複体を定数余単体図式として既存の交代余面複体へ代入した値。
- `cechConstantCochainComplex_d`：元の外微分は0と恒等を交互に取る。
- `cechConstantCochainComplex_d_f`：各縦次数で評価した外微分は、同じ定数加群列の微分。

`CechConstantPositiveDouble`（78行）：
- `cechConstantPositiveDoubleTerm`：外零次に明示的な零複体を置き、正次数では元の複体を保つ各項。
- `cechConstantPositiveDoubleD`：正の外次数で元の定数図式の微分を保つ。
- `cechConstantPositiveDoubleD_squared`：同じ外微分の二乗は零。
- `cechConstantPositiveDouble`：元の定数二重複体の正次数だけを残す商。
- `cechConstantPositiveDoubleProjectionComponent`：元の定数図式から同じ商への射影の各成分。
- `cechConstantPositiveDoubleProjection`：同じ成分からなる二重複体の射。
- `cechConstantPositiveDoubleProjection_surjective`：全ての外次数・縦次数の同じ射影の成分は全射。

`CechConstantPositiveDoubleTotal`（61行）：
- `cechConstantPositiveDoubleRowIso`：同じ商の各行は、元の各加群のcechConstantPositiveTailと、同じ各項・微分を保って同型。
- `cechConstantPositiveDouble_total_acyclic`：同じ商の整数係数のtotalは、既存の行の判定により完全。

`SchemePerfectCechTupleSquareReducedDouble`（112行）：
- `schemePerfectCechTupleSquarePositiveBaseProjection`：実際のF8の正方向の二重複体から、同じ定数基底列の正次数の商への射。
- `schemePerfectCechTupleSquarePositiveBaseProjection_surjective`：実際の同じ射の全ての外次数・縦次数の成分は全射。
- `schemePerfectCechTupleSquareReducedDouble`：元の同じ射の核。
- `schemePerfectCechTupleSquareReducedShortComplex`：元の同じ核の包含と射影からなる短複体。
- `schemePerfectCechTupleSquareReduced_shortExact`：同じ短複体は、既存の核の完全性と元の射の全射性により短完全。
- `DegreeOneProjectiveModel.perfectCechTupleSquareReducedTotal_acyclic`：元の射影表示・中心のCartesian四角形・全射性・中心外同型・有限アフィン被覆の下で、同じ核のtotalが完全となるČech版。既存の射影F8、同じtotalの短完全性、MathlibのHomologySequenceLemmas.acyclic_X₁を使う。docstringにBST13 Lemma 3.9・BS17 Lemma 4.6(i)、Stacks 30.2.6の比較を形式化しないことを明記した。


検証：五本をまとめたmodule形式の下書き検証 `2g-g4-reduced-square-check-3.log` は終了0。五本と直接importerの入口の対象ビルドは **5,309ジョブ・終了0**（`2g-g4-reduced-square-native.log`、依存のキャッシュ再生を含む）。固定manifest・下書き・本体のSHA256と全バイト一致を五本とも再確認した。対象ビルドと別の共有鍵で、非公開・生成分も含む実際の全所有宣言を監査し **44宣言・標準三公理のみ・終了0**（`2g-g4-reduced-square-audit.log`）。上の順に7、4、11、6、16宣言。選ばれた核とAbelian構造、核の包含の単射性・射影の全射性は同じ既存の構造で明示した。追加公理・sorry・既存宣言の型変更・資源上限の引き上げ・200行超の宣言なし。haveI・letI等のstyle警告は残る。共有鍵 --class impl --wait 3600、待ちは一件。root・下流全ビルド・AlgebraicGeometry全体監査なし。

今回372行＋登録5行＝377行。基準56ea849a3からの外枠計数は **15,159行**（新規214モジュール本体14,899行、既存追加25行、入口235行）。新規所有宣言の小監査累計 **1,538**、既存15宣言は別計上。

到達点は、元のF8の実際の全複体から余分な定数基底列を除いた同じ核のtotalの完全性まで。この核を元のY側と中心側の増大二重Čechへ比較すること、元の閉像のNoether帰納、アフィンの出口とG5は未完。最終のAugmentedRingCechExactと利用側の型は不変で、停止点2g-2ではない。

残りを型に沿って再評価すると、中心側・Y側の短完全列300〜550行、同じ全複体と元の増大複体の比較450〜850行、元の閉像のNoether帰納400〜700行、元のアフィン環のČechへの出口250〜500行、G5の模型・Frobenius・filtered余極限の自然な移送600〜1,000行。残り合計 **2,000〜3,600行**、完成見込み **17,159〜18,759行（約17,200〜18,800行）**。前節の16,300〜17,300行を更新する。

承認済み外枠18,000行を超える見込みとなったので、coordination.md §2の規則に従い、検証済みのこの束をコミットした後、この線の新しいLeanの編集・ビルドを止める。別の規模境界報告と、代わりの2h段0の紙を更新する。現在の条件付きの核の完全性をG4の一般の降下やG5の完成扱いにしない。mainは11-16 16:25の指示どおり取り込んでいない。

一覧：済み1／全体3（うち追加0）。


規模境界の紙は [18,000行の境界報告](scheme-w1-2g-2-size-boundary-18000.md) と [2h段0 §11](scheme-w1-2h-route.md) に記録した。検証済みの数学の先端は7b841f924。外枠の判断までこの線の新しいLeanは止め、2hのLeanも始めない。

一覧：済み1／全体3（うち追加0）。


ユーザーの回答「20,000行へ広げて再開（推奨）」により、外枠20,000行で同じ型・範囲のまま再開する。直前の規模境界によるLeanの停止は解除した。mainは取り込まない。

中心側・Y側に分ける同じ四角形の法則（既存G4の有限cone・合成則、着手前の型、二本計120〜220行）：`CechAugmentedSquare.leftSquare` は元のC・base・scalarを保ち、EとcenterBaseを零にした四角形。`rightSquare` は元のE・centerBase・centerを保ち、Cとbaseを零にした四角形。`Map.leftProjection` は元の四角形からleftSquareへの射影、`Map.rightInclusion` はrightSquareから元の四角形への包含。両者の同じtotalComplexMapの合成は零。この同じ二つの射の短複体が各次数で短完全であることを、元の各項の直積の包含・射影で照合する。元の構造層の係数と実際の四角形の辺を保ち、降下の仮定は新しく足さない。

同じ左右の四角形の射の単位・合成・自然性（既存G4の合成則・自然性の法則、着手前の型、90〜180行）：`Map.onLeftSquare`・`Map.onRightSquare` は元の射のC/baseまたはE/centerを保つ射。同じ射のid・compを保ち、`leftProjection_naturality` と `rightInclusion_naturality` で元の四角形の射と可換。この法則を元の実際のF8余単体図式へ渡し、別々の各項の短完全性を単なる点ごとの主張で終わらせない。

実際のF8の左右の短完全列の図式化（既存G4の有限cone・関手の法則、着手前の型、90〜160行）：`schemePerfectCechTupleSquareLeftFunctor`・`…RightFunctor` は同じ各nerve次数のleftSquare・rightSquareのtotalと実際の単体の射を持つ関手。`…LeftProjection`・`…RightInclusion` は元のF8図式の同じ自然変換。`schemePerfectCechTupleSquarePositiveLeftRightShortComplex` は既存の交代余面複体関手に代入した短複体。`…_shortExact` は各外次数で元のleftRight_shortExactを使う短完全性。別々のHの同型を可換な図式の代わりにしない。


## G4：同じ中心側・F8・Y側の短完全列の実際の図式

20,000行での再開後、元のC/baseまたはE/centerを保つ包含・射影を作り、同じ全複体の短完全性を全次数で照合した。同じ射の単位・合成・自然性により、元のF8の実際の余単体図式へ渡し、交代余面複体の同じ二重複体の短完全列を得た。各項のHの同型だけで可換な図式を代用していない。

`CechAugmentedSquareLeftRight`（85行）：
- `CechAugmentedSquare.leftSquare`：元のC・base・scalarを保持し、EとcenterBaseを零にしたY側の四角形。
- `CechAugmentedSquare.rightSquare`：元のE・centerBase・centerを保持し、Cとbaseを零にした中心側の四角形。
- `CechAugmentedSquare.Map.leftProjection`：元の四角形から同じY側への射影。
- `CechAugmentedSquare.Map.rightInclusion`：同じ中心側から元の四角形への包含。
- `CechAugmentedSquare.rightInclusion_leftProjection`：元の同じtotalComplexMapの包含と射影の合成は零。

`CechAugmentedSquareLeftRightExact`（98行）：
- `CechAugmentedSquare.leftRightShortComplex`：元の二つの同じtotalComplexMapからなる短複体。
- `CechAugmentedSquare.leftRight_shortExact`：同じ各項の直積の包含・射影により、全次数で単射・完全性・全射性を照合した短完全性。

`CechAugmentedSquareLeftRightNaturality`（118行）：
- `CechAugmentedSquare.Map.onLeftSquare`：元の射のCとbaseの射を、そのままY側へ渡す。
- `CechAugmentedSquare.Map.onRightSquare`：元の射のEとcenterの射を、そのまま中心側へ渡す。
- `CechAugmentedSquare.Map.onLeftSquare_id`：同じY側への射は単位を保つ。
- `CechAugmentedSquare.Map.onRightSquare_id`：同じ中心側への射は単位を保つ。
- `CechAugmentedSquare.Map.onLeftSquare_comp`：同じY側への射は合成を保つ。
- `CechAugmentedSquare.Map.onRightSquare_comp`：同じ中心側への射は合成を保つ。
- `CechAugmentedSquare.leftProjection_naturality`：元の四角形からY側への射影は、元の射に自然。
- `CechAugmentedSquare.rightInclusion_naturality`：中心側から元の四角形への包含は、元の射に自然。

`SchemePerfectCechTupleSquareLeftRight`（102行）：
- `schemePerfectCechTupleSquareLeftFunctor`：元のF8のY側の各項と全ての実際の単体の射からなる関手。
- `schemePerfectCechTupleSquareRightFunctor`：元のF8の中心側の各項と全ての実際の単体の射からなる関手。
- `schemePerfectCechTupleSquareLeftProjection`：元のF8図式から同じY側の図式への自然な射影。
- `schemePerfectCechTupleSquareRightInclusion`：同じ中心側の図式から元のF8図式への自然な包含。
- `schemePerfectCechTupleSquarePositiveLeftRightShortComplex`：元の包含・射影を既存の交代余面複体関手へ渡した短複体。
- `schemePerfectCechTupleSquarePositiveLeftRight_shortExact`：各外次数で元のleftRight_shortExactを使う、実際の同じ二重複体の短完全性。


検証：四本をまとめたmodule形式の下書き検証 `2g-g4-square-left-right-diagram-check-2.log` は終了0。四本と直接importerの入口の対象ビルドは **5,313ジョブ・終了0**（`2g-g4-square-left-right-diagram-native.log`、依存のキャッシュ再生を含む）。固定manifest・下書き・本体のSHA256と全バイト一致を四本とも再確認した。対象ビルドと別の共有鍵で、非公開・生成分も含む実際の全所有宣言を監査し **54宣言・標準三公理のみ・終了0**（`2g-g4-square-left-right-diagram-audit.log`）。上の順に18、3、15、18宣言。単射性の照合では直積の射影の始域を明示し、元の同じ各項を比較した。追加公理・sorry・既存宣言の型変更・資源上限の引き上げ・200行超の宣言なし。letI・未使用変数等のstyle警告は残る。共有鍵 --class impl --wait 3600、待ちは一件。root・下流全ビルド・AlgebraicGeometry全体監査なし。

再開後の今回403行＋登録4行＝407行。基準56ea849a3からの外枠計数は **15,566行**（新規218モジュール本体15,302行、既存追加25行、入口239行）。新規所有宣言の小監査累計 **1,592**、既存15宣言は別計上。このターンの二つの数学の束は合計9モジュール、本体775行＋登録9行、所有宣言98件で、全件が対象ビルドと小監査を通った。

外枠はユーザーが承認した **20,000行**。境界時点の完成見込み約17,200〜18,800行を暫定の基準とし、次の核の比較と帰納の組み立てで再計測する。残る主要な接続は **同じ基底列への射と核の短完全列、元の増大二重Čechとの比較、元の閉像のNoether帰納、アフィン環のČechへの出口、G5の模型・Frobenius・filtered余極限の移送（5接続）**。

今回の短完全列は実際のF8の同じ正方向の図式のもの。正の定数基底列を除いた核同士の短完全列と元のY側・中心側の比較はまだ未実装である。一般のproper降下・最終のv被覆の完全性を完成扱いにしない。G4・G5は未完で、停止点2g-2ではない。最終のAugmentedRingCechExactと利用側の型は不変。mainは取り込んでいない。

一覧：済み1／全体3（うち追加0）。

正の定数基底列の射・自然性・短完全性（既存G4の単位・合成・係数移送・有限cone比較の法則、着手前の型、三本計150〜260行）：`cechConstantPositiveDoubleMap f` は外零次に明示的零複体の恒等、正次数に同じ複体の射fを置く。id・comp・zeroを保ち、`cechConstantPositiveDoubleFunctor` とそのPreservesZeroMorphismsを与える。`cechConstantPositiveDoubleProjection_naturality` は元の定数図式から同じ商への射影の自然性。`cechConstantPositiveDouble_shortExact` は元の複体の短完全性を同じ正次数の商へ渡す。外零次では零複体、正次数では元の短完全性を使い、対角線の境界消去や新しい降下の判定は作り直さない。

左右へ取った同じ基底射影（既存G4の自然性・係数移送の法則、着手前の型、二本計170〜270行）：`baseProjection_onLeftSquare_totalComplexMap_surjective`・`…onRightSquare…` は、元のMap.baseProjectionへonLeftSquare/onRightSquareを適用した同じtotalの射の全成分の全射性。`schemePerfectCechTupleSquareBaseLeftComplex`・`…BaseRightComplex` は、第0項の同じbaseSquareの左右の全複体。`…BaseLeftProjection`・`…BaseRightProjection` は、実際の左右の余単体図式からこれらの同じ定数図式への自然変換。元のMapレベルの可換性とonLeft/onRightの合成則を使い、別の零複体への無説明な同定をしない。各項の全射性も同じgenericな法則から供給する。

実際の左右と基底列の短完全列の射（既存G4の自然性・有限cone比較の法則、着手前の型、二本計140〜240行）：`schemePerfectCechTupleSquarePositiveBaseLeftProjection`・`…RightProjection` は、元の左右の余単体の射影を交代余面複体と同じ正次数の商へ渡した射。全成分の全射性を保持する。`schemePerfectCechTupleSquareBaseLeftRightShortComplex` は、第0項の同じbaseSquareの左右の短完全列を、正次数の商の関手へ渡した短複体で、同じ短完全性を持つ。`schemePerfectCechTupleSquareBaseComparison` は、実際のF8の左右の短完全列からこの基底列への射。三つの成分を既存の中央と今回の左右の射影に取り、二つの四角の可換性は元のleftProjection_naturality/rightInclusion_naturalityをbaseProjectionへ適用して得る。

既存snake lemmaの同じ核への代入（G4の有限cone比較の証明分割、着手前の型、60〜110行）：Abelianな圏Cの短複体の射φ:S→Tについて、S・Tが短完全でφがepiなら、ShortComplex Cでの同じkernel φは短完全（`cechShortComplexKernel_shortExact`）。MathlibのSnakeInputのL₀_exact・mono_L₀_f・L₁'_exactと、epiのcokernelが零であることだけを使う。`cechShortComplexKernelMiddleIso` は、π₂の既存の核保存による `(kernel φ).X₂ ≅ kernel φ.τ₂`。そのhomと元の核の包含の式も同じkernelComparison_comp_ιから取る。新しいsnake lemmaや一般の9補題の証明を作り直さず、元の中央の核を別のものへ無説明に置き換えない。

同じ核の左右の比較（既存G4の核保存・係数移送の法則、着手前の型、追加20〜35行）：π₁・π₃についても同じ既存のkernelComparisonで `(kernel φ).X₁ ≅ kernel φ.τ₁`、`(kernel φ).X₃ ≅ kernel φ.τ₃` を取る。中央の式と合わせ、選ばれた三つの元の核を保持する。

実際の核の短完全列とF8の消去（既存G4の有限cone比較の証明分割、着手前の型、130〜220行）：`schemePerfectCechTupleSquareKernelSequence` は実際の基底比較の射のShortComplexでの核。三成分の全射性から同じ比較の射のepiを示し、前記の既存snake lemmaへの代入で短完全性を得る。中項は元の `schemePerfectCechTupleSquareReducedDouble` と標準同型で、元の核の包含を保つ。`DegreeOneProjectiveModel.perfectCechTupleSquareLeftKernelTotal_acyclic_of_right` は、元の射影F8の仮定と、同じ中心側の射影の核のtotalの完全性から、同じY側の核のtotalの完全性を得る条件付きのČech版。既存のtotal.mapIso・totalの短完全性・HomologySequenceLemmasを使う。中心側の完全性をNoether帰納から供給する部分はなお未完で、この条件付きの消去を一般の降下の完成と呼ばない。

同じ左右の核の型注釈（既存G4の証明分割、着手前の型、追加15〜30行）：`schemePerfectCechTupleSquareRightKernel`・`…LeftKernel` は、既存の実際の左右の正次数基底射影のkernelそのものにHomologicalComplex₂の型を明示した値。構成・射・仮定を変更せず、totalの入力の型の照合で選ばれた極限の内部を展開しないための分割に使う。


## G4：実際の三つの基底射影の核の短完全列と条件付きの消去

同じ正次数の基底列を射・短完全列に自然にする法則を整え、実際の左右と中央の射影を一つの可換な短複体の射へ束ねた。その三成分は全射で、既存snake lemmaを同じ核へ適用し、実際の核の短完全列を得た。中項は元のschemePerfectCechTupleSquareReducedDoubleと標準同型で、元の包含を保つ。射影F8の仮定の下で、中心側の同じ核のtotalの完全性からY側へ戻す条件付きの消去まで検証した。

`CechConstantPositiveDoubleMap`（54行）：
- `cechConstantPositiveDoubleMapComponent`：外零次の明示的零複体の恒等と、正次数の元の複体の射を成分に取る。
- `cechConstantPositiveDoubleMap`：元の定数図式の射の可換性により、同じ正次数の商の二重複体の射を得る。

`CechConstantPositiveDoubleFunctor`（57行）：
- `cechConstantPositiveDoubleMap_id`：同じ正次数の商の射は単位を保つ。
- `cechConstantPositiveDoubleMap_comp`：同じ正次数の商の射は合成を保つ。
- `cechConstantPositiveDoubleMap_zero`：外零次の零複体の性質と正次数の元の零写像により、零を保つ。
- `cechConstantPositiveDoubleFunctor`：元の複体と射を同じ正次数の商へ送る関手。
- `cechConstantPositiveDoubleFunctor_preservesZeroMorphisms`：同じ関手の零写像保存。

`CechConstantPositiveDoubleExact`（56行）：
- `cechConstantPositiveDoubleProjection_naturality`：元の定数図式から同じ正次数の商への射影は、元の射に自然。
- `cechConstantPositiveDouble_shortExact`：外零次は零複体、正次数は元の短完全列として、同じ関手が短完全性を保つ。

`CechAugmentedSquareBaseLeftRightSurjective`（66行）：
- `CechAugmentedSquare.baseProjection_onLeftSquare_totalComplexMap_surjective`：元のbaseProjectionのY側の同じtotalComplexMapは全次数の成分で全射。
- `CechAugmentedSquare.baseProjection_onRightSquare_totalComplexMap_surjective`：元のbaseProjectionの中心側の同じtotalComplexMapは全次数の成分で全射。

`SchemePerfectCechTupleSquareBaseLeftRight`（97行）：
- private `schemeSquareBaseMap_comm`：実際の単体の射の後に元の基底射影を合成すると、元の射影と一致するMapレベルの式。
- `schemePerfectCechTupleSquareBaseLeftComplex`：元の第0項の同じbaseSquareのY側の全複体。
- `schemePerfectCechTupleSquareBaseRightComplex`：元の第0項の同じbaseSquareの中心側の全複体。
- `schemePerfectCechTupleSquareBaseLeftProjection`：実際のY側の図式から同じ定数基底図式への自然変換。
- `schemePerfectCechTupleSquareBaseRightProjection`：実際の中心側の図式から同じ定数基底図式への自然変換。
- `schemePerfectCechTupleSquareBaseLeftProjection_surjective`：同じY側の自然変換の全成分は全射。
- `schemePerfectCechTupleSquareBaseRightProjection_surjective`：同じ中心側の自然変換の全成分は全射。

`SchemePerfectCechTupleSquarePositiveBaseLeftRight`（67行）：
- `schemePerfectCechTupleSquarePositiveBaseLeftProjection`：実際のY側の自然変換を同じ交代余面複体と正次数の商へ渡した射影。
- `schemePerfectCechTupleSquarePositiveBaseRightProjection`：実際の中心側の自然変換を同じ交代余面複体と正次数の商へ渡した射影。
- `schemePerfectCechTupleSquarePositiveBaseLeftProjection_surjective`：同じY側の射影は全ての外次数・縦次数の成分で全射。
- `schemePerfectCechTupleSquarePositiveBaseRightProjection_surjective`：同じ中心側の射影は全ての外次数・縦次数の成分で全射。

`SchemePerfectCechTupleSquareBaseComparison`（82行）：
- `schemePerfectCechTupleSquareBaseLeftRightShortComplex`：元の第0項のbaseSquareの左右の短複体を、同じ正次数の商の関手へ渡す。
- `schemePerfectCechTupleSquareBaseLeftRight_shortExact`：同じ正次数の基底列は短完全。
- `schemePerfectCechTupleSquareBaseComparison`：実際のF8の左右の短完全列から、同じ基底列への可換な短複体の射。

`CechShortComplexKernelExact`（73行）：
- private `cechKernelSnakeInput`：既存の核・余核をそのままMathlibのSnakeInputへ代入する。
- `cechShortComplexKernel_shortExact`：短完全列間のepiの同じ核は、既存snake lemmaの完全性・単射性と余核の零性により短完全。
- `cechShortComplexKernelLeftIso`：π₁の既存の核保存による、同じ左項と元の左成分の核の標準比較。
- `cechShortComplexKernelRightIso`：π₃の既存の核保存による、同じ右項と元の右成分の核の標準比較。
- `cechShortComplexKernelMiddleIso`：π₂の既存の核保存による、同じ中項と元の中央成分の核の標準比較。
- `cechShortComplexKernelMiddleIso_hom_ι`：同じ中項の比較は元の核の包含を保つ。

`SchemePerfectCechTupleSquareKernelSequence`（148行）：
- `schemePerfectCechTupleSquareKernelSequence`：実際のF8から基底列への射の、ShortComplexでの同じ核の列。
- `schemePerfectCechTupleSquareKernelSequence_shortExact`：元の三成分の全射性と既存snake lemmaの同じ核への代入から得る短完全性。
- `schemePerfectCechTupleSquareKernelSequenceMiddleIso`：同じ列の中項は、元の実際の中央の射影の核schemePerfectCechTupleSquareReducedDoubleと標準同型。
- `schemePerfectCechTupleSquareKernelSequenceMiddleIso_hom_ι`：同じ中項の比較は元の実際の核の包含を保つ。
- `schemePerfectCechTupleSquareRightKernel`：元の実際の中心側の射影のkernelそのものに二重複体の型を明示する。
- `schemePerfectCechTupleSquareLeftKernel`：元の実際のY側の射影のkernelそのものに二重複体の型を明示する。
- `DegreeOneProjectiveModel.perfectCechTupleSquareLeftKernelTotal_acyclic_of_right`：元の射影F8の仮定と同じ中心側の核のtotalの完全性から、同じY側の核のtotalの完全性を得る条件付きのČech版。既存のtotal.mapIso・totalの短完全性・HomologySequenceLemmasを使用し、docstringにBST13 Lemma 3.9・BS17 Lemma 4.6(i)、Stacks 30.2.6の比較を形式化しないことを明記した。

検証：九本をまとめたmodule形式の下書き検証 `2g-g4-square-kernel-sequence-check-4.log` は終了0。九本と直接importerの入口の対象ビルドは **5,322ジョブ・終了0**（`2g-g4-square-kernel-sequence-native.log`、依存のキャッシュ再生を含む）。固定manifest・下書き・本体のSHA256と全バイト一致を九本とも確認した。対象ビルドと別の共有鍵で非公開・生成分も含む実際の全所有宣言を小監査し、**81宣言・標準三公理のみ・終了0**（`2g-g4-square-kernel-sequence-audit.log`）。上の順に6、6、2、2、10、5、10、23、17宣言。大きいkernelの期待型から射を推測する照合を避け、圏・短複体・射を明示し、標準同型とそのtotalを先に型の確定した値へ分割することで、既定200,000 heartbeatsのまま通した。追加公理・sorry・既存宣言の型変更・資源上限の引き上げ・200行超の宣言なし。haveI等のstyle警告は残る。共有鍵 --class impl --wait 3600、待ちは一件。root・下流全ビルド・AlgebraicGeometry全体監査なし。

今回700行＋登録9行＝709行。基準56ea849a3からの外枠計数は **16,275行**（新規227モジュール本体16,002行、既存追加25行、入口248行）。新規所有宣言の小監査累計 **1,673**、既存15宣言は別計上。外枠はユーザー承認済みの20,000行。

残りは、左右の同じ核のtotalと元の増大二重Čechの比較450〜850行、Noether帰納の組み立て（nil不変性、相対proper fppf・合成の消去を含む）400〜700行、元のアフィン環のČechへの出口250〜500行、G5の模型・Frobenius・filtered余極限の移送600〜1,000行。残り合計 **1,700〜3,050行**、完成見込み **17,975〜19,325行（約18,000〜19,400行）** と再計測した。前の約17,200〜18,800行を更新する。

残る主要な接続は **元の増大複体との比較、相対proper fppfと合成を含む元の閉像のNoether帰納、アフィン環のČechへの出口、G5の自然な移送（4接続）**。今回の条件付きの消去のhRightをNoether帰納から供給する部分は未完。相対proper fppfの非アフィン中間基底の接続もこの帰納の組み立てに含め、Spec R上の平坦全射の既存の結果だけで完了扱いにしない。G4・G5は未完、停止点2g-2ではない。最終のAugmentedRingCechExactと利用側の型は不変。mainは取り込んでいない。

一覧：済み1／全体3（うち追加0）。

同じ整数係数のtotalの関手と核保存（既存G4の単位・加法・係数移送・有限cone比較の法則、着手前の型、二本計80〜140行）：`cechIntegerLiftTotalFunctor` は同じMathlibのtotalFunctorを固定した値。各ιTotalで加法性を照合し、既存のcechIntegerLiftTotal_shortExactを同じ関手の短完全性へ渡す。`cechIntegerLiftTotalFunctor_preservesFiniteLimits` は既存のFunctor.preservesFiniteLimits_iff_forall_exact_map_and_monoへの代入。`cechIntegerLiftTotalKernelIso` は同じkernel fのtotalと、同じtotal.map fのkernelとの標準比較で、元の核の包含の式もPreservesKernel.iso_homとkernelComparison_comp_ιから取る。直和の境界消去や核の元の持ち上げを作り直さない。


### 同じtotalの関手と核保存（20,000行承認後）

`CechIntegerLiftTotalFunctor`（44行）：
- `cechIntegerLiftTotalFunctor`：同じMathlibの整数係数のtotalFunctorを固定する。
- `cechIntegerLiftTotalFunctor_additive`：各ιTotalで加法性を照合する。
- `cechIntegerLiftTotalFunctor_shortExact`：既存の同じtotalの短完全性を関手の形へ渡す。

`CechIntegerLiftTotalKernel`（50行）：
- `cechIntegerLiftTotalFunctor_preservesFiniteLimits`：既存の加法性・短完全性をMathlibの有限極限保存判定へ代入する。
- `cechIntegerLiftTotalKernelIso`：同じ核のtotalと同じtotal.mapの核の標準同型。
- `cechIntegerLiftTotalKernelIso_hom_ι`：同型は元の核の包含のtotalを保持する。

検証：module形式の二本の下書き検証 `2g-g4-total-kernel-check-1.log` は終了0。二本と直接importerの入口の対象ビルドは5,324ジョブ・終了0（`2g-g4-total-kernel-native.log`、依存のキャッシュ再生を含む）。固定manifestのSHA256と下書き・本体の全バイト一致を確認。対象ビルドと別の共有鍵による所有宣言の小監査は20宣言（8、12）、非公開・生成分も含め標準三公理のみ、終了0（`2g-g4-total-kernel-audit.log`）。新しい核の元の持ち上げや直和の境界消去は作っていない。追加公理・sorry・既存APIの型変更・資源上限の引き上げ・200行超の宣言なし。

今回94行＋入口2行＝96行。基準56ea849a3からの外枠計数は16,371行（新規229モジュール本体16,096行、既存追加25行、入口250行）。新規所有宣言の小監査累計1,693、既存15宣言は別計上。20,000行の外枠内。完成見込み約18,000〜19,400行を維持する。元の増大二重Čechとの比較は未完で、この標準比較だけでG4を完了扱いにしない。残りは元の増大複体との比較、相対proper fppfと合成を含むNoether帰納、元のアフィン環のČechへの出口、G5の模型・Frobenius・filtered余極限の自然な移送。mainを取り込んでいない。共有鍵 --class impl --wait 3600、待ちは一件、ビルドと監査の間で解放。root・下流全ビルド・AlgebraicGeometry全体監査なし。一覧：済み1／全体3（うち追加0）。


アフィン環の出口に使う既存比較の片側単射の場合（G4の同じtotal比較の証明分割、着手前の型、80〜160行見込み）：`cechShortExact_quasiIso_f_of_acyclic_X₃ (S : ShortComplex (CochainComplex (ModuleCat ℤ) ℕ)) (hS : S.ShortExact) (h₃ : S.X₃.Acyclic) : QuasiIso S.f` を既存の長完全列と零次の単射から示す。`cechIntegerLiftTotal_quasiIso_of_mono_columns (f : K ⟶ L) (hf : ∀ a, QuasiIso (f.f a)) (hm : ∀ a b, Function.Injective (((f.f a).f b).hom)) : QuasiIso (HomologicalComplex₂.total.map f up)` は同じcokernelの短完全列を各列・元のtotalへ渡して取る。Γのsingleからの増大は正次数で全射でないため、既存の全射判定を誤って適用しない。同じ各項・射・totalと最終型は保つ。


同じΓ増大への代入（G4の同じ各列比較の法則、着手前の型、70〜140行見込み）：アフィンなY,Sとf:Y⟶Sに対し `schemePerfectCechTupleGlobalAugmentationHom f U p hp h n` のmonoを、既存の零次増大の単射性と正次数のsingleの零性で示す。元のΓ図式をsingle関手・交代余面関手へ渡した同じ二重複体と同じ増大の射を固定し、そのtotal.mapのQuasiIsoを直前の単射の場合の列比較へ代入して取る。有限アフィン被覆Uの仮定は変えない。この段階では元の基底環の増大項を含む出口は未完とする。


### アフィンnerveの実際のΓ増大のtotal比較

`CechIntegerLiftTotalMonoQuasiIso`（73行）：
- `cechShortExact_quasiIso_f_of_acyclic_X₃`：同じ自然数次数の短完全列の第三項の完全性から第一射の擬同型性を得る。正次数の単射・全射は既存の長完全列、零次の単射はmono_homologyMap_of_mono_of_not_relを使う。
- `cechIntegerLiftTotal_quasiIso_of_mono_columns`：元の二重複体の各列の擬同型と各成分の単射性から、元の同じtotal.mapの擬同型性を得る。余核の短完全列を各列と元のtotalへ渡すだけで、対角線の消去を作り直さない。

`AffineCechNerveTupleGlobalTotal`（78行）：
- `affineCechNerveTupleGlobalAugmentation_mono_f`：アフィンnerveの同じΓ増大の各成分はmono。零次は元のアフィン増大の単射性、正次数はsingleの零性を使う。
- `schemePerfectCechTupleGlobalDouble`：実際のΓのFrobenius係数図式を、同じsingle関手と交代余面関手へ渡した二重複体。
- `schemePerfectCechTupleGlobalDoubleMap`：元の自然なΓ増大を交代余面関手へ渡した実際の二重複体の射。
- `affineCechNerveTupleGlobalTotal_quasiIso`：同じ実際のΓ増大のtotalは擬同型であるČech版。原典の比較と形式化しないStacks 30.2.6の一致をdocstringで明記する。

検証：単射の場合のtotal比較の下書き `2g-g4-mono-total-check-2.log` と、実際のΓ増大への代入 `2g-g4-affine-global-total-check-3.log` は終了0。各対象と直接importerの入口の小ビルドはそれぞれ5,325、5,326ジョブ・終了0（`2g-g4-mono-total-native.log`、`2g-g4-affine-global-total-native.log`、依存のキャッシュ再生を含む）。各成分のmonoを明示した補題へ分割し、曖昧な宇宙のインスタンス推論を回避した。既存宣言の型は変更していない。固定manifestのSHA256と下書き・本体の全バイト一致を二本とも確認。対象ビルドと別の共有鍵による小監査は20宣言（8、12）、非公開・生成分も含め標準三公理のみ・終了0（`2g-g4-affine-global-total-audit.log`）。追加公理・sorry・資源上限の引き上げ・200行超の宣言なし。letI/haveIのstyle警告は残る。

今回151行＋入口2行＝153行。基準56ea849a3からの外枠計数は16,524行（新規231モジュール本体16,247行、既存追加25行、入口252行）。新規所有宣言の小監査累計1,713、既存15宣言は別計上。承認済み20,000行の外枠内。完成見込み約18,000〜19,400行を維持する。アフィン環の出口のうち、増大項を除く実際のΓ図式のtotal比較が閉じた。基底環の増大項を含む出口はなお未完。F8の元の増大複体との比較、相対proper fppfと合成を含むNoether帰納、G5の自然な模型・Frobenius・filtered余極限の移送も残る。G4・G5は未完、停止点2g-2ではない。mainは取り込んでいない。共有鍵 --class impl --wait 3600、待ちは一件、ビルドの間だけ保持し監査前に解放。root・下流全ビルド・AlgebraicGeometry全体監査なし。一覧：済み1／全体3（うち追加0）。


増大項を含む同じΓの比較（G4の既存の係数移送・因子分解の法則、着手前の型、二本計140〜240行見込み）：`schemePerfectCechGlobalAugmented f p hp hR` は同じ基底のFrobenius順極限と同じ実際のnerveのΓ係数の増大図式をまとめる。`schemePerfectCechGlobalSingleAugmented` はこれを既存のsingle関手でwhiskerした値。`schemePerfectCechTupleAugmentedGlobalMap` は零次id・正次数の元のΓ増大からなる同じ増大余単体図式の射で、可換性はschemePerfectCechTupleAugmentationHom_factor_globalそのもの。既存のaugmentedCochainで二重複体の同じ射へ移し、アフィンなY上の有限アフィン被覆なら、各列の既存のΓ増大の擬同型と単射性を直前のtotal比較へ代入する。元のRの増大と全写像を保ち、原典と異なる追加の模型仮定は入れない。


Γのsingleの同じtotalを零次行へ戻す比較（G4の同じ全複体の法則、着手前の型、二本計100〜200行見込み）：`cechIntegerTotalToRowZero_isIso (K : HomologicalComplex₂ (ModuleCat ℤ) up up) (hz : ∀ a b, b ≠ 0 → IsZero ((K.X a).X b)) : IsIso (HomologicalAlgebra.totalToRowZero K)` を元の各ιTotalの式から取る。新しいtotalは作らない。Γのsingleの増大二重複体へ代入し、既存のsingleCompEvalIsoSelfとB1.mapAugmentedCochainIsoを使って、元のModuleCat係数のΓ増大複体との同型を取る。この法則と直前の擬同型により元のタプルtotalの完全性をΓ増大の完全性へ戻す。Γ–Spec・環のconerveへの移送はその後に既存の自然同型で行う。


### 元の基底環の増大を含むΓのtotal比較

`SchemePerfectCechGlobalAugmented`（66行）：
- `schemePerfectCechGlobalScalar`：元の基底環から実際のnerveのΓへのFrobenius係数写像。
- `schemePerfectCechGlobalScalar_naturality`：同じ大域スカラーの係数写像は実際のnerveの射に自然。
- `schemePerfectCechGlobalAugmented`：元の基底項と同じ実際のΓ係数の増大余単体図式。
- `schemePerfectCechGlobalSingleAugmented`：同じ増大図式を既存のsingle関手でwhiskerした値。

`SchemePerfectCechTupleAugmentedGlobal`（89行）：
- `schemePerfectCechTupleAugmentedGlobalMap`：基底項の恒等射と元のΓ増大からなる同じ増大図式の射。既存の増大の因子分解で可換性を取る。
- `schemePerfectCechGlobalAugmentedDouble`：同じΓのsingleの増大図式をB1の既存の複体関手へ渡す。
- `schemePerfectCechTupleAugmentedGlobalDoubleMap`：元の基底の増大を含む、同じ二重複体の実際の比較射。
- `schemePerfectCechTupleAugmentedGlobalDoubleMap_zero`：元の基底項での比較は恒等射。
- `schemePerfectCechTupleAugmentedGlobalDoubleMap_succ`：元の各nerve項の比較は同じΓ増大。
- `affineCechNerveTupleAugmentedGlobalTotal_quasiIso`：アフィンY上の有限アフィン被覆では、元の増大項を含む比較のtotalも擬同型であるČech版。分離的なスキームの準連接層のHとの比較は形式化しないことをdocstringに明記。

検証：個別のΓ図式 `2g-g4-global-augmented-check-1.log` と、二本をまとめたmodule形式 `2g-g4-augmented-global-check-2.log` は終了0。二本と直接importerの入口の対象ビルドは5,328ジョブ・終了0（`2g-g4-augmented-global-native.log`、依存のキャッシュ再生を含む）。固定manifest・下書き・本体のSHA256と全バイト一致を確認。別の共有鍵による所有宣言の小監査は28宣言（15、13）、非公開・生成分も含め標準三公理のみ、終了0（`2g-g4-augmented-global-audit.log`）。既存APIの型変更・追加公理・sorry・資源上限の引き上げ・200行超の宣言なし。

今回155行＋入口2行＝157行。基準56ea849a3からの外枠計数は16,681行（新規233モジュール本体16,402行、既存追加25行、入口254行）。新規所有宣言の小監査累計1,741、既存15宣言は別計上。外枠20,000行、完成見込み約18,000〜19,400行を維持。元の増大Γ複体へtotalから戻す比較は下書きを検証中で、まだ完成扱いにしない。元の環のconerveへの移送、F8の核と元の増大複体の比較、Noether帰納（相対proper fppf・合成を含む）、G5の自然な移送も残る。G4・G5は未完。mainを取り込んでいない。共有鍵 --class impl --wait 3600、待ちは一件。root・下流全ビルド・AlgebraicGeometry全体監査なし。一覧：済み1／全体3（うち追加0）。


元の環の増大conerveへの出口の係数移送（G4の既存の自然同型の増大との整合性、着手前の型、60〜120行見込み）：`affineScalarPerfectAugmentedIso` は既存のaffineScalarPerfectCechIsoとそのaugmentationの式を元の基底で恒等の増大図式の同型へまとめる。`affineScalarPerfectCech_exact_iff_tuple_total_acyclic` は元のスカラーR→Γ(Y)のfrobeniusAugmentedRingCoefficientsのAugmentedRingCechExactと、同じアフィンYのschemePerfectCechTupleDoubleのtotalの完全性を同値にする。ringCechExact_iff_integer_acyclic、直前のΓ増大のtotal比較、既存のaugmentedCochain.mapIsoだけを合成する。最終型AugmentedRingCechExactは変更しない。


### 同じtotalから元の増大Γ複体とスカラー環の出口への比較

`CechIntegerTotalToRowZeroIso`（50行）：
- `cechIntegerTotalToRowZero_isIso`：正の縦次数の各項が零のとき、既存の同じtotalToRowZeroは同型。元の各ιTotalで逆射の二つの合成を照合する。
- `cechIntegerTotalToRowZeroIso`：同じtotalと零次行の標準同型。

`SchemePerfectCechGlobalAugmentedTotal`（80行）：
- `cechSingleAugmentedTotalIso`：元の増大図式にsingleを入れた同じtotalと元の増大複体の標準同型。既存の軸射影、singleCompEvalIsoSelf、B1.mapAugmentedCochainIsoだけを合成する。
- `schemePerfectCechGlobalAugmentedTotalIso`：実際のΓのsingleのtotalと、同じ元の増大Γ複体の標準同型。
- `affineCechNerveTupleAugmentedGlobal_acyclic_iff`：アフィンY上の有限アフィン被覆では、元のタプルtotalの完全性と同じ増大Γ複体の完全性が一致するČech版。

`AffineScalarPerfectTupleTotal`（67行）：
- `affineScalarPerfectAugmentedIso`：元のスカラーR→Γ(Y)の環の増大conerveのFrobenius係数と、同じΓ増大係数の標準同型。基底項では恒等。
- `affineScalarPerfectCech_exact_iff_tuple_total_acyclic`：元のスカラー環準同型のfrobeniusAugmentedRingCoefficientsのAugmentedRingCechExactと、同じアフィンタプルtotalの完全性の同値。最終の述語の型・定義を保つČech版。

検証：三本をまとめたmodule形式の下書き `2g-g4-global-row-zero-check-3.log` は終了0。三本と直接importerの入口の対象ビルドは5,331ジョブ・終了0（`2g-g4-global-row-zero-native.log`、依存のキャッシュ再生を含む）。固定manifest・下書き・本体のSHA256と全バイト一致を確認。別の共有鍵による所有宣言の小監査は31宣言（10、15、6）、非公開・生成分も含め標準三公理のみ、終了0（`2g-g4-global-row-zero-audit.log`）。追加公理・sorry・既存宣言の型変更・資源上限の引き上げ・200行超の宣言なし。haveIのstyle警告は残る。

今回197行＋入口3行＝200行。基準56ea849a3からの外枠計数は16,881行（新規236モジュール本体16,599行、既存追加25行、入口257行）。新規所有宣言の小監査累計1,772、既存15宣言は別計上。20,000行の外枠内で、完成見込み約18,000〜19,400行を維持する。元のスカラー環準同型に対するアフィン環の出口が閉じた。一般のρ:R→Sへ戻すΓSpecの係数移送の法則は明示が残る。F8の核と元の増大複体との比較、相対proper fppf・合成を含むNoether帰納、G5の自然な模型・Frobenius・filtered余極限の移送はなお未完であり、この出口だけでG4を完了扱いにしない。mainは今回の停止点まで取り込まない指示を守っており、未取り込み。共有鍵 --class impl --wait 3600、待ちは一件、対象ビルドと監査は別リース。root・下流全ビルド・AlgebraicGeometry全体監査なし。一覧：済み1／全体3（うち追加0）。


元の任意の環準同型へ戻すΓSpecの係数移送（G4の既存の自然同型の法則、着手前の型、一本文100〜180行見込み）：ρ:R→SのSpec.mapとその実際のスカラーR→Γ(Spec S)について、`specScalarFrobeniusArrowIso` は元のΓSpecIso_inv_naturalityと既存のfrobeniusDirectLimitRingIsoで同じFrobeniusの矢印の同型を取る。`specScalarFrobeniusAugmentedIso` は既存のfrobeniusAugmentedRingCoefficientsIsoと増大conerveの関手で元の増大環図式の同型へ戻す。`ringFrobeniusCech_exact_iff_spec_tuple_total_acyclic` は元のρのAugmentedRingCechExactと同じSpec.map ρのタプルtotalの完全性の同値。標数(p:S)=0はρと(p:R)=0から内部で供給し、最終の仮定を増やさない。


同じF8のY側の成分の座標の法則（G4の元の核のtotal比較の証明分割、着手前の型、一本文80〜160行見込み）：各四角形sとb:ℕについて `leftCι : s.C.X b ⟶ s.leftSquare.totalComplex.X (b+1)`、`leftCπ` はその逆の同じ座標射。零次ではC⁰×0の第一座標、後続では0×Cの第二座標を使い、正逆の式・微分との負符号・Map.onLeftSquareとの自然性・元のスカラーの辺・同じbaseProjectionへの合成零を照合する。これは同じ選択済み零加群・直積の同型を明示する法則で、kernelを別の構成に置き換えず、元の全複体の再索引に使う。


### 任意の元の環準同型の増大図式への出口

`SpecScalarPerfectTupleTotal`（79行）：
- `specScalarFrobeniusArrowIso`：任意の元のρ:R→Sと、同じSpec.map ρの大域スカラーのFrobeniusの矢印の標準同型。ΓSpecIso_inv_naturalityと既存のfrobeniusDirectLimitRingIsoを使う。
- `specScalarFrobeniusAugmentedIso`：元のρの増大Frobenius係数と、同じ大域スカラーの増大係数の標準同型。基底項と全ての正次数の実際の射を保つ。
- `ringFrobeniusCech_exact_iff_spec_tuple_total_acyclic`：元のρのfrobeniusAugmentedRingCoefficientsのAugmentedRingCechExactは、同じSpec.map ρのタプルtotalの完全性と同値。Sの標数条件はρとRの標数条件から内部で供給し、仮定を増やさない。

検証：下書き `2g-g4-spec-scalar-total-check-2.log` は終了0。対象と直接importerの入口の小ビルドは5,332ジョブ・終了0（`2g-g4-spec-scalar-total-native.log`、依存のキャッシュ再生を含む）。固定manifestと下書き・本体のSHA256と全バイト一致を確認。別の共有鍵による所有宣言の小監査は19宣言、非公開・生成分も含め標準三公理のみ、終了0（`2g-g4-spec-scalar-total-audit.log`）。追加公理・sorry・既存宣言の型変更・資源上限の引き上げ・200行超の宣言なし。

今回79行＋入口1行＝80行。基準56ea849a3からの外枠計数は16,961行（新規237モジュール本体16,678行、既存追加25行、入口258行）。新規所有宣言の小監査累計1,791、既存15宣言は別計上。20,000行の外枠内。完成見込み約18,000〜19,400行を維持する。元の任意の環準同型に対するアフィン環の出口が閉じた。F8の核と元の増大複体との比較、Noether帰納（相対proper fppf・合成を含む）、G5の模型・Frobenius・filtered余極限の自然な移送は未完であり、G4・G5はまだ完成扱いにしない。mainは取り込んでいない。共有鍵 --class impl --wait 3600、待ちは一件、対象ビルドと監査は別リース。root・下流全ビルド・AlgebraicGeometry全体監査なし。一覧：済み1／全体3（うち追加0）。


同じF8の中心側の座標の法則（G4の元の核のtotal比較の同じ証明分割、着手前の型、一本文90〜170行見込み）：`rightEι : s.E.X b ⟶ s.rightSquare.totalComplex.X (b+2)` と逆のrightEπ、`rightCenterι : s.centerBase ⟶ s.rightSquare.totalComplex.X 1` と逆のrightCenterπを元の直積の座標で取る。各正逆の式、Eの縦微分、中心からEへの負符号、元のMap.onRightSquareとの自然性、同じbaseProjectionへの合成零を照合する。左右いずれも元の核とtotalは変えず、中心側のunsignedな次数のずらしと符号の照合の入力とする。


元の各直和入射を使うY側のtotal比較の下書き（G4の同じ再索引の法則、着手前の型、一本文70〜150行見込み）：元のschemePerfectCechTupleDoubleの(a+1,b)の項を、同じF8のY側の(a,b+1)へleftCιで入れ、根の(0,0)は元のRのsingleObjXSelfを用い、(0,b+1)は零とする。各写像を既存のtotalDescへ渡して同じ全次数の射を作り、ι_totalDescで各入射の式を固定する。この段階は次数ごとの射であり、微分との可換性・基底射影への合成零・同じ核への持ち上げ・逆射は別途照合する。これらが未検証の間は完成した複体の同型と呼ばない。


夜の共有鍵待機中の下書き：`CechAugmentedSquareLeftComponents.lean`（Y側の同じ座標、縦微分の負符号、自然性、基底射影への合成零）、`CechAugmentedSquareRightComponents.lean`（中心側のE・中心の同じ座標と符号）、`SchemePerfectCechTupleLeftTotalComponents.lean`（元の各ιTotalを使う同じ全次数の再索引の射）をscheme-draftsへ置いた。三本とも本体未登録・未検証・未コミットで、検証済みの実測には算入していない。最初の一本の検証は共有鍵 --class impl --wait 3600 の一件だけで待機中。生存するツールセッションへのpollで待機を確認し、夜の調整役のrootビルドと一括監査の鍵を待っている。待機を失敗・数学的なblockedとは扱わず、同じセッションを継続する。元の増大二重複体から同じ核のtotalへの鎖写像・逆射・二つの合成はなお未完。外枠の検証済み実測16,961行、完成見込み約18,000〜19,400行、承認済み上限20,000行は不変。一覧：済み1／全体3（うち追加0）。


同じ再索引の水平方向の照合（G4の同じ自然性の証明分割、着手前の型、上の再索引下書きに約35〜70行を追記）：`schemePerfectCechTupleLeftCι_horizontal (a b : ℕ)` は元のCの座標の包含とY側の外微分の可換性を、各実際の余面でのleftCι_naturalityを同じ交代和へ渡して示す。`schemePerfectCechTupleLeftBase_horizontal_zero` は元の基底の各余面の恒等射の交代和が零である式。複体の射の可換性はこの二つと既存のleftCι_d・scalar_leftCιから元の各ιTotalで照合する。検証前のため同じ鎖写像の完成とはまだ数えない。


共有鍵待機中の追加の紙：元の各ιTotalからσの微分との可換性を照合する順番をtotal-comparison-routeへ追記した。根の(0,0)、singleの零項(0,b+1)、Cの(a+1,b)の三場合に分け、既存のtotal_d_summand、元のスカラー、同じ各余面の自然性、(-1)^aと縦微分の負符号を使う。元の鎖写像の可換性を仮定する型にはしない。下書きの水平自然性と基底の交代和零を追加したが、本体には未登録で、検証済み実測16,961行は変わらない。同じセッション63342へのpollで共有鍵の一件待機を確認した。停止点2g-2でも数学的なblockedでもない。一覧：済み1／全体3（うち追加0）。


同じ再索引の次数ごとの左逆（G4の同じ分裂の式の証明分割、着手前の型、一本文100〜180行見込み）：`schemePerfectCechTupleLeftTotalRetractionSummand` は元のY側の(a,b+1)のC座標をleftCπで元の(a+1,b)へ戻し、(0,0)の基底だけを元のsingleへ戻し、正の外次数の基底を零へ送る。`schemePerfectCechTupleLeftTotalRetractionComponent` は元のtotalDescへこの各脚を入れた次数ごとの射。元の各ιTotalとleftCι_πからσⁿ≫ψⁿ=𝟙を照合する。ψを鎖写像とは主張せず、元の同じ核の完全性の照合の補助射とする。


元の再索引の鎖写像性（G4の同じ微分との可換性の法則、着手前の型、一本文100〜200行見込み）：`schemePerfectCechTupleLeftTotalComponent_d (n : ℕ)` はσⁿ≫d_L=d_K≫σⁿ⁺¹。既存のtotal_d_summand、元のCの座標の水平自然性・縦微分の負符号・根のスカラー・singleの零性で照合する。`schemePerfectCechTupleLeftTotalMap` はその同じ成分を持つ複体の射。型に微分の可換性を仮定として加えず、同じσから元の核への比較を作る。


### 元のF8の座標・直和の再索引と次数ごとの左逆

`CechAugmentedSquareLeftComponents`（106行、以下の名前空間はCechAugmentedSquare）：
- private instances：元のleftSquareの中心とEの各項の選択済み零加群のSubsingletonを、型を明示して供給する。
- `leftCι`：元のY側の正の縦次数のCの座標への包含。
- `leftCπ`：元のY側の正の縦次数から同じCへの射影。
- `leftCι_π`：Cでの包含・射影の合成は恒等射。
- `leftCπ_ι`：元のY側の各項でも射影・包含の合成は恒等射。
- `leftCι_d`：元のCの座標の縦微分は、同じCの微分の負符号。
- `scalar_leftCι`：元のスカラーと同じCの包含の合成は、元のY側の零次の微分。
- `leftCι_naturality`：同じ包含は元のMap.onLeftSquareに自然。
- `leftCι_baseProjection`：元の基底射影との合成は零。

`CechAugmentedSquareRightComponents`（117行、以下の名前空間はCechAugmentedSquare）：
- private instances：元のrightSquareのCと正次数のsourceの選択済み零加群のSubsingletonを型付きで供給する。
- `rightEι`：元の中心側のEの座標への包含。
- `rightEπ`：元の中心側のEの座標からの射影。
- `rightCenterι`：元の縦一次の中心の座標への包含。
- `rightCenterπ`：元の縦一次の中心の座標からの射影。
- `rightEι_π`：Eでの包含・射影の合成は恒等射。
- `rightEπ_ι`：元の中心側の各正次数でも射影・包含の合成は恒等射。
- `rightCenterι_π`：中心での包含・射影の合成は恒等射。
- `rightCenterπ_ι`：元の縦一次の項でも射影・包含の合成は恒等射。
- `rightEι_d`：Eの座標は元のEの微分を保つ。
- `rightCenterι_d`：元の中心からEへの辺は同じ負符号を持つ。
- `rightEι_naturality`：同じEの包含は元のMap.onRightSquareに自然。
- `rightCenterι_naturality`：同じ中心の包含は元のMap.onRightSquareに自然。
- `rightEι_baseProjection`：元の基底射影との合成は零。

`SchemePerfectCechTupleLeftTotalComponents`（118行）：
- `schemePerfectCechTupleSquareLeftPositiveDouble`：元の同じY側の図式の交代余面複体に型を明示する。
- `schemePerfectCechTupleLeftTotalSummand`：元の各項を同じ全次数のY側の項へ入れる、元の直和の各脚。
- `schemePerfectCechTupleLeftTotalComponent`：同じtotalDescへ各脚を入れた各全次数の射。
- `ι_schemePerfectCechTupleLeftTotalComponent`：元の各直和入射で指定した同じ再索引の脚になる。
- private `cechLeftComponent_sum_f`：複体の射の同じ有限和を各成分で評価する。
- `schemePerfectCechTupleLeftCι_horizontal`：同じCの包含は各実際の余面の交代和の水平微分と可換。
- `schemePerfectCechTupleLeftBase_horizontal_zero`：元の基底の外零次の水平微分は、同じ恒等射二つの交代和で零。

`SchemePerfectCechTupleLeftTotalRetraction`（105行）：
- `schemePerfectCechTupleLeftTotalRetractionSummand`：元のCの座標を戻し、正の外次数の基底だけを零へ送る元の直和の各脚。
- `schemePerfectCechTupleLeftTotalRetractionComponent`：同じtotalDescによる次数ごとの補助射。鎖写像とは主張しない。
- `ι_schemePerfectCechTupleLeftTotalRetractionComponent`：各元の直和入射で、指定した同じ座標の射影になる。
- `schemePerfectCechTupleLeftTotalComponent_retraction`：元の各全次数で、同じ再索引の後に座標を戻すと恒等射。

検証：固定した四本をまとめたmodule形式 `2g-g4-coordinates-check-4.log` は終了0。四本と直接importerの入口の対象ビルドは5,336ジョブ・終了0（`2g-g4-coordinates-native.log`、依存のキャッシュ再生を含む）。固定manifest・下書き・本体のSHA256と全バイト一致を確認。別の共有鍵による所有宣言の小監査は70宣言（12、15、22、21）、非公開・生成分も含め標準三公理のみ、終了0（`2g-g4-coordinates-audit.log`）。追加公理・sorry・既存宣言の型変更・資源上限の引き上げ・200行超の宣言なし。letI/haveIと長い行のstyle警告は残る。零対象の型を明示し、元の微分の定義を局所的に開いて既存のof_dを使い、基底の合成は型の確定したEq.trans/congrArgで照合した。

紙の符号の補助点検：worktree内のcheck-f8-reindexing-signs.pyで、次数0〜16の整数座標における左右の鎖条件・左逆・基底成分の分裂・射影への合成零を2,510件点検して一致した。中心側はunsignedな一段のずらし、Eの(-1)^bと中心の-1を用いた。補助の左逆が一般には鎖写像でないことも点検した。この有限計算はLeanの形式検証の代わりとはしない。

今回446行＋入口4行＝450行。基準56ea849a3からの外枠計数は17,411行（新規241モジュール本体17,124行、既存追加25行、入口262行）。新規所有宣言の小監査累計1,861、既存15宣言は別計上。承認済みの外枠20,000行内。

残りの見込みを更新する。前向きの鎖写像性・基底成分の分裂と同じ核への同型、中心側で同じ左側の比較と既存のextendを再利用する部分は計450〜800行、相対proper fppf・合成を含むNoether帰納400〜700行、G5の自然な模型・Frobenius・filtered余極限の移送600〜1,000行。残り1,450〜2,500行、完成見込み18,861〜19,911行（約18,800〜19,900行）。上端が20,000行に近いので、未検証の下書きも含め以後の各束で照合し、超える見込みになれば検証済みをコミットして境界報告と2hの紙へ移る。現在は超える見込みとはしていない。4本の完成だけでσの鎖写像性や元の核との同型、G4・G5の完成とは呼ばない。前向きの鎖写像性の下書きは未検証で作業木に残している。mainを取り込んでいない。共有鍵 --class impl --wait 3600、待ちは一件、対象ビルドと監査は別リース。root・下流全ビルド・AlgebraicGeometry全体監査なし。一覧：済み1／全体3（うち追加0）。


同じY側の基底射影の成分（G4の同じ核・分裂の式の法則、着手前の型、一本文70〜140行見込み）：元のleftCι/leftCπの二つの合成の式をleftCIsoへまとめ、同じbaseProjection.onLeftSquareの正の縦次数の成分が零であることを取る。実際のschemePerfectCechTupleSquarePositiveBaseLeftProjectionについて、外零次の全成分は零、正の外次数かつ正の縦次数は零、正の外次数の縦零次は元のRの恒等射という三つの式を、同じ構成の定義から照合する。これを元のtotalへ渡し、ψσ+Pr=1とσP=0の照合に用いる。


元の基底射影への合成零（G4の同じ核の法則、着手前の型、一本文100〜180行見込み）：`schemePerfectCechTupleLeftTotalMap_baseProjection` は、元のσと元のschemePerfectCechTupleSquarePositiveBaseLeftProjectionのtotal.mapの合成が零である式。各元のιTotalで、根は外零次の射影零、Cの項は正の縦次数の射影零、singleの正次数は零性を使う。`schemePerfectCechTupleLeftTotalShortComplex` はこの同じ二つの射から作る短複体で、短完全性や核との同型はここで仮定せず別に示す。


同じ基底射影の次数ごとの右逆（G4の同じ分裂の法則、着手前の型、一本文100〜180行見込み）：`schemePerfectCechTupleLeftTotalBaseSectionSummand` は元のQの正の外次数・縦零次のRを同じLの項へ入れ、零の項を零へ送る。`schemePerfectCechTupleLeftTotalBaseSectionComponent` は同じtotalDescを用いる次数ごとの射。元の射影の成分の式とQの他の項の零性からrⁿ≫P.f n=𝟙を照合する。rも鎖写像とは仮定せず、元の射影の全射性とψσ+Pr=1へ用いる。


同じ各全次数の分裂の第二式（G4の同じ核の法則、着手前の型、基底の右逆の下書きに70〜140行を追記）：`schemePerfectCechTupleLeftTotal_split (n : ℕ)` はψⁿ≫σⁿ+P.f n≫rⁿ=𝟙。元のLの各ιTotalで、(0,0)は元のsingleの正逆、(a+1,0)は元のRの射影の恒等式、正の縦次数は元のleftCπ_ιと射影零を用いる。補助射が鎖写像であるとは主張しない。この式を短完全性と元のkernelの普遍性へ渡す。


同じ短完全性への既存APIの代入（G4の同じ核の法則、着手前の型、短複体の下書きへ20〜50行追記）：MathlibのShortComplex.Splittingはr・sとf≫r=1、s≫g=1、r≫f+g≫s=1を受け取り、Splitting.shortExactを供給する。各全次数で元のψ・rと検証する三つの式をそのまま `schemePerfectCechTupleLeftTotalDegreeSplitting n` に入れ、既存のHomologicalComplex.shortExact_of_degreewise_shortExactへ渡す。新しい核の元の持ち上げやModuleCatの完全性の元ごとの証明は作らない。


2026-11-17深夜の検証状況：前向き比較射の鎖写像性と同じ基底射影の成分をまとめたmodule形式の下書き `2g-g4-left-differential-check-3.log` は終了0（131行＋67行）。型の確定した局所射・Eq.trans・congrArgで根と二方向の式を照合した。同じバイトの二本を本体へ移して入口へ登録したが、対象ビルドは共有鍵の唯一のセッション60811で待機中であり、まだコミット・監査済みとはしない。コミット済みの検証実測17,411行に対し、作業木の本体はこの二本と入口200行を含め17,611行。完成見込み18,861〜19,911行はこの候補を含む。元の短複体・基底の右逆・第二の分裂の式・Mathlib.Splittingへの代入の次の二本は未検証の下書きとしてscheme-draftsに置いており、本体未登録・未コミット。最初の対象ビルドと別鍵の監査を終えてから次の下書きを検証する。停止点2g-2ではなく、mainも未取り込み。一覧：済み1／全体3（うち追加0）。


元の同じ核からの完全性の移送（G4の既存の短完全列の法則、着手前の型、短複体の下書きに60〜140行追記）：`schemePerfectCechTupleLeftWholeTotal_acyclic_iff` は同じσの短完全列と元の正次数の基底列の完全性から、L.totalの完全性と元の増大totalの完全性を同値にする。元のPP自体のkernelSequenceをtotalへ渡した既存の短完全列を併用し、`schemePerfectCechTupleLeftKernelTotal_acyclic_iff` は元のsame LeftKernel.totalと元の増大totalの完全性の同値を取る。補助のkernel同型を組み立てる前に、必要な完全性を既存のacyclic_X₁/acyclic_X₂で渡す。同じ射影とkernelのままであり、元の定理の型・仮定は変更しない。


2026-11-17 00:27の更新：前向き比較射と元の基底射影の成分の二本、および直接importerの入口の対象ビルドは5,338ジョブ・終了0（2g-g4-left-differential-native.log、依存のキャッシュ再生を含む）。同じ固定バイトの二本198行と入口2行は対象ビルド済みであり、作業木の本体計数は17,611行。別の共有鍵で所有宣言の小監査を開始し、生存するセッション37527へのpollで待機を確認した。監査はまだ未完のため、二本の数学は未コミット、宣言数・公理の監査成功とはまだ報告しない。検証コミット済みの実測は17,411行。次の基底の右逆・分裂の式と元の短複体の短完全性・元のkernelの完全性の移送の二本は下書きのままで、311行のmodule形式バッチを準備した（未検証・本体未登録）。mainは未取り込み。一覧：済み1／全体3（うち追加0）。
