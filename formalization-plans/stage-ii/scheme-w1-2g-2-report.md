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
