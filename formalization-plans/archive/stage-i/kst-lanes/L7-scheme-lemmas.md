# K-L7：スキーム論と blowup

> **休止（2026-10-19）**：foundations.md v2 の第 II 段で再開する（L7b の残りから）。引き継ぎ節を正本として保持。

## 引き継ぎ（2026-10-19）

### 現在地

- K-L7。K 非依存、正本 §13-13 の分担を維持。新しい工程には進まず停止する。
- L7a 完了：一般スキームの通常 blowup、例外 Cartier 因子、正の冪比較、固有性、中心外同型。
- L7b 進行中：有限基礎加群の平坦化、実分裂／射影代数を入力する自由化中心、中心の降下・合成、strict transform の幾何は証明済み。
- Stacks 05CG・05DJ・05DK・05DM・05DP、059X の Noether 特殊形、忠実平坦降下、局所化と完備化による射影性判定は証明済み。
- 今回の区切りは Stacks 051R の多項式商の場合。非零な先頭係数の積を反転し、実際の標準単項式基底から自由性を証明した。
- 一般の 05FS、一般の L7b、L7c の本体は未完了。条件付きの中心存在を一般平坦化の完成とは呼ばない。
- 検証済みコミット：`4adf352c`。対象ビルド成功（3705 jobs）、公理監査成功（2003 宣言、標準三公理のみ）。

### 残り（依存順、時間は概算）

- Stacks 051R：多項式商の局所化とテンソル基底変更の比較を構成し、有限型代数の一般自由性へ移送する（1–3 時間）。
- Stacks 05FS, Lemma 38.9.2：一般自由性・Noether 帰納法・証明済みの剰余／完備化／忠実平坦降下を接続し、代数の射影性の存在を完成する（8–20 時間）。
- Stacks 0811 と 0810：相対 Noether 正規化・支持次元の devissage を実装し、実分裂を入力する現在の中心存在から一般有限型加群の平坦化へ進む（16–40 時間）。
- Stacks 081T, Lemma 38.31.4／Temkin 2008 Lemma 2.1.5：上記の平坦化中心を strict transform と大域貼り合わせへ接続し、固定済みの Noether 特殊形を完成する（8–20 時間）。
- KST Prop 5.2：鳩ノ巣による共通冪、核の消滅、Artin–Rees による交わり消滅（4–8 時間）。
- Huneke–Swanson 8.1.5・8.2.1／KST Lemma 5.6 古典部分：生成元毎の二乗とイデアル平方を区別し、Rees 拡大の整性・有限性から有限射を構成（8–20 時間）。
- KST Remark 3.3／Lemma 5.5 の幾何入力：K-L5 の対象確定後、別対象間の閉埋め込みと中心外同型を接続する（界面受領後 4–12 時間）。K/pro の結論は K-L6。

### 主要宣言（名前のみ）

- `blowup`、`blowupπ`、`blowupPowerIso`
- `exists_noetherian_finite_flattening_center`
- `exists_admissible_composition_domination`
- `exists_domination_of_flat_schematicallyDense_strictTransform`
- `exists_fg_center_boundaryFreeOpenPullbacks_of_split`
- `exists_fg_center_boundaryFreeOpenPullbacks_of_projective`
- `projective_of_countable_flat_mittagLeffler`
- `projective_of_complete_of_fibre_associatedPrimes`
- `faithfullyFlat_localization_completion_product`
- `projective_of_countable_flat_of_localization_completion`
- `projective_reduction_baseChange`
- `projective_geometricallyIntegral_completion_baseChange`
- `projective_geometricallyIntegral_of_free_localization_of_projective_reduction`
- `exists_finite_leading_degree_cover`
- `standardMonomialQuotientBasis`
- `leading_degree_cover_localization`
- `exists_nonzero_free_polynomial_quotient_localization`

### 依存と提供

- 読み取り専用の既存環論：`CommutativeAlgebra.GradedSubquotient`、`AdicCompletionTensor`、`AdicCompletionFlat`、`AdicCompletionNoetherian`。
- Mathlib の Proj・局所化・イデアル層・テンソル積・単項式順序／除法を使用。K のモジュールは依存に含めない。
- K-L5 に通常 blowup、冪比較、中心外同型、普遍写像を提供。導来 blowup の underlying scheme は別対象として受領する。
- K-L6 に古典的幾何入力を提供予定。Lemma 5.5・Claim 5.3・Prop 5.4 の K/pro の結論は同レーン担当。

### 未コミット

- 所有ディレクトリ・集約・監査スクリプトの検証済み Lean 差分はコミット済み。本引き継ぎ節は別の文書コミットで保存する。
- 共有 `SerrePositivity.lean` の `public import SerrePositivity.KST.SchemeLemmas` 一行は追加済みだが未コミット。他レーンの import 追加と混在し、ファイル全体の `git commit --only` が他者の差分を含むため残す。
- 他レーンの共有作業ツリー差分は本レーンのコミット対象外。

### 既知の問題

- L7 の import 閉包・対象ビルド・公理監査は正常。追加公理・sorry は導入していない。
- 前回の工程区切りの全体ビルドは他レーン `InfinityCategories/F1/CoherentHomComparison.lean:167` の simp エラーで失敗。今回の区切りでは全体ビルドを再実行していない。
- `ModelCategory SSet` の instance 仮定は本レーンでは使用しない。既知の宣言名衝突はない。
- 実分裂／射影性の入力を 05FS の存在証明に読み替えない。`X̃` を `affineBlowup I` と定義しない。
- `Finset.image` を型に使う際は DecidableEq が必要。標準単項式の基底は同一 universe の有限変数型と係数環を使う現在の宣言を正本とする。

### 次の一手

- `GenericFreePolynomialQuotient.lean` を起点に、局所化後の多項式商と元の商のテンソル基底変更との実際の線形／代数同型を構成する。有限型代数への移送だけを次の保存単位とし、対象ビルドと既存監査を通す。

作成日：2026-10-18。
レーン名：K-L7（スキーム論と blowup）。
正本：`formalization-plans/archive/stage-i/kst-lanes/k-theory-kst-route.md`。
共通の決定：`formalization-plans/archive/stage-i/infinity-lanes/foundations.md`。
本文は作業履歴ではなく、現在の設計と受入条件を記す。
実施の経緯は個々のコミットメッセージに記す。

## 2. 目標

1. イデアルの blowup を実際のスキームとして構成する。
2. 構造射を定義して基底を明記する。
3. 中心の逆像を閉部分スキームとして定義する。
4. 逆像イデアルが可逆であることを証明する。
5. 例外閉部分スキームの有効 Cartier 性を証明する。
6. 正の冪に対する blowup の同型を証明する。
7. 有限生成中心に対する固有性を証明する。
8. 中心の補開集合上の同型を証明する。
9. 固有な modification を支配する blowup を構成する。
10. KST §5 の古典的な環論とスキーム論を証明する。
11. 既存の K 理論・導来幾何に依存させない。
12. 公開定理の全公理依存を標準三公理に限る。

## 3. 所有範囲

- Lean ソースは `SerrePositivity/KST/SchemeLemmas/`。
- namespace は `SerrePositivity.KST.SchemeLemmas`。
- 集約は `SerrePositivity/KST/SchemeLemmas.lean`。
- ルートには当該集約の `public import` 一行だけを加える。
- 公理監査は `scripts/audit_kst_scheme_lemmas.lean`。
- 本計画の変更は本レーンが行う。
- `CommutativeAlgebra/` は読み取り専用。
- 他レーンの計画・実装・監査を変更しない。
- KST 正本の変更も本レーンでは行わない。
- 導来 blowup は K-L5 の所有。
- pro 対象の一般論は K-L6 の所有。
- §10 の紙の検証の正本は K-L11 の所有。

## 4. 原典との対応

| 原典 | 内容 | 本レーンでの扱い |
| --- | --- | --- |
| KST §5.1、Prop 5.2 | 有限な抽象 blowup | 環論部分を証明 |
| KST §5.2、Claim 5.3 | 左逆元による帰着 | スキーム射の部分を証明 |
| KST §5.2、Prop 5.4 | 実際の blowup への帰着 | 支配射と左逆元の部分を証明 |
| KST §5.3、Lemma 5.5(i) | 導来構成と古典的構成の比較 | 古典的入力を証明 |
| KST §5.3、Lemma 5.5(ii)(iii) | 二重添字の消滅 | §10-9 の検証後に接続 |
| KST Lemma 5.6 | 有限射と blowup の塔 | 古典的有限射を本レーンで証明 |
| Stacks 081T | modification の blowup 支配 | Noether な特殊形から証明 |
| Stacks 01WQ Lemma 31.14.2 | 有効 Cartier 条件のアフィン局所モデル | 実際の商の Spec と包含射で定義・検証 |
| Temkin 2008 Lemma 2.1.5 | 同上の KST の引用元 | 番号を併記 |
| Huneke–Swanson Prop 8.1.5 | reduction と Rees 代数 | 原文の仮定を確認して証明 |
| Huneke–Swanson Thm 8.2.1 | 整依存と reduction | 有限射への適用を証明 |
| Artin–Rees | 冪と核の交わり | Mathlib の実証明を適用 |

KST は Kerz–Strunk–Tamme, *Algebraic K-theory and descent for blow-ups*。
基準の版は arXiv:1611.08466v4（2017-08-16）。
Stacks はタグを固定し、節番号変更による混同を避ける。
081T は取得時点で Lemma 38.31.4。
Temkin の対象は *Desingularization of quasi-excellent schemes in char 0*。
別の Temkin 論文の同番号と混同しない。
書籍の番号は Proposition と Theorem を区別する。
原文未確認の主張は確認済みと記さない。

## 5. 利用できる基盤

### 5.1 Mathlib の環論

- `reesAlgebra I` は `R[X]` の部分代数。
- 係数の条件は `f.coeff n ∈ I ^ n`。
- `reesAlgebra.monomial_mem` が単項式の所属を判定する。
- `reesAlgebra.as_sum_support` が有限和分解を与える。
- `adjoin_monomial_eq_reesAlgebra` が次数一生成性を与える。
- `reesAlgebra.fg` が有限生成性を与える。
- Noether 環上の有限型性は既存の instance。
- Rees 代数の Noether 性も既存の instance。
- `Ideal.exists_pow_inf_eq_pow_smul` が Artin–Rees を与える。
- 局所化と冪の写像の補題は既存 API を調べて適用する。
- Veronese の Proj 同型は独立した不足 API とする。

### 5.2 Mathlib のスキーム論

- `AlgebraicGeometry.Proj` が実際のスキームを返す。
- `Proj.toSpecZero` が零次成分の Spec への射を返す。
- `Proj.basicOpenIsoSpec` が斉次局所化のチャートを与える。
- `Proj.affineOpenCover` が Proj のアフィン開被覆を与える。
- 有限型な次数付き環の構造射は固有。
- `Proj.map` は次数を保つ準同型に対して定義済み。
- 冪の比較で必要な次数変更は通常の `Proj.map` と区別する。
- スキームの gluing は既存 API を使う。
- `Scheme.IdealSheafData` の局所表示 API を確認する。
- `IsClosedImmersion.of_comp` を切断に適用する。
- 等化子の閉埋め込みは `isClosedImmersion_equalizer_ι_left` を使う。
- 固有射の基底変換と合成に関する instance を使う。

### 5.3 リポジトリの環論

- `CommutativeAlgebra/ReesModule.lean` を読む。
- `CommutativeAlgebra/ReesModuleGrading.lean` を読む。
- Rees 加群の斉次成分の内部直和を参考にする。
- `CommutativeAlgebra/ArtinReesGrowth.lean` を読む。
- 正則列の既存宣言の仮定と依存を確認する。
- 必要な既存宣言は直接 import する。
- 未証明入力を含む大きな集約 import は避ける。
- 同じ定理を実装する前に利用可能性を確認する。

## 6. L7a：blowup

### 6.1 アフィン構成

1. `reesGrade I n` を Rees 代数内の次数 n 成分として定義する。
2. 係数条件による所属判定を証明する。
3. 零・加法・加法逆元について閉じることを証明する。
4. 次数 n、m の積が次数 n+m に属することを証明する。
5. 各 Rees 多項式の単項式分解を定義する。
6. 分解写像の加法性を証明する。
7. 分解と再構成が互いに逆であることを証明する。
8. `GradedRing` の instance を構成する。
9. 零次成分と基礎環の環同型を構成する。
10. `affineBlowup I := Proj (reesGrade I)` を定義する。
11. 零次成分の Spec 同型を通して構造射を定義する。
12. 基礎環の有限型性を零次成分上に移す。
13. 有限生成中心について構造射の固有性を証明する。
14. `I = ⊤` と `I = ⊥` の端点を検証する。

### 6.2 チャートと補開集合

1. a ∈ I に対する次数一単項式を定義する。
2. 標準開集合 D₊(at) の局所化環を記述する。
3. 分数 a/b の関係を斉次局所化で表す。
4. a が基礎環で可逆ならチャートが基底の D(a) と一致することを示す。
5. 標準開集合の重なりで環準同型の一致を示す。
6. D(I) 上の同型を貼り合わせる。
7. 同型と構造射の合成の等式を証明する。
8. 中心を避ける開集合への制限と両立することを示す。

### 6.3 例外閉部分スキーム

1. 中心 V(I) の逆像を閉部分スキームとして作る。
2. 逆像イデアルが各チャートで a に生成されることを示す。
3. チャート内の a が非零因子であることを示す。
4. 基礎環内での a の非零因子性は仮定しない。
5. 局所化の関係から Rees チャート上の性質を示す。
6. チャート間の生成元の比が単元であることを示す。
7. 可逆イデアルを貼り合わせる。
8. 有効 Cartier 因子としての例外因子を構成する。
9. O(1) = I O と符号規約を対応させる。
10. O(-1) = O(E) と記す場合の双対の向きを確認する。

### 6.4 冪と一般スキーム

1. n > 0 を明示する。
2. Rees(I^n) と Rees(I) の n 次 Veronese を比較する。
3. 環の同型と次数の再添字を区別する。
4. 斉次局所化の零次環の同型を作る。
5. 基本開集合上で Proj 同型を構成する。
6. 重なり上で同型が一致することを証明する。
7. 基礎スキーム上の同型であることを証明する。
8. アフィン局所化と blowup の可換性を証明する。
9. 一般のイデアル層に対して貼り合わせる。
10. アフィン被覆の選択への非依存を同型で表す。
11. 一般スキーム上の構造射を定義する。
12. 有限型な中心について固有性を局所化する。
13. 補開集合上の同型と例外因子を貼り合わせる。

## 8. L7c：KST §5 の古典的部分

### 8.1 Prop 5.2

1. A → B の有限性と補開集合上の同型を正確に仮定する。
2. A のイデアル I と B 内での拡大を区別する。
3. 有限生成性により局所化での消滅指数を有限個選ぶ。
4. 鳩ノ巣原理で共通の冪 N を作る。
5. I^N B ⊆ image(A → B) を証明する。
6. 核の各生成元の消滅指数を求める。
7. 共通冪で核を消す。
8. Artin–Rees を核部分加群に適用する。
9. 十分大きい N に対し I^N ∩ ker(A → B) = 0 を示す。
10. 大きい指数への単調性を別に証明する。
11. K 固有の Cor 4.12 は本ファイルから import しない。

### 8.2 Claim 5.3・Prop 5.4

1. 固有射の切断が閉埋め込みになることを証明する。
2. α と β の始域・終域を明記する。
3. 左逆元の等式をスキーム射の等式として記す。
4. 等化子の閉埋め込みを用いて比較射の像を扱う。
5. 一般の K 群への適用は利用側に残す。
6. 抽象的な retract の命題と幾何的な構成を区別する。

### 8.3 Huneke–Swanson と Lemma 5.6 の古典的入力

1. a′(2) は生成元ごとの二乗のイデアルとして定義する。
2. (a′)^2 はイデアルの二乗として定義する。
3. 二つのイデアルを定義上同一視しない。
4. 交差項の整依存のモニック方程式を作る。
5. Rees 代数の拡大の整性を証明する。
6. 有限型性と整性から有限性を証明する。
7. Proj 上の有限射をチャート上で構成する。
8. Bl_{(a′)^2} ≅ Bl_{a′} と合成する。
9. 導来塔との接続は L7d に残す。

### 8.4 Lemma 5.5

1. (i) の古典的な比較射を構成する。
2. 導来零次ホモトピーとの比較自体は K-L5 に接続する。
3. (ii)(iii) の m と厚み指数 n の順序を固定する。
4. m に依存する指数を一様と呼ばない。
5. §10-9 の紙の確認を実装の前に行う。
6. K-L6 の対角共終性の宣言に接続する。

## 9. §10-9：実装前の紙の確認

対象は Lemma 5.5(ii)(iii) の二重添字と Isaksen 4.7 の置換。
現状は未着手であり、検証済みとはしない。
実装前に原文の量化子をこの節に記す。
固定した m の後に n を選ぶ主張と、一様 n の主張を分ける。
対角に必要な単調な上界の存在を確認する。
有限個の前段への条件を最大値でまとめる方針を検討する。
導来次数に関する一様性も別に確認する。
主張と証明方針を記録してチャットに報告してから実装する。
報告後に承認待ちを挟まない。
未解決の設計変更が必要な場合は提案として停止する。

## 10. L7d：合流条件

- K-L5 の導来 blowup の実在する定義を受け取る。
- 古典的 truncation との比較の型を合わせる。
- X̃(2^n) の遷移射と合成則を確認する。
- Lemma 5.6 の有限射を当該遷移射と比較する。
- Thm A の K 群側の組み立ては利用側と合流する。
- L7d が未完了の間は古典的部分だけの完了を報告する。

## 12. 保存・検証・コミット

1. 保存単位の対象モジュールを `lake build` する。
2. `set -o pipefail` を設定して終了コードを確認する。
3. 監査は集約 import の公開宣言と補助生成宣言を調べる。
4. 監査は `Lean.collectAxioms` で依存公理を再帰的に収集する。
5. 許可する公理は `propext`、`Classical.choice`、`Quot.sound` のみ。
6. `sorryAx` もその他の独自公理も拒否する。
7. 宣言数ゼロの監査は成功扱いにしない。
8. `git diff --check` を確認する。
9. コミット対象は自分の検証済みファイルに限る。
10. `git commit --only` を使う。
11. ルートの他レーンの差分を取り込まない。
12. amend・rebase・reset は使わない。
13. 工程の区切りで全体ビルドを行う。
14. 並行作業による自分の import 閉包の破損では回避策を作らず報告する。
15. 工程の完了時に現在地と主要宣言の表を書き換える。

## 13. 設計上の決定

- 論文の番号を Lean のモジュール説明と宣言の説明に記す。
- docstring は概要／方針／規約／使われ方を日本語で書く。
- 実際の数学的構造の法則だけを構造体に持たせる。
- 未証明の平坦化・有限性・同型を構造体の仮定に押し込まない。
- 名前だけの定理や自明な条件付き言い換えで工程完了としない。
- 環は原則 `CommRing`、スキームは Mathlib の `Scheme` を使う。
- blowup の一般構成を K の界面から独立させる。
- 有限生成性が必要な箇所だけに仮定を置く。
- Noether 特殊形から始めても一般化の余地を型に残す。
- 正の冪の比較では n = 0 を含めない。
- 例外因子は逆像閉部分スキームと Cartier 構造を区別する。
- Rees 代数の指数と多項式次数の一致を明示する。
- 状態が変わった節は追記の履歴でなく現状に書き換える。

## 記録の所在

実施記録・現在地の詳細・型一覧は [archive/L7-scheme-lemmas-log.md](../../L7-scheme-lemmas-log.md) に移した（2026-10-19）。現在地は冒頭の引き継ぎ節が正本で、工程ごとの記録はコミットメッセージに置く。
