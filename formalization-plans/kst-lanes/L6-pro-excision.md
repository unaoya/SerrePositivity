# K-L6（pro 切除）

## 所有するもの・借りるもの

- 所有するもの：ℕ 添字の塔、レベル射、Artin–Mazur 型 pro 同型判定。
- 所有するもの：pro-零性、pro-cartesian の最小形式、対角の共終性。
- 所有するもの：KST §4 の切除証明と Appendix A の必要部分。
- 借りるもの：π_n とスペクトルの fiber 列は K-L9。
- 借りるもの：H_* と plus 構成・群完備化は K-L2。
- 借りるもの：K の値域・関手・局所化の界面は K0・K2。
- 借りるもの：Koszul 複体と Artin–Rees の既存証明。
- 借りるもの：§10 の原典検証は K-L11 の成果も参照する。
- 界面が未到着の部分は明示的な引数とし、証明済みとは表示しない。
- 本レーン自身が証明すべき結論を構造体の仮定に隠さない。

## 正本・目標

- 正本は `formalization-plans/k-theory-kst-route.md`。
- 基盤の決定は `formalization-plans/foundations.md` を優先する。
- KST は arXiv:1611.08466v4。
- 第 1 目標は係数つき pro 切除の完全証明。
- 最終用途は KST Thm A を介する定理 3.1 と supportedRankK0_descent。
- 追加公理、引用定理、sorry は導入しない。
- 標準公理 propext・Classical.choice・Quot.sound だけを許す。
- 作業 namespace は `SerrePositivity.KST.ProExcision`。
- Lean 実装は `SerrePositivity/KST/ProExcision/` に限定する。
- 集約は `SerrePositivity/KST/ProExcision.lean`。
- 監査は `scripts/audit_kst_pro_excision.lean`。
- ルートには指定の public import を 1 行だけ追加する。
- 他レーンの変更は読み取り専用とし、コミットに含めない。

## 現在地

- L6a：最小形式の実装完了。塔・レベル射・pro 同型判定・関手保存・再添字・pro-零性・対角共終性を検証済み。
- L1：具体的な自然なレベル完全列から塔への持ち上げを証明。fiber 長完全列自体は K-L9 の入力。
- L2：加群の塔における pro 五項補題を証明。外側はレベル同型でなく pro 同型。
- L3：任意の関手での保存を証明したので、加法関手にも適用可能。具体的な有理化関手は K-L9 から借用。
- L6b：進行中。Lemma 4.9 の有限生成加群係数版を検証済み。
- 平坦底変換の自然なホモロジー比較・イデアル倍の像・pro-零性保存まで検証済み。
- Lemma 4.10：実際の Mathlib SpectralSequence の頁の pro-零性保存と有限拡張を検証済み。
- Koszul SS 自体の構成・E₂ 同定・次数ごとの有限収束と edge 比較は残件。
- 有限な Koszul 方向の項による濾過をテンソル複体上に構成済み。
- そこから実際の mapping cone スペクトル対象と有限行補助スペクトル系列を構成済み。
- 初端の零性と終端の全 Koszul 複体への包含が同型であることを証明済み。
- Mathlib の補助頁番号と KST の E₂ 頁の対応は未検証。初頁・微分・次頁の同定を次に行う。
- π_n の具体的な複体ホモロジーとの同定は K-L9 の界面から受け取る。
- Lemma 4.9 は原典の列長帰納法と異なり、Artin–Rees と実際の冪遷移の深度を用いた。
- L6a 区切りの全体ビルドは別レーンの RationalFixedPoints・CoefficientForget で失敗。
- 当該二ファイルは L6 の import 閉包外であり変更しない。L6 対象ビルドは成功。
- L6c：未着手。
- L6d：未着手。紙の検証を実装前に記録する。
- L6e：未着手。simple 空間版の検証が必要。
- L6f：未着手。最小スペクトル系列の仕様を着手前に報告する。
- L6g：未着手。非零因子化と系の再構成を着手前に確認する。
- この文書は現在の仕様と到達点を上書きして保つ。
- 実施の経緯はコミットメッセージに記録する。

## 主要宣言の表

| 宣言 | ファイル | 状態 | 意味 |
| --- | --- | --- | --- |
| Tower | Pro.lean | 検証済み | ℕ 上の逆系 |
| LevelHom | Pro.lean | 検証済み | 同じ添字上の可換な射 |
| IsProIso | Pro.lean | 検証済み | eventual inverse の二つの三角形 |
| Tower.map | Pro.lean | 検証済み | 関手による塔の像 |
| LevelHom.map | Pro.lean | 検証済み | 関手によるレベル射の像 |
| IsProIso.map | Pro.lean | 検証済み | 関手による pro 同型保存 |
| diagonal_cofinal | Pro.lean | 検証済み | 二添字の共通上界 |
| IsProZero | Pro.lean | 検証済み | 遷移射の eventual 零性 |
| Tower.reindexHom_isProIso | Pro.lean | 検証済み | 増大する単調再添字 |
| IsProZero.map | Pro.lean | 検証済み | 零射保存関手による保存 |
| IsProEquivalence | Pro.lean | 検証済み | 次数別の pro 同型判定 |
| IsProCartesian | Pro.lean | 検証済み | 与えられた hofib 比較の pro 同値 |
| FiveTermHom.isProIso | FiveLemma.lean | 検証済み | 外側四射が pro 同型なら中央も pro 同型 |
| isProIso_of_mono_epi | ModulePro.lean | 検証済み | 核・余核の eventual 零化から逆射を構成 |
| LevelwiseExactSequence.toTower | ExactSequence.lean | 検証済み | L1 の自然な族を塔に組み立てる |
| ExactTowerSequence.fiveTerm | ExactSequence.lean | 検証済み | 五項部分の抽出 |
| koszulHomologyTower_isProZero | KoszulPro.lean | 検証済み | Lemma 4.9 の環係数版 |
| koszulTensorHomologyTower_isProZero | KoszulPro.lean | 検証済み | Lemma 4.9 の全有限生成加群版 |
| range_lTensor_le_ideal_smul | KoszulPro.lean | 検証済み | 平坦性不要の遷移深度保存 |
| flatTensorHomologyIso | FlatBaseChange.lean | 検証済み | 平坦テンソルとホモロジーの自然同型 |
| ideal_smul_tensor_range | FlatBaseChange.lean | 検証済み | a(n)M のテンソル像 |
| koszul_flatTensor_homology_proZero | FlatBaseChange.lean | 検証済み | 有限生成性を係数変更前にのみ要求 |
| spectral_page_proZero | SpectralPro.lean | 検証済み | 実際のスペクトル系列の全後続頁へ零性を移す |
| proZero_finite_extension | SpectralPro.lean | 検証済み | 有限拡張の pro-零性 |
| proIso_of_injective_exact_proZero | SpectralPro.lean | 検証済み | edge 比較に使う pro 同型判定 |
| koszulFilteredSpectralObject | KoszulFiltration.lean | 検証済み | 有限な実際の濾過から構成 |
| koszulFilteredSpectralSequence | KoszulFiltration.lean | 検証済み | Mathlib の有限行補助スペクトル系列 |
| koszulTruncation_initial_isZero | KoszulFiltration.lean | 検証済み | 濾過の初端 |
| koszulTruncation_terminal_isIso | KoszulFiltration.lean | 検証済み | 濾過の終端 |
| koszul_comparison | KoszulPro.lean | 予定 | KST Lemma 4.10 |
| prop414 | Prop414.lean | 予定 | 中心的係数による非可換版 |
| pro_whitehead | Whitehead.lean | 予定 | simple 空間版 |
| claim418 | Serre.lean | 予定 | 相対 Serre SS の帰結 |
| theorem411 | Excision.lean | 予定 | pro 切除 |

## L6a：最小 pro 形式

- 原典は KST §4.1、Definition 4.4、Lemma 4.6。
- 正本 §2.6 の最小定義に従い一般の pro 圏全体は構成しない。
- 対象は任意の圏 C に値を持つ ℕ 添字の塔。
- 遷移射は m ≥ n に対して X_m → X_n。
- 同じ添字の遷移は恒等射。
- 二つの遷移の合成は直接の遷移と一致する。
- レベル射 f は f_n : X_n → Y_n と自然性を持つ。
- pro 同型判定は各 n について m ≥ n と g : Y_m → X_n の存在。
- 第一の三角形は f_m ≫ g = X(m,n)。
- 第二の三角形は g ≫ f_n = Y(m,n)。
- 存在する g の族にレベル射としての整合性を要求しない。
- 定数塔の判定が通常の同型と一致することを示す。
- 恒等射が pro 同型であることを示す。
- 合成が pro 同型であることを示す。
- 関手による像は遷移射と自然性を写して定義する。
- L3 は加法性を必要としない一般の関手の補題を先に証明する。
- 有理テンソル関手への適用と完全性の使用を区別する。
- L4 は (m,n) ≤ (max m n,max m n) の明示的証人を使う。
- 単調な共終再添字についても比較射を構成する。
- pro-零性は各 n である m ≥ n の遷移射が零になること。
- 零対象への pro 同型との一致を検証する。
- pro-cartesian はレベルごとに形成した hofib 間の射の pro 同値。
- レベルごとの各射を同値と要求する強すぎる条件は採らない。
- π_n による同値判定は K-L9 の明示的な入力から構成する。
- L1 は fiber 列から得る次数ごとの完全列を自然性込みで塔へ持ち上げる。
- L1 の fiber の存在自体は本レーンで仮定し直さない。
- L2 はレベル完全列を diagram chase し eventual な上界をまとめる。
- L2 では外側四つの同型から中央の eventual 単射・全射を導く。
- レベルごとの同型だけの五項補題で代替しない。
- 保存単位では Pro の対象ビルドと宣言ごとの公理監査を実行する。

## L6b：Koszul と平坦底変換

- 原典は [KST v4](https://arxiv.org/pdf/1611.08466v4) p.23、Lemma 4.9・Lemma 4.10。
- Lemma 4.9 の証明経路の差分：列長帰納法を用いず、標的項の有限性・Koszul 座標の零作用・Artin–Rees・冪遷移のイデアル深度を使う。
- 係数付き複体は既存 koszulComplex に tensor を施したものであり、既存の反復錐モデルとの自然同型を用いて零化イデアルを移す。
- 既存の koszulComplex の次数規約を先に確認する。
- ホモロジーの次数変換を docstring に明記する。
- 有限生成加群と Noether 仮定の使用箇所を分ける。
- Artin–Rees は Ideal.exists_pow_inf_eq_pow_smul を用いる。
- 正次数の Koszul ホモロジーの遷移を構成する。
- 零次数の比較は商加群との同定を使う。
- 有限生成された境界とサイクルへの Artin–Rees を用いる。
- 各次数の消滅指数は固定された標的レベルに依存してよい。
- 複数次数を一様に扱う必要があれば有限性を証明する。
- 係数 H の平坦性は tensor の完全性として使う。
- π_*(B ⊗ H) の比較は複体のホモロジー底変換から得る。
- a(n)M の像と tensor の比較を別補題にする。
- pro-零性の保存には零射保存と関手性を使う。
- 非可換 H の Noether 性を仮定しない。
- 中心的な A 作用だけが必要であることを型で示す。
- 既存 CommutativeAlgebra のソースは変更しない。
- 既存 HomologicalAlgebra も読み取り専用とする。
- 対象 import 閉包のビルド失敗は回避せず報告する。
- 完了時に主要宣言の型と仮定を表へ反映する。

## L6c：群状単体モノイドのホモロジー

- 原典は KST Appendix A。
- 対象は Prop A.1、Lemma A.2・A.4。
- 構成は Construction A.5・A.6。
- G ⋉ H の半直積の作用と積の順序を固定する。
- 群状条件は π₀ が群になる条件として明示する。
- 群ホモロジー H_* の定義自体は K-L2 から借りる。
- bar 構成への比較射は自然性を含めて記述する。
- 相対ホモロジーは絶対ホモロジーと混同しない。
- 次数零の補題と正次数の補題を分ける。
- augmentation とその切断を構成する。
- 有限段階から安定化への移行を明示する。
- filtered 余極限の完全性が必要な場所を記録する。
- 単体次数とホモロジー次数を別の引数とする。
- 行列サイズ n と塔の添字を区別する。
- 自然変換から誘導される chain homotopy を証明する。
- Prop 4.14 が使う相対零化補題まで進める。
- Suslin–Wodzicki の議論を引用定理として登録しない。
- 原典が arguing as in と書く箇所も具体的に証明する。
- 未到着の界面を本レーンの結論で埋めない。
- 完了時に対象ビルドと公理監査を行う。

## L6d：非可換再記述の紙の検証

- 実装前の紙の検証項目は正本 §10-1。
- 原典は KST Proposition 4.14、Claim 4.15、Lemma 4.16。
- I は結合的で非単位的でもよい単体環。
- a は中心的で各単体次数で乗法が単射。
- φ は右乗法 v ↦ va とする。
- M_{n,n}(I) の作用は左からの行列積である。
- (Mv)a = M(va) は結合律で成り立つ。
- 中心性は aI が両側イデアルであることにも用いる。
- u⁻¹ψ(v)u のブロック行列計算を記録してから実装する。
- 単位化した環における逆行列の具体式を確かめる。
- φ と ψ の定義域・値域を明記する。
- 安定 GL の共役作用を誘導する。
- 原典の可換環という仮定と本実装の差分を明記する。
- 目標は像上での GL(ℤ) の作用の自明性。
- 全ホモロジー上の自明性を主張しない。
- 相対ホモロジーの零化に帰着する。
- Lemma A.4 の適用条件を照合する。
- 紙の検証の未解決点があれば設計変更として報告する。
- 検証結果の報告後は承認待ちせず進む。
- 現時点で紙の検証完了とは扱わない。

## L6e：pro-Whitehead

- 原典は KST Lemma 4.2、Proposition 4.3。
- 参照は Bousfield–Kan III.5.4(ii)・III.6.6。
- 紙の検証項目は正本 §10-4。
- 適用対象は連結 H 空間なので simple 空間版を目標とする。
- π₁ が可換で高次 π への作用が自明という条件を明示する。
- 連結性だけで simple 性を置き換えない。
- π_* pro 同型から H_* pro 同型を導く易しい向きを先に扱う。
- 逆向きには Postnikov 段階と相対 Hurewicz を整理する。
- 次数ごとの指数と全次数一様の指数を混同しない。
- BK の完備化の主張から必要な部分を検証する。
- π_n の具体的構成は K-L9 の責任範囲。
- H_n の具体的構成は K-L2 の責任範囲。
- 本レーンは借用界面への明示的な引数で先へ進む。
- 借用する法則と本レーンが示す結論を区別する。
- Prop 4.8 の適用を見据えた自然性を含める。
- Claim 4.17 の fiber に simple 性がある理由を記録する。
- 基点変更の扱いを曖昧にしない。
- 群とアーベル群の境界次数を区別する。
- 紙の検証を報告してから Lean 実装に入る。
- 現時点では未着手。

## L6f：局所係数つき相対 Serre SS

- 原典は Claim 4.18。
- 比較資料は Geisser–Hesselholt 2006 Lemma 1.2。
- Suslin–Wodzicki Corollary 1.7 との対応も調べる。
- 着手前に必要最小限の形をこの節へ書いて報告する。
- 現時点ではその最小形の検証を完了していない。
- 一般の Serre SS 全体を無条件の仮定に置かない。
- 相対 pair と基底の基本群の作用を明示する。
- E₂ 頁は局所係数の群ホモロジーとして記述する。
- 収束は各総次数の有限濾過として記述する。
- pro-自明な作用とレベルごとの自明な作用を区別する。
- Claim 4.19 から必要な eventual 零化を取り出す。
- 次数ごとに有限個の微分の指数をまとめる。
- 濾過の graded の pro-同型から全体へ移る補題を証明する。
- edge map が目的の比較射と一致することを示す。
- 係数の自明化が自然であることを検証する。
- π₁ の作用を落とした定数係数 SS で代替しない。
- ホモトピー fiber と通常の fiber の比較を明示する。
- 単体モデルの置換に関する自然性を記録する。
- 対象ビルドと公理監査を行う。
- 完了時に入力と結論を主要宣言の表に反映する。

## L6g：主定理と系

- 原典は KST Theorem 4.11、Corollary 4.12・4.13。
- 基底 r = 1 と帰納段階を分離する。
- 非零因子化は正本 §10-2 の紙の検証を先行する。
- R[t] 上の半自由置換を各段階で両立させる。
- 低次数 K は K0・K2 の界面を明示的に受け取る。
- Weibel III.4.3 の負の K の切除への依存を明記する。
- 高次数 K は BĜL⁺ と pro-Whitehead に帰着する。
- Claim 4.17 はホモロジーの pro 同型の主張。
- Claim 4.18 は L6f の結論を用いる。
- Claim 4.19 は Prop 4.14 と ι/σ トリックから導く。
- 帰納段階は定数でない pro-系で記述する。
- Lemma 4.10 の一様性が必要な箇所を点検する。
- Cor 4.12・4.13 は正本 §10-3 の紙の再構成を先行する。
- I の冪と生成元ごとの冪の共終性を明示する。
- Koszul の塔と商環の塔の比較は Prop 4.8 を通す。
- Cor 4.13 の正次数 π の pro-零性を確認する。
- 原典と異なる再構成であることを docstring に書く。
- 主定理の K への依存を循環させない。
- 工程の区切りで全体ビルドを実行する。
- 全工程の終了以外に完了とは報告しない。

## 保存・検証・統合の規約

- 各保存単位で lake build SerrePositivity.KST.ProExcision を実行する。
- 監査は lake env lean scripts/audit_kst_pro_excision.lean。
- 公理出力に sorryAx または追加公理があれば未検証とする。
- 全体ビルドは工程の区切りで実行する。
- ビルドは set -o pipefail を指定し終了コードを確認する。
- 新規・変更宣言に日本語 docstring を付ける。
- docstring は概要／方針／規約／使われ方を含む。
- 数学的法則を持つ構造体はその法則の意味を記す。
- 実施記録はコミットメッセージに置く。
- git commit --only で所有する検証済みファイルだけを含める。
- amend・rebase・reset を使わない。
- ルートの既存変更を自分のコミットに巻き込まない。
- 共有ファイルのステージ差分を確認する。
- 他レーンの import 閉包が壊れたら回避策を作らない。
- その場合は具体的なファイルとエラーを報告する。
- 各工程の完了時に現在地と主要宣言を更新する。
- 各工程の報告後は次の工程に進む。
- 設計変更が必要なら差分と理由を具体的に提案する。
- 未証明の仮定を供給済みと表示しない。
- 本レーンの完成とリポジトリ全体の完成を区別する。

