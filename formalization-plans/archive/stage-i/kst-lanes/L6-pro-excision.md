# K-L6（pro 切除）

> **凍結（2026-10-19）**：foundations.md v2 により pro 切除は Land–Tamme の ⊙（K-基盤 2）で行う。L6a〜g の既存コードは Auxiliary として保持し、再開しない。

## 引き継ぎ（2026-10-19）

### 現在地

- L6a・L6b は複体模型まで、L6c は借用 π・H_* の明示的な模型界面に対して完了。
- L6b は Koszul cone の長完全列と Artin–Rees による経路。π との模型同定は別途借用する。
- L6d は進行中。非可換 Lemma 4.16、Claim 4.15、通常の有限 rank 遷移での零化まで検証済み。
- 実 bar・H_*・相対商と順序余極限の比較、実安定相対 H_* 上の列右乗法・行左乗法の零化を証明済み。
- 今回の区切りは実 aI→I、係数射による ĜL・行列作用の写像、中心乗法による実核・列群同型、同変性反映。
- 相対包含の因子化、Prop 4.14 の整数作用の最終結論、L6e〜g は未完。新工程には着手せず停止する。
- 対象 `lake build SerrePositivity.KST.ProExcision` 成功。1644宣言の公理監査は標準三公理のみ。

### 残り（依存順）

- L6d：KST Prop 4.14／SW92 Prop 1.5。aI→I の相対包含を既証明の乗法零化へ因子化し、rank 自然性を接続（8〜16時間）。
- L6d：SW92 Lemma 1.4、KST Prop 4.14。実アフィン共役・有限支持の置換共役・整数作用を接続し完成（16〜32時間）。
- L6e：KST Lemma 4.2・Prop 4.3、BK III.5.4・III.6.6。§10-4 を紙で確認して simple 版 pro-Whitehead（16〜32時間以上）。
- L6f：KST Claim 4.18／GH06 Lemma 1.2。局所係数つき相対 Serre スペクトル系列の最小形を先に計画・報告（40〜80時間以上）。
- L6g：KST Thm 4.11 の r=1 基底と帰納、Cor 4.12・4.13 の §10-3 再構成。K0・K2 界面に接続（40〜80時間以上）。
- 見積もりは実装時間の概算。L6e 以降は借用界面とスペクトル系列の基盤により増える。

### 主要宣言（名前のみ）

- `koszul_comparison_isProIso`
- `constructionA5`
- `constructionA5_equivariant`
- `propA1ComparisonIso`
- `nonUnitalLemma416`
- `claim415`
- `SimplicialHomologyModel.preservesSequentialColimits`
- `SimplicialHomologyModel.relativeBarSequentialColimitIso`
- `NonUnitalSimplicialRing.stableColumnAffineRelativeRightMap_zero`
- `NonUnitalSimplicialRing.stableRowAffineRelativeLeftMap_zero`
- `NonUnitalSimplicialRing.centralIdealInclusion`
- `NonUnitalSimplicialRing.centralIdealColumnGroupIso`
- `NonUnitalSimplicialRing.centralIdealColumnGroupIso_inclusion`
- `SimplicialActionHom.ofInjectiveComposite`
- `SimplicialActionHom.inverseOfIso`

### 依存と提供

- 所有：`KST/ProExcision/`、集約、公理監査、本計画。pro 最小形式と KST §4・App. A の上記検証済み界面を提供。
- 読取専用：`HomologicalAlgebra/` の Koszul・cone・Artin–Rees、`CommutativeAlgebra/FlatTensorFiltration`。
- 読取専用：`KST/Comparison/` の成分環・群完備化・bar・`HomologyFilteredColimits`、`HomotopicalAlgebra/Simplicial/` の局所化・対角比較。
- π_n・fiber・弱同値の模型は K-L9、H_*・plus は K-L2、K 基底は K0・K2 から借用。
- H_* は `F : SSet ⥤ ModuleCat ℤ` と `SimplicialHomologyModel F i` を明示。必要箇所で anodyne 射の反転を明示する。
- filtered 保存は自然な鎖模型から実証明済み。結論を仮定する追加フィールドは置いていない。

### 未コミット

- 所有ファイルに未コミットなし（本節も計画ファイルのみの追加コミットで保存）。他レーンの変更は対象外。

### 既知の問題

- 今回の対象ビルド・監査に失敗なし。全体ビルドは今回は再実行していない。
- 過去の全体ビルドは F1 と F1B の `relativeFunctorVertex` 重複で失敗（`/tmp/kst-l6-full-build.log`）。他レーンの改名後の解消は未再確認。
- 固定 Mathlib の `SpectralSequence.homologyData` が私有証明定数を参照する kernel 不具合。依存先は修復せず、同 API は使用しない。
- 最小再現と版更新時の再確認は本文脚注 `mathlib-homologydata`。L6f でもこの API に依存する実装は避ける。
- 所有ソースに `ModelCategory SSet` の instance 仮定は追加していない。借用 H_* の模型・anodyne 反転は上記の明示的な前提。
- A.5 は非被約 C(H) を保ち、右辺を C(φ)+C(φ′)−C(e) とする augmentation 補正。標的は μ:P×Q→H の採用版。
- 非可換 I の可換性は仮定しない。a の各次数での中心性と、必要箇所だけ乗法の単射性を明示する。
- 行側比較は係数の単体方向も反転する `reverseOpposite` と符号付き鎖同型。nerve の反転だけと混同しない。
- 整数作用の最終段は原典の生成系を引用せず、既証明の Whitehead 六ブロック分解と有限支持を用いる別経路。移送は未完。
- Cor 4.12・4.13 の再構成も未完であり、K 切除全体の完成は主張しない。

### 次の一手

- L6d を再開し、`centralIdealColumnGroupIso_inclusion` と `SimplicialActionHom.ofInjectiveComposite` から中心乗法同型の同変性・逆同変性を作り、実 aI→I の相対包含を列右乗法へ因子化する。続いて行側を接続する。

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

- 正本は `formalization-plans/archive/stage-i/kst-lanes/k-theory-kst-route.md`。
- 基盤の決定は `formalization-plans/archive/stage-i/infinity-lanes/foundations.md` を優先する。
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

## 記録の所在

実施記録・現在地の詳細・型一覧は [archive/L6-pro-excision-log.md](../../L6-pro-excision-log.md) に移した（2026-10-19）。現在地は冒頭の引き継ぎ節が正本で、工程ごとの記録はコミットメッセージに置く。
