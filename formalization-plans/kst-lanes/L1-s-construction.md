# K-L1：∞-S• 構成と連結 K

> **v2 の位置づけ（2026-10-19）**：foundations.md §6 の K-S• → K-基盤。L1c〜f の後、L3 は非連結 K を BGT (a) のみで（暫定 (b) は使わない）、続けて局所化不変量・Tamme・Land–Tamme（K-基盤 1・2）。

## 引き継ぎ（2026-10-19）

### 現在地
- K-L1（∞-S• 構成、連結 K）。L1a・L1b 完了。L1c 進行中、L1d–f 未完了。L1g は別途指示待ち。
- 全 gapped S• と第一行制限そのものの trivial Kan fibration を証明済み。
- core・対角実現・Kan 置換・Ω、反復 S の段と単射な構造射への置換、零方向の境界比較を構成済み。
- Ω から既存の path homotopy fiber への全基点 π_* 同型は証明済み。直前の S 実現との比較は未証明。
- 元の object/core 実現比較の弱同値、McCarthy の左 fiber の切断、λ→μ・λ→ν の両枝を証明済み。
- 停止の区切りは §6.59：両枝の span、C 内で点ごとに選ぶ raw ρ、面・退化との自然性、恒等端点。
- raw ρ の cofiber 性・gapped 性・左 fiber 条件は未証明。実ホモトピーや加法性の完成ではない。
- Lean 保存単位は 1dab0347。対象ビルド3218 jobs、公理監査1652宣言が成功、標準三公理のみ。

### 残り（依存順、原典番号と時間見積もり）
- 以下は再開後の実装作業時間の粗い目安。未形式化の難所で増えるため納期ではない。
- ρ の cofiber・gapped 性と subobject・quotient の厳密な回収：Fiore–Pieper Lemma 4.24、(4.26)、8–24時間。
- ρ と第二の θ を左 fiber の実ホモトピーにし、切断との変形収縮を完成：同 Lemma 4.24・Example 9.14、24–72時間。
- 単体積版 Quillen A と object 加法性：同 Theorem 1.15・Lemma 4.24、16–40時間。
- object/core 比較を使った実現の加法性と有限反復への自然性：同 Proposition 4.27・Theorem 4.35、8–24時間。
- 面の homotopy pullback 条件、S 実現と既存の homotopy fiber の比較、構造射との照合：HTT 5.1.2.2、
  L11 §11・Fiore–Pieper Theorem 4.35、16–40時間。L2 の実現定理に面条件を追加仮定で渡さない。
- 正の Ω 条件・delooping・負次数消滅と BF 連結スペクトル関手：BGT Definition 7.1、経路正本 §10-5、
  §13 決定2・5・12、L9c の BF 界面、16–48時間。
- π₀ K と TriangulatedK0(h C) の対象類を保つ自然同型：経路正本 §5 K0 界面欄6、L11 型草案 S1、16–40時間。
- dg 関手性・Morita 不変性：経路正本 §4 D1・§5 K1b、U16・A3e、8–24時間（依存 API の照合を含む）。
- L1g（fibration、filtered 余極限、Bass、非連結化）は今回の実装対象に拡張しない。

### 主要宣言（名前のみ）
- `sConstruction`、`simplicialSConstruction`、`firstRowRestriction_trivialKanFibration`、`firstRowEquivalence`
- `StableModel`、`PreservesCofiberData`、`sEndofunctor`、`multiRealizationFunctor`
- `kSpace`、`kKanSequence`、`monicKKanSequence`、`monicKKanSequenceProjection_piIsomorphism`
- `iteratedPathHomotopyFiber`、`iteratedPathLoopComparison_piIsomorphism`
- `objectToCoreSRealization_localized_isIso`、`objectCoreRowIso`
- `cofiberStableSubobject`、`cofiberStableQuotient`、`mcCarthyFiberSection_quotient`
- `mcCarthyLambdaMu`、`mcCarthyLambdaNu`、`mcCarthySpan`、`mcCarthyRhoRaw_pre`、`mcCarthyRhoRaw_timeZero`

### 依存と提供
- 所有は `SerrePositivity/KST/SConstruction/`、集約、監査スクリプト、本計画。namespace は同名。
- 読取専用：Core（F0、関手圏の点ごとの極限等）、Stable（α-S）、F1/F1B（core・充満包含）、
  Spectra（L9）、Comparison（L2）、HomotopicalAlgebra（具体的 Kan 置換・局所化・対角）。
- 提供：全 gapped S• と第一行の完全な比較、安定な入力の完全関手の圏、object/core 実現比較。
- K スペクトル・加法性・TriangulatedK0 比較・Morita 不変性は未提供。条件付きの段を完成品に数えない。
- 将来接続：L9 の Ω・π_*・BF、L2 の実現と plus 比較、α-S の h C の三角構造、N の dg nerve、D の Perf。

### 未コミット
- 担当ファイルの未コミット差分なし。本節も担当計画だけの `git commit --only` で保存して停止する。
- 他レーンの作業中の差分・未追跡ファイルは触れていない。

### 既知の問題
- 最終の対象ビルド・公理監査に失敗なし。全体 lake build は今回再実行していない。
- 名前衝突の未解決例なし。Core・Stable・F1 等の公開名・型は本レーンで変更していない。
- SConstruction 内の明示的な `[ModelCategory SSet]` 引数は検索で見つからず。HA の具体的 instance と
  anodyne 局所化を利用。推移的依存を含む model instance 全体の棚卸しは別途必要。
- 1652宣言の監査は追加公理・sorry を検出しない状態。許可は propext・Classical.choice・Quot.sound のみ。
- raw ρ の型は Ar→Fun(正方形,C)。cofiber・gapped・fiber への持ち上げをまだ要求していない点が主な未完。
- cofiber 図式の圏で任意に選んだ押し出しでは、subobject・quotient の strict な回収を結論できない。
- homotopy fiber 比較を既存の構造射と形式的に合成するだけでは正の Ω 条件の証明にならない。
- C×C と S₂C の ∞ 圏の同値は主張しない。加法性は S• と実現の後の定理。
- Git は既存の gc.log と unreachable loose objects の警告を出す。整理操作はしていない。

### 次の一手
- raw ρ の cofiber・gapped 性を証明する一工程から再開する。
- 方針：S_n(cofiberDiagrams C) の安定性と包含の完全性を使い、同じ span の押し出しとの関手同型で
  C 内で点ごとに選んだ raw ρ を比較して条件を移す。`ihomCurryIso` で二重内部 Hom と積形状を照合する。
- その後に各角の正規化を使う subobject・quotient の strict 回収へ進む。未証明条件を仮定にしない。
- 再開時の検証は対象ビルドと `lake env lean scripts/audit_kst_s_construction.lean`。他レーンは編集しない。

## 1. 目標・担当範囲

小さい安定 ∞ 圏 C の全 gapped 図式から S•C を構成し、core・実現・loop により連結 K を定義する。
反復 S• による連結スペクトル、加法性、π₀ と三角圏の Grothendieck 群の比較、dg 圏への適用までを証明する。
引用を証明の代用にせず、追加公理・sorry を使わない。条件付き成果を無条件の完成と数えない。

所有：`SerrePositivity/KST/SConstruction/`、namespace `SerrePositivity.KST.SConstruction`。
Core 公開名・型を変更しない。Stable（α-S）、F1 の core（α2）、Spectra（L9）、比較・plus（L2）は読み取り専用。

## 2. 原典・正本

- `k-theory-kst-route.md` §4 D1、§5 K1・K0、§6、§10-5・11・12・13、§13 決定2・5・9・12。
- `foundations.md`。非連結化の最終定義は BGT、暫定実装は Schlichting。非連結化は今回の範囲外。
- `L11-paper.md` §5・11・12・13・S1。特に以下の文言補正を採用する。
- BGT v4 Definition 7.1、Lemma 7.3、Remark 7.4（gapped と第一行）。
- Fiore–Pieper Lemma 4.24、Proposition 4.27、Theorem 4.35、Corollary 3.35（McCarthy 型加法性）。
- HTT 4.3.2.15（相対余極限拡張）、5.1.2.2（関手圏の点ごとの極限・双対）。

## 3. 工程

| 工程 | ファイル | 完了条件 |
| --- | --- | --- |
| L1a | Gapped.lean | Ar[n] と nerve、ihom、零対角・pushout 条件、充満部分単体集合 S_n、単体的関手性 |
| L1b | FirstRow.lean | 第一行制限、相対境界持ち上げ性、trivial Kan fibration |
| L1c | KSpace.lean | 各段の core、対角実現・Kan 置換・Ω、反復 S• と L9 BF スペクトルへの接続 |
| L1d | Additivity.lean | McCarthy 型ホモトピーによる実現後の加法性 |
| L1e | PiZero.lean | π₀ K(C) ≃+ TriangulatedK0(h C)、対象類と自然性 |
| L1f | DGApplication.lean | K(N_dg(Perf_dg D))、dg 関手性、Morita 不変性 |
| L1g | 別途指示 | fibration 定理、filtered 余極限、Bass、非連結化 |

## 4. 設計と実装前の文言

### Ar と gapped

Ar[n] は Fin(n+1) の対 (i,j), i≤j の成分ごとの順序の圏。
単調写像 θ:[m]→[n] は (i,j)↦(θi,θj) を誘導する。
図式圏は ihom(N Ar[n],C)。gapped は全対角 F(i,i) が零対象であり、
i≤j≤k≤l に対する F(i,k)→F(i,l), F(j,k)→F(j,l) の全四角が pushout となる条件。
S_n はこの頂点条件による充満部分単体集合。順序写像による前合成は条件を保つため、
選択を含まず Δᵒᵖ 上の単体的対象を与える。退化する四角にも同じ pushout 条件を課す。

### §10-13：gapped と第一行

原典の結論は Gap([n],C)→Fun(Δ^{1,…,n},C) の ∞ 圏の同値である。
これだけから literal な trivial Kan fibration と結論しない。
要求された元の制限写像について、有限個の相対 cocartesian completion を積み上げ、
零対象と余極限錐の相対境界持ち上げ性から全境界に対する RLP を証明する。
n=0 は零対象の空間として別処理する。全 gapped 図式を保ち、第一行の選択模型に置換しない。
不足する相対拡張補題は本レーン内で証明する。設計変更が必要なら実装前に提案する。
Ar[n] と正方形の積から (0,i),(0,j),(i,i),(i,j) への自然な添字写像を用い、
gapped 図式の全 cofiber 四角形を一つの族として取り出す。
その族は右上角の評価で元の図式を厳密に回収するため、境界上の既存データを保持できる。
相対 cofiber 補完をこの Ar[n] パラメーターに適用する際は、第一行と対角での条件を同時に固定する。
得られる右上角の図式の全四角形が押し出しとなることは、余極限の普遍性と押し出しの貼り合わせから
別に証明する。単に各区間に cofiber を持つことだけで gapped 条件を結論しない。
点ごとの余極限・押し出しを関手 ∞ 圏へ移す向きは、相対始点境界充填と内部 Hom の交換で証明する。
正次元のパラメーター境界では全頂点が指定されているため、境界を厳密に保つ補完の gapped 性は
全部分複体の頂点条件から回収できる。零次元の gapped 性および出力の第一行の厳密な回収は別条件として残す。

### §10-11：加法性

E(A,C,B) の cofiber 列から subobject・quotient への射について、
|core S•E|→|core S•A|×|core S•B| が同値となることを証明する。
E≃A×B という ∞ 圏レベルの誤った主張にはしない。
Fiore–Pieper の McCarthy 型の経路を用い、普遍的 cocartesian completion の制限自明
ファイブレーションでパラメータ付き pushout を選び、単体ホモトピー、単体積版 Quillen A、
対角実現、object/core 比較を証明する。Waldhausen の元の証明からの経路変更を明記する。

### §10-12：最小 fibration 定理（後続 L1g の仕様）

C 安定、D thick、W={f | cofib(f)∈D}。W の2-out-of-3・pushout・extension 安定性が必要。
∞ 局所化と dg 商の比較には mapping 空間の比較まで要求し、H⁰ の Verdier 普遍性で代用しない。
冪等完備化は K₀ を変えるため、連結 K の局所化を全冪等完備 Verdier 列に無条件では課さない。
最終的な非連結 K(D)→K(C)→K((C/D)^idem) の fiber 列へは、必要な cofinality 条件を明示した
連結版と Schlichting suspension を経由する。L11 では ∞ 版全体は未検証である。
今回の L1a–f の成果としてこの定理を完成扱いしない。

### K と界面

L9 の基点・Ω・π_* の座標に従う。BF 模型は単射 ΣX_n→X_(n+1) と、随伴の全基点 π_* 同型。
厳密な Ω 同型を要求しない。未着 API は明示的な入力として隔離し、証明済みの構成と区別する。
π₀ は一般 dg 圏の H⁰D でなく、小さい Perf の H⁰ の TriangulatedK0 と比較する。
S4 未着時は cofiber 列の像が distinguished triangle になる仮定を明記する。
相対 K は L9 のスペクトル fiber を優先し、次数ごとの kernel/cokernel から復元しない。
Kₙ の境界・比較同型は自然性と対象類の式を含む。宇宙は S1.1 に従い小さい模型にそろえる。

## 5. 検証・保存

各保存単位で `lake build SerrePositivity.KST.SConstruction` と
`lake env lean scripts/audit_kst_s_construction.lean` を実行する。
公開宣言を #check / #print axioms で監査し、許可するのは propext、Classical.choice、Quot.sound のみ。
全体ビルドは工程の区切りで行う。自分の import 閉包外の並行作業の失敗は記録して続ける。
自分の検証済みファイルだけを保存し、経緯はコミットメッセージに記す。

## 記録の所在

実施記録・現在地の詳細・型一覧は [archive/L1-s-construction-log.md](archive/L1-s-construction-log.md) に移した（2026-10-19）。現在地は冒頭の引き継ぎ節が正本で、工程ごとの記録はコミットメッセージに置く。
