# K-S• → K-基盤 1・2：∞-S• と局所化不変量

> **v2 の位置づけ（2026-10-19）**：foundations.md §6 の K-S• → K-基盤。L1c〜f の後、L3 は非連結 K を BGT (a) のみで（暫定 (b) は使わない）、続けて局所化不変量・Tamme・Land–Tamme（K-基盤 1・2）。

## 引き継ぎ（2026-10-19）

### 現在地
- K-L1（∞-S• 構成、連結 K）。L1a・L1b 完了。L1c 進行中、L1d–f 未完了。後続は L3・K-基盤 1・2（v2 の担当範囲）。
- 全 gapped S• と第一行制限そのものの trivial Kan fibration を証明済み。
- core・対角実現・Kan 置換・Ω、反復 S の段と単射な構造射への置換、零方向の境界比較を構成済み。
- Ω から既存の path homotopy fiber への全基点 π_* 同型は証明済み。直前の S 実現との比較は未証明。
- 元の object/core 実現比較の弱同値、McCarthy の左 fiber の切断、λ→μ・λ→ν の両枝を証明済み。
- raw ρ の全頂点の cofiber 性、A・E が gapped のときの gapped 性を証明済み。
- 同じ C 内の選択を保つ cofiber 値の `mcCarthyRho`、面・退化の自然性、時刻零の E の厳密回収を構成済み。
- subobject は動かした添字の A、quotient は元の E という strict 回収と左 fiber 条件を証明済み。
- `mcCarthyRhoFiberHomotopy`：左 fiber の恒等射から `mcCarthyRhoTerminal` への実単体ホモトピーを構成済み。全時刻で quotient を厳密に固定する。
- 終端のパラメーターと subobject の厳密な固定から、第二の `mcCarthyThetaFiberHomotopy` を構成済み。始点は ρ の終端、終点は quotient と切断の合成。
- 固定零始点の矢印の終点射影の trivial Kan fibration と、θ の点ごとの可逆性を証明済み。可変時刻の gapped 性を関手同型で移す。
- ρ・θ の二つの実ホモトピーと厳密な切断から `cofiberLeftFiberQuotient_localized_isIso` を証明済み。単体積版 Quillen A・加法性は未完。
- 対象ビルド3275 jobs、公理監査1771宣言が成功。標準三公理のみ。保存単位の詳細はコミットメッセージ。

### 残り（依存順、原典番号と時間見積もり）
- 以下は再開後の実装作業時間の粗い目安。未形式化の難所で増えるため納期ではない。
- 単体積版 Quillen A と object 加法性：同 Theorem 1.15・Lemma 4.24、16–40時間。
- object/core 比較を使った実現の加法性と有限反復への自然性：同 Proposition 4.27・Theorem 4.35、8–24時間。
- 面の homotopy pullback 条件、S 実現と既存の homotopy fiber の比較、構造射との照合：HTT 5.1.2.2、
  L11 §11・Fiore–Pieper Theorem 4.35、16–40時間。L2 の実現定理に面条件を追加仮定で渡さない。
- 正の Ω 条件・delooping・負次数消滅と BF 連結スペクトル関手：BGT Definition 7.1、経路正本 §10-5、
  §13 決定2・5・12、L9c の BF 界面、16–48時間。
- π₀ K と TriangulatedK0(h C) の対象類を保つ自然同型：経路正本 §5 K0 界面欄6、L11 型草案 S1、16–40時間。
- dg 関手性・Morita 不変性：経路正本 §4 D1・§5 K1b、U16・A3e、8–24時間（依存 API の照合を含む）。
- L3・K-基盤 1・2 は §6・7 の依存順に続行。非連結化は F2-lite の Ind を待つ。

### 主要宣言（名前のみ）
- `sConstruction`、`simplicialSConstruction`、`firstRowRestriction_trivialKanFibration`、`firstRowEquivalence`
- `StableModel`、`PreservesCofiberData`、`sEndofunctor`、`multiRealizationFunctor`
- `kSpace`、`kKanSequence`、`monicKKanSequence`、`monicKKanSequenceProjection_piIsomorphism`
- `iteratedPathHomotopyFiber`、`iteratedPathLoopComparison_piIsomorphism`
- `objectToCoreSRealization_localized_isIso`、`objectCoreRowIso`
- `cofiberStableSubobject`、`cofiberStableQuotient`、`mcCarthyFiberSection_quotient`
- `mcCarthyLambdaMu`、`mcCarthyLambdaNu`、`mcCarthySpan`、`mcCarthyRhoRaw_pre`、`mcCarthyRhoRaw_timeZero`
- `mcCarthyRhoRaw_isCofiber`、`mcCarthyRhoRaw_isGapped`、`mcCarthyRho`、`mcCarthyRho_isGapped`
- `mcCarthyRho_ι`、`mcCarthyRho_pre`、`mcCarthyRho_timeZero`、`pointwiseDiagramPushoutApex_postcompIso`
- `mcCarthyRho_source`、`mcCarthyRho_quotient`、`mcCarthyRhoFiberMap`、`mcCarthyRhoFiberHomotopy`
- `mcCarthyRhoFiberMap_quotient`、`mcCarthyRhoTerminal_parameter`、`mcCarthyRhoTerminal_source`
- `fixedSourceArrowsTarget_trivialKanFibration`、`zeroSourceThetaHomotopy`、`mcCarthyThetaFiberHomotopy`
- `mcCarthyFiber_retraction_localized`、`cofiberLeftFiberQuotient_localized_isIso`

### 依存と提供
- 所有は `SerrePositivity/KST/SConstruction/`、集約、監査スクリプト、本計画。namespace は同名。
- 読取専用：Core（F0、関手圏の点ごとの極限等）、Stable（α-S）、F1/F1B（core・充満包含）、
  Spectra（L9）、Comparison（L2）、HomotopicalAlgebra（具体的 Kan 置換・局所化・対角）。
- 提供：全 gapped S• と第一行の完全な比較、安定な入力の完全関手の圏、object/core 実現比較、ρ の cofiber・gapped 性、左 fiber 内の二ホモトピー、quotient 射の局所化同型。
- K スペクトル・加法性・TriangulatedK0 比較・Morita 不変性は未提供。条件付きの段を完成品に数えない。
- 将来接続：L9 の Ω・π_*・BF、既存の実現比較（L2 は Auxiliary として凍結）、α-S の h C の三角構造、N の dg nerve、D の Perf。

### 未コミット
- 担当ファイルは検証済み保存単位（新規11モジュール、集約、監査スクリプト、本計画）にコミット。未保存の担当差分なし。
- 他レーンの作業中の差分・未追跡ファイルは触れていない。

### 既知の問題
- 最終の対象ビルド・公理監査に失敗なし。全体 lake build は今回再実行していない。
- 名前衝突の未解決例なし。Core・Stable・F1 等の公開名・型は本レーンで変更していない。
- SConstruction 内の明示的な `[ModelCategory SSet]` 引数は検索で見つからず。HA の具体的 instance と
  anodyne 局所化を利用。推移的依存を含む model instance 全体の棚卸しは別途必要。
- 1771宣言の監査は追加公理・sorry を検出しない状態。許可は propext・Classical.choice・Quot.sound のみ。
- raw ρ の型は Ar→Fun(正方形,C)。cofiber 値への持ち上げ・gapped 性・各角の strict 回収・左 fiber 条件は証明済み。二つの実ホモトピーと quotient 射の局所化同型まで証明済み。
- cofiber 図式の圏で任意に選んだ押し出しでは、subobject・quotient の strict な回収を結論できない。
- homotopy fiber 比較を既存の構造射と形式的に合成するだけでは正の Ω 条件の証明にならない。
- C×C と S₂C の ∞ 圏の同値は主張しない。加法性は S• と実現の後の定理。
- Git は既存の gc.log と unreachable loose objects の警告を出す。整理操作はしていない。

### 次の一手
- 単体積版 Quillen A：f:X→Y、g:X→Z に対し、全 y:Δ[m]→Y の strict 左 fiber から Z への射が局所化同型なら、(f,g):X→Y×Z が局所化同型となる定理を実証明する（Fiore–Pieper Theorem 1.15）。
- 単体圏上の左 fiber 図式とその自然な quotient 射を使う。`simplexLeftFiberMap_postcomp`・`cofiberLeftFiberQuotient_localized_isIso` が具体的な入力。所有内に一般補題を追加し、他レーンの公開名・型は変更しない。
- 既存の `localized_diagonal_map`・単体 nerve augmentation・実現比較の API を照合し、単体圏による二重単体解消の二方向の弱同値を証明する。未証明の Quillen A を構造体の仮定にしない。
- その定理を subobject・quotient に適用して object 加法性へ進み、object/core 比較で core 実現へ移す。
- 検証は対象ビルドと `lake env lean scripts/audit_kst_s_construction.lean`。他レーンは編集しない。

## 1. 目標・担当範囲

小さい安定 ∞ 圏 C の全 gapped 図式から S•C を構成し、core・実現・loop により連結 K を定義する。
反復 S• による連結スペクトル、加法性、π₀ と三角圏の Grothendieck 群の比較、dg 圏への適用までを証明する。
引用を証明の代用にせず、追加公理・sorry を使わない。条件付き成果を無条件の完成と数えない。

所有：`SerrePositivity/KST/SConstruction/`、namespace `SerrePositivity.KST.SConstruction`。
Core 公開名・型を変更しない。Stable（α-S）、F1 の core（α2）、Spectra（L9）、比較・plus（L2）は読み取り専用。

## 2. 原典・正本

- `k-theory-kst-route.md` §4 D1、§5 K1・K0、§6、§10-5・11・12・13、§13 決定2・5・9・12。
- `foundations.md` §8 と経路正本 §13 決定16を優先。非連結化は BGT (a) のみ。
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
| L3 | §6 | fibration 定理、BGT (a) の非連結化、局所化不変量 |
| K-基盤 2 | §7 | Tamme の分裂、dg 増強流の ⊙ と Land–Tamme 主定理 |

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

### §10-12：最小 fibration 定理（後続 L3 の仕様）

C 安定、D thick、W={f | cofib(f)∈D}。W の2-out-of-3・pushout・extension 安定性が必要。
∞ 局所化と dg 商の比較には mapping 空間の比較まで要求し、H⁰ の Verdier 普遍性で代用しない。
冪等完備化は K₀ を変えるため、連結 K の局所化を全冪等完備 Verdier 列に無条件では課さない。
最終的な非連結 K(D)→K(C)→K((C/D)^idem) の fiber 列へは、必要な cofinality 条件を明示した
連結版と BGT §9 の非連結化を経由する。L11 では ∞ 版全体は未検証である。
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

## 6. L3・K-基盤 1（L1c〜f の後）

- **担当境界**：K の fibration・局所化定理は本レーン。Drinfeld 商の dg nerve と ∞ 圏的 Verdier 商の比較・Verdier 列の供給は D レーン β3。H⁰ の普遍性だけで mapping 空間の比較を代用しない。
- **Ind を待つ間**：小さい安定 ∞ 圏の完全関手を基礎に、冪等完備性の述語、Cat^perf の対象・射、Verdier 列、半直交分解、Sp 値の局所化不変量の定義と分裂列の帰結を整える。Cat^perf の ∞ 圏としての構成・極限は α2b の Cat_∞ に接続する。冪等完備化の存在を未証明の仮定で完成扱いしない。
- **fibration**：W の2-out-of-3・pushout・extension 安定性、S• の相対構成と加法性から連結版を証明し、必要な cofinality を明示する（Waldhausen 1985 §1.6、BGT §7–9、80–160時間）。β3 の商との比較は到着後に接続する。
- **非連結化は BGT (a) のみ**：N の Ind・κ-compact・冪等完備化と α2b の F2-lite を待ち、BGT §9 の suspension と反復 colimit により定義する（80–160時間）。Schlichting 暫定版 (b)・Bass による定義は導入しない。
- **完了条件**：冪等完備 Verdier 列を fiber 列に送る非連結 K、Morita 不変性、filtered 余極限との可換、連結 K との比較を証明する。値域の ∞ 圏 Sp は Sp レーンの供給を使い、局所化不変量の構造体にモデル圏 instance を要求しない（BGT §8–9、40–100時間）。

## 7. K-基盤 2（dg 増強流）

- **Tamme**：完全関手の lax pullback、標準包含・射影、半直交分解と分裂列を構成し、任意の局所化不変量で分裂を証明する（Tamme 2018 §1、60–120時間）。Cat_∞ の極限は α2b、dg gluing との比較は D の β4 を読み取り専用で使う。
- **Land–Tamme の ⊙**：dg 代数の Milnor 四角形から Perf の lax pullback と対角像の Verdier 商を作り、生成元の dg 自己準同型代数として A′ ⊙_A B を構成する。D の β3・β4・β5（非可換 D(A)・相対テンソル・Morita）を使う（Land–Tamme 2019 §1–2、100–200時間）。E₁ 環スペクトル・HA §2–4 の構成には進まない。
- **主定理**：Tamme の分裂と上の Verdier 列から、B′ を ⊙ に置き換えた四角形を全ての局所化不変量が引き戻しに送ると証明する。dg の対象供給と ∞ 圏の形式的議論を接続する（Land–Tamme §2、60–120時間）。
- **pro 版**：Tor の pro 消滅から ⊙→B′ の比較を経て pro 切除へ。Tor の環論は L7 の入力を待つ（Land–Tamme §3、80–160時間）。第 II 段のスキーム応用は基盤 I-a・I-b が閉じるまで起動しない。

## 記録の所在

実施記録・現在地の詳細・型一覧は [archive/L1-s-construction-log.md](archive/L1-s-construction-log.md) に移した（2026-10-19）。現在地は冒頭の引き継ぎ節が正本で、工程ごとの記録はコミットメッセージに置く。
