# K-L5：導来 blowup と半直交分解

> **休止（2026-10-19）**：foundations.md v2 の第 II 段（K の代数幾何）で再開する。引き継ぎ節を正本として保持。

## 引き継ぎ（2026-10-19）

### 現在地

- L5a の設計を固定。全図式 dg 加群の射影的模型と、canonical な導来係数拡大比較の
  可逆性・局所 perfect 性による充満 dg 候補を構成済み。層の Perf との比較は未完了。
- L5b は部分完了。普遍チャート、実際の有限重なり・pivot 変更、O(m)、Koszul 外積模型、
  導来底変更、E・D(n) の局所模型、指定遷移と cocycle を証明済み。
- 例外因子の実際の係数図式と共通 Ko(A;a) 表示の図式同型、canonical な比較の保存反映、
  元の例外因子 Koszul 表示の cartesian perfect dg 候補と指定 H⁰ 比較を構成済み。
- 例外因子の構造加群の cartesian perfect 性、指定 dg 代表と導来像への同型まで検証済み。
- L5c〜L5f は未実装。紙の検証や H⁰ 比較を、層の降下・dg 商の普遍性の証明とは扱わない。
- 最終検証：`lake build SerrePositivity.KST.DerivedBlowup` 成功（4800 jobs）。
  `lake env lean scripts/audit_kst_derived_blowup.lean` 成功（3750 宣言、標準三公理のみ）。

### 残り（依存順、原典番号と時間見積もり）

見積もりは実装・検証の粗い範囲。依存レーンの供給待ち時間を除き、大きな不確実性がある。

1. L5b：例外因子の整数捻り O_E(m)、平坦中央 H 係数化、閉埋め込み・射影の指定局所関手。
   KST v4 §3.1・Def 3.1・Lemma 3.6、pp.11–14。40〜120 時間。
2. L5a/b：図式 dg 候補と coherent homotopy-cartesian section／層の Perf の比較。
   dg 商・高次降下の整合性を含む。KST §3.1・Def 3.1、pp.11–14、L4 T3 が入力。
   80〜240 時間。古典 truncation の D_qc と導来 D_qc の同一視はしない。
3. L5c：負捻りの消滅と Rp′_*O=A′。KST Lemma 3.10・3.11、pp.15–16、
   Thomason 1993 Lemme 2.3、p.200。射影空間の有限 Čech 計算による別経路。80〜160 時間。
4. L5d：H 係数版の生成・充満忠実性・j*j_* の分解・部分商同値。
   KST Lemma 3.8〜3.15、pp.14–18、式 (3.4)、Neeman 9.1.5（局所化は L4）。160〜320 時間。
5. L5e：S1 の K0 界面に対する導来 blowup 降下。KST Thm 3.7、p.14・証明 p.18。
   上記半直交分解と S1 確定後、16〜48 時間。
6. L5f：射影束公式・Bass 基本定理と自然な分裂。KST Thm 3.16・3.17、p.19、
   TT 4.1、pp.329–330；6.1、pp.351–354；6.6、p.361；7.5、pp.365–366。40〜120 時間。

### 主要宣言（名前のみ）

- `finiteOverlapDGAlgebraDiagram`
- `finiteOverlapExceptionalDGAlgebraDiagram`
- `finiteOverlapExceptionalDGAlgebraInclusionNatTrans`
- `finiteOverlapExceptionalProductDiagramIso`
- `finiteOverlapExceptionalBaseNatTrans`
- `CartesianPerfectDiagramDGModel`
- `blowupDerivedTwistEquivalence`
- `diagramCoefficientDerivedComparison_square`
- `diagramCoefficientCartesianPerfectEquivalence`
- `finiteOverlapExceptionalAlgebraDerivedExtensionComparison_isIso_iff`
- `ExceptionalCartesianPerfectDiagramDGModel`
- `exceptionalCartesianPerfectDiagramHomotopyEquivalence`
- `exceptionalCartesianPerfectDiagramProductEquivalence`
- `derivedExceptionalStructureModule_cartesianPerfect`
- `exceptionalStructureDGObject`
- `exceptionalStructureDGObjectDerivedIso`

### 依存と提供

- 読取専用入力：`DifferentialGraded/` の DGCategory・加群・graph 導来随伴・Morita、
  L6 の Koszul、L7 の `KST/SchemeLemmas/`、L4 の `KST/DerivedGeometry/`。
- L4 の T1〜T3・Perf・RHom は未供給部分を残す。S1 の K0 界面確定は L5e/f の前提。
- 提供：実際のチャート／例外因子 dg 係数図式、基底射・閉埋め込みの係数自然変換、
  指定比較射、cartesian perfect dg 候補、捻り、元の E と共通 Koszul 表示の H⁰ 比較。
- 所有：`SerrePositivity/KST/DerivedBlowup/`、同名集約、当計画、専用公理監査スクリプト。

### 未コミット

- 本レーン所有の未コミット差分なし（引き継ぎ節も専用コミットに保存）。
- 共有ルート `SerrePositivity.lean` その他の他レーン差分はコミット対象外。変更・整理しない。

### 既知の問題

- 対象ビルド失敗・検出済みの名前衝突なし。共有ルート全体の最終ビルドは今回未実施。
- 所有ソースの検索で `ModelCategory`・`SSet`・`sorry`・`axiom` は一致なし。
  一般図式 API は `Small`、添字の順序・決定可能性などの仮定を持つ。型は Lean を正本とする。
- H⁰ の圏同値や係数圏の準同値だけで、coherent な降下・dg 商の普遍性・層の Perf の同値を
  結論しない。平坦中央 H 係数版および層の j・p・q との整合性も未完了。
- L11 記録では Thomason の全証明の直接照合は未確認。有限 Čech 再証明は別経路と明記する。
- 共有 Git に gc 警告あり。掃除・amend・rebase・reset は実施していない。

### 次の一手

例外因子の実際の有限重なり推移単元から O_E(m) を構成し、上記の元の dg 候補内で
canonical な比較の可逆性と局所 perfect 性を証明する。その後 H 係数化・層比較へ進む。

## 目標と所有

導来 blowup の有限チャート模型、射影空間のコホモロジー、KST Lemma3.8〜3.15、
Thm3.7・3.16・3.17 の係数版を証明する。namespace は
`SerrePositivity.KST.DerivedBlowup`、所有ソースは `SerrePositivity/KST/DerivedBlowup/`。
集約は `SerrePositivity/KST/DerivedBlowup.lean`、監査は `scripts/audit_kst_derived_blowup.lean`。
L4 の層・Perf・局所化・MV・Čech、L6 の Koszul と pro 消滅、L7 の古典 blowup は読み取り専用。
K に依存する部分は S1 の界面を明示的な構造体引数として用い、その存在を公理化しない。

## 原典

| 対象 | 原典と頁 | 経路 |
| --- | --- | --- |
| チャートと導来底変更 | KST arXiv:1611.08466v4 Def3.1・Lemma3.6、pp.11–14 | 普遍 blowup の導来底変更を Koszul 模型で具体化 |
| 生成と充満忠実性 | KST Lemma3.8〜3.12、pp.14–17 | 中央平坦係数 H へ拡張 |
| 部分商の同値 | KST Lemma3.13〜3.15、pp.17–18 | L4 の Neeman9.1.5 と接続 |
| 導来 blowup 降下 | KST Thm3.7、p.14、証明p.18 | K0 の局所化界面に対して証明 |
| 射影束・Bass | KST Thm3.16・3.17、p.19 | TT4.1 pp.329–330、6.1 pp.351–354、6.6 p.361、7.5 pp.365–366 |
| 押し出しと消滅 | Thomason1993 Lemme2.3 p.200；KST Lemma3.10・3.11 pp.15–16 | 射影空間の有限 Čech 計算による再証明。原典と異なる経路 |

正本：[KST経路](k-theory-kst-route.md)、[基盤](../infinity-lanes/foundations.md)、
[L11検証 §7・§8](L11-paper.md)。

## L5a：Perf の模型と比較

I=Fin(r+1)。U_i の環は Ko(A[S_j : j≠i]; (a_iS_j−a_j)_{j≠i})。
重なりは S_k を可逆化し、S_i=1 と規格化して S_j を S_j/S_k に送る。
全ての有限非空重なりを含む Čech 図式を用いる。基底環上の非導来 tensor ではなく、
局所 K-flat 模型による導来スカラー拡大を用いる。

第一候補を採用する：この環図式上の dg 加群の coherent な homotopy-cartesian section の
dg 圏を導来圏の模型とし、その局所 perfect な充満部分 dg 圏を Perf とする。
各遷移の随伴比較 `R_V ⊗ᴸ_{R_U} M_U → M_V` が擬同型であることを cartesian 条件とする。
単に underlying A 加群の制限射が擬同型である、という条件ではない。
strict な等式での複体の貼り合わせ・三重 cocycle だけの模型は採らない。

具体的には全 diagram-module の dg 圏を使い、図式の射影的／半自由置換を行った後、
objectwise acyclic を dg 商してから cartesian 条件と局所 perfect 条件を課す。
これにより mapping 複体も導来化する。対象だけを coherent にして Hom を通常の等化子で
計算する模型は採らない。局所 K-flat 分解を先行させる順序は L4 §26 と同じ。

比較の定理は二段に分ける：(1) 古典スキームの場合、L4 の T3 の Čech 降下で
層レベル `DqcDGModel` とこの chart-section 模型の Morita 同値を証明する。
(2) 導来チャートでは dg 代数の局所化・導来底変更・射影公式の比較を同じ Čech 図式上で証明する。
古典 truncation の D_qc と導来 D_qc が同じだとは主張しない。
L4 の T3 は現在未供給なので (1) は未証明の定理として工程に残す。
模型の定義に比較同値を仮定として入れない。L5b の環と Koszul 変換はこの比較を待たず構成できる。

O(1) は遷移単元 S_k、O(−1) はその逆を持つ可逆加群。
例外因子 E のチャートは Ko(A;a)[S_j:j≠i]、D(n) は U_i の Koszul に
a_0^n,…,a_r^n を加えたもの。これらの同定は Koszul 列の可逆基底変換で証明する。
H 係数版は中央 A 作用を持つ A 平坦な結合代数を tensor し、導来 tensor との比較を証明する。

## 工程

| 工程 | 内容 | 完成に必要な証拠 |
| --- | --- | --- |
| L5a | 上記の模型・L4との比較の配置 | 設計記載済み。比較の証明完了とはしない |
| L5b Charts | 普遍環・重なり・O(1)・Koszul基底変換・E・D(n) | 実際の環射／複体射とcocycleの証明 |
| L5c ProjectiveSpace | 負捻り消滅、Rp′_*O=A′ | Čech複体の縮約と導来比較 |
| L5d SemiOrthogonal | 3.8〜3.15 | 生成・Hom・部分商同値の証明 |
| L5e Theorem37 | 導来blowup降下 | K0界面からの自然なcartesian比較 |
| L5f ProjectiveBundle | 3.16・3.17 | 射影束分解・Bass完全列・自然分裂 |

## 記録の所在

実施記録・現在地の詳細・型一覧は [archive/L5-derived-blowup-log.md](../../L5-derived-blowup-log.md) に移した（2026-10-19）。現在地は冒頭の引き継ぎ節が正本で、工程ごとの記録はコミットメッセージに置く。
