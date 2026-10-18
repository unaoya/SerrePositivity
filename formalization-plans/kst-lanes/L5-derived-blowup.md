# K-L5：導来 blowup と半直交分解

## 現在地

L5a の模型を固定。L5b の多項式チャート、普遍構造射、重なりの座標 cocycle、
O(1) の単元 cocycle、Koszul 関係式の変換公式は対象ビルド済み。
局所化環上の同型と Koszul cdga の構造・基底変換は未実装であり、L5b 全体は未完了。
L5c〜L5f は未実装。完成は各工程の構成・比較・対象ビルドと全宣言公理監査が揃った時点。
既存の L11 の検証記録を、Lean の証明済み宣言とは扱わない。

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

正本：[KST経路](../k-theory-kst-route.md)、[基盤](../foundations.md)、
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

## 主要宣言

| 宣言 | ファイル | 状態 |
| --- | --- | --- |
| `ChartIndex`・`ChartRing`・`chartCoordinate`・`chartRelation` | Charts | 対象ビルド済み |
| `normalizeCoordinates_cocycle`・`transitionUnit_cocycle` | Charts | 対象ビルド済み |
| `chartTransition`・`chartTransition_coordinate` | Charts | 対象ビルド済み |
| `chartTransition_cocycle`・`chartTransition_unit_cocycle` | Charts | 対象ビルド済み |
| `chartTransition_relation` | Charts | 対象ビルド済み |
| `UniversalBase`・`UniversalChart`・`projectiveChartInclusion` | UniversalCharts | 対象ビルド済み |
| `universalBaseMap`・`universalBaseMap_X`・`universalMinor_zero` | UniversalCharts | 対象ビルド済み |

Koszul 関係式の変換は環の元の等式であり、複体または dg 代数の同型ではない。
上表の所有モジュールの全34定数について、公理監査は標準三公理のみで成功。

## 保存単位の検査

`lake build SerrePositivity.KST.DerivedBlowup` と
`lake env lean scripts/audit_kst_derived_blowup.lean` を実行する。
監査は所有モジュール内の生成宣言も含む全定数の依存公理を再帰検査し、
`propext`・`Classical.choice`・`Quot.sound` のみを許す。
他レーンの変更をコミットしない。ルート追加は担当集約の import 一行だけとする。
