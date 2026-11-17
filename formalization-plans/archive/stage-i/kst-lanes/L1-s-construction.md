# K-S• → K-基盤 1・2：∞-S• と局所化不変量

> **v3（2026-10-24）**：K-S• レーンの正本。所有：KST/SConstruction/。K-10 c は完了。d は Milnor 条件付き native Verdier 列と固定 ν の resolved 屋根を接続済み。e の Cat^perf 形式的結論を検証・保存済み。D の入口から四完備性を充足、残る具体的供給は d → e。VertexPrescribedExtension・ZeroBoundaryExtension と Stable 由来の 4 本は R で Core/・Stable/ へ移動済み。

> **v2 の位置づけ（2026-10-19）**：foundations.md §6 の K-S• → K-基盤。L1c〜f の後、L3 は非連結 K を BGT (a) のみで（暫定 (b) は使わない）、続けて局所化不変量・Tamme・Land–Tamme（K-基盤 1・2）。

## 引き継ぎ（2026-10-28・R 窓前の停止）

### 現在地
- **現在地コミット**：`d6b372b95`。元 end 辺の native 全評価と旧指定ホモトピーの全単体・全写像・同じ内部 Hom 辺の厳密一致、同じ元 cone 全二単体の二短辺回収まで構成し、集約・専用監査へ登録済み。元全 cone 図式と同じ底辺の選択 cofiber 全比較、元区間の全 Hom 増大表示・任意基底変換・元 Serre 対角の tensor 分解も保存済み。
- K-10 c は完了。d④② の D2 三入力は `19fab5fa8` で無条件代入済み。元二脚・恒等二脚・元 corner cone の全比較と、同じ resolved 商・指定冪等完備化を保持する。d②・e② と厚核側の下指定二単体は **K-S2 へ移管**。
- d④③：同じ実 S 長方形 `dgOdotMilnorActualRectangleDiagram` を構成済み。元上下比較二単体、実右零化面、長方形自体の上下合成二単体を厳密回収する。第一・第二認証は無条件構成済み。第三の全長方形認証は未完。
- `kernel_vertex` の等号そのものは `dgOdotMilnorActualRectangleDiagram_kernel_vertex` で証明済み。残るのは第三認証と組み合わせた最終 `DGOdotMilnorActualRectangleInput` への組み込み。独立の存在仮定に戻さない。
- `dgOdotMilnorRightAxisCompositeNuComparison` は元実中央射と実差の合成を元 cell 商射影へ全比較する。`dgOdotMilnorActualMiddleNativeArrowComparison` は中央辺の全矢印像を元 dg augmentation 全族へ照合する。元包含・負符号付き長辺、同じ二段 Perf 評価と元 raw 図式も回収済み。元 LT の `exactLift` への中央全関手同型は未完で、差との合成辺比較だけで第三認証を代用しない。
- 元 cone 左包含の同じ次数 −1 元を全 Hom end に持ち上げ、元零化二単体・零上二単体・全四角形を構成済み。native 全関手族への同時評価は core に制限せず、標的 Small を要求しない。元点評価で元 dg 加群の両二単体を厳密回収し、同じ全 cofiber 列を実証した。
- `dgOdotMilnorRightAxisCofiberFamily` は同じ元全 cone 図式を Sp 正本の `CofiberDiagrams.space` へ入れる。`dgOdotMilnorRightAxisCofiberFamilyComparison` は同じ底辺の選択 cofiber との全図式比較。一般形の `dgModuleNaturalConeCofiberLiftComparison_bottom` は全関手圏で底辺射影が指定恒等であることを保持する。元 counit の逆回転との全族照合は未完。
- **停止**：R 窓前の停止指示に従い、この検証済み区切りを保存して停止準備完了。稼働上限は 10-28 07:41 JST。再セッションは立てず、以後はユーザーの R 窓後の指示まで再開しない。

### ③ の残り（依存順、暫定見積もり）
1. [x] 元 end 閉辺の全 native 評価と旧指定ホモトピーの全比較（HA Construction 1.3.1.6）。`dgFunctorNativeStrictNatTrans_simplex`・`_homotopyMap`・`_edge` は全入力単体・全パラメータ写像・同じ内部 Hom 辺の厳密等号。`dgModuleNaturalConeFullTriangle_firstEdge`・`_lastEdge` は同じ元 cone 全二単体の二短辺を元指定辺へ接続する。
2. [ ] 同じ元 cone 全族の Perf/ν 評価を保ち、指定右辺を元 LT counit の全矢印族へ比較する。右辺切断 `CofiberRotation.rightSection` との全図式比較を回収し、底辺へ写して逆回転の中央全関手比較を作る（LT §1.2、4–8h）。`LaxUniversalDifference.connectingArrow` の全矢印像で比較し、元 cell 値同値と恒等 lax の矢印表示で反映する。
3. [ ] 共通 S 長方形の上下指定二単体と全二面比較を整列し、`VerdierRectangleDiagramIso` を構成（LT §1.2、3–6h）。下指定二単体は K-S2 の公開物を読み取り専用で使う。商辺や差の終点同型だけへ弱めない。
4. [ ] 第一・第二認証と第三認証、証明済み `kernel_vertex` を同じ `DGOdotMilnorActualRectangleInput` に組み込み、`dgOdotMilnorActualRectangle` として公開（1–2h）。集約・専用監査を通し、公開名をユーザー経由で **K-S2・Sp-3** へ報告する。見積もりは全比較の型照合に依存し、公開予定時刻は R 窓後の再開時に再評価する。

### K-S2・Sp-3 に渡す公開名（型は Lean が正本）
- 共通実長方形：`dgOdotMilnorActualRectangleDiagram`。
- 第一認証：`dgOdotMilnorActualRightSquareDiagramIso`、境界 `dgOdotMilnorActualRightBoundary`。
- 第二認証：`dgOdotMilnorActualOuterSquareDiagramIso`、境界 `dgOdotMilnorActualOuterBoundary`。
- 始点等号：`dgOdotMilnorActualRectangleDiagram_kernel_vertex`。
- **三認証一括の予定名（未公開・未定義）**：`dgOdotMilnorActualRectangle`。
- 消費型：既存 `DGOdotMilnorActualRectangleInput R d h` は変更しない。`diagram` は上記の共通実図式、`rightComparison`・`outerComparison` は上記の実認証。`boundary`・`comparison` が残る全長方形比較である。
- K-S2 の下指定面：`dgOdotTailKernelLiftTriangle`。共有対角は元厳密合成 `dgOdotMilnorFlatKernelInputMap ≫ dgOdotMilnorRightAxisInputMap`（`dgOdotTailKernelLiftComposite`）。元 S 上指定二単体も同じ対角を保持する。長方形の `pastingBottomTriangle` とは区別する。
- K-S2 の厚核面移送：`dgOdotMilnorKernelOuterSquareDiagramIso`、`dgOdotMilnorSourceOuterToKernelPerfectComparison`、`dgOdotMilnorNuNullLowerPerfectTriangleComparison`。
- 全 end 辺の旧指定辺との厳密一致：`dgFunctorNativeStrictNatTrans_edge`、`dgFunctorNativeStrictNatTrans_homotopyMap`。元全 cone 二単体の境界：`dgModuleNaturalConeFullTriangle_firstEdge`、`dgModuleNaturalConeFullTriangle_lastEdge`。
- 再開の中央比較入口：`dgOdotMilnorActualMiddleNativeArrowComparison`、`dgOdotMilnorRightAxisCompositeNuComparison`、`dgOdotMilnorRightAxisFullConeSquare`、`dgOdotMilnorRightAxisFullConeSquare_lower`、`dgOdotMilnorRightAxisCofiberFamilyComparison`。

### 依存・設計・供給依頼
- 所有：`KST/SConstruction/`、同集約、専用監査、本計画。ただし `Cofinality/`・`Cofinality.lean` は K-cof、`DGOdotTail*.lean`・`OdotTailAll.lean` は K-S2 の所有で読み取り専用。Derived・Gluing・F2・Stable・LocalizingInvariants は読み取り専用。コピー・移動・改名・削除をしない。
- dg 供給は D/D2、∞ Verdier 商・局所化・cofiber 比較 API は Sp の正本を使用。D2 の三比較、D-21 の実冪等完備化、D の perfect-projective 像補題 `perfectDGFunctorImage_perfectProjective`、nerve 同値からの `dgFunctor_quasiEquivalence_of_nerve` は消費済み。
- 始域は採用済みの「元入力への増大屋根＋ν 像の指定同値」で回収する。native Verdier 列・LT 錐の元始域は保持。resolved 商＋指定完備化を厳密商と取り違えない。
- Γ の自然収縮経路は、積 dg 圏上の h-射影性等が未証明なので臨界経路から外した。D の `moduleHomotopicallyProjective_contractingElement_of_acyclic` だけで解決済みとはしない。現経路は元 cone 左包含の明示自然 primitive である。
- **他レーンへ未送付の供給依頼・設計提案：なし**。D の nerve 反映は供給済みで消費した。追加不足は再開後、型と所有レーンをチャットでユーザーへ中継する。計画への記載だけで依頼済みとしない。
- 厳密 dg 入力限定、固定 S・ν・旧 K の公開型は不変。一般 StableInfinity 上の全スペクトル豊穣関手や一般 BF 高次整流を再開しない。K-S•-S4 の塔／Tor 比較は K-10 e 後で、未着手。

### 検証・未コミット・既知の問題
- 最新の集約 15938 jobs・公式監査 14406 宣言は成功。標準三公理のみ、監査型に ModelCategory 参照なし。所有の repository import 閉包 12118 モジュールは全て解決。新規 sorry・公理・検証上限／透明性オプション変更なし。
- 現在の検証ログ：`/tmp/ks-native-strict-edge-cutoff-aggregate.log`、`/tmp/ks-native-strict-edge-cutoff-audit.log`、`/tmp/ks-native-strict-edge-cutoff-closure.txt`。集約・公式監査・閉包検査済み。d・e の無条件の LT・非連結 K は未完。
- **未追跡で残す所有ファイル：なし**。今回の新葉は全て登録・検証して保存済み。他レーンの変更・未追跡ファイルには触れない。`/tmp/ks-actual-middle-remaining-type.lean` は残る全矢印比較から中央比較への反映を型検査した照合用メモであり、残る全比較の証明ではない。
- 所有閉包の破損・未解決の名前衝突なし。既存 Git gc 警告に整理操作はしない。キャッシュは消さない。

### 再開入口（R 窓後の指示を受けてから）
- 最初は `DGModuleNaturalConeFullBoundary` の同じ元二短辺回収を元全 cofiber 図式へ適用する。現在の族の標的は `dgNerve (RightModule Q)` なので、同じ Perf/ν 評価を保って元 LT counit の全矢印族と図式の指定右辺を照合する。`CofiberDiagrams.right` の全関手圏上の充満忠実性で `CofiberRotation.rightSection` との全図式比較を回収し、底辺へ写して `inverseRotation` に接続する。元 primitive・元終域評価・負符号付き長辺を保持する。全 end 辺と旧指定辺の比較は再構成しない。
- 上の③残り2→3→4。元 `dgOdotMilnorActualMiddleNativeArrowComparison` の右辺と、元 cell 値同値・`dgOdotMilnorOuterMiddleValueEquivalence` 後の `LaxUniversalDifference.connectingArrow` の全関手同型を示せば、元始域同値と恒等 lax の矢印同型に沿った反映で中央全比較へ戻せる。差との合成だけの比較は十分でない。
- 最終公開まで `dgOdotMilnorActualRectangle` を完成済みとは報告しない。d②・e② と下指定面は K-S2 に任せ、本レーンは③の本体のみを進める。
- **K-10 d②〜d④・e② 三段目（固定）**：
  1. [ ] d②（K-S2 へ移管）：D2 の Milnor 条件・実 lax 比較・cell 平坦商の型を照合する。
  2. [x] d③：元対角の充満忠実性と thick 核・局所化を Milnor 条件から接続する。
  3. [x] d②〜③：固定 S・ν の主経路を resolved 射影へ接続する。
  4. [ ] d④：Sp の零角・実面・長方形比較を接続し、未供給の全図式入力を分離する。
  5. [ ] e②（K-S2 へ移管）：四完備性を保持して Cat^perf の実商入力と LT 結論へ接続する。
  6. [x] 集約・公式監査・禁止仮定検査を通し、引き継ぎを保存する。

## 1. 目標・担当範囲

小さい安定 ∞ 圏 C の全 gapped 図式から S•C を構成し、core・実現・loop により連結 K を定義する。
反復 S• による連結スペクトル、加法性、π₀ と三角圏の Grothendieck 群の比較、dg 圏への適用までを証明する。
引用を証明の代用にせず、追加公理・sorry を使わない。条件付き成果を無条件の完成と数えない。

所有：`SerrePositivity/KST/SConstruction/`、namespace `SerrePositivity.KST.SConstruction`。
新たな K の関手の入力は厳密 dg 圏・dg 関手に限定する。安定 ∞ 圏上の既存成果は補助として保持する。
Core 公開名・型を変更しない。Stable（α-S）、F1 の core（α2）、Spectra（L9）、比較・plus（L2）は読み取り専用。

## 2. 原典・正本

- `k-theory-kst-route.md` §4 D1、§5 K1・K0、§6、§10-5・11・12・13、§13 決定2・5・9・12。
- `foundations.md` §8 と経路正本 §13 決定16を優先。非連結化は BGT (a) のみ。19:50 のユーザー承認決定に従い、Verdier 商・分数・局所化の API は Sp の `KST/LocalizingInvariants/` を正本とし、同種補題を SConstruction に新設しない。不足は Sp（∞ 側）・D（dg 側）へ依頼して待つ。K-10 c の具体的商 End 比較は続行する。
- `L11-paper.md` §5・11・12・13・S1。特に以下の文言補正を採用する。
- BGT v4 Definition 7.1、Lemma 7.3、Remark 7.4（gapped と第一行）。
- Fiore–Pieper Lemma 4.24、Proposition 4.27、Theorem 4.35、Corollary 3.35（McCarthy 型加法性）。
- [Rivera–Zeinalian, Higher Structures 4(1), 2020](https://dml.cz/bitstream/handle/10338.dmlcz/153417/HigherStructures_004-2020-1_2.pdf), §2.3（具体的な立方体圏、max connection のみ）・Example 2.2・Proposition 4.6：cubical Serre 対角と Λ の oplax tensor。原典の存在を追加仮定で代用しない。necklace の全射・joints・cube への作用は [Rivera–Zeinalian 2018](https://msp.org/agt/2018/18-7/agt-v18-n7-p02-s.pdf) §3・Propositions 3.1・4.2 を併用する。
- HTT 4.3.2.15（相対余極限拡張）、5.1.2.2（関手圏の点ごとの極限・双対）。

## 3. 工程

| 工程 | ファイル | 完了条件 |
| --- | --- | --- |
| L1a | Gapped.lean | Ar[n] と nerve、ihom、零対角・pushout 条件、充満部分単体集合 S_n、単体的関手性 |
| L1b | FirstRow.lean | 第一行制限、相対境界持ち上げ性、trivial Kan fibration |
| L1c（完了） | KOmegaSpectrum.lean・PresentedPerfectDGBFOmegaSpectrum.lean・PresentedPerfectDGBFConnectivity.lean | 実 BF Ω スペクトル、同じ零段と全負整数群消滅 |
| L1d（完了） | CoreAdditivity.lean・MultiRealizationAdditivity.lean・AdditivityNaturality.lean | McCarthy 型ホモトピー、全正反復実現の元の射対の加法性と自然性 |
| L1e（完了） | TriangulatedKZeroNatIso.lean・PresentedPerfectDGBFKZeroNatIso.lean | π₀ K ≃+ TriangulatedK0、同じ対象類と自然同型 |
| L1f（完了） | PresentedPerfectDGBFInfinityFunctor.lean・PresentedPerfectDGBFMoritaInfinity.lean・DGKHomotopyFunctor.lean | 実 Perf、厳密豊穣 BF K と γ1、Morita・準同値不変性、元の dgK 群との自然同型 |
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

K の主経路は **厳密 dg 入力に限定** する。dg 圏の単体的圏から BF スペクトルの単体的圏への
厳密な単体的豊穣関手を与え、γ1 の coherent nerve の関手性から Sp への ∞ 関手を得る。
任意の安定 ∞ 圏・完全関手に対する BF 上の手作業の高次整流は保存済みの補助成果に留める。
関手的な小さい Perf 模型と実 BF 置換・厳密豊穣関手・Sp 値化は構成済み。元の dgK への実スペクトル比較と全整数 π 同型も構成済み。同じ Sp 値関手の Morita・準同値不変性も証明済み。同じ Perf 上の整数 π 比較と新 BF の π₀=K₀ の入力自然性も証明済み。実 Perf 評価の native 比較と新 BF K→元の dgK の同じ実比較・整数群同型の入力自然性も証明済み。
実 Perf の対象型は宇宙 max (u+1) v、小さい代表系も現状は同じ対象宇宙に置く。
Small.{u} の証拠だけから native nerve の宇宙が縮むとは扱わない。

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

- **担当境界**：foundations.md §6 の 10-22 改訂に従い、K-6 の fibration・局所化定理は K-F レーンの `KST/Fibration/` を読み取り専用で接続する。本レーンは元の S• と厳密豊穣 K を供給する。Drinfeld 商の dg nerve と ∞ 圏的 Verdier 商の比較・Verdier 列の供給は D レーン β3。H⁰ の普遍性だけで mapping 空間の比較を代用しない。
- **Ind を待つ間**：N の全 coherent 冪等図式の分裂条件を使い、完全関手を持つ `StableInfinity` の全部分圏として `perfectStableInfinity`（Cat^perf）と quasicategory 性・充満忠実な包含を構成済み。`PerfectVerdierSequence` は既存の実 Verdier 商と N の `IsIdempotentCompletion` を保持し、商自体の冪等完備性は要求しない。同じ全 coherent 四角形と半直交分解、filtered 余極限保存を含む Sp 値局所化不変量も定義し、半直交分解の元の射影を保持する列へ接続済み。任意の提示列の coherent 四角形は元の二辺・零角と全単体を保って構成し、局所化不変量の同じ三対象・二辺の実 Sp fiber 列へ接続済み。不変量の半直交分解の分裂は、元の三射の回収・実 Sp 積錐の ∞ 極限性と同じ中央値への可逆辺まで証明済み。元の lax pullback の coherent 冪等完備性を両入力の完備性だけから証明し、元の包含・切断・射影を保つ Tamme 分裂と実 Sp 積錐へ接続済み。商・冪等完備化の存在と非連結 K の局所化性は未完成。
- **fibration の接続**：W の安定性・相対 S•・cofinality と連結版は K-F が担当する（Waldhausen 1985 §1.6、BGT §7–9）。本レーンは元の S•・加法性・Sp 値 K の公開界面を維持し、K-F の定理と β3 の商比較が到着後に接続する（接続の見積もりは両界面の型確定後）。 K-F 向け固定最小界面は `Gapped` の `Ar`・`arObj`・`arNerve`・`arMap`・`arNerveMap`・`gappedSubcomplex`・`sConstruction`・`sMap`・`sMap_ι`・`simplicialSConstruction`、全 Ar 評価は包含と Core の `evaluateFunctorAt` の合成、厳密な再添字可換性は `StructureMapCofibers.sMap_gapped_evaluate`（namespace は SConstruction）。後合成は同ファイルの `sPostcomp_gapped_evaluate`。相対加法性は `relativeCoreSAdditivityMap_localized_isIso`・`relativeMultiRealizationAdditivityMap_localized_isIso`（`ClosedStablePredicate` 版）、fiber 入力は `cofiberLeftFiberQuotient_localized_isIso` と `simplicialProductQuillenA`。任意の W 辺部分複体の定理ではないため、W の保存・相対比較を別に証明して接続する。 K-1 の固定追加界面として `CofiberCompletion` の `cofiberDiagrams`・`cofiberProjection`、`CofiberCompletionLifting` の `cofiberProjection_trivialKanFibration` を供給する（全て namespace SConstruction）。全 cofiber 四角形の選択と全高次族を保持し、射影は底辺 (0,0)→(1,0)、零角は (0,1)。後者の instance 仮定は `[Quasicategory C] [IsStable C]` のみで、ModelCategory 引数は無い。W 辺への pullback 制限と核条件との比較は K-F が担当する。 K-F の K-1/K-2 追加固定界面は `MultiRealizationFunctorIso` の `multiRealization_map_positive_localized_eq_of_functorIso`（全て namespace SConstruction）。完全射 f,g と `FunctorIso f.val g.val` から正の全反復 `multiRealizationFunctor (r+1)` の同じ射の anodyne 局所化像の等号を供給する。零回を含む一般版は `multiRealizationFunctor_map_localized_eq_of_functorIso`、元の射の実ホモトピーは `multiRealizationHomotopyOfFunctorIso`。証明は実完全関手 core の辺を元の全反復 S•・core・対角の厳密豊穣作用へ写し、全入力・全添字の整合性を保持する。行ごとの局所化等号だけから対角を結論せず、K-3 以降の定理も仮定しない。 K-F 固定三界面（厳密 dg 入力のみ）：`DGKFixedInterface` の `dgKInputInfinity` を同じ S とし、`dgKInputNu`・`dgKInputK` を固定。`dgKInputNu_vertex`・`dgKInputNu_edge`・`dgKInputNuMap_eq` が元の安定値と完全射を回収し、`dgKInputK_vertex`・`dgKInputK_edge` が元の BF 値と射を回収する。`DGKFixedSConstruction` の `dgKInputSBoundaryComparison_localized_isIso`・`dgKInputSBoundaryComparison_naturality` は ν(P) の元の境界商から正段への弱比較と元の辺に関する厳密可換式。`dgKInputSpectrum_zero`・`dgKInputSpectrumMap_zero` は同じ零段と零段射の loop 回収。旧 SOA K との対象別可逆辺は `dgKInputSOAComparison_isInvertible`（旧比較射自体の Sp 写像空間での自然性は未主張）。一般 StableCategory 上の K は提供しない。K-6(d) は同じ S 内の図式の ν 像が D β3 の VerdierDiagram となる場合に K が fiber 四角形を与える相対形で K-F が接続する。負次数消滅と π₀=K₀ は既存 `PresentedPerfectDGBFConnectivity`・`PresentedPerfectDGBFKZeroNatIso` を使う。
- **K-F の K-1/K-2 相対 fiber 固定入力**：`RelativeCofiberLeftFiber` の `relativeCofiberSubobjectLeftFiber A B a` は `simplexLeftFiber (objectSConstructionFunctor.map (relativeCofiberSubobject A B)) a`、`relativeCofiberLeftFiberQuotient A B a` はその `simplexLeftFiberProjection` と `objectSConstructionFunctor.map (relativeCofiberQuotient A B)` の合成。`RelativeFiberEquivalence` の `relativeCofiberLeftFiberQuotient_localized_isIso`（namespace SConstruction）は任意の `StableModel X`、`ClosedStablePredicate A B`、全 m と `a : (objectSConstruction (closedSubcategory A)) _⦋m⦌` に適用できる。根拠は同じ相対左 fiber 内の `relativeMcCarthyRhoHomotopy`・`relativeMcCarthyThetaHomotopy` と `relativeMcCarthyFiberSection_quotient`。全 C 版を W 部分圏へ制限しただけの結論ではない。周囲との射影・パラメータ・quotient の厳密照合は `relativeCofiberLeftFiberForget_projection`・`relativeCofiberLeftFiberForget_parameter`・`relativeCofiberLeftFiberForget_quotient`。K-3 以降を使用せず、K-F の基底変換と Quillen A の接続へ供給する。
- **非連結化は BGT (a) のみ**：foundations.md §6 の 10-23 改訂に従い K-7 レーンの `KST/NonConnective/` を読み取り専用で接続する。α2b の Ind・κ-compact、N の冪等完備化と F2-lite に基づく BGT §9 の dg suspension と反復 colimit は K-7 が担当し、本レーンは固定 S・ν・連結 K と元の S• 比較を供給する（接続の見積もりは型確定後）。Schlichting 暫定版 (b)・Bass による定義は導入しない。
- **完了条件**：冪等完備 Verdier 列を fiber 列に送る非連結 K、Morita 不変性、filtered 余極限との可換、連結 K との比較を証明する。値域の ∞ 圏 Sp は Sp レーンの供給を使い、局所化不変量の構造体にモデル圏 instance を要求しない（BGT §8–9、40–100時間）。

## 7. K-基盤 2（dg 増強流）

- **Tamme**：一般の Cat^perf の半直交分解について、任意の局所化不変量の同じ実値の分裂、元の包含・切断・射影の回収、実 Sp 積錐の ∞ 極限性と同じ分裂の可逆辺まで証明済み。元の F2 lax pullback の coherent 冪等完備性を C・D の完備性だけから証明し、同じ三頂点・両包含・第一射影を保つ Cat^perf 上の Tamme 分裂へ接続済み（Tamme 2018 §1）。残りは dg gluing との具体的同定で、D2 β4 の型確定後に接続する。Cat_∞ の極限は α2b、dg gluing 比較は D2 の β4、Sp の抽象分裂は K-5 を読み取り専用で使う。
- **Land–Tamme の ⊙**：元の非可換 dg 代数四角形から実延長像を保持する小模型・全 Hom 自然な比較対角と実 dg gluing を構成。指定対角商 End を右加群の向きで代数化し、元の右代数射を保持。D β3 の実商と D の生成 API により、元の ⊙→指定商の実一回 Perf 延長の Morita／準同値／native 同値を生成仮定なしで供給済み。固定 S の入力・実右三角形・ν/K 像と同値も供給済み。全 Hom・単位・全次数合成を保つ実 cone 関手、固定前像の既存収縮を持つ ContractedFunctor と既存商延長、元の関手・End・ε の回収、実 ⊙→元の終域代数の比較と元の右脚を構成。商 cone 作用の同じ tensor 評価と元の三段同型は、元の比較代数射の自由代表作用に全 Hom 自然で、同じ比較・逆比較・閉零自然同型を供給。評価した同じ cone 点を含む小さい実 Perf 模型を構成し、同じ二作用・元の三段同型・全 Hom 比較を保持済み。元の Hom end の入力閉同型と逆律、実一回 Perf 延長の指定同型・全 Hom 自然性と順逆成分回収、元の比較代数射の実延長と同じ小模型内の cone 一回延長との標準合成比較を保持する全次数比較・逆比較・閉零自然同型まで供給済み。元の終域から同じ小模型への厳密 Yoneda を、元の自由代表 End への準同値とその包含へ厳密に分解し、D の自由生成 API から Morita と同じ一回 dg Perf 延長の準同値／native 同値を追加仮定なしで供給済み。同じ固定 S 辺の Morita・ν の元の完全射の同値・K の全整数 π 同型と Sp 辺の可逆性、元の比較代数射との実三角形と同じ ν/K 像も供給済み。元の閉同型の宇宙持ち上げ・入力 Hom end の同じ閉同型と native core の実辺、固定 S の標準区間比較四角形と両対象端の固定・指定三辺の選択二単体、その同じ ν/K 像を供給済み。元の native 比較四角形の ν 像と同じ一回 Perf 延長の順逆成分の照合も供給済み。残りは D2 β4 による Perf(gluing) と元の Perf lax pullback の同定、同じ実商の D β3 Verdier 列・idempotent completion 後の実比較、S 内の自然な零化・長方形全体と ν 像の等式。対象別 ε の収縮を S 内の自然な零化と取り違えない。商・局所化 API は Sp 正本と D β3、生成 API は D から読み取り専用で使う（Land–Tamme 2019 §1.2 Lemma 1.11、100〜200時間）。E₁ 環スペクトル・HA §2–4 は構成しない。
- **主定理**：Tamme の分裂と上の Verdier 列から、B′ を ⊙ に置き換えた四角形を全ての局所化不変量が引き戻しに送ると証明する。dg の対象供給と ∞ 圏の形式的議論を接続する（Land–Tamme §2、60–120時間）。 Cat^perf 側には `PerfectLaxQuotient` の実商・完備化入力と二脚の比較を供給済み。完備化後の射は厳密 Verdier 商と仮定せず、包含の零化から普遍差への指定比較正方形を構成し、その全単体を Cat^perf へ持ち上げ済み。元の二つの Verdier 図式を含む全比較長方形と外周を Cat^perf に保持し、同じ Sp 値の比較正方形の引き戻し性を証明済み。元の C・D の値の BF 積に対する両射影を保つ Tamme 同値も証明済み。同じ全図式を元の C・D・完備化先の値の実 BF 積へ移し、四頂点・全関手同型・四成分・四辺の自然性・引き戻し性を保持済み。元の商の二脚と完備化後の商射の二脚も全比較済み。移送後の四辺は元の包含・両射影、対角、完備化後の元の二脚の実積射へ Arrow の等号で照合済み。元の実 BF 四辺に境界を固定し、元の左端の値を頂点・元の完備化後の二脚を脚とする実 Sp 極限錐まで供給済み。Cat^perf の実商・完備化を入力とする抽象切除は完了。dg gluing と ⊙ の具体的同定を追加仮定で代用せず、具体的主定理はその接続後に数える。 固定 dg 始域 S 上の現行 K-10 接続は `DGKRelativeInvariant`：E:S→Sp と `IsRelativeLocalizingInvariant (dgKInputNu A) E` を使い、S 内の長方形の ν 像が元の Tamme 長方形に一致する場合の同じ比較四角形の pullback 性と元の ν 像の回収を供給。一般 StableCategory 上の K は構成しない。
- **pro 版**：K-S•-S4（Sp の K-8 e 向け dg 供給）は K-10 e 後に着手。DGOdotInput の塔上の ⊙→B′ の LevelHom と cone の H⁻ʲ・Tor 欠損の自然比較（π₀・次数差を含む）を予定し、現在は着手しない。Tor の pro 消滅から ⊙→B′ の比較を経て pro 切除へ。Sp の K-8 の抽象 pro 論と β6 の dg 連結度を読み取り専用で接続する。Tor の環論で D の供給が必要になった時点でコーディネータ経由で依頼する（Land–Tamme §3、80–160時間）。第 II 段のスキーム応用は基盤 I-a・I-b が閉じるまで起動しない。

## 記録の所在

実施記録・現在地の詳細・型一覧は [archive/L1-s-construction-log.md](../../L1-s-construction-log.md) に移した（2026-10-19）。現在地は冒頭の引き継ぎ節が正本で、工程ごとの記録はコミットメッセージに置く。
