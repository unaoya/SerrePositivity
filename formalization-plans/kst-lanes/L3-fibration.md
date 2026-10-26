# K-B レーン：K-6 fibration 定理（L3）

> **分担更新（2026-10-26）**：K-B は K-6 のみを継承する。所有：KST/Fibration/（Relative/ を含む）、集約 Fibration.lean、audit_kst_fibration、本計画（300 行以内）。既存 ClosedStable* は編集せず、S-1 (c) の新規供給葉を消費する。K-7・NonConnective/ は K-B3 へ移管し、以後編集しない。第 I 段の完成条件は I-4。

> **v2 の位置づけ（2026-10-22 新設）**：foundations.md §6 の K-F。K-S• の L1（∞-S•、加法性、homotopy fiber）と Sp の K-5
> （抽象 Verdier 列、Sp 値局所化不変量）を読み取り専用で使う。**2026-10-25 採用の修正**：(d) は固定の厳密 dg 入力 S・ν:S→StableInfinity・連結 K:S→Sp に対し、K(D)→fib_Sp(K(C)→K(C/D)) が非負次数で π 同型となる連結版（連結スペクトラムでの引き戻し）とする。10-22 の「実 Sp fiber 四角形へ送る」は撤回。固定連結 K の Sp 引き戻し性は主張しない。既存の条件付き Sp fiber 定理は条件付きで保持する。
> 非連結化（K-7、BGT §9）は F1b・N の Ind・冪等完備化の後に別途。

## 引き継ぎ（2026-10-26、c5 代入入口を公開して Sp 中継待ち）

### 現在の供給と残り
- 公開主定理：`Relative.ConnectiveFibrationTheorem` の `k6FibrationOfC5`。同じ R・D・I を固定し、依頼文そのままの c5 一つから d の非負次数比較と e の出力を `K6FibrationConclusions` に束ねる。c5 自体の実供給は未着。
- c4 完了：S-1 (a) `5640d0942` の `nativeTriangle_ext` を `kbMovingCanonicalFiniteExtConsumer` の四有限端点へ代入した。`verdierCanonicalKernelSquareIso d` は実読出し・相対合成も実供給から選び、d のみから元の全四角形の FunctorIso を構成する。
- K-B2 向け共通化は `f2e3595d9` の `closedStableFlagPostPullback`（B・P のみ）を公開済み。K-B-S2 は `bf29e6b53` で保存・チャット報告済み。Sp 所有の二変数 corner RLP は重複実装しない。
- 残りの順序：c5 の Sp 有限線型図式・core 逆像商比較の代入 → 条件付きで組み立てた b・d と e の構造射入力の放電。K-7 の同じ条件付き実反復は K-B3 が所有する。
- 供給：S-1 (a) `5640d0942` と S-1 (c) `69c370610` を消費済み。Sp 有限線型図式比較の依頼は、ユーザーが循環のない閉包を確認して中継済み。下記の正確な型の実供給待ち。
- 所有外の NonConnective・ClosedStable* は編集していない。未コミットの作業は停止時に所有ファイルだけで保存する。
- 次の一手：ここまでを保存して停止し、ユーザー経由の Sp 到着を待つ。到着後は下記と同じ型の証明を `Relative.k6FibrationOfC5 R D I` へ一回代入する。c4・共終性の追加入力はない。
- 検証：Fibration 集約と専用公理監査を行い、結果はコミット本文へ記録する。NonConnective の検証・編集は K-B3 が担当する。
### c5：Sp コーディネータへの供給依頼（正確な型）
- import：`SerrePositivity.KST.Fibration.RelativeFirstRowSimplexQuotient`。`h : VerdierSequence.{u}` に対し次を依頼する（名前は供給元が決定）。
```lean
∀ n : ℕ, IsIso (AnodyneHomotopy.anodyneQ.map
  (relativeFirstRowSimplexQuotient h.projection n))
```
- 射は同じ商後合成 `Fun(Δ[n], middle) → Fun(Δ[n], right)` に沿う core の厳密逆像から、標的 core への指定射影。n=0 を含む。一般局所化の普遍性だけで core 比較を代用しない。
- 元の正段との同値：`relativeSQuotient_localized_isIso_iff_firstRowSimplex`。元の実現への接続：`relativeSQuotientRealization_localized_isIso_of_firstRowSimplices`。
- `Relative.SingleRelativeComparison.ofFirstRowSimplices` は同じ c4 全四角形同型と c5 入力を既存の相対実現界面へ渡す。供給の存在は主張しない。NonConnective への新規 import はない。

### 現在地
- e の受け渡し：`Relative.CanonicalSuspensionInput` は `Cofinality.kSpectrumMap_cofinality`（7397052d8）を元の実 Yoneda 完備化比較へ代入する。正次数 π 全単射・零次単射・一回 loop 後の非負次数 π 同型に共終性入力は残らない。
- `dgKappaCanonicalSuspensionStructureMap_nonnegative` は同じ I・Z と c5 だけを取り、元の固定 K の実隣接構造射の非負次数 π 同型を供給する。`_eq` は K-B3 の既存 hcofinal 付き射との厳密等号で、反復の隣接射を選び直さない。全 native 自然性・逐次余極限・非連結化後の局所化性は K-B3 側。
- b の統合：`Relative.CanonicalRealization` は c5 だけから元の商射の指定基点上の fiber 同型と、元の核包含への射影公式を供給する。S1 の実閉部分圏四角形は `closedRelativeInfinitySquare_isPullback` で無条件の native 引き戻しへ接続した。
- d の組み立て：`Relative.CanonicalSingleStageDetection` は c5 のみから同じ実供給 BF fiber 比較の非負次数 π 全単射性と群同型を得る。`Relative.CanonicalFixedSourceFiber` は元の実核比較と指定始点同型を前置し、元の固定 K(D) 始点を持つ実比較辺と非負次数 π 同型まで接続する。
- d の境界：上記の比較先は同じ実供給 BF 右辺の fiber。ユーザー確定により旧固定 K 右辺への輸送は K-6 の範囲外。必要時は K-B3 が K-7 f で K-S• へ提起する。c5 は未放電。d の葉は既存 NonConnective を読み取り専用で消費する Relative.All に集約し、主 Fibration 集約へ NonConnective を逆 import しない。
- b の既存界面：`Relative.All` の `finiteComparisonNatIso` は局所化圏値の単体的同型（生の SSet 実現同値を含意しない）。`singleAdditivityFiberIso` と射影公式は同じ包含・指定基点を保持し、単回版に追加収縮入力はない。`relativeRealizationInfinitySquare_isPullback` は実相対核四角形に適用し、元の指定 Verdier 四角形へ戻すには `SingleRelativeComparison` の二比較が必要。
- S-1 (c) `69c370610` の無条件四角形・fiber 同型・元の射影公式・指定零旗の零化を `Relative.FibrationSupply` から公開し b で消費済み。同じ集約は有限座標と相対実現界面も公開する。NonConnective は import せず、既存 ClosedStable* は編集していない。
- 採用済みの連結版へ再開：K-6 d は元の実 fiber 比較の非負次数 π 同型。`DGConnectiveFiberComparison` は固定 dg 四角形と K 零角から同じ実 fiber 比較・全脚の二胞体・非負次数条件付き群同型を構成し、ν の Verdier 認証や Sp 引き戻し性を使わない。K-7 は同じ cone の K 零性から構造射・比較を作る。c5 と d を継続し、K-7 d は K-B3 へ渡す。
- `VerdierFullSLowerDeformation` は元の全下側二胞体から最大 path 二胞体への実三角柱・恒等縦辺・全関手同型を与える。`VerdierFullSLowerShortFaces` は二短辺の全時刻固定、`VerdierFullSLowerRelativeDeformation` は同じ内ホーンを固定した可縮 Kan 延長空間への実辺と元の全三角柱の回収を保持する。`VerdierFullSLowerMaximalFaces` は同じ変形の時刻一で二短辺を評価し、元の指定包含・商の同じ全一単体へ戻す。`VerdierFullSLowerKernelTriangle` は同じ最大 path 図式の全二胞体を元の実 Kan 包含・商の標準合成へ同定し、元の指定 Verdier 下側全二胞体から元の商核下側全二胞体への実関手同型を与える。`VerdierFullSLowerDeformationSource` は同じ全三角柱・最大化全二胞体・動く対角族を、元の Stable∞ 二胞体から同じ S• Kan 作用への像として厳密回収する。`VerdierLowerDeformationZeroHom` は同じ Stable∞ 三角柱の全次数・全時刻単体の長い Hom を元の零値部分空間へ持ち上げ、同じ全 Hom と全正反復 S• Kan 像を厳密回収する。`VerdierLowerDeformationFullSLongHom` はこの全族を元の全 S• 始域の native Kan Hom へ延長し、元の core 包含で全次数・全時刻の全 Hom を厳密回収する。二胞体では元の変形二胞体の全長 Hom 自身に一致する。`VerdierLowerDeformationFullSComposite` は指定した三頂点全体の合成 path と、その全 S• 作用の実合成端を全時刻で保持する。`VerdierLowerDeformationFullSNaturality` は同じ零値持ち上げと全 S• 延長の、全パラメータの単調な制限との厳密な可換性を与える。`VerdierFullSMovingSquarePrism` は元の動く対角を厳密に共有する上側全族に条件付きで、両全三角柱を回収する四角柱・四頂点の可逆性・同じ元の Verdier 四角形との全関手同型を構成する。終端を実全 S• 商核へ固定し、下側全二胞体の最大化との厳密一致を証明した。`verdierFullSMovingKernelSquareIso` は同じ実商核まで接続するが、上側全族自体は未供給で、存在入力を主経路へ追加しない。F1 正本への依頼：短辺・合成端を固定した全長 Hom のパラメータ付き族から、元の全二胞体の族を厳密回収する公開界面（コーディネータ経由）。
- `ZeroMiddleControlledTriangleInput` は元の全 S• Hom を core 包含で制限し、同じ二短辺の指定合成端を持つ実 fiber の点を構成する。元の指定 core 二胞体の全長 Hom と厳密に一致し、元の合成 path と仕様の全体 path の等号も回収する。`ZeroMiddleFixedHornComparison` は元の三面を固定する実充填空間の可縮 Kan 性・元の既存充填の指定点・構成済みの制御充填との fiber 内の同型と面 2 の上側全比較を供給する。制御充填の存在は主張しない。`VerdierLowerDeformationZeroHomFaces` は同じ零値長 Hom の持ち上げが全ての面・退化に厳密に自然であることを保持する。点ごとの零値条件を全三角柱の整合的な族へ接続するが、上側との同じ動く対角での貼り合わせは未証明。
- 上流 import 閉包は D の修正後に復旧確認済み。両所有集約を再ビルドして成功。K-6 c4 の全四角形比較と c5 の商実現比較を進める。
- 工程 (a) 完了。K-5 の実核条件から包含の本質像を同定し、cofiber-W と商の可逆性、二対三・pushout・pullback・ホモトピーに対する拡大安定性を証明。
- 工程 (b)（K-B2 の明示供給境界版 f7d3f64a4 を消費、既存葉は読み取り専用で供給）：全相対 S_n・面退化・core 包含・商への射と核四角形を構成。元の全 Ar 評価・S 後合成の完全性と全成分の零対象検出を証明。
  同じ実 cofiber による相対辺判定と、全 n の二対三・pushout・pullback・拡大安定性を証明。元の S_n(D) 包含は全写像空間で充満忠実で実核像に一致し、同じ cofiber の像条件を回収。W 辺・相対 cofiber 射影は trivial Kan、全正反復の加法性へ接続済み。
- 有限 W 列の初期頂点・連続 cofiber 比較は、零長で厳密同型、全長・全正反復で局所化同型。
  全単体的有限積比較は未主張。元の相対 S と W 列 core S の対角・定数列・実押し出しを保持。
- 元の核包含を実核への完全同値へ制限し、K-2 Segal 実現で元の核四角形を homotopy pullback と証明。
  relativeSFibrationFiberIso は実 fiber と core S(D) の局所化同型で、同じ射影は元の包含の実現射。
  quotientSFibrationFiberIsoOfComparison は条件付き。元の S• 商核四角形を構成し、同じ商実現比較の可逆性を入力すれば homotopy pullback。通常の全錐比較と任意の Kan 四角形の橋渡しにより、同じ Ex∞ coherent 四角形は native な ∞ 引き戻し。元の四頂点・四辺を同じ Ex∞ Kan 値と元の射の coherent な一単体として回収し、同じ相対 S 核の角の終対象性も証明。一回の反復実現への全 Hom の座標読み替えは元の豊穣関手と等しい。指定 Verdier 四角形の包含・商辺と三頂点は厳密一致し、残る角は実終対象間の同型。零値完全関手の実 Kan Hom 部分空間は可縮で、任意の指定部分族を厳密に保つ延長と元の全正反復 S の全 Hom への図式比較を構成。零圏から・零圏への全 Hom の可縮性により、指定 Verdier 四角形は元の StableInfinity の零角付き四角形となる。指定 Verdier 上側二単体の全長 Hom を元の零値部分複体へ読み出し、同じ全長 Hom と元の全正反復 S 像で厳密照合。元の上下二単体の共有対角 δ₁ は厳密一致。下側の全長 Hom も零値族へ読み出し、全正反復 S 像で厳密回収。共有対角の同じ両端で読んだ両二胞体族は直接 path の像が同じ対角頂点で、全関手同型を構成。可縮な零値 Hom 空間への制限の実 fiber により、対角上の制限が元の恒等一単体となる全比較辺を構成。評価円柱は全時刻で共有対角を固定し、全正反復 S の全 Hom 作用後も固定条件を保つ。比較円柱の合成 path 側の実辺を評価し、元の指定両端で下側合成が包含・商の合成そのものと証明。元の上側零合成との全自然同値を、同じ比較円柱から回収。合成 path 上の全時刻評価も厳密一致。一つの零自己関手→恒等の実自然変換を全 S_n の全 Hom 作用へ送り、全ての面・退化に自然な実円柱を構成。核上の包含そのものを順射とする全単体的同型で相対核へ戻し、同じパラメータの対角円柱と一点への具体的収縮ホモトピーを構成。元の商比較へ全単体的円柱を送り、元の core S 包含・商の実合成に対する具体的零化ホモトピーを構成。零値後合成の全族を元の Kan Hom へ読み戻し、その全 S_n 作用が同じ商核円柱の包含後の像と厳密一致。指定下側二胞体の直接 path→合成 path 族と、実合成端を全時刻で固定した全比較辺・円柱を構成し、全正反復 S の全 Hom 作用後も固定。元の指定両端への対象座標の輸送後も同じ全収縮族を異種等号で照合。元の core 包含で制限した全単体的零化円柱の各段は、K-S• の同じ全 Kan Hom 族による core S_n 作用と厳密一致し、対角は元の零化円柱を回収。全図式 Hom の射影を用いて全入力族を全単体的円柱へ送り、対角が元の豊穣対角作用と厳密一致すると証明。全有限反復 core S• へ接続し、一回の native 図式と元の core S• の恒等成分の同型を介して、元の商核零化円柱が同じ実合成の全豊穣実現族の評価と厳密一致。core 制限・対角・Ex∞ を通る全四角形比較は c4 で構成済み。商実現比較の可逆性は未証明で、無条件 K-6(b) の統合は未完。
- Ore・分母輸送・固定分数・可変終点 coslice の既存構成は保持し、新設は Sp 正本へ依頼する。
  全 span 族の評価・全単体被覆・W 反転・降下・同じ分数比較の回収を構成。一般比較同値・span 普遍性は未証明。
  tamme* の lax 専用仮定を一般 Verdier 商へ流用しない。H⁰ の普遍性で全写像空間を代用しない。
- 元の scaffold 埋め込み・二脚・相対三角・係数点と、native 表現の pointedMap の指定点を保持。
  豊穣実現・curry・転置・反転・strict transport の同じ指定成分を、元の点の作用と照合済み。
- 切断の底変換・under 実現・初頂点制限・反転・共通 Hom 解像の指定成分を、元の実図式と照合。
  同じ strict 持ち上げの恒等射評価は、第一射影により元の単体切断の初頂点を厳密に回収する。
- F1 の exists_leftCoherentTransport_directComparison は底上の同値だけで指定 scaffold 三角形を残さず、元の係数点との一致は推論しない。
- scaffoldNerveRepresentationIso は指定 scaffold 三角形を保持し、係数点を元の恒等射評価の同じ fiber 点の
  pointedMap 像へ送ると証明。scaffoldStraighteningRepresentationIso はその指定制限比較を Sp の前合成充満忠実性で戻す。
  新主経路の scaffoldPointedReconstruction は実射・射影・前合成同値・fiber 点計算を構成。
- 指定した全制限比較と降下後の同じ成分を厳密に照合。native 表現の制限点は第一射影した元の同じ fiber 点の像。
  元の単体切断の係数点を、新復元射による同じ初頂点 fiber 点の実像へ接続済み。
- 左右の底変換比較の端点等式と切断の全空間値を保持。初頂点 fiber 点は既存の実底変換像と厳密一致。
  任意の実 fiber 点を零単体切断で回収し、元の実図式の同じ指定成分に対する復元像の底変換自然性を証明。
- 新分類比較は、strict・cocartesian 切断の元の係数点を、実底変換した同じ fiber 点の新復元像へ送る。
  既存の coslice 点族は恒等錐で同じ実点を回収。新復元恒等点からの延長は新復元射と全写像空間で自然同型で、前合成同値。
- 既存の分数分類を新比較へ接続。元の恒等 span の strict Kan 比較像は、既存の固定分数評価を経由して
  同じ scaffold 復元恒等点へ送られる。元の coslice 合成は新復元射と全相対写像空間で自然同型で、無条件に前合成同値。
  元の比較に、商上の実右逆と全相対写像空間内の余単位を構成。同じ右逆を全 fiber へ制限し、余単位と本質的全射性を証明。
  同じ比較二胞体の成分の点の射の全射性を、元の strict Kan 比較成分の実本質的全射性へ移送。
  Sp 正本の `verdierFractionMappingComparison_isFullyFaithful`（d08ea0c53）を代入し、元の全 strict Kan 成分・全終点の分数比較の同値と元の商上の比較自体の可逆性を `WeakQuotientMappingEquivalence` で接続した。商実現比較は未完。
- 工程 (c)：中央・右 π の k 未満の消滅の下で、左 fiber の同じ消滅 ⇔ πₖ 射影全射を K-5 の実長完全列で証明。
  中央 πⱼ=0 なら右 πⱼ₊₁／射影像 ≃ 左 fiber πⱼ。代表元は元の接続射。零次余核の障害を明示。
- 固定 dg K の実頂点・実辺の整数 π 作用を同じ BF 射と可換に比較し、πⱼ 全射性の同値を証明。
  元の Verdier 商の三角圏 K₀ 作用は全射で、同じ射の代数的零次余核は零群。
  固定 ν の同じ dg 辺の K₀ 作用を実完全関手と照合し、ν 像が Verdier 列となる厳密 dg 列の全射性を証明。
  既存の厳密 dg K₀ 自然比較と固定頂点・辺の同定で、ν 像が Verdier となる同じ固定 K 商辺の実 π₀ 全射性を証明。
  任意の相対 Verdier 四角形の元の右辺を同じ dg 射として回収し、ν 像の商辺と照合。元の K 右辺の実 π₀ 全射性を証明。
  同じ相対 K 右辺を持つ実 Sp fiber 四角形を構成し、元の BF fiber との群同型で全負整数群の消滅を証明。K(D) との同定は未証明。
  ν(P) が零なら全反復 S・境界商の一点射が局所化可逆で、正段の整数 π 検出により固定 K(P) は零。任意の元の相対 K 四角形の零角を保持する。
- 工程 (d) は採用済みの連結相対形：同じ厳密 dg 入力 S 上の ν:S→StableInfinity、連結 K:S→Sp。元の実 fiber 比較の非負次数 π 同型を証明する。以下の Sp 引き戻し検出は追加仮定に条件付きの既存成果として保持する。
  元の零角・右辺を保持した canonical fiber と K(D) からの実比較辺、全脚の合成三角形を構成。元の四角形の引き戻し性 ⇔ 同じ比較辺の可逆性を証明。
  比較先を同じ dg 右射の BF fiber に比較し、両端の負次数消滅を証明。元の比較の非負次数 π が全単射なら元の K 四角形は引き戻し。非負次数の条件は未証明。
  固定 K の非負次数 π と一段 S• 境界商の π を自然に比較。元の core S•・対角実現・境界商の全 Hom を ν 後合成と照合し、指定 VerdierDiagram の境界商四角形と固定 K の各正段四角形を全高次単体で同定。元の反復実現から境界商への商射は全 Hom に自然で、同じ Ex∞ 商射を成分とする全図式同型を構成。基点忘却後の全正段で同じ Sp 辺の可逆性を検出し、元の実 fiber 錐の極限性も証明。元の相対 K 四角形が引き戻し ⇔ ν 像の元の全正反復 S• 実現の Ex∞ 四角形が引き戻し、まで証明。後者の無条件な引き戻し性は未証明。
- 工程 (e)：冪等完備化の正次数同型・零次単射・loop 比較を実共終性で放電し、同じ元の固定 K 構造射への c5 のみの入口を供給。K-7 本体は K-B3 が担当。
- Fibration・Relative.All と専用監査で b・d・e の供給閉包を検証する。c1〜c4 は完了。c5 の商実現比較の実供給待ちで、無条件 K-6 の完成印は変更しない。
### 残り（依存順）
1. 商実現比較を証明し、無条件の連結版 fibration 定理へ接続する（Waldhausen 1.6.4、BGT §7、40–80時間）。
2. 証明済みの任意の相対 Verdier 四角形の実 π₀ cofinality・fiber 連結性を、β3 の具体提示へ照合する（BGT §7–8、4–8時間）。
3. 証明済みの固定 K の相対零保存と元の四角形を保持し、K(D)→fib_Sp(K(C)→K(C/D)) の非負次数 π 同型へ接続する（BGT §7–8、16–32時間）。
4. 固定 dg 界面との接続後に、完備化と BGT §9 の非連結化への実入力を確定する（8–16時間、K-7 本体は別）。
### K-B3 向け公開界面（共通接頭辞 SerrePositivity.KST.Fibration.Relative）
- 一葉 import：`SerrePositivity.KST.Fibration.Relative.ConnectiveFibrationTheorem`。主 Fibration 集約の NonConnective 非依存は保持する。
- BF 中央／商対象：`dgKappaNativeBFFiniteOmegaSpectrum R D I (dgKappaNativeBFFiniteNativeObject R D I 1)`／同添字 3。商射：`(dgKappaNativeCoherentBFArrow R D I 1).hom`。主定理の `.quotient_edge` で照合する。
| 出力 | 公開名 | 範囲 |
| --- | --- | --- |
| c5 一回の入口 | `k6FibrationOfC5`・`K6FibrationConclusions` | `.fiber_nonnegative`・`.quotient_edge` と e の四結論を射影。c5 の Prop は依頼文どおり。 |
| d | `dgKappaCanonicalFixedSourceFiberComparison_nonnegative`・`k6Fibration_fiberTarget` | 元の固定 K(D) から実供給 BF 右辺の Sp fiber。旧固定右辺への輸送は範囲外（ユーザー確定）。`k6Fibration_quotientEdge` が実右辺を照合。 |
| e の隣接射 | `dgKappaCanonicalSuspensionStructureMap_nonnegative` | 同じ I・Z と c5 のみ。正次数同型・零次単射・loop 比較は実共終性で放電済み。 |
| 既存反復との照合 | `dgKappaCanonicalSuspensionStructureMap_eq` | 任意の既存 hcofinal 証明を用いた元の構造射との厳密等号。 |

### 主要宣言（共通接頭辞 SerrePositivity.KST.Fibration）
- weakEquivalences、mem_weakEquivalences_iff_invertible、weakEquivalences_twoOfThree、weakEquivalences_pushout_iff、weakEquivalences_pullback_iff、weakEquivalences_extension。
- verdierSStageKernelEquivalence_inclusion、verdierSPostcomp_fullyFaithful、verdierSPostcomp_kernel、relativeSConstruction_mem_edge_iff_cofiber_image。
- weakStringConstantPostSquare_homotopyPullback、relativeSKernelRealizationSquare_homotopyPullback、relativeSFibrationFiberIso、quotientSFibrationFiberIsoOfComparison、quotientSKernelInfinitySquare_isPullback、quotientSKernelInfinitySquare_right、quotientSKernelInfinitySquare_bottom、quotientSKernelInfinitySquare_corner_isTerminal、stableCoreSingleKanEnrichedFunctor_eq、stableMultiSingleKan_edge、quotientSKernelInfinitySquare_right_eq_verdierSingle、quotientSKernelInfinitySquare_bottom_eq_verdierSingle、quotientSKernelCornerIso_verdierSingle、zeroStableHomSpace_isContractibleKan、zeroStableHomFamily_extend、zeroStableHomMultiFamilyIso、verdierDiagramZeroTriangle、stableHomZeroVertex_iff_of_edge、coherentTriangleLongHom、verdierUpperTriangleZeroHomLift_recovery、verdierUpperTriangleZeroHomLift_multi_recovery、verdierTriangle_sharedDiagonal、verdierLowerTriangleZeroHomLift_multi_recovery、verdierNullHomFamily_direct、verdierNullHomFamilyIso、contractibleTargetRestriction_trivialKanFibration、FixedRestrictionFunctorEdge、verdierNullHomRelativeComparison、verdierNullHomRelativeMultiComparison、verdierNullHomComparisonPrism_diagonal、verdierLowerTriangle_first_arrow、verdierLowerTriangle_last_arrow、verdierNullCompositeOriginalMap_lower、verdierNullCompositeIso、verdierNullHomComparisonPrism_composite、exInfinityCommSqInfinitySquare_isPullback、strictCoherentCone_isLimit_iff_of_transformation、fractionKanQuotientDiagram_classificationIso、weakQuotientCosliceComparison、weakQuotientCosliceUnit_identity。
- weakSpanKanMappingComparison_value_equivalence_iff、weakIdentityKanMappingComparisonUnitIso、leftStraighteningCandidate_classificationIso_pointHom、leftCocartesianKanClassificationIso_pointHom。
- dgKPiComparison、dgKPiComparison_naturality、dgKPiMap_surjective_iff、dgKNativeSBoundaryPiEquiv_naturality、dgKNativePiMap_bijective_iff_sBoundary、dgRelativeVerdierSBoundaryFixedKSquareIso、dgRelativeKPositiveSquare_isPullback_iff、spectrumFiberSquare_evaluation_isPullback、spectrumEdge_isInvertible_of_positive_evaluation、dgRelativeK_isPullback_iff_sBoundary、stableBoundaryQuotientKanIso、verdierMultiBoundaryForget_isPullback_iff、spectrumEdge_isInvertible_of_positive_spaceEvaluation、dgRelativeK_isPullback_iff_multiRealization。
- dgKInputK_preservesRelativeZero、dgRelativeK_zero_corner、dgRelativeKZeroTriangle、dgRelativeFiberVertexComparison、dgRelativeK_isPullback_of_fiberComparison_pi_nonnegative。
- scaffoldNerveRepresentationIso_pointHom、scaffoldStraighteningRepresentationIso_pre、
  scaffoldPointedReconstruction、scaffoldPointedReconstruction_pointHom。
- scaffoldStraighteningGlobalChart_original_pointHom、firstVertexSectionFiberPoint_val、
  scaffoldPointedReconstruction_coefficient_pointHom。
- scaffoldBaseChangeCoefficientIso_pointHom、scaffoldBaseChangeCoefficientIso_heq_diagramValue、
  straighteningBaseChangeLeftChart_eq_firstVertex、straighteningBaseChangeRightChart_eq_firstVertex。
- baseChangeImageSectionFiberPoint_eq、vertexFiberZeroSection_firstVertex、
  scaffoldVertexBaseChangeIso_eq_diagramValue、scaffoldPointedReconstruction_baseChange_pointHom。
- scaffoldCocartesianBaseChangeClassificationIso_pointHom、coslicePointFamilyAt_recoveryIso、
  scaffoldCoslicePointExtension_reconstructionIso、scaffoldCoslicePointExtension_isPrecompositionEquivalence。
- weakIdentityNativeComparisonImage_scaffold_pointHom、weakCosliceComposite_scaffold_relativeIso、
  weakCosliceComposite_scaffold_functorIso、weakCosliceComposite_isPrecompositionEquivalence。
- verdierKZeroMap_surjective、verdierKZeroCofinalityObstruction_subsingleton、dgNuKZeroMap_surjective_of_verdier。
- dgKPiZeroMap_surjective_of_verdier、dgKBFHomotopyFiber_negative_subsingleton_of_verdier、
  dgKInputFiberSquare、dgRelativePiZeroMap_surjective、dgRelativeFiberSquare_negative_subsingleton。
- weakCosliceComparisonFiber_isEssentiallySurjective、weakSpanKanMappingComparison_value_isEssentiallySurjective、
  weakQuotientMappingComparison_isIso_of_fraction_fullyFaithful。
- relabelEnrichedObjects_uncurry、coreSingleSimplicialIso_diagonal_hom、coreSingleRealizationFamily_coordinates、quotientSKernelNullCylinder_coreRealization、stableCoreSingleKanFamily_coordinates、quotientSKernelNullCylinder_exInfinity、quotientSKernelNullCylinder_coreKan、verdierNullContractionCoreKanEvaluation_original_heq。
- relativeSKernelContractionCylinder、relativeSKernelDiagonalContraction、quotientSKernelNullHomotopy、quotientSKernelContractionImage_fullS、quotientSKernelNullNatTrans_app、quotientSKernelNullNatTrans_diagonal、stableMultiCoreFamilyCylinder_diagonal、quotientSKernelNullCylinder_native、verdierNullContractionComparison、verdierNullContractionFamily_original_heq。
- relativeSectionBaseChangeComponentIso_pointHom、relativeSectionBaseChangeComponentIso_heq_transportMap、
  leftStraighteningSectionJointDiagram_baseChangeIso_pre、leftStraighteningSectionJointDiagram_baseChangeIso_vertex。
- fiberGroup_lowerBound_iff_projection_surjective、connectiveFiber_iff_projection_piZero_surjective、
  fiberCofinalityObstructionEquiv、piZeroCofinalityObstructionEquiv_mk。
### 依存と提供
- 読み取り専用：KST/SConstruction、KST/LocalizingInvariants、KST/Spectra、InfinityCategories/Derived。
- K-S• の固定 K-1/K-2 は L1 §6：加法性、MultiRealizationFunctorIso の正反復、RelativeCofiberLeftFiber、
  RelativeFiberEquivalence と Quillen A。任意 W への制限・底変換・元の射影の照合は K-F が証明する。
- 相対 (d) の固定三点は K-S• の DGKFixedInterface・DGKFixedSConstruction を読み取り専用で使う。固定 ν・K の頂点・辺、厳密 dg の K₀ 自然比較・負次数消滅は提供済み。
- 商・分数・局所化は Sp 正本。一般分数比較の充満忠実性は Sp 正本から供給され、元の商上比較へ代入済み。厚い β3 列の実核接続は依頼済み。有限線型図式の局所化の正確な依頼型は冒頭（依頼中継済み・実供給待ち）。
- Sp の IsStable は使わない。実 fiber 列・整数長完全列・π 同値検出を使う。提供先は K-7 と K-基盤 2。
### K-B-S：Sp-6 s4 への空間値全族単位（供給完了）
- 元の `markedSpanFamily` と同じ `weakSpanKanQuotientDiagram` を保持する。一般 Verdier 分数比較の充満忠実性は Sp 正本が消費・公開し、K-B は元の商上比較の可逆性へ代入済み。K-6 c5 の商実現比較自体は未完。

| 条件 | 同じ実全族に対する公開名 |
| --- | --- |
| 実全族写像 | `weakSpanKanQuotientFamilyMap`：元の marked span 全族から同じ商図式の小さい unstraightening への実射。 |
| 底 q の厳密保持 | `weakSpanKanQuotientFamilyMap_projection`。 |
| 元の各固定 fiber の実制限 | `weakSpanKanQuotientFamilyFixedFiber`・`weakSpanKanQuotientFamilyFixedFiber_ι`：包含後は元の固定 span 全族包含≫同じ実全族写像に厳密一致。 |
| 同じ全 fiber 単位の回収 | `weakSpanKanQuotientFamilyFixedFiber_recovery`：全ての元の終点 y で、元の固定 span 全体の Kan 置換単位を全関手同型で回収する。指定正規化は `weakSpanKanQuotientZeroValueComparison`、同じ射の同値性は `weakSpanKanQuotientZeroValueComparison_isQCatEquivalence`。 |
| 既存指定恒等点 | `weakSpanKanQuotientFamilyFixedFiber_identityIso`：元の `weakIdentityFixedSpan` の実像と既存 `weakIdentityQuotientFiberPoint` を同じ q(x) fiber 内で比較。補助点で代用しない。 |

- Ind-S (5) の正本 `CocartesianKanUnstraighteningUnit`・`CocartesianKanUnstraighteningUnitPoints` を読み取り専用で消費。同じ元の span 射影の単体圏引き戻し、`strictKanCompletion`、元の単位へ代入し、同じ存在証拠から実単位・厳密な底・全 fiber 回収を取り出す。`weakSpanKanUnstraighteningUnit_fixedFiberIso` は元の固定 span 座標で既存の全単位へ戻す。
- 相対初頂点降下は F1 正本 `relativeFunctorPre_isQCatEquivalence_of_firstVertexLocalization` を消費する。`weakSpanKanQuotientFamilyMapRestrictionIso` は同じ元の実単位を相対関手空間内で回収し、底を忘れた絶対同型で代用しない。追加の相対同値性や単位存在の入力は不要。
- `WeakSpanFixedSimplexCollapse` は元の固定 span の全単体の同時比較 prism と、元の span 座標・底の全時刻固定・両端の厳密回収を保持する。`weakSpanKanQuotientFamilyFixedFiberIso` は同じ商 fiber 内の相対比較と prism を元の初頂点局所化で戻す。
- `WeakSpanKanQuotientValueEdge`・`WeakSpanKanQuotientValueCancellation` は元の実 transport 辺と指定値比較辺を保持し、指定成分の逆関係を実三角形の Kan ホモトピーへ戻す。`weakSpanKanQuotientSimplexFiberValueRecovery` は同じ全 fiber 比較を元の小さい宇宙で正規化し、`weakSpanKanQuotientSimplexUnitFiber_recovery` は同じ実単位の商像から元の Kan 単位を回収する。
- `WeakSpanZeroSimplexFiber`・`WeakSpanKanQuotientZeroUnit` は同じ零単体の実 fiber 包含を元の全族持ち上げへ全単体で厳密照合する。`WeakIdentityQuotientValueCoordinates`・`WeakIdentityQuotientZeroValue` は元の恒等点の既存値比較と同じ零単体比較を全関手同型で照合し、同じ指定値比較の充満忠実性で実 fiber 内の恒等点比較を反映する。
- 既存の絶対降下・底厳密化と条件付き全族利用側は保持する。新しい供給は元の `IsVerdierSequence i q` の下で、単位や比較の存在入力を追加せず構成したもの。I・P・懸垂供給境界には変更なし。空間値に限定し、Cat∞ 値分類や一般局所化・商 API は追加しない。

### 採用済み設計：c4 の上側輸送で指定全長 Hom を保持する
- 既存の非指定 `zeroMiddleFullSKanTetrahedron` と条件付きの `VerdierFullSMovingSquarePrism` は保持する。三面の充填条件だけから未指定欠面の全 native Hom 回収を推論しない。
- Ind-S (9)・(9b) は実供給を消費済み。指定二短辺・合成端・全 native Hom を保持する実 canonical 族と、同じ元の三面を固定した実因子分解族を使う。正規化前後は同じ固定ホーン空間内の可逆比較で結び、厳密切断は使わない。
- `VerdierMovingCanonicalSquareIso` は同じ読出しの正規化下側と動く全 S• 上側を全共有対角で貼り、全四頂点の可逆性・両端全関手同型を追加仮定なしで供給する。`VerdierNativeControlledSquareIso` は同じ実 (9b) 欠面と元の下側を保ち、対角固定四角柱で元の指定 Verdier 四角形へ戻す。
- `VerdierMovingCanonicalSquareComparison` は四つの指定有限端点の二胞体同定に条件付きで、両実四角柱を同じ元の商核まで接続する。四端点の二面・全 native Hom はすべて照合済み。S-1 (a) の消費後は `verdierCanonicalKernelSquareIso` が四端点条件なしで同じ実比較を供給する。c5 の商実現比較は未完。

### 未コミット
- 固定三面からの上側全境界回収と、同じ実列の第一行比較から固定 K 構造辺への接続を両集約へ接続済み。両専用監査成功。所有 Lean の未コミットなし。
### 既知の問題
- 一般分数比較の同値性と元の商上比較の可逆性は接続済み。有限線型図式の局所化、span 普遍性、商実現比較、厚い β3 列の Perf 核照合、相対連結版 K-6 は未完。
- 現在の条件付き fiber 同型や一般の群判定を、具体的 K の局所化性の証明とは数えない。
- D-9 の実小核と Sp-6 の固定零化構成子は K-B に接続済み。同じ実零角の Perf 零性は K-B で証明済み。固定 ν 上の Verdier 証拠と Perf 完備化・P 照合は別の条件。native Verdier 列だけから連結 K の Sp fiber 性を結論しない。
### 次の一手
- c4 は完了。c5 の実供給を `Relative.SingleRelativeComparison.ofCanonicalFirstRowSimplices` へ代入する。
- c5：Sp 正本の有限線型図式の局所化を元の正段商比較へ代入し、同じ実商実現・連結 fibration へ接続する。分数比較の充満忠実性は供給済み。同種 API を新設しない。
- K-7：D-8 の実 I・P・Z と同じ cone の零性を消費済み。共終性・一回の未完備 S• fibration と全 native 入力作用の残る境界を L10 の同じ実 BF 列へ接続する。K-B2 向け共通化は B・P のみの `closedStableFlagPostPullback` を供給済み。

### K-6 c の三段目（v3）
- [x] c1 `relabelEnrichedObjects` の全 Hom 座標読み替え。
- [x] c2 `coreSingleSimplicialIso` の対角と実現同型の逆射の照合。
- [x] c3 商核零化円柱の元の core S 実現対象への輸送。
- [x] c4 Ex∞ 上で指定二胞体を保つ全四角形比較（S-1 (a) を実代入、d のみの FunctorIso）。
- [ ] c5 商実現比較と無条件の連結版への接続。

## 規約
- 配置 `SerrePositivity/KST/Fibration/`、集約 `KST/Fibration.lean`、監査 `scripts/audit_kst_fibration.lean`。
- foundations.md §8 と k-theory-kst-route.md §13（決定 15・16）。H⁰ の Verdier 普遍性で写像空間の比較を代用しない。Sp の IsStable は使わない。
- 原典：Waldhausen 1985 §1.6、BGT 2013 §7〜9、Barwick 2016。

## 冪等完備化・K-7 への入力境界（工程 e）

原典：[BGT §9.1、定義 9.1・9.6](https://arxiv.org/pdf/1001.2282#page=57)。
FκA=(Indω A)κ と ΣκA=FκA/A の列、K(FκA) の消滅、完全列・κ-filtered 余極限の保存を使い、
非連結 K は colimₙ ΩⁿK(ΣκⁿA) で構成する。これらの構成・消滅・余極限の証明は K-7 側。

| 入力 | 検証した正本と K-F の境界 |
| --- | --- |
| 完備化前の商 | Sp の IsVerdierSequence・VerdierSequence。K-F の quotientSFibrationFiberIsoOfComparison は商実現比較の可逆性が未証明の条件付き界面。 |
| 完備化 | N の IsIdempotentCompletion は充満忠実性と retract 条件を保持。IsIdempotentCompletion.pre_isQCatEquivalence は全関手 ∞ 圏の普遍性。H⁰ では代用しない。 |
| 安定・完全性 | N の IsIdempotentCompletion.isStable・isExactFunctor、idem_isStable・idemYoneda_isExactFunctor を使う。元の Idem C は宇宙 u+1、idemYoneda の始域は ulift C。 |
| 零次 cofinality | 厳密 dg 入力の ν と K の指定比較へ接続する。完備化という条件だけでは π₀ 全射性を入力せず、実 K 比較で検査する。K-F の piZeroCofinalityObstructionEquiv は中央 π₋₁=0 の下で、元の射影の余核を左 fiber の π₋₁ と同定する。 |
| K-7 への提供 | 指定射影を保つ b・d と、`dgKappaCanonicalSuspensionStructureMap_nonnegative`。同じ I・Z と c5 のみから元の固定 K 隣接射の非負次数 π 同型。`_eq` で既存反復射へ厳密照合。全入力作用・逐次余極限・非連結化後の局所化性は K-B3 所有。 |

### Ind-S (9)：実供給済みの正規化全族再構成
- `controlledTriangleNormalizedFamilySupply`（f206fbbb1）を `ZeroMiddleComparisonSupply` で消費済み。任意 K の指定二短辺・合成端・全族可逆比較・全 native Hom 回収・正規化後の全対角を保持する。[採用仕様の全型](archive/L3-ind9-supply-specification.md)。
- `controlledTriangleCoherentEncoder` の実像を上下で使い、同じ実読出しの全対角を厳密に貼る。元 t とは同じ固定ホーン空間内の可逆比較で戻す。厳密切断・元 t 自身の厳密全対角回収は撤回済み。
- (9b) の実 `controlledFactorizationTetraFamily` は元の三面・全 native Hom を保持し、固定三面 fiber 内で既存充填との比較を持つ。制御された同じ実充填を使い、任意四面の可填性は要求しない。
- 二短辺と全 native Hom による有限二胞体外延性は S-1 (a) から消費済み。`VerdierMovingCanonicalFiniteExt` が archive の利用側を実代入し、主経路に存在仮定はない。

### 採用経路：実商と Perf 完備化の K 比較を分ける（ユーザー採用）
- D-9 の `resolvedDGQuotientFlatKernel_isStableVerdierSequence` は完備化前の native 実商への列。固定 ν の `IsVerdierSequence` は Perf 完備化後の射に通常の `IsLocalization` を要求する。今回の実核・P・Morita 照合は、この追加認証を含まない。
- 採用：K-6 の完備化前の連結 fibration と、同じ実商の元の dg Yoneda 完備化の実 K 比較を分ける。K-7 の同じ cone について、後者の正次数 π 同型・零次 π 単射と構成済みの K 零性を使い、固定 K への実 fiber 比較の非負次数 π 同型を得る。K₀ 全射性・連結 K の Sp 引き戻し性は要求しない。
- 固定 S・ν・K と同じ I・採用済み供給境界は不変。既存の条件付き相対屋根と Sp fiber 定理も保持する。完備化前の商の局所化は D・Sp、K の cofinality は K-S• 正本とし、K-B に同種 API を重ねない。
- `DGKappaNativeKernelThick` は同じ実核の冪等完備性で D 正本の thick 核の retract 表示を戻し、完備化前の商の零化対象が元の実小核の本質像であることを証明する。`DGKappaNativeVerdier` は同じ包含・商辺を保つ Sp の完備化前の `IsVerdierSequence`・全四角形提示を供給する。固定 ν の完備化後の認証は使わない。`DGKappaRawSuspensionCompletion` は始域を移さない同じ実商の元の dg Yoneda を完備化として認証し、実 Perf 評価と SOA 比較で固定 K への実 BF 比較を保持する。正次数 π 同型・零次単射と一回 loop の非負次数同型は `CanonicalSuspensionInput` が実共終性で放電済み。`DGKappaNativeKernelKComparison` は元の評価と同じ実供給 P による実核同値から、固定 K の始点を戻す。`DGKappaNativeFibration` はこの実列を元の相対 S• fiber 比較へ代入し、包含射影を厳密回収する。実商の fiber・Ex∞ 核四角形への接続は、既存の正段商比較 `hstage` に条件付きで、`DGKappaNativeSquareComparison` は同じ提示を動く共有対角の四角柱へ代入し、指定上側全族・全対角条件・縦辺可逆性と同じ正段比較に条件付きで、元の全 S• 四角形へ引き戻し性を移す。c4 の全二胞体比較は `verdierCanonicalKernelSquareIso` で無条件化済み。c5 の正段商比較は未完。
- 共終性は K-S• の `Cofinality.kSpectrumMap_cofinality` を消費済み。旧 `hcofinal` 引数付き API は保持し、同じ指定完備化射へ実供給を代入する。K₀ 全射性は要求しない。
- `CanonicalSuspensionInput` は主 Fibration 集約から分離した Relative.All に集約する。主集約の NonConnective 非依存と、共終性供給側からの循環回避を保つ。

### 採用済み：同じ未完備実列だけの有限 BF 四角形比較
- `kSpectrumMap` の射ごとの供給だけから、元の native 二胞体を持つ実 BF 四角形は回収しない。一般の BF 高次面整流は L1 のユーザー指示で中断済み。固定 `dgKInputK` を代入すると商が Perf 完備化後に戻る。
- ユーザー採用の有限 BF 比較は K-S•-S3 から実供給済み。同じ D-9 未完備実列の元二胞体を、新 BF 四対象・四辺上の実 Φ へ送り、各正段の全 S• 四角形比較と旧 K への指定整数群同型との可換性を保持する。`DGKappaSuppliedBF*` の主利用側は供給を直接消費し、hBF の存在引数を取らない。一般 StableInfinity の K 関手化は再開しない。
- [旧四対象固定型と範囲](archive/L3-raw-bf-square-proposal.md) の `DGKappaNativeBFBoundaryInput`・`DGKappaNativeBFSquare`・旧 hBF に条件付きの fiber・loop・固定 K 構造射の利用側は保持する。ただし実 S3 の BF 対象は旧四対象と厳密には等しくなく、旧 hBF の存在は主張しない。実供給側の構造辺から固定 K への戻しは末尾の二頂点比較の設計補足で扱う。c4 は完了。c5 と K-7 c5・d3 の印は未完。

### c5 の有限第一行比較の消費
- `RelativeFirstRow` は元の相対 gapped S_n を同じ商関手の相対第一行の厳密な逆像と認証し、第一行制限を底変換した trivial Kan fibration を構成する。`RelativeFirstRowQuotient` は元の商比較との厳密可換性と局所化可逆性の必要十分条件を保持する。
- `RelativeFirstRowRealization` は正段の残入力を `∀ n, IsIso (AnodyneHomotopy.anodyneQ.map (relativeFirstRowQuotient q (n+1)))` に移し、同じ実現・Ex∞ 射・商核四角形へ条件付きで接続する。第一行の標準単体座標同型は同じ商後合成に厳密自然。同じ D-9 実列の `dgKappaNativeFullSSquare_isPullback_of_firstRows` と `dgKappaNativeBFFixedStructure_nonnegative_of_firstRows` まで接続。一般局所化から core 比較を推論しない。有限図式の Verdier 分数・core 比較の依頼は依頼中継済み・実供給待ち。
- `RelativeFirstRowSimplex` は同じ相対部分複体の標準単体座標への厳密な両側逆を供給する。`RelativeFirstRowSimplexQuotient` は元の商比較との厳密四角形を保持し、正段条件を `∀ n, IsIso (AnodyneHomotopy.anodyneQ.map (relativeFirstRowSimplexQuotient q n))` と同値にする。この型から元の商実現への条件付き利用側まで接続済み。先の第一行型と同値な供給型。Sp へは初回報告の正確な型をユーザー経由で送る。新たな局所化存在入力は追加しない。

### Ind-S (9b)：同じ三面を保つ制御三単体の実構成（採用（06:29））
- ユーザー採用（06:29）。(9) と (9b) を一括で Ind-S に発注済み。元の二胞体・二つの厳密合成面・同じ長 Hom を保つ因子分解三単体族を使い、構成後に同じ固定三面 fiber 内で既存充填と比較する。[型・供給範囲](archive/L3-controlled-factorization-tetra-proposal.md)。(9b) は 77a33b4c9 の controlledFactorizationTetraFamily を ZeroMiddleNativeFactorization で代入済み。(9) も f206fbbb1 の実供給を代入済み。旧条件付き入口は保持する。全族 Hom 回収の既存要求は保持。今後の提案・依頼は要約と型のファイル・行を必ずユーザー経由で中継する。

### 採用済み供給命題の利用側

| 明示定理引数 | 型の正本（SerrePositivity/ 以下） | 供給元・回収内容 |
|---|---|---|
| `h9 : zeroMiddleControlledTriangleComparisonSupply` | KST/Fibration/ZeroMiddleReconstructionSupply.lean:105 | Ind-S (9)：f206fbbb1 の実供給を ZeroMiddleComparisonSupply で消費済み。指定二短辺・合成端・全族可逆比較・native 回収・正規化対角を保持。旧厳密切断版の供給は要求しない |
| `h9b : zeroMiddleFactorizationTetraSupply` | KST/Fibration/ZeroMiddleReconstructionSupply.lean:97 | Ind-S (9b)：実供給済み（77a33b4c9）。ZeroMiddleNativeFactorization の zeroMiddleFactorizationTetraSupply_of_indS9b を代入 |

- (9)・(9b) は実供給を代入済み。旧明示引数の入口は条件付きのまま保持する。`ZeroMiddleFullSReconstruction`・`ZeroMiddleReconstructedFamily` は元の core 始域・全 S• 中間頂点と同じ短辺への再構成・実ホーン回収・同じ実入力への読戻しを保持する。`ZeroMiddleFactorizationTetra`・`ZeroMiddleFactorizationComparison` は同じ実因子分解族の三面・長 Hom を回収し、ホーン全体の回収後に既存充填との固定三面 fiber 内比較へ渡す。動く共有対角の貼り合わせと K-6 c4 は実供給で完了。K-6 c5、K-7 c5・d3 の無条件化は未完。

### 採用済み仕様補足：全族の共有対角の厳密回収
- ユーザー採用、Ind-S (9) へ中継済み。各 K 頂点の全 native Hom 回収から全時刻の式を推論せず、同じ encode/read の normalize(t)=encode(longHom(t)) に対する直接 path 評価の全族厳密回収式と、元 t との固定ホーン内の可逆比較を持つ強化命題を明示引数に取る。元 t 自身への厳密式は要求しない。標準区間像への移送は既存の F2.Presentable.functorIsoTensor を消費して diagonalIso まで構成し、uncurry の追加供給は不要とユーザー経由で中継済み（[依存箇所・型](archive/L3-uncurry-comparison-request.md:24)）。旧 `ZeroMiddleReconstructedDiagonal` の厳密対角定理と `ZeroMiddleNormalizedFamily` の厳密読出し保存・冪等性は旧強仕様に条件付きのまま保持し、実供給を要求しない。新仕様では全族可逆比較の直接 path 評価に沿って移送する。`VerdierLowerNormalizedReconstruction` は比較条項自体を使わない形へ一般化し、`ZeroMiddleFullSComparisonReconstruction` は採用済み仕様を同じ実座標へ代入する。`ZeroMiddleComparisonSupply` は f206fbbb1 を消費し、`VerdierLowerSuppliedNormalization` から供給命題引数を除去した。`ZeroMiddleSuppliedReconstruction` は同じ実データから上側正規化族・厳密ホーン・正規化対角と元入力への直接 path 全族同型を構成する。[型・範囲・採否の影響](archive/L3-whole-diagonal-recovery-proposal.md)。
- VerdierLowerReconstructionBoundary は元の実下側変形の二短辺と固定ホーン族の実入力点を厳密回収する。VerdierLowerNormalizedReconstruction は (9) に条件付きで、同じ実下側族との全関手同型・元の二短辺・正規化側の全対角・各入力点の全 native Hom 読出しと全時刻の実合成端を接続する。合成端は元の二つの実 Kan 射の厳密合成の定値族と一致する。
- ZeroMiddleControlledLongFamily は Ind の 218e5b449 を消費し、指定長 Hom 入力から全ホーン・各入力点の全 native Hom を保つ実上側族を (9) の仮定なしで構成する。全時刻対角の厳密回収とは区別する。
- VerdierNativeCompositeEdge は元の全長 Hom 比較の実合成端成分を core 制限と宇宙持ち上げへ送り、上側・下側の同じ実合成端間の可逆辺を保持する。VerdierOriginalCompositeNativeEdge は元の比較を指定 Verdier 両端へ輸送し、下側始端を実包含・実商の合成、上側終端を指定左辺・上辺の合成の元の core S• 作用へ厳密回収する。
- 二短辺と全 native 長 Hom の HEq による二単体外延性は S-1 (a) の実証明を消費済み。本体へ新たな存在仮定は追加していない。

- VerdierNativeLongHomShift は指定両端の長 Hom 全族と元の実合成端比較の定数族を全関手 Kan 複体で合成し、同じ合成二単体を保持する。
- native path 座標へ戻した同じ族は、直接 path の全パラメータを厳密保存し上側の元の実合成端を回収する。
- VerdierNativeCompositeFunctoriality は両合成端を元の二つの core Kan 射の厳密合成へ照合する。
- VerdierLowerLongHomTransport は実下側読出しを同じ指定両端へ輸送し、元の実包含・商の合成端を全入力で回収する。
- (9) に条件付きの同じ下側読出しから、直接端を保つ上側合成端入力まで代入済み。
- VerdierLowerNativeReadout は 840438555 の実読出しを代入し、上側入力の (9) 仮定を除去した。
- VerdierUpperLongHomTransport・VerdierReadoutUpperFamily は同じ入力を元の全 S• 上側座標へ戻し、全ホーンと各入力の全 native Hom を保持する実上側族を仮定なしで構成する。
- VerdierNativeDiagonalCoordinates は同じ上下座標と指定両端の全対角族を照合する。
- VerdierNormalizedSharedDiagonal は (9) に条件付きで、元の実下側との全関手同型と両全ホーンを保持し、正規化した上下族の全時刻対角の厳密一致を構成する。
- VerdierOriginalNativeHomFamily は元の上下全 path 比較を指定両端へ送り、直接端上の恒等比較・元の合成端成分を保持する。
- 合成端辺は同じ全族比較の成分として構成し、実一単体の回収式を接続した。
- VerdierOriginalNativeHomSquare は元の上下全 path・直接端の恒等辺・実合成端辺を四辺に持つ実四角形を回収する。
- VerdierOriginalNativeComposition は同じ実三辺を持つ合成二単体を仮定なしで構成する。
- VerdierLowerNativeReadoutEndpoints・Coordinates は同じ実読出しの始端を元の下側全 path、終端を実包含・商の合成端の定値全 path へ戻す。
- Homotopy は同じ L の uncurry と合成 path 上の全時刻定値性を厳密保持し、(9) の正規化読出しも同じ入力として渡す。
- VerdierOriginalFullSHomFamily は指定両端で全 S• 比較を構成し、その同じ全円柱を core へ制限する。
- 同じ円柱の直接端での全時刻恒等性と、動く全 S• 合成端族の core 制限の厳密一致まで接続した。
- FixedRestrictionFunctorComponent・VerdierFullSComparisonComponents は同じ指定成分を実恒等辺へ戻す。
- VerdierReadoutBoundaryTriangles は直接端で読出し成分、合成端で同じ全 S• 比較成分を合成辺として保持する実二単体を構成する。
- CoherentTriangleIntervalEndpoints は所有 path の二端点座標、VerdierOriginalFullSCompositeVertices は同じ動く短辺の両端の元の実完全射を回収する。
- VerdierReadoutBoundaryDiagram は同じ二つの実二単体を区間境界上へ貼り、三面を元の実比較成分へ全次数で回収する。
- VerdierReadoutPathBoundary は同じ native path 境界と二端点の全族厳密回収を構成する。
- VerdierReadoutRelativeComposition は同じ読出しと全 S• 比較を、同じ二端点の実境界二単体を固定して合成する。
- VerdierReadoutCompositionBoundary は同じ合成の直接端を元の読出し、全 path 端を同じ全 S• 比較成分へ全族で厳密回収する。
- ZeroMiddleCanonicalEncoder は公開実 encoder の全対角・native Hom 回収を消費し、VerdierCanonicalSharedDiagonal は供給命題引数・厳密切断なしで全共有対角を構成する。
- 動く上側短辺・有限端点と元の指定上下二胞体への照合は続行中。

### K-S•-S3 の実供給と採用済み二頂点比較
- 実供給 `dgKappaNativeCoherentBFSquare` は新 BF 四対象を持ち、旧 K とは指定整数群同型を介して四辺の π 作用が可換。`DGKappaSuppliedBFSquare` は元の全 S• 比較と旧 K-cof の群作用を消費し、`DGKappaSuppliedBFZero`・`DGKappaSuppliedBFFiberComparison`・`DGKappaSuppliedBFOneStage` は hBF の存在仮定なしで零角・同じ実 fiber 比較・非負次数 π 比較へ接続する。`DGKappaSuppliedBFConeZero`・`DGKappaSuppliedBFConnectiveStructure` は同じ cone の零性から新 BF 上の実構造辺を作る。旧四対象を固定した hBF の条件付き定理は保持する。
- 二頂点比較は K-S• の 8b9bb13d2 で実供給済み。dgKappaNativeBFKernelQuotientVertexIso を代入し、DGKappaSuppliedBFFixedStructure で旧実核・実商の loop を経る固定 K 構造辺と非負次数 π 比較へ接続した。DGSuspensionSuppliedBFSequence は共終性・一回の S• fibration に条件付きで、二頂点比較の仮定なしに元の実余錐・連結比較・全整数末尾表示まで渡す。[型（28行）・範囲・採否の影響](archive/L3-supplied-bf-vertex-comparison.md)。二頂点比較は実スペクトル比較から構成し、整数群の抽象同型だけから Sp 同型を推論しない。

- `VerdierMovingUpper*`・`VerdierReadoutMovingLongInput`・`VerdierMovingSharedDiagonal` は同じ実相対合成を動く第二短辺の長 Hom fiber へ渡し、元の下側との可逆比較と全共有対角を保持する。
- 追加供給命題引数・厳密切断なし。
- `VerdierMovingUpperNativeEndpoints`・`VerdierMovingUpperShortEndpoints` は同じ実入力と二短辺の両端を回収し、`verdierMovingSharedDiagonal_nativeEndpoints_exists` は同じ N・F の全ホーン・全共有対角・元の下側との可逆比較と両端全 native Hom を同時に供給する。
- 厳密切断は不要。
- `VerdierMovingUpperShortFaces`・`VerdierMovingUpperBoundaryEdges` は全二短辺と両端の元の coherent 辺を回収する。
- `ZeroMiddleNativeUpperBoundary` は同じ実 (9b) 充填の欠面から元の二短辺・全 native Hom を回収する。
- `VerdierMovingUpperFactorizationCoordinates`・`VerdierUpperNativeOriginalCoordinates`・`VerdierMovingUpperVertices` は同じ対象座標と元の全 Hom を照合する。
- `VerdierMovingUpperFirstComparison`・`VerdierMovingUpperLastTriangle`・`VerdierMovingUpperLastComparison` は両端で二面の厳密等式と全 native Hom の HEq を供給する。
- 始端は同じ実 (9b) 欠面、終端は同じ二実射の標準合成である。
- 指定有限二胞体の厳密同定は `VerdierMovingCanonicalFiniteExt` で S-1 (a) を代入済み。元の同じ実 (9b) 三面内の比較を使う。
- `VerdierLowerCanonicalFamily`・`VerdierLowerCanonicalReadout` は同じ実読出しの全 native Hom・全対角・固定ホーン内の可逆比較を同時に保持する。
- `VerdierMovingCanonicalSharedDiagonal`・`VerdierNormalizedSquareFamily`・`VerdierMovingCanonicalSquare` は同じ読出しの上下実族を全共有対角で四角柱へ貼り、下側全 native Hom と元の族への可逆比較を保持する。
- `VerdierLowerCanonicalShortFaces`・`VerdierLowerCanonicalVerticalEdges` は同じ下側の二短辺・全 native Hom・三頂点の元の縦辺を回収し、追加仮定なしで下側の両端関手同型を供給する。
- `VerdierMovingUpperVertexColumns`・`VerdierMovingUpperVerticalEdges` は動く第二短辺を保ったまま三頂点の恒等縦辺を回収する。
- `VerdierMovingCanonicalSquareIso` は同じ全四角柱の四頂点の可逆性と両端全関手同型を追加仮定なしで供給する。
- `VerdierMovingUpperKernelTriangle` は標準終端を実商核上側へ厳密回収する。
- `VerdierNativeControlledUpperPrism`・`VerdierNativeControlledSquare*` は同じ実 (9b) 欠面から元の指定上側への対角固定可逆三角柱を、元の下側を固定して全四角柱・全関手同型へ貼る。
- `VerdierMovingCanonicalKernelEndpoint`・`VerdierMovingCanonicalSquareComparison` は四つの指定有限端点照合に条件付きで、同じ正規化四角柱を元の Verdier・実商核四角形の全関手同型へ接続し、元の商の各正段比較から引き戻し性を移す。
- `VerdierLowerCanonicalFiniteFaces` は下側両端についても元の指定二胞体への二面の厳密等号と全 native Hom の HEq を供給する。
- 四端点の全三条件は揃っており、[外延性の利用側](archive/L3-native-triangle-ext-consumer.md:47) は型検査済み。
- F1 外延性の実供給による四端点同定は完了。商の正段比較は未放電。
- K-B2 向け共通化：`FiniteFlagComparisonInduction` を既存 q 版の帰納段へ代入した。`ClosedFlagCofiberCoordinates`・`ClosedFlagFiniteComparison`・`ClosedFlagFiniteRecursion` は B・P のみの共通補完と全座標自然性・厳密分解を保持する。`StableTrivialPullbackSection`・`ClosedTailMultiStep`・`ClosedTailCanonicalComponents` は同じ全旗の先行面と最後の cofiber 比較を K-B2 の相対加法性へ接続し、全正反復の局所化同型を供給する。`ClosedFlagOneEquivalence`・`ClosedFlagOneComparison`・`ClosedFlagFiniteEquivalence` は同じ一辺加法性を共通帰納へ接続し、全正長・全正反復の元の有限積比較の局所化同型を供給する。`ClosedFlagFiniteAllLengths` は公開済み K-B2 の零長同型を代入し、零長を含む全長の局所化同型を供給する。`ClosedKernelCoefficient`・`ClosedFlagCofiberPostcomparison` は元の P 自身の包含係数同型と全関手比較を保持する。`ClosedKernelInitialPullback` は全長・全正反復の実初期評価引き戻しを供給する。`SimplicialInitialPullback` を既存 q 版と共有し、`ClosedFlagPostCartesian.closedStableFlagPost_homotopyPullback` と `closedStableFlagPostPullback` は元の単回 F・包含・全作用素の引き戻しを B・P のみから供給する。既存の K-B2 条件付き葉は保持し、新しい利用葉で代入する。

### c4 の全関手同型から c5・K-7 への受け渡し
- `NonConnective/DGKappaSuppliedBFFirstRowSimplices` は同じ実 D-9 列の全四角形 `FunctorIso` と元の商の標準単体比較を直接消費する。実商核の引き戻しを移し、同じ BF fiber の非負次数 π 同型と固定 K 構造射へ続ける。旧入口の両比較は明示定理引数。c4 は `verdierCanonicalKernelSquareIso` を実代入でき、`Relative.SingleRelativeComparison.ofCanonicalFirstRowSimplices` は c5 だけを残す。無条件の連結版は主張しない。c4 の正規化下側族を旧上側ホモトピーへ戻す追加要求はない。
