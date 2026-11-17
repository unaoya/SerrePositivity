# BS-W16 の報告（report-codex-w16.md） — 停止点 0〜3：E1〜E4（§1〜§11、2026-11-10〜11-11）

元の報告：[report-codex-w16.md](../../bhatt-scholze/reports/report-codex-w16.md)


`main` の 18350a5a7 を `math/bs-impl` に fast-forward した。以下は既存の宣言と型を読んだ段階の案。行数は共用補題を含む新規 Lean の概算で、型検査とビルドは実施していない。

`Interface/Theory.lean` の欄を基準とした。`Shared/BarrattEcclesTheory.lean` の `sorry` は欄の代入で 40 件。指示書の 41 件はモジュール docstring に出る語も数えた値。既存の `barrattEcclesCore` の 7 欄はそのまま再利用する。`strictToD` と `ofCdga` は drafts に既存宣言の合成が書かれており、それぞれ E1・E4 で本体に出せる。E4 表に列挙されていない余単体的 cdga の 5 欄も §4 で個別に点検した。

## 1. E1　D の係数制限と厳密複体

係数制限は、T 上で半自由な複体を S 上で半自由と扱えない。任意の環準同型 f に対し、まず台の複体を制限してから S 上の半自由分解へ送る。具体的な ∞ 関手と通常の導来圏での関手を結ぶところを E3 と共用する。

| 欄 | 既存宣言からの経路 | 足りない補題・規模 |
| --- | --- | --- |
| `strictToD` | `ComplexLimits.complexOrdinaryDerivedSource` を使う。元の鎖写像の像は `complexOrdinaryAmbient_edge`、擬同型の反転は `complexOrdinaryDerivedSource_map_weak`。 | 定義は数行。 |
| `strictToD_homologyIso` | `complexSemifreeResolutionAugmentationHomotopy` をホモトピー圏へ送り、`derivedInfinityHomologyComparison` と `complexHomotopyComparison_fac` を使って Hⁱ を取る。`complexOrdinaryDerivedSource_vertex_eq` で成分を解像の頂点に合わせる。 | 垂直辺を `complexSemifreeResolutionValueAugmentation` と照合する。成分の可逆性は `complexSemifreeResolutionValueAugmentation_quasiIso`。各鎖写像との自然性は同じ全 augmentation から取る。120–300 行。 |
| `restrictD` | `dgNerveRestrictScalarsIso` と `ScalarExtension.restrictionComplexDGFunctor` が候補。`restrictionComplexDGFunctor` の始域は移送した豊穣構造なので、まず `DGRestrictScalars` からその構造への Hom の比較を確認する。T 上の半自由部分圏から全複体へ移し、S 上で `complexSemifreeResolutionInfinity` を合成する。 | 移送した豊穣構造との dg 比較、閉零 nerve と通常の複体の制限との全関手比較。T 上の全 dg 複体から制限する形も用意すると E3 に使える。150–350 行。 |
| `restrictD_id` | 厳密な複体の制限の恒等比較と `complexSemifreeResolutionRetractIso` を合成する。 | 恒等比較を同じ dg 関手に照合してから nerve に送る。30–90 行。 |
| `restrictD_comp` | 二段の制限の中間に入る T 側の解像の augmentation を次の制限で送る。一段の制限との厳密な合成比較を挟み、最後の解像で擬同型を反転する。 | 制限は擬同型を保つこと、augmentation の全単体ホモトピーの後合成、全成分の可逆性。80–180 行。 |
| `restrictD_homologyIso` | 通常の導来圏に `derivedRestrictScalars`、`derivedRestrictScalarsFactors`、`derivedRestrictScalarsHomologyIso` がある。厳密な制限との比較を `derivedInfinityHomotopyEquivalence` に通し、`ModuleCat.restrictScalars` の台の加法群との比較を後合成する。 | 同じ `restrictD` のホモトピー圏での関手を通常の導来制限と同定する自然同型。別経路として dg augmentation と厳密複体のホモロジーの制限比較を直接合成できる。90–220 行。 |

先に `strictToD_homologyIso` を閉じておくと、係数の比較や H⁰ の忘却比較の検算に使える。E1 は共用込みで約 450–1,100 行。③ の G8・G9・G10・G14 を前提にしない。

## 2. E2　忘却、始対象、余積

| 欄 | 既存宣言からの経路 | 足りない補題・規模 |
| --- | --- | --- |
| `forget_conservative` | `cAlgVertexEquiv` で両端の cofibrant 代表を取り、`cofibrantAlgebraMappingSpacePiZeroEquiv`・`cofibrantAlgebraMappingSpacePiZeroEquiv_class` と DK 写像空間比較で、辺の類をその間の厳密射の類で表す。模型では `modelCategory_weakEquivalences` により底の擬同型が弱同値。`cAlgForgetDerived_sourceIso` と厳密複体の Hⁱ 比較で、忘却像の可逆性から全次数の擬同型を得る。`cAlgLocalizationSource_inverts` で戻す。 | cofibrant–fibrant 間の厳密射から局所化の Hom への全射を、既存 DK の類との整合付きで示す。模型構造を実際に入れ、π₀ 上の代表を取る。100–260 行。 |
| `discrete_initial` | `cAlgFreeForgetDerivedAdjunction` で D(S) の零から自由代数の始対象を得る。`Operad.freeAlgebraAdjunction` の厳密側では零複体の自由代数は arity 0 だけ。`discreteAlgebraFunctor` と `discreteCAlgUnderEmbedding` で構造射 `𝟙` の像へ移す。 | 自由代数の零での値の比較、または cofibrant な厳密始対象からの frame 写像空間が可縮である直接証明。E2 の他の欄に依存しない。80–200 行。 |
| `coprodWith` | 右因子 y の cofibrant 代表を固定。`Operad.AlgebraAllColimits` の通常の二項余積を cofibrant 対象に使う。二項余積は離散二点の図式圏から左 Quillen となることを確認し、弱同値の保存を得て `cAlgLocalizationPrecomposition_isQCatEquivalence` で降ろす。 | cofibrant 余積の閉性、固定右因子での弱同値保存と源での全関手比較。100–230 行。 |
| `coprodWith_cocone` | 上で使った二つの余積脚を `binaryPointDiagram` 上の指定余錐へ運ぶ。共通の fibrant 標的への mapping frame で、通常の余積の Hom の積比較を全単体で使う。 | model の余積余錐と native `IsColimitCone` の照合。安定圏用 `hasColimit_binaryPointDiagram` は CAlg に適用しない。150–350 行。**［一般∞］** |
| `coproduct_tensor` | `hopfDiagonal`・`hopf` と augmentation の余単位から代数のテンソルと二脚を作り、厳密余積からテンソルへの比較を構成する。D(S) 側は既存の `tensorWith`。自由代数では `freeAlgebraFunctor_forget` の Schur 形を使い、混合項の shuffle／制限比較を試す。 | 一般の cofibrant 代数で比較が擬同型になる証明が要る。自由代数から移すなら自由 bar の実現を忘却が計算すること、またはセル付加での比較を使う。底の K-flat 性と半自由分解でのテンソル比較も必要。固定 y に対して厳密な自然比較を作り、源での自然同型を局所化して初めて欄を埋める。400–1,000 行以上。 |
| `forget_preservesSifted` | `Operad.forget_createsSiftedColimitsOfShape`、`Operad.freeAlgebraForget_preservesSiftedColimits`、`Diagram.projectiveModelCategory` と `Diagram.forget` は通常の図式の部品。`cofibrantAlgebraFreeResolution` とその増大は自由 bar の候補。 | 欄は任意の小さい sifted **単体集合** I と元の指定余錐を扱う。図式を扱える模型へ直す比較、ホモトピー余極限の計算、忘却後の余錐との照合を要する。まず filtered と幾何学的実現を別々に検証し、一般の sifted への還元を実証できるか調べる。通常圏の保存、自由随伴、通常のモナド性だけからは出ない。600–1,600 行以上。**［一般∞］** |

E2 は保存的と始対象を先に検査する。余積・テンソル比較と sifted 保存は相互に依存させない。とくに自由 bar で余積比較を拡張する場合、先に幾何学的実現の保存だけを独立に示す。E2 の全欄は約 1,400–3,600 行以上。sifted の全形は③の G10 そのものではないが、一般の図式比較まで必要になれば別の基盤単位とする候補。

## 3. E3　代数の係数変更（M13）

`ScalarExtension.extension` と `restriction` の随伴 `ScalarExtension.adjunction`、拡大のモノイダル構造 `extensionMonoidal` と制限の `restrictionLaxMonoidal` が出発点。`Operad.restrictAlgebra` は**同じ係数環上の operad 射**に沿う制限なので、それだけで環の係数制限にはならない。`operad S` の拡大と `operad T` を arity ごとに比較し、置換・対称群作用・augmentation と両立させる。

| 欄 | 既存宣言からの経路 | 足りない補題・規模 |
| --- | --- | --- |
| `restrict` | 制限の lax monoidal 構造と Barratt–Eccles の係数比較で T 代数の底と作用を S に制限。`algebraCAlgSource` を後合成し、厳密制限が擬同型を保つことを使って cofibrant の局所化の源から降ろす。 | 係数を変えた arity の自然比較と代数の厳密制限。S 上で cofibrant と仮定しない。180–420 行。 |
| `baseChange` | `extensionMonoidal` で厳密拡大を構成し、S 上の cofibrant 代表に適用。制限が `modelCategory_fibrations` と `modelCategory_weakEquivalences` の双方を保てば拡大は左 Quillen。 | 作用の移送、左 Quillen 性、cofibrant 対象間の弱同値保存とその局所化。共用分を除き 100–250 行。 |
| `baseChange_adjunction` | 厳密な単位・余単位を源の置換と合わせ、局所化の全関手圏比較で降ろす。`cAlgForgetDerived_exists` と `cAlgLocalizationPrecomposition_isQCatEquivalence` が手本。 | 導来した両関手の同じ単位・余単位と三角等式、`QCatAdjunction` への橋。既存 `quillenCfDerivedAdjunctionWithComparisons_exists` は豊穣随伴と固定 pushout-product の入力付き。現模型でその入力を別途作らず使えるかは未確認。180–450 行。**［一般∞］** |
| `restrict_forget` | 厳密な制限の底は複体の厳密制限。E1 の源比較と `algebraCAlgSource_underlyingDerivedIso` を合成して局所化の源で揃える。 | 置換の augmentation の自然比較、全関手同型の降下。60–150 行。 |
| `baseChange_forget` | 厳密拡大の底は複体の拡大。`derivedInfinityBaseChange` は `semifreeBaseChangeDG` を使う。 | cofibrant 代数の底の K-flat 性または別の適切な解像比較。任意の f に対する同じ拡大の全関手比較。200–550 行。 |
| `restrict_id` | 厳密制限の恒等同型を同じ局所化の源上で取る。 | arity の恒等比較、全関手への降下。30–80 行。 |
| `restrict_comp` | 厳密制限の合成比較を使う。中間の cofibrant 置換があれば、その弱同値を制限し像で反転する。 | operad 作用との合成整合性と全関手比較。60–150 行。 |
| `discrete_restrict` | `restrictRingAlgebra`、`discreteAlgebraFunctor` と `discreteCAlgUnderEmbedding` を使う。零次の台は通常の制限で、単位・積と構造射を比較する。 | 離散入力全体の厳密比較と `restrict` の源比較。60–150 行。 |

E3 は約 850–2,100 行。③ を直接の前提にはしない。随伴の降下に必要な比較を全単体で得られるかが見積もりの幅。

## 4. E4　π₀、厳密入力、Tot

| 欄 | 既存宣言からの経路 | 足りない補題・規模 |
| --- | --- | --- |
| `pi0` | `homologyCommAlgebra` を使い、積 `homologyCommRing_mul`、単位 `homologyCommRing_one`、構造射 `homologyAlgebra_algebraMap` を厳密な代数射で保つ。擬同型で環同型となるので、局所化して `commAlgCatEquivUnder` で `RingAlgebra` に送る。 | H⁰ の環準同型の関手化、擬同型反転、元の `CAlg_R` のホモトピー圏への降下。100–260 行。 |
| `pi0_forget` | `algebraCAlgSource_underlyingDerivedIso` と E1 の `strictToD_homologyIso`。厳密な射上で H⁰ の線形写像が同じであることを使う。 | ホモトピー圏上で自然同型として降ろす。60–140 行。 |
| `pi0_discrete` | `zeroDegreeHomologyAlgebraIso`、`homologyBinary_discrete`、`homologyNullary_discrete`、`discreteCAlgUnderEmbedding`。 | 既存の零次比較の代数射に関する自然性、cofibrant 置換の回収。40–120 行。 |
| `pi0_restrict` | E3 の厳密制限と E1 の H⁰ の制限比較を使う。 | 加法群の同型が積・単位・係数射を保つこと。単に D 側の同型を使うだけでは環の自然同型にならない。80–200 行。 |
| `ofCdga` | `commutativeAlgebraFunctor` と `Operad.restrictAlgebra (augmentation S)` の nerve を `algebraCAlgSource` に送る。 | drafts の合成を本体へ出す。数行。 |
| `ofCdga_forget` | `algebraCAlgSource_underlyingDerivedIso` を上の厳密入力で前合成する。 | 二つの厳密な忘却の合成を射も含めて比較。30–100 行。 |
| `ofCdga_discrete` | 界面の `discreteCDGA` と `discreteCommutativeFunctor`・`discreteAlgebraFunctor` が使う次数零 single を照合する。 | `Interface/StrictInputs` と模型側の零次モノイドの自然比較。点ごとの同型で終えず `discreteCAlgUnderEmbedding` の同じ図式に接続。70–160 行。 |
| `ofCosimplicial` | 厳密離散代数の各項を `discreteAlgebraFunctor` で送り、`framedLimitFunctor S SimplexCategory` を取って `algebraCAlgSource` へ。 | 宇宙と離散 Under の厳密図式の照合。関手の候補自体は 30–90 行。 |
| `ofCosimplicial_forget` | `framedLimitCarrierNatIso` と `algebraCAlgSource_underlyingDerivedIso` で複体の frame 極限まで比較できる。 | その複体の導来像と `cosimplicialCochains` の全関手比較。ここを W16 内の模型に特化した計算で示さない限り、G10 の複体比較を待つ。G10 の既存依頼型は頂点・各次数を中心にしているので、この欄には射と指定錐までの比較を確認する。G10 後の接続 100–300 行。 |
| `ofCosimplicial_cone` | `framedLimitDerivedIso` は通常の局所化での右導来関手の値を照合する。`cAlgForgetDerived_mapJoinCone_isLimit` と E2 の保存性を使う経路もある。 | frame から同じ全図式上の native 錐と脚を構成し、写像空間で極限性を示す。D 側で示す場合は CAlg の極限の存在と保存性による反映も要る。G10 の D 側極限錐だけからは CAlg の錐は得られない。250–650 行以上。**［一般∞］** |
| `ofCosimplicial_restrict` | E3 の `discrete_restrict` と係数制限の右随伴性を使い、同じ Δ 図式の極限を比較する。厳密制限と frame の交換を直接示す経路もある。 | 関手の圏での極限比較。頂点ごとに得た極限同型を全関手同型として使うには、射についての錐の整合が必要。前二欄の後、120–320 行。**［一般∞］** |

E4 表にない余単体的 cdga の 5 欄は次の扱いを提案する。厳密入力の値を `ofCdga` と同じ厳密代数関手から作り、可換環の Tot と frame を共用する。

| 欄 | 経路と残り |
| --- | --- |
| `ofCosimplicialCdga` | 厳密 cdga の各項を `ofCdga` の源の厳密代数に送り、同じ `framedLimitFunctor` を使う。関手の候補は 20–60 行。 |
| `ofCosimplicialCdga_cone` | 可換環の場合の native 錐を作る橋が任意の厳密余単体的代数図式を扱えば再利用できる。追加 40–150 行。D 側を直積による総複体で計算する経路なら、非有界複体について直積による総化とその自然比較が別途必要。 |
| `ofCosimplicialCdga_discrete` | `ofCdga_discrete` の源での厳密比較を frame に送り、`framedLimitFunctor_map_quasiIso` を使う。同じ厳密 frame モデルを選ぶと小さくなる。50–150 行。 |
| `ofCosimplicialCdga_evalZero` | 同じ native 極限錐の一族を [0] に制限して `SSet.Homotopy` を構成する。自然な辺の選択と時刻 0・1 の端点の照合が要る。80–220 行。 |
| `ofCosimplicialCdga_evalZero_leg` | 上で選んだ辺と同じ錐の `F2.nativeConeLeg` の**辺の等式**を示す。ホモトピー類の等式まででは欄に足りない。30–110 行。 |

Tot を除く E4 は約 400–1,000 行。Tot の追加は G10 側の証明を除いても約 750–2,000 行。全余単体的 cdga での総複体比較は、W14 の A1 に残した行 0 への射影の可逆性を閉じるときにも要る。現行の欄は維持し、A1 のために必要なら同じ模型上の別定理として扱う。

## 5. ③ を待つ欄と段 4 の組み立て

- **③ を待つ候補は Tot の比較群。** `ofCosimplicial_forget` は G10 の全関手版が必要。`ofCosimplicial_cone`・`ofCosimplicial_restrict` は、同じフレームから native 極限錐を先に構成できれば G10 から独立に進められる。そこまで届かない場合は G10 後。`ofCosimplicialCdga_cone` と指定脚の 2 欄は同じ錐の橋を待つ。既存 G10 の対象は余単体的加群の次数零入力なので、非有界 cdga の全比較までを G10 の供給に含めて見積もらない。
- **③ の既定タスクとは別に規模が大きい欄。** `forget_preservesSifted` と `coproduct_tensor` は図式・テンソルのモデル比較が必要。E2 で局所化した図式の強さを確かめ、実装の見通しが立つまで完成の見積もりを確定しない。
- **範囲外。** `presentable` と `powerOp0`、`powerOp0_zero`、`powerOp0_pos`、`powerOp0_discrete`、`powerOp0_tot` の 6 欄。M15 は界面の欄にない。
- **段 4 の引数。** `powerOp0` 本体と従属する 4 法則は一緒に受け取る。Tot や sifted 等の欄が残る間は、G12・P⁰ のみを引数とする完成版を本体に置く条件に達しない。実際に供給できた欄と残りを停止点ごとに分け、界面の型は維持する。

**置き場所の案。** 各群の実例は `EInfinity/BarrattEccles/Theory/`。D 側だけの比較は `EInfinity/ComplexLimits/` か同じ `Theory/` 内の別ファイル。表中の **［一般∞］** は模型に固有でない補題候補で、KL-W1 の取り込みまでは `EInfinity/` 配下の専用補助ファイルに置き、移動候補として報告する。実例の証明で使う模型構造は既に構成したものを明示し、`[ModelCategory SSet]` は使わない。

停止点 0 ではこの報告だけを追加し、段 1 は承認待ち。

## 6. 停止点 1　E1（D の側）

`main` の承認 154faf181 を含む ea5d61388 を `math/bs-impl` に取り込んだ（7507b59e8）。

| 欄 | 本体の宣言と証明 |
| --- | --- |
| `restrictD` | `barrattEcclesRestrictD`。全複体の dg nerve で、既存の `dgNerveRestrictScalarsIso` と `restrictionComplexDGFunctor` による項別制限を行い、半自由解像を取る。 |
| `restrictD_id` | `barrattEcclesRestrictD_id`。全複体での厳密な恒等則と既存の半自由 retract を使う。 |
| `restrictD_comp` | `barrattEcclesRestrictD_comp`。全複体での厳密な合成則を使い、中間の半自由解像の augmentation を、項別制限後に反転する。各頂点で同じ augmentation の辺を評価する。 |
| `restrictD_homologyIso` | `barrattEcclesRestrictD_homologyIso`。任意の辺で項別制限した複体射を回収し、`exactCochainHomologyIso` を適用する。半自由解像と比較してから、係数制限が台の可換群を保つことを使う。 |
| `strictToD_homologyIso` | `complexOrdinaryDerivedSourceHomologyIso`。既存の `complexOrdinaryDerivedSource` に対し、同じ半自由解像の全 augmentation からホモロジーの自然同型を作る。厳密複体の各射は閉零辺として元の複体射に一致する。 |

任意の可換環準同型と全余鎖次数を扱う。新設の二モジュールは複体に固有で、［一般∞］の移動候補はない。

**入口と段階 II の監査に登録するモジュール**

- `SerrePositivity.EInfinity.ComplexLimits.StrictHomology`
- `SerrePositivity.EInfinity.BarrattEccles.Theory.DerivedRestriction`

`with_build_lock.sh --wait 1800` の下で `lake build SerrePositivity.EInfinity.BarrattEccles.Theory.DerivedRestriction` に成功（追加の二本をコンパイル、警告 0）。両モジュールの宣言を段階 II と同じ方式で再帰監査し、52 宣言・標準三公理のみ。sorry・追加公理 0。既存の宣言と界面の型は維持。入口と共通監査への登録は調整役に渡す。

## 7. 停止点 2　E2 の先行分と規模の判定

### 検査済みの二欄

- `forget_conservative` は `cAlgForgetDerived_conservative`。通常の局所化の射を cofibrant–fibrant な代数間の厳密射で代表する。自由 hammock の比較の両側で生成射の像を照合し、CAlg_R の同じ射の類を得る。忘却像の可逆性を E1 の全次数のホモロジー比較で擬同型に戻し、局所化で反転する。
- `discrete_initial` は `discreteCAlgUnderEmbedding_initial`。導来自由・忘却随伴で D(S) の零対象を送り、始対象を得る。零複体の自由代数は Schur 図式の arity 0 だけを持ち、Barratt–Eccles の augmentation で離散基礎環への指定射が擬同型になる。同じ自由 probe の零での値を介して恒等構造射の離散像に移す。

**入口と段階 II の監査に登録するモジュール**

- `SerrePositivity.EInfinity.SimplicialLocalization.SourceHom`
- `SerrePositivity.EInfinity.BarrattEccles.Theory.Conservative`
- `SerrePositivity.EInfinity.BarrattEccles.Theory.DiscreteInitial`

`SourceHom` は任意の相対圏で再利用できるが、現在の自由 hammock と DK の実装に依存する。独立な一般 ∞ 圏の新規補題はない。

共有鍵の下で `Theory.Conservative` と `Theory.DiscreteInitial` の対象ビルドに成功。新規三本の宣言を段階 II と同じ方式で再帰監査し、39 宣言・標準三公理のみ。sorry・追加公理 0。既存の宣言と界面の型は維持。

### 幾何学的実現と sifted 保存

`forget_preservesSifted` の現在の経路は 1,500 行を超える見込みなので、指示書 §3 の 1 によりここで区切る。実現の保存は余積とテンソルの比較から独立に調べた。

- `Operad.Algebra.forget_createsSiftedColimitsOfShape` は通常の sifted 図式の余極限を作る。これを使うには、指定された ∞ 図式を厳密な図式で表し、模型のホモトピー余極限と元の native 余錐を脚まで比較する必要がある。
- まず Δᵒᵖ の場合に、忘却後の同じホモトピー余極限の比較が必要。`DiagramModel.QuillenColimitComparison` は左 Quillen 関手用で、右 Quillen の `Operad.Algebra.forget` には代入できない。必要なのは、代数の projective 置換を忘却した図式で複体のホモトピー余極限を計算できる証明、または独立な重み付き実現と複体の実現の比較。
- `sigma_preservesSmallSiftedColimits_of_filtered_geometric` の始域は `SigmaPresheafInfinity`。今の CAlg_R に適用するための表示・降下は別途必要。任意の小 sifted 単体集合に対して直接示す場合も、図式と元の余錐の比較が残る。

幾何学的実現に対する厳密図式・native 余錐の橋を 500–800 行、代数の実現と忘却後の複体の実現の比較を 600–1,000 行、filtered および全 sifted への拡張を 500–900 行と見積もる。既存の補題を再利用した場合の紙の見積もりで、合計約 1,600–2,700 行。比較の結果は二つの模型で同じ指定余錐まで要求される。

`coprodWith`、`coprodWith_cocone`、`coproduct_tensor` はこの停止点に含めない。余積比較に sifted 保存を仮定として追加していない。E3 へ進むか、E2 の残りを ④ に分けるかは調整役の判断を待つ。

## 8. 夜間作業メモ（停止点 3 の前）

### 8.1 `baseChange_forget` と台の K 平坦性

cofibrant 代数 X に対し、`SmallObject.relativeCellComplexιObj` で始対象から X への射を分解し、右の `πObj` に対する持ち上げで X を同じ始対象から作ったセル代数の retract にする。`modelCategory_cofibrantlyGenerated` と `ModelGeneration.cofibrations_eq_generated` からこの持ち上げを得る。セル代数の台の余極限には `Operad.Algebra.forget_createsFilteredColimitsOfShape` を使う。

夜間に書いた Lean は次の四本。ビルドと監査は次の枠で行う。

| モジュール | 書いた部分 |
| --- | --- |
| `Theory.ArityKFlat` | `complexBasis` と `complex_isZero_positive` から arity ごとの K 平坦性を示し、`schurι_zero_isIso` で始代数の台へ移す。 |
| `Theory.CellularWeights` | 各付加セルの微分を有限個の先行セルの単項式で表したとき、各単項式の総重みより大きい自然数重みを整礎再帰で取る。 |
| `Theory.CellularCarrierKFlat` | 次数ごと分裂した逐次フィルトレーションと K 平坦な各商から `complexKFlat_of_degreewiseSplit` と `complexKFlat_colimit` で全体へ移す。小対象分解のセルのラベルを整数次数に戻し、各段が K 平坦であれば、`complexKFlat_of_retract` で任意の cofibrant 代数へ戻す。 |
| `Theory.CarrierScalarExtensionKFlat` | K 平坦な台を入力に取り、D(S) の実際の semifree 置換の augmentation を係数拡大しても擬同型となる成分を作る。`extension_quasiIso_of_kFlat_ends` を使う。 |

残る構成は、生成射 `complexSphereToDisk` の自由像を付加したときの**次数付きの準自由表示**。始代数から出発し、台の次数付き代数をセル生成元の自由代数と同定する。新しい生成元の微分は付加前の代数への境界射で与える。極限段では `RelativeCellComplex` の連続性と忘却の filtered 余極限を用い、各境界の有限台を引き継ぐ。この表示から `CellularWeights` の入力を取り、差分の複体で生成元の微分が消えること、次数ごとの分裂、重み全体の余極限で元の台に戻ることを示す。

重みの各商は、生成元の語の置換軌道ごとに arity の演算複体のシフトと stabilizer による余不変を取る。`orbitIndexEquiv` と `equivariantBasis_rightAction` で arity の基底を自由な右正則軌道として読める。stabilizer への制限と Koszul 符号を照合し、各次数の余不変の自由基底を作る。軌道ごとに上有界なので `complexKFlat_of_flat_boundedAbove` を適用し、直和には `complexKFlat_colimit` と AB4 を使う。基礎環上の arity の K 平坦性だけから余不変の K 平坦性を推論することはできない。

この構成が閉じたら、`allAlgebraCoefficientExtension_sourceIso` の左側を cofibrant 源へ制限し、`algebraCAlgSource_underlyingDerivedIso` と同じ semifree augmentation で右側の複体底変更を比較する。全厳密射で自然な増大を使って可逆二胞体を作り、`cAlgLocalizationSource_descendIso` で元の界面の `FunctorIso` に降ろす。今ある四本はこの還元までで、セルの準自由表示と `baseChange_forget` 本体は残る。

### 8.2 二項余積（§4 の 3、HA §3.2.4.7）

1. **模型の余積と指定余錐。** `cAlgVertexRepresentative` と `cAlgVertexRepresentativeIso` で右因子 y の cofibrant 代表 B を固定する。厳密な余積は `Operad.AlgebraAllColimits` の `HasColimitsOfSize` から取れる。離散二点図式の projective cofibrancy は各入力の cofibrancy と一致し、`DiagramModel.Projective.colimit_isLeftQuillen` と Brown の補題で、固定 B の余積が cofibrant 入力の弱同値を保つことを示す。この関手を `cAlgLocalizationSource_isLocalization` で降ろし、`coprodWith` を得る。
   余錐には同じ厳密な二つの包含を使う。`rightFrame` と `cotensorHomEquiv` の同一の対象 frame への Hom は、厳密な余積の普遍性から各単体次数で二つの Hom の積になる。この射を CAlg の native な写像空間で**指定された二つの脚による制限**と照合する。二点離散図式の余錐のファイバーをこの積として読み、`isColimitCone_of_coconeFiberMap_weakEquivalence` を適用する。右因子は代表から y への頂点同型で輸送する。要るのは共通 frame の積比較、二脚の native な照合、固定右因子の全関手への降下。一般の図式の strictification は二点の場合に不要。
2. **Hopf 対角とテンソル。** `hopf A` の `diagonalComponent` と二つの代数作用から、Koszul 符号つきの台のテンソルに作用を入れる。余単位則と零入力の単位を使って二つの包含を代数射にし、余積からの自然な比較射を作る。自由代数二本では、`Operad.freeAlgebraAdjunction` による `Free(V ⊕ W)` の同定から、混合入力の `(m,n)` ごとに比較する。必要なのは E(m+n) の制限から E(m) ⊗ E(n) への二色比較。各色で他方の入力を零入力で消す操作と Hopf 対角から作り、augmentation との可換性を示す。`equivariantBasis` を部分群へ制限して、両側が置換群環上で上有界かつ次数ごと射影的な解像度であることを示す。そのうえで、比較を同変な鎖ホモトピー同値にし、語のテンソルと余不変に移す。
   セル代数二本では §8.1 の重みを色ごとに取り、総重みの各商で自由の場合へ戻す。次数ごとの分裂、filtered 余極限のホモロジーとの可換性、retract を順に使い、任意の cofibrant 対で比較射が擬同型となることを示す。重みの選択はこの対象ごとの証明で使い、自然性は先に作った二変数の厳密な比較射から得る。
3. **強い形。** B を固定した厳密な比較射を、左変数の全厳密射について自然変換にする。台の K 平坦性で両因子の semifree augmentation を外し、`tensorWith (atVertex (forget S) y)` と比較する。既存の `algebraCAlgSource_underlyingDerivedIso` で忘却を台の導来像にそろえ、同じ局所化源上で可逆二胞体にしてから `cAlgLocalizationSource_descendIso` で降ろす。これにより右因子 y ごとの指定された `FunctorIso` を得る。各頂点の同型だけではこの欄を埋められない。

**規模の見込み。** 模型の余積と二脚の native な照合は約 350–600 行。Hopf の作用と包含は約 200–350 行、二色の自由比較とセルからの移送は約 500–800 行、強い形への降下は約 150–300 行。§8.1 の準自由表示と置換軌道の補題を共有できれば `coproduct_tensor` は約 850–1,450 行。共有部分をこの欄で新たに構成する場合は 1,500 行程度の上限を越える見込みなので、着手時にその切り分けを確かめる。経路に sifted 保存を仮定しない。

### 8.3 `forget_preservesSifted` の三部品（§4 の 4、HA §3.2.3.1）

| 部品 | 使う既存の宣言 | 足りない補題 |
| --- | --- | --- |
| Δᵒᵖ の図式と native な幾何学的実現の橋 | `HasSmallGeometricRealizations`、`PreservesSmallGeometricRealizations`、`DiagramModel.Projective.modelCategory`、`DiagramModel.HomotopyColimit.replacement` と `replacementComparison`、`DiagramModel.ColimitFrame.homIso` と `homIso_source_naturality`、`DiagramModel.WeightedHomotopyColimitFrame.homIso`、`cAlgLocalizationSource_isLocalization`。 | 任意の `nerve SmallSimplexOpposite ⟶ CAlg_R` の指定図式を厳密な projective 図式の像として比較する。既存の空間図式の strictification は標的が違う。次に模型の hocolim の余錐を native な余錐へ送り、指定脚を照合して余極限性を得る。単に各頂点を厳密な代数で代表させるだけでは足りない。 |
| 代数の実現と忘却後の複体の実現の比較 | `Operad.Algebra.forget_createsSiftedColimitsOfShape`、`DiagramModel.Projective.free` と `generators`、`DiagramModel.HomotopyColimit.comparison`、`normalizedSimplexCochainContraction`、`cotensorCarrierIso` と `weightedCotensorCarrierIso`。後二者は右 frame の照合に使える。`DiagramModel.QuillenColimitComparison.map_homotopyColimit_comparison_weakEquivalence` の対象は左 Quillen 関手。 | projective 置換 Q の台について、複体の外側の単体次数を正規化し、内部余鎖次数との直和 Tot から通常の `colim UQ` への増大が擬同型であることを示す。代数の projective セルの生成元は評価の左随伴により `Δ[k]` で添字づけられる。付加ラベルごとに重みを取り、各商で現れる有限個の標準単体の積を、同じラベルの因子の置換と可換に初頂点へ収縮する。正規化、符号、余不変、次数ごとの分裂を照合してから増大を閉じる。最後に U が作る通常の sifted 余極限と native な指定余錐を比較する。U の右 Quillen 性だけではこの比較は得られない。 |
| filtered と全 sifted への拡張 | `exists_cofinal_cardinalFiltered_poset`、`DiagramModel.HomotopyColimit.comparison_weakEquivalence_of_filtered`、`dgStrictFilteredColimit_quasiIso`、`dgKappaStrictFilteredColimitComparison_unconditional`、`Operad.Algebra.forget_createsFilteredColimitsOfShape`、`sigma_preservesSmallSiftedColimits_of_filtered_geometric`。 | filtered は cofinal poset に制限し、厳密な代数図式への比較と指定余錐の移送を作る。複体の filtered 比較は再利用でき、代数の弱同値は台の擬同型で判定する。全 sifted では、`SigmaPresheafInfinity` を始域とする既存の定理を使うなら、元の小図式を含む小さい有限余積閉包、その `PΣ` から CAlg への延長、元の図式と余錐への引き戻しが要る。延長の filtered と実現の保存を確認してから U との合成に適用する。別案は各 sifted 形から直接、同じ余錐を計算する比較。 |

目安は順に 500–800 行、600–1,000 行、500–900 行で計 1,600–2,700 行。共有するセル表示は §8.1 で型を確定する。Δᵒᵖ の strictification や全 sifted の延長を新たに大きく作る必要が判明し、約 2,700 行を超える見込みならそこで報告する。幾何学的実現の保存には二項余積とテンソルの比較を使わない。

### 8.4 朝に回すビルド順

1. `Theory.CAlgPiZeroRestriction` を対象ビルドし、`HomologyRestrictionOperations` と合わせて再帰監査する。前者は最終比較の検査が残り、後者は前の対象ビルドで成功して `af458c4c4` に保存済み。停止点 3 の報告ではこの結果と E3 の残欄を区別する。
2. `Theory.ArityKFlat` と `Theory.CellularWeights` を小さく検査し、次に `Theory.CellularCarrierKFlat` と `Theory.CarrierScalarExtensionKFlat` を検査する。新規四本は夜間作業の未コミット分。通った分の追加公理を監査する。
3. セルの準自由表示、重みの商、`baseChange_forget` を順に対象ビルドする。続いて §4 の順に二項余積とテンソルの比較、Δᵒᵖ の橋と実現比較、filtered と全 sifted を別々に検査する。

共有鍵の取得は KL-W1 の完了ファイル以降、または 8 時以降。取得には `--wait 1800` を使い、夜間に再開する場合も一回 30 分以内とする。

## 9. 朝の進捗（停止点 3 の前）

main の `898ab07c4` を `5527355d9` で取り込んだ。⑤b・⑤c・⑥ と、この段で編集するファイルの重複はない。

### 証明済みの欄

- E3 は `restrict`、`baseChange`、`baseChange_adjunction`、`restrict_forget`、`restrict_id`、`restrict_comp`、`discrete_restrict` の七欄。導来随伴の単位・余単位と三角等式も既存の局所化源で比較した。
- Tot 以外の E4 は `ofCdga`、`ofCdga_forget`、`ofCdga_discrete`、`pi0`、`pi0_forget`、`pi0_discrete`、`pi0_restrict`。最後の比較は厳密な H⁰ の比較が積・単位・構造射を保つことから、通常の局所化を通して得た。
- `CAlgPiZeroRestriction` の対象ビルド成功。夜にビルド済みの `HomologyRestrictionOperations` と合わせて 50 宣言を再帰監査し、標準三公理のみ。π₀ の最後の比較は `1ac469436`。この二本より前の 41 本では 585 宣言を監査済み。

### K 平坦性から全関手比較まで

`CellularGenerators` で実際の `AttachCells` の生成元と境界を取り出し、`attachedGenerator_d`、`attachedGenerator_hom_ext`、`exists_attachedGenerator_map` を証明した。`DerivedExtensionNerve` と `DerivedExtensionSource` は、複体の元の全 semifree augmentation を係数拡大した円柱を使う。K 平坦な源の全頂点で増大を反転し、同じ半自由部分圏の retract 比較を合成した。

`CAlgExtensionForget` の `barrattEcclesBaseChange_forget_of_cofibrantCarrierKFlat`は、この自然同型を cofibrant 代数の局所化源から降ろす。これで界面と同じ向きの `FunctorIso` が、cofibrant 代数の台の K 平坦性から従う。四本とも対象ビルド成功。35 宣言の再帰監査で標準三公理のみ（`b45afe9f5`）。

### 停止点 3 に残る証明

夜間の四本は対象ビルドを通り、11 宣言の再帰監査で標準三公理のみだった（`e16e9628b`）。セルの境界を取り出せても、台が次数付き自由代数になる証明には、Schur の余不変の関係と付加の pushout の関係を照合する必要がある。具体的には、sphere と disk の次数ごとの分裂を自由代数側へ移し、境界 cycle によって新生成元の微分を指定した自由な次数付き台を構成する。先行段との比較を pushout の普遍性で示し、極限段では忘却が作る filtered 余極限へ移す。今の `Operad` は複体に特化しており、次数付きオペラッド代数への忘却の余極限保存は既存の補題から直接使えない。

重みの商を計算する際、Mathlib の `Rep.coinvariantsTensorFreeLEquiv` により正則作用の因子の余不変を加群の直和で記述できる。Barratt–Eccles 側の `equivariantBasis_rightAction` と Schur 図式の diagonal action、次数付きテンソルの符号との照合が要る。 演算側の先頭置換を単位に正規化すれば、語の置換軌道を別に選ばず、基点つき非退化単体と順序つきの語で基底を添字づけられる。微分の後に正規化で語が置換されても総重みは変わらない。付加生成元の総重みと演算の単体次数の辞書式順序を使うと、生成元の微分は重みを下げ、演算の微分は単体次数を下げる。自由基底との照合が取れれば、この順序でも K 平坦性を示せる。

残る入力は `cofibrantCarrierKFlat_of_cellStages` の `hstage`。始段・実際の小対象分解・retract と、K 平坦性を得た後の自然比較は証明済み。ここでは停止点 3 前の進捗を記録する。E2 の余積と sifted 保存は停止点 3 の後の作業。

### 証明済み 51 本の登録候補

すべて `SerrePositivity.EInfinity.BarrattEccles.Theory` の下。個別の対象ビルドと再帰監査で計 681 宣言、標準三公理のみ。入口と段階 II 監査への登録は取り込み時に調整役が行う。

- `AlgebraCoefficientExtension`, `AlgebraCoefficientRestriction`, `AlgebraRestrictionCoherence`, `AlgebraTransport`
- `CAlgAdjunctionComparison`, `CAlgCdga`, `CAlgCoefficientExtension`, `CAlgCoefficientRestriction`
- `CAlgCoefficientSourceComparison`, `CAlgDerivedAdjunction`, `CAlgDiscreteRestriction`, `CAlgExtensionSourceComparison`
- `CAlgFullLocalizationSource`, `CAlgHoLocalization`, `CAlgPiZero`, `CAlgPiZeroDiscrete`
- `CAlgPiZeroForget`, `CAlgPiZeroRestriction`, `CAlgRestrictionCoherence`, `CAlgRestrictionForget`
- `CoefficientAugmentation`, `CoefficientBraiding`, `CoefficientChains`, `CoefficientExtension`
- `CoefficientExtensionOperad`, `CoefficientMonoidAction`, `CoefficientOperad`, `CoefficientRestrictionCoherence`
- `DerivedRestrictionSource`, `DiscreteCoefficientCarrier`, `DiscreteCoefficientOperations`, `HomologyAlgebraFunctor`
- `HomologyRestrictionClasses`, `HomologyRestrictionOperations`, `LaxTensorComparison`, `LaxTensorPower`
- `LocalizedAdjunctionAssembly`, `LocalizedAdjunctionTriangles`, `LocalizedAdjunctionWhiskering`, `LocalizedNerveNatTrans`
- `OperadTensorComparison`, `OrdinaryHoComposition`, `TensorAdjunctionMate`

- `ArityKFlat`、`CarrierScalarExtensionKFlat`、`CellularCarrierKFlat`、`CellularWeights`

- `CAlgExtensionForget`、`CellularGenerators`、`DerivedExtensionNerve`、`DerivedExtensionSource`

［一般∞］移動候補は `LocalizedAdjunctionWhiskering`、`LocalizedAdjunctionTriangles`、`LocalizedAdjunctionAssembly`、`LocalizedNerveNatTrans`、`OrdinaryHoComposition`。

## 10. 次数付き自由表示の構成（停止点 3 の前）

D75 の Barratt–Eccles 実例で進める。界面の型は §9 のまま。E2 の余積と sifted 保存は停止点 3 の後に扱う。

- 複体の微分を消す関手は各次数の加群を保つ。テンソルの次数成分を比較し、右随伴は各次数で cycle の対 `Z^i(Y) × Z^{i+1}(Y)` を取る。微分は `(a,b) ↦ (b,0)`。随伴で射 `u` を `(u,ud)` に送る。オペラッドの微分も消し、arity の比較とその随伴像で台の随伴を代数へ持ち上げる。
- 微分を消した自由代数の比較は、台の右随伴が忘却と可換なことから左随伴の一意性で得る。付加の pushout とその coproduct を代数の左随伴で送り、disk の次数ごとの分裂を使う。元の付加の境界側の射は disk の左因子、新生成元は右因子になる。pushout は先行段と新生成元の自由代数の余積になる。
- 超限合成では、段 `j` の余錐を `k < j` で付加した生成元で添字づける。後続段は先行段の余錐と新生成元の余錐を組み合わせる。極限段は早い段の降下射が生成元上で一致することから整合性を得て、元の連続な図式の余極限を使う。
- 余不変の基底は、各 arity の `equivariantBasis` を先頭置換の逆元で左正則表現として読み、`Rep.coinvariantsTensorFreeLEquiv` を適用する。Schur 図式は次数ごとに arity の余不変の直和へ分解する。残る比較は、テンソルの双次数成分とこの自由表現、語のテンソル基底、付加の境界と Leibniz 則の照合。
- 各セルの重みをその正の余鎖次数以上にも取ると、重み `n` 以下の基底の張る複体は次数 `n` より上で零になる。この部分複体は次数ごとに自由で、基底全体がその filtered 余極限を与える。さらに「重み − 余鎖次数」を自然数の高さにすれば、重みが増えない微分で高さが真に下がる。既存の `ComplexSemifreeBasis` と `moduleSemifree_objectwiseKFlat` をこの形で使う。

整理券方式を含む main の `c77013db6` を `2455d678f` で取り込んだ。旧方式で待っていたこのレーンの二件を終了し、`--wait 1800` で対象ビルドを一件にまとめて並べ直した。


### 検証済みの補助三本（11-11 午前）

`738c1f44f` に `EraseDifferential`・`AttachCoproductCells`・`WeightedBasisKFlat` をコミットした。三本の対象ビルドは成功し、再帰的な公理監査は計 61 宣言、標準三公理のみ。新しい公理と sorry は零。既存の公開宣言と界面の型は変更していない。

- `eraseDifferential` は次数の加群と射を保ち、零射と各図式形の余極限を保存する。次数付きテンソルと単位の比較同型を含む。
- `mapAttachCells` と `attachComplementIsColimit` は、指定されたセル付加の pushout を関手で送り、境界と補完因子の余積表示から付加後の余積表示を得る。
- `cellularWeightAbove` はセルの次数の下限と境界単項式の重みを同時に支配する。`complexKFlat_of_weightedBasis` は、次数を支配し微分で増えない重み付き基底から既存の semifree 基底を作り、K 平坦性を得る。

登録候補は上記三モジュール（いずれも `SerrePositivity.EInfinity.BarrattEccles.Theory` の下）。残りの自由表示・双次数の表現分解・境界の重みの照合は作業中。`hstage` と無条件の `baseChange_forget` はまだ閉じておらず、停止点 3 には達していない。


### 追加の検証（11-11 午前、停止点 3 の前）

`a3dedbc65` に `ArityCoinvariantColimit`・`ArityFreeRepresentation`・`OperadTransportAdjunction`・`TransfiniteCoproductCells` をコミットした。先の三本と合わせて 156 宣言の再帰的な公理監査を通過。

`81d4b3668` に `EraseDifferentialAdjunction`・`EraseDisk`・`TensorDegreeRepresentation` と、`EraseDifferential` の比較射の直接構成をコミットした。以上十本の対象ビルドと再帰的な公理監査は成功し、計 228 宣言、標準三公理のみ。公開される型と界面の型は変更していない。

- `transportAdjunction` は、複体上の強モノイダル随伴と互いに随伴な arity 比較から、実際のオペラッド代数上の随伴を作る。
- `cellStageCofanIsColimit` は、始段の始対象・後続段の指定余積・極限段の連続性から、先行セル全体で添字づけた指定余積を与える。
- `arityDegreeFreeIso` と `arityDegreeCoinvariantsTensorBasis` は、実際の正則 arity の作用と、対角余不変の基底を照合する。
- `arityDiagramCoconeIsColimit` と `schurDegreeArityIso` は、Schur の有限全単射上の図式を arity の余不変に分解する。
- `eraseDifferentialAdjunction` と `erasedDiskCofanIsColimit` は、微分を消す複体上の随伴と disk の指定された分裂を与える。
- `tensorDegreeRepresentationIsColimit` と `tensorDegreeCoinvariantsIso` は、複体の群作用を保つ双次数分解と、その余不変の分解を与える。

今回追加で登録する候補は、上記七本（すべて `SerrePositivity.EInfinity.BarrattEccles.Theory` の下）。`SchurDegreeDecomposition` は対象の型検査まで通り、公理監査とコミットは後続の基底の比較と合わせて行う。モノイダル比較・代数への持ち上げ・実際のセル段の自由表示は引き続き検証中。境界と基底の重みの照合、`hstage`、無条件の `baseChange_forget` は残っている。

main `7a689544b` を `4c3faf273` で取り込んだ。以後、整理券はこの worktree で一件、待機は `--wait 3600`、鍵の占有は一回 30 分以内としている。


### 語の基底と重み付き部分加群の検証（11-11 昼）

`a7b6bb934` に `SchurDegreeDecomposition`・`SchurDegreeBasis`・`TensorPowerDegreeBasis`・`SchurWordBasis`・`SphereCoproductBasis` をコミットした。十五本を合わせた再帰監査は 358 宣言、標準三公理のみだった。

さらに `TensorPowerDegreeBasis` の指定基底ベクトルの包含式、`BasisWeightSpan` と `EraseDifferentialGraded` の対象ビルドを確認した。十七本を合わせた再帰監査は 389 宣言、標準三公理のみ。`SchurWordBasis` の import は、使っている正次数消滅の供給元 `BarrattEccles.Degrees` にそろえた。

- `schurWordBasis` は、係数の基点つき非退化単体と斉次入力の語から、元の Schur 複体の各次数の基底を与える。
- `sphereCoproductDegreeBasis` は、実際の球複体の余積の指定包含を使う基底を与える。
- `basisWeightSpan` は、重みの上限で選んだ基底の張る部分加群。基底展開の台での判定、線形写像と純粋テンソルによる保存を証明した。
- `EraseDifferentialGraded` は、Mathlib の次数付き忘却の強モノイダル比較を保持し、微分を消す比較との可換性を証明した。

追加の登録候補は、この節の七本。いずれも `SerrePositivity.EInfinity.BarrattEccles.Theory` の下に置く。

セル段へ移す随伴とモノイダル構造、実際の境界からの重み選択は作業木で検証中。セル段の微分が基底の重みを増やさないことと、`hstage`、無条件の `baseChange_forget` が残る。停止点 3 前の途中記録。


### 対称モノイダル構造とオペラッドの検証（11-11 昼）

`EraseDifferentialBraiding`・`EraseDifferentialMonoidal`・`OperadMonoidalImage`・`EraseOperad` の対象ビルドが成功した。先の十七本と合わせた二十一本の再帰監査は 456 宣言、標準三公理のみ。登録候補にこの四本を追加する。

- 忘却の tensorator とその逆を両端に置き、Koszul 対称性を斉次テンソル上で照合した。比較射を相殺して自然性・結合則・単位則も得た。最終のモノイダル構造の対象検査は約 10 秒。
- `Operad.monoidalImage` は、複体間の lax braided 関手による対称オペラッドの移送。既存の `LaxComparisonSquare` の合成を使い、単位・内外の置換・入れ子と独立な二つの合成則を証明した。
- `Operad.erase` をこの構成の実例にした。自由代数の比較に必要な右随伴への持ち上げは作業木で検証中。

セル段の微分が重みを増やさないこと、`hstage` と無条件の `baseChange_forget` は引き続き残る。停止点 3 前の途中記録。


### 自由代数とセル付加の比較（11-11 昼）

`EraseAlgebraAdjunction` と `EraseCellAttachment` も対象ビルドと再帰監査を通った。二十三本の監査は計 497 宣言、標準三公理のみ。登録候補にこの二本を追加する。

`Operad.eraseAlgebraAdjunction` は、既存のモノイダル随伴の随伴対応で単位と部分合成を照合した代数上の随伴。`eraseFreeAlgebraIso` は自由・忘却随伴との合成を比較し、自由代数の自然同型を与える。`eraseAttachmentCofanIsColimit` はこの随伴と disk の指定分裂から、実際の付加の余積表示を与える。

超限合成への移行、実際のセル段への語の基底の移送、微分と重みの照合は作業木に置いている。`hstage` と無条件の `baseChange_forget` の証明を続ける。


### 実際のセル段の自由基底と境界の重み（11-11 昼）

`ErasedCellularAlgebra`・`CellStageGradedBasis`・`CellStageWeights`・`SchurBasisImages` の対象ビルドと再帰監査が成功した。追加二十七本を合わせた監査は計 572 宣言、標準三公理のみ。登録候補にこの四本を加える。いずれも `SerrePositivity.EInfinity.BarrattEccles.Theory` の下。

- `erasedCellStageCofanIsColimit` は、元の連続な相対セル複体の各段を先行セルの自由代数の指定余積で表す。再添字の前後の図式を自然同型で比較した。`erasedCellStageFreeIso_generator` と `_naturality` は、生成元の包含と後の段への指定射を保つ。
- `cellStageSchurDegreeIso` と `cellStageWordBasis` は、元のセル段の各次数の加群を、元の Barratt–Eccles の Schur 表示とその語の基底へ移す。次数評価には、微分を消した複体を明示している。
- `cellBoundaryNormalForm` は付加する実際の境界の基底展開。`cellStageWeight` はその有限の台から整礎再帰で選ぶ重み。`cellBoundaryWord_weight_lt` と `cellBoundary_mem_lowerSpan` により、各境界の語はそのセルより真に小さい重みを持つ。各セルと各基底語の余鎖次数を重みが支配することも証明した。
- `schurDegreeBasis_apply` と `arityDegreeCoinvariantsTensorBasis_apply` は、基底ベクトルを指定包含と余不変の比較同型で記述する。

残る作業は、語の基底を実際の演算と付加生成元の式で照合し、演算の合成・対称群の正規化・微分によって語の総重みが増えないことを証明する部分。これを `complexKFlat_of_weightedBasis` の微分の条件へ入れ、`hstage` と無条件の `baseChange_forget` を閉じる。停止点 3 前の途中記録。


### 正規化・対称群・演算の合成の重み保存（11-11 夕方、停止点 3 の前）

追加四十三本を合わせた対象ビルドと再帰的な公理監査が成功した。監査は計 812 宣言、標準三公理のみ。
界面の型と既存の main の公開宣言は変更していない。

- `SchurBasisImages` の指定包含の式を、正規化された係数と入力の語の式まで拡張した。
- `TensorWordSymmetry`・`TensorPowerWordWeights` は Koszul 組紐・結合子・全対称群の作用による総重みの保存を与える。
- `SchurGeneratorWeights` は対角置換不変性から、正規化された係数の評価を任意の係数へ広げた。正次数の係数は零である。
- `EraseFreeGenerators` は自由代数の比較が指定された単位と随伴対応を保つことを示す。`ErasePowerComparison` は微分を消すテンソル冪の比較が各語の基底を保つことを示す。
- `PowerWordEvaluation` と `OperadWordEvaluation` は指定入力とその微分の重みの上限から、評価された語の微分を評価する。後者は演算自体の重み保存を明示的に仮定するので、この二本だけではセル代数の微分の条件は閉じていない。
- `WeightedTensorFamily` は有限入力族の係数と入力の分離・テンソル冪の連結を、指定された基底と添字の移送まで含めて比較する。
- `SchurOperationWeights.preserves_schurOperationGenerator` は、自由代数の演算の合成生成射が、任意の係数について入力の総重みを増やさないことを示す。

今回追加の登録候補（すべて `SerrePositivity.EInfinity.BarrattEccles.Theory` の下）:

1. `SchurDegreeInclusions`
2. `TensorWordWeights`
3. `TensorWordSymmetry`
4. `TensorPowerWordWeights`
5. `SchurWordNormalForm`
6. `EraseFreeGenerators`
7. `ErasePowerComparison`
8. `SchurGeneratorWeights`
9. `PowerWordEvaluation`
10. `OperadWordEvaluation`
11. `TensorFamilyWeights`
12. `UnitWordWeights`
13. `BasedWeightMaps`
14. `WeightedTensorFamily`
15. `SchurWeightedBasis`
16. `SchurOperationWeights`

`SchurPowerWordLift` と `SchurActionWeights` は未検証なのでコミットに含めず、作業木で検査を続ける。
残りは自由代数の作用全体の重み保存、実際のセル段の作用・付加生成元・後続段への指定射との照合、微分の重み評価である。
`hstage` と無条件の `baseChange_forget` は未完了で、停止点 3 には達していない。


### 実際のセル段の作用・包含・語の評価（11-11 夕方、停止点 3 の前）

追加五十九本の対象ビルドと再帰的な公理監査が成功した。監査は 864 宣言、標準三公理のみ。
今回は各モジュールに監査された宣言があることも検査している。`SchurWeightedBasis` の今回新設した係数基底は、返す型を具体的なオペラッドの arity の表記にそろえた（従前の複体と定義上同じ型）。界面と main の既存の公開宣言は変更していない。

- `SchurPowerWordLift` は、Schur 語のテンソル基底を、同じ重みの上限を持つ内側の演算族へ持ち上げる。先頭と末尾を扱う補題に分け、依存する arity の族の型照合を軽くした。宣言ごとの heartbeat 上限の増加は不要になった。
- `SchurActionWeights` と `SchurUnitWeights` は、自由代数の作用全体と生成元の包含の重み保存を与える。
- `EraseAlgebraWordAction` と `EraseWordEvaluation` は、微分を消す比較が、基底および任意の指定された斉次入力の語の評価を保つことを示す。
- `ErasedIsoWeightTransfer` は、微分を消した代数の間の同型が次数ごとの指定基底を保つとき、元の代数の作用の重み保存を移す。元の複体の間の同型は仮定しない。
- `CellStageActionWeights` は実際のセル段の作用の重み保存を証明した。
- `CellStageFreeNaturality` は元の球複体の余積による自由表示と段の指定射の自然性。`CellStageInclusionWeights` はこれと `SchurMapWeights` を使い、実際の後続段への包含の重み保存を証明した。
- `CellStageWordEvaluation` は、元のセル段の基底語を、自由表示の生成元の像に係数演算を作用させた式で表す。

今回追加の登録候補（すべて `SerrePositivity.EInfinity.BarrattEccles.Theory` の下）:

1. `PowerWordNaturality`
2. `EraseAlgebraWordAction`
3. `WeightBasisEquiv`
4. `ErasedIsoWeightTransfer`
5. `WeightedPowerMap`
6. `SchurMapWeights`
7. `EraseWordEvaluation`
8. `CellStageFreeNaturality`
9. `SphereCoproductInclusions`
10. `SchurPowerWordLift`
11. `SchurActionWeights`
12. `CellStageActionWeights`
13. `FreeWordEvaluation`
14. `SchurUnitWeights`
15. `CellStageInclusionWeights`
16. `CellStageWordEvaluation`

残りは、自由表示で定義した生成元の像を、実際の付加生成元の後続段での像へ照合し、その微分を実際の付加の境界へ結びつける部分。
境界の重み評価・後続段への包含・語の微分の一般補題をこの照合に適用して、`hstage` と無条件の `baseChange_forget` を閉じる。
停止点 3 にはまだ達していない。


### 鍵の運用の修正（11-11 17:10 の指示）

`build-session.py /tmp/bsw16/graded/live33` を終了し、共有の鍵の解放とプロセスの終了を確認した。
鍵を保持したまま要求を待ち、編集・証明の検討・報告を進める形は廃止する。
今後は一回の `lake build <対象>` または一回の `lake env lean <監査>` のコマンドそのものを、
`zsh scripts/refactor/with_build_lock.sh --wait 3600 -- …` で実行する。
コマンドが終われば直ちに鍵を返し、次の検査は編集を終えてから新しい整理券一枚で待つ。
常駐のセッションは再使用しない。

main `32959effc`（coord の優先・鍵の履歴・ビルド中だけ保持する規則）を `f35b802c7` で取り込んだ。
枝の `scripts/refactor/with_build_lock.sh` が main と一致することを確認した。
解放後の列で、この worktree の持ち主・整理券はないことを確認した。

取り込み前の検証済みの五十九本は `fd67340aa` に保存済み（864 宣言、標準三公理のみ）。
`CellStageDifferentialWeights` と `EraseAttachmentGenerators` は未検証であり、コミットせず作業木に残す。
生成元の微分・実際の境界の照合、`hstage` と無条件の `baseChange_forget` は引き続き未完了。
停止点 3 には達していない。


## 11. 停止点 3　E3（M13）の八欄と Tot 以外の E4

`main` の `32959effc` を取り込んだ `math/bs-impl` で検証した。
残っていた cofibrant 代数の台の K 平坦性と、無条件の `baseChange_forget` が閉じた。
E3 の八欄と、先に検証した Tot 以外の E4 の七欄が本体の宣言で供給できる。
界面の型、main の既存の公開宣言、共通の入口と段階 II の監査への登録は変更していない。

### E3 の欄

| 欄 | 本体の宣言（`SerrePositivity.EInfinity.BarrattEccles`） |
| --- | --- |
| `restrict` | `barrattEcclesRestrict` |
| `baseChange` | `barrattEcclesBaseChange` |
| `baseChange_adjunction` | `barrattEcclesBaseChange_adjunction` |
| `restrict_forget` | `barrattEcclesRestrict_forget` |
| `baseChange_forget` | `barrattEcclesBaseChange_forget`（今回） |
| `restrict_id` | `barrattEcclesRestrict_id` |
| `restrict_comp` | `barrattEcclesRestrict_comp` |
| `discrete_restrict` | `barrattEcclesDiscrete_restrict` |

`barrattEcclesBaseChange_forget` は任意の環準同型 `f : S →+* T` に対する
`FunctorIso (barrattEcclesBaseChange f ≫ cAlgForgetDerived T)
(cAlgForgetDerived S ≫ derivedInfinityBaseChange f)`。
頂点ごとの比較を与えるだけでなく、元の界面と同じ全関手の自然同型を与える。
K 平坦性を引数に要求しない。

### 最後の証明

1. `EraseAttachmentGenerators` は、微分消去後のセル付加の自由生成元を、元の実際の付加生成元へ照合する。disk の指定分裂の下の次数の成分を使う。
2. `CellStageFreeGenerators` と `CellStageGeneratorCompatibility` は、元の球複体の余積から作った自由表示が各セルの指定生成元を保ち、その生成元の像が実際の付加生成元を後続段へ送ったものであることを示す。
3. `cellStageGeneratorValue_d`（`CellStageGeneratorDifferential`） は、その微分が実際の付加の境界を元の段から送ったものであることを、複体射の可換性と段の指定射の合成で示す。
4. 全体で選んだセルの重み、境界の有限な基底展開、後続段への包含の重み保存から、生成元の微分の上限を得る。語の評価の Leibniz 則で全基底語の微分へ広げる。
5. 重みが次数を支配し、微分で重みが増えないことから、`weightedSemifreeBasis` の自然数の高さが微分で下がる。これで実際の各セル段の `cellStageCarrierKFlat`、すなわち従前の `hstage` を供給する。
6. `cofibrantCarrierKFlat`（`CAlgExtensionForgetKFlat`） は既存の小対象分解と retract の帰着にこれを適用する。同じ cofibrant DK 入力の台の K 平坦性を、証明済みの局所化源の全関手比較へ渡し、`barrattEcclesBaseChange_forget` を得る。

今回最後に追加する六本は `CellStageDifferentialWeights`、`EraseAttachmentGenerators`、
`CellStageFreeGenerators`、`CellStageGeneratorCompatibility`、`CellStageGeneratorDifferential`、
`CAlgExtensionForgetKFlat`。いずれも `EInfinity/BarrattEccles/Theory/` の下。

### 検証

- 対象ビルド：`lake build SerrePositivity.EInfinity.BarrattEccles.Theory.CAlgExtensionForgetKFlat` 成功。最後のセル段・生成元・境界と係数拡大の比較を依存込みで検査した。
- 再帰的な公理監査：新設 **116 モジュール・1,567 宣言**、標準三公理 `propext`・`Classical.choice`・`Quot.sound` のみ。各モジュールで監査対象の宣言が一つ以上あることも検査した。本体の `sorry`・追加公理は 0。
- 一回の対象ビルド、一回の監査ごとに `with_build_lock.sh --wait 3600` で取得・返却した。編集・証明の検討・報告の間は保持せず、常駐セッションは使っていない。
- `git diff --check` 成功。最終の六本に 100 字超の行はない。

### 取り込みと次の範囲

入口と段階 II 監査への登録は調整役に依頼する。既存の §9・§10 の一覧を合わせた、今回の取り込み対象のモジュール全体は下記の 116 本。
［一般∞］の移動候補は前掲の `LocalizedAdjunctionWhiskering`・`LocalizedAdjunctionTriangles`・
`LocalizedAdjunctionAssembly`・`LocalizedNerveNatTrans`・`OrdinaryHoComposition`。
KL-W1 の改名は先取りしていない。

Tot 以外の E4 の `ofCdga`・`ofCdga_forget`・`ofCdga_discrete`・`pi0`・`pi0_forget`・
`pi0_discrete`・`pi0_restrict` は §9 の検証済みの宣言を使う。
W16 の残りは §4 の順で、E2 の余積とテンソルの比較、sifted の保存、Tot の群。
Tot の G10 待ちと、範囲外の G12・P⁰ は従前の扱いを保つ。
全界面の実例の組み立ては段 4 の作業として残る。

### 登録する全モジュール

```text
SerrePositivity.EInfinity.BarrattEccles.Theory.AlgebraCoefficientExtension
SerrePositivity.EInfinity.BarrattEccles.Theory.AlgebraCoefficientRestriction
SerrePositivity.EInfinity.BarrattEccles.Theory.AlgebraRestrictionCoherence
SerrePositivity.EInfinity.BarrattEccles.Theory.AlgebraTransport
SerrePositivity.EInfinity.BarrattEccles.Theory.ArityCoinvariantColimit
SerrePositivity.EInfinity.BarrattEccles.Theory.ArityFreeRepresentation
SerrePositivity.EInfinity.BarrattEccles.Theory.ArityKFlat
SerrePositivity.EInfinity.BarrattEccles.Theory.AttachCoproductCells
SerrePositivity.EInfinity.BarrattEccles.Theory.BasedWeightMaps
SerrePositivity.EInfinity.BarrattEccles.Theory.BasisWeightSpan
SerrePositivity.EInfinity.BarrattEccles.Theory.CAlgAdjunctionComparison
SerrePositivity.EInfinity.BarrattEccles.Theory.CAlgCdga
SerrePositivity.EInfinity.BarrattEccles.Theory.CAlgCoefficientExtension
SerrePositivity.EInfinity.BarrattEccles.Theory.CAlgCoefficientRestriction
SerrePositivity.EInfinity.BarrattEccles.Theory.CAlgCoefficientSourceComparison
SerrePositivity.EInfinity.BarrattEccles.Theory.CAlgDerivedAdjunction
SerrePositivity.EInfinity.BarrattEccles.Theory.CAlgDiscreteRestriction
SerrePositivity.EInfinity.BarrattEccles.Theory.CAlgExtensionForget
SerrePositivity.EInfinity.BarrattEccles.Theory.CAlgExtensionForgetKFlat
SerrePositivity.EInfinity.BarrattEccles.Theory.CAlgExtensionSourceComparison
SerrePositivity.EInfinity.BarrattEccles.Theory.CAlgFullLocalizationSource
SerrePositivity.EInfinity.BarrattEccles.Theory.CAlgHoLocalization
SerrePositivity.EInfinity.BarrattEccles.Theory.CAlgPiZero
SerrePositivity.EInfinity.BarrattEccles.Theory.CAlgPiZeroDiscrete
SerrePositivity.EInfinity.BarrattEccles.Theory.CAlgPiZeroForget
SerrePositivity.EInfinity.BarrattEccles.Theory.CAlgPiZeroRestriction
SerrePositivity.EInfinity.BarrattEccles.Theory.CAlgRestrictionCoherence
SerrePositivity.EInfinity.BarrattEccles.Theory.CAlgRestrictionForget
SerrePositivity.EInfinity.BarrattEccles.Theory.CarrierScalarExtensionKFlat
SerrePositivity.EInfinity.BarrattEccles.Theory.CellStageActionWeights
SerrePositivity.EInfinity.BarrattEccles.Theory.CellStageDifferentialWeights
SerrePositivity.EInfinity.BarrattEccles.Theory.CellStageFreeGenerators
SerrePositivity.EInfinity.BarrattEccles.Theory.CellStageFreeNaturality
SerrePositivity.EInfinity.BarrattEccles.Theory.CellStageGeneratorCompatibility
SerrePositivity.EInfinity.BarrattEccles.Theory.CellStageGeneratorDifferential
SerrePositivity.EInfinity.BarrattEccles.Theory.CellStageGradedBasis
SerrePositivity.EInfinity.BarrattEccles.Theory.CellStageInclusionWeights
SerrePositivity.EInfinity.BarrattEccles.Theory.CellStageWeights
SerrePositivity.EInfinity.BarrattEccles.Theory.CellStageWordEvaluation
SerrePositivity.EInfinity.BarrattEccles.Theory.CellularCarrierKFlat
SerrePositivity.EInfinity.BarrattEccles.Theory.CellularGenerators
SerrePositivity.EInfinity.BarrattEccles.Theory.CellularWeights
SerrePositivity.EInfinity.BarrattEccles.Theory.CoefficientAugmentation
SerrePositivity.EInfinity.BarrattEccles.Theory.CoefficientBraiding
SerrePositivity.EInfinity.BarrattEccles.Theory.CoefficientChains
SerrePositivity.EInfinity.BarrattEccles.Theory.CoefficientExtension
SerrePositivity.EInfinity.BarrattEccles.Theory.CoefficientExtensionOperad
SerrePositivity.EInfinity.BarrattEccles.Theory.CoefficientMonoidAction
SerrePositivity.EInfinity.BarrattEccles.Theory.CoefficientOperad
SerrePositivity.EInfinity.BarrattEccles.Theory.CoefficientRestrictionCoherence
SerrePositivity.EInfinity.BarrattEccles.Theory.DerivedExtensionNerve
SerrePositivity.EInfinity.BarrattEccles.Theory.DerivedExtensionSource
SerrePositivity.EInfinity.BarrattEccles.Theory.DerivedRestrictionSource
SerrePositivity.EInfinity.BarrattEccles.Theory.DiscreteCoefficientCarrier
SerrePositivity.EInfinity.BarrattEccles.Theory.DiscreteCoefficientOperations
SerrePositivity.EInfinity.BarrattEccles.Theory.EraseAlgebraAdjunction
SerrePositivity.EInfinity.BarrattEccles.Theory.EraseAlgebraWordAction
SerrePositivity.EInfinity.BarrattEccles.Theory.EraseAttachmentGenerators
SerrePositivity.EInfinity.BarrattEccles.Theory.EraseCellAttachment
SerrePositivity.EInfinity.BarrattEccles.Theory.EraseDifferential
SerrePositivity.EInfinity.BarrattEccles.Theory.EraseDifferentialAdjunction
SerrePositivity.EInfinity.BarrattEccles.Theory.EraseDifferentialBraiding
SerrePositivity.EInfinity.BarrattEccles.Theory.EraseDifferentialGraded
SerrePositivity.EInfinity.BarrattEccles.Theory.EraseDifferentialMonoidal
SerrePositivity.EInfinity.BarrattEccles.Theory.EraseDisk
SerrePositivity.EInfinity.BarrattEccles.Theory.EraseFreeGenerators
SerrePositivity.EInfinity.BarrattEccles.Theory.EraseOperad
SerrePositivity.EInfinity.BarrattEccles.Theory.ErasePowerComparison
SerrePositivity.EInfinity.BarrattEccles.Theory.EraseWordEvaluation
SerrePositivity.EInfinity.BarrattEccles.Theory.ErasedCellularAlgebra
SerrePositivity.EInfinity.BarrattEccles.Theory.ErasedIsoWeightTransfer
SerrePositivity.EInfinity.BarrattEccles.Theory.FreeWordEvaluation
SerrePositivity.EInfinity.BarrattEccles.Theory.HomologyAlgebraFunctor
SerrePositivity.EInfinity.BarrattEccles.Theory.HomologyRestrictionClasses
SerrePositivity.EInfinity.BarrattEccles.Theory.HomologyRestrictionOperations
SerrePositivity.EInfinity.BarrattEccles.Theory.LaxTensorComparison
SerrePositivity.EInfinity.BarrattEccles.Theory.LaxTensorPower
SerrePositivity.EInfinity.BarrattEccles.Theory.LocalizedAdjunctionAssembly
SerrePositivity.EInfinity.BarrattEccles.Theory.LocalizedAdjunctionTriangles
SerrePositivity.EInfinity.BarrattEccles.Theory.LocalizedAdjunctionWhiskering
SerrePositivity.EInfinity.BarrattEccles.Theory.LocalizedNerveNatTrans
SerrePositivity.EInfinity.BarrattEccles.Theory.OperadMonoidalImage
SerrePositivity.EInfinity.BarrattEccles.Theory.OperadTensorComparison
SerrePositivity.EInfinity.BarrattEccles.Theory.OperadTransportAdjunction
SerrePositivity.EInfinity.BarrattEccles.Theory.OperadWordEvaluation
SerrePositivity.EInfinity.BarrattEccles.Theory.OrdinaryHoComposition
SerrePositivity.EInfinity.BarrattEccles.Theory.PowerWordEvaluation
SerrePositivity.EInfinity.BarrattEccles.Theory.PowerWordNaturality
SerrePositivity.EInfinity.BarrattEccles.Theory.SchurActionWeights
SerrePositivity.EInfinity.BarrattEccles.Theory.SchurBasisImages
SerrePositivity.EInfinity.BarrattEccles.Theory.SchurDegreeBasis
SerrePositivity.EInfinity.BarrattEccles.Theory.SchurDegreeDecomposition
SerrePositivity.EInfinity.BarrattEccles.Theory.SchurDegreeInclusions
SerrePositivity.EInfinity.BarrattEccles.Theory.SchurGeneratorWeights
SerrePositivity.EInfinity.BarrattEccles.Theory.SchurMapWeights
SerrePositivity.EInfinity.BarrattEccles.Theory.SchurOperationWeights
SerrePositivity.EInfinity.BarrattEccles.Theory.SchurPowerWordLift
SerrePositivity.EInfinity.BarrattEccles.Theory.SchurUnitWeights
SerrePositivity.EInfinity.BarrattEccles.Theory.SchurWeightedBasis
SerrePositivity.EInfinity.BarrattEccles.Theory.SchurWordBasis
SerrePositivity.EInfinity.BarrattEccles.Theory.SchurWordNormalForm
SerrePositivity.EInfinity.BarrattEccles.Theory.SphereCoproductBasis
SerrePositivity.EInfinity.BarrattEccles.Theory.SphereCoproductInclusions
SerrePositivity.EInfinity.BarrattEccles.Theory.TensorAdjunctionMate
SerrePositivity.EInfinity.BarrattEccles.Theory.TensorDegreeRepresentation
SerrePositivity.EInfinity.BarrattEccles.Theory.TensorFamilyWeights
SerrePositivity.EInfinity.BarrattEccles.Theory.TensorPowerDegreeBasis
SerrePositivity.EInfinity.BarrattEccles.Theory.TensorPowerWordWeights
SerrePositivity.EInfinity.BarrattEccles.Theory.TensorWordSymmetry
SerrePositivity.EInfinity.BarrattEccles.Theory.TensorWordWeights
SerrePositivity.EInfinity.BarrattEccles.Theory.TransfiniteCoproductCells
SerrePositivity.EInfinity.BarrattEccles.Theory.UnitWordWeights
SerrePositivity.EInfinity.BarrattEccles.Theory.WeightBasisEquiv
SerrePositivity.EInfinity.BarrattEccles.Theory.WeightedBasisKFlat
SerrePositivity.EInfinity.BarrattEccles.Theory.WeightedPowerMap
SerrePositivity.EInfinity.BarrattEccles.Theory.WeightedTensorFamily
```

