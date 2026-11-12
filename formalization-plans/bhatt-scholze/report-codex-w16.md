# BS-W16 停止点 0（2026-11-10）

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

## 12. E2 再開と規模上限による中間停止（11-11 夕）

停止点 3 の取り込みを受け、`math/bs-impl` に main `7a3a0f965` を取り込んだ。登録 `afe1366a0` を含む。今回触る三本は新規で、⑤b・⑤c・⑥ の担当ファイルとの重複はない。界面の型・既存の公開宣言・入口・共有監査スクリプトは変更していない。

### 12.1 証明した部分と未完了の欄

三本、計 245 行を追加した。

| モジュール（すべて `EInfinity/BarrattEccles/Theory/`） | 供給する宣言・内容 |
| --- | --- |
| `CoproductModel` | `modelCoprodWith`、`modelCoprodWith_isLeftQuillen`、`modelCoprodWith_cofibrant`、`modelCoprodWith_map_weakEquivalence`。指定された余積射の pushout 性で cofibration と trivial cofibration の保存を示し、Ken Brown で cofibrant 入力間の弱同値の保存を得る。`cofibrantAlgebraCoprodWith` で実際の Barratt–Eccles 模型の cofibrant 部分圏へ制限する。ここで使うレポジトリの `Quillen.IsLeftQuillen` は二つの保存条件であり、固定右因子との余積に通常の右随伴があるとは主張していない。 |
| `CAlgCoproductFunctor` | `cofibrantAlgebraDKCoprodWith`、`cofibrantAlgebraDKCoprodWith_map_weak`、`cofibrantAlgebraCoprodRelative`、`cAlgCoprodWithModel`、`cAlgCoprodWithModel_vertex`、`barrattEcclesCoprodWith`。cofibrant な厳密余積を同じ DK 入力の相対関手にし、`localizationNerveMap` で CAlg の全関手へ送る。右因子 y は `cAlgVertexEquiv` の逆像で選ぶ。 |
| `RightFrameCoproduct` | `coprodOppositeProductIso`、`rightFrameCoprodHomIso` とその `_fst`・`_snd`。共通の右 frame への simplicial Hom を二つの Hom の積に分解し、二つの射が指定包含による前合成であることを等式で示す。 |

`coprodWith` の型の関手はできた。一方、`coprodWith_cocone`（指定された native な余積錐とその余極限性）と、右因子ごとの強い `coproduct_tensor : FunctorIso ...` はまだ証明していない。ここを E2 の完了や停止点 2 の追加達成とは扱わない。sifted 保存には依存していない。Tot・段 4 の実例の組み立てにはまだ進んでいない。

native な錐への次の比較では、`binaryCoconeOfEdges` の指定脚、`ModelRightFrameComparison.modelRightFramePinchedEquivalence`、`isColimitCone_of_pointHomFamily_comparison` を候補として使える。今回の Hom の積同型だけから native な余極限性を結論してはいない。`HomotopyFunctionComplex.FrameComparison.homLeft_weakEquivalence` や `ChosenComparison.left_weakEquivalence` の `[ModelCategory SSet]` を要求する版は使わない。

### 12.2 上限の再見積もりと停止理由

指示書 §3 の 1：**「二つのどちらかが見積もりの上限（各 1,500 行程度）を超えそうなら、そこで止めて報告する」**。sifted の上限だけは §4 の 4 で約 2,700 行に更新されている。`coproduct_tensor` の上限を変更する決定はないため、その規則による中間停止とする。

§8.2 の 850〜1,450 行は、準自由表示を共有するほか、二色の自由比較を 500〜800 行で閉じる見込みに基づいていた。停止点 3 の成果と残る API を照合すると、この部分を過小評価していた。新規の見込みは次のとおり。native な余積錐の残作業はこの表に含めない。

| `coproduct_tensor` に残る部分 | 再利用できるもの | なお必要なもの | 新規行数の目安 |
| --- | --- | --- | --- |
| Hopf テンソル代数と二つの包含 | `BarrattEccles.hopf`、`Hopf.diagonalComponent`、`Hadamard.separate`・`pair`、テンソル冪の置換と代入の比較 | `X.carrier ⊗ Y.carrier` 上の作用、等変性・単位・代入の則、零入力を使った二つの包含が代数射であること、全射での自然性。既存の `ConvolutionAlgebra` は内部 Hom の構成で、このテンソル代数を供給しない。 | 400〜650 |
| 二色の自由比較 | `equivariantBasis`・`equivariantBasis_rightAction`、arity の増大、Mathlib の `Rep` の射影解像度の比較 | `Σ_m × Σ_n` への制限、`E(m+n)` と `E(m) ⊗ E(n)` の指定比較、同変な鎖ホモトピー同値、二色の語と余不変による自由代数比較。対角の存在だけから余不変後の擬同型は従わない。 | 550〜850 |
| 実際のセル対への移送 | `cellStageErasedFreeIso`、`cellStageWordBasis`、`cellStageWeight`、`cellBoundaryWord_weight_lt`、`WeightedTensorFamily` と `TensorWordWeights` | 二色の入力を併せた余積の表示、比較射の指定された重み商での式、商を上の二色比較と同定すること、擬同型を次数ごとの分裂・filtered 余極限・retract へ移すこと。既存の K 平坦性の結論はこの比較の擬同型性を供給しない。 | 600〜850 |
| 強い全関手版への降下 | `cofibrantCarrierKFlat`、停止点 3 の semifree 増大の比較、`cAlgLocalizationSource_descendIso` | 同じ厳密な比較射を全射で自然な二胞体にし、固定右因子の `tensorWith` と同定して降ろす。 | 200〜350 |
| **計** | 停止点 3 で完成した補助は再計上しない | native な余積錐の残作業は別 | **1,750〜2,700** |

特に停止点 3 で得たのは一色の次数付き自由表示と、微分が重みを増やさないこと・境界が下の重みに入ることである。二色の部分群の解像度比較や、比較射の重み商の擬同型性を、そこから追加証明なしに使うことはできない。③ を待つことが判明したための停止ではなく、許可された規模を超える見込みによる停止である。上限を変更してこの経路を続けるかは調整役の判断を待つ。指示書 §4 の順序を保ち、sifted へ先に飛ばさない。

### 12.3 検証・登録候補

対象ビルド：`lake build SerrePositivity.EInfinity.BarrattEccles.Theory.CAlgCoproductFunctor SerrePositivity.EInfinity.BarrattEccles.Theory.RightFrameCoproduct` が成功。依存する新規 `CoproductModel` も対象ビルド済み。最終ログに警告なし。ルートビルドは行っていない。

三本・34 宣言の再帰的な公理監査に成功し、依存する公理は標準三公理のみだった。ソースの sorry・admit・新規公理は零。ビルドと監査はそれぞれ一回の `with_build_lock.sh --wait 3600` で実行し、常駐セッションは使っていない。このレーンの鍵は監査終了時に返却済み。

登録候補は、いずれも `SerrePositivity.EInfinity.BarrattEccles.Theory` の下の次の三本。登録は調整役が取り込み時に行う。

- `CoproductModel`
- `CAlgCoproductFunctor`
- `RightFrameCoproduct`

新規の［一般∞］移動候補はない。`RightFrameCoproduct` の一般部分は通常の圏と simplicial Hom の補題で、今回は Barratt–Eccles の証明の隣に置いた。既報の［一般∞］五本は移動していない。

## 13. §6 の再開と native な余積錐の見積もり（11-11 夜）

main `892772144` の指示書 §6 を `c0c30cd30` で取り込んだ。`coproduct_tensor` を W16 の中で続ける。単独の目安は約 2,700 行、native な錐と合わせた停止上限は約 3,500 行。⑤b・⑤c・⑥ のファイルには触らず、新規の `Theory/HopfTensor*` などで進める。

### 13.1 最初の区切り：native な錐の見積もり

`coprodWith_cocone` は、関手の指定頂点を頂点とする `JoinCocone (binaryPointDiagram x y)` と `IsColimitCone` を供給する。`CAlgCoproductFunctor.barrattEcclesCoprodWith` の定義を保ち、同じ厳密な二つの包含から脚を作る。

| 作業 | 規模の目安 |
| --- | --- |
| `CoproductModel`・`CAlgCoproductFunctor`・`RightFrameCoproduct`（前回の三本、証明済み） | 245 行 |
| 同じ局所化源の包含を native な辺へ送り、`binaryCoconeOfEdges` の二脚と頂点を照合 | 70〜100 行 |
| 二点図式の `coconeMappingSpace` を二つの Hom の積で計算し、指定脚による比較射を照合 | 80〜130 行 |
| 共通の右 frame の Hom と CAlg の Hom の比較を指定包含の前合成に合わせる | 180〜250 行 |
| `isColimitCone_of_pointHomFamily_comparison` への適用と、任意の頂点 x・y への輸送 | 40〜75 行 |
| **計（前回の三本を含む）** | **615〜800 行** |

使う候補は `binaryCoconeOfEdges` とその `_vertex`・`_leg_left`・`_leg_right`、`ModelRightFrameComparison.modelRightFramePinchedEquivalence`、同じ全標的の coherent 比較、`isColimitCone_of_pointHomFamily_comparison`。`ModelCategory SSet` を仮定する frame 比較は使わない。`hasColimit_binaryPointDiagram` の安定性を要求する版も CAlg には適用しない。

この見込みでは、`coproduct_tensor` の 1,750〜2,700 行と合わせて **2,365〜3,500 行**。前回の 245 行を別に二重計上していない。源変数の指定前合成を保つ比較と二点の余錐空間の計算はまだ型検査前であり、この部分が見込みを超えると分かった時点で合計の上限を再点検する。

### 13.2 二色比較で使う既存 API の確認

`CategoryTheory.ProjectiveResolution.liftHomotopy` は、同じ増大を保つ指定された二射の間の鎖ホモトピーを供給する。`homotopyEquiv` 自体の順射は選ばれた持ち上げなので、二色の指定比較そのものを順射に保つ組み立てを `ResolutionAugmentationComparison` に書いた。逆射だけを恒等射の持ち上げにし、両合成を `liftHomotopy` で比較する形である。これは表現のアーベル圏でも使える。

また Mathlib `RepresentationTheory.Coinduced` には、部分群への `Rep.resFunctor` の `PreservesProjectiveObjects` がある。したがって、現時点では等変なホモトピー逆を既存 API から組めないという停止条件には当たらない。ただし、`E(m+n)` の制限と `E(m) ⊗ E(n)` に射影解像度の構造を入れること、指定された二色比較が増大を保つことは別途証明が必要である。非同変な収縮を余不変に渡すだけで済ませない。

### 13.3 最初の検証済みのまとまり（包含を除く）

今回の新規十三本は計 **767 行**。前回の三本 245 行と合わせて十六本 1,012 行を検証した。今回のうち `ResolutionAugmentationComparison` と `TwoColorPermutation` の計 107 行は、二色比較の前置きに当たる。包含を含む残りを完成したとは扱わない。

- `hopfTensorAction` の全 arity の作用、等変性、単位則、指定された先頭代入射の比較、`hopfTensorAction_comp_zero` を証明した。`hopfTensorAlgebra` は任意の Hopf オペラッドと任意の二代数を取り、台が元の複体のテンソルである実際の代数を返す。cofibrancy は構成に不要。
- `hopfTensorMap`、二変数の `hopfTensorFunctor`、固定右因子の `hopfTensorWith` を定義した。自然性は全代数射の台の射の等式として証明している。
- `resolutionHomotopyEquivOfAugmentation` は指定された増大保存射そのものを順射に保つ。二色の置換群の埋め込み `twoColorPermutationHom` とその単射性も証明した。実際の二色複体を射影解像度とする構成は残る。
- `zeroArity_isZero_nonzero` と、次数集中下でホモトピーを射の等式へ戻す `eq_of_homotopy_concentrated` により、`zeroArity_augmentation_isIso` を証明した。これは零入力の増大が擬同型であるという既存の結論を、厳密な同型性へ強める新しい宣言である。

**検証。** `lake build ...Theory.HopfTensorFunctor ...Theory.ZeroArity` が成功。ほかの二色の前置きも個別の対象ビルドに成功。前回の三本を含む十六本・**115 宣言**を再帰監査し、標準三公理のみだった。sorry・admit・新規公理・デバッグ出力は零。`ZeroArity` には、証明中の二つの `letI` を `let` にする提案の警告がある。宣言の型・既存の公開宣言・界面・入口・共有監査スクリプトは変えていない。ルートビルドは行っていない。鍵は一回の対象ビルドまたは一回の監査の間だけ取り、待ちは `--wait 3600`、整理券は一枚とした。監査の鍵は返却済み。

**登録候補。** 前回の `CoproductModel`・`CAlgCoproductFunctor`・`RightFrameCoproduct` に、次の十三本を加えた十六本。すべて `SerrePositivity.EInfinity.BarrattEccles.Theory` の下。

- `ConcentratedHomotopy`
- `HopfTensorAlgebra`
- `HopfTensorFirstBlock`
- `HopfTensorFunctor`
- `HopfTensorInsertion`
- `HopfTensorNaturality`
- `HopfTensorOperations`
- `HopfTensorUnit`
- `ResolutionAugmentationComparison`
- `TensorActionAssembly`
- `TensorFirstBlockCoherence`
- `TwoColorPermutation`
- `ZeroArity`

新規の［一般∞］移動候補はない。一般のアーベル圏とモノイダル圏の補助は、この実装の隣に置いている。既報の［一般∞］五本は動かしていない。

**続き。** 単位代数の始対象性と左右の単位同型、二つの包含と余積からの指定比較、実際の二色の解像度比較、セル対への移送、強い全関手版への降下が残る。作業木の `HopfTensorUnitObject`・`TensorUnitCoherence`・`HopfTensorUnitPowers`・`HopfTensorUnitors` は次に型検査する候補で、今回の監査・登録候補・コミットには含めない。承認待ちの停止ではなく、§6 の順に包含の証明を続ける。

## 14. 単位・包含・厳密な自然変換の完成と、合計規模による中間停止（11-11 夜）

§13 の最初の区切りを `50d08b622` に保存した後、単位代数と二つの包含を続けた。今回追加する五本は **459 行**。§13 の十三本 767 行と合わせたテンソル側の新規十八本は **1,226 行**、前回の余積の三本 245 行まで含めると二十一本 **1,471 行**。行数は module docstring と空行を含む新規 Lean ファイル全体で数えている。

### 14.1 今回証明したもの

| モジュール | 宣言・内容 |
| --- | --- |
| `HopfTensorUnitObject` | `hopfTensorUnitObject` は Hopf 余単位に沿ってテンソル単位の可換代数を制限する。`hopfTensorUnitIsInitial` は、零入力の余単位が同型ならこの代数が厳密な始対象であることを証明する。`hopfTensorUnitMap` は任意の代数への指定射。自由零代数からの射を、零入力の Schur 包含の同型性で比較している。 |
| `TensorUnitCoherence` | 二列分離・左右の単位子・任意の作用射の整合性を証明する。`tensorActionRightCounit` と `tensorActionLeftCounit` は、テンソル作用の単位子の保存を実際の Hopf 余単位則へ帰着する。 |
| `HopfTensorUnitPowers` | `tensorPowerSeparation_rightUnit`・`_leftUnit`。単位因子の反復積で二列分離を縮約すると、元の左右の単位子のテンソル冪になる。空積も含む。 |
| `HopfTensorUnitors` | `hopfTensorRightUnitor`・`hopfTensorLeftUnitor` は、台の左右の単位子を実際のオペラッド代数の同型へ上げる。零入力の余単位の同型性はこの二つの構成には不要。 |
| `HopfTensorInclusions` | `hopfTensorInl`・`hopfTensorInr` と両変数の全射での自然性、`hopfCoproductComparison`、固定右因子の `hopfCoproductTensorNat` を構成した。`BarrattEccles.barrattEcclesCoproductTensorNat` は零入力の同型性を §13 の証明で供給し、任意の可換環・任意の右因子で実際の模型へ適用する。 |

単位代数・単位同型・包含の構成は任意の Hopf オペラッドで述べ、始対象性と包含だけに零入力の余単位の同型性を要求する。実際の Barratt–Eccles 模型ではこの入力を証明済みで供給する。cofibrancy・K 平坦性を自然変換の構成の仮定には置いていない。

得られた最後の宣言は、通常の代数の圏の **指定された自然変換**

```lean
barrattEcclesCoproductTensorNat (R : Type u) [CommRing R]
    (Y : (operad R).Algebra) :
  modelCoprodWith Y ⟶ hopfTensorWith (hopf R) Y
```

である。比較射の擬同型性、CAlg から D への `FunctorIso`、native な余積錐の余極限性はまだ残る。`EInfinityTheory.coproduct_tensor` を供給し終えたとは扱わない。

### 14.2 検証

`lake build SerrePositivity.EInfinity.BarrattEccles.Theory.HopfTensorInclusions` が成功し、五本すべての対象ビルドを確認した。最終ログでは今回の五本の警告は零。親の既報 `ZeroArity` の `letI` に関する提案二件は残っている。

五本・**72 宣言**を再帰監査し、標準三公理のみだった。§13 の十六本・115 宣言と合わせ、二十一本・**187 宣言**を監査済み。sorry・admit・新規公理・デバッグ出力は零。界面の型と既存の公開宣言は変更せず、新規ファイルだけで証明した。drafts と入口と共有監査スクリプトは編集していない。`ModelCategory SSet` の仮定は使っていない。

対象ビルドと監査は、それぞれ一回の `with_build_lock.sh --wait 3600` で実行し、一回の命令が終わるごとに返却した。整理券は一枚。常駐の要求受付セッションとルートビルドは行っていない。このレーンの監査の鍵は返却済み。

### 14.3 実測による再見積もりと停止条件 1

§12.2 で **400〜650 行**とした「Hopf テンソル代数と二つの包含」は、今回までの実測で **1,119 行**になった。新規十八本 1,226 行から、二色比較の前置き二本 107 行を引いた値である。零入力の増大の厳密な同型性、単位代数の始対象性、左右それぞれの単位子の作用保存、全射での包含の自然性までが必要となり、この部分の当初の見積もりが小さすぎた。

残る部分には §12.2 の承認済みの見積もりをそのまま使い、証明済みの二色の前置き 107 行を差し引く。native な錐の見積もりは §13.1 のまま。実測による次の再計算では、前回三本と前置き二本を二重計上していない。

| 区分 | 実測・残りの見込み |
| --- | --- |
| 検証済みのテンソル側の十八本（二色の前置き二本を含む） | 1,226 行（実測） |
| 二色の自由比較の残り（従来 550〜850 行から検証済み 107 行を引く） | 443〜743 行 |
| 実際のセル対への移送 | 600〜850 行 |
| 強い全関手版への降下 | 200〜350 行 |
| native な余積錐（前回三本 245 行を含む） | 615〜800 行 |
| **合計** | **3,084〜3,969 行（約 3,100〜4,000 行）** |

単に将来の補助が増える可能性ではなく、最初の部分の実測が従来の上限を約 470 行上回ったため、合計約 3,500 行を超える見込みになった。指示書 §6 の **「合計（`coproduct_tensor` と native な錐）が 3,500 行を超えそうなら止める」** に従い、このまとまりで **中間停止し、調整役の判断を待つ**。

停止理由は条件 1 の規模。指定された射を保つ等変な鎖ホモトピー逆の一般の組み立ては §13 で証明済みである。実際の二色の係数複体の射影解像度構造・増大・比較射の照合は残る。セル対への移送では、微分を消す関手と自由関手の余積保存によって二つの既存のセル段を `Free(V ⊕ W)` の表示へ移す経路を検討しているが、この残りの見積もりを小さくできるという証明上の根拠はまだ得ていない。

再開時の次の作業は二色の係数比較である。`sifted`・Tot・段 4 の組み立てには進んでいない。今回の五本まで検証・監査・コミットを揃え、未検査の Lean ファイルを残さずに止める。

### 14.4 取り込み時の登録候補（二十一本）

すべて `SerrePositivity.EInfinity.BarrattEccles.Theory` の下。前回の三本と §13 の十三本、今回の五本を含む。入口と段階 II 監査への登録は調整役が行う。

- `CoproductModel`
- `CAlgCoproductFunctor`
- `RightFrameCoproduct`
- `ConcentratedHomotopy`
- `HopfTensorAlgebra`
- `HopfTensorFirstBlock`
- `HopfTensorFunctor`
- `HopfTensorInsertion`
- `HopfTensorNaturality`
- `HopfTensorOperations`
- `HopfTensorUnit`
- `ResolutionAugmentationComparison`
- `TensorActionAssembly`
- `TensorFirstBlockCoherence`
- `TwoColorPermutation`
- `ZeroArity`
- `HopfTensorInclusions`
- `HopfTensorUnitObject`
- `HopfTensorUnitPowers`
- `HopfTensorUnitors`
- `TensorUnitCoherence`

今回も［一般∞］の移動候補の追加は零。既報の五本の場所はそのまま。


## 15. 二色の係数の射影性と、合計規模による中間停止（11-11 夜）

main `727ab85f3` を `math/bs-impl` に取り込み、指示書 §7 に従って二色係数の比較から再開した。§14.4 の二十一本は取り込み済みなので、今回の登録候補には含めない。今回も界面・既存の公開宣言・drafts・入口・共有監査スクリプトは変更していない。

### 15.1 今回のまとまり

| 新規モジュール | 内容 |
| --- | --- |
| `RepresentationComplex` | 複体の自己射による群作用を、表現の圏の複体と射にする。忘却後の全複体との指定同型、各成分の射の一致を保持する。 |
| `ArityRepresentationChain` | `arityComplexAction` と `arityRepresentationChain`。逆元で右作用を左作用へ直し、既存の `arityDegreeFreeIso` から各鎖次数の射影性を得る。 |
| `ArityRepresentationAugmentation` | 実際の `complexAugmentation` の零次成分を使う、表現の圏の指定増大。鎖複体の忘却と元の正規化鎖の同型も作る。 |
| `ArityProjectiveResolution` | `arityRepresentationAugmentation_forget` は指定増大の忘却を `normalizedChainContraction.hom` と照合する。`arityProjectiveResolution` は任意の可換環上で、実際の arity の複体とこの増大を持つ射影解像度。 |
| `TwoColorCoefficientSource` | ブロック置換の像 `TwoColorGroup` と Σ_m × Σ_n の指定同型、両色への群準同型を定義する。`twoColorSourceResolution` は部分群への制限が射影対象とホモロジーを保つ既存 API を使った、実際の始域の射影解像度。 |
| `RepresentationFreeBasis` | 左正則な自由軌道基底から自由表現への指定同型。基底を送る自由射の台を基底の線形同型と照合する。 |
| `TwoColorBidegreeBasis` | 二つの実際の arity の基底をまとめ、`twoColorBidegreeFreeIso` と `twoColorBidegree_projective` を証明する。 |
| `TwoColorTensorProjective` | 非正双次数の自由性と正次数の零性を使い、実際のコチェインテンソルの全次数の射影性を `twoColorTensorDegree_projective` として証明する。双次数の指定包含を持つ既存の `tensorDegreeRepresentationIsColimit` を使う。 |
| `NonpositiveHomotopyRestriction` | 非正複体の指定されたホモトピーと同値を q ↦ −q に沿って制限する。零次の境界で始域の正一次が零という条件を明示する。 |

群の位数の可逆性・体・標数零は仮定していない。任意の可換基礎環での表現の圏を使い、`ModelCategory SSet` も要求しない。

**まだ得られていないもの。** テンソル側の指定増大を備えた射影解像度、零入力への代入で作る両色の係数射とその等変性・増大の可換性、実際の Hopf 比較との一致、Schur 表示と余不変への移送は残る。特に `twoColorTensorDegree_projective` だけで係数の指定比較のホモトピー同値を供給したとは扱わない。`coproduct_tensor`・native な余積錐・sifted・Tot・段 4 は未完のまま。

### 15.2 実測と残りの見積もり

今回の新規九本は **699 行**（module docstring と空行を含む実測）。検証結果は下の検証欄に記す。二色の前置き二本 107 行は、取り込み済みのテンソル側 1,226 行に含まれる。今回の分と重複して足さない。

§12.2 の「二色の自由比較全体 550〜850 行」は、解像度の比較定理だけでなく、その入力を実際の表現・複体・増大として用意する部分を過小評価していた。今回の準備だけで約 700 行になり、次の三群がまだ要る。

| 二色比較の残り | 見込みと具体的な接続 |
| --- | --- |
| テンソル側の指定増大・解像度 | 180〜260 行。`cochainTensorHomotopyEquiv` と `complexContraction` を合成し、`NonpositiveHomotopyRestriction` で鎖次数へ移し、忘却後の指定増大の一致を照合する。 |
| 両色の係数射・等変性・増大 | 320〜500 行。`Operad.composition` に零入力の単位と一入力の単位を代入する。外側の既存の等変性は `composition_adjacent_block_equivariance` なので、ブロック内の置換を隣接互換で生成する段と、出力の添字同定が必要。Hopf 対角・余単位を通す増大の図式も含む。 |
| 実際の自由比較への照合 | 300〜450 行。指定係数射と `barrattEcclesCoproductTensorNat` の自由生成元上の一致、色付き入力語への分解、群の余不変を取った指定比較を照合し、`resolutionHomotopyEquivOfAugmentation` の順射をこの射のまま移す。 |
| **二色比較の残り小計** | **800〜1,210 行** |

セル対への移送も、既存の K 平坦性の結論だけの適用にはならない。`weightedSemifreeBasis.height` は「入力の重み − コチェイン次数」で、arity の微分も高さを下げる。この高さの商では arity の微分が消える。一方、二色の係数の**鎖**ホモトピー同値を商へ適用するには、arity の微分を残す入力重みのフィルトレーションを使う必要がある。既存の入力重みの安定性・基底・短完全列の補題は再利用するが、段・商と指定比較の同定は新しく要る。

| 実際のセル対への移送の内訳 | 見込み |
| --- | --- |
| 微分を忘れた二つのセル段の余積と、自由代数の和の表示 | 200〜250 行 |
| 入力重みの段と比較射の安定性 | 150〜200 行 |
| 商を係数複体と色付き語の和に同定し、指定比較を照合 | 250〜350 行 |
| 短完全列による段ごとの比較と、網羅的な列の余極限 | 150〜200 行 |
| 任意の cofibrant な対への retract・段の移送 | 100〜150 行 |
| **セル対の小計** | **850〜1,150 行** |

これにより、従来の残りの見積もりをそのまま使うことはできない。

| 全体 | 実測・見込み |
| --- | --- |
| 取り込み済みのテンソル側十八本 | 1,226 行（実測、前置き 107 行を含む） |
| 今回の係数の準備 | 699 行（実測） |
| 二色の自由比較の残り | 800〜1,210 行 |
| 実際のセル対への移送 | 850〜1,150 行 |
| 強い全関手版への降下 | 200〜350 行 |
| native な余積錐 | 615〜800 行（取り込み済み三本 245 行を含む） |
| **合計** | **約 4,400〜5,400 行、中心は約 4,900 行** |

したがって、§7 の **停止条件 1「合計が 4,500 行を超えそうなとき」** に当たり、今回の検証済みのまとまりで中間停止し、調整役の判断を待つ。セル対の見込みは現在 1,200 行以下なので、停止条件 2 による停止とは扱わない。始域の射影解像度とテンソル側の次数ごとの射影性は組めており、指定係数射の残りが既存 API から構成不可能と判明したわけでもない。停止条件 3 による断念とは区別する。

### 15.3 検証・登録候補

対象ビルドは次の一回の `lake build` が成功し、依存する九本すべてを確認した。

```text
lake build SerrePositivity.EInfinity.BarrattEccles.Theory.TwoColorTensorProjective \
  SerrePositivity.EInfinity.BarrattEccles.Theory.NonpositiveHomotopyRestriction
```

最終ログ：`/tmp/bsw16/graded/two-color-projective-06.log`。今回の九本の警告は零。九本・**106 宣言**を `/tmp/bsw16/graded/audit-two-color-resolution.lean` で再帰監査し、標準三公理（`propext`・`Classical.choice`・`Quot.sound`）のみだった。監査ログ：`/tmp/bsw16/graded/audit-two-color-resolution.log`。sorry・admit・新規公理・デバッグ宣言は零。新規 Lean の 100 字超の行と末尾空白、報告書の `git diff --check` の指摘も零。

ビルド・監査はそれぞれ一回の `with_build_lock.sh --wait 3600` で行い、命令の終了ごとに返却した。整理券は一枚。常駐セッション・編集中の鍵の保持・ルートビルドは行っていない。監査の鍵は返却済み。今回の九本と報告書を枝に保存し、未検査の Lean ファイルを残さず、上記の停止条件 1 の判断を待つ。

今回の九本はすべて `SerrePositivity.EInfinity.BarrattEccles.Theory` の下で、15.1 の表のとおり。登録は調整役が行う。新規の［一般∞］移動候補は零。一般の表現・複体の補助も今回の実装の隣に置き、既報の［一般∞］五本は動かしていない。


## 16. 続行後：指定された二色係数の射まで（11-11 夜）

§15 の規模による中間停止の報告後、ユーザーから「続けてください」と指示を受けて再開した。main `375deaa6e` を枝に取り込み（merge `bf017ab0a`）、登録変更を含む最新の作業木で進めた。以下は承認待ちの停止ではなく、検証済みの中間保存である。作業順は §4 のままで、次は指定増大との可換性を閉じる。

### 16.1 証明したもの

今回の新規十本は **853 行**（module docstring と空行を含む）。内容は次のとおり。

| モジュール | 内容 |
| --- | --- |
| `NonpositiveUnitRestriction` | 零次単一複体を q ↦ −q に沿って制限したものと、零次の鎖単一複体の同型。零次成分は元の `singleObjXSelf` を保持する。 |
| `RepresentationChainAugmentation` | 群不変な元の増大から、表現の圏の鎖複体の指定増大を作る。`representationChainAugmentation_forget` は忘却後の射を元の制限と照合し、擬同型性を表現の圏へ反映する。 |
| `TwoColorTensorAugmentation` | 実際の `complexAugmentation` 二つのテンソルと単位子から、`twoColorTensorChainAugmentation` と `twoColorTargetResolution` を得る。元の二つの収縮のテンソルを使い、群同変な収縮を仮定しない。 |
| `TwoColorResolutionComparison` | 始域の制限した自明表現を終域と同定する。増大を保つ指定射から、同じ順射を持つ等変な鎖ホモトピー同値を作る。**増大の可換性は引数に明示**している。 |
| `TensorUnitAdjacent` | テンソル単位の冪の隣接交換と、単位と同型な対象の冪の隣接交換が恒等射になる。 |
| `NullaryFamilyAdjacent` | 実際の arity 0 の増大の同型を用い、零入力係数の有限族の隣接交換を恒等射と同定する。 |
| `NullaryPrefixDelete` | 指定された零入力の単位を反復合成へ代入する係数射 `nullaryPrefixDelete`。消去する入力の任意の置換に対する不変性を、隣接互換による生成から証明した。 |
| `NullaryPrefixTail` | 残した尾の任意の置換に関する、同じ係数射の等変性。空の出力ブロックを除く arity の移送も照合する。 |
| `TwoColorCoefficientProjections` | ブロック交換と零入力への代入から、実際の両色への射影 `twoColorLeftCoefficient`・`twoColorRightCoefficient` と、そのブロック内置換に関する等変性を構成した。 |
| `TwoColorCoefficientMap` | 実際の Hopf 対角の後に二つの射影を適用する `twoColorCoefficientComparison`。二色部分群の実際の作用との可換性を証明し、`twoColorCoefficientChainMap` として二つの解像度の鎖複体の間の射へ移した。 |

任意の可換基礎環での主張であり、群の位数の可逆性・標数零・`ModelCategory SSet` は仮定していない。終域の射影解像度も、始域と同じ自明表現を値に取る。指定された係数射を解像度の任意の lift に置き換えてはいない。

### 16.2 検証と未完部分

`lake build SerrePositivity.EInfinity.BarrattEccles.Theory.TwoColorCoefficientMap` が成功し、依存する今回の十本を確認した。最終ログは `/tmp/bsw16/graded/two-color-map-01.log`。新規十本の警告は零。既報 `ZeroArity` の `letI` に関する提案二件は残る。

十本・**129 宣言**を `/tmp/bsw16/graded/audit-two-color-map.lean` で再帰監査し、標準三公理のみだった。ログは `/tmp/bsw16/graded/audit-two-color-map.log`。sorry・admit・新規公理・デバッグ宣言は零。前回の九本・106 宣言と合わせ、今回までの未取り込みの十九本・**235 宣言**を監査済み。二十一本の取り込み済みのものを再登録候補へ重ねていない。

**未完**：`twoColorCoefficientChainMap` が指定増大を保つこと、得られる等変な鎖ホモトピー同値を自由代数の指定比較へ移すこと、実際のセル対への移送、強い全関手版と native な余積錐が残る。`twoColorResolutionHomotopyEquiv` に実際の指定射と増大の可換性を供給し終えたとは扱わない。`coproduct_tensor`・sifted・Tot・段 4 は未完のまま。

次は、零入力への射影と増大の可換性を、オペラッド射が反復合成を保つことへ帰着して進める。その自然性の補助 `OperadMorphismInsertion.lean` は編集中で、今回の十本の保存・監査・登録候補には含めない。実際のセル対への移送にはまだ着手しておらず、1,200 行の上限は引き続き確認する。

現在までの実測は、取り込み済み二十一本 1,471 行、§15 の九本 699 行、今回の十本 853 行、計 **四十本・3,023 行**。前回報告した全体規模の見込みに対する続行指示の下で作業している。

界面の型・既存の公開宣言・drafts・入口・共有監査スクリプトは変更していない。鍵は各一回のビルド・監査だけ `--wait 3600` で取り、終了ごとに返却した。監査の鍵も返却済み。常駐セッション・編集中の鍵の保持・ルートビルドは行っていない。

### 16.3 取り込み時の登録候補

今回の十本は 16.1 の表の一覧で、すべて `SerrePositivity.EInfinity.BarrattEccles.Theory` の下。前回 `4237883e9` の九本（§15.1）も現在の main では未登録なので、次の取り込みでは **十九本**が候補となる。入口・共有監査への登録は調整役が行う。新しい［一般∞］移動候補は零。既報の五本はそのまま。


## 17. 実際の二色係数比較の等変な鎖ホモトピー同値（11-11 夜）

§16 の中間保存 `1364ddf10` に続け、指定増大との可換性を閉じた。今回の新規六本は **453 行**。以下も承認待ちの停止ではなく、検証済みの中間保存である。

| モジュール | 内容 |
| --- | --- |
| `OperadMorphismInsertion` | オペラッド射の成分と arity の移送、一段の反復合成の自然性。 |
| `OperadMorphismComposition` | 任意のオペラッド射が `composeFirstInputs` を保つ。全内側 arity と未代入の尾を許し、零入力も含む。 |
| `CommutativeComposition` | 可換オペラッドの反復合成を、指定された単位族の縮約として計算する。 |
| `NullaryPrefixAugmentation` | 零入力への指定代入射 `nullaryPrefixDelete` が実際の増大を保つ。単位からの係数族の挿入と両因子の射の比較も含む。 |
| `TwoColorCoefficientAugmentation` | 両色への射影が増大を保ち、実際の Hopf 比較 `twoColorCoefficientComparison` と `twoColorTensorAugmentation` の合成が `complexAugmentation` に一致することを証明した。 |
| `TwoColorCoefficientEquivalence` | `twoColorCoefficientChainMap_augmentation` が二つの射影解像度の指定増大を照合する。これを供給した `twoColorCoefficientHomotopyEquiv` は、任意の可換環上で実際の係数鎖写像を順射に持つ等変な鎖ホモトピー同値。擬同型性も得る。 |

**条件付きの比較補題への入力は、ここで実際の射について供給済みになった。** `twoColorCoefficientHomotopyEquiv` 自体に、射影解像度・増大の可換性・比較射・K 平坦性・群の位数の可逆性を外部入力として残していない。順射を任意の lift に取り替えてもいない。したがって、§7 の停止条件 3 に挙げられていた「二色の係数複体の射影解像度・増大・比較射の照合」の組み立ては、実際の鎖複体について完了した。

対象ビルド `lake build SerrePositivity.EInfinity.BarrattEccles.Theory.TwoColorCoefficientEquivalence` が成功し、新規六本の警告は零。ログは `/tmp/bsw16/graded/two-color-equivalence-01.log`。既報 `ZeroArity` の提案二件だけが残る。六本・**26 宣言**の再帰監査は標準三公理のみ（`/tmp/bsw16/graded/audit-two-color-equivalence.log`）。sorry・admit・新規公理・デバッグ宣言は零。対象ビルドと監査の鍵は一回ずつ取り、命令終了ごとに返却した。

次は、この指定された等変ホモトピー同値を整数コチェイン次数に戻し、テンソルと余不変を取る関手へ通す。編集中の `NonpositiveExtension.lean` は、今回の六本の検証・監査・保存には含めない。自由代数の指定比較との一致、実際のセル対への移送、全関手版の同型、native な余積錐はまだ残る。sifted・Tot・段 4 へは進んでいない。

現在までの実測は **四十六本・3,476 行**。今回の六本もすべて `SerrePositivity.EInfinity.BarrattEccles.Theory` の下で、登録候補は上の表の一覧。§15 の九本と §16 の十本も main 未取り込みなので、次の取り込み時の候補は計 **二十五本・261 宣言**となる。入口と共有監査への登録は調整役が行う。既存の公開宣言・界面の型・drafts は変更していない。新規の［一般∞］移動候補は零。実際のセル対の移送は未着手で、1,200 行の上限は継続して確認する。


## 18. 指定係数比較の整数次数とテンソル余不変（11-11 夜）

§17 の中間保存 `07c990e8b` の後、係数の同値を元の整数コチェイン次数へ戻した。今回の新規三本は **261 行**。

- `NonpositiveExtension`：非正次数への制限の延長と元の複体との指定同型。正次数では零対象の同型を使い、射との自然性も証明した。
- `NonpositiveHomotopyExtension`：制限間のホモトピー同値を元の複体へ戻す。順射が元の指定射の制限なら、戻した同値の順射をその元の射そのものにする。
- `TwoColorCochainEquivalence`：実際の `twoColorCoefficientCochainMap` を順射とする整数次数の等変なホモトピー同値。任意の二色部分群の表現をテンソルして余不変を取る関手を適用した同値も構成した。任意の可換環・任意の表現で使え、テンソルする表現の平坦性・射影性は不要。

`lake build SerrePositivity.EInfinity.BarrattEccles.Theory.TwoColorCochainEquivalence` が成功し、新規三本の警告は零（ログ `/tmp/bsw16/graded/two-color-cochain-equivalence-02.log`）。三本・**53 宣言**を再帰監査し、標準三公理のみ（`/tmp/bsw16/graded/audit-two-color-cochain.log`）。sorry・admit・新規公理・デバッグ宣言は零。鍵は各一回のビルドと監査だけ取得し、命令の終了ごとに返却した。

これも承認待ちの停止ではなく、検証済みの中間保存。次は、色付き入力の Schur 表示と実際の自由代数の指定比較をこの係数同値に照合する。モデルの係数比較の等変性・指定増大・順射の照合自体は完了している。実際の自由代数の比較とセル対への移送、`coproduct_tensor` の全関手版、native な余積錐はまだ完了していない。sifted・Tot・段 4 には進んでいない。

現在までの実測は **四十九本・3,737 行**。今回の三本も `SerrePositivity.EInfinity.BarrattEccles.Theory` の下で、上の一覧を登録候補とする。§15〜§18 を合わせた未取り込みの候補は **二十八本・314 宣言**。共通入口・監査への登録は調整役が行う。既存の公開宣言・界面の型・drafts・入口・共有監査スクリプトを変更していない。新規の［一般∞］移動候補も零。


## 19. 誘導係数への接続と、セル対の規模による中間停止（11-11 夜）

### 19.1 今回までに閉じた係数比較

§18 の `36249aefe` に続け、`TwoColorInducedCoefficients.lean`（**79 行**）を追加した。Mathlib の `Rep.coinvariantsTensorIndNatIso` を実際の arity の表現の複体へ適用する。`twoColorInducedSourceIso` は、二色部分群から誘導した表現を持つ対称群の係数の余不変を、二色部分群へ制限した係数の余不変へ比較する。関手の合成の複体上の同型も明示した。

`twoColorInducedCoefficientHomotopyEquiv` は、その指定同型の後に元の係数比較を適用する順射を持つ。これは色付き入力語の Schur 分解の成分であり、実際の自由代数全体の比較の擬同型性を証明済みとは扱わない。任意の可換基礎環・任意の二色部分群の表現での主張で、平坦性と群の位数の可逆性を要求しない。

対象ビルドが成功（`/tmp/bsw16/graded/two-color-induced-04.log`）、新規モジュールの警告は零。**14 宣言**の再帰監査は標準三公理のみ（`/tmp/bsw16/graded/audit-two-color-induced.log`）。既報 `ZeroArity` の提案二件は残る。今回の続行で追加した分は、§16 の十本・853 行、§17 の六本・453 行、§18 の三本・261 行、今回の一本・79 行、計 **二十本・1,646 行・222 宣言**。全て対象ビルドと再帰監査を確認した。§15 の九本も含めた未取り込みの候補は **二十九本・2,345 行・328 宣言**。取り込み済みの二十一本を含む現在までの全実測は **五十本・3,816 行**。

### 19.2 セル対へ移すために実際に足りないもの

§15 ではセル対への移送を 850〜1,150 行とした。しかし、係数比較を閉じて移送先の商を具体化すると、その見積もりは小さすぎた。次の既存 API の実際の型・定義を確認した。

1. `OperadWordEvaluation.evaluatedWord_d_mem` と `PowerWordEvaluation.powerWordValue_d_mem` は、微分後も**同じ重みの上限以内**に入る主張。必要な「元の微分から係数微分の項を引いた残りが、入力重みを真に下げる」という主張は供給していない。前者の証明では係数微分の項と入力微分の項を足して同じ上限に入れている。この分解は再利用するが、入力側の真の低下と先頭の係数微分の一致を、新しい主張として示す必要がある。
2. `InfinityCategories/Derived/SemifreeBasisLayers.lean` の `ComplexSemifreeBasis.layerComplex` は**全微分を零に置く定義**であり、`highProjection_differential` も高い射影が零となる主張。今回必要な入力重みの商には係数の微分が残るため、この商の複体と商射をそのまま流用できない。既存の公開宣言を変更せず、非零の係数微分を持つ層・座標・商射の構成が要る。
3. `HomologicalAlgebra/ModuleSubcomplex.lean` の `quotient` と `shortExact` は再利用できる。ただし、それだけで入力重みの層の座標、二つの実際のセル代数の余積・テンソルの商の同定、指定比較の商射との可換性が得られるわけではない。
4. 既存の `Complexes/Perturbation.lean` の `perturbComplex` は、追加する cochain の閉性と二乗零を個別に受け取る。今回の入力重みを下げる項へ、そのまま適用して以下の構成を省けることは確認していない。この未検証の節約を見積もりには入れない。

前回は、係数微分を残す層の新規構成と、入力微分の真の低下の証明を、商の同定の短い一項にまとめすぎていた。特に、既存の高さの商が零微分であることを変更せずに、入力重みの商へ使うという省略はできない。

### 19.3 セル対だけの再見積もりと停止条件 2

以下は**実際のセル対への移送に必要な新規 Lean 全体**の見込みで、汎用の補助もこの内訳に数える。他の置き場所へ移して行数から除くことはしない。色付き入力語の Schur 分解・自由代数の指定比較の残り、強い全関手版、native な余積錐は、以下の見積もりには含めていない。

| セル対への移送の構成 | 新しい見込み |
| --- | --- |
| 微分を忘れる関手による実際の余積の移送、両方のセル生成元の和の表示 | 200〜260 行 |
| 入力語の微分の真の重みの低下と、係数微分を残す先頭項の一致 | 210〜300 行 |
| 係数微分を持つ入力重みの層・座標・商射 | 180〜240 行 |
| 重みの段の複体、包含、指定比較の段への制限、網羅性 | 120〜180 行 |
| 実際の余積側・テンソル側の商を係数と語の表示に同定し、商の指定射を照合 | 300〜380 行 |
| 短完全列による段ごとの比較から、網羅的な列の余極限での擬同型へ移す | 200〜260 行 |
| 任意の cofibrant な対へのセル表示・retract の移送 | 100〜150 行 |
| **セル対の合計** | **1,310〜1,770 行（約 1,300〜1,800 行）** |

これは測定済みの行数ではなく、上の不足する主張を分けた実装見積もりである。現在の経路では中心約 1,500 行となり、§7 の **停止条件 2「実際のセル対への移送が 1,200 行を超えそうなとき」** に当たる。今回の検証済みの係数比較のまとまりで**中間停止し、調整役の判断を待つ**。

§15 の合計規模による停止については、その後の「続けてください」の指示を受けて上記の係数比較を続けた。今回の停止は、その以前の合計上限を再び理由にしたものではなく、別に指定されているセル対の 1,200 行の条件による。解像度・指定増大・実際の比較射と等変な逆は §17〜§18 で構成済みなので、停止条件 3 による断念でもない。

再開時は、残る色付き Schur 分解と実際の自由代数の比較を閉じたうえで、上のセル対の移送へ進む。`coproduct_tensor` の全関手版、native な余積錐、sifted、Tot、段 4 はまだ未完。今回までの本体の追加には sorry・admit・新規公理・デバッグ宣言を残していない。界面の型、既存の公開宣言、drafts、共通入口、共有監査スクリプトは変更していない。全てビルドと監査の一回ごとに鍵を取り、終了ごとに返却した。未検査の Lean ファイルは残さず、監査の鍵も返却済み。

### 19.4 次の取り込み時の登録候補（二十九本）

全て `SerrePositivity.EInfinity.BarrattEccles.Theory` の下。§15〜§19 の未取り込み分で、main 登録済みの §14.4 の二十一本は含めない。入口と監査への登録は調整役が行う。

- `RepresentationComplex`
- `ArityRepresentationChain`
- `ArityRepresentationAugmentation`
- `ArityProjectiveResolution`
- `TwoColorCoefficientSource`
- `RepresentationFreeBasis`
- `TwoColorBidegreeBasis`
- `TwoColorTensorProjective`
- `NonpositiveHomotopyRestriction`
- `NonpositiveUnitRestriction`
- `RepresentationChainAugmentation`
- `TwoColorTensorAugmentation`
- `TwoColorResolutionComparison`
- `TensorUnitAdjacent`
- `NullaryFamilyAdjacent`
- `NullaryPrefixDelete`
- `NullaryPrefixTail`
- `TwoColorCoefficientProjections`
- `TwoColorCoefficientMap`
- `OperadMorphismInsertion`
- `OperadMorphismComposition`
- `CommutativeComposition`
- `NullaryPrefixAugmentation`
- `TwoColorCoefficientAugmentation`
- `TwoColorCoefficientEquivalence`
- `NonpositiveExtension`
- `NonpositiveHomotopyExtension`
- `TwoColorCochainEquivalence`
- `TwoColorInducedCoefficients`

新規の［一般∞］移動候補は零。既報の五本は動かしていない。

## 20. 二色の入力語の指定分解と、合計規模による中間停止（11-11 夜）

### 20.1 再開と今回の範囲

main `cba436208` を `math/bs-impl` へ fast-forward で取り込み、指示書 §8 を読んだ。§15〜§19 の二十九本は main に入っているため、今回の登録候補には含めない。順序を守り、セル対の前に、残る色付き Schur 分解と自由代数の指定比較を調べた。

新規の `BinaryTensorWords` は、`power (X ⊞ Y) n` を二色の入力語へ分ける指定包含・指定射影を構成する。各包含と同じ語の射影の合成は恒等射、異なる語の射影との合成は零、全射影と包含の合成の和は恒等射となる。`BinaryTensorBicone` は、**実際の和のテンソル冪を頂点とする**双錐の極限・余極限性と、指定包含による射の外延性を与える。一般の加法的モノイダル圏での主張で、平坦性や群の位数の可逆性を要求しない。

`BinaryTensorColors` は再帰的な語と `Fin n → Bool` の指定全単射を構成する。`BinaryTensorColorAction` は逆置換による左作用と左因子の個数の不変性を与える。`BinaryTensorBlocks` は左の m 因子の後に右の n 因子を置く標準語を定め、そのテンソルを `power X m ⊗ power Y n` へ結合子で同定する。`BinaryTensorNaturality` は、左右の入力の射について、語ごとの包含・射影と実際の和のテンソル冪の射との自然性を示す。

これらは色付き分解の基盤であり、まだ**対称群に等変な誘導表示の同型でも、実際の自由代数の指定比較の擬同型性でもない**。セル対、強い全関手版、native な余積錐、sifted、Tot、段 4 は未完。

### 20.2 係数比較から実際の自由比較までに残る接続

`twoColorInducedSourceIso` は、**入力の表現が既に `Rep.ind` の形で与えられている場合**の Shapiro の比較である。`power (K ⊞ L) r` の色付き成分をその誘導表現にする同型は供給しない。また、今回の有限直和の余極限性だけでは、その成分の指定射が `twoColorCoefficientComparison` になるとは結論できない。

既存 API と照合した残りは次のとおり。`TensorPowers.adjacentIso` の自然性、`tensorFamilyAdjacentIso`、`Rep.indResHomEquiv` と `Representation.IndV.hom_ext`、軌道と安定化群の全単射、`schurDegreeBidegreeIso`、`twoColorInducedCoefficientHomotopyEquiv` は再利用する。これらを使う新規の証明・座標の照合を次の見込みに含める。既存ライブラリの行数は数えない。

| 自由比較の残る構成 | 見込み |
| --- | --- |
| 語の指定包含の置換との両立、標準ブロック上の指定部分群の作用の照合 | 160〜220 行 |
| 色の個数を固定した軌道と、標準語の安定化群の同定 | 120〜180 行 |
| 指定包含から誘導表現の射・逆を作り、複体上の同型とする | 260〜340 行 |
| 実際の Schur 複体の始域・テンソル側の分解と、arity・双次数の再添字付け | 220〜300 行 |
| 自由代数の指定 Hopf 比較と係数比較を包含上で照合し、擬同型へ接続 | 180〜250 行 |
| **今回の基盤の後の自由比較の残り** | **940〜1,290 行** |

これは未実装部分の見積もりであり、下限を証明したものではない。とくに `Rep.indResHomEquiv` で順射を作るだけでは足りず、逆と指定包含上の二つの恒等式が要る。`schurDegreeBidegreeIso` は次数ごとの表示であるため、複体の同型としての微分との両立も残る。これらを未検証の定義的等しさとして省かない。

§19 ではセル対の不足を分けて見積もった一方、その表の外にある色付き Schur 分解・自由比較の残りの内訳を更新しきれていなかった。今回の増分は係数の等変な解像度比較のやり直しではなく、この入力の誘導表示と実際の指定射への接続である。

### 20.3 合計の停止条件とセル対の状態

セル対への移送の実装は**未着手、追加零行**。§19.3 の七行の構成はいずれも未着手で、見込み 1,310〜1,770 行は据え置く。入力微分の真の低下・係数微分を残す商が既存の定義を変えずに作れないと判明したわけではない。セル対 2,000 行の停止条件にも、セル対完了の必須停止点にもまだ達していない。

合計は下の検証後の実測に、上の自由比較の残り、§19.3 のセル対、§12.2 の全関手版、§13.1 の native な錐の残りを足して判断する。native な錐の証明済み三本 245 行は既存の全実測に含まれているため、残りは 370〜555 行だけを数える。

| 区分 | 実測・残りの見込み |
| --- | --- |
| main に入った五十本（§19.1） | 実測 3,816 行 |
| 今回の六本（docstring・空行を含む） | 実測 490 行 |
| **現在までの全実測** | **五十六本・4,306 行** |
| 自由比較の残り（§20.2） | 940〜1,290 行 |
| セル対（§19.3、未着手） | 1,310〜1,770 行 |
| 強い全関手版への降下（§12.2） | 200〜350 行 |
| native な余積錐の残り（§13.1、既存 245 行を除く） | 370〜555 行 |
| **全体の再見積もり** | **7,126〜8,271 行（約 7,100〜8,300 行）** |

この見込みは §8 の**停止条件 2「合計が 7,000 行を超えそうなとき」**に当たる。そのため、今回の基盤の検証と報告を区切りに中間停止し、調整役の判断を待つ。セル対を完了したという報告ではない。セル対完了時の、§19.3 の各行の見込みと実測の差の報告は、その必須停止点に残る。二色の係数比較の同値が作れないという停止でもなく、既存定義の変更を求めるものでもない。

### 20.4 検証と次の取り込み時の登録候補

登録候補は次の六本だけ。全て `SerrePositivity.EInfinity.BarrattEccles.Theory` の下。共通入口と段階 II の共有監査への登録は調整役が行う。

- `BinaryTensorWords`（132 行）
- `BinaryTensorBicone`（61 行）
- `BinaryTensorColors`（76 行）
- `BinaryTensorColorAction`（61 行）
- `BinaryTensorBlocks`（82 行）
- `BinaryTensorNaturality`（78 行）

対象ビルドは `/tmp/bsw16/graded/binary-tensor-words-08.log` で成功した（対象の新規六本の警告零）。六本の **121 宣言**の再帰監査は `/tmp/bsw16/graded/audit-binary-tensor.log` で成功し、標準三公理のみ。本体の追加には sorry・admit・新規公理・デバッグ宣言を残していない。既存の公開宣言、界面の型、drafts、共通入口、共有監査スクリプトは変更していない。他レーンとのファイルの重複も零。新規の［一般∞］移動候補は零で、既報の五本は動かしていない。ビルド・監査はそれぞれ `--wait 3600` で一枚だけ整理券を出し、実行の終了ごとに鍵を返した。未検査の Lean ファイルは残さず、監査の鍵も返却済み。

## 21. 夜の紙の検討：経路 A／B、sifted 保存、A2・A7 の要求（11-11）

### 21.1 今回の作業と結論

調整役の指示と main の指示書 §9（読んだ時点の main `93759d8a9`）に従い、**Lean の作成・変更・ビルド・監査は行わない**。main は参照だけにし、枝への merge も行っていない。本節だけを変更する。§20 の六本の取り込み後の登録ビルドは調整役の持ち分。

数学的な経路としては、B は §19.3 のセル対の七項目を全て置き換えられる。ただし、代わりに導来自由・忘却随伴の bar 分解の実現と、指定された比較をその実現に沿って延ばす証明が必要になる。通常の代数のモナド性から、この導来の主張を証明済みとはできない。現存 API の段階では **B が A より小さいとはまだ判断できない**。先に sifted の保存の橋の範囲を確かめる必要がある。

以下の行数は全て**未実装・型検査前の見積もり**。docstring・補助・自然性・指定錐の照合も含める。上限を変更する提案や実装再開の承認とは扱わない。A2・A7 自身の残る prismatic な証明と G12・Tot は、E2 の比較見積もりに混ぜない。

### 21.2 共通の基盤と不足

`C := CAlg_R R`、`D := derivedInfinityCategory R`、`U := cAlgForgetDerived R` と書く。導来自由関手 `F := cAlgFreeDerived R` と `cAlgFreeForgetDerivedAdjunction R : F ⊣ U` は **本体で無条件に構成済み**（`BarrattEccles/FreeProbeDerivedFreeForget.lean:36–40`）。B のためにこの随伴を一から作る必要はない。`free_isLeftQuillen`・`freeProbeFunctor_cofibrant`・`freeProbeFunctor_map_quasiIso`（`FreeProbeFunctor.lean`）で厳密な自由代数と接続できる。`cAlgForgetDerived_conservative` も証明済み。

共通して、次はまだ必要である。

| 区分 | 再利用と不足 | 残りの見込み |
| --- | --- | --- |
| 自由代数の指定比較 | §20 の六本、`twoColorInducedCoefficientHomotopyEquiv`、Schur の次数表示を再利用。色の軌道・安定化群、誘導表示の複体の同型、実際の Hopf 射との照合は §20.2 の五行のまま残る | 940〜1,290 行 |
| native な二項余積錐 | `barrattEcclesCoprodWith`・`RightFrameCoproduct` と指定包含を再利用。指定頂点・二脚を持つ `IsColimitCone` はまだない。§13.1 の未完分であり、B でも使う | 370〜555 行 |
| 全関手の指定自然比較 | 厳密な `barrattEcclesCoproductTensorNat`、`cAlgLocalizationSource_descendIso` などを再利用。実際の `tensorWith` と比較し、各右因子について `FunctorIso` にする仕上げ。下記 B の実現に沿った可逆性の証明は別に数える | 200〜350 行 |
| **共通の残り C** | 既存 4,306 行は再計上しない | **1,510〜2,195 行** |

自由比較は**任意の cofibrant な入力複体**の自由 E∞ 代数まで届く形が要る。入力微分を零とする場合だけで終えると、B の反復 `FU` の各項へ適用するために別の移送が残る。§20.2 の「複体の同型・指定射」の照合にこの点を含める。

通常の離散多項式環 `R[X]` と、D(R) の生成元に自由な E∞ 代数 `F(R[0])` を同じものとして扱わない。後者には対称群の導来余不変が現れ、一般の基礎環では離散多項式への置換はできない。A2 の `AnimatedAlgebra` は多項式環からの sifted 完成であり、その像だけで C の全対象を生成したとはまだ言えない。B の全界面の供給には、導来自由関手 F の分解を使う。

### 21.3 経路 A：自由比較をセル対へ移す

証明の順序は、共通の自由比較、§19.3 のセル対、任意の cofibrant 対への retract、指定自然比較の局所化への降下となる。セル対で扱う射は新しく選んだ同値ではなく、既存の Hopf テンソルへの指定射である。

再利用は `CellStageGradedBasis`・`CellStageFreeNaturality`・`CellStageGeneratorDifferential`、`OperadWordEvaluation`・`PowerWordEvaluation`、`ModuleSubcomplex.quotient`・`shortExact`、cofibrant な台の K 平坦性、セル表示と retract。§19.2 のとおり、重みの「非増大」だけでは足りず、係数微分を引いた後の真の低下と、係数微分を残す層が必要になる。

§19.3 の七行は全て未着手で、200〜260、210〜300、180〜240、120〜180、300〜380、200〜260、100〜150 行、計 **1,310〜1,770 行**のまま。ここを別の一般補助へ移して計上から除かない。A は `forget_preservesSifted` や bar の実現に依存せず、この欄を先に閉じられる利点がある。一方、最後に E2 全体を完成するには sifted の保存も別に必要であり、その費用を隠さない。

### 21.4 経路 B：自由比較を単体的な分解で延ばす

必要な主張を次の順で分ける。

1. **導来 bar の図式と増大。** 随伴 F ⊣ U から、各代数 X に対し次数 n が `(FU)^(n+1) X` である増大単体的図式 B(X) を作る。図式全体・増大は X とその射について自然にする。`ComonadSimplicialResolution.diagram`・`augmentation` は通常の 1 圏の余モナドについて構成済みで、面・退化の計算を再利用できる。しかし、準圏上の随伴からこの図式への接続と全 coherence は別の仕事。
2. **同じ増大の実現。** U B(X) の追加退化による分裂を使い、その指定増大の幾何学的実現が UX であることを示す。C 側の実現の存在、U による保存、保存的性質を組み合わせ、B(X) の指定増大自身を X を頂点とする余極限錐にする。C の実現の存在を U の「保存」だけから取り出すことはしない。具体的な模型の hocolim から native な錐を構成するか、別に存在を供給する必要がある。
3. **比較の両辺が各変数の実現を保つ。** `x ↦ U(x ⨿ y)` は、U の実現保存と native な余積錐を使う。固定右因子との余積が通常の左随伴であるとは主張しない。sifted 形状の弱可縮性により定値 y の余極限が y となることと、二つの余極限の交換で示す。`x ↦ Ux ⊗^L Uy` は D(R) の導来テンソルの実現保存を使う。この保存は `coproduct_tensor` 自身から導かず、D の閉モノイダル構造または K 平坦な模型から独立に示す。
4. **自由×自由から全体へ。** B(X)・B(Y) の各次数は自由な対象であるため、指定された自由比較を適用する。まず一変数、次に他変数の実現を取る。対角だけで済ませるなら、Δᵒᵖ の対角の共終性と、二重実現の比較も必要になる。別々の二回の実現ならこの追加の対角照合を省ける。指定比較の自然性により各次数の射を同じ比較の実現として結ぶ。
5. **強い形。** 各点で逆を選ぶ方法は使わず、既存の自然比較の各成分が可逆であると示し、`FunctorIso` にする。X・Y・それらの射に関する増大の自然性も保持する。頂点ごとの同型を作るだけで終えない。

この経路が通れば、**§19.3 の七行全部が不要**になる。具体的には入力重みの真の低下、係数微分を残す商、段ごとの短完全列、網羅的余極限、最後のセル対の retract を証明しない。既存の K 平坦性の証明は自由入力の模型・導来テンソルの比較に再利用するが、A の未着手の重みの層は B の前提に持ち込まない。

| B に特有の仕事（共通 C・下記 S を除く） | 見込み |
| --- | --- |
| 導来随伴の反復と bar の全図式・指定増大・自然性 | 200〜350 行 |
| U の下の分裂、指定増大の実現、C 側の存在と保存的性質の適用 | 350〜550 行 |
| 各項の導来自由対象を厳密な自由比較へ接続する | 200〜350 行 |
| 固定余積・導来テンソルの実現保存、二回の実現による指定比較の可逆性 | 350〜550 行 |
| 全図式の射と増大の整合、関手の可逆性の判定への接続 | 200〜350 行 |
| **B 固有の残り T** | **1,300〜2,150 行** |

通常の `forget_monadic` は、相対圏の弱同値を考えない Beck のモナド性である。それを「∞ 圏で U がモナド的、bar は U により実現される」と読み替えない。B は、これらを別に閉じれば数学的に循環しない経路である。U の実現保存を余積＝テンソルから証明したり、C の実現の存在を未供給の G12 に黙って委ねたりすれば循環・未供給入力になる。

### 21.5 sifted 保存の段 0：型の射程、再利用、不足

目標の実際の型は `PreservesSmallSiftedColimits (cAlgForgetDerived R)`。`F2/Presentable/SiftedColimitPreservation.lean:24` の定義は、小さい **任意の sifted な単体集合形状 I**、任意の図式 D、任意の指定 native な余錐 c を量化し、c の像の余極限性を要求する。通常の小圏 J の厳密な図式、あるいは対象の同値だけではこの型に届かない。

| 確認した既存の宣言 | 実際に得られるもの／残るもの |
| --- | --- |
| `Operad.Algebra.forget_createsSiftedColimitsOfShape`、`forget_createsFilteredColimitsOfShape`（`Operad/AlgebraSiftedColimits.lean`） | 通常の厳密な余極限の創出。図式を cofibrant に置換した後の hocolim の保存や、native な全余錐の保存までは主張しない |
| `Operad.Algebra.forget_monadic`（`AlgebraMonadic.lean`） | 通常のモナド性。B の導来 bar の実現とは区別する |
| `BarrattEccles.Diagram.projectiveModelCategory`・`weakEquivalence_iff`（`DiagramModel.lean`） | 厳密な図式の置換と対象ごとの擬同型の判定。U が projective cofibrant 図式を cofibrant 図式へ送るとはまだ言えない |
| `DiagramModel.HomotopyColimit.functor`・`comparison`、`PointwiseColimitComparison`、`QuillenColimitComparison` | 具体的 hocolim と通常の colim の比較。`QuillenColimitComparison` は左 Quillen 関手用で、右 Quillen U にはそのまま適用できない |
| `FilteredHomotopyColimit.comparison_weakEquivalence_of_filtered`・`exists_filtered_comparison` | 仮定の κ 以上に十分 filtered な場合。全ての通常の filtered 図式に使えると読み替えない。加群の filtered 余極限の完全性から擬同型の保存を別に接続する |
| `HomotopyWeight.pointwiseRealization`・`tensorRealization`・`realization_map_frame_weakEquivalence`、`FrameRealizationLifting.map_monomorphism`・`map_anodyne` | 同じ frame の実現と射の比較の部品。代数の実現を忘却したものと、複体の実現との同じ脚を持つ比較は未供給 |
| `CAlgUnderlyingDerivedComparison.algebraReplacementUnderlyingDerivedIso`、`algebraCAlgSource_underlyingDerivedIso` | 実際の U と厳密な台の図式を結ぶ自然同型。実現を比較するときの入口に使う |
| `cAlgFreeForgetDerivedAdjunction`、`cAlgForgetDerived_conservative` | 実際の導来随伴と保存的性質。実現保存そのものではない |
| `SiftedSimplexCategory`、`SiftedContractibility.isWeaklyContractible_of_sifted`、`PreservesSmallSiftedColimits.of_functorIso` | Δᵒᵖ の sifted 性、定値図式、関手の同型による保存の輸送に使う |
| `sigmaComparison_isIso_of_filtered_geometric`（`SigmaFilteredGeometricDetection.lean`） | 始域が `SigmaPresheafInfinity C` の比較の判定。CAlg の全対象へそのまま適用できない。filtered と幾何学的実現の二つの保存から、今回の全 sifted 保存への一般の接続は別に要る |

幾何学的実現の模型の候補は、実際の単体的代数の Reedy/projective 置換と frame の重み付き実現である。**任意の単体的代数の通常の colim を取るだけでは、導来実現にならない**。U の実現比較では、テンソルの Eilenberg–Zilber 型の比較または明示的な latching の議論で、同じ増大・脚・射を照合する必要がある。この比較は二項の `coproduct_tensor` を前提とせず、オペラッドの各 arity と有限テンソル冪から示すことを独立の目標にする。

`ColimitMapComparison.diagramSourceComparison_weakEquivalence` は `[ModelCategory SSet]` を要求する版なので使わない。既存の frame による単体的ホモトピー同値の比較を使い、その仮定を追加しない。

| sifted 保存 S の不足 | 見込み |
| --- | --- |
| 厳密な Δᵒᵖ 図式の hocolim と、指定脚を持つ native な実現錐の橋 | 550〜850 行 |
| 代数の実現と台の複体の実現の比較、arity と微分・射の整合 | 500〜800 行 |
| 任意の coherent な単体的図式を上の厳密な計算へ移す比較と、その指定錐の照合 | 450〜750 行 |
| 全 filtered 図式の擬同型保存と、その native な錐への輸送 | 250〜400 行 |
| 任意の sifted な単体集合形状へ延ばす生成・比較（存在・宇宙の条件も含む） | 400〜700 行 |
| 指定した U への輸送と最終の欄の組み立て・自然性の確認 | 150〜250 行 |
| **S の合計** | **2,300〜3,750 行** |

特に三行目と五行目は型検査前の不確実性が高い。既存の厳密化・局所化の図式比較から一般の全図式版へ届くか、③ の G10 と共有すべき橋が残るかを、現時点では確定していない。**G10 が必ず不要とも、待つほかないとも断定しない**。この部分を零行として旧上限 2,700 行に合わせることはできない。旧見込み 1,600〜2,700 行を、そのまま実装の確約として維持しない。

最初の確認の区切りとしては、一つの厳密な Δᵒᵖ 図式について、具体的実現と指定 native 錐の間を同じ射で結べるかを紙の型から確かめるのがよい。その次に U の実現比較、さらに任意の coherent 図式へ進む。最初から「全 sifted 保存を供給済み」として B を始めない。これは明日の経路判断への提案であり、今夜の実装再開ではない。

### 21.6 A／B の全体規模の比較

途中までの 4,306 行を両方に一度だけ含める。S は W16 の E2 の完了にどちらの経路でも必要な仕事で、B の比較の見積もりから外して安く見せない。native な錐も共通 C に含まれている。

| 範囲 | A：セル対 | B：自由 bar と実現 |
| --- | --- | --- |
| 証明済み（両方に再利用） | 4,306 | 4,306 |
| 共通 C（自由比較、native な錐、自然比較の仕上げ） | 1,510〜2,195 | 1,510〜2,195 |
| 固有部分 | セル対 1,310〜1,770 | T 1,300〜2,150 |
| sifted S | 2,300〜3,750 | 2,300〜3,750 |
| **E2 の両欄と native な錐までの総計** | **9,426〜12,021** | **9,416〜12,401** |
| sifted に依存せず余積比較を先に閉じられるか | 可 | この計画では不可。少なくとも実現の保存が先 |

A の sifted を除いた総計は §20 の 7,126〜8,271 行に一致する。B はセル対を除く代わりに T を加えるので、現状の見積もりでは削減を約束できない。S の図式の橋や T の bar の coherence に既存 API の直接適用が見つかれば下がり得るが、未確認の短縮を予算には入れていない。E2 の上限を上げる提案ではなく、共通部分を全て見える形にするための比較である。

### 21.7 A2・A7 の実際の使い方

`drafts/A2/` と `drafts/A7/` を検索したところ、**`coprodWith`・`coprodWith_cocone`・`coproduct_tensor` の直接参照は零件**。現状は `E : EInfinityTheory` を受け取り、余錐・押し出しの普遍性を要求する型と、証明を残したコメントによる間接的な依存である。したがって「どの欄が実際に呼ばれているか」と「残る証明に何が要るか」を区別する。

| drafts の宣言と場所 | 実際の要求 | 必要な比較の強さ・入力の範囲 |
| --- | --- | --- |
| A2 `polyTensorCocone`（`BaseChangeAndTensor.lean:131`） | 多項式環の二つの変数包含を脚とする native な錐を定義 | Poly 内の指定余積。CAlg の全関手版はこの定義自体には不要 |
| A2 `prismaticCohomologyPoly_tensor`（同:138） | その錐を Δ で送ったものが完備 CAlg で余極限となること | Poly の n,m ごとの指定脚の Künneth で足りる。ただし Δ の値は一般に離散代数ではないため、標的を離散代数だけの比較へ縮められない。単なる頂点の同型だけでは脚を同定できない |
| A2 `derivedPrismaticCohomology_tensor`（同:147） | 任意の animated X,Y と任意の余極限錐 c の像が余極限であること | Poly 上の指定比較を両変数で sifted 延長するため、射と二つの包含に自然な比較・余極限交換が必要。全 CAlg 上の強い `FunctorIso` は十分な道具だが、この型の結論そのものではなく、animated の Δ の像に沿う自然な比較でも原理的に足りる |
| A7 `twoSidedBar`・`relativeTensor_eq_bar`（`AnimatedPerfectoidization.lean:83,89`） | animated な相対テンソルの bar と、その指定実現錐 | 始域の有限余積・実現の普遍性。ここでは CAlg の余積＝台のテンソルの全関手版を直接使わない。B の自由・忘却 bar とは別の二側 bar |
| A7 `preservesRelativeTensor_of_siftedAndTensor`（同:101） | 一般の準圏の関手が、任意の二項余積錐と sifted 実現を保つとき、任意の span の押し出しを保つ | 全ての図式の射を送る自然性・指定錐が要る。対象ごとの非自然な同型だけでは、bar の面・退化を送れない。仮定自体は余錐の保存であり `FunctorIso` 欄の直接要求ではない |
| A7 `derivedPrismaticCohomology_relativeTensor`（同:120） | animated Δ の相対版 | A2 の全 animated な指定余積保存と実現保存を使う。Poly でだけ示して終えることはできない |
| A7 `frobeniusColimit_relativeTensor`（同:200） | 自己関手 τ と自然変換 φ を伴う塔の余極限が span を保つこと | 任意の塔の射・span・指定余錐の自然性。固定対象の同型では足りない。押し出しの余極限の交換として示せれば、台のテンソルとの全比較は別問題にできる |
| A7 `completion_relativeTensor`・`modD_relativeTensor`（同:224,236） | 完備圏を標的とする反射と底変換の押し出し保存 | 左随伴性と指定錐の輸送が入口。`coproduct_tensor` を使わずに CAlg 内の普遍性で述べられる部分 |
| A7 `perfectoidization_relativeTensorMap`・`perfectoidization_relativeTensor`（同:259,273） | 任意の完備 animated span について、指定比較辺が可逆 | 完全な Prop 8.13 の型では入力は任意。離散・多項式入力だけには弱められない。指定された比較辺なので、頂点が同型であるという別の主張では足りない |
| A7 `selfTensor_perfectoidization_eq`（`UniversalProperty.lean:179`） | 特定の self span における `VertexIso` と両脚上の恒等式 | この利用だけなら対象ごとの同型＋明示的な脚の式で足り、全 CAlg 上の `FunctorIso` は型には現れない。続く `selfTensor_unit_eq_mul` ではその脚と単位の自然性が必要。E3 の一意性のための狭い利用と、Prop 8.13 の全主張は分ける |

A7 の残る `AnimatedDomain.lean` は完備化と離散入力の橋、`DiscreteCore.lean` は離散性の議論が中心で、三欄の直接参照はない。`UniversalProperty.lean` の `animatedUnderlyingCAlg` や A2 `discreteRealizationIso`、A7 `perfectoidizationAnimated_discrete` は **別の関手比較の全自然同型**を要求する。それらを `coproduct_tensor` の直接の呼び出しと数えない。A2 `derivedPrismaticCohomology_baseChange` も別の底変換の `FunctorIso` である。

#### 三つの欄ごとの切り分け

- **`coprodWith`**：既存の指定された右因子の関手。A2・A7 はその具体的な頂点表示を固定してはいないが、これを使えば一変数の余積図式を関手として扱える。bar・sifted 延長では射までの関手性が必要。
- **`coprodWith_cocone`**：A2・A7 の余錐としての主張への直接の入口はこの普遍性である。存在する余錐だけではなく、同じ二つの脚と頂点を保つ比較が要る。一般の錐から指定錐へ、余錐の圏での一意性により輸送する部分も残る。
- **`coproduct_tensor`**：界面の欄は固定 y ごとの**全関手の** `FunctorIso`。この実例を完成する仕事では強い形が必須であり、BS の狭い利用だけを理由に対象ごとの版へ変更しない。一方、A2・A7 の現状の宣言型はこの欄の全射程より狭く、各所で必要なのは指定錐・その脚・比較の自然性である。

さらに、**界面の `coproduct_tensor` の型自体には、選んだ `coprodWith_cocone` の二脚をテンソルの標準射へ送るという条件が書かれていない**。強い `FunctorIso` があるだけで、その同型が指定脚を保存すると自動的に結論しない。実例では元の Hopf 射を保つ追加の照合補題を示すか、A2 の証明ではその比較を別に構成する必要がある。この費用を共通 C の「指定射との照合」に含めた。今夜は界面を変更しない。

従って、BS の狭い用途に限定した迂回を検討する余地はあるが、(i) A2 の Poly 上の**標的**は一般の prismatic E∞ 代数、(ii) A7 の Prop 8.13 は任意の animated span、(iii) 界面の完成は全 CAlg の強い形、という三点は残る。「離散入力だけの余積比較で W16 全体が閉じる」という結論にはならない。

### 21.8 明日の判断に渡す区切り

A はセル対の不足が具体的で、B はその全てを除けるが実現の橋へ仕事が移る。どちらでも自由比較の残りと native な錐は必要で、B は未供給の sifted 保存を前提に先へ進めない。明日はまず、実現の厳密図式から全 coherent 図式への橋を⑤aだけで閉じる範囲と③との共有範囲を決め、その実情を踏まえて A／B を選ぶのがよい。今夜は判断を先取りせず、Lean の実装を止めたままにする。本節は紙の報告だけで、登録すべき新規モジュールは零、ビルドの鍵の取得も零。

## 22. 共通部分 a の入力複体の比較と、1,550 行の上限による停止（11-11 夜）

### 22.1 再開と作業範囲

調整役の夜の追加指示を受けて共通部分 a を再開した。main `f654cdc11` を `math/bs-impl` に merge したコミットは `9fc7cdbcb`。main の作業木では編集・ビルドしていない。今回の上限は **a の追加実装全体で約 1,550 行**と読み、以下の一般補助、任意の入力複体への拡張、docstring・空行も全て数える。

セル対、bar の実現、sifted の保存には手を付けていない。a の完了後に b へ進む順序に従い、b（native な余積錐）、c（その脚の照合）、段 4 の組み立て関数はまだ実装していない。以下の再見積もりが a の上限に当たるため、検証した範囲を保存して停止する。

### 22.2 今回閉じた入力複体の補題

追加は次の五本、**902 行**。小補助として書いた八本は、未取り込みのうちに最初の二本へ統合して、重複する module docstring と import を除いた。公開されている既存モジュールの場所・宣言は変更していない。下の実測は統合後で、旧ファイルを重複して数えない。

| 新規モジュール（全て `SerrePositivity.EInfinity.BarrattEccles.Theory` の下） | 実測 | 得られたもの |
| --- | --- | --- |
| `BinaryTensorInputDecomposition` | 355 行 | 語のテンソルを既存の `tensorFamily` へ同定し、指定生成射と包含を照合。隣接交換から任意の置換へ拡張し、その順射を元のテンソル冪の包含・射影による行列成分として同定。語を固定する群の作用と、包含・射影の同変性を複体の射として構成 |
| `BinaryTensorColorClassification` | 200 行 | 色の二つのファイバーの濃度が等しい語を置換で結ぶ。標準パターンの左右のファイバーを Fin m、Fin n へ同定。その安定化群を既存の `twoColorPermutationHom` の像そのものと同定 |
| `FiniteInductionMatrix` | 183 行 | 指定包含・射影から誘導／余誘導の射を作る。部分群外の成分の消滅と包含・射影の恒等式から、標準の `Rep.indCoindIso` との行列比較を証明。異なる成分間の消滅と有限直和の一般補題、微分を保つ誘導／余誘導の複体射も構成 |
| `TwoColorComplexInputs` | 73 行 | 既証明の指定係数同値を、**任意の表現の入力複体**とテンソルして余不変を取る直和全複体へ拡張。順射は元の係数射を同じ双関手へ送った射であることも証明 |
| `TwoColorInputComponents` | 91 行 | 実際の標準パターンと実際の二色部分群へ上の構成を適用。和のテンソル冪の全対称群の入力表現、標準成分の二色部分群の入力表現、それらの指定包含・射影、包含の後の射影の恒等式、誘導入力からの複体射・余誘導入力への複体射を構成 |
| **今回の計** | **902 行** | |

入力 X・Y は任意の複体で、零微分・有界性・平坦性を要求していない。従って、ここまでの入力の補題は任意の cofibrant な入力にも使える。`twoColorComplexInputHomotopyEquiv` は係数のホモトピーを全複体へ移すため、入力微分を捨ててから擬同型を結論する方法には依存しない。

ただし **自由代数の指定比較の擬同型性は未完**。特に `finiteInductionBiconeIsBilimit` は、実際の入力における全成分の網羅性 `hcover`、異なる成分間の消滅 `hcross` などを入力する一般補題である。今回、それらを全 arity の実際の入力に適用し終えたとは扱わない。`twoColorInducedInputInclusion` は実際の入力複体から作った指定射だが、これらを全色数にわたって足した射が同型であるという宣言ではない。

### 22.3 元の五行に対する実測と残り

§20.2 の五行ごとに、今回の実測を一度だけ割り付ける。三行目には、任意の入力複体の直和全複体への係数比較の拡張も含める。第四・第五行は未着手。

| 元の五行 | §20.2 の見込み | 今回の実測 | まだ必要なもの | 残りの見込み |
| --- | --- | --- | --- | --- |
| 語の指定包含と置換、標準ブロックの作用 | 160〜220 | 355 | 標準パターンの複体を `power X m ⊗ power Y n` へ移す同型と、その同型が二つの既存の置換作用を保つ照合 | 80〜120 |
| 固定色数の軌道と標準語の安定化群 | 120〜180 | 200 | 任意の語の二つのファイバー濃度の和と arity の一致、arity を固定して色数を走らせたときの代表の網羅性、添字の等式による移送 | 60〜90 |
| 誘導表示の射・逆・複体上の同型 | 260〜340 | 347 | 実際の全入力での `hself`・`hcross`・`hcover`、全成分の誘導表示の直和が入力複体となる同型、微分に関する自然性をまとめる。一般補題の仮定のまま残さない | 200〜300 |
| 実際の Schur 複体の両側の分解・再添字付け | 220〜300 | 0 | 入力の直和を実際の Schur 余極限へ通し、係数と入力の直和全複体、arity と色数、テンソル側の二つの Schur 図式の順序を照合 | 250〜350 |
| 指定 Hopf 比較と係数比較、自由比較の擬同型 | 180〜250 | 0 | 自由代数の和の表示と指定二包含、Hopf 対角・単位挿入・零入力削除との一致を生成射上で照合。両側の同型を通った指定射を特定して擬同型へ結ぶ | 250〜350 |
| **合計** | **940〜1,290** | **902** | | **840〜1,210** |

全て docstring・空行を含む追加 Lean の見込みで、a の外に一般補助の費用を出していない。特に今回の任意の置換への拡張と、微分を保つ安定化群の包含・射影の構成が、第一行の旧見込みを上回った。第三行では、一般の誘導／余誘導の行列比較を作っても、それを全色数にわたる実際の入力の同型へ適用する部分が残ることを分けた。

従って a の見込みは **902 + 840〜1,210 = 1,742〜2,112 行（約 1,750〜2,100 行）**。これは a に与えられた約 1,550 行を超えそうなので、追加指示の「上限を超えそうなときは、その時点で報告して止める」に従って停止する。a の完了報告ではなく、b へ進む条件も満たしていない。b の 670 行の枠や c・段 4 へ a の残りを移して計上することはしない。

参考として、以前までの coproduct_tensor と native な錐の全実測 4,306 行に今回を加えると **六十一本・5,208 行**。今回の停止判断に使う枠は、再開時に指定された a 自体の 1,550 行である。セル対・bar・sifted の経路の判断は先取りしていない。

### 22.4 検証と登録候補

登録候補は §22.2 の五本だけ。統合前の八つのファイル名は登録しない。既存の公開宣言、界面の型、drafts、共通入口、共有監査スクリプトは変更していない。他レーンのファイルとの重複も零。新規の［一般∞］の移動候補は零。

対象ビルドは `/tmp/bsw16/graded/two-color-input-components-03.log` で成功。新規五本の警告は零、依存先の既報 `ZeroArity` の警告二件は残る。登録と取り込みのビルドは調整役が行う。

五本の **129 宣言**の再帰監査も成功し、標準三公理のみ（`/tmp/bsw16/graded/audit-common-inputs.log`）。本体の追加には sorry・admit・新規公理・デバッグ宣言を残していない。ビルド・監査はそれぞれ `--wait 3600` で一枚だけ整理券を出し、実行の終了ごとに鍵を返却した。未検査の Lean ソースは残していない。ここで実装を止め、調整役の判断を待つ。


## 23. 11-12 朝：b の native な余錐の構成、普遍性の前で規模による中間停止

### 23.1 指示の取り込みと停止の範囲

朝の指示に従って main を `math/bs-impl` へ取り込み、§11 が入った `2fc3dc7ce` までそろえた。a の五本・902 行には変更を加えていない。今回の順序は b → c → 組み立て関数。b の余錐とその脚・頂点は作れたが、**`coprodWith_cocone` の欄に要る余極限性はまだ供給していない**。以下の再見積もりが b の約 670 行を超えそうなので、追加実装を止めた。b の完了報告ではない。c と段 4 の組み立ては未着手。

### 23.2 型検査したもの

新規二本、**297 行**（docstring・空行込み）。既存の公開宣言・界面・drafts・入口・共有監査は変更していない。

| モジュール（`SerrePositivity.EInfinity.BarrattEccles.Theory` の下） | 行数 | 得られたもの |
| --- | --- | --- |
| `NativeCoproductCocone` | 113 | cofibrant な代表の厳密余積の二包含を、同じ DK 頂点の間の辺へ送る。`cAlgCoprodCocone` は二点図式の実際の `JoinCocone`。その頂点が既存の `barrattEcclesCoprodWith` の指定した値に一致し、二つの脚が指定包含の同じ一次単体であることを証明 |
| `BinaryCoconeSpace` | 184 | 任意のパラメータからの join の族を貼り、余積図式の終点固定の余錐空間を、二枝の余錐空間の積へ同型にする。制限射そのものの `IsIso`、積の Kan 性、および指定の全 Hom の族の積比較が同値なら余極限であるという検査補題を証明 |
| **計** | **297** | |

`cAlgCofibrantArrow` は、元の `localizationArrowPoint` と同じ `exInfinityUnit` から辺を作る。局所化の source map で選ばれた頂点が標準の頂点と等しいと仮定していない（一般には頂点の同型で比較する必要がある）。`cAlgCoprodCocone_vertex`・`cAlgCoprodCocone_leg_left`・`cAlgCoprodCocone_leg_right` は指定した余錐についての等式。

`binaryCocone_isColimit_of_pointHomRestriction` の仮定は、各終点 z について

```lean
IsQCatEquivalence
  (HomotopyLimits.coconePointHomFamily d z ≫ binaryCoconeSpaceRestriction p z)
```

である。ここは実際の比較射の同値性の**還元先**であり、この仮定を `cAlgCoprodCocone` に対して閉じたという扱いにはしない。`BinaryCoconeSpace` は **［一般∞］の移動候補**。KL-W1 の取り込み前なので `InfinityCategories/` には追加していない。

### 23.3 余極限性の残りと既存 API の調査

既存の `rightFrameCoprodHomIso` は、同じ右 frame への厳密余積の Hom を積へ分け、二射影が指定包含による前合成であることまで与える。一方、`modelRightFramePinchedEquivalence` と `rightFrameTerminalHomIso` は固定した始域について終域全体を比較する入口である。これらを対象ごとに適用しただけでは、**二つの始域の包含が native な錐の脚による前合成に対応すること**は出ない。

別の経路として、既存の `cAlgMappingSpaceComparisonIso_precompose` は実際の DK Hom と `mappingSpace` の比較に始域の前合成の自然性を与える。`sourceFrameHomComparison` とその `sourceFrameHomComparison_isIso` も再利用できる。こちらでは次が残る。

1. X・Y の余単体的 cofibrant 分解の余積と、X ⨿ Y の選んだ分解の間の指定比較を作る。余積 frame の Reedy cofibrancy、augmentation と比較の弱同値性を示す。
2. その Hom の積比較を `mappingSpace`、ULift、DK の実際の Kan Hom へ運ぶ。**同じ二つの指定射**を保ち、積に関する反転性を使って比較全体を同値にする。
3. coslice fiber と左 pinched Hom、および coherent nerve の Hom の比較を通し、native な二脚の前合成と照合する。実際の余錐の `coconePointHomFamily` の二制限は、対応する前合成とのホモトピーまで扱う必要がある。
4. 今回の検査補題を指定の `cAlgCoprodCocone` に適用して、界面の部分型を供給する。

始域の frame の不変性は `SerrePositivity.EInfinity.FrameHom.source_weakEquivalence_isIso`（`InfinityCategories/ModelBridge/SourceInvariance.lean`）を使える。これは anodyne を反転する関手に対する結論で、`[ModelCategory SSet]` を要求しない。対して `HomotopyFunctionComplex/SourceInvariance.lean` の `cosimplicialHomMap_weakEquivalence` はその仮定を要求するため、今回の実装に使う入口にはしない。必要な模型の存在が未供給だから止めるのではなく、指定した射までの比較の実装費用による停止である。

### 23.4 再見積もりと停止判断

全て b の追加 Lean に計上し、補助を c や組み立て関数の枠へ移していない。残りは未実装の見込みで、既存宣言だけで閉じたとは主張しない。

| b の部分 | 今回の実測 | 残りの見込み |
| --- | --- | --- |
| native な余錐・指定頂点・二脚 | 113 | 0 |
| 二枝の余錐空間の積分解・普遍性の検査への還元 | 184 | 0 |
| 余積 frame・指定比較・Reedy cofibrancy と弱同値性 | 0 | 120〜170 |
| `mappingSpace` から実際の DK Hom の積比較までの移送 | 0 | 80〜120 |
| 左 Hom・二つの native な脚・全 Hom の族との照合 | 0 | 150〜220 |
| 指定余錐への適用と界面の部分型の供給 | 0 | 40〜60 |
| **合計** | **297** | **390〜570** |

従って b の見込みは **687〜867 行（約 690〜870 行）**。旧見込みの約 670 行には、厳密な Hom の積分解と既存の対象ごとの frame 比較を合成するだけで、native な二脚まで比較できると見込んでいた不足がある。今回はその照合を明示的な残作業に分けた。上限を超えそうなときに止めるという指示に従い、この時点で追加の Lean を止める。a・セル対・bar の実現・sifted の保存は進めていない。

c の厳密な式自体は `barrattEcclesCoproductTensorNat` と `coprod.inl_desc`・`coprod.inr_desc` から出るが、指定 native な錐の脚の照合を b の未証明の余極限性と取り違えない。今回 c を完了と報告することはせず、組み立て関数の既証明欄として `coprodWith_cocone` を入れてもいない。

### 23.5 検証・登録候補・取り込み待ち

対象二本のビルドは `/tmp/bsw16/graded/native-coproduct-space-05.log` で成功。追加二本に Lean の警告は零。ビルドの wrapper が別レーンの既存 `lake build` を警告表示したが、自レーンは鍵付きで指定二本のみをビルドした。

二本の **50 宣言**の再帰監査も成功し、標準三公理のみ（`/tmp/bsw16/graded/audit-native-coproduct.log`）。本体の追加に sorry・admit・新規公理・デバッグ宣言・満たせない `[ModelCategory SSet]` の仮定はない。未検査の Lean ソースは残していない。

今回の登録候補は §23.2 の二本だけ。前回の §22 の五本とは別で、合わせて未取り込みは七本。調整役の指示どおり、KL-W1 の取り込みと改名表への追従の後に取り込む。旧名を先取りして改名していない。他レーンのファイルとの重複は零。鍵は一回のビルド・監査ごとに `--wait 3600` で取得し、終了時に返却した。


## 24. 11-12：b 完了 — 指定余積関手の native な余極限錐

### 24.1 結論と規模

§23 の後の指示（b を約 900 行、超過 3 割以内は報告して続行）に従って再開した。**`barrattEcclesCoprodWith_cocone` を、本体で無条件に構成した。** 型は界面の欄と同じく、各 x・y について `JoinCocone (binaryPointDiagram x y)`、その頂点が既存の `barrattEcclesCoprodWith A y` の x での値に等しいこと、そして `IsColimitCone` の組である。余極限性を引数に取る組み立てではない。

b の最終差分は **九本・1,022 行**。§23 の実測のうち `NativeCoproductCocone` の 113 行も含む。900 行からの超過は 122 行（約 13.6%）で、今回承認された 3 割の範囲内で完了した。a・セル対・bar の実現・sifted 保存・Tot は進めていない。昼の §12 の判断（経路 B、a の残りと厳密 bar は共通部分の後、二脚の条件を界面に追加）も確認した。

### 24.2 実装の内訳と前の見積もりとの差

| モジュール（全て `SerrePositivity.EInfinity.BarrattEccles.Theory` の下） | 実測 | 内容 |
| --- | --- | --- |
| `NativeCoproductCocone` | 113 | §23 で作った指定包含・辺・頂点。DK 比較には同じ `cofibrantAlgebraDKCoprodInl/Inr` を使う |
| `CoproductFrames` | 121 | 二つの余単体的分解の余積は Reedy cofibrant。余積の指定分解への比較が各次数で弱同値。二包含を厳密に保つ |
| `CoproductFrameHom` | 94 | 余積 frame の全単体の Hom を、二包含の前合成による二項積へ厳密に分解 |
| `AnodyneBinaryProducts` | 106 | 選ばれた圏論の積と単体集合のテンソル積を比較。anodyne 局所化の二項積保存、指定した組への射の自然性 |
| `CoproductMappingSpace` | 141 | 始域 frame の比較と自然な終域置換を消去し、元の Map^h の二包含の積比較を局所化同型にする |
| `CoproductDKHom` | 101 | ULift の積保存と `cAlgMappingSpaceComparisonIso_precompose` を使い、実際の Ex∞ Kan DK Hom の指定積比較を局所化同型にする |
| `EnrichedPointPrecomposition` | 78 | 豊穣関手と点の前合成の自然性。実際の Kan Hom の前合成と、元の前合成の Ex∞ 像の局所化等式。反対圏の後合成との照合 |
| `CoproductNativeUniversal` | 168 | 厳密二包含の普通の余錐に、離散図式の全 Hom の判定を適用して native な余極限性を証明 |
| `NativeCoproduct` | 100 | 二点の形状同型で指定 `binaryPointDiagram` へ戻し、頂点を既存の関手の値に正規化。界面と同じ部分型を供給 |
| **合計** | **1,022** | |

§23 の残作業の表では、frame 120〜170 行、DK まで 80〜120 行、native な脚と全 Hom の照合 150〜220 行、界面の供給 40〜60 行と見込んでいた。実際には frame の Hom の積の構成と、単体集合のテンソル積・選ばれた圏論の積の区別、局所化自体の積保存、ULift と実際の点の前合成までの照合に追加が要った。これらを b の外に出して計上していない。

一方、最後の native な余極限性は、既存の `strictCoherentCone_isLimit_of_discrete_representableComparison`、`strictNativeCocone_isColimit_iff`、`JoinCocone.reindexIso` を再利用できた。左 pinched Hom と二枝の coslice fiber の積分解から進む前の還元は不要となったため、**未取り込みで本体・他レーンから参照がない `BinaryCoconeSpace`（184 行）を最終差分から外した**。これは §23 の登録候補の取り消しでもある。ファイルが一度作られたことと、経路を変えて不要になったことをここに記録し、取り込み済みの実装を数から落とす操作はしていない。§23 のコミットには前の版が保存されている。

### 24.3 指定射と全 Hom の照合

`cAlgCoprodHomRestriction_isIso` は実際の Kan DK Hom から二つの Hom の積への**同じ二包含による射**についての結論である。対象ごとの任意の同値を取って自然性を推定していない。`kanStrictPrecompose_localized` は元の同じ `exInfinityUnit` と豊穣関手の合成則から、native な脚の実際の前合成とこの比較射を照合する。

`cAlgBinaryCocone_isColimit` は二点の普通の余錐について、反対圏の離散図式の全 Hom の比較へ適用したもの。π₀ だけで普遍性を結論していない。`cAlgNativeCoprodCocone` はこの余極限錐を形状同型で戻した、実際に採用する余錐である。§23 の `cAlgCoprodCocone` 自体の余極限性を別途証明したという主張にはしていない。

### 24.4 検証と登録候補

最終対象ビルドは `/tmp/bsw16/graded/native-coproduct-06.log` で成功し、追加モジュールの Lean の警告は零。登録候補は §24.2 の九本。**`BinaryCoconeSpace` は登録しない。** §22 の五本は別に未取り込みのままなので、今回までで取り込み待ちの新規モジュールは合計十四本となる。

九本の **116 宣言**の再帰監査は成功し、標準三公理のみ（`/tmp/bsw16/graded/audit-native-coproduct-complete.log`）。追加本体に sorry・admit・新規公理・デバッグ宣言・満たせない `[ModelCategory SSet]` の仮定はない。未検査の Lean ソースは残していない。

［一般∞］の移動候補は `CoproductFrames`・`CoproductFrameHom`・`AnodyneBinaryProducts`・`EnrichedPointPrecomposition`。KL-W1 の前なので全て `EInfinity/` の下に置いた。ほかの五本は BE 固有の比較・錐の供給である。既存の公開宣言・drafts・共通入口・共有監査は変更していない。界面の新しい二脚の欄はこの b ではまだ足していない（次の c で型を整える）。他レーンのファイルとの重複は零。

ビルドと監査は一回の実行ごとに `--wait 3600` で鍵を取り、終わったら返す形。KL-W1 の取り込みと改名表への追従までは main への取り込みを依頼しない。b の後は指示の順に c、新しい二脚の欄を含む組み立て関数へ進む。


## 25. c：指定二脚の厳密比較と、新欄 `coproduct_tensor_legs`

### 25.1 閉じた照合

`NativeCoproductLegs` で、**界面へ実際に供給した `barrattEcclesCoprodWith_cocone`** の第一・第二脚を、元の cofibrant な厳密余積の二包含の Kan 局所化の辺へ同定した。等式は `coherentCoconeLegMap` による **Δ[1] からの写像全体**の等式であり、零次の類だけの同定ではない。

さらに、既存の全関手版の厳密自然変換 `barrattEcclesCoproductTensorNat` について、二包含との合成が `hopfTensorInl`・`hopfTensorInr` であることを証明した。台の複体に忘却した式も証明し、それぞれ

```lean
(ρ_ B.carrier).inv ≫ (𝟙 B.carrier ⊗ₘ unitD)
(λ_ D.carrier).inv ≫ (unitB ⊗ₘ 𝟙 D.carrier)
```

という単位からの標準射そのものである。単位を与える零 arity の同型性も BE について無条件に証明して使う。c のこの厳密な照合に a・bar の実現・sifted 保存は使っていない。

### 25.2 新しい欄の型と意味

昼の指示 §12 の 4 に従い、新欄の名前を **`coproduct_tensor_legs`** とした。`EInfinityTheory` の既存の欄の型は変更していない。欄の型は次の補助を使う。

```lean
TensorCoproductLegCompatibility S toEInfinityCore x y (coprodWith S y)
  (coprodWith_cocone S x y).val (coprodWith_cocone S x y).property.1
  (coproduct_tensor S y)
```

この条件は、**既存の同じ全関手版の `FunctorIso`** の x での成分を、指定余錐の頂点からの同型に正規化し、忘却した二脚との合成が `derivedTensorInlHom`・`derivedTensorInrHom` に等しいことを要求する。二脚の可換式は D(S) の通常のホモトピー圏の式である。全関手版の同型を対象ごとの任意の同型へ弱めていない。

標準射を界面内で定義する際に、BE の unit や Hopf 代数を参照しないようにした。離散基底代数から x・y への各射について、その忘却の像の単位の H⁰ の類を、`discrete_forget`、離散入力の既存の自由解像度の増大、代表の H⁰ との比較から読む。条件は、その**同じ単位の類を表す**複体のテンソル単位からの鎖写像の代表の存在と、その代表による二標準射との可換式を要求する。単位の正規化を落として任意の射を「標準射」として選ぶ条件にはしていない。EInfinityTheory の `discrete_initial` によって単位射は存在するので、単位射への量化が空で成り立つ条件でもない。

`TensorLegs` で使うのは、固定された D(S) の既存の semifree 代表・閉 dg 射・複体の単位子である。**CAlg の模型の API は使っていない。** 三本の Interface モジュールに BE・hammock・ModelCategory の直接 import はなく、宣言・欄に `[ModelCategory SSet]` の仮定もない。

`coproduct_tensor` 自体の全関手版の同型は経路 B の後段で供給するため、**新欄の BE における全実例の証明も、その同型と組で後段に残る**。今回の厳密な二包含の公式は、その実例を構成するための照合である。未構成の全関手版の同型や新欄の実例を無条件に証明済みとは扱わず、次の組み立て関数では、指示どおりこの新欄も引数に取る。

### 25.3 規模・配置・検証

| ファイル | 実測 | 役割 |
| --- | --- | --- |
| `EInfinity/NativeBinaryCoconeHom` | 44 行 | 指定二脚の始点を正規化したホモトピー圏の射。**［一般∞］の移動候補** |
| `EInfinity/Interface/TensorLegs` | 91 行 | D(S) の二標準射と、同じ semifree 代表のテンソル頂点との等式 |
| `EInfinity/Interface/TensorUnitClasses` | 77 行 | 離散基底代数・単位の H⁰ の類・単位の鎖写像の代表の正規化 |
| `EInfinity/Interface/CoproductTensorLegs` | 55 行 | 全関手版の同じ成分と指定二脚の適合条件 |
| `EInfinity/BarrattEccles/Theory/NativeCoproductLegs` | 115 行 | 実際の native な脚の同定、厳密自然変換の二包含と台の公式 |
| `EInfinity/Interface/Theory.lean` の追加 | 6 行 | import と新欄 |
| `drafts/Shared/BarrattEcclesTheory.lean` の追加 | 1 行 | 作業用の全実例に新しい未供給欄を反映（drafts 内の sorry） |
| **合計** | **389 行** | |

c の上限約 400 行以内。一般の二脚の補助は Interface の中へ混在させず、EInfinity の下の専用ファイルへ分けた。A1 の二本・A0・A3・items.csv は編集していない。共有の `Shared/BarrattEcclesTheory` は W14 のこの実例の持ち分で、今回の新欄一行だけを追加した。

対象ビルドは `/tmp/bsw16/graded/tensor-legs-complete-02.log`（厳密照合）と `/tmp/bsw16/graded/tensor-legs-interface-final.log`（一般∞の補助の分離後の界面）で成功。追加ファイルの Lean 警告は零、依存先 `ZeroArity` の既報二件は残る。

本体の六モジュール（新規五本と既存の `Interface.Theory`）の **163 宣言**の再帰監査も成功し、標準三公理のみ（`/tmp/bsw16/graded/audit-coproduct-tensor-legs.log`）。追加本体に sorry・admit・新規公理・デバッグ宣言はない。

作業用全実例 `drafts/Shared/BarrattEcclesTheory.lean` も、新欄を加えた状態で型検査が成功（`/tmp/bsw16/graded/draft-theory-tensor-legs.log`）。このファイルの既存・追加の sorry の警告は drafts の未供給欄であり、本体の監査には含めていない。鍵は各ビルド・監査・drafts の型検査の終了時に返却した。

登録候補は上表の新規五モジュール。既存の `Interface.Theory` は新欄が加わったため、その監査も今回行う。b の九本と §22 の五本を含め、取り込み待ちの新規モジュールは合計十九本。KL-W1 の後の改名表に追従してから取り込む。c の後は、`coproduct_tensor_legs` を含む未供給の欄だけを引数に取る組み立て関数へ進む。


## 26. 段 4：既証明欄を固定した全界面の組み立て

### 26.1 結論

本体の `EInfinity/BarrattEccles/Theory/Assembly.lean` に **`barrattEcclesTheoryOfRemaining`** を置いた。既存の作業用の名前 `barrattEcclesTheory` と衝突させず、既証明欄を固定して全 `EInfinityTheory` を返す関数である。未供給の欄の型を推論して結論だけを仮定するのではなく、構造体の各既証明欄へ実際の本体の証明を代入して型検査している。

引数は次の **十八欄だけ**。同じテンソルの全関手版の同型を、新しい二脚の適合条件の型にも使っている。

| 群 | 引数 |
| --- | --- |
| 保存・存在 | `forget_preservesSifted`、`presentable` |
| テンソル | `coproduct_tensor`、`coproduct_tensor_legs` |
| 通常の cosimplicial Tot | `ofCosimplicial`、`ofCosimplicial_forget`、`ofCosimplicial_cone`、`ofCosimplicial_restrict` |
| cdga の Tot | `ofCosimplicialCdga`、`ofCosimplicialCdga_cone`、`ofCosimplicialCdga_discrete`、`ofCosimplicialCdga_evalZero`、`ofCosimplicialCdga_evalZero_leg` |
| 冪作用 | `powerOp0`、`powerOp0_zero`、`powerOp0_pos`、`powerOp0_discrete`、`powerOp0_tot` |

中核、忘却の保存性の既証明部分・保存的性質、指定余積関手と native な余極限錐、離散基底環の始対象性、M13 の係数変更・比較・ホモロジー比較、π₀ の四欄、厳密な複体のホモロジー比較、`ofCdga` の三欄は本体の既存証明で供給する。特に `baseChange_forget` は `barrattEcclesBaseChange_forget` を使い、K 平坦性を外部の追加仮定に戻していない。

この関数は未供給の十八欄を仮定にする、承認された条件付きの組み立てである。G12・M14・G10 や経路 B の全関手版の比較まで無条件に証明したという主張ではない。

### 26.2 作業用実例と規模

`drafts/Shared/BarrattEcclesTheory.lean` の既存の名前 `barrattEcclesTheory` を保ち、新しい組み立て関数への適用に書き換えた。**証明済みの欄の sorry はこのファイルから外し、残る十八欄だけを名前付き引数の sorry として残した。** 他の BS の drafts には変更を加えていない。

本体の組み立ては **89 行**、作業用全実例は整理後 **49 行**。両方の現行のファイル全体を足しても 138 行で、組み立ての上限約 300 行以内である。共通入口・共有監査スクリプトには登録していない。

### 26.3 検証と次の順序

対象ビルドは `/tmp/bsw16/graded/barratt-eccles-theory-assembly-01.log` で成功。新しい組み立てモジュールの **16 宣言**の再帰監査も標準三公理のみ（`/tmp/bsw16/graded/audit-theory-assembly.log`）。同じ検査で関数の型の最上位の引数を列挙し、上表の十八欄だけであることを確かめた。本体に sorry・admit・新規公理・追加の `[ModelCategory SSet]` 仮定はない。

作業用実例を接続した後の型検査も成功（`/tmp/bsw16/graded/draft-theory-assembly.log`）。その sorry の警告は未供給欄の drafts に限る。ビルド・監査・drafts の検査はそれぞれ別に `--wait 3600` で鍵を取り、終了時に返却した。

登録候補は **`SerrePositivity.EInfinity.BarrattEccles.Theory.Assembly`**。§22 の五本・b の九本・c の五本と合わせ、取り込み待ちの新規モジュールは二十本。`BinaryCoconeSpace` の取り消しは変わらない。KL-W1 の後の改名への追従は取り込み前に行う。

これで b → c → 組み立ての共通部分を区切った。承認待ちにはせず、指示書 §12 の順に **a の自由代数の比較の残り（上限約 2,100 行、3 割以内の超過は報告して続行）**へ戻る。その後は厳密な bar 図式・増大・U の下の分裂（上限約 800 行）。セル対は行わず、bar の ∞ 図式への移送・実現の同定・全関手版・sifted の残り・Tot は③-b の橋の後に残す。


## 27. a の再開途中：KL-W1 verify の間はビルド・監査を待つ

### 27.1 資源待機と作業木

11-12 09:40 の調整役の連絡に従い、KL-W1 verify の終了の連絡まで、ビルドと監査を控える。
自分の実行中の対象ビルドは終了し、待ちの要求を取り消した。`with_build_lock.sh --status` で
`holder: (free)`、`queue (day order): 0` を確認した。他レーンのプロセスには触れていない。

直前の exec セッションの終了を誤認して次の要求を出したため、一時的に同じ worktree の要求が二つになった。
待ちの方を取り消し、両方の exec セッションの終了を回収済み。以後は `write_stdin` の戻りに
`session_id` がなく終了コードがあることを確かめてから次の要求を出す。鍵の中で常駐するセッションは使っていない。

b・c・組み立ての完了は §§24〜26 のとおり（`2bcb51fac`・`7c71d375c`・`9728984d0`）。
a の今回の六本は、未検証の修正を含むため**コードをコミットせず作業木に置く**。
この節は資源待機の途中記録であり、a の完了報告でも、上限による停止の申請でもない。

### 27.2 現在の下書きと確認済みの範囲

| モジュール（すべて `EInfinity/BarrattEccles/Theory/`） | 行数 | 状態 |
| --- | ---: | --- |
| `TwoColorStandardPowers` | 52 | 実際の標準パターンの入力から `power X m ⊗ power Y n` への複体の同型。対象ビルド成功 |
| `BinaryTensorWordCounts` | 111 | 二色の入力数の和、置換不変性、標準語の軌道による被覆、固定 arity の代表。対象ビルド成功 |
| `TwoColorStandardInclusion` | 75 | 指定包含を左右の冪の包含と `appendIso` で計算。停止直前の対象ビルド成功、追加警告零 |
| `BinaryTensorOrbitInputs` | 100 | 実際の標準代表の安定化群上の入力複体、指定包含・射影、自己行列・異なる入力数の行列の消滅。対象ビルド成功、追加警告零 |
| `TwoColorInputMatrix` | 55 | 各次数の誘導包含・余誘導射影の合成。元の複体射の別名の同定で型検査が重くなったため、実際の次数射で述べ直した修正は未検証 |
| `BinaryTensorOrbitDecomposition` | 102 | 誘導包含による射の検出と有限双錐の普遍性の下書き。停止前の構文エラーを修正済み、修正後の型検査は未実施 |
| **計** | **495** | 六本の一括の成功・監査は未実施 |

これらは任意の入力複体を扱う。零微分、有界性、平坦性、群の位数の可逆性は仮定していない。
既存の公開宣言とその定義は変更していない。新しい sorry・admit・axiom は書いていないが、
**未検証の二本を証明済みとして数えない**。監査の宣言数もまだ確定していない。

§22 の既存五本 902 行と今回の下書き 495 行を合わせ、a は現時点で **1,397 行**。
残りは、(1) 標準入力同型のブロック置換との可換性、(2) 実際の誘導直和の型検査と微分の照合、
(3) Schur 表示の複体としての直和・余不変・全複体の比較、(4) 指定 Hopf 比較の同定と弱同値。
特に次数ごとの Schur 分解だけから複体の同型を主張せず、係数の微分と入力の微分の双方を照合する。
入力の次数と係数の次数の順序にも注意する。経路 A のセル対は作っていない。

### 27.3 再開の連絡の後の順序

1. 現在の六本を対象に、一回の小さなビルドで未検証の二本から修正する。
   鍵は `--wait 3600` で一枚だけ出し、対象ビルドの終了時に返却する。
2. 六本の型検査が成功したところで、それぞれを含む再帰監査を一回だけ別の鍵で行う。
   標準三公理のみを確認してから、コードと検証結果をコミットする。
3. a の残りを上の順に閉じる。上限約 2,100 行に対し、3 割を超える見込みとなったときは止める。
4. a の完了を報告した後に、厳密な随伴の bar・増大・U の下の分裂へ進む（上限約 800 行）。
   いまはその実装には着手していない。bar の ∞ 図式への移送・実現の同定・全関手版、
   sifted の残り、Tot は引き続き③-b の橋の後に残す。

未検証の六本はまだ登録候補の確定一覧に加えない。現在の確定済みの取り込み待ち一覧は §26 の二十本。
KL-W1 の取り込み後の改名表は、調整役から受け取ってから追従する。

## 28. 検収用の型案：`coproduct_tensor_legs`

### 28.1 名前と正確な型

提案名は **`EInfinityTheory.coproduct_tensor_legs`**。§25 の `7c71d375c` に置いた型を検収用の案として提示する。
欄を足すことの承認と、今回の具体的な型の検収は分ける。この案は枝にあり、main への取り込み・型の確定は調整役の検収を待つ。
今回は界面のコードに追加変更をしていない。

```lean
coproduct_tensor_legs (S : Type u) [CommRing S]
    (x y : (CAlg S) _⦋0⦌) :
  TensorCoproductLegCompatibility S toEInfinityCore x y (coprodWith S y)
    (coprodWith_cocone S x y).val
    (coprodWith_cocone S x y).property.1 (coproduct_tensor S y)
```

`TensorCoproductLegCompatibility` の入力は次の型である。

```lean
(S : Type u) [CommRing S] (E : EInfinityCore.{u})
(x y : (E.CAlg S) _⦋0⦌) (P : E.CAlg S ⟶ E.CAlg S)
(c : JoinCocone (binaryPointDiagram x y))
(hv : c.vertex = atVertex P x)
(θ : FunctorIso (P ≫ E.forget S)
  (E.forget S ≫ tensorWith (atVertex (E.forget S) y)))
```

条件の展開は以下。`θ` は、既存の `coproduct_tensor S y` の**同じ全関手版の同型**である。
対象ごとに別の同型を選んで条件を満たす型にはしていない。

```lean
def TensorCoproductLegCompatibility : Prop :=
  ∀ (ηx : (SSet.HomotopyCategory.mk (coreUnitVertex S E) : (E.CAlg S).HomotopyCategory) ⟶
        SSet.HomotopyCategory.mk x)
    (ηy : (SSet.HomotopyCategory.mk (coreUnitVertex S E) : (E.CAlg S).HomotopyCategory) ⟶
        SSet.HomotopyCategory.mk y),
  ∃ (unitX : 𝟙_ (Complex S) ⟶
        (derivedInfinityCategoryVertexEquiv S (atVertex (E.forget S) x)).val)
    (unitY : 𝟙_ (Complex S) ⟶
        (derivedInfinityCategoryVertexEquiv S (atVertex (E.forget S) y)).val),
    NormalizedTensorUnit S E x ηx unitX ∧ NormalizedTensorUnit S E y ηy unitY ∧
    (hoFunctor.map (E.forget S)).toFunctor.map (binaryCoconeLeftHom c) ≫
        (tensorComparisonAtCocone S E x y P c hv θ).hom =
      derivedTensorInlHom S (atVertex (E.forget S) x) (atVertex (E.forget S) y) unitY ∧
    (hoFunctor.map (E.forget S)).toFunctor.map (binaryCoconeRightHom c) ≫
        (tensorComparisonAtCocone S E x y P c hv θ).hom =
      derivedTensorInrHom S (atVertex (E.forget S) x) (atVertex (E.forget S) y) unitX

```

`binaryCoconeLeftHom c`・`RightHom c` は、指定された native 余錐の**実際の二脚**のホモトピー圏での射。
`tensorComparisonAtCocone` は頂点の等式 `hv` で始域を正規化した `θ.app x` である。
右辺の標準射は、同じ semifree 代表の鎖写像
`(ρ_ _).inv ≫ (𝟙 _ ⊗ₘ unitY)` と `(λ_ _).inv ≫ (unitX ⊗ₘ 𝟙 _)` の D(S) での類を使う。

`NormalizedTensorUnit S E x ηx unitX` は

```lean
(complexUnitHZeroIso S).inv ≫ HomologicalComplex.homologyMap unitX 0 =
  coreUnitClass S E x ηx
```

という条件。`coreUnitClass` は離散基底代数からの射を `E.forget` と H⁰ に送り、
`E.discrete_forget` と同じ H⁰ の代表比較で読む。任意の閉元を単位として選んで済ませない。
`discrete_initial` があるので単位代数からの射への量化も空ではない。
単位複体から semifree 代表への射は H⁰ の類でホモトピー類が決まるため、代表の選択はこの正規化で管理する。

D71 に従い、これらの `Interface/` の型は BE・hammock のモジュールを直接 import せず、その API を使わず、
欄の型に `[ModelCategory _]` を置かない。D(S) の固定された semifree の API は使う。

### 28.2 A2 の `derivedPrismaticCohomology_tensor` での使い方

A2 の現行の結論は、入力の**任意の指定二項余極限錐** `c` を Δ で写したものが余極限錐となること。
単に二対象の値が同型であるという結論ではない。

1. 出力側で `E.coprodWith_cocone A (Δ X) (Δ Y)` を取り、その普遍性から
   `Δ c.vertex` への比較辺 `q` を作る。二脚は Δ を適用した入力の二脚で指定する。
2. `E.coproduct_tensor A (Δ Y)` で忘却後の比較の始域を `U(Δ X) ⊗ᴸ U(Δ Y)` に移す。
   **この移送と実際の二脚の整合を保証するのが新欄**である。
3. 多項式の場合、同じ二つの変数包含が誘導する Künneth 射と `U(q)` を同定する。
   Hodge–Tate の gr と微分形式の Künneth、完備性による検出で、この指定射が同値と示す。
4. sifted 表示で一般の入力へ延ばす際は、`coproduct_tensor` の第一変数での全関手版の自然性を使う。
   対象ごとの任意の同型では、図式の射と比較辺 `q` の同定を運べない。
5. `forget_conservative` で `q` が可逆と戻し、指定余積錐から比較辺に沿って余極限性を移送する。
   これで Δ による**同じ錐**の保存となる。

注意：忘却後の「テンソルと二脚」の錐が D(A) の余積錐だとは主張しない。
D(A) の加法的な余積と、CAlg の余積を忘却したテンソルとは別である。

新欄はホモトピー圏での二脚の可換式を記録する。native な錐の移送に必要な二つの三角形は、
この等式から固定端点の辺のホモトピーを取り出して作る補助補題が要る。
二点離散の図式なので、二脚間の追加の相互 coherence はないが、
**この錐の比較補題そのものは未証明**。それを仮定せずに `IsColimitCone` が直ちに従うとは数えない。
比較補題が不足するなら、条件を coherent な三角形の選択まで含めるかを実装前に調整役へ戻す。

## 29. 経路 B の厳密な前段の設計（ビルドなし）

### 29.1 実際の随伴と既存の単体的分解

係数環を `A`、`P := BarrattEccles.operad A` とする。既存の厳密な随伴は

```lean
F := P.freeAlgebraFunctor
U := Operad.Algebra.forget P
h := P.freeAlgebraAdjunction  -- F ⊣ U
G := h.toComonad             -- 代数圏上。台の関手は U ⋙ F
```

である（合成の記法上 `U ⋙ F` が数学の F U）。余単位は `h.counit`、余乗法は F η U。
`freeAlgebraAdjunction_unit_app` は単位を `P.schurUnit` に、
`freeAlgebraAdjunction_counit_app` は余単位を `X.evaluationHom` に同定している。

`HomotopicalAlgebra/HomotopyFunctionComplex/ComonadSimplicialResolution.lean` の
`SerrePositivity.HomotopyFunctionComplex.ComonadSimplicialResolution` を `R` と略記すると、使う型は

```lean
strictBar (X : P.Algebra) : SimplicialObject P.Algebra := R.diagram G X
strictBarAugmentation (X : P.Algebra) :
  strictBar X ⟶ (SimplicialObject.const P.Algebra).obj X := R.augmentation G X
strictBarAugmented (X : P.Algebra) : SimplicialObject.Augmented P.Algebra
```

最後は `left := strictBar X`、`right := X`、`hom := strictBarAugmentation X` の構造体。
ここにモデル構造・cofibrancy の仮定は不要である。

| 使う既存宣言 | 供給されるもの |
| --- | --- |
| `R.diagram`、`diagram_obj` | 通常の `SimplexCategoryᵒᵖ` 上の全図式、Bₙ(X) = Gⁿ⁺¹ X |
| `R.diagram_face` | `ComonadResolutionOperators.face G X (n+1) i` による面 |
| `R.diagram_degeneracy` | `ComonadResolutionOperators.degeneracy G X n i` による退化 |
| `R.augmentation`、`augmentation_app` | 全図式の増大と、反復余単位による各成分 |
| `ComonadResolutionOperators.face_face`、`degeneracy_face_*`、`degeneracy_degeneracy` | 既存の単体的関係式。書き直さない |
| `ComonadResolutionOperators.face_augmentation`、`degeneracy_augmentation` | 増大と面・退化の可換性 |

自由・忘却随伴を新たな抽象仮定にせず、これらへ実際の `P.freeAlgebraAdjunction` を代入する。
ただし、Bₙ が自由代数であることから台の入力まで cofibrant と結論してはならない。
後段で cofibrant な複体上の自由比較を使うには、入力の cofibrant 置換とその比較が別途必要。
これは厳密な bar の定義・分裂とは分け、③-b の橋の後の比較の課題に残す。

### 29.2 忘却後の追加退化の型と五つの式

忘却後の増大図式の型は

```lean
strictBarUnderlyingAugmented (X : P.Algebra) :
  SimplicialObject.Augmented (Complex A)
strictBarUnderlyingExtraDegeneracy (X : P.Algebra) :
  SimplicialObject.Augmented.ExtraDegeneracy (strictBarUnderlyingAugmented X)
```

`left := strictBar X ⋙ U`、`right := U.obj X`。
増大の成分を `U.map ((R.augmentation G X).app j)` と定め、自然性は既存の増大の自然性へ
`U.map` を適用して示す。定値関手との合成が定義上同一であると無理に仮定しない。

Mathlib `AlgebraicTopology/ExtraDegeneracy` の既存の構造体へ、以下を入れる。

- `s' := h.unit.app (U.obj X)`。
- `s n := h.unit.app (U.obj (ComonadResolutionOperators.power G X (n+1)))`。
  目標の終域は U Gⁿ⁺² X = U F U Gⁿ⁺¹ X。
- `s'_comp_ε`：X における随伴の右三角恒等式。
- `s_comp_δ₀ n`：Gⁿ⁺¹ X における同じ右三角恒等式。
- `s₀_comp_δ₁`：`U.map (h.counit.app X)` に対する η の自然性。
- `s_comp_δ n i`：面の後続添字の再帰式 `face_succ` と、U を適用した面に対する η の自然性。
- `s_comp_σ n i`：退化の後続添字の再帰式 `degeneracy_succ` と、U を適用した退化に対する η の自然性。

追加退化は**忘却後の複体の射**であり、通常は代数射ではない。
したがって代数圏の bar 自身が分裂しているという誤った強化は行わない。
`ExtraDegeneracy.section_`・`section_comp_hom`・`homotopy` は構造体を供給した後に再利用できる。
`OrdinaryBarSourceExtraDegeneracy` は通常の Hom 集合と逆転した単体添字の別の bar なので、
その実例を BE の bar の分裂として使わない。構造体への包装の参考に限る。

### 29.3 X に関する自然性、規模、境界

`powerMap G f 0 := f`、`powerMap G f (n+1) := G.map (powerMap G f n)` とし、
面との可換性は余単位の自然性、退化との可換性は余乗法の自然性で帰納する。
面・退化による通常の単体圏の生成を使って

```lean
strictBarFunctor : P.Algebra ⥤ SimplicialObject P.Algebra
strictBarAugmentedFunctor : P.Algebra ⥤ SimplicialObject.Augmented P.Algebra
```

まで保つ。追加退化の X についての自然性も `h.unit.naturality` から得る。
対象ごとの分裂しか作らず、後で全関手版に自然性を足す設計にはしない。

| 部分 | 新規 Lean の見込み |
| --- | ---: |
| 実随伴の適用、bar・増大・成分の式 | 70〜110 |
| `powerMap`、X の全関手と増大の自然性 | 130〜200 |
| U の下の増大、追加退化と関係式、自然性 | 130〜210 |
| BE の指定単位・評価射の式と公開の包装 | 60〜100 |
| **計** | **390〜620** |

任意の随伴で成り立つ部分は `EInfinity/` の専用補助ファイルへ置き、一般圏の補助として報告する。
新しい `InfinityCategories/` のファイルは作らない。既存の Comonad 分解を変更しない。
上限約 800 行、3 割の緩めも含む既定の停止規則を保つ。
この見込みには bar の ∞ 図式への移送・実現の同定・cofibrant な自由入力への比較・全関手版のテンソル比較を含めない。
それらは③-b の取り込み後の作業で、厳密な分裂だけから完了したとは数えない。

## 30. c と段 4 の組み立ての下書きの所在

今回の依頼の c と組み立てについては、先行して書いた本体のコードがあるため、同じ実装を重複して作らない。
**今回の verify 待機中はビルドも監査もしていない。** 以下は待機前に確認した結果の再掲である。

- c：`Theory/NativeCoproductLegs.lean`（115 行、`7c71d375c`）。
  `barrattEcclesCoprodWith_cocone_leg_left/right` は採用した native 錐の脚を厳密な二包含の区間全体へ同定する。
  `barrattEcclesCoproductTensorNat_inl/inr` と `_carrier` は**既存の厳密な自然変換**が
  その二包含を上の標準テンソル射へ送ることを示す。
  全関手版の `coproduct_tensor` が未供給なので、§28 の欄の無条件の実例まで証明したとは数えない。
- 組み立て：`Theory/Assembly.lean`（89 行、`9728984d0`）。
  `barrattEcclesTheoryOfRemaining` は既証明欄を固定し、残る十八欄だけを引数に取る。
  引数 `coproduct_tensor_legs` の型は、先行する**同じ引数** `coproduct_tensor` を参照する。
  忘却の sifted 保存、presentable、テンソル比較・二脚、通常 Tot の四欄、cdga Tot の五欄、P⁰ の五欄が未供給。
  `baseChange_forget` は追加の K 平坦性仮定なしの本体の証明を代入している。
- `drafts/Shared/BarrattEcclesTheory.lean` は、この組み立てへ十八欄だけを渡す 49 行の作業用実例。
  既証明欄の sorry は除去済み。⑤b の A1 二本、⑤c の A0・A3 は触っていない。

§28 の型案の検収で変更が必要になれば、界面、組み立ての対応する引数、作業用実例を同時に追従する。
その再検証は verify 終了の連絡後に行う。検収前に共通入口や共有監査へ登録しない。

## 31. ④の段 0 の下調べ：G12・M14・M15（紙のみ）

この節は将来の④の設計のための下調べで、W16 の実装範囲を広げるものではない。
地図は現在の枝の `research/htt-coverage/{items.csv,review/}` と
`research/ha-coverage/{items.csv,review/}` を読んだ結果であり、CSV は編集しない。
以下の `none`・`partial` は地図の調査上の分類であり、新しく型検査した証明の判定ではない。
KL-W1 の改名を先取りせず、現在の main 系統の宣言名・モジュール名を記す。

### 31.1 G12：BE の CAlg の presentable 性

最終の型は既存の界面どおりである。

```lean
(S : Type u) [CommRing S] ⊢
  @F2.Presentable.IsPresentable (barrattEcclesCore.CAlg S)
    (barrattEcclesCore.quasicategory S)
```

準圏のインスタンスは既存の `barrattEcclesCore.quasicategory S` を明示している。
`IsPresentable` の中身は同じ宇宙での accessibility と**全ての小さい native 余極限**の存在。
単に通常の厳密代数圏に余極限があることではない。

再利用できる本体：

- `derivedInfinityCategory_isPresentable`（`Derived/Presentable/DerivedCategory`）：非有界 D(S) の実際の presentable 性。
- `Operad.freeAlgebraAdjunction`、`Algebra.forget_isCardinalAccessible`、`freeAlgebra_finitelyPresentable`：
  厳密な自由・忘却、通常圏での filtered 保存と自由像の小ささ。
- `Operad/AlgebraSiftedColimits.forget_createsSiftedColimitsOfShape`：通常の dg 代数の sifted 余極限。
- `BarrattEccles.modelCategory`、`modelCategory_cofibrantlyGenerated`：実際に構成された模型と生成族。
- W16 の `cAlgForgetDerived_conservative` と無条件の係数変更の比較。
  ただし `forget_preservesSifted` は引き続き未供給である。
- `F2.Presentable.IsPresentable.of_equivalence`：同じ native 準圏の全同値を**構成できた後**の移送。

地図との対応：

| 地図の項目 | 現在の分類と使い分け |
| --- | --- |
| HA 3.2.3.5 | `none`。G12 の直接の数学的対応。全 ∞ オペラッドの一般定理を実装することは D75 の BS 経路の要件ではない |
| HA 3.2.3.1 | `none`。厳密な sifted 保存から native な保存への橋は未供給。③-b と W16 の BE 固有部分を使う |
| HA 4.7.3.5 | `partial`。Mathlib の通常圏の Barr–Beck はあるが、U-split 単体図式による ∞ モナド性まではない |
| HTT 5.5.1.1 | `partial`。presentable から前層反射表示を得る結果はある。CAlg の presentability を前提なしに作る逆方向ではない |
| HTT A.3.7.6 | `none`。組合せ的な単体模型から native な presentability へ移す汎用比較は地図上未供給 |
| HA 1.3.5.21 | `partial`。加群の D(S) の presentability は本体にある。CAlg へは別の橋が要る |
| HTT 5.5.8.15 | `own`。PΣ の filtered・幾何学的実現による全関手の普遍性は再利用候補。ただし CAlg 全体を PΣ と同一視する証明はない |

提案経路は、D(S) の presentability、誘導された自由・忘却随伴、③-b の実現の橋と W16 の sifted 保存を使い、
**BE に実際に作用する accessible なモナドの代数との全準圏比較**を作るもの。
その代数圏の accessibility と全小余極限から G12 を得る。
汎用の HTT A.3.7.6 を作る案は代替であり、現在の BE 模型が simplicial combinatorial であるという追加証明も必要。
cofibrantly generated だけからその仮定を満たしたことにしない。

不足は、(a) 誘導されたモナドと全 Eilenberg–Moore 準圏、(b) 同じ U の実際のモナド性の比較、
(c) accessible なモナドから native presentability を得る一般の定理。
U が保存的・sifted 保存である二条件だけを別の構造体に詰めて、その結論を仮定に入れる実例にはしない。

規模の初期見込み：一般のモナド性・代数圏の橋が供給済みなら BE への適用は **600〜1,000 行**。
その橋も④で作る場合は一般部分 **2,400〜4,000 行**、適用を合わせ **3,000〜5,000 行**。
これは未実装の一般部分を含む幅のある見積もりであり、現在の模型の欄だけの小さな証明という見込みではない。
③-b の完成物を読んだ後、重複する一般部分を差し引いて段 0 で確定する必要がある。

### 31.2 M14：Frobenius 半線形な P⁰

供給する入口は、既存の次の全自然変換である。

```lean
powerOp0 (k : Type u) [CommRing k] (p : ℕ) [Fact p.Prime] [CharP k p] :
  FunctorHom (forget k) (forget k ≫ restrictD (frobenius k p))
```

加えて、同じ変換について π₀ で Frobenius、πₙ（n > 0、つまり H⁻ⁿ）で零、
離散入力と cosimplicial 可換環の Tot で指定 Frobenius 射に一致する四条件が必要。
`powerOp0_pos` は H の**負次数**の条件であり、正のコホモロジー次数の消滅と取り違えない。
単に各ホモロジー群に関数を定義するだけでは界面の型を満たさない。

再利用：BE の `operad` の作用と自由代数、`arityRepresentationChain` と実際の対称群の射影解像度、
`twoColorCoefficientComparison` など指定係数射を同じ解像度で管理した経験と API、
W16 の係数制限 `barrattEcclesRestrictD`・`restrictD_homologyIso`・π₀ 比較・離散入力比較。
ただし二色の係数比較は P⁰ の構成そのものではなく、p 個の入力の巡回対称性を持つ冪作用を供給しない。
`drafts/Shared/EInfinityPowerOperation.lean` は界面からホモトピー上の作用を読む利用側の型を与えるが、
`E.powerOp0` を引数として使っているため模型での構成の証拠にはしない。

地図：主な出典は **DAG XIII Construction 2.2.6・Remark 2.2.7** で、HTT・HA の項目表に
その番号の独立項目はない。対応しない HA の定理番号を P⁰ に割り当てない。
HA 3.1.3（自由代数）・3.2.3.1（実現等）・4.7.3.5（モナド的な分解）は構成を延ばすための周辺項目であり、
それらの完成で P⁰ が既に得られるとはしない。HTT の presentable・余極限の項目も操作の係数計算を供給しない。

不足の分解：

1. BE の p 入力の作用から、k 線形ではなく φₖ 半線形な鎖レベルの指定操作を作る。
   符号、巡回群の作用、微分と作用の整合を含む。既存の通常の Frobenius 環準同型だけでは不足。
2. その操作を弱同値で局所化して、U 全体の coherent 自然変換として降ろす。
   ホモロジー上の自然性だけで置き換えない。
3. 零次と正のホモロジー次数での値を、同じ操作について計算する。
4. 離散入力と Tot の Frobenius との**同じ変換の成分の一致**を証明する。
   Tot の比較は G10 と係数制限の比較を待つ。

初期見込み：係数・鎖レベルの操作と値の計算 **1,600〜2,800 行**、
自然変換と局所化 **600〜1,000 行**、離散・Tot の照合 **600〜1,200 行**、
**計 2,800〜5,000 行**。p 群の解像度の追加 API が必要なら再見積もりする。
この段階では実装・新しい界面欄の追加を行わない。

### 31.3 M15：一般の E∞ 底 R 上の descendability

利用側の入口は `drafts/Shared/Descendable.lean` の

```lean
IsDescendableOver (R B : (E.CAlg A) _⦋0⦌) (f : SSet.Edge R B) : Prop
HasDescentIndexLEOver (R B : (E.CAlg A) _⦋0⦌) (f : SSet.Edge R B) (n : ℕ) : Prop
```

である。一般の R に対し **Mod_R(D(A))** の thick ⊗-ideal として定義する。
`R = Δ_T` は離散環であるとは限らない。固定した離散 A の D(A) の定義だけでは Lemma 8.6 に足りない。
M15 を `EInfinityTheory` に新たな欄として入れる設計にはしない（既存の界面設計の決定）。

再利用できるもの：

- D(A) の `tensorWith`、安定性、fiber/cofiber と極限・Tot の部品。
- `StableVertexClosure` と、`dgThickClosureProperty_iff_nativeStableRetract` など
  native な安定閉包と retract の既存比較。これらは指定 dg 部分圏の厚い閉包であり、相対テンソルへの閉性は別途必要。
- 通常の内部加群の `MonoidalModuleColimits.colimitCoconeLiftsToColimit`、
  `MonoidalModulePresentability.isLocallyPresentable`、`MonoidalBalancedTensor.symmetricCategory`。
  通常の対称モノイダル圏内の結果であり、一般の E∞-R 加群の ∞ 圏への比較を供給しない。
- W16 の指定余積と二脚の比較は将来の Amitsur 図式の構造射の照合に使える。
  任意の相対テンソル B ⊗ᴸ_R C は、絶対テンソルの欄一つから直ちに得られるものではない。

地図との対応：

| 地図の項目 | 対応と現状 |
| --- | --- |
| HA 4.2.1.15 | `partial`。通常圏の内部モノイド・内部加群の型がある。全 E∞ 底の加群準圏ではない |
| HA 4.2.3.5・4.2.3.7 | `partial`。通常の加群の余極限・局所可呈示性。native の一般の R-加群にする橋が不足 |
| HA 4.5.1.1 | `partial`。通常の固定可換環の加群圏。一般の可換代数対象への適用は未供給 |
| HA 4.5.2.1 | `partial`。通常の内部加群の対称モノイダル相対テンソルはある。導来相対テンソルとの全比較が必要 |
| HA 4.5.3.1 | `none`。基底 R を動かす加群の高次圏と底変換の全体が不足 |
| HA 1.1.3.3 | `partial`。安定部分圏の一部の判定。thick ⊗-ideal と有限指数判定全体ではない |

descendability 自体の直接の出典は **Mathew Definition 3.18・Proposition 3.22**、
指数と Frobenius 余極限は **BS17 §11.2・Lemma 11.22**。
これらを HTT/HA の一般の「降下」項目の完成に数えない。特に HTT §6 のトポスの降下は別の主張である。

不足と順序：

1. 一般の BE 代数 R 上の加群の局所化、安定性、相対テンソルと内部 Hom、底変換の coherent な構成。
   この模型の構成と、抽象的な数学の一般定理は分ける。
2. 安定対称モノイダルな加群圏で thick ⊗-ideal・指数を定義し、
   `descendable ↔ ∃ n, index ≤ n`、底変換・合成・テンソルでの安定性を示す。
3. 指数から Amitsur の塔の nilpotence／収束を導き、任意の R-加群の Tot 降下へ進む。
   有限段で塔が一律に分裂する、と未証明に仮定しない。
4. RHom による指数 ≤ 2、Frobenius 余極限の指数評価、完備版を同じ相対底 R で示す。

`drafts/Shared/Descendable.lean` の一般底の定義はまだ sorry、RHom と完備版の一部は
`True := by trivial` の印である。これらは必要な主張の証明として数えず、実装前に正しい型を確定する。

初期見込み：一般の R-加群・相対テンソルの模型と比較 **2,500〜4,500 行**、
thick ⊗-ideal・指数と安定性 **900〜1,500 行**、Amitsur の塔・降下・指数評価と完備版 **1,400〜2,500 行**、
**計 4,800〜8,500 行**。加群圏の一般部分が供給済みなら残る部分は **2,300〜4,000 行**。
この幅は一般の E∞ 底を落とさない場合の初期見込みで、離散底だけで完了扱いにはしない。

### 31.4 現在の待機と再開順

今回は紙の検討と既存コード・地図の読取りだけを行った。ビルド・監査は走らせず、鍵も要求していない。
新たな Lean 実装や既存の界面の変更は加えていない。
調整役の型の検収を待つ間も独立の紙の作業は可能だが、verify 終了の連絡までは検証しない。
終了の連絡後は、§27 の作業木に残っている自由比較の六本の型検査と監査から再開する。
bar の実装は a の区切りの後、③-b を要する実現・Tot はその取り込みの後という順序を保つ。

## 32. verify 待機中の Lean 下書き（11-12 10 時の依頼）

D78 により §28 の `coproduct_tensor_legs` の型が承認された。
二点離散の図式なので二脚のホモトピー圏での可換式を維持し、欄を coherent な三角形の選択へ強めない。
指示書 §13 の錐の移送は一般補題として、指定の将来のパスに下書きを置いた。
**この節の新しい三本は未検証・未コミットであり、証明の完成・監査成功とは数えない。**

### 32.1 二点余錐の一般の移送

下書きの場所：
`SerrePositivity/InfinityCategories/Kerodon/LimitsAndColimits/LimitsAndColimits/BinaryCoconeApexTransport.lean`（72 行）。
KL-W1 枝にも同名のファイルがないことを読取りで確認し、既存ファイルは変更していない。
名前空間も `SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits` とした。

`p : Δ[0] ⨿ Δ[0] ⟶ X`、`c d : JoinCocone p` を固定する。
`binaryCoconeVertexIso_of_apexIso` は、`e : VertexIso c.vertex d.vertex` と
`[c.left] ≫ e.hom = [d.left]`・`[c.right] ≫ e.hom = [d.right]` から、
**同じ p 上の coslice の頂点同型**を作る。
`isColimitCone_iff_binaryCocone_apexIso` と
`IsColimitCone.of_binaryCocone_apexIso` はその同型で指定余錐の余極限性を移す。
安定性、模型、テンソル構造、辺の三角形の追加仮定は置かない。

既存の `exists_binaryCoconeEdgeLift_of_comm` を再利用し、頂点の同型を代表する辺を持ち上げ、
`leftFibration_reflects_invertibleEdge` と `isColimitCone_iff_of_vertexIso` を使う証明を書いた。
現在の枝の import と旧公開名を使っており、KL-W1 の改名表への追従後に検証する。
配置表では `BinaryCoconeEdgeLift` が一般的な型のまま HA/StableInfinityCategories 側へ移る予定なので、
取込み後の一般補題の依存先の配置も確認対象とする。関連する共有ファイルには手を入れていない。

### 32.2 厳密な bar と BE への適用

- `SerrePositivity/EInfinity/StrictAdjunctionBar.lean`：236 行。
  `powerMap` と面・退化・増大の自然性を用い、既存の Comonad 分解を
  `diagramFunctor`・`augmentedFunctor` に束ねる。
  任意の厳密な随伴 `h : F ⊣ U` の `h.toComonad` へ適用し、
  `underlyingAugmented`・`underlyingExtraDegeneracy`、切断、増大との合成、追加退化の自然性まで書いた。
  追加退化の五つの条件には、既存の面・退化の式、右三角恒等式、単位の自然性を使用する。
- `SerrePositivity/EInfinity/BarrattEccles/Theory/StrictBar.lean`：58 行。
  実際の `(operad A).freeAlgebraAdjunction` を代入する。
  bar・増大の全関手、忘却後の分裂、零次の増大と評価射の一致、零次の切断と Schur 単位の一致を公開する下書き。

**合計 294 行**で、上限約 800 行以内。一般部分はモデル構造を仮定せず、
代数圏内の追加退化、実現の保存、局所化との同定、bar の入力の cofibrant 性は主張していない。
一般圏の補助は専用の `EInfinity/StrictAdjunctionBar.lean` に置き、移動候補と印を付けた。

### 32.3 A2 のコメントと再開順

`drafts/A2/BaseChangeAndTensor.lean` の `derivedPrismaticCohomology_tensor` の証明手順のコメントを、
§28.2 の指定比較辺 → `coproduct_tensor` → `coproduct_tensor_legs` →
多項式 Künneth と sifted 表示 → 保存的な忘却 → 一般の二点余錐の移送、という順に直した。
宣言の型と既存の sorry は保った。コメントと空白を除いた Lean の文字列が変更前と同じことだけを
軽いテキスト比較で確認した。これは Lean の型検査ではない。

今回、ビルド・監査・鍵の要求は一切行っていない。
三本には sorry・admit・axiom を書いていないが、型検査していないため監査の宣言数は未記入。
A2 のコメントとこの報告だけをコミットし、新規三本は自由比較の六本と同じく作業木に残す。
verify 終了の連絡後は、**自由比較六本 → 一般の二点余錐の移送 → 厳密な bar の二本**の順で検証し、
成功した区切りで監査とコードのコミットを行う。KL-W1 の取り込み・改名表への追従が必要なものは先に行う。

## 33. verify 後の再開：自由比較の作業木の六本を検証

§27 の六本は対象ビルドと再帰監査が成功した。
標準パターンを左右のテンソル冪へ移す複体の同型と指定包含の式、語の濃度による軌道の被覆、
実際の標準代表の安定化群の入力と指定包含・射影、直交性、誘導した入力表現の有限直和の普遍性を供給する。
誘導包含による射の検出は `Rep.indResAdjunction` の自然性から標準代表の包含へ戻して証明した。
未供給の被覆条件を新たな仮定として残していない。任意の入力複体を許す。

| 登録候補（接頭辞 `SerrePositivity.EInfinity.BarrattEccles.Theory.`） | 行数 |
| --- | ---: |
| `TwoColorStandardPowers` | 52 |
| `BinaryTensorWordCounts` | 111 |
| `TwoColorInputMatrix` | 65 |
| `TwoColorStandardInclusion` | 75 |
| `BinaryTensorOrbitInputs` | 100 |
| `BinaryTensorOrbitDecomposition` | 104 |
| **計** | **507** |

`TwoColorInputMatrix` の比較同型は、その構成に部分群の所属判定が入る。
当初、具体的な二色部分群の計算可能な判定と、一般定理の classical な判定の間の照合で型検査が遅くなった。
同じ指定比較同型のために、補題の型の `letI : DecidablePred (· ∈ H)` で一般定理と同じ判定を明示した。
新しい数学的仮定や別の比較同型へ置き換えたのではない。最終の一本は 2.7 秒でビルド成功、追加警告零。

対象ビルドの成功は `/tmp/bsw16/graded/resume-free-inputs-03.log`（軌道直和）と
`resume-free-inputs-10.log`（最後の行列比較）、先行の成功分は §27 の記録に対応する。
六本の一括の再帰監査は `/tmp/bsw16/graded/audit-free-inputs-six.log` で成功：**71 宣言、標準三公理のみ**。
追加本体に sorry・admit・新規公理はない。各ビルド・監査の終了を回収してから次の鍵を取った。

a は §22 の 902 行と合わせて **1,409 行**。自由代数の Hopf 比較の弱同値までは未完了。
標準入力同型のブロック置換との照合、誘導表示と係数の全複体としての Schur 分解、
実際の Hopf 自由比較の同定が残る。段階の完了と今回の作業木の検証を混同しない。
取り込み待ちの新規モジュールは、§26 の二十本と今回六本で二十六本。
共通入口と共有監査スクリプトは編集していない。

次は依頼された検証順に一般の二点余錐の移送、厳密な bar の下書きを検証し、その後 a の残りへ戻る。
