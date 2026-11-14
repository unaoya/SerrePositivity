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

## 34. D78 の二点余錐の一般の移送補題の検証

§32.1 の `BinaryCoconeApexTransport.lean`（72 行）は対象ビルドと監査が成功した。
`binaryCoconeVertexIso_of_apexIso`、`isColimitCone_iff_binaryCocone_apexIso`、
`IsColimitCone.of_binaryCocone_apexIso` の三つの公開補題を供給する。
一般の準圏と固定された二点離散図式に対する主張で、安定性・模型・テンソル構造は要求しない。
辺の三角形の選択を仮定に強めず、ホモトピー圏での二脚の可換式から構成した。

ビルド `/tmp/bsw16/graded/binary-cocone-apex-02.log` は成功。
監査 `/tmp/bsw16/graded/audit-binary-cocone-apex.log` は **4 宣言、標準三公理のみ**。
sorry・admit・新規公理はない。KL-W1 の規則の名前空間
`Kerodon.LimitsAndColimits.LimitsAndColimits` による重複名前空間の警告三件は残した。

登録候補は
`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.BinaryCoconeApexTransport`。
これは取り込み前の枝で旧 import・既存の旧宣言名を用いて検証したものであり、
KL-W1 取り込み後の改名表への追従と、その後の対象検査は別途必要。
§32.1 の一般の補助の依存先の配置の確認も引き続き取り込み時の確認事項。
入口と共有監査スクリプトは編集していない。取り込み待ちの新規モジュールは二十七本。

自由比較の六本、D78 の移送補題の検証を区切り、次は厳密な bar の二本を検証する。

## 35. 経路 B の厳密な bar の前段：対象ビルドと監査が成功

§32.2 の二本を検証した。
`SerrePositivity.EInfinity.StrictAdjunctionBar` は任意の厳密な随伴の実際の余モナドを用い、
通常の `SimplexCategoryᵒᵖ` 上の bar の全関手、増大の全関手、右随伴を適用した増大と追加退化、
追加退化からの自然な切断と増大との合成、対象に関する追加退化の自然性を供給する。
既存の `ComonadSimplicialResolution` を再利用し、対象に関する自然性を面・退化と単体圏の生成で証明した。
一般圏の補助として、移動候補の印を module docstring に付けている。

`SerrePositivity.EInfinity.BarrattEccles.Theory.StrictBar` は、
構成済みの `(operad A).freeAlgebraAdjunction` を実際に代入し、BE の bar・増大・忘却後の追加退化を供給する。
零次の増大は既存の `evaluationHom`、忘却後の零次の切断は同じ `schurUnit` へ同定した。

追加のモデル構造、cofibrancy、実現の保存、局所化の同定を仮定していない。
追加退化を**代数圏内の分裂**としては主張していない。
bar の各項の自由代数への入力を cofibrant と示すこと、bar を ∞ の図式へ移し実現を同定すること、
全関手版の `coproduct_tensor` と `forget_preservesSifted`、Tot の群は引き続き未供給。

| 新規登録候補 | 行数 |
| --- | ---: |
| `SerrePositivity.EInfinity.StrictAdjunctionBar` | 266 |
| `SerrePositivity.EInfinity.BarrattEccles.Theory.StrictBar` | 60 |
| **計** | **326** |

上限約 800 行以内。対象ビルド `/tmp/bsw16/graded/strict-bar-06.log` は成功、追加警告零。
再帰監査 `/tmp/bsw16/graded/audit-strict-bar.log` は **49 宣言、標準三公理のみ**。
sorry・admit・新規公理はない。各ビルドと監査は別々の鍵で行い、終了後に返却した。

これで依頼された「自由比較六本 → 二点余錐の一般の移送 → 厳密な bar」の検証順を完了した。
共通入口と共有監査の登録は行っていない。§34 と合わせ取り込み待ちの新規モジュールは二十九本。
KL-W1 の取り込みと改名表への追従は調整役からの案内の後に行う。
次は a の残りへ戻る。厳密な bar の前段を検証したことを、a や経路 B の全体の完了とは数えない。

## 36. a：標準入力の作用の照合と、規模による中間停止

### 36.1 今回閉じた部分

`SerrePositivity.EInfinity.BarrattEccles.Theory.TwoColorStandardAction`（104 行）を追加した。
指定標準入力から左右のテンソル冪への同型について、実際の signed permutation action と可換であることを示す。
左右の冪を和の冪へ含める射の式を使い、標準パターンを固定する証明を保ったまま、
二色部分群の指定射影のブロック置換と照合した。
`twoColorStandardPowersIso_action` は抽象的に作用が存在するという主張ではなく、同じ指定同型の可換式である。
入力の有界性・零微分・平坦性は要求しない。

対象ビルド `/tmp/bsw16/graded/standard-action-04.log` は成功。
新規ファイルの追加警告は零。依存先の既報の `ZeroArity` の二警告はそのまま。
再帰監査 `/tmp/bsw16/graded/audit-standard-action.log` は **17 宣言、標準三公理のみ**。
sorry・admit・新規公理はない。

登録候補は上の一本。取り込み待ちの新規モジュールは §35 の二十九本と合わせ三十本。
入口・共有監査には登録していない。

### 36.2 残りの比較を再分解した結果

a の既存 §22 の五本は 902 行、§33 の六本は 507 行、今回 104 行で、**現時点の実測は 1,513 行**。
標準入力の作用の照合まで進め、残りの実際の始域・終域を照合したところ、
§22.3 の第四行「Schur 分解・全複体の比較」には、異なる三つの比較が必要であることを確認した。
これらは単に同型を合成するだけの既存の公開宣言では供給されていない。

1. `TwoColorInducedCoefficients.twoColorInducedSourceIso` の入力 V は **一つの Rep**。
   任意の V の複体に対しては、誘導入力と制限係数の余不変の比較を両変数で自然にし、
   入力と係数の双方の微分を保つ全複体の比較へ持ち上げる必要がある（120〜180 行の見込み）。
   `TwoColorComplexInputs.twoColorComplexInputHomotopyEquiv` は任意の V の複体で使えるが、
   その始域は既に二色群へ制限した係数の全複体であり、この誘導側からの比較を供給するものではない。
2. `SchurDegreeDecomposition.schurDegreeBidegreeIso` は **各次数の加群の同型**。
   `schurFunctor` の全複体を arity と余不変の全複体の直和へ同定し、指定生成射と微分を照合する必要がある
   （210〜300 行の見込み）。既存の次数ごとの同型だけを複体の同型として扱わない。
3. 終域の二つの自由代数のテンソルを、二色の入力とテンソル係数の同じ直和全複体へ移す必要がある。
   arity の二重直和と全複体の交換、入力と係数の順序と符号、指定生成射の照合を含む
   （170〜260 行の見込み）。Mathlib の `mapBifunctorFlipIso`・全複体の対称性は部品に使えるが、
   この BE の実際の Schur 表示と指定比較との同定を既に持っているわけではない。

この第四行だけで **500〜740 行**の新しい見込みとなる。旧 250〜350 行との差は、
同じ型の同型の連結と思っていた部分に、Rep とその複体、次数ごとの Schur 表示と複体の Schur 表示、
係数・入力の全複体と実際の二自由代数のテンソル、という別の型の橋があったため。
鎖ホモトピーを作り直す必要を見込んでいるのではなく、既存の指定した係数の同値を**同じ射**へ接続するための比較である。

### 36.3 五行の見込みと実測の差

§22.3 と同じ五行を保ち、その外へ作業を追加していない。
以下の実測は新規 611 行を各行へ割り当てたもので、基礎の 902 行とは重ねて数えない。

| §22.3 の行 | 旧残りの見込み | 今回までの追加実測 | なお残る見込み | 更新後のこの行の合計 |
| --- | ---: | ---: | ---: | ---: |
| 1. 標準入力と左右の冪・ブロック置換 | 80〜120 | 231（52 + 75 + 104） | 70〜110：分離された冪の表現の複体との同型への包装 | 301〜341 |
| 2. 色の個数・arity の添字 | 60〜90 | 111 | 80〜120：固定 arity の群と m+n の群の移送、係数・誘導表示の再添字 | 191〜231 |
| 3. 実際の誘導入力の直和 | 200〜300 | 269（65 + 100 + 104） | 80〜120：次数ごとの指定有限直和を微分つきの直和へ束ねる | 349〜389 |
| 4. Schur 表示と全複体 | 250〜350 | 0 | 500〜740：§36.2 の三比較 | 500〜740 |
| 5. 実際の Hopf 自由比較との一致・弱同値 | 250〜350 | 0 | 250〜350 | 250〜350 |
| **追加分の計** | **840〜1,210** | **611** | **980〜1,440** | **1,591〜2,051** |

基礎の 902 行を含め、a 全体の更新後の見込みは **2,493〜2,953 行**。
現在の承認は約 2,100 行、3 割の緩めを含む継続の上限は **2,730 行**。
今回の見込み上限 2,953 行は約 41% の超過となり、3 割を超える。
指示書 §12 の 5 の停止規則に従い、**ここで a の Lean 実装を止めて報告する**。
今回通った指定作用の補題の監査・コミットだけを済ませ、それ以降の橋の実装は始めない。
上限を自分の判断で広げない。経路 A のセル対には戻っていない。

bar の厳密な前段は §35 のとおり検証済みだが、この不足を代わりに消すものではない。
経路 B もまず自由比較を必要とするため、現時点で `coproduct_tensor`・その二脚の全実例が無条件に完成したとはしない。
今回の依頼の下書きの検証順とコミットは全て完了。共有の鍵・整理券を自分は保持しておらず、
今後は調整役の判断を待つ。KL-W1 の改名表への追従は案内を受けてから行う。

## 37. KL-W1 の追従：取り込み前の collect で drafts の未解決宣言により停止

### 37.1 対象と取り込み前の状態

main への KL-W1 取り込み（`19f081dcb`、案内時の main は `8f68a475d`）を受け、
`kerodon-layout-w1-report.md` の「レーン別の追従表」を読んだ。
コードの直前の HEAD は `2ae14588e`、検証済みのコードはすべてコミット済み、未検証の下書きはなかった。

配布の `kerodon-layout-stop-3/bs-impl-files.json` の 32 本へ、10:21 後に追加した
`SerrePositivity/EInfinity/BarrattEccles/Theory/TwoColorStandardAction.lean` を加え、**33 本**の一覧を作った。
この一覧は main との merge base からの枝固有の全 Lean 差分と集合として一致し、漏れ・余分とも零。
リポジトリ内の控えは `formalization-plans/bhatt-scholze/klw1-followup/bs-impl-files.json`。
実際に渡した一覧と成果物は `/tmp/bsw16/klw1-followup/` に保存した。

### 37.2 実行と停止の根拠

取り込み前の同じソースと成果物から、配布した KL-W1 作業木の道具を使って collect を実行した。
Lean を使う収集の間だけ `--wait 3600` の鍵を一枚取得した。

```text
python3 /Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout/scripts/refactor/klw1_namespace.py collect
  --root /Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-impl
  --files /tmp/bsw16/klw1-followup/bs-impl-files.json
  --output /tmp/bsw16/klw1-followup/before-index
```

**本体 31 本の採取まで成功**したが、32 本目の
`formalization-plans/bhatt-scholze/drafts/A2/BaseChangeAndTensor.lean` で Lean の解決エラーとなり、
collect が終了コード 2 で止まった。ログは `/tmp/bsw16/klw1-followup/collect.log`。

最初のエラーは同ファイル **43 行目**の
`unknown namespace SerrePositivity.BhattScholze.Perfectoidization.Derived`。
続けて `AnimatedAlgebra`、`derivedPrismaticCohomology`、`animatedCompletionUnit` などを解決できず、
それらの `(E := E)` の引数にも連鎖したエラーが出る。
このファイルの先頭には、他の drafts を将来 import する旨のコメントがあり、実際の import には入っていない。
例えば `AnimatedAlgebra` は `drafts/A2/AnimatedAlgebra.lean`、
`derivedPrismaticCohomology` は `drafts/A2/DerivedPrismaticCohomology.lean`、
`animatedCompletionUnit` は `drafts/A7/AnimatedDomain.lean` の宣言である。
今回の A2 の編集は証明方針のコメントだけで、型を変えてはいない。

これは未実装の sorry の警告ではなく、単独での elaboration が成立しない drafts に対する参照採取のエラー。
実装レーンで仮の宣言を足す、他レーンの drafts を実装する、対象を黙って除く、
採取していない参照を文字列で推測して書き換える、という対応はしていない。
「迷う箇所は書き換えず報告、KL-W1 側で道具を直す」という依頼に従い、ここを報告する。

### 37.3 保存物、未実施の段、再開の入口

- `before-index/`：成功した本体 31 本の参照 JSON。collect が中断したため、全 33 本の完了マニフェスト
  `before-index/files.json` は生成されていない。完全な before_index とは数えない。
- `before-sources/`・`before-state.json`：全 33 本の改名前のソース、各ソースと二つの改名表の SHA-256、コードの HEAD。
  停止後も全 33 本のソースのバイト列が採取入力と一致することを確認した。
- `drafts/Shared/BarrattEcclesTheory.lean`：一覧の最後の一本で、A2 で停止したため**未採取**。
- `direct-importers-before.json`：検証範囲の準備として、本体の直接 importer 六本、drafts 十四本を列挙した。
  まだこれらの移行後のビルドを行ったという結果ではない。

**rewrite・プレビューの反映・main の取り込み・移行後の対象ビルドは、すべて未実施。**
`review.json` もまだ作っていないので、保留零とは報告しない。
自分の収集プロセスは終了を回収済み、鍵と整理券は返却済み。
今回コミットするのは対象一覧とこの停止報告だけで、Lean のソースは書き換えていない。

KL-W1 側から、このように単独では解決しない drafts の採取方法の案内・修正を受けた後に、
同じ入力で必要な採取を完了し、プレビューと review を確認してから main の取り込みへ進む。
改名を済ませて報告した後に a を再開する、という順序を守る。
そのときの a の上限は今回の新しい承認どおり **約 3,000 行、3 割の緩めはなし**とする。

## 38. KL-W1 の追従：drafts を除いたプレビューで八本が保留

§37 への調整役の指示に従い、drafts 二本を対象から外した。
対象一覧 `klw1-followup/bs-impl-files.json` は本体 **31 本**だけに更新した。
この 31 本の採取済み JSON がすべてあり、各ソースのバイト列も現在と完全一致することを確認し、
採取済みの `before-index/files.json` を同じ 31 本の範囲に揃えて再利用した。
再度の Lean の採取は行っていない。drafts の追従は調整役の担当とし、A2 のコメントも保った。
本体だけで数えると、移動対象の旧 import があるのは **10 ファイル・29 行**。
配布時の 11 ファイル・31 行との差は、今回除外した A2 drafts の二つの旧 import である。

### 38.1 rewrite の実行結果

同じ取り込み前のソースと採取済み索引から、配布の道具で次を実行した。

```text
python3 /Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout/scripts/refactor/klw1_namespace.py rewrite
  --root /Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-impl
  --files /tmp/bsw16/klw1-followup/bs-impl-body-files.json
  --index /tmp/bsw16/klw1-followup/before-index
  --plan /Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout/scripts/refactor/targets/kl-namespace-map.json
  --output /tmp/bsw16/klw1-followup/preview-body
```

終了コード **1**、**23 本**のプレビューを出力し、**8 本・16 箇所**を `review.json` に保留した。
出力されたうち 14 本はソースと同一、9 本には **138 行追加・138 行削除**のプレビュー差分がある。
差分を読み、import・`open`・解決された宣言名の置換として確認したが、まだ作業木へ反映していない。
一覧は `klw1-followup/preview-stats.json`、全差分は `/tmp/bsw16/klw1-followup/preview-body.diff`。

### 38.2 保留の全件（道具側への引き継ぎ）

そのままの診断 JSON を `klw1-followup/review.json` に保存した。
位置は取り込み前の同じソースの UTF-8 バイト位置であり、以下の行番号は読みやすい控え。

| ファイル（`SerrePositivity/EInfinity/` 以下） | 行 | 保留された構文 |
| --- | --- | --- |
| `BarrattEccles/Theory/CoproductDKHom.lean` | 22 | `open` の `SimplicialLocalization` |
| `BarrattEccles/Theory/CoproductNativeUniversal.lean` | 26・27 | `SerrePositivity.InfinityCategories.HomotopyLimits`・`SimplicialLocalization` |
| `BarrattEccles/Theory/EnrichedPointPrecomposition.lean` | 21 | `SimplicialLocalization` |
| 同上 | 50・57 | `RelativeCategory.{u}` の二箇所 |
| `BarrattEccles/Theory/NativeCoproduct.lean` | 22・23 | `SerrePositivity.InfinityCategories.HomotopyLimits`・`open scoped Simplicial` |
| `BarrattEccles/Theory/NativeCoproductCocone.lean` | 31・32 | `SimplicialLocalization`・`open scoped Simplicial` |
| `BarrattEccles/Theory/NativeCoproductLegs.lean` | 22〜24 | `SerrePositivity.InfinityCategories.HomotopyLimits`・`SimplicialLocalization`・`open scoped Simplicial` |
| `Interface/Theory.lean` | 41・42 | `SerrePositivity.InfinityCategories.HomotopyLimits`・`open scoped Simplicial` |
| `StrictAdjunctionBar.lean` | 26 | `ComonadResolutionOperators` |

14 箇所の理由は **`explicit opens policy needed for a renamed namespace`**。
残る二箇所は **`non-identifier syntax for SerrePositivity.EInfinity.SimplicialLocalization.RelativeCategory`**
で、編集位置のソースはどちらも `RelativeCategory.{u}`。

依頼どおり、保留箇所の `open` 方針や宇宙適用の編集を手で推測していない。
改名表と採取器のソースにも変更していない。KL-W1 側でこの診断を扱う道具・方針の案内を待つ。

### 38.3 現在の状態

Lean のソースは 31 本すべて採取時と同じまま。main の取り込み、プレビューの反映、
移行後の変更ファイル・直接 importer の対象ビルドは**まだ行っていない**。
今回の rewrite は Python によるプレビュー作成だけで、鍵も要求していない。

今回コミットするのは、本体のみの一覧、診断・プレビュー統計、この報告だけ。
drafts の改名は調整役に委ねる。KL-W1 の追従を完了して報告してから、
a を **上限約 3,000 行、緩めなし**で続ける順序は変えない。

## 39. 道具の修正待ちの間の a：入力と arity の複体全体での比較

§38 の 16 箇所は KL-W1 の道具・open 方針の修正を待つ、という調整役の指示を受け、
その間に a を今の main 取り込み前の枝で再開した。採取済みの本体 31 本を変えず、
新規の補助ファイルだけに進めた。全 31 本の SHA-256 が採取時と同じことも再確認した。
改名表・道具・drafts には変更していない。

### 39.1 検証済みの四本

以下は `SerrePositivity/EInfinity/BarrattEccles/Theory/` 以下。いずれも任意の入力の複体を扱い、
入力を零微分・有界・平坦なものに限定していない。

| 新規モジュール | 行数 | 今回閉じた比較 |
| --- | ---: | --- |
| `TwoColorSeparatedInput` | 87 | 指定標準入力と左右のテンソル冪の同型を、実際の二色部分群上の表現の複体の同型へ持ち上げる。順射も元の指定射 |
| `BinaryTensorOrbitComplex` | 69 | 標準代表から誘導した入力の直和を、元の入力の複体へ同定。指定包含、微分、余極限性を保持 |
| `TwoColorInducedComplexInputs` | 103 | 誘導表現と余不変の同型の入力方向の自然性を証明し、任意の入力複体の二重複体・直和全複体へ持ち上げる。指定 Hopf 係数射の鎖ホモトピー同値と合成 |
| `SchurComplexArity` | 114 | 有限全単射の余極限を arity ごとの余不変の複体の直和へ同定。余極限の生成元を指定商写像の後の直和包含へ送る |

四本計 **373 行**。§36 までの a の実測 **1,513 行**と合わせて **1,886 行**。
これは a の完成ではない。左右の入力数による arity の運び、テンソル余不変の全複体との比較、
二つの自由 Schur 代数のテンソル側の表示、実際の指定比較との照合と自然性が残る。
既存の公開宣言の定義や界面の型を変えていない。
セル対・bar の実現・sifted の保存には進んでいない。

### 39.2 ビルド・監査・改名との関係

変更した四本だけの対象ビルドを通した。最後の成功ログは
`/tmp/bsw16/graded/free-complex-two-02.log`（軌道直和）、
`free-complex-three-01.log`（標準入力）、`free-arity-07.log`（arity 分解）、
`induced-complex-10.log`（誘導入力）。新規四本には警告なし。
依存の `ZeroArity` の既存警告は再生される。

別の一回の鍵で四本に属する全宣言を監査し、**81 宣言・標準三公理のみ**。
ログは `/tmp/bsw16/graded/audit-free-complex-four.log`。本体に sorry・追加公理はない。
各ビルド・監査の終了を回収して鍵を返してから、次の一枚を要求する形を守った。

この四本は 10:21 より後の新規ファイルで、凍結した 31 本の採取範囲には含まれない。
道具の修正連絡を受けたら、同じ 31 本の rewrite をやり直すとともに、main を取り込む前に
この追加分も採取・確認し、取り込み後の対象ビルドに含める。31 本の既存索引へ未採取の内容を混ぜない。
入口・共通監査への登録は調整役の取り込み時とする。登録待ちの追加一覧は上表の四本。

a の上限は **約 3,000 行、緩めなし**。今後の補助も全て a の行数に含める。
この報告後、道具の修正連絡までは、今の枝で残りの自由比較を続ける。

## 40. a の全複体の比較と、残りの接続を含めた規模の再確認

§39 の後も、採取済み 31 本には触れず、新規ファイルだけで進めた。
今回の区切りは、以下の六本の下書きの検証・監査までとする。
その先の比較の新設は、下記の規模の理由で止める。

### 40.1 今回の範囲と残る区別

`CoinvariantTensorComplex` は、実際の複体のテンソルの対角作用を持つ余不変と、
表現の複体のテンソル余不変の直和全複体を同定する。双次数の指定包含、
左右の微分、Koszul の符号を照合する。
`SchurArityTotalComparison` はこれを実際の Schur 図式へ適用する。

`ProductCoinvariants` は、独立な二つの群作用について、直積群の余不変を左右の余不変の
テンソルへ分ける。両方向の射を商の普遍性から作り、元の生成元と両入力での自然性を固定する。
`ProductCoinvariantComplex` はこの自然性を二重複体へ持ち上げ、全複体との同型を使って
非有界な複体について同じ分離を行う。

`TwoColorOrbitArity` は、個数による標準代表と元の標準パターンの等式、その安定化群と
指定二色部分群の等式・同型、固定 arity と左入力数の組から左右の入力数への再添字を扱う。
`TwoColorOrbitTransport` は、その群同型で制限した実際の入力表現の複体を指定標準入力へ同定する。

**これらは、自由比較を完成したという主張ではない。**
群の同型があることと、その同型に沿って余不変・誘導表示・指定された比較射を移すことを区別する。
後者はまだ全部は作っていない。別の同型を選んで指定 Hopf 比較の照合を省いてはいない。

### 40.2 残りを接続ごとに数えた見込み

従来の §36.2 の三比較のうち、全複体の比較と直積群の分離の一般部分を今回作った。
ただし、それを実際の Schur 表示へ接続するには、次が残る。

| 未完了の接続 | 使えるもの | まだ要る照合 | 残りの見込み |
| --- | --- | --- | ---: |
| 固定 arity の軌道直和を二色の係数比較へ接続 | `binaryTensorOrbitComplexIso`、`binaryTensorCountIndexEquiv`、`twoColorOrbitStandardInputIso`、`twoColorInducedComplexSourceIso` | arity の再添字の後の誘導・制限・余不変の比較。群の等式・同型に沿った運びが、指定誘導包含と整合すること | 100〜140 |
| Schur の係数と入力の順序・係数作用の照合 | `schurArityTotalIsoSum`、`coinvariantTensorTotalIso`、既存の `mapBifunctorFlipIso` と braiding | `sequence A` の作用と `arityRepresentationCochain` の比較、および係数・入力の交換を、指定商写像を保つ複体の射として接続 | 80〜100 |
| 実際のテンソル側の二色表示 | `productCoinvariantsIso`・その自然性、`productCoinvariantComplexIso`、`twoColorGroupEquiv`、複体の associator・braiding | 二色部分群から左右の置換群の直積への群変更に沿う余不変の同型、四因子の交換、二つの Schur 直和のテンソルと二色直和の比較、各生成元の像 | 230〜330 |
| 指定 Hopf 自由比較との一致、自然性、弱同値 | 既存の `twoColorCoefficientCochainMap`、`twoColorComplexInputHomotopyEquiv`、`barrattEcclesCoproductTensorNat` | 生成元ごとの図式が交換し、分解した射が同じ指定係数射になること。直和を経た比較の弱同値と入力射への自然性 | 250〜350 |
| **計** | | | **660〜920** |

`Rep.coinvariantsTensorIndNatIso` は入力一つが表現である比較を供給するが、
上表の群変更・arity の再添字と指定包含の整合までは主張していない。
`ProductCoinvariants` は任意の直積群の独立な作用の比較であり、
実際の `TwoColorGroup` と二つの `ULift` された置換群の直積の比較は別に要る。
Mathlib の `RepresentationTheory/Coinvariants`・`Rep/Res` と本体の公開 API を調べた範囲では、
この最後の群変更を指定商写像ごと運ぶ同型は見つからなかった。
既存の associator と `mapBifunctorFlipIso` は再利用し、符号つき全複体の一般論は作り直さない。

今回の下書き六本は計 **462 行**、§39 の実測 **1,886 行**と合わせて **2,348 行**。
下書き時点での残りを含む a 全体は **3,008〜3,268 行**の見込みとなる。
現在の承認は **約 3,000 行、緩めなし**なので、新しい比較の実装はここで止める。
行数を別の一般補助や他の作業へ移して計上から外すことはしない。
今回の下書き六本の修正・検証・監査・コミットだけを区切りまで行い、その実測を次項に記録する。
セル対、bar の実現、sifted 保存へは進まない。KL-W1 の道具の修正を手で先取りもしない。

### 40.3 検証の区切り、最終実測、登録待ち一覧

下書き済みの六本だけを修正して、全て対象ビルドを通した。
表のパスは `SerrePositivity/EInfinity/BarrattEccles/Theory/` 以下。

| 登録待ちモジュール | 最終実測 | 最後の成功ログ（`/tmp/bsw16/graded/` 以下） |
| --- | ---: | --- |
| `CoinvariantTensorComplex` | 98 | `coinvariant-product-06.log` |
| `TwoColorOrbitArity` | 59 | `coinvariant-arity-04.log` |
| `ProductCoinvariants` | 120 | `product-coinvariants-07.log` |
| `SchurArityTotalComparison` | 60 | `free-total-three-09.log` |
| `ProductCoinvariantComplex` | 73 | `product-complex-11.log` |
| `TwoColorOrbitTransport` | 63 | `free-total-three-09.log` |
| **計** | **473** | |

直積群の複体版の微分との照合は、商とテンソルの指定生成元で両辺を直接計算して閉じた。
全六本に属する宣言を別の一回の鍵で監査し、**107 宣言・標準三公理のみ**。
監査ログは `audit-free-total-six.log`。新規六本に警告なし、sorry・追加公理なし。
§39 の四本と合わせ、今回追加の **十本・188 宣言**を監査済み。
既存の公開宣言・界面の型・共通入口・共通監査には変更していない。

下書きからの修正を含む最終実測は、今回 **473 行**、a 全体 **2,359 行**。
§40.2 の残り **660〜920 行**と合わせた最終見込みは **3,019〜3,279 行**。
§40.2 の下書き時点の数字から 11 行増えた分も含めている。
承認上限 **約 3,000 行、緩めなし**を超えそうなので、ここで a の実装を中間停止する。
自由比較や `coproduct_tensor` の証明を完了したとは報告しない。

停止後は上限内の新設を続けず、今回の通った六本と報告だけをコミットする。
今回の全ビルドと監査は、それぞれ終了を回収して鍵・整理券を返却済み。
常駐ビルドセッションや複数の整理券は使っていない。

### 40.4 KL-W1 の修正連絡後の再開

元の **31 本**は、全てのソースの SHA-256 が採取時と一致したまま。
§38 の保留 16 箇所は道具の修正連絡待ちで、rewrite の再実行・main の取り込み・
プレビューの反映・改名後の対象ビルドはまだ行っていない。
drafts の改名は調整役の担当とし、今回触れていない。

新規十本の追加一覧を `klw1-followup/bs-impl-extra-files.json` に用意した。
この一覧は採取完了の印ではない。追加十本の before_index は**未採取**。
連絡後は同じ 31 本で rewrite を再実行し、追加十本も取り込み前の枝で別途採取・確認してから、
main の取り込み、プレビューの反映、変更ファイルと直接 importer の対象ビルドへ進む。
元の索引へ未採取の新しいソースを混ぜない。入口と監査への登録は調整役が取り込み時に行う。
登録待ちの今回の追加分は、§39 の四本と §40.3 の六本である。

## 41. §14 からの再開：Schur 複体の同値を組み立て、指定射の照合で規模を再確認

調整役の §14（main の指示書を読み、ユーザーの指示でも確認）に従い、
a の上限を **約 3,300 行、緩めなし**として再開した。
KL-W1 の修正連絡待ちのまま今の枝でビルドしてよい、という指示に従い、
main は取り込まず、採取済み 31 本を保って、新規補助だけで進めた。

### 41.1 今回検証した範囲

以下は全て `SerrePositivity/EInfinity/BarrattEccles/Theory/` 以下。
入口・共通監査への登録待ちの追加一覧でもある。

| 新規モジュール | 実測 | 今回閉じたもの |
| --- | ---: | --- |
| `CoinvariantGroupChange` | 73 | 群同型に沿う余不変の同型。指定商の生成元、表現の射、複体の微分を保持 |
| `SchurCoefficientOrder` | 124 | 実際の `sequence` の作用と指定 arity の作用の同定、braiding による係数と入力の交換、全複体への指定商写像、双次数生成元と braiding での商の計算 |
| `InducedCoinvariantTotal` | 77 | 任意の安定化群での誘導入力と制限した係数の全複体の同型。入力方向の加法性と有限直和の保存 |
| `TwoColorTargetSchur` | 124 | 二色部分群と左右の置換群の直積の同定、四因子の符号つき交換、二色係数比較の標的と二つの実際の Schur arity 成分のテンソルの同型 |
| `TwoColorSourceSchur` | 81 | 実際の Schur arity から指定軌道直和への同型。各標準代表を指定二色係数比較へ接続した鎖ホモトピー同値 |
| `ComplexCoproductHomotopy` | 61 | 各成分の指定鎖ホモトピーを直和へ束ねること、指定直和写像の鎖ホモトピー同値。添字の宇宙は係数環から独立 |
| `FreeSchurComparison` | 69 | arity と色の個数の再添字、二つの Schur 直和のテンソルの二添字表示、指定係数射を全 arity へ束ねた鎖ホモトピー同値 |
| `FreeHopfComparison` | 89 | 左右の指定 Hopf 包含から自由代数の普遍性で定める厳密な比較、その左右の生成元と arity での式、零入力の照合に使う単位入力族の縮約 |
| **計** | **698** | |

`freeSchurCoefficientHomotopyEquiv X Y` は、
`Schur(X ⊞ Y)` と `Schur(X) ⊗ Schur(Y)` の鎖ホモトピー同値。
任意の複体 `X`・`Y` で述べており、cofibrant・有界・平坦という追加仮定を置いていない。
順射は、既存の指定二色係数射を、今回の指定同型と直和写像で束ねた射である。
任意に選んだ係数比較へ差し替えていない。

ただし、**この順射が `freeHopfComparison` の底の射、従って既存の厳密な余積比較から
得る射と一致するという定理は、まだ証明していない。a は未完了。**
この同値の存在だけから、`barrattEcclesCoproductTensorNat` の成分が弱同値だとは結論しない。

### 41.2 残る指定射の照合の正確な形

`r = m + n`、`C_s = (operad A).arity s`、`V = power X m ⊗ power Y n` と書く。
共通の始域 `C_r ⊗ V` から、次の二つの射を固定して比較する。

- `J`：`𝟙 C_r` と `binaryTensorStandardPowersIso X Y m n` の逆射、
  標準パターンの指定包含、元の `schurι` の合成。
- `M`：`twoColorCoefficientComparison A m n ▷ V`、
  `tensorμ C_m C_n (power X m) (power Y n)`、
  `schurι A (sequence A) X m ⊗ₘ schurι A (sequence A) Y n` の合成。

必要なのは、同じ `J` と `M` について、
`J ≫ (freeSchurCoefficientHomotopyEquiv X Y).hom = M` と
`J ≫ (freeHopfComparison (hopf A) h0 X Y).hom = M` を証明すること。
その後、標準代表の軌道が全ての語を覆うことと Schur の生成射の普遍性で全射の等式へ延ばす。
自由代数関手の余積比較を介して、元の厳密な指定比較の弱同値と関手的な形へ戻す。

前者には、今回の商の双次数での計算に加え、誘導表示の単位生成元と指定包含を前合成した図式の照合が残る。
後者には、零入力への代入の係数射 `nullaryPrefixDelete` と、代数の実際の零入力作用との照合が残る。
`Operad.Algebra.iteratedOperationTensor_action` は再利用できるが、それ自体がこの最後の図式ではない。
`FreeHopfComparison` の arity の式も、この零入力の計算を済ませたという主張ではない。

### 41.3 見積りとの差と、上限による中間停止

§40.2 の各行へ今回のファイルを一度ずつ割り当てると、以下となる。
これは **a 完了時の実測ではなく、未完了の中間比較**である。
`FreeSchurComparison` の全体の直和への組み立ては第四行に数えた。
指定包含・商を前合成する図式の残りは、最後の指定射の照合にまとめて数え、重複させない。

| §40.2 の行 | 旧残りの見込み | 今回の実測 | 旧見込みとの差 |
| --- | ---: | ---: | ---: |
| 固定 arity の軌道直和と二色係数の接続 | 100〜140 | 231（73 + 77 + 81） | +91〜+131 |
| 係数と入力の順序・係数作用 | 80〜100 | 124 | +24〜+44 |
| テンソル側の二色表示 | 230〜330 | 124 | −206〜−106 |
| 指定射の照合と全体の比較 | 250〜350 | 219（61 + 69 + 89）、なお未完 | −131〜−31、ただし残りあり |
| **計** | **660〜920** | **698** | **−222〜+38、ただし残りあり** |

最後の指定射の照合の残りを、次の三つに分けて見直した。

| 残り | 再利用と未証明の接続 | 見込み |
| --- | --- | ---: |
| 構成した同値の順射について `J ≫ hom = M` | 商の双次数計算・braiding の整合は今回証明済み。誘導の単位生成元、群変更、直和包含を前合成した同じ図式を照合する | 90〜130 |
| 厳密な Hopf 比較について `J ≫ hom = M` | 今回の arity の式と単位入力族の縮約、既存の `iteratedOperationTensor_action` を使う。零入力の単位射との比較、`nullaryPrefixDelete` の作用、左右のブロックへの適用が残る | 120〜170 |
| 全射・元の余積比較の弱同値・自然性 | 二つの生成元での式から全射の等式を得て、自由代数の余積比較と既存の指定自然変換へ戻す | 40〜60 |
| **計** | | **250〜360** |

§40.2 の見積りでは、同型を構成することと、指定射へ戻すためにその同型へ生成元を前合成する
図式の照合を、十分に分けて数えられていなかった。新しい数学的な経路を足したのではないが、
同じ指定射との一致を未証明のまま完了と数えることはできない。

今回までの実測は **2,359 + 698 = 3,057 行**。
残りを含む完成見込みは **3,307〜3,417 行**で、承認上限 **約 3,300 行、緩めなし**を超えそうである。
従って §14 の指示に従い、**ここで新しい Lean の追加を止めて中間停止する**。
上限を自分で広げず、残りを別のファイル・作業へ移して計上から外さない。
この停止は鍵の待ち時間や、模型の追加仮定が必要になったことによるものではない。
a が閉じていないので、その後の厳密な bar 前段の残り・c・組み立て関数には進んでいない。

### 41.4 検証・監査・改名の状態

新規八本の対象ビルドと直接の importer のビルドは成功。
主なログは `/tmp/bsw16/graded/` 以下の
`group-change-01.log`、`induced-total-02.log`、`quotient-swap-07.log`、
`free-quotient-06.log`、`free-unit-11.log`。
新規八本に警告なし。依存の `ZeroArity` の既存警告は再生される。

別の一回の鍵で八本に属する全宣言を監査し、**199 宣言・標準三公理のみ**。
ログは `audit-free-resume-eight.log`。sorry・追加公理はない。
`[ModelCategory SSet]` のような追加仮定も使っていない。
ビルド・監査の各終了を回収して鍵・整理券を返した。常駐セッションは使っていない。

採取済み 31 本は、今回も SHA-256 が採取時と完全一致することを確認した。
修正連絡待ちの 16 箇所は変更せず、main の取り込み・rewrite の再実行・反映はまだ行っていない。
drafts、共通入口、共通監査、既存の公開宣言には変更していない。
追加採取用の `klw1-followup/bs-impl-extra-files.json` は、§39〜40 の十本に今回の八本を加えた **18 本**に更新する。
これは採取完了の印ではなく、追加十八本の before_index は未採取のままである。
修正連絡後の改名追従は §40.4 の手順で行う。


## 42. KL-W1 の改名追従（修正版 8267bf808、11-12）

### 42.1 採取と差分

修正版の共有道具 `SerrePositivity-kerodon-layout/scripts/refactor/klw1_namespace.py`
（`8267bf808`）を使用した。古い部分採取は使わず、
`/tmp/bsw16/klw1-followup-49-8267/before-index/` へ collect から実行し直した。
対象は従来の本体 31 本と、10:21 以後に検証・コミットした §39〜41 の 18 本を合わせた **49 本**。
drafts と未検証の下書きは含めない。採取終了時に元ソースの SHA-256 が変わっていないことも確認した。

新しい index に対する rewrite は成功し、`review.json` は `{}`（**保留 0**）。
プレビュー全体の差分を確認した。書き換えは次の **17 本、339 行置換（+339 / -339）**。
このうち import の変更は 10 本・29 行で、それ以外は名前空間・宣言参照・scope の明示である。
ファイル自体の移動、宣言の意味の変更はない。

| ファイル | 置換行数 |
| --- | ---: |
| `SerrePositivity/EInfinity/BarrattEccles/Theory/AnodyneBinaryProducts.lean` | 4 |
| `SerrePositivity/EInfinity/BarrattEccles/Theory/CoproductDKHom.lean` | 8 |
| `SerrePositivity/EInfinity/BarrattEccles/Theory/CoproductFrameHom.lean` | 12 |
| `SerrePositivity/EInfinity/BarrattEccles/Theory/CoproductFrames.lean` | 5 |
| `SerrePositivity/EInfinity/BarrattEccles/Theory/CoproductMappingSpace.lean` | 20 |
| `SerrePositivity/EInfinity/BarrattEccles/Theory/CoproductNativeUniversal.lean` | 20 |
| `SerrePositivity/EInfinity/BarrattEccles/Theory/EnrichedPointPrecomposition.lean` | 13 |
| `SerrePositivity/EInfinity/BarrattEccles/Theory/NativeCoproduct.lean` | 31 |
| `SerrePositivity/EInfinity/BarrattEccles/Theory/NativeCoproductCocone.lean` | 15 |
| `SerrePositivity/EInfinity/BarrattEccles/Theory/NativeCoproductLegs.lean` | 27 |
| `SerrePositivity/EInfinity/Interface/CoproductTensorLegs.lean` | 6 |
| `SerrePositivity/EInfinity/Interface/TensorLegs.lean` | 41 |
| `SerrePositivity/EInfinity/Interface/TensorUnitClasses.lean` | 9 |
| `SerrePositivity/EInfinity/Interface/Theory.lean` | 56 |
| `SerrePositivity/EInfinity/NativeBinaryCoconeHom.lean` | 10 |
| `SerrePositivity/EInfinity/StrictAdjunctionBar.lean` | 31 |
| `SerrePositivity/InfinityCategories/Kerodon/LimitsAndColimits/LimitsAndColimits/BinaryCoconeApexTransport.lean` | 31 |

`klw1-followup/bs-impl-files.json` を 49 本の正本に更新し、`review.json`・
`preview-stats.json` を今回の結果で置き換えた。出所は `followup-provenance.json` に記録した。
追加分の `bs-impl-extra-files.json` は、この 49 本に含まれる 18 本の内訳として残す。

### 42.2 main の取り込み

`main` の `ef145b288`（指定の `23f47736c` 以降）を `math/bs-impl` に取り込み、
確認済みプレビューを反映した（ビルド失敗のため merge commit は未作成）。競合は `Interface/Theory.lean` の一か所だけ。
main とプレビューを照合し、main の改名を保ちつつ D78 の承認済み import と
`coproduct_tensor_legs` の欄を残す形で解決した。`open scoped _root_.Simplicial` は
道具の生成した scope の明示である。drafts の改名は手動で行わず、調整役の main から取り込んだ。

### 42.3 検証

対象 49 本と、書き換えたモジュールの本体内の直接の importer（重複を除く追加 6 本）を合わせた
**55 対象**をビルドした。共通入口・監査の登録は編集しない。
対象・importer の全一覧とログは今回の `/tmp/bsw16/klw1-followup-49-8267/` に保存する。


**結果：失敗（終了コード 1）。追従完了とはしない。**
`review.json` の保留が 0 でも、生成された `open` が実際の main の import 環境で
解決されない例が残っている。失敗として列挙された対象は次の三本。

| ファイル・行 | 最初のエラー |
| --- | --- |
| `BarrattEccles/Theory/AnodyneBinaryProducts.lean:22` | `open _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison` の unknown namespace |
| `StrictAdjunctionBar.lean:25` | `open _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom` の unknown namespace（続いて `ComonadResolutionOperators`・`power` などが未解決） |
| `BarrattEccles/Theory/EnrichedPointPrecomposition.lean:21` | 同じ `HA.ModelCategoryComparison` の unknown namespace（続いて `localizationHom`・`kanLocalizationUnit` などが未解決） |

詳細は `klw1-followup/build-failure.json`、全ログは
`/tmp/bsw16/klw1-followup-49-8267/build.log`。
道具が生成した open の対応を推測で変更せず、KL-W1 の確認を待つ。
ビルドの終了を回収し、鍵と整理券を返した。ビルド失敗のため公理監査は行わない。
49 本のソース中に `sorry`・`axiom` がないことは別途確認した。

検証が通るまで Lean はコミットしない規則に従い、今回の追従コミットは **なし**。
main の取り込みは競合解決済み・merge commit 前の状態で、生成ソースとこの報告を作業木に保持する。
採取前の元ソース、採取 index、プレビュー、差分は今回の新しい `/tmp/` ディレクトリに保存済み。
§41 の自由比較の残りや、新しい証明には手を付けていない。


## 43. §42 の後の検証と a の作業木の分離（11-12 夜）

調整役の連絡の前に、失敗した三本の使用宣言の定義元を確認した。
`AnodyneBinaryProducts` と `EnrichedPointPrecomposition` の open は、実際に import される
移動対象外の宣言に必要な `SerrePositivity.SimplicialModel` へ戻した。
`StrictAdjunctionBar` は同じ理由で `SerrePositivity.HomotopyFunctionComplex` へ戻した。
また `EnrichedPointPrecomposition` では、参照が既に完全修飾された後の不要な
`SerrePositivity.KST.Comparison` の open を除いた。
この状態の 55 対象のビルドは **成功（13,550 jobs、終了コード 0）**。
ログは `/tmp/bsw16/klw1-followup-49-8267/build-open-fix-2.log`。
採取前との実際の差分は 17 本・337 行置換。公理監査・コミットはまだ行っていない。

その後の調整役の指示に従い、この手修正も含めて **未コミットの merge をそのまま保持**する。
採取器の修正連絡を待ち、そのとき rewrite からやり直す。今回の成功で改名追従の完了とはしない。
共通入口・監査の登録も変更しない。鍵・整理券は返却済み。

**a には別の作業木を選んだ。** merge 前の `5fe517e63` から
`../SerrePositivity-bs-impl-a`、枝 `math/bs-impl-a` を作る。
元の `math/bs-impl` の merge は stash・abort・commit せず保持する。
a の実装と対象ビルドは新しい作業木で行い、上限は §15 の **3,500 行、最後の上げ**を守る。
完了時には §20.2・§40.2 の各行の見込みと実測を報告する。


## 44. 別作業木で a の厳密な余積比較への復帰を証明（11-12）

§43 の別作業木 `SerrePositivity-bs-impl-a`（枝 `math/bs-impl-a`、基点 `5fe517e63`）で作業した。
`math/bs-impl` の未コミットの merge は保持し、こちらでは main を取り込んでいない。

### 44.1 証明した範囲

新規 `SerrePositivity/EInfinity/BarrattEccles/Theory/FreeHopfCoproduct.lean`（**92 行**）。
登録すべき新規モジュールは `SerrePositivity.EInfinity.BarrattEccles.Theory.FreeHopfCoproduct`。

- `freeSumCoproductIso`：自由・忘却随伴と標準の余積比較により、
  `Free X ⨿ Free Y ≅ Free (X ⊞ Y)` を構成する。
- `freeSumCoproductIso_inl`・`inr`：この同型は二つの指定包含を自由関手で送った包含へ送る。
- `freeSumCoproductIso_hopfComparison`：この同型の後の `freeHopfComparison` は、
  元の厳密な `hopfCoproductComparison` と同じ代数射である。生成元での左右の式から証明した。
- `hopfCoproductComparison_quasiIso_of_free`：自由生成元での指定 Hopf 射が擬同型なら、
  厳密な余積の同じ比較も擬同型になる。

一般の Hopf オペラッドについて述べ、必要な仮定は零 arity の余単位の同型性と、
代数の二項余積の存在だけ。入力複体に cofibrancy・K 平坦性・有界性を仮定しない。
最後の補題の擬同型性の仮定は明示的な仮定であり、BE の係数比較との一致を証明したという意味ではない。

### 44.2 実測と残り

今回の 92 行は §40.2・§41.3 の「指定射の照合と全体の比較」の行に計上する。
a の実測は **3,057 + 92 = 3,149 行**。最後の上限 **3,500 行**まで 351 行。
今回は元の余積比較へ戻す接続を閉じたが、
§41.2 の `J ≫ freeSchurCoefficientHomotopyEquiv.hom = M` と
`J ≫ freeHopfComparison.hom = M`、そこから全射の一致を得る部分は残る。
**a は未完了**であり、§20.2・§40.2 の完了時比較としては報告しない。

### 44.3 検証

新規一対象のビルドは成功（`free-hopf-coproduct-a-08.log`、10,502 jobs）。
ジョブ数には依存の共有キャッシュ復元を含み、root ビルドは行っていない。
新規モジュールに警告なし。未登録なので本体内の直接の importer はまだない。
ログと一モジュールの全宣言の監査は `/tmp/bsw16/` 以下。

ビルド終了の回収後、別の一回の鍵で新規一モジュールの全宣言を監査した。
**15 宣言・標準三公理のみ**（`audit-free-hopf-coproduct-a.log`）。
sorry・追加公理はない。ビルドと監査の各終了を回収し、鍵・整理券を返した。
未コミットの merge のある元の作業木へは、この新しい Lean をまだ移していない。
次回の改名追従の対象には、検証済みの追加分として今回の一モジュールも含める。


## 45. KL-W1 d07e86e14 による追従の完了と一時枝の合流（11-12）

### 45.1 修正版の rewrite

保持していた merge を捨てず、調整役の許可どおり採取済みの 49 本の `before_index` を再利用した。
書き換えの入力は採取時に保存した同じ元ソースとし、現在の書き換え済みソースの文字位置は使わない。
共有道具 `SerrePositivity-kerodon-layout` の **`d07e86e14`** とその改名表で rewrite からやり直した。
出力は `/tmp/bsw16/klw1-followup-d07-preview/`。

`review.json` は **保留 0**。元の混在した名前空間の open を保ち、移動した宣言だけを完全修飾する。
旧プレビューとの差分を確認し、§43 の三本の手修正も含めて新しい道具の結果へ置き換えた。
採取時のソースと最終出力の差分は **15 本・284 行置換（+284 / -284）**。
次が各ファイルの実測であり、詳細の正本は `klw1-followup/preview-stats.json`。

| ファイル | 置換行数 |
| --- | ---: |
| `SerrePositivity/EInfinity/BarrattEccles/Theory/CoproductDKHom.lean` | 4 |
| `SerrePositivity/EInfinity/BarrattEccles/Theory/CoproductFrameHom.lean` | 11 |
| `SerrePositivity/EInfinity/BarrattEccles/Theory/CoproductFrames.lean` | 4 |
| `SerrePositivity/EInfinity/BarrattEccles/Theory/CoproductMappingSpace.lean` | 11 |
| `SerrePositivity/EInfinity/BarrattEccles/Theory/CoproductNativeUniversal.lean` | 17 |
| `SerrePositivity/EInfinity/BarrattEccles/Theory/EnrichedPointPrecomposition.lean` | 11 |
| `SerrePositivity/EInfinity/BarrattEccles/Theory/NativeCoproduct.lean` | 31 |
| `SerrePositivity/EInfinity/BarrattEccles/Theory/NativeCoproductCocone.lean` | 15 |
| `SerrePositivity/EInfinity/BarrattEccles/Theory/NativeCoproductLegs.lean` | 27 |
| `SerrePositivity/EInfinity/Interface/CoproductTensorLegs.lean` | 6 |
| `SerrePositivity/EInfinity/Interface/TensorLegs.lean` | 41 |
| `SerrePositivity/EInfinity/Interface/TensorUnitClasses.lean` | 9 |
| `SerrePositivity/EInfinity/Interface/Theory.lean` | 56 |
| `SerrePositivity/EInfinity/NativeBinaryCoconeHom.lean` | 10 |
| `SerrePositivity/InfinityCategories/Kerodon/LimitsAndColimits/LimitsAndColimits/BinaryCoconeApexTransport.lean` | 31 |

§42〜43 のビルド失敗・手修正・未コミットという記録は、その時点の履歴である。
今回の結果は `followup-provenance.json` と本節に記録する。
`StrictAdjunctionBar` と `AnodyneBinaryProducts` は元ソースと同じになり、最終的な変更 15 本に含めない。
drafts は新たに書き換えていない。main にある調整役の追従だけを取り込んだ。

### 45.2 取り込みと検証

保持中の `ef145b288` の merge と修正版の追従を **`aed89b498`** に確定した。
その後、指定された **main `e61b3f534`** を取り込み、**`e8e607ce6`** に確定した。
修正版の本体 49 本と、変更したモジュールの本体内の直接の importer を合わせた **55 対象**のビルドは、
修正版反映後・最新 main 取り込み後の両方で成功（各 13,550 jobs）。
49 モジュールに属する全宣言の監査も **948 宣言・標準三公理のみ**。
ログは今回の出力先の `build.log`・`build-main.log`・`audit.log`。

続いて `math/bs-impl-a` の **`3f26491d1`** を合流させた。
本体の競合はなく、報告ファイル末尾の競合は §44 の追記を保持して解決した。
`FreeHopfCoproduct` は改名対象の import・宣言参照を持たず、ソースを変更せずに取り込んだ。
合流後の **56 対象**のビルドも成功（13,551 jobs、`build56.log`）。
ルートの `SerrePositivity` はビルドしていない。
改名に伴う長い行と既存の重複名前空間の linter 警告は残る。

### 45.3 登録待ちと a の残り

`bs-impl-files.json` は、今回追従した 49 本に `FreeHopfCoproduct` を加えた **50 本**へ更新した。
main `e61b3f534` に既にあるのは `Interface/Theory` の一本だけで、**新規登録待ちは 49 モジュール**。
その全一覧を `klw1-followup/registration-modules.json` に保存した。
共通入口・共通監査の登録は調整役に委ね、こちらでは変更していない。

a の実測は §44 の **3,149 行**のまま。今回の改名や枝の合流で証明が増えたとは数えない。
残りは §41.2 の指定係数射との一致であり、a はまだ未完了。
合流後は本来の `math/bs-impl` と `SerrePositivity-bs-impl` で再開する。

合流後の 50 モジュールの全宣言の監査も **963 宣言・標準三公理のみ**で成功（`audit50.log`）。
sorry・追加公理はなく、監査終了を回収して鍵と整理券を返した。
一時作業木は合流コミット後に `git worktree remove` で削除した。


## 46. 合流後の a：単位射の零入力照合と、最後の上限での中間停止

§45 の合流後、`math/bs-impl` で作業を再開した。
一時作業木 `SerrePositivity-bs-impl-a` は合流後に削除済み。
新しい本体は `SerrePositivity/EInfinity/BarrattEccles/Theory/HopfNullaryUnitMap.lean`（**81 行**）。

### 46.1 今回閉じたもの

- `hopfTensorUnitArrow_nullary`：単位代数からの任意の代数射は、実際の零入力作用と可換。
- `hopfTensorUnitMap_hom_nullary`：始対象性から選ばれた指定単位射の底の射は、
  零入力の余単位の逆、右単位子の逆、代数の零入力作用の合成と等しい。
- `hopf_counit_zero_eq_nullaryCoefficientIso`：BE の Hopf 余単位は、
  `nullaryPrefixDelete` に使う指定零入力係数同型の同じ順射。
- `barrattEcclesTensorUnitMap_nullary`：従って BE の指定単位射を、
  `nullaryCoefficientIso` の逆と同じ代数の零入力作用で計算できる。

一般の Hopf オペラッドの部分は代数射の arity 0 の保存則から証明した。
BE の部分も既存の増大を使い、始対象性による選択を別の射へ差し替えていない。
cofibrancy・平坦性・有界性などの入力の追加仮定はない。
ただし、この一射の式から、任意個の入力を消去する `nullaryPrefixDelete` の作用の式や
二色の指定 Hopf 比較との一致が自動的に閉じるとは扱わない。

### 46.2 実測と残り

今回の 81 行も、§40.2 の「指定射の照合と全体の比較」に計上する。
§41.3 の中間比較を更新すると次のとおり（**未完了の比較**）。

| §40.2 の行 | §40.2 での残りの見込み | §41・44・46 の実測 | 差 |
| --- | ---: | ---: | ---: |
| 固定 arity の軌道直和と二色係数の接続 | 100〜140 | 231 | +91〜+131 |
| 係数と入力の順序・係数作用 | 80〜100 | 124 | +24〜+44 |
| テンソル側の二色表示 | 230〜330 | 124 | −206〜−106 |
| 指定射の照合と全体の比較 | 250〜350 | 392（219 + 92 + 81）、なお未完 | +42〜+142、なお残りあり |
| **計** | **660〜920** | **871** | **−49〜+211、なお残りあり** |

今回までの a の実測は **2,359 + 871 = 3,230 行**。
上限 3,500 行まで **270 行**である。
残りの同じ指定射への照合を、今回閉じた補題で実際に置き換えた後の単位で見直すと、以下となる。

| 残り | まだ証明していない接続 | 見込み |
| --- | --- | ---: |
| `J ≫ freeSchurCoefficientHomotopyEquiv.hom = M` | 誘導表示の単位生成元・群変更・全複体の商・直和包含を前合成した図式 | 90〜130 |
| `J ≫ freeHopfComparison.hom = M` | 今回の一つの単位射の式を有限入力族へ移し、`nullaryPrefixDelete` の作用と Hopf 対角の左右への代入を同じ標準語で照合 | 110〜160 |
| 全射の一致と指定自然変換への復帰 | 標準語を前合成する族が Schur の全射を検出することを示して二つの式を束ねる。厳密な余積への復帰と擬同型性の移送自体は §44 で済み | 50〜70 |
| **計** | | **250〜360** |

完成見込みは **3,480〜3,590 行**となり、最後の承認上限 **3,500 行**を超えそうである。
従って指示書 §15 の停止条件に従い、**ここで a の新しい実装を止める**。
今回も `freeSchurCoefficientHomotopyEquiv` の存在から指定 Hopf 射の擬同型性を結論しない。
**a は未完了。** 完了時に求められた §20.2・§40.2 の最終実測としては報告しない。

§41 の見込みでは、生成元での射を厳密な余積へ戻す接続と、実際の標準語を前合成した族で
全射の一致を検出する接続が十分に分かれていなかった。前者は §44 の 92 行で閉じたが、後者は残る。
零入力についても、始対象性で選ばれた一射の式と、有限族の反復代入の式を区別する必要があった。
閉じていない図式を補題の引数や弱い主張へ移して a の完了とはしていない。

### 46.3 検証と登録待ち

新規一対象のビルドは成功（`/tmp/bsw16/hopf-nullary-unit-05.log`）。
別の一回の鍵で全 **4 宣言・標準三公理のみ**を監査した
（`/tmp/bsw16/audit-hopf-nullary-unit.log`）。sorry・追加公理はない。
監査後は長い一行の改行だけを行い、最終ソースを `hopf-nullary-unit-06.log` の対象ビルドで確認した（成功、新規警告なし）。
本体内の直接の importer はまだない。

登録待ちに `SerrePositivity.EInfinity.BarrattEccles.Theory.HopfNullaryUnitMap` を追加する。
登録一覧はこれで新規 **50 モジュール**、追従対象と合流分を含む本体の一覧は **51 本**。
共通入口と共通監査は変更していない。

ビルド・監査は各一回ごとに鍵を取り、終了を回収して返した。未コミットの Lean は残さない。


## 47. §16 からの再開：零入力の反復代入の図式を証明、規模による中間停止

main `7ed68f3a5` を取り込んだ（merge `6781298c6`）。指示書 §16 を読み、
a の上限を **約 3,600 行**として再開した。
main に登録された §22 以降の本体・界面・組み立て関数の型は変更していない。

### 47.1 今回閉じたものと、まだ閉じていないもの

新規二モジュールは、いずれも `SerrePositivity/EInfinity/BarrattEccles/Theory/` 以下。

| モジュール | 実測 | 閉じたもの |
| --- | ---: | --- |
| `NullaryEvaluation` | 131 | 零乗だけの有限族の連結と指定単位族の縮約の一致。単位入力の分離公式の逆向き。指定零入力係数を入れた反復合成が `nullaryPrefixDelete` を入力冪とテンソルした同じ射になること |
| `FreeStandardCoefficients` | 53 | 共通の始域からの指定射 `J`・`M` の定義。厳密な自由 Hopf 射に `J` を前合成した、元の arity の作用による式 |
| **計** | **184** | |

`nullarySourceInsert_operation` は任意の複体 `K` と入力数 `m`・`n` で述べた、
実際の複体の射の等式。`m = 0`・`n = 0` を含み、微分を変えず、
cofibrancy・平坦性・有界性の仮定を置かない。
零入力族の縮約の後、係数の和次数と入力冪の和次数の両方の同一視を保持した。

ただし、この射の等式を代数の作用へ適用し、左右の自由生成元と指定単位射からなる
標準二色語へ移す照合はまだ残る。
`freeStandardSource_hopfComparison_arity` も、元の `freeHopfComparison_arity` を
同じ標準語に前合成した式であり、**`freeStandardTarget`（`M`）との一致ではない**。
次の二式はいずれも未証明である。

- `J ≫ freeSchurCoefficientHomotopyEquiv.hom = M`
- `J ≫ freeHopfComparison.hom = M`

構成した鎖ホモトピー同値の存在だけから、指定自然変換の成分が擬同型だとは結論していない。

### 47.2 見込みと実測の中間比較

今回の 184 行は、§40.2 の「指定射の照合と全体の比較」の行に一度ずつ計上する。
これは完了時の比較ではなく、未完了の中間実測である。

| §40.2 の行 | §40.2 の残りの見込み | §41・44・46・47 の実測 | 差 |
| --- | ---: | ---: | ---: |
| 固定 arity の軌道直和と二色係数の接続 | 100〜140 | 231 | +91〜+131 |
| 係数と入力の順序・係数作用 | 80〜100 | 124 | +24〜+44 |
| テンソル側の二色表示 | 230〜330 | 124 | −206〜−106 |
| 指定射の照合と全体の比較 | 250〜350 | 576（392 + 184）、なお未完 | +226〜+326、なお残りあり |
| **計** | **660〜920** | **1,055** | **+135〜+395、なお残りあり** |

現在の a の実測は **2,359 + 1,055 = 3,414 行**。上限まで **186 行**である。
今回の有限零入力の射の図式を再利用し、未証明の接続だけを分けると、残りは以下となる。

| 残り | 要る照合 | 見込み |
| --- | --- | ---: |
| 構成した同値の順射について `J ≫ hom = M` | 誘導表示の単位生成元・群変更・全複体の商・直和包含を前合成した図式。今回 `J`・`M` を型として固定したが、この可換性はまだ証明していない | 90〜130 |
| 厳密な Hopf 射について `J ≫ hom = M` | 今回の反復合成の等式を代数の作用へ移す。左右の生成元・指定単位射からなる標準二色語を分離し、左ブロックの交換も含め Hopf 対角の両因子を指定係数射へ照合 | 80〜120 |
| 全射の一致と指定自然変換への復帰 | 標準語を前合成する族が全 Schur 射を検出することを示し、二つの図式を束ねる。厳密な余積比較への復帰自体は §44 で証明済み | 50〜70 |
| **計** | | **220〜320** |

完成見込みは **3,634〜3,734 行**で、承認上限 **3,600 行**を超えそうである。
従って **§16 の停止条件に従い、ここで新しい実装を止める**。
今回の見積りでも、有限零入力の係数の反復合成、代数の作用、標準二色語のテンソル分離を
一つの短い照合として見ていた点が不十分だった。131 行で閉じたのは最初の図式までで、
残る二つを閉じた扱いにはできない。共通射の定義と arity の式の 53 行も、二つの可換図式の証明を含まない。

**a は未完了。** §20.2・§40.2 の「完了時の実測」としては報告せず、
経路 B の厳密な前段の残り・④ の準備へはまだ進まない。

### 47.3 検証と登録待ち

新規二対象の最終ビルドは成功（10,506 jobs）。新規モジュールに警告なし。
ログは `/tmp/bsw16/nullary-standard-final.log`。ルートのビルドは行っていない。
本体内の直接の importer はまだない。

終了を回収した後、別の一回の鍵で二モジュールに属する全宣言を監査した。
**37 宣言・標準三公理のみ**（`/tmp/bsw16/audit-nullary-standard.log`）。
sorry・追加公理はない。ビルド・監査の各終了を回収し、鍵と整理券を返した。
登録待ちは次の二モジュール（以前の一覧の 50 モジュールは main の登録を確認済み）。

- `SerrePositivity.EInfinity.BarrattEccles.Theory.NullaryEvaluation`
- `SerrePositivity.EInfinity.BarrattEccles.Theory.FreeStandardCoefficients`

`klw1-followup/registration-modules.json` を、この現在の登録待ち二本の一覧へ更新した。
`bs-impl-files.json` は本体 **53 本**、追加分の内訳は **22 本**。
共通入口と共通監査は編集していない。


## 48. §17・新しい規模規則からの再開：標準語の検出と指定商の照合、規模による中間停止

main `f5baa8763` を merge `210b8a4e7` で取り込んだ。
指示書 §17 と末尾の規模規則を読み、a の上限は **3,800 行のまま**と確認した。
既存の公開宣言の型、界面の欄、共通入口、共通監査は変更していない。
ほかのレーンと対象ファイルの重複はない。

### 48.1 今回の増分

以下は `SerrePositivity/EInfinity/BarrattEccles/Theory/` 以下。

| モジュール | 今回の増分 | 内容 |
| --- | ---: | --- |
| `NullaryEvaluation` | 46（131 → 177） | `nullaryUnitPower`、`nullaryPrefixDelete_action`、`nullaryUnitPower_eq`。係数の零入力消去を実際の任意の代数の作用へ移し、その単位入力の有限族を指定 Hopf 単位射と照合 |
| `FreeStandardExt` | 60 | `freeStandardSource_hom_ext`。標準二色語上の一致から任意の Schur 射の一致を検出。任意の語を標準語の置換軌道に移し、Schur 商の対角関係で係数の置換も消去 |
| `FreeCoefficientCompatibility` | 104 | `schurTensorArityIso_generators` と `schurArityInputCoefficientIso_quotient`。テンソル側の二つの元の生成射と直和包含の一致、および元の arity の商と入力優先の全複体の指定商との一致 |
| **計** | **210** | |

零入力作用の補題、標準語の検出、指定商の照合は、いずれも任意の複体・入力数を扱う。
cofibrancy、平坦性、有界性を追加していない。零入力の係数と入力の双方の次数の運搬を保った。

ただし、次の二式は **どちらも未証明**である。

- `J ≫ freeSchurCoefficientHomotopyEquiv.hom = M`
- `J ≫ freeHopfComparison.hom = M`

今回の商の式は、第一式の最初と最後の表示変更を照合したもので、
誘導表示の単位生成元・群変更・係数比較を通した図式全体の証明ではない。
`freeStandardSource_hom_ext` は二式が証明できた後の全射の一致を与えるが、二式を供給しない。
鎖ホモトピー同値の存在だけから指定 Hopf 比較の擬同型性を結論していない。

### 48.2 実測と残りの見込み

今回の増分を §40.2 の最後の行へ一度ずつ計上する。

| §40.2 の行 | 当時の残りの見込み | 今回までの実測 | 差 |
| --- | ---: | ---: | ---: |
| 固定 arity の軌道直和と二色係数の接続 | 100〜140 | 231 | +91〜+131 |
| 係数と入力の順序・係数作用 | 80〜100 | 124 | +24〜+44 |
| テンソル側の二色表示 | 230〜330 | 124 | −206〜−106 |
| 指定射の照合と全体の比較 | 250〜350 | 786（576 + 210）、未完 | +436〜+536、残りあり |
| **計** | **660〜920** | **1,265** | **+345〜+605、残りあり** |

現在の a は **2,359 + 1,265 = 3,624 行**（docstring・空行を含む）。
残りは、公開 API と指定射の始域・終域を照合した次の内訳で見積もる。
既存 API の本体の行数や、今回証明した箇所は重複して数えない。

| 残る図式 | 再利用と不足 | 残りの見込み |
| --- | --- | ---: |
| 構成した同値の側：標準語から誘導表示・軌道直和へ | 今回の arity 商の式を使う。`binaryTensorOrbitComplexIso_ι` と誘導の単位生成元を、`inducedCoinvariantTotalIso`、標準部分群の変更、全複体の指定商まで移す照合が残る | 95〜140 |
| 構成した同値の側：係数射からテンソル側の指定商へ | 今回のテンソル側生成射の式を使う。`twoColorComplexInputHomotopyEquiv_hom`、四因子の交換、群変更、直積余不変の比較が元の生成元を同じ射へ送ることが残る | 45〜70 |
| 厳密な Hopf 射の側：標準語上の一致 | 今回の代数の零入力作用を使う。標準語に作用させたテンソル冪を左右へ分離し、左ブロック交換・右の零入力消去を指定二色係数と照合する部分が残る | 95〜135 |
| 全射の一致と指定余積比較の擬同型へ | 今回の `freeStandardSource_hom_ext` と既存の `hopfCoproductComparison_quasiIso_of_free` を使う。二図式から順射の一致を得て、指定鎖ホモトピー同値の擬同型性を移す | 15〜25 |
| **計** | | **250〜370** |

完成見込みは **3,874〜3,994 行**で、上限 **3,800 行**を超えそうである。
従って指示書 §17 と新しい規模規則に従い、下書き済みの分の検証・監査・コミットを終えて止める。
**a は未完了**であり、経路 B の厳密な前段の残りや④の準備にはまだ進まない。
§20.2・§40.2 の完了時の比較表は、未証明の二図式が閉じた時点に残す。

§47 の見積りでは、構成した同値の同型の鎖と、元の指定商の生成元を保つ図式の証明を
90〜130 行へまとめていた。しかし、今回の arity 商・テンソル側生成射の照合だけで 104 行を要し、
誘導表示と群変更を通す図式は残っている。零入力の反復合成を代数の作用へ移す 46 行も、
標準語の分離・ブロック交換自体を含まない。この二つを一つの短い書き換えとして扱った見積りが小さかった。
行数を別段や一般補助へ移して計上から外してはいない。

### 48.3 検証と登録待ち

三対象の最終ビルドは成功（10,508 jobs、`/tmp/bsw16/free-coefficient-08.log`）。
今回の三本に新規警告はない。既存の `ZeroArity` の警告の再表示のみ。
ルートビルドは行っていない。今回変更・追加した三本の本体内の直接の importer はまだない。

ビルドの終了と鍵の返却を回収した後、別の一回の鍵で四モジュールの所有宣言を監査した。
**54 宣言・標準三公理のみ**（`/tmp/bsw16/audit48.log`、終了コード 0）。
sorry・追加公理はない。監査も終了を回収し、鍵と整理券を返した。

登録待ちは以下の四本。最初の二本は §47 からの登録待ちで、後の二本が今回の新設。

- `SerrePositivity.EInfinity.BarrattEccles.Theory.NullaryEvaluation`
- `SerrePositivity.EInfinity.BarrattEccles.Theory.FreeStandardCoefficients`
- `SerrePositivity.EInfinity.BarrattEccles.Theory.FreeStandardExt`
- `SerrePositivity.EInfinity.BarrattEccles.Theory.FreeCoefficientCompatibility`

`klw1-followup/registration-modules.json` に四本を記録した。
本体の一覧は 55 本、追加分の一覧は 24 本。
共通入口と共通監査への登録は調整役に残す。未検証の Lean は作業木に残さない。


## 49. §18 の取り込みとホモトピー圏による照合の確認（途中記録）

main `28a87a2ed` を取り込み、§18 を読んだ。a の上限は 4,000 行。
本体の実測は 3,624 行のままで、§48 の残り 250〜370 行の見込みはまだ更新していない。
この記録は完了報告でも、規模条件による停止報告でもない。

ホモトピー圏での一致に弱めてよい接続は次のとおり。

1. 指定自由 Hopf 射 `f` と `freeSchurCoefficientHomotopyEquiv.hom` の間に、
   **全複体上の** `Homotopy f e.hom` があれば、`Homotopy.homologyMap_eq` と
   `HomotopyEquiv.quasiIso_hom` により `QuasiIso f` が従う。
   そこから `hopfCoproductComparison_quasiIso_of_free` に接続できる。
   擬同型性を得るために厳密な射の等式まで要求する必要はない。
2. この方法では、元の指定自然変換を保持してその各成分の擬同型性を証明する。
   対象ごとのホモトピー同値を選んだだけで FunctorIso を構成したとはしない。
   脚の条件は既存の指定比較の脚を使い、ホモトピー圏の等式へ移せばよい。
3. 一方、各 `J` を前合成した後のホモトピーから、全射のホモトピーが
   自動的に従うとはいえない。`freeStandardSource_hom_ext` は元の圏での等式の検出であり、
   商関手がそこで用いる余極限を保つことはこの補題からは出ない。
   ホモトピーを使うなら、係数の段で等変なホモトピーを作り、
   `twoColorComplexInputHomotopyEquiv` と同様に入力・余不変・全複体へ運び、
   軌道直和でまとめる経路が必要になる。
4. `inducedCoinvariantTotalIso` は比較同型を供給するが、指定誘導包含からその同型へ
   入る図式の照合を省く理由にはならない。ホモトピーに弱めても、その接続または
   それを置き換える等変ホモトピーの構成が残る。

従って現時点では、ホモトピー圏での一致が十分であることと、残る照合が既に証明できたことを
区別する。二つの指定射の照合は引き続き未証明。今回 Lean の変更・ビルド・監査は行っていない。
§20.2・§40.2 の完了時の実測比較は未提出である。


## 50. 元の圏での一致への復帰と、指定商の接続（実装途中）

ユーザーの指示に従い、ホモトピー圏への弱化は採用せず、元の複体の圏での厳密な一致を実装する。
`FreeCoefficientCompatibility` に `schurArityInputCoinvariantIso_quotient` を追加した。
元の arity の商を `schurArityInputCoinvariantIso` で移した射が、braiding の後の
同じ対角作用の指定商写像となることを、複体の射の等式として証明した。
既存の `schurArityInputCoefficientIso_quotient` と `coinvariantTotalQuotient_comparison` を接続している。

増分は 15 行、a の実測は **3,639 行**。二つの指定射の照合全体はまだ未完了で、
この補題だけを a の完了とはしない。規模による停止条件に達したという報告でもない。
次に残るのは、指定商を四因子の交換・群変更・直積群の分離へ通す照合と、
標準語への厳密な Hopf 作用の照合である。

一対象のビルドは成功（`/tmp/bsw16/strict-coefficient-01.log`）。
別の鍵での監査も成功し、四モジュール・56 宣言・標準三公理のみ
（`/tmp/bsw16/audit-strict-coefficient.log`）。sorry・追加公理はない。
鍵の終了をそれぞれ回収済み。新規モジュールはなく、登録待ち四本の一覧は同じ。


## 51. 厳密な指定商の分離を証明し、§18 の規模条件で停止

元の複体の圏での一致を実装し、`ProductQuotientCompatibility`（83 行）を追加した。
次の五宣言を定義・証明した。任意の群・非有界複体を扱い、平坦性を仮定しない。

- `actionCoinvariantQuotient`：元の作用の複体の指定商写像。
- `actionCoinvariantQuotient_naturality`：同変な複体の射との厳密な可換性。
- `productCoinvariantTotalIso_quotient`：直積群の全複体の分離と、左右の指定商のテンソルの一致。
- `coinvariantGroupChangeComplexIso_quotient`：群変更が元の指定商を保つこと。
- `productCoinvariantComplexIso_quotient`：実際のテンソル複体の対角作用の商についての分離公式。

全複体の双次数の指定包含へ前合成し、元のテンソルの生成元で照合した。
これらは厳密な射の等式であり、ホモトピー圏への弱化は用いていない。

### 51.1 実測・残り・停止の理由

現在の a は **3,639 + 83 = 3,722 行**。§48 からの増分は §50 の 15 行と今回の 83 行である。
§40.2 の中間比較は次のとおり（完了時の比較ではない）。

| §40.2 の行 | 当時の見込み | 今回までの実測 | 差 |
| --- | ---: | ---: | ---: |
| 固定 arity の軌道直和と二色係数の接続 | 100〜140 | 231 | +91〜+131 |
| 係数と入力の順序・係数作用 | 80〜100 | 124 | +24〜+44 |
| テンソル側の二色表示 | 230〜330 | 124 | −206〜−106 |
| 指定射の照合と全体の比較 | 250〜350 | 884（786 + 15 + 83）、未完 | +534〜+634 |
| **計** | **660〜920** | **1,363** | **+443〜+703** |

残りは次のように見積もる。既存補題の行数は重複計上しない。

| 残る接続 | 今回閉じた部分と、なお必要な部分 | 見込み |
| --- | --- | ---: |
| 標準語から誘導表示・軌道直和へ | 指定商の基礎式はあるが、`inducedCoinvariantTotalIso` の単位生成元、標準部分群の同定、軌道直和への包含を通す図式が残る | 95〜140 |
| 係数比較からテンソル側の指定商へ | 一般の群変更と直積分離は今回証明。`twoColorTargetSchurIso` の四因子交換、`twoColorLeftInputAction_sequence`・右の対応式による運搬、二つの Schur 商への復帰を同じ式へ組み合わせる部分が残る | 30〜50 |
| 厳密な Hopf 射の標準語上の式 | 単位の反復代入はあるが、標準語のテンソル冪を分離し、左ブロック交換と指定二色係数を照合する部分が残る | 95〜135 |
| 全射の一致と指定余積比較の擬同型 | `freeStandardSource_hom_ext` と `hopfCoproductComparison_quasiIso_of_free` へ二図式を接続する | 15〜25 |
| **残り計** | | **235〜350** |

完成見込みは **3,957〜4,072 行**。上端が承認上限 **4,000 行**を超える見込みとなったので、
§18 に従い検証済み分をコミットして停止する。これは実測が既に 4,000 行を超えたという意味ではない。
§48 ではテンソル側の残り全体を 45〜70 行と見積もったが、§50 と今回の一般の指定商の接続に
計 98 行を要し、二色の具体的な作用の同定を含む適用がなお残る。この点で見込みが増えた。

停止前のホモトピー圏による検討は §49 に記録済み。
全射のホモトピーがあれば擬同型性への復帰には十分だが、標準語上のホモトピーだけでは
`freeStandardSource_hom_ext` を適用できない。さらに、その後のユーザーの指示は
「ホモトピー圏ではなく元の圏での一致」であるため、今回も厳密な一致だけを採用した。
弱化によって未証明の接続を完了扱いにはしていない。

**a は未完了**。`J ≫ freeSchurCoefficientHomotopyEquiv.hom = M` と
`J ≫ freeHopfComparison.hom = M` は引き続き未証明。
§20.2・§40.2 の完了時の比較は未提出であり、B の厳密な前段の残りへは進んでいない。

### 51.2 検証・登録待ち

一対象の最終ビルド成功（`/tmp/bsw16/product-quotient-05.log`）。新設モジュールの警告なし。
本体の直接の importer はまだない。別の一回の鍵で、登録待ち五モジュールの全所有宣言を監査した。
**69 宣言・標準三公理のみ**（`/tmp/bsw16/audit-product-quotient.log`）。sorry・追加公理はない。
各終了を回収し、鍵を返した。ルートビルドは行っていない。

登録待ちの従来四本に、次を追加する。

- `SerrePositivity.EInfinity.BarrattEccles.Theory.ProductQuotientCompatibility`

一覧は `klw1-followup/registration-modules.json`（五本）。共通入口と共通監査は変更していない。


## 52. §19 の取り込み、厳密な作用の運搬と日程の見通し（途中記録）

main `e08a65880` を取り込み、§19 を読んだ。上限は 4,200 行で、厳密な一致のまま続ける。
`ProductQuotientCompatibility` に `actionCoinvariantQuotient_transport`（13 行）を追加した。
同じ群作用の等式を表現の複体の同型へ移したとき、その余不変への指定商写像が
元の複体の圏で厳密に保たれることを証明した。
`twoColorTargetSchurIso` 内の左右の入力作用の同定を、指定商とともに扱うための補題である。

一対象のビルド成功（`/tmp/bsw16/quotient-transport-01.log`）。
別の鍵の監査も成功し、五モジュール・70 宣言・標準三公理のみ
（`/tmp/bsw16/audit-quotient-transport.log`）。各終了を回収して鍵を返した。
新設モジュールはなく、登録待ちは五本のまま。a の実測は **3,735 行**。

### 52.1 11 月 13 日夕方までの見通し

**現時点では完了を確約できず、凍結の一晩の確実な前提には置けない。**
残りの二つの図式全体は、まだ Lean で型検査できた証明になっていない。
行数の見込みだけを根拠に、必要な作業時間や完了日を保証しない。
これまでの見積りでは、表示同型の構成と指定商・指定包含を保つ可換性の証明を
短い一つの接続として扱い、小さく見積もっていた。

残る確認点は、(1) 誘導表示の単位生成元から軌道直和までの指定射、
(2) 二色の具体的な作用・四因子の交換・左右の Schur 商への接続、
(3) 厳密な Hopf 射の標準語上の式、(4) 全射の一致と擬同型性への復帰。
今回の運搬補題は (2) の準備であり、(1)〜(4) が閉じたとはしていない。

この記録は完了報告でも規模による停止報告でもない。
二式 `J ≫ freeSchurCoefficientHomotopyEquiv.hom = M` と
`J ≫ freeHopfComparison.hom = M` は未証明であり、
§20.2・§40.2 の完了時の実測比較はまだ提出していない。


## 53. 二色の具体的なテンソル側の図式を証明（実装途中）

`TwoColorTargetCompatibility`（64 行）に `twoColorTargetSchurIso_quotient` を証明した。
`twoColorTargetSchurIso` の順射に左右の `schurArityInputCoinvariantIso` の順射を後合成し、
元の二色の全複体の指定商を前合成すると、四因子の `tensorμ` の後の左右の指定商のテンソルに
厳密に一致する。後合成している二つの射は既存の同型の順射である。

今回は一般補題の追加だけではなく、具体的な二色作用に対して、左右の入力作用の同定、
表現の複体への等式の運搬、群変更、直積分離を適用した図式全体を閉じた。
運搬の書き換えで 200,000 heartbeats の上限に達したため、この一補題だけ 800,000 にした。
既存宣言や界面の型は変更していない。

一対象の最終ビルド成功（`/tmp/bsw16/target-compatibility-05.log`）。
別の鍵での所有宣言の監査も成功し、六モジュール・75 宣言・標準三公理のみ
（`/tmp/bsw16/audit-target-compatibility.log`）。sorry・追加公理はない。
各プロセスの終了を回収し、鍵を返した。新規の長い行はない。

a の実測は **3,735 + 64 = 3,799 行**。承認上限は 4,200 行。
残るのは、このテンソル側の式を係数比較の順射・軌道直和へ接続することと、
厳密な Hopf 射の標準語上の式、および全射の一致・擬同型性への復帰。
二つの `J ≫ hom = M` 全体の完了報告ではない。目標は継続中であり、規模停止は宣言しない。
§20.2・§40.2 の完了時の比較と、凍結前の完了判定は依然として未提出である。

登録待ちに `SerrePositivity.EInfinity.BarrattEccles.Theory.TwoColorTargetCompatibility` を追加する。
一覧は六本。共通入口・共通監査は編集していない。


## 54. 指定係数比較の順射から元の Schur 商までを接続（実装途中）

`CoinvariantQuotientNaturality`（100 行）を追加した。

- `coinvariantTotalQuotient_naturality_right`：入力を固定した任意の同変な係数射と、指定全複体商の厳密な自然性。
- `twoColorCoefficientTarget_quotient`：既存の `twoColorComplexInputHomotopyEquiv.hom` を、§53 の具体的な二色表示の図式へ接続。
- `twoColorCoefficientTarget_schurQuotient`：元の係数優先の順序で、同じ指定係数射と左右の元の arity 商のテンソルに一致すること。

最後の式は左右の `schurArityInputCoinvariantIso` の順射で後合成して検出し、
`schurArityInputCoinvariantIso_quotient`、braiding の自然性、既存の `tensorμ_braiding` で証明した。
すべて元の複体の圏の射の等式であり、ホモトピー圏へ弱めていない。
また `TwoColorTargetCompatibility` に計算上限を変更した理由のコメントを一行追加し、
linter の指示に従った（64 → 65 行、証明内容は同じ）。

a の実測は **3,799 + 100 + 1 = 3,900 行**。上限は 4,200 行。
テンソル側の係数射と元の商の式は閉じたが、標準語から誘導表示・軌道直和への始域側と、
厳密な Hopf 射の標準語上の式、全射の一致・擬同型性への復帰は残っている。
従って二つの `J ≫ hom = M` 全体の完了を宣言しない。目標は継続中。

対象ビルド成功（`/tmp/bsw16/quotient-naturality-06.log`）。
別の鍵で七モジュール・80 宣言を監査し、標準三公理のみ
（`/tmp/bsw16/audit-quotient-naturality.log`）。その後の変更は上記の理由コメントだけで、
最終ソースと直接の importer のビルドも成功（`/tmp/bsw16/quotient-naturality-07.log`）。
sorry・追加公理はない。すべて終了を回収し、鍵を返した。

登録待ちに `SerrePositivity.EInfinity.BarrattEccles.Theory.CoinvariantQuotientNaturality` を追加する。
一覧は七本。共通入口・共通監査は変更していない。


## 55. 誘導表示の指定包含の照合と、完成見込みによる中間停止

### 55.1 今回閉じた範囲

`InducedQuotientCompatibility`（53 行）に
`inducedCoinvariantTotalIso_inv_inclusion` を証明した。
任意の部分群 H、入力の表現複体 V、元の群上の複体 W・B と指定包含
`ι : V ⟶ res W` について、双次数の元 x・y の余不変類を、誘導表示の全複体の逆比較と
`finiteInductionCochainInclusion` に通すと、指定包含の値 `ι(x)` と y の余不変類になる。
等式は元の複体の各次数での厳密な等式であり、ホモトピー圏を使っていない。
入力の cofibrancy も仮定していない。

独立した包含射の等式を先に型付けする案では、全複体の展開時に 800,000 heartbeats に達した。
最終版はその案を残さず、既存の `HomologicalComplex₂.ιTotal_map` から生成元の等式を直接取り出し、
`ι_mapBifunctorMap` と誘導表現の単位生成元の計算を使った。
最終版に `maxHeartbeats` の引上げはない。未使用の simp 引数の警告も除去した。
既存の公開宣言と界面の型は変更していない。

最終対象ビルド成功：`/tmp/bsw16/induced-quotient-10.log`。
別の鍵で最終監査成功：`/tmp/bsw16/audit-induced-quotient-final.log`。
登録待ち八モジュール・83 宣言、標準三公理のみ。sorry・追加公理はない。
鍵は `--wait 3600` で一コマンドずつ取得し、すべての終了を回収して返した。
新規モジュールなので直接の importer はまだない。共通入口と共通監査は編集していない。

### 55.2 残る接続を含む見込みと停止理由

a の検証済み実測は **3,900 + 53 = 3,953 行**。承認上限 4,200 行に対する残枠は 247 行。
今回の補題だけでは、標準語から元の Schur 複体の比較への式はまだ得られない。
`schurArityOrbitIso`・`orbitStandardCoefficientIso`・`schurBinaryOrbitIso` の実際の定義に沿い、
残りを次のように分けて数え直した。

| 未証明の接続 | 使う既存の宣言と、残る式 | 追加見込み |
| --- | --- | ---: |
| 群変更と指定全複体商 | `coinvariantTotalGroupChangeIso` に対する指定商の式。作用商の群変更の補題から運ぶ | 25〜40 |
| 入力射と指定全複体商 | 係数方向の自然性は済み。入力方向の自然性を、今回の誘導包含の式と接続する | 30〜45 |
| 標準語の同定 | `twoColorOrbitStandardInputIso`・`twoColorStandardSeparatedIso` を、同じ指定商と標準語包含の式に適用する | 20〜35 |
| 軌道直和から全 Schur 比較 | `schurArityOrbitIso` の各包含、`sigmaSigmaIso` と `Sigma.reindex` の指定包含を追い、§54 のテンソル側の式へ接続する | 35〜50 |
| 厳密な Hopf 射の標準語上の式 | 既存の零入力消去・左右の単位挿入と分離を使い、`freeStandardSource_hopfComparison_arity` を同じ指定係数射の式へ戻す | 95〜135 |
| 全射の一致と擬同型への復帰 | `freeStandardSource_hom_ext` と既存の自由余積比較への移送 | 15〜25 |
| **残り** | | **220〜330** |

完成見込みは **4,173〜4,283 行**。これは未実装部分の見積りであり、行数の下限の証明ではない。
上端が承認上限を 83 行超える見込みなので、新しい証明の追加はここで止め、
今回検証に通った分をコミットして報告する。一般補助へ分けた行数も a に含めている。

以前の「始域側の接続」の見積りでは、誘導表示の生成元の計算と、群変更・入力射の自然性・
直和の指定包含の照合を一つの短い接続として扱っていた。今回の 53 行が閉じるのは前者であり、
後者を定義的等しさとして省くことはできない。新しい経路の追加やセル対への変更ではない。
§51 の 3,722 行からの増分は 231 行で、残りを含めると同時点から 451〜561 行となる。
同時点の残り 235〜350 行という見積りを超えていることも明記する。

### 55.3 未完了の主張・日程・登録

`J ≫ freeSchurCoefficientHomotopyEquiv.hom = M` と
`J ≫ freeHopfComparison.hom = M` の全体は未証明。
したがって指定された自由 Hopf 比較の擬同型性の完了は宣言しない。
§20.2・§40.2 の各行の最終実測比較は、a が閉じた時点の報告として依然残る。
今回の表は途中の見積り更新であり、その完了報告の代用ではない。

**11 月 13 日夕方までに閉じられるとは、現時点では確約できない。**
今回の停止条件に加え、二つの指定射の全体の証明はまだ検証されていないため、
凍結の一晩の確実な前提には置かない。厳密な一致の方針は維持する。
bar・sifted・Tot には進んでいない。

登録待ちに `SerrePositivity.EInfinity.BarrattEccles.Theory.InducedQuotientCompatibility` を追加した。
全八本の一覧は `klw1-followup/registration-modules.json`。
この節は規模の見込みによる中間停止の報告であり、a または W16 全体の完了報告ではない。

## 56. §20：残る照合の型の一覧（実装前に固定）

main `f0ae62e99` の §20 を取り込んだ。以下を実装前の一覧とする。
記載した型は紙の型案であり、まだ新しい Lean ファイルとして検証したとは扱わない。
既存宣言の型はソースで確認した。以下の新規主張を番号順に証明する。
一覧にない数学的な補助主張が必要と判明したら、局所 `have` に隠して続けず、その型と漏れた理由を報告して止める。
結合律・同型の消去・関手性・要素での ext・定義の展開そのものは既存 API の使用とする。
「全体の等式を証明するために必要な任意の補題」のような予備枠は設けない。

### 56.1 共通の記法と始域側（L01〜L09）

一般の部分は namespace `SerrePositivity.EInfinity`、次の文脈を使う。

```lean
open CategoryTheory MonoidalCategory HomologicalComplex Limits
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers
universe u
variable {R G H : Type u} [CommRing R] [Group G] [Group H]
variable {K K' L : Complex R}
```

**L01：群変更と指定全複体商。** `coinvariantTotalQuotient_comparison` と
`coinvariantGroupChangeComplexIso_quotient` を、`coinvariantTotalGroupChangeIso` の定義へ適用する。

```lean
lemma coinvariantTotalGroupChangeIso_quotient
    (e : H ≃* G) (ρ : G →* End K) (σ : G →* End L) :
    coinvariantTotalQuotient (ρ.comp e.toMonoidHom) (σ.comp e.toMonoidHom) ≫
      (coinvariantTotalGroupChangeIso e ρ σ).hom = coinvariantTotalQuotient ρ σ
```

**L02：入力方向の自然性。** 係数方向の既存
`coinvariantTotalQuotient_naturality_right` と同じ双次数の指定商の計算。
`coinvariantTotalQuotient_ι`、`ι_mapBifunctorMap`、`TensorProduct.ext` を使う。

```lean
lemma coinvariantTotalQuotient_naturality_left
    (ρ : G →* End K) (τ : G →* End K') (σ : G →* End L)
    (f : K ⟶ K') (hf : ∀ g, (ρ g).asHom ≫ f = f ≫ (τ g).asHom) :
    coinvariantTotalQuotient ρ σ ≫
      (inputCoinvariantTotalFunctor (representationCochainComplex σ)).map
        (representationCochainMap ρ τ f hf) =
    (f ▷ L) ≫ coinvariantTotalQuotient τ σ
```

**L03：入力作用の等式による運搬。** `h` を消去し、関手の `map_id` を使う。

```lean
lemma coinvariantTotalQuotient_transport_left
    (ρ τ : G →* End K) (σ : G →* End L) (h : ρ = τ) :
    coinvariantTotalQuotient ρ σ ≫
      (inputCoinvariantTotalFunctor (representationCochainComplex σ)).map
        (eqToIso (congrArg representationCochainComplex h)).hom =
    coinvariantTotalQuotient τ σ
```

以下は namespace `SerrePositivity.EInfinity.BarrattEccles` で、
`(R : Type u) [CommRing R] (X Y : Complex R)` を変数とする。
紙の式を短くするため、次の略記を固定する（新しい数学的仮定はない）。

```lean
local notation "C" => (operad R).arity
local notation "F" => (operad R).freeAlgebra
local notation "A₀" => fun Z r =>
  arityCoinvariantComplex (schurDiagram R (sequence R) Z) r
local notation "q₀" => fun Z r =>
  arityCoinvariantComplexQuotient (schurDiagram R (sequence R) Z) r
local notation "ρw" => fun r (k : ULift.{u} (Fin (r + 1))) =>
  binaryTensorWordFixedAction X Y r (binaryTensorCountPattern r k.down)
    ((MulEquiv.ulift : ULift.{u} (Equiv.Perm (Fin r)) ≃*
      Equiv.Perm (Fin r)).toMonoidHom.comp (binaryTensorPatternSubgroup r k).subtype)
    (fun g => g.property)
local notation "σw" => fun r (k : ULift.{u} (Fin (r + 1))) =>
  (arityComplexAction R r).comp (binaryTensorPatternSubgroup r k).subtype
local notation "qW" => fun r k => coinvariantTotalQuotient (ρw r k) (σw r k)
local notation "qS" => fun m n => coinvariantTotalQuotient
  (tensorComplexAction (twoColorLeftInputAction X m n) (twoColorRightInputAction Y m n))
  (twoColorSourceComplexAction R m n)
local notation "qStd" => fun m n =>
  (β_ (C (m + n)) (power X m ⊗ power Y n)).hom ≫ qS m n
local notation "S" => fun m n =>
  eqToHom (congrArg (binaryTensorWordObj X Y (m + n)) (binaryTensorCountPattern_add m n)) ≫
    (binaryTensorStandardPowersIso X Y m n).hom
```

**L04：実際の固定 arity の軌道直和の指定包含。**
`schurArityInputCoefficientIso_quotient`、L03、
`binaryTensorOrbitComplexIso_ι`、`PreservesCoproduct.iso` の包含の式、
`inducedCoinvariantTotalIso_inv_inclusion`（§55）を使う。
必要なら同型の逆を後合成して検出し、`mapBifunctor.hom_ext` と生成元で確認する。

```lean
lemma schurArityOrbitIso_word_quotient (r : ℕ) (k : ULift.{u} (Fin (r + 1))) :
    (C r ◁ binaryTensorWordInclusion X Y r (binaryTensorCountPattern r k.down)) ≫
      q₀ (X ⊞ Y) r ≫ (schurArityOrbitIso X Y r).hom =
    (β_ (C r) (binaryTensorWordObj X Y r (binaryTensorCountPattern r k.down))).hom ≫
      qW r k ≫ Sigma.ι (orbitCoefficientComplex X Y r) k
```

**L05：標準語の群と分離同型が指定商を保つ。**
L01・L02・L03、`binaryTensorFixedRepresentationCongr` の定義（語の等式の消去）、
`twoColorStandardSeparatedIso_hom_f` を使用する。

```lean
lemma orbitStandardCoefficientIso_quotient (m n : ℕ) :
    qW (m + n) (ULift.up ⟨m, by omega⟩) ≫
      (orbitStandardCoefficientIso X Y m n).hom =
    (S m n ▷ C (m + n)) ≫ qS m n
```

**L06：標準語から arity の直和への式。** L04・L05、braiding の自然性、
`binaryTensorCountPattern_add` の等式による運搬と同型の消去。

```lean
lemma schurArityOrbitIso_standard_quotient (m n : ℕ) :
    (C (m + n) ◁ ((binaryTensorStandardPowersIso X Y m n).inv ≫
      binaryTensorWordInclusion X Y (m + n) (binaryTensorStandardPattern m n))) ≫
      q₀ (X ⊞ Y) (m + n) ≫ (schurArityOrbitIso X Y (m + n)).hom =
    qStd m n ≫ (orbitStandardCoefficientIso X Y m n).inv ≫
      Sigma.ι (orbitCoefficientComplex X Y (m + n)) (ULift.up ⟨m, by omega⟩)
```

**L07：全 arity を二添字へ移した包含の式。** L06、
`arityCoinvariantComplexIso_ι`、`Sigma.map`・`sigmaSigmaIso`・`Sigma.reindex` の包含の式。

```lean
lemma freeStandardSource_binaryOrbit (m n : ℕ) :
    freeStandardSource R X Y m n ≫ (schurBinaryOrbitIso X Y).hom =
    qStd m n ≫ (orbitStandardCoefficientIso X Y m n).inv ≫
      Sigma.ι (fun p : ℕ × ℕ => orbitCoefficientComplex X Y (p.1 + p.2)
        (ULift.up ⟨p.1, by omega⟩)) (m, n)
```

**L08：二色係数側の直和への接続。** L07、既存
`twoColorCoefficientTarget_schurQuotient`、`schurTensorArityIso_generators` を使う。
これは二つの全体式の第一の式であり、途中の図式で代用しない。

```lean
lemma freeStandardSource_coefficientComparison (m n : ℕ) :
    freeStandardSource R X Y m n ≫ (freeSchurCoefficientHomotopyEquiv X Y).hom =
      freeStandardTarget R X Y m n
```

**L09：標準ブロックの包含（新証明不要）。** 既存の
`binaryTensorStandardPowersIso_inclusion` を逆同型で前合成するだけで次の型を得る。

```lean
lemma standardWord_inclusion_append (m n : ℕ) :
    (binaryTensorStandardPowersIso X Y m n).inv ≫
      binaryTensorWordInclusion X Y (m + n) (binaryTensorStandardPattern m n) =
    (TensorPowers.map (biprod.inl : X ⟶ X ⊞ Y) m ⊗ₘ
      TensorPowers.map (biprod.inr : Y ⟶ X ⊞ Y) n) ≫ (appendIso (X ⊞ Y) m n).hom
```

### 56.2 Hopf 射側（L10〜L18）

L10〜L12 は一般の複体について namespace `SerrePositivity.EInfinity` で述べる。

**L10：一定族の分離と冪の分離。** 二つの分離の定義に沿う帰納法。
各後続段は同じ `tensorμ` で、`tensorFamily_const_succ_hom` を用いる。

```lean
lemma tensorFamilyTensorIso_const (K L : Complex R) (r : ℕ) :
    eqToHom (tensorFamily_const (K ⊗ L) r) ≫ (tensorPowerSeparation K L r).hom =
    (tensorFamilyTensorIso r (fun _ => K) (fun _ => L)).hom ≫
      (eqToHom (tensorFamily_const K r) ⊗ₘ eqToHom (tensorFamily_const L r))
```

一定族の射の比較は新補題不要：`tensorFamilyGenerator_asMap` と
`tensorFamilyGenerator_constant` が
`tensorFamilyMap r (fun _ => f) ≫ eqToHom (tensorFamily_const L r) =
 eqToHom (tensorFamily_const K r) ≫ TensorPowers.map f r`
を与える。

**L11：左単位の挿入と分離。** 右側の型は既存 `tensorFamilyTensorIso_insert_right`。
左側は `tensorFamilyTensorIso_unit_left` に逆同型を合成して得る。

```lean
lemma tensorFamilyTensorIso_insert_left (r : ℕ) (V : Fin r → Complex R) :
    tensorFamilyMap r (fun j => (λ_ (V j)).inv) ≫
      (tensorFamilyTensorIso r (fun _ => 𝟙_ (Complex R)) V).hom =
    (λ_ (tensorFamily r V)).inv ≫
      ((tensorUnitFamilyIso R r).inv ⊗ₘ 𝟙 (tensorFamily r V))
```

**L12a・L12b：単位射を一方へ入れた冪の分離。** 以下の `unitPow` は式の略記。
L10・L11・既存の右単位版、`tensorFamilyTensorIso_naturality`、一定族の射の比較を使う。

```lean
local notation "unitPow" => fun {K : Complex R} (u : 𝟙_ (Complex R) ⟶ K) r =>
  (tensorUnitFamilyIso R r).inv ≫ tensorFamilyMap r (fun _ => u) ≫
    eqToHom (tensorFamily_const K r)
lemma tensorPowerSeparation_insert_right {Z K L : Complex R}
    (f : Z ⟶ K) (u : 𝟙_ (Complex R) ⟶ L) (r : ℕ) :
    TensorPowers.map ((ρ_ Z).inv ≫ (f ⊗ₘ u)) r ≫ (tensorPowerSeparation K L r).hom =
    (ρ_ (power Z r)).inv ≫ (TensorPowers.map f r ⊗ₘ unitPow u r)
lemma tensorPowerSeparation_insert_left {Z K L : Complex R}
    (u : 𝟙_ (Complex R) ⟶ K) (f : Z ⟶ L) (r : ℕ) :
    TensorPowers.map ((λ_ Z).inv ≫ (u ⊗ₘ f)) r ≫ (tensorPowerSeparation K L r).hom =
    (λ_ (power Z r)).inv ≫ (unitPow u r ⊗ₘ TensorPowers.map f r)
```

以下は再び BarrattEccles、R・X・Y・C・F は §56.1 と同じ。
指定単位族を末尾／先頭へ挿入する二つの射を、次の式で略記する。
（実装で定義名を設けても、この二式の略記に限る。）

```lean
local notation "eL" => fun m n =>
  (ρ_ (power X m)).inv ≫
    (TensorPowers.map ((operad R).schurUnit X) m ⊗ₘ nullaryUnitPower R (F X) n) ≫
    (appendIso (F X).carrier m n).hom
local notation "eR" => fun m n =>
  (λ_ (power Y n)).inv ≫
    (nullaryUnitPower R (F Y) m ⊗ₘ TensorPowers.map ((operad R).schurUnit Y) n) ≫
    (appendIso (F Y).carrier m n).hom
```

**L13：実際の Hopf 入力の分離。** L09・L12、`appendIso_naturality`、
`tensorPowerSeparation_append`、`nullaryUnitPower_eq`、
`freeHopfComparisonInput`・`hopfTensorInl`・`hopfTensorInr` の定義。
残る四因子の配置は `tensorμ` と単位子の自然性・monoidal coherence。

```lean
lemma freeHopfComparisonInput_standard_separation (m n : ℕ)
    (h0 : IsIso ((hopf R).counit.map.app (FiniteBijection.of 0))) :
    (binaryTensorStandardPowersIso X Y m n).inv ≫
      binaryTensorWordInclusion X Y (m + n) (binaryTensorStandardPattern m n) ≫
      TensorPowers.map (freeHopfComparisonInput (hopf R) h0 X Y) (m + n) ≫
      (tensorPowerSeparation (F X).carrier (F Y).carrier (m + n)).hom =
    eL m n ⊗ₘ eR m n
```

**L14：末尾の零入力の作用。** 前半を消す既存 `nullaryPrefixDelete_action` の左右交換版。
`twoColorLeftCoefficient`、`appendIso_blockSwap`、代数の equivariance を用いる。

```lean
lemma twoColorLeftCoefficient_action (Z : (operad R).Algebra) (m n : ℕ) :
    (twoColorLeftCoefficient R m n ▷ power Z.carrier m) ≫ Z.action m =
    (C (m + n) ◁ ((ρ_ (power Z.carrier m)).inv ≫
      (power Z.carrier m ◁ nullaryUnitPower R Z n) ≫
      (appendIso Z.carrier m n).hom)) ≫ Z.action (m + n)
```

**L15a・L15b：自由生成元への作用。** L14 と既存 `nullaryPrefixDelete_action` を
入力冪の射で前合成し、`Operad.schurAction_generators` を使う。

```lean
lemma freeLeftUnitExtension_action (m n : ℕ) :
    (C (m + n) ◁ eL m n) ≫ (F X).action (m + n) =
    (twoColorLeftCoefficient R m n ▷ power X m) ≫ schurι R (sequence R) X m
lemma freeRightUnitExtension_action (m n : ℕ) :
    (C (m + n) ◁ eR m n) ≫ (F Y).action (m + n) =
    (twoColorRightCoefficient R m n ▷ power Y n) ≫ schurι R (sequence R) Y n
```

**L16：第二の全体式。** 既存 `freeStandardSource_hopfComparison_arity` に L13・L15 を適用。
`hopfTensorAction` と `twoColorCoefficientComparison` を展開し、`tensorμ` の自然性で接続。

```lean
lemma freeStandardSource_hopfComparison (m n : ℕ)
    (h0 : IsIso ((hopf R).counit.map.app (FiniteBijection.of 0))) :
    freeStandardSource R X Y m n ≫ (freeHopfComparison (hopf R) h0 X Y).hom =
    freeStandardTarget R X Y m n
```

**L17：自由代数全体での指定射の一致。** L08・L16 と既存 `freeStandardSource_hom_ext`。

```lean
lemma freeHopfComparison_eq_coefficientComparison
    (h0 : IsIso ((hopf R).counit.map.app (FiniteBijection.of 0))) :
    (freeHopfComparison (hopf R) h0 X Y).hom =
      (freeSchurCoefficientHomotopyEquiv X Y).hom
```

**L18：指定射の擬同型性。** L17 と鎖ホモトピー同値の既存の擬同型性のインスタンス。
任意の X・Y で主張するので、任意の cofibrant な入力も含む。

```lean
lemma freeHopfComparison_quasiIso
    (h0 : IsIso ((hopf R).counit.map.app (FiniteBijection.of 0))) :
    QuasiIso (freeHopfComparison (hopf R) h0 X Y).hom
```

その後の元の厳密な自由余積比較への復帰は既存
`hopfCoproductComparison_quasiIso_of_free` を用いる（新しい移送補題は要らない）。

### 56.3 §55.2 の行との対応と実装時の停止規則

| §55.2 の行 | 今回の型 |
| --- | --- |
| 群変更と指定全複体商 | L01 |
| 入力射と指定全複体商 | L02・L03、既存の §55 の誘導包含の補題 |
| 標準語の同定 | L05、L06 の語の等式の運搬 |
| 軌道直和から全 Schur 比較 | L04・L06・L07・L08 |
| 厳密な Hopf 射の標準語上の式 | L09〜L16（L09 は既存宣言の系） |
| 全射の一致と擬同型への復帰 | L17・L18、既存の自由余積への移送 |

外枠は約 4,600 行。今後は途中の残行数の見込みだけで止めない。
上の一覧外の補題が必要になった場合に、その型と漏れた理由を記録して止める。
局所補題も対象とし、未証明の仮定を加えることや同型を別の射へ取り替えることで穴を隠さない。
§20.2・§40.2・§55.2 の見込みと最終実測の比較は、L18 まで閉じてから提出する。


## 57. 型一覧 L01〜L03 の検証と、L04 で判明した一覧外の主張による停止

### 57.1 検証済みの部分

§56 の型一覧を `876d5f357` で先にコミットし、承認待ちを挟まず実装に入った。
`SourceQuotientNaturality`（77 行）で次の三つを、一覧の型のまま証明した。

- L01 `coinvariantTotalGroupChangeIso_quotient`：群変更と指定全複体商。
- L02 `coinvariantTotalQuotient_naturality_left`：入力方向の自然性。
- L03 `coinvariantTotalQuotient_transport_left`：入力作用の等式による運搬。

対象ビルド成功：`/tmp/bsw16/source-naturality-02.log`。
別の鍵で監査成功：`/tmp/bsw16/audit-source-naturality.log`。
登録待ち九モジュール・87 宣言、標準三公理のみ。sorry・追加公理・新規の長い行はない。
鍵は `--wait 3600` で各ビルド・監査に限って持ち、全プロセスの終了を回収した。
実測は **3,953 + 77 = 4,030 行**。今回の停止は 4,600 行の外枠によるものではない。

### 57.2 一覧から漏れた具体的な入力作用の等式

L04 で `schurArityOrbitIso` の逆を後合成し、直和の比較を指定誘導包含まで戻した。
続いて `schurArityInputCoefficientIso_quotient` を適用し、
`binaryTensorFullInputSequenceIso` に沿う商の運搬を L03 で処理する箇所に来た。
ここで L03 の引数 `h` に渡す、以下の具体的な主張が型一覧に記載されていなかった。

```lean
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Limits
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers
universe u
lemma binaryTensorInputAction_eq (R : Type u) [CommRing R]
    (X Y : Complex R) (r : ℕ) :
    finiteBijectionComplexAction (bijectionFunctor (X ⊞ Y)) r =
      binaryTensorPowerAction X Y r
        (MulEquiv.ulift : ULift.{u} (Equiv.Perm (Fin r)) ≃*
          Equiv.Perm (Fin r)).toMonoidHom
end SerrePositivity.EInfinity.BarrattEccles
```

これは新しい数学的構成を要する主張ではない。
既存 `binaryTensorFullInputSequenceIso` の定義は、内部で `MonoidHom.ext`・`End.ext`・
`bijectionFunctor_map_permutation (X ⊞ Y) r g.down` を使い、この等式を表現複体の同型へ運んでいる。
ただし公開されている宣言の結論は複体の **同型** であり、上の **作用の等式** そのものではない。
L03 はその等式を仮定として受け取るので、L03 を証明しただけでは具体的な引数は供給されない。

§56 の L04 の説明で「L03 と既存の同型の定義を使う」とまとめ、
この具体的な引数を Lean の主張の型に落とすのを省いたのが漏れた理由である。
局所 `have` として同じ等式を証明して進めることも、今回の一覧外の補題の追加に当たるため行っていない。
上の型を新たな一覧項目として扱う必要がある、と判断して §20 の停止条件を適用した。

なお、同型を展開して L03 を直接書き換えに使う下書きは、
`/tmp/bsw16/orbit-quotient-04.log` のとおり型照合で 800,000 heartbeats に達した。
この計算上限自体を、新しい数学的補題が不可欠であることの証明とはしない。
停止理由は、具体的な作用の等式を一覧に含めずに L03 の適用を予定していたという一覧の漏れである。
既存の公開宣言を変更する必要があると主張しているわけでもない。

### 57.3 下書き・未完了部分・登録

L04 の未検証下書きは `/tmp/bsw16/OrbitQuotientCompatibility-L04-unverified.lean` に保管した。
本体の未検証モジュールとしては残さず、コミットにも含めない。
L04 は未証明、L05 以降は未実装で、二つの指定射全体の一致と a は未完了。
§20.2・§40.2・§55.2 の最終実測比較は、a が閉じた後の作業として残る。

今回の登録対象は `SerrePositivity.EInfinity.BarrattEccles.Theory.SourceQuotientNaturality`。
全九本の登録待ち一覧は `klw1-followup/registration-modules.json` に更新した。
共通入口と共通監査への登録は行っていない。
ここで一覧外の補題についての判断を待ち、bar・sifted・Tot には進まない。

## 58. §21 の再開と追加照合の台帳（進行中）

main `65cfdbe3f` の §21 を取り込み、L04a を実装した。
`BinaryInputActionEquality` の `binaryTensorInputAction_eq` は、既存の
`bijectionFunctor_map_permutation` から `MonoidHom.ext`・`End.ext` で証明した。
この具体的な等式を L03 に渡し、L04 `schurArityOrbitIso_word_quotient` も証明した。
L04 は直和の逆同型を後合成して指定誘導包含へ戻し、braiding の自然性と
`inducedCoinvariantTotalIso_inv_inclusion` により閉じた。
対象ビルド成功：`/tmp/bsw16/orbit-quotient-06.log`。この時点では追加分の公理監査は未実施。

### 58.1 追加照合 I1（使用数 1／3）

L05 の `binaryTensorFixedRepresentationCongr` は語の等式から作る同型である。
その同型に沿って指定全複体商を運ぶ次の型を追加する。
§56 では「語の等式の消去」と説明していたが、実装では一般の二つの語を変数として
等式を消去する必要があるため、その照合を独立の型として明記する。
新しい構成ではなく、同じ指定商の等式による運搬である。

```lean
namespace SerrePositivity.EInfinity
open CategoryTheory HomologicalComplex MonoidalCategory
open SerrePositivity.DifferentialGraded
universe u
variable {R G : Type u} [CommRing R] [Group G]
lemma coinvariantTotalQuotient_wordCongr (X Y : Complex R) {L : Complex R}
    {r : ℕ} {w z : BinaryTensorWord r} (h : w = z)
    (φ : G →* Equiv.Perm (Fin r)) (hw : ∀ g, φ g • w = w)
    (hz : ∀ g, φ g • z = z) (σ : G →* End L) :
    coinvariantTotalQuotient (binaryTensorWordFixedAction X Y r w φ hw) σ ≫
      (inputCoinvariantTotalFunctor (representationCochainComplex σ)).map
        (binaryTensorFixedRepresentationCongr X Y h φ hw hz).hom =
    (eqToHom (congrArg (binaryTensorWordObj X Y r) h) ▷ L) ≫
      coinvariantTotalQuotient (binaryTensorWordFixedAction X Y r z φ hz) σ
end SerrePositivity.EInfinity
```

L04a は調整役の承認済み追加で、この 3 枠には数えない。

### 58.2 追加照合 I2（使用数 2／3）

L14 の `operadBlockSwap m n` は `Fin (m + n) ≃ Fin (n + m)` である。
既存の `Operad.Algebra.equivariance` は同じ arity の置換について述べているため、
異なる長さの式で表記した同じ作用との照合を次の型で追加する。
全単射から長さの等式を得てそれを消去し、既存の等変性へ戻すだけであり、
作用・擬同型・ホモトピーを新しく構成しない。

```lean
namespace SerrePositivity.EInfinity
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers
universe u
variable {R : Type u} [CommRing R]
lemma algebra_action_bijection {P : Operad R} (Z : P.Algebra)
    {m n : ℕ} (e : Fin m ≃ Fin n) :
    (P.arityBijectionMap e ⊗ₘ tensorPowerEquivMap Z.carrier e) ≫ Z.action n = Z.action m
end SerrePositivity.EInfinity
```

再利用する宣言は `Fintype.card_congr`、`tensorPowerEquivMap_perm`、`Z.equivariance`。

### 58.3 追加照合 I3（使用数 3／3）

L13 の四因子の配置を、既存の `tensorμ_natural` と単位子の coherence に
接続するため、次の照合を独立させる。§56 では四因子の配置を文章でまとめていた。
二つの単位入力を先に入れて並べ替える射と、並べ替えた場所に同じ単位入力を
入れる射の一致であり、新しい構成・ホモトピー・擬同型性は含まない。

```lean
namespace SerrePositivity.EInfinity
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
universe u
variable {R : Type u} [CommRing R]
lemma tensorμ_unit_insert {X Y K L M N : Complex R}
    (f : X ⟶ K) (u : 𝟙_ (Complex R) ⟶ L)
    (v : 𝟙_ (Complex R) ⟶ M) (g : Y ⟶ N) :
    (((ρ_ X).inv ≫ (f ⊗ₘ u)) ⊗ₘ ((λ_ Y).inv ≫ (v ⊗ₘ g))) ≫
      tensorμ K L M N =
    ((ρ_ X).inv ≫ (f ⊗ₘ v)) ⊗ₘ ((λ_ Y).inv ≫ (u ⊗ₘ g))
end SerrePositivity.EInfinity
```

追加枠はこれで使い切った。今後一覧にない第四の照合または新しい数学が
必要と判明した時点で、その型と漏れた理由を書いて停止する。

### 58.4 一つ目の全体式と単位入力の分離（対象ビルド済み）

`StandardSourceComparison.freeStandardSource_coefficientComparison` により
**L08 `J ≫ freeSchurCoefficientHomotopyEquiv.hom = M` を元の複体の圏で証明した**。
L06 は固定 arity の指定標準語、L07 はその全 arity の直和への包含である。
再添字付けの逆で選ばれる添字も定義で照合し、別の同型への取り替えをしていない。
最終の警告除去を含む対象ビルドは `/tmp/bsw16/standard-hopf-01.log` で成功。
同じ呼び出しの `StandardHopfInput` は未検証の下書きで失敗しており、
呼び出し全体が成功したとは扱わない。

`StandardTensorSeparation` では L10・L11・L12a・L12b と I2 を証明した。
`UnitInputShuffle` では I3 を証明した。
ログはそれぞれ `/tmp/bsw16/standard-source-04.log` と `standard-source-05.log`。

| 追加モジュール | 型一覧 | 検証済み行数 |
| --- | --- | ---: |
| BinaryInputActionEquality | L04a | 30 |
| OrbitQuotientCompatibility | L04 | 85 |
| WordQuotientTransport | I1 | 40 |
| StandardQuotientCompatibility | L05 | 71 |
| StandardSourceComparison | L06〜L08 | 86 |
| StandardTensorSeparation | L10〜L12、I2 | 99 |
| UnitInputShuffle | I3 | 34 |
| **追加計** | | **445** |

a の検証済み実測は **4,030 + 445 = 4,475 行**。
L09 は既存の `binaryTensorStandardPowersIso_inclusion` をそのまま用いる。
L13〜L18 は未検証で、二つ目の全体式と a 全体はまだ未完了。
§20 に従い、型一覧の証明中は見込みによる中間停止を繰り返さずに続ける。
この時点の登録待ちは上の七本を含む計十六本。共通入口と共通監査は編集しない。

七本を含む登録待ち十六本の監査は **120 宣言・標準三公理のみ**で成功。
ログは `/tmp/bsw16/audit-standard-source.log`。sorry・追加公理はなく、鍵を返却した。
七本と報告・登録待ち一覧だけをコミットし、未検証の三本は作業木に保持して L13 以降を続ける。

## 59. a の二つの指定射を厳密に同定（対象ビルド完了）

### 59.1 閉じた主張と一般性

§21 の承認後、`L04a` と §58 の追加照合 I1〜I3 を含む型一覧を証明した。
第四の一覧外補題、新しい構成・ホモトピー・擬同型性の補題は追加していない。
L18 の擬同型性は、最初から一覧にある主張である。

今回の三本は `SerrePositivity/EInfinity/BarrattEccles/Theory/` 以下。

| モジュール | 行数 | 証明した一覧項目 |
| --- | ---: | --- |
| `StandardHopfInput` | 72 | L13。実際の指定 Hopf 入力を、同じ左右の単位族へ分離。`freeLeftUnitExtension`・`freeRightUnitExtension` は §56 の eL・eR の式の略記 |
| `StandardUnitAction` | 66 | L14・L15a・L15b。末尾の零入力の作用と、左右の自由生成元への実際の作用 |
| `FreeHopfStrictComparison` | 59 | L16・L17・L18。二つ目の標準語上の式、全射の厳密な一致、指定自由 Hopf 比較の擬同型性 |
| **追加計** | **197** | |

二つの全体式は、同じ `freeStandardSource` と `freeStandardTarget` を用いて閉じた。

- `freeStandardSource_coefficientComparison`（L08）：
  `J ≫ freeSchurCoefficientHomotopyEquiv.hom = M`。
- `freeStandardSource_hopfComparison`（L16）：
  `J ≫ freeHopfComparison.hom = M`。
- `freeHopfComparison_eq_coefficientComparison`（L17）：
  標準語の射の判別補題から、**元の複体の圏で二つの指定射そのものが等しい**。
- `freeHopfComparison_quasiIso`（L18）：
  その等式と既存の鎖ホモトピー同値の擬同型性から、実際の指定自由 Hopf 比較の擬同型性を得た。

ホモトピー圏での一致への置き換えはしていない。
係数比較の順射を別の選択で作り直したり、Hopf 比較の定義を変更したりもしていない。
任意の可換環 R と任意の入力複体 X・Y で述べ、cofibrancy・有界性・平坦性を仮定しない。
従って「任意の cofibrant な入力まで」という a の要求を含む。
`h0` は以前から指定 Hopf 包含に使う零 arity の余単位の同型性の証明であり、
新しい K 平坦性・モデル構造などの仮定を足していない。

元の厳密な自由余積比較へは、L18 を局所インスタンスとして供給して既存の
`hopfCoproductComparison_quasiIso_of_free` を適用できる。
既存の `freeSumCoproductIso_hopfComparison` が、その余積比較と同じ指定射の一致を保証する。
このための新しい移送補題を重ねて作っていない。
一般の代数への bar・幾何学的実現による拡張、全関手版 `coproduct_tensor` は、a の完了とは別の残作業である。

### 59.2 §20.2 の五行：見込みと最終実測

行数は docstring・空行を含む。§22.3・§36.3 の配賦を引き継ぎ、
一般補助の行数を外へ出さず、各ファイルを一度だけ数える。
§41 以後の指定包含・商・単位・射全体の照合は、§41.3 の方針どおり第五行へ計上した。

| §20.2 の行 | 元の見込み | 最終実測 | 差（実測−見込み） |
| --- | ---: | ---: | ---: |
| 語の指定包含・置換・標準ブロックの作用 | 160〜220 | 673 | +453〜+513 |
| 固定色数の軌道・標準語の安定化群 | 120〜180 | 433 | +253〜+313 |
| 誘導表示の射・逆・複体上の同型 | 260〜340 | 788 | +448〜+528 |
| Schur 複体の両側の分解・再添字付け | 220〜300 | 1,074 | +774〜+854 |
| 指定 Hopf 比較と係数比較・自由比較の擬同型 | 180〜250 | 1,704 | +1,454〜+1,524 |
| **計** | **940〜1,290** | **4,672** | **+3,382〜+3,732** |

配賦の検算：第一行は 355 + 231 + `TwoColorSeparatedInput` 87。
第二行は 200 + 111 + `TwoColorOrbitArity` 59 + `TwoColorOrbitTransport` 63。
第三行は 347 + 269 + `BinaryTensorOrbitComplex` 69 + `TwoColorInducedComplexInputs` 103。
第四行は `SchurComplexArity` 114、§40 の残り四本 351、
§41 の `CoinvariantGroupChange`・`SchurCoefficientOrder`・`InducedCoinvariantTotal`・
`TwoColorTargetSchur`・`TwoColorSourceSchur`・`ComplexCoproductHomotopy`・`FreeSchurComparison` の 609。
第五行は §41 の `FreeHopfComparison` 89 と、§44 以後の a の追加 1,615。

### 59.3 §40.2 の四行：見込みと最終実測

§40.3 の検証済み基点は 2,359 行。そこからの追加は **2,313 行**。
§41.3 の最初の三行の割り付けを保ち、それ以後の指定射の照合を第四行に含める。

| §40.2 の行 | 当時の残りの見込み | その後の最終実測 | 差 |
| --- | ---: | ---: | ---: |
| 固定 arity の軌道直和と二色係数の接続 | 100〜140 | 231 | +91〜+131 |
| 係数と入力の順序・係数作用 | 80〜100 | 124 | +24〜+44 |
| テンソル側の二色表示 | 230〜330 | 124 | −206〜−106 |
| 指定射の照合と全体の比較 | 250〜350 | 1,834 | +1,484〜+1,584 |
| **計** | **660〜920** | **2,313** | **+1,393〜+1,653** |

### 59.4 §55.2 の六行：見込みと最終実測

§55 の基点は 3,953 行。そこからの追加は **719 行**。
宣言を一つのファイルにまとめた箇所は下に示す連続行の区切りで割り付け、
ヘッダー・末尾・空行も含めて重複も除外もない。

| §55.2 の行 | 当時の残りの見込み | 最終実測 | 差 |
| --- | ---: | ---: | ---: |
| 群変更と指定全複体商 | 25〜40 | 33 | −7〜+8 |
| 入力射と指定全複体商 | 30〜45 | 74 | +29〜+44 |
| 標準語の同定 | 20〜35 | 160 | +125〜+140 |
| 軌道直和から全 Schur 比較 | 35〜50 | 122 | +72〜+87 |
| 厳密な Hopf 射の標準語上の式 | 95〜135 | 313 | +178〜+218 |
| 全射の一致と擬同型への復帰 | 15〜25 | 17 | −8〜+2 |
| **計** | **220〜330** | **719** | **+389〜+499** |

配賦：`SourceQuotientNaturality` の 1〜33 行を第一行、34〜77 行と
`BinaryInputActionEquality` 30 行を第二行へ置いた。
第三行は `WordQuotientTransport` 40、`StandardQuotientCompatibility` 71、
`StandardSourceComparison` 1〜49 行。
第四行は `OrbitQuotientCompatibility` 85 と `StandardSourceComparison` 50〜86 行。
第五行は `StandardTensorSeparation` 99、`UnitInputShuffle` 34、
`StandardHopfInput` 72、`StandardUnitAction` 66、`FreeHopfStrictComparison` 1〜42 行。
第六行は同ファイル 43〜59 行。

膨らんだ主因は、同型の存在と、その同型が指定商・指定包含・指定単位族を
保つという式を、旧見込みで短い一接続として扱っていたことである。
とくに標準語を等式で運ぶ場合と群同型で運ぶ場合、複体の台と自由代数の台、
有限族の単位挿入とテンソル冪の分離を、別々に照合する必要があった。
§56 の型一覧を固定してからは、承認された L04a と I1〜I3 だけを補い、
別経路・セル対・新しい数学へ広げずに閉じた。

最終実測 **4,672 行**は外枠の約 4,600 行に対して **72 行多い**。
この差を隠すための行の圧縮や別枠への移動は行っていない。
§20 の「一覧の補題を証明している間は、行数では止まらない」に従って一覧を閉じた。
a の型一覧に未証明の主張は残らない。一般の `coproduct_tensor` 全体の完了を意味するものではない。

### 59.5 検証・監査・登録

対象 `FreeHopfStrictComparison` のビルドは成功（10,523 jobs）。
ログは `/tmp/bsw16/standard-hopf-07.log`。
今回の三本に sorry・追加公理はなく、新しい警告もない。
依存先に既存の `letI` の style 警告が出るが、その既存宣言は変更していない。

公理監査は `/tmp/bsw16/audit-free-hopf-strict.lean` により、登録待ちの全十九本を対象とする。
結果は **十九本・146 宣言・標準三公理のみで成功**。
ログは `/tmp/bsw16/audit-free-hopf-strict.log`。監査の終了コード 0 を回収し、鍵と整理券を返却した。
これにより **a は完了**。新しい十本は全て対象ビルド・公理監査済みで、未検証の下書きは残らない。
登録待ち一覧は `klw1-followup/registration-modules.json` に保存する。
共通入口・共通監査・drafts・既存の公開宣言・界面の型は変更していない。

今回追加の登録対象：

- `SerrePositivity.EInfinity.BarrattEccles.Theory.StandardHopfInput`
- `SerrePositivity.EInfinity.BarrattEccles.Theory.StandardUnitAction`
- `SerrePositivity.EInfinity.BarrattEccles.Theory.FreeHopfStrictComparison`

§58 の七本は `9cbb55631`。今回の三本はその後の追加として取り込める。

§56 の紙の型一覧から L18 まで完了し、追加照合は I1〜I3 の三件で止まっている。
次は承認済みの順序どおり経路 B の厳密な前段の残り、続いて橋を待つ間の④の段 0 の準備。
今回のコミットには、その次の段の Lean の実装を混ぜていない。

## 60. §22：厳密な bar 前段の完了範囲の照合

main `561cecd5d` を fast-forward で取り込み、§22 を読んだ。
§29 の設計と `3bbb3b2ce` の二本（KL-W1 追従後の現在のソース）を宣言ごとに照合した。
厳密な前段に未実装の要件は残っていない。追加の包装を作る前に、既存の公開 API が
すでに満たしている範囲を次表で確定する。

| §29 の要件 | 一般の随伴での供給 | BE への実際の適用 |
| --- | --- | --- |
| 全単体図式 B と対象の全関手 | `StrictAdjunctionBar.diagramMap`・`diagramFunctor`・`barFunctor` | `strictBarFunctor` |
| 増大と対象に関する自然性 | `powerMap_augmentation`・`augmentedFunctor`・`barAugmentedFunctor` | `strictBarAugmentedFunctor` |
| 忘却後の同じ増大 | `underlyingAugmented` | `strictBarUnderlyingAugmented` |
| 単位からの追加退化と五つの関係式 | `underlyingExtraDegeneracy` の全欄 | `strictBarUnderlyingExtraDegeneracy` |
| 追加退化の自然性（全次数と零次） | `underlyingExtraDegeneracy_naturality`・`underlyingExtraDegeneracy_section_naturality` | 実際の `freeAlgebraAdjunction` を代入して使用可能 |
| 定値図式からの切断と増大との合成 | `underlyingSection`・`underlyingSection_comp_augmentation` | 同じ随伴を代入して使用可能 |
| 指定された評価射と生成元への照合 | 随伴の余単位・単位 | `strictBarAugmentation_zero`・`strictBarUnderlyingSection_zero` |

一般ファイルは `SerrePositivity/EInfinity/StrictAdjunctionBar.lean`、
実例は `SerrePositivity/EInfinity/BarrattEccles/Theory/StrictBar.lean`。
各次数の対象が Gⁿ⁺¹X である式、面と退化の式は、再利用元の
`ComonadSimplicialResolution.diagram_obj`・`diagram_face`・`diagram_degeneracy`。
追加退化からの単体的ホモトピーも Mathlib `ExtraDegeneracy.homotopy` を直接使える。
これらを BE 用の別名として再宣言する必要はない。

実測は従来どおり **266 + 60 = 326 行**、今回の追加 Lean は **0 行**。
§29 の見込み 390〜620 行より 64〜294 行少なく、上限 1,600 行以内。
検証根拠は §35 の対象ビルドと全二本・49 宣言の公理監査（標準三公理のみ）。
今回はソースを変更しておらず、同じ対象の再ビルド・再監査は行わなかった。
二本の module docstring に残る「未検証下書き」は当時の待機メモで、§35 の検証結果が現在の状態。

§29.1 の cofibrant 入力の取り直しの注意は、a が任意の入力複体で閉じたことで、
自由比較そのものの適用条件には不要となった。ただし bar の ∞ 図式への移送・実現の同定は
依然として必要であり、厳密な追加退化から native な余極限性へ飛躍しない。
これらと Tot・U の比較は、§22 の 3 の担当判断を待つ。
新規登録モジュールはなし。ここから④の紙の段 0 に進む。

## 61. ④の段 0：G12・M14・M15 の型案と実装の分割案（承認待ち）

### 61.1 現在の到達点と読み直した資料

§31 の下調べを、KL-W1 後の型・a 完了後の API に合わせて更新した。
読んだ入口は `EInfinity/Interface/Theory.lean`、`BarrattEccles/Theory.lean`、
`Theory/Assembly.lean`、`drafts/Shared/Descendable.lean` と HTT・HA の項目表。
項目表・drafts・界面は編集していない。この節の型案は紙上の案で、型検査済み宣言ではない。

今回使えるようになった a は、厳密な自由代数の指定 Hopf 比較の擬同型性を供給する。
一般の代数への実現による拡張、`forget_preservesSifted`、native な Tot の比較はまだ別の入力である。
G12・M14・M15 の証明でそれらを供給済みとは数えない。

### 61.2 G12：同じ CAlg の native presentability

入口の型案は既存の欄と完全に同じ。

```lean
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories
-- 証明対象（紙の型案）
example (S : Type u) [CommRing S] :
    @IsPresentable (barrattEcclesCore.CAlg S)
      (barrattEcclesCore.quasicategory S) := by
  -- native accessibility と全小余極限を証明する
```

現在の `HTT/PresentableInfinityCategories/Definition.lean` の定義は
`IsAccessible C ∧ HasSmallColimits C`。§31 の旧名 `F2.Presentable` は使わない。
宇宙 u の全図式の native 余極限と、同じ CAlg の accessibility の両方が要る。

証明の筋は、D(S) 上の誘導された自由・忘却随伴を固定し、実際の BE 代数と
そのモナドの代数の全準圏比較を作り、accessible なモナドの代数の presentability を適用するもの。
`derivedInfinityCategory_isPresentable`、`Operad.freeAlgebraAdjunction`、
`Algebra.forget_isCardinalAccessible`、`freeAlgebra_finitelyPresentable` と
`AlgebraSiftedColimits.forget_createsSiftedColimitsOfShape` を再利用する。
`cAlgForgetDerived_conservative` と厳密な bar の分裂はモナド性の入力になる。
通常圏の filtered 保存を、局所化後の native な保存へそのまま読み替えない。

不足：誘導随伴の全単位・余単位、native な U-split 実現の比較、∞ モナド性、
accessible なモナドからの accessibility と全小余極限。
③-b の 3b-2／3b-4 が供給する一般の橋を検収してから、重複を差し引く。
HTT A.3.7.6 による模型からの直接経路は代替だが、現模型の単体的・組合せ的な仮定と
同じ native 局所化への比較の不足があるため、cofibrantly generated の事実だけでは採用しない。

地図：HA 3.2.3.5（直接の数学的対応）、HA 4.7.3.5（モナド性）、
HTT 5.5.1.1（presentability の特徴づけ）、HTT A.3.7.6（代替の模型表示）。
地図の項目名は照合したが、それらの一般定理が現在すべて証明済みだとはしない。

### 61.3 M14：同じ全自然変換としての P⁰

入口は `EInfinityTheory.powerOp0` の型を保つ。E を全欄の実例の引数とした紙の書き方では、
次の型と、その同じ α に関する四つの条件を一緒に供給する。

```lean
-- FunctorHom は Project/LocalizationAndKanExtensionAuxiliaries/FunctorCategories
(E : SerrePositivity.EInfinity.EInfinityTheory.{u})
(k : Type u) [CommRing k] (p : ℕ) [Fact p.Prime] [CharP k p] ⊢
  FunctorHom (E.forget k) (E.forget k ≫ E.restrictD (frobenius k p))
```

これは型の表示用で、E の既存の `powerOp0` を証明に使う循環にはしない。
実装では証明済み欄から固定した BE の `forget`・`restrictD` に対して α を構成し、
組み立て関数へ渡す。四条件の正確な型は `Theory.lean` の
`powerOp0_zero`・`powerOp0_pos`・`powerOp0_discrete`・`powerOp0_tot` をそのまま使う。
零次の式は `restrictD_homologyIso` と `pi0_forget` による同定の後で a ↦ a^p、
正のホモロジー次数の式は **H⁻ⁿ（n > 0）で零**。
離散と Tot は、同じ α の成分が指定 Frobenius の射に等しいという条件である。

証明の筋：BE の p 入力の係数解像度と作用から Frobenius 半線形な操作を構成し、
微分・符号・対称性を照合する。次に弱同値による局所化を通して coherent な全自然変換へ降ろし、
その変換の値を零次・負のコホモロジー次数・離散入力・Tot の順で計算する。
既存の `arityRepresentationChain`、BE の作用、係数制限の全関手とホモロジー比較を再利用する。
a の二色比較は指定射の管理に使えるが、p 入力の操作そのものの代用にはならない。

不足：p 入力の操作と微分の照合、半線形性、局所化での全自然性、四条件の同一変換での証明。
Tot の条件は G10 と係数制限との比較を待つ。
直接の出典の対応は §31 と同じ DAG XIII Construction 2.2.6・Remark 2.2.7。
HTT・HA の項目表にはこの操作の独立番号はなく、周辺の HA 3.1.3・3.2.3.1・4.7.3.5 の
完成を M14 の証明とは数えない。論文の再照合は実装前の紙の確認に含める。

### 61.4 M15：一般の E∞ 底を保った descendability

入口の型は drafts の既存 API と同じ二つを採用する。

```lean
(E : SerrePositivity.EInfinity.EInfinityTheory.{u})
(A : Type u) [CommRing A]
(R B : (E.CAlg A) _⦋0⦌) (f : SSet.Edge R B) ⊢ Prop
-- IsDescendableOver (E := E) A R B f

(E : SerrePositivity.EInfinity.EInfinityTheory.{u})
(A : Type u) [CommRing A]
(R B : (E.CAlg A) _⦋0⦌) (f : SSet.Edge R B) (n : ℕ) ⊢ Prop
-- HasDescentIndexLEOver (E := E) A R B f n
```

第一の定義は Mod_R(D(A)) で B の生成する thick ⊗-ideal が単位 R を含むこと。
第二は F := fib(f) として、指定された F^{⊗_R n} → R がその加群圏のホモトピー圏で零であること。
この指数の零射の条件は定義自体の数学的条件で、a の厳密な指定射の照合の弱化とは別である。

最初に閉じる定理の型案：

```lean
-- パラメータ E A R B f は上と同じ
IsDescendableOver (E := E) A R B f ↔
  ∃ n, HasDescentIndexLEOver (E := E) A R B f n
```

証明の筋と順序：

1. 一般の BE 代数 R の加群準圏を作り、安定性・相対テンソル・単位・底変換を構成する。
2. thick ⊗-ideal の生成と指数の有限性の同値を証明する。
   押し出しでの安定性は drafts の `isDescendableOver_pushout` と同じ型で供給する。
3. 指数の nilpotence から Amitsur の塔と Tot 降下を導き、
   `isDescendableOver_tot_equiv` の `AmitsurData` の同じ増大錐を扱う。
4. RHom の指数 ≤ 2、Frobenius 余極限の指数評価、完備版を一般の底のまま供給する。

不足は一般の R-加群の模型と native な比較、相対テンソルの全構造、
有限指数と厚い閉包の同値、Amitsur の塔の収束、完備化との整合。
通常の内部加群の余極限・balanced tensor と `StableVertexClosure` の retract・安定閉包は
再利用候補だが、全体を離散 A 上の D(A) に落として済ませない。
RHom と完備版にある `True := by trivial` は証明済み項目には数えず、
それぞれ一般 R 上の加群・指定射・完備化のデータを入れた主張へ置き換える設計を先に確定する。
M15 を `EInfinityTheory` の新しい欄として増やさない。

地図：HA 4.2.1.15、4.2.3.5・4.2.3.7、4.5.1.1・4.5.2.1・4.5.3.1 は
加群と相対テンソルの基盤。直接の descendability は Mathew Definition 3.18・Proposition 3.22、
指数の利用は BS17 §11.2・Lemma 11.22 に対応する（§31 の出典確認を引き継ぐ）。

### 61.5 規模・分担と停止点

③-b の橋と BE への適用の分担が未確定なので、一般部分と実例を含む幅を保つ。
以下は追加 Lean（空行・docstring 込み）の初期見込みで、証明済み行数ではない。

| 作業 | 内訳 | 見込み | 段 0 上端の二倍による停止基準 |
| --- | --- | ---: | ---: |
| G12 | 一般のモナド性・presentability 2,400〜4,000、BE 適用 600〜1,000 | 3,000〜5,000 | 10,000 |
| M14 | 操作と値 1,600〜2,800、局所化 600〜1,000、離散・Tot 600〜1,200 | 2,800〜5,000 | 10,000 |
| M15 | 一般 R-加群 2,500〜4,500、指数 900〜1,500、降下・評価・完備版 1,400〜2,500 | 4,800〜8,500 | 17,000 |
| **合計** | | **10,600〜18,500** | 各作業で判断 |

各作業の見込みの半分に達した段階で、止まらず実測と残りの見込みを報告する。
一般部分が他レーンから供給された場合は、適用の費用と重複しないよう再集計する。
G12 の最初の分担判断はモナド性と presentability の一般部分の担当、
M14 は p 入力の鎖レベル構成の経路の紙の確認、M15 は一般 R-加群の模型と比較の担当が必要。
RHom・完備版の正確な入力型は、M15 の実装前に利用側の A5 の担当とすり合わせる。
ここで未確定の `True` を実装可能な型として承認依頼するものではない。

**④の段 0 の停止点。承認を待つ。** 今回は紙の確認と報告だけで、Lean ソースの変更は零。
したがって新しい対象ビルド・監査・登録候補はない。共有鍵・整理券も取得していない。
3b-4 の BE 模型の実現・Tot・U の比較の担当は、§22 の 3 の判断を待つ。

## 62. M14 の紙の確認：出典の構成と D(k) の欄との比較が未供給

### 62.1 読んだ一次資料と構成経路

調整役の順序 M14 → M15 → G12 に従い、実装前に以下を確認した。

- [BS 著者版](https://people.mpim-bonn.mpg.de/scholze/prisms.pdf) §8、特に Lemma 8.4、印刷 pp.63–64。
- [DAG XIII](https://www.math.ias.edu/~lurie/papers/DAG-XIII.pdf) §2.2、特に Example 2.2.5、Construction 2.2.6、Remark 2.2.7、Warning 2.2.8、印刷 pp.34–35。

DAG の経路を模式的に書く。G = C_p、
T̂_p(M) = (M^{⊗p})^{tG}、T_p はその完全加群への制限からの余極限保存延長。
T_p はスペクトル的な k–k 双加群 B を用いて B ⊗_k (−) と表される。
標数 p の指定 Tate 類から右 k 加群の射 k → B[−1] を取り、
T_p → T̂_p、Tate の境界、ホモトピー軌道から対称冪への射、代数の作用を合成する。
得られる P⁰ は CAlg_k → Sp の全自然変換である。

Remark 2.2.7 はこの同じ構成の π₀ と正のホモトピー次数での値を計算する。
BS Lemma 8.4 はその消滅と、単体的余単体的 F_p 代数の levelwise Frobenius との比較を用いる。
通常の p 重積を全次数で直接 P⁰ とする構成ではない。

### 62.2 現在の欄までに足りない比較

現在の `EInfinityTheory.powerOp0` は

```lean
FunctorHom (forget k) (forget k ≫ restrictD (frobenius k p))
```

であり、成分は D(k) の射を与える。出典の Sp 値の変換をこの型へ持ち上げる比較は、
Construction 2.2.6 の結論そのものには含まれていない。
Warning 2.2.8 の通常の k 線形性への注意は、係数制限を入れる動機にはなるが、
それだけでスペクトル的な全自然変換の Frobenius 半線形な D(k) への持ち上げを証明しない。
§31・§61 では、この二段階を十分に分けずに「半線形な鎖レベル操作」と見積もっていた。

必要な主張を数学の型として固定すると、V_k : D(k) → Sp を Eilenberg–Mac Lane の忘却とし、
U_k : CAlg_k → D(k)、φ = Frobenius として次になる。

```text
α : NatTrans(U_k, φ_* U_k)
e : NatIso(V_k ◦ φ_*, V_k)
V_k(α) followed by e = P⁰_DAG
    in the functor infinity-category Fun(CAlg_k, Sp).
```

ここで射の向きは通常の数学の合成記法。必要なのは成分のホモロジーでの式だけでなく、
同じ全変換についての比較である。V_k の Lean の実装名とこの比較を先に設けるか、
BE の鎖の模型から α を独立に構成して同じ比較を証明する必要がある。
右 k 加群の射 k → B[−1] を、Frobenius でねじった左作用とも整合する双加群の射へ
持ち上げる条件を省略できない。左右作用のホモトピー群上の一致だけを証明して代用しない。

これは「現在の欄が不可能」という結論ではない。出典を読んで確認できたのは、
欄までの追加の持ち上げ定理が未供給であること。その定理の存在・構成経路をまだ確定していない。
特に k = F_p への特殊化だけで全自然性の持ち上げまで自動的に解消するとは扱わない。

### 62.3 実装に必要な部品と現在の不足

鎖の模型で進む候補は、G の周期的な完全解像度、ノルムと Tate 境界、
p 入力の BE 作用との比較、完全入力から全入力への延長、上記の持ち上げの順である。
既存の BE の対称群の射影解像度と作用は再利用できるが、
それらだけでは完全解像度・Tate 構成・指定類・双加群の左右作用を供給しない。
また T̂_p は一般の filtered 余極限を保存しないので、T_p との区別を保つ必要がある。

a で閉じた二色自由比較を p 入力の操作として流用しない。
ホモロジー群に Frobenius と零を次数ごとに指定し、それを coherent な自然変換とする実装も行わない。
実装する部品の型一覧は、上の持ち上げを鎖レベルでどう保証するかの確認後に確定する。
この不足を含めた行数を、既承認の 2,800〜5,000 行に収まると再断定する根拠はまだない。

### 62.4 判断を要する点と状態

まず、現在の D(k) 値の欄を維持したまま、§62.2 の持ち上げ定理の紙の確認を
M14 の最初の仕事として続ける方針の確認を求める。
出典が直接供給する Sp 値への変更は界面・利用側に影響するため、こちらでは行わない。
既存の界面を変更せず、持ち上げを仮定する補助構造体で欄を埋めることもしない。

今回の成果は実装前の紙の確認と、欠けていた主張の型の特定。
Lean ソースの変更・ビルド・監査・鍵の取得はなし。M15・G12・Tot の照合は未着手。
この型の判断がつくまで、M14 の構成を本体へ追加する作業は止める。

## 63. D79 候補：P⁰ の持ち上げと Sp 値への修正の比較（紙、判断待ち）

### 63.1 結論と二案の境界

提案は **案2（原典の Sp 値）を、まず k = F_p に限定して採用する**こと。
Lemma 8.4 の数学的な議論にはこれで足りる。現在の D(k) 値の欄を供給できたとは主張しない。
案1には、§62.2 の持ち上げ定理の存在を確定する課題が残る。
案2にも V と native なスペクトル圏、ホモトピー比較の実装が必要であり、界面の数行の変更だけでは済まない。
今回は比較の紙の作業だけ。界面・drafts・本体の Lean は変更しない。

出典は §62 の [BS 著者版 §8・Lemma 8.4](https://people.mpim-bonn.mpg.de/scholze/prisms.pdf) と
[DAG XIII §2.2](https://www.math.ias.edu/~lurie/papers/DAG-XIII.pdf)。
後者の Example 2.2.5 と Construction 2.2.6 の双加群・指定類による経路を基準とする。

### 63.2 V_k の供給状況と作る経路

本体で確認した範囲：

| 部品 | 読んだ所在 | 供給と限界 |
| --- | --- | --- |
| 対称スペクトル、安定局所化 | `Spectra/Stable/LocalizingMaps`・`Replacement`・`EnrichedModel`・`DerivedTensorInverse` | 安定化・局所化の材料。一般の基礎模型や presentation を引数とする宣言もある。D(k) → Sp の完成した全関手ではない |
| Ω スペクトルと写像空間 | `KST/Spectra.lean` と `KST/Spectra/` | `OmegaSpectrum`、ループ・写像・ホモトピー群の基盤。これを本件の native Sp と同定し、D(k) の全関手へ接続する工程は別 |
| 安定準圏の一般論 | `InfinityCategories/HA/StableInfinityCategories/` | suspension・loop・exact functor・三角構造。安定性だけから D(k) の Eilenberg–Mac Lane 関手の実例は得られない |
| 加群の Dold–Kan | `Kerodon/ExamplesOfInfinityCategories/DifferentialGradedCategories/DoldKanIso` | `standardDoldKanModuleIso` は dg Hom の標準模型と Mathlib Γ の同型。対象の非有界複体全体のスペクトル化とは別 |
| D(k) のホモロジー・安定性 | `Project/DerivedCategories/Homology`・`ModulePiZeroMoore`・`StableHomotopyComparison` | `derivedInfinityHomologyFunctor`、`modulePiZeroMooreEquiv`、`derivedStableHomotopyEquivalence` 等。ホモトピー圏の比較を native な V と取り違えない |

以上と `Eilenberg`・`DoldKan`・spectrum 関連の宣言検索では、
**要求された V_k と自然な π_n V_k ≅ H^{-n} の比較を一式で使える入口は確認できなかった**。
名前の検索だけを数学的な不存在の証明とはしない。

構成案：複体を加法群へ忘却し、各整数シフトの適切な connective truncation に Γ を適用する。
標準ループ比較を指定して Eilenberg–Mac Lane の Ω スペクトルを作る。
全鎖写像・パラメータ付き写像への自然性、準同型を安定同値へ送ることを示し、
現在の `derivedInfinityCategory k` の局所化を通して native V_k を得る。
必要なのは対象ごとのスペクトルだけでなく全関手、自然な整数次数の π/H 比較、
極限・幾何学的実現との比較、係数を忘れる比較である。

一般の係数制限について V_S ◦ f_* ≃ V_T を持てば、案1の e にも利用できる。
案2を F_p のみで始める場合は V_{F_p} を先に作り、全 k の係数比較は後へ送れる。
`[ModelCategory SSet]` を自由な仮定として置く宣言をそのまま適用したことにはしない。
スペクトルの模型の選択と、既存 KST の Ω スペクトルへの比較の要否を、着手前に調整役と確定する必要がある。

### 63.3 案1：Frobenius 半線形な D(k) への持ち上げ

固定する数学的な型は §62.2 と同じ。

```text
U_k : CAlg_k → D(k),  V_k : D(k) → Sp,  φ = Frob_k
α : NatTrans(U_k, φ_* U_k)
e : NatIso(V_k ◦ φ_*, V_k)
e ◦ V_k(α) = P⁰_DAG  in Fun(CAlg_k, Sp).
```

候補経路は、DAG の B に対し指定 Tate 類の右 k 加群射を、
左作用を φ でねじった双加群の射へ持ち上げ、その射を全入力とテンソルして α を作るもの。
その後 Tate 境界・BE の p 入力作用との比較を全自然変換として示す。
B の両作用のホモトピー群での照合と、双加群射の存在・coherence は分けて証明する。

現時点でその双加群の持ち上げの存在を保証する既存宣言・出典の定理は特定していない。
Warning 2.2.8 が通常の k 線形性を否定することは、Frobenius twist 後の持ち上げの
存在も不存在も決めない。k = F_p でも coherent な持ち上げが自動的にあると仮定しない。
したがって案1の総規模には、存在自体の紙の確認という未評価のリスクがある。

この持ち上げが存在し、原典の P⁰ と同一と証明できれば、Lemma 8.4 は通る。
その際の消滅の論証自体は Sp へ忘却してよく、D(k) の射としての強さを本質的には使わない。

### 63.4 案2：Sp 値の界面と A4 の必要条件

Sp を native 準圏として固定し、W_k := U_k ⋙ V_k（Lean の合成順）とする案。
型の模式図であり、未実装の Sp を既存の宣言名として扱わない。

```text
powerOp0Sp : FunctorHom W_k W_k
π_n : h Sp → AddCommGrp
π_n V_k(x) ≅ underlyingAddGroup(H^{-n}(x))   -- x と射に自然
powerOp0_zero : π_0(powerOp0Sp_X) = Frobenius  -- π_0 U と環の比較後
powerOp0_pos  : ∀ n > 0, π_n(powerOp0Sp_X) = 0
```

離散・Tot の欄は D(k) の射の等式から h Sp の射の等式へ移す。
両辺は同じ W_k で忘却し、指定 Frobenius の像と比較する。
P⁰ を環スペクトルの射や CAlg の辺として要求しない。
π₀ の環構造は U_k の π₀ の環から比較で運ぶもので、Sp の全対象に環構造を置かない。

A4 の依存の洗い出し：

| 箇所 | 現在の D(k) 依存 | Sp 案の扱い |
| --- | --- | --- |
| `Shared/EInfinityPowerOperation.powerOperationZero` | `cohomologyOnHo.map` と `restrictD_homology` により成分を読む | π_n の写像を π/H の自然同型で共役する |
| 同 `powerOperationZero_natTrans`・`primeField` | D(k) 内の半線形変換、係数制限の恒等比較 | W_{F_p} 上の自己変換。係数 twist の消去は不要 |
| 同 `powerOperationZero_component` | D(k) のホモトピー圏の射を辺に持ち上げる | Sp の成分と π/H 比較の自然性へ書き換える。D(k) の辺を選ぶ必要はない |
| 同 `eq_frobenius_discrete`・`eq_frobenius_tot` | 等式の終域が h D(k) | 指定 Frobenius の像との h Sp の等式へ変更 |
| `A4/Perfectoidization.prismaticPerfection_coconnective` | 結論は D(A) の coconnectivity。現在の証明は sorry と説明コメント | mod p の対象を CAlg_{F_p} へ制限し W_{F_p} で読む。π_n の消滅を π/H 比較で H^{-n} の消滅へ戻す |
| 同 `prismaticPerfection_h0_perfectDelta` | H⁰ 上の Frobenius、C/p ↪ H⁰(X/p) の単射 | π₀/H⁰ の環と射の比較で足りる。P⁰ 自身を D(A) の射とする必要はない |
| 同 `perfectoidization_coconnective` | d の正則性と完備性の議論 | 上の二結果から進み、P⁰ の線形な持ち上げを使わない |

したがって **数学の筋は Sp 案で通るが、現在の Shared の定義を無変更で再利用はできない**。
A4 の結論の型を変える必要はなく、共有の操作の読み方を変える必要がある。

必要な橋を明記する。mod p の対象 X を CAlg_{F_p} に移し、塔の shift の像が
P⁰ の同じ成分に一致することを、A2 の levelwise Frobenius 比較から得る。
W_{F_p} の必要な極限と幾何学的実現の保存・比較、変換と指定錐の両立を用いる。
shift が同値なら π_n(P⁰) は同型で、n > 0 では同時に零なので π_n W(X) = 0。
π/H 比較から X/p の coconnectivity、p 完備性と導来 Nakayama から X の結論へ進む。
P⁰ と shift の可換性だけでは、P⁰ の可逆性は導けない。

### 63.5 k = F_p に限定する範囲

**Lemma 8.4 と G-A4-1 には F_p で足りる。** 元の底 A/p 自体を F_p と同一視せず、
標準写像 F_p → A/p に沿う CAlg の係数制限を用いる。
Frobenius は F_p を固定するので、制限後には自己変換と shift の比較を述べられる。
H⁰ の Frobenius は、任意の F_p 代数の台の環で x ↦ x^p と主張できる。
一般の k の P⁰ を構成したとみなさず、最初の欄を p と CAlg_{ZMod p} に絞る案を推す。
一般 k の操作が必要になれば、CAlg_k → CAlg_{F_p} と V の係数忘却比較により
Sp 値の操作を移す経路を別途供給する。

### 63.6 規模の比較と判断点

以下はソースの調査からの初期見込み。全関手・自然性・同じ指定射の照合を含める。
未知の一般構成が多く、既承認の M14 2,800〜5,000 行を確定した上限として流用しない。

| 部品 | 追加 Lean の見込み |
| --- | ---: |
| native Sp の入口・既存 Ω 模型との接続の必要部分 | 1,500〜3,000 |
| V_{F_p}、π/H の全自然比較、局所化、必要な極限・実現比較 | 2,000〜4,000 |
| P⁰ の Tate・p 入力・指定類・全自然変換と次数の計算 | 3,000〜5,500 |
| 離散・Tot・実現の同じ変換の照合と Shared/A4 移行 | 1,000〜2,000 |
| **案2の F_p 最小範囲** | **7,500〜14,500** |
| 一般 k の V と係数忘却の比較（必要な場合の追加） | 700〜1,500 |
| 案1の半線形双加群の持ち上げと原典との全比較（存在が確定した場合のみの追加） | 1,500〜3,500 |

案1は共通の Sp 経路と一般 k の比較も含めて **条件付き 9,700〜19,500 行**。
持ち上げの存在を紙で確定できない限り、これは完成の保証や費用の上界ではない。
案2にはその存在問題がなく、Lemma 8.4 の所要の強さに一致するため優先する。
新しい規模は新しい作業案であり、これを自己承認の実装枠にしない。
スペクトル側を他レーンが供給する場合は該当部分を差し引き、同じ行数を二重計上しない。

判断してほしい点：案2・F_p 最小範囲の採用、native Sp の模型の選択と V の担当、
界面と Shared の移行範囲。3b-2／3b-4 の担当決定と、極限・実現比較の費用を合わせる必要がある。
**ここで紙の比較の停止点として止め、D79 の決定を待つ。**
Lean の変更・ビルド・監査・鍵の取得はなし。M15・G12 へは進まない。

## 64. D79 (i) の実装とスペクトル模型の最初の区切り（検証済み）

main の §24・D79 を取り込み、界面・組み立て関数・Shared・A4 の型を変更した。
`[CharP k p]` を保つ。全界面の `toSpectra k` とその比較はデータとして受け取り、
実例の証明は指示どおり F_p から構成する。一般 k の実例を今回供給した意味ではない。

### 64.1 使う実在の Sp と π

追加調査で `KST/Spectra/CoherentNerve.lean` の `KST.Spectra.Sp` と
`KST/LocalizingInvariants/SpectrumHomotopyFunctor.lean` の
`SpectrumHo.piFunctor : ℤ → (hoFunctor.obj Sp ⥤ CommGrpCat)` を確認した。
Sp は既存 Ω スペクトルの単体的圏の coherent nerve で、quasicategory の実例も既存。
π は任意の辺の類から BF 射の代表を回収し、代表の選択に依存しない実際のホモトピー群関手。
`CommGrpCat.toAddCommGrp` で加法記法へ送って使う。
§63 の調査ではこの native Sp と π の入口を特定しきれていなかったため、この点を訂正する。
V と自然な π/H の比較の入口は引き続き新しく作る必要がある。

当面この Ω 模型を標的に固定する。`Spectra/` の対称スペクトルとの新しい比較同値は要求せず、
両模型を同一と仮定もしない。追加の `[ModelCategory SSet]` を仮定する経路は使わない。
界面は既存の Sp のみを参照し、BE 模型の定義を参照しない。

### 64.2 新しい欄と指定射

- `toSpectra S : D(S) ⟶ KST.Spectra.Sp`。
- `toSpectra_homologyIso S i`：hV の後の実 π_{−i}（加法化）と Hⁱ の台の加法群の自然同型。
- `toSpectra_restrict f`：係数制限後に忘れた Sp と元の Sp の全関手の同型。
- `powerOp0`：`forget k ≫ toSpectra k` の coherent な自然自己変換。
- `powerOp0_zero`・`powerOp0_pos`：同じ Sp の成分への π₀ と πₙ（n > 0）の主張。
- 離散・Tot：従来の指定 Frobenius の D(k) の射を hV で送り、
  `toSpectra_restrict` で台のスペクトルへ戻した同じ射との等式。

最初の型検査で、最後の係数忘却比較を省くと右辺が V(φ_*X) に着地し、
P⁰ の自己射と終域が合わないことを確認した。この比較を明示して再検証し、対象ビルドを通した。
P⁰ の D(k) への持ち上げは要求しない。

組み立て関数には V と二つの比較を未供給引数として追加。
`drafts/Shared/BarrattEcclesTheory` も同じ引数を受ける。
Shared の操作は Sp の π を π/H の同型で共役して読み、D(k) の辺を選ばない。
A4 の coconnectivity の結論は変更せず、その証明の筋を Sp と π/H の比較に合わせた。
実現・Tot の比較を証明済みとする変更は加えていない。

### 64.3 検証の状態

対象は `Interface.Theory` と直接の importer `BarrattEccles.Theory.Assembly`。
ビルドの整理券は一枚、`--wait 3600`。新しい実例の証明はまだない。
成功・公理監査の結果を回収してから、(i) の変更をコミットして報告する。
Shared と A4 は drafts の規則どおりビルド対象に入れない。
次の (ii) は、この同じ Sp を標的とする V_{F_p} と π/H 比較の構成である。


### 64.4 先行取り込み用の検証結果

対象 `BarrattEccles.Theory.Assembly` と依存する `Interface.Theory` は
`/tmp/bsw16/d79-interface-02.log` でビルド成功（12,922 jobs）。
変更した本体二本を `/tmp/bsw16/audit-d79.lean` で監査し、
**104 宣言、標準三公理のみ**で成功。ログは `/tmp/bsw16/audit-d79.log`。
本体に sorry・追加公理はない。Fully qualified な長い行に longLine の style 警告が残る。
監査とビルドは別の鍵で行い、それぞれ終了を回収して鍵と整理券を返却した。

取り込み対象は本体二本、drafts 三本、報告書。
新規モジュールはないため、共通入口・共通監査への追加登録は不要。
Shared の二つの数学的性質（零次 Frobenius、正のホモトピー次数で零）と
離散・Tot との比較は保ち、それを読む型だけを Sp と π/H へ移した。
drafts の sorry を新しい証明として数えていない。

(i) の先行取り込みが可能な区切りまで完了。
(ii) では既存 Ω 模型の Sp を標的に、V_{F_p} とその π/H の自然比較を構成する。
一般 k の V と係数忘却の実例、P⁰ 自体と Rem 2.2.7、離散・Tot の照合は未供給。
新しい構造欄を証明済みの実例として埋めた、という報告ではない。

### 64.5 夜の取り込み点

**取り込み点：D79 (i)、`615ceab26`。** 界面と drafts の型変更は先行して取り込める。
朝の調整役の取り込みを待たず (ii) へ進む。承認が要る変更や上限の見込みに当たった場合は、
その線の Lean を止めて M15 の一般 R 加群の紙の段 0 へ移る。

## 65. D79 (ii)：同じ Γ による各段からの構成（進行中）

模型選択は §64.1 のとおり既存の Ω スペクトルの native Sp。
Γ(M[n] の非正 smart 切断) を第 n 段に取る。
この符号なら、第 n 段の π_{j+n} は H^{-j}(M) に対応する。
Γ から得た段に suspension 構造射を入れ、随伴構造射の全基点での π 同型を示す。
Γ の段を持つだけでは `OmegaSpectrum` の `sigma_mono` は自動的には得られないため、
まず `KanSequence` の Ω 条件を示し、既存 `KanSequence.cofibrantOmegaSpectrum` へ進む。
同じ置換の自然性・単体的パラメータへの整合を確認してから native 関手へ降ろす。
置換の対象ごとの存在だけで全関手を作ったことにはしない。

最初の追加モジュールは `PowerOperation/EilenbergMacLaneLevels`。
シフト・smart 切断・Γ の実関手と、同じ Γ の正規化が指定切断へ戻る自然同型を供給する。
ここでは構造射・Ω 条件・V 自体の完成を主張しない。対象ビルドは未回収。

### 65.1 各段・基点・Kan 性の最初の検証済み束

`PowerOperation/` の三本を対象ビルドと監査に通した。

| モジュール | 行数 | 供給 |
| --- | ---: | --- |
| EilenbergMacLaneLevels | 50 | 実シフト・smart 切断・Γ の全関手、同じ Dold–Kan の余単位による正規化の自然同型 |
| EilenbergMacLanePoints | 42 | 単体的加群の零基点を全次数・全射で保持する関手、台の段との一致 |
| EilenbergMacLaneKan | 39 | 単位からの dg Hom の実 Γ との同型、既存 N4 の線形充填からの Kan 性 |
| **計** | **131** | |

ビルド `/tmp/bsw16/em-levels-03.log` は成功（3,784 jobs）、新規警告なし。
監査 `/tmp/bsw16/audit-em-levels.log` は **三本・29 宣言・標準三公理のみ**。
本体に sorry・追加公理なし。終了を回収し、鍵と整理券を返却済み。
新規登録候補はこの三本（接頭辞 `SerrePositivity.EInfinity.PowerOperation.`）。
共通入口・共通監査は変更しない。

ここで止まらず、π と正規化ホモロジーの既存の一般比較を各段へ接続する。
構造射・Ω 条件・単射化の全関手性・局所化と native V はまだ未供給。

### 65.2 指定された各段の π/H と自然性

さらに四本を検証した。全て `EInfinity/PowerOperation/` 以下。

| モジュール | 行数 | 供給 |
| --- | ---: | --- |
| EilenbergMacLaneStageHomology | 54 | Γ の正規化のホモロジーの自然同型と、零基点の正次数 π/Moore 比較 |
| EilenbergMacLaneStageNaturality | 44 | 同じ各段の比較が任意の鎖写像で可換する式 |
| EilenbergMacLaneTruncation | 44 | smart 切断の H_d を H^{-d} へ、シフトした段を H^{r-d} へ戻す同型。d=0 の境界も含む |
| EilenbergMacLaneCohomotopy | 46 | 各段の π_{n+1} と H^{r-(n+1)} の群同型、n+1=j+r の場合の H^{-j} への移送 |
| **追加計** | **188** | |

最終ビルドは `/tmp/bsw16/em-stages-final.log`、監査は
`/tmp/bsw16/audit-em-stages.log`。七本計 **73 宣言・標準三公理のみ**で成功。
七本の実測は **319 行**、新規警告・sorry・追加公理なし。
構造射を仮定に加えた V の実例を作ったのではなく、実際の指定 Γ の各段について証明したもの。
零次数の段の π₀、構造射、Ω 条件、置換の全自然性、native V は未供給。
特に各段の群同型を持つことだけから、スペクトル全体の全自然比較の完成とは扱わない。

登録候補は今回の四本（接頭辞 `SerrePositivity.EInfinity.PowerOperation.`）。
§65.1 と合わせ七本。共通入口と共通監査は調整役の取り込み時の登録に委ねる。
夜の規則に従い検証済みの四本をコミットし、次の構造射の構成へ進む。

### 65.3 鎖のシフト遷移と有限単体による Γ の積

検証済みの追加三本は `EilenbergMacLaneShiftTransition`（72 行）、
`EilenbergMacLaneProbePair`（57 行）、`EilenbergMacLaneGammaPair`（56 行）。
smart 切断のシフトからの指定射・自然性・負次数の準同型性、
有限標準単体の AW 対角を用いた評価、実 Γ の二項積を供給した。
AW を大きい宇宙の Γ の台へ直接適用せず、小さい標準単体で評価している。

ビルドは `/tmp/bsw16/em-transition-04.log` と
`/tmp/bsw16/em-gamma-pair-05.log` で成功。監査
`/tmp/bsw16/audit-em-pairs.log` は十本・121 宣言・標準三公理のみ。
追加 185 行、(ii) の検証済み実測は計 504 行。新規警告・sorry・追加公理なし。
登録候補は上記三本（接頭辞 `SerrePositivity.EInfinity.PowerOperation.`）。
スペクトル構造射・Ω 条件・置換の全自然性・native V はまだ未供給。
次は Γ の零元の照合を閉じて基点付き構造射へ接続する。

### 65.4 零基点・smash・基本円・指定構造射

以下の七本を検証した（全て `EInfinity/PowerOperation/`）。

| モジュール | 行数 |
| --- | ---: |
| EilenbergMacLaneGammaZero | 67 |
| EilenbergMacLaneGammaPairNaturality | 48 |
| EilenbergMacLaneGammaAxes | 59 |
| EilenbergMacLaneGammaSmash | 72 |
| EilenbergMacLaneGammaSmashNaturality | 55 |
| EilenbergMacLaneCircle | 63 |
| EilenbergMacLaneSuspension | 46 |

追加計 **410 行**、(ii) の検証済み実測は **914 行**。
`gammaProbeEquiv_zero` と逆方向の照合、二項評価の両変数での自然性、
二つの零軸の零化から、既存 `ReducedPair` の普遍性で `gammaSmashPair` を作った。
基点付きの零射の大きな定義展開を避け、既存の一般補題を使っている。

基本円は固定した単位複体の第 1 段の π₁ で、指定 π/H 比較の逆像として定めた。
代表を選ぶのはこの固定対象だけで、複体変数ごとの選択はしない。
`unitCircle_class` と `unitCircle_homology` により、同じ類の計算を検証済み。
`gammaSuspension`・`levelSigma` は、この円・実 Γ の smash 積・左シフト同型を
合成した実際の構造射である。Ω 条件を新たな仮定として加えてはいない。
構造射の自然性の最終照合、Ω 条件、置換の全自然性と native V は未完。

最終ビルド `/tmp/bsw16/em-suspension-03.log` は成功（4,213 jobs）。
監査 `/tmp/bsw16/audit-em-suspension.log` は **17 本・201 宣言・標準三公理のみ**。
新規警告・sorry・追加公理なし。監査の終了と鍵の返却も回収済み。
登録候補は表の七本（接頭辞 `SerrePositivity.EInfinity.PowerOperation.`）。
共通入口と共通監査は触らない。夜の規則に従い、報告後も自然性・Ω 条件の照合を続ける。

### 65.5 実 Kan 列の全関手と、零次数・全基点の比較

| 追加モジュール（`PowerOperation/`） | 行数 |
| --- | ---: |
| EilenbergMacLaneComponents | 53 |
| EilenbergMacLaneSuspensionNaturality | 53 |
| EilenbergMacLaneSequence | 64 |
| EilenbergMacLaneGammaWeakEquivalence | 62 |

追加 **232 行**、(ii) の検証済み実測は **1146 行**。
`levelPiZeroHomologyEquiv`・`levelPiZeroCohomologyEquiv` は各段の π₀ と H^r の比較。
`gammaSuspension_naturality`・`levelSigma_naturality` は任意の複体射について厳密な可換式。
これにより `eilenbergMacLaneSequenceFunctor` を実際の Kan 列の全関手として得た。
ここでは Ω 条件を入力した Ω スペクトルを実例と呼んでいない。

`gammaMap_kanPiIsomorphism_iff` は、同じ Γ の台の全基点・零次数を含む π 同型と、
指定 smart 切断射の準同型性の同値。既存の Moore 判定と実余単位の
`Arrow.isoMk` を使い、未供給の仮定や `[ModelCategory SSet]` を加えていない。

ビルド `/tmp/bsw16/em-sequence-03.log` で列の全関手が成功。
弱同値判定の修正後の最終ビルドは `/tmp/bsw16/em-gamma-weak-01.log` で成功。
監査 `/tmp/bsw16/audit-em-sequence.log` は **21 本・228 宣言・標準三公理のみ**。
最終の四本に警告・sorry・追加公理なし。終了を回収し、鍵を返却済み。
登録候補は表の四本（接頭辞 `SerrePositivity.EInfinity.PowerOperation.`）。

残りは、指定 suspension 射の Ω 条件（π/H のシフトとの照合）、
逐次単射置換の全自然性、native Sp への全関手とその π/H の全自然比較。
対象ごとの群同型や列の通常の全関手だけから native V の完成とは扱わない。
この区切りの後も、夜の規則に従い (ii) の実装を続ける。

### 65.6 逐次単射置換の全関手性と準同型の保存

| 追加モジュール（`PowerOperation/`） | 行数 | 用途 |
| --- | ---: | --- |
| PointedFactorizationFunctor | 65 | ［一般∞］移動候補 |
| KanSequenceReplacementMaps | 91 | ［一般∞］移動候補 |
| KanSequenceReplacementFunctor | 99 | ［一般∞］移動候補 |
| EilenbergMacLaneQuasiIso | 47 | Γ の各段の準同型保存 |

追加 **302 行**、(ii) の検証済み実測は **1448 行**。
既存 `PointedFactorization.factorization` の実 SOA を変更せず、
正方形の中間対象への作用と左右因子の自然性を公開した。
既存の `KanSequence.replacementStage` と同じ段を帰納的に使い、
厳密な列の射への作用、恒等射・合成の保存、元の列への比較自然変換を証明。
`kanSequenceReplacementMap_piIsomorphism` は同じ比較自然変換の可換式から
段ごとの全基点 π 同型を移す。Ω 条件をまだ示していない対象を Sp と呼んでいない。

`smartTruncationMap_quasiIso` は零次数の境界を含む実 smart 切断の準同型保存。
`truncLEIso_inv_naturality` と `quasiIso_extendMap_iff` により、同じ切断射を運ぶ。
これを Γ の弱同値判定に接続し、元の準同型を各段の全基点 π 同型へ送った。

最終ビルド `/tmp/bsw16/em-replacement-quasi-01.log` は成功（4,764 jobs）、新規警告なし。
監査 `/tmp/bsw16/audit-em-replacement.log` は **25 本・268 宣言・標準三公理のみ**。
sorry・追加公理なし。終了・鍵返却を回収済み。登録候補は表の四本
（接頭辞 `SerrePositivity.EInfinity.PowerOperation.`）。
一般補助三本は EInfinity 下に置き、将来の場所は調整役に委ねる。
残りは指定 suspension 射の Ω 条件、その出力の native V と π/H の全自然比較。
夜の規則に従い、ここでも承認を待たずに (ii) を続ける。

### 65.7 Γ の加法・指定単位と、Ω 列からの native 図式

| 追加モジュール（`PowerOperation/`） | 行数 |
| --- | ---: |
| EilenbergMacLaneGammaAdditivity | 71 |
| EilenbergMacLaneGammaBilinearity | 77 |
| EilenbergMacLaneGammaUnit | 67 |
| EilenbergMacLaneGammaUnitPoint | 48 |
| OmegaSequenceReplacementFunctor | 59 |
| OmegaSequenceNative | 41 |

追加 **363 行**、(ii) の検証済み実測は **1811 行**。
Γ の標準単体評価とその逆の加法性、指定 AW 積の両変数での加法性を示した。
`gammaUnitSimplex` は AW 余単位の実随伴像。`gammaUnitPoint` で全単体に整合させ、
`gammaPair_right_unit_point` は元の指定右単位子そのものを得る等式である。
この点は零基点とは区別される。

最後の二本は **［一般∞］移動候補**。Ω 列の充満部分圏に同じ逐次単射置換を制限し、
BF スペクトルへの通常の全関手を得た。`omegaSequenceNative` はその通常の nerve を
既存 `nerveToCoherent` で native Sp へ送る標準比較。頂点も同じ置換対象である。
これは一般の coherent 図式の厳密化や D(A) からの降下を済ませたという主張ではない。
Eilenberg–Mac Lane 列の Ω 条件そのものは引き続き未証明であり、V の実例は未供給。

最終ビルドは `/tmp/bsw16/em-gamma-bilinear-03.log`、
`/tmp/bsw16/em-native-unit-01.log`（native 比較の成功）、
`/tmp/bsw16/em-gamma-unitpoint-01.log`。
監査 `/tmp/bsw16/audit-em-unit.log` は **31 本・327 宣言・標準三公理のみ**。
最終六本に新規警告・sorry・追加公理なし。終了・鍵返却を回収済み。
登録候補は表の六本（接頭辞 `SerrePositivity.EInfinity.PowerOperation.`）。
次は指定単位の零次数の係数と、基本円を使う Ω 比較の照合を続ける。

## 66. 夜の代わりの作業：M15 の一般 R 加群の段 0（紙のみ）

### 66.1 必要な一般性と型の案

`Shared/Descendable.lean` の一般形では、R は `(E.CAlg A)` の任意の頂点。
R を離散環 A の像に制限した D(A) の thick ideal で代用しない。
以下は **新しい名前の型案**であり、現存する宣言・検証済みコードではない。
`EInfinityTheory` に M15 の欄を加える提案でもない。

```lean
-- E : EInfinityTheory.{u}, A : Type u, [CommRing A]
-- R B : (E.CAlg A) _⦋0⦌, f : SSet.Edge R B
modulesOver (E : EInfinityTheory.{u}) (A : Type u) [CommRing A]
  (R : (E.CAlg A) _⦋0⦌) : SSet.{u+1}
modulesOverForget (R : (E.CAlg A) _⦋0⦌) :
  modulesOver E A R ⟶ derivedInfinityCategory A
moduleUnit (R : (E.CAlg A) _⦋0⦌) : (modulesOver E A R) _⦋0⦌
algebraAsModule (f : SSet.Edge R B) : (modulesOver E A R) _⦋0⦌
moduleTensorWith (R : (E.CAlg A) _⦋0⦌) (M : (modulesOver E A R) _⦋0⦌) :
  modulesOver E A R ⟶ modulesOver E A R
moduleRestrict (f : SSet.Edge R B) : modulesOver E A B ⟶ modulesOver E A R
moduleExtend (f : SSet.Edge R B) : modulesOver E A R ⟶ modulesOver E A B
```

単位加群から `algebraAsModule f` への指定辺が必要であり、台は `E.forget A` が送る f。
f の fiber は **modulesOver E A R の中で**取る。
指数 n の射は、その fiber の n 重相対テンソルから同じ単位加群への指定射。
`HasDescentIndexLEOver` はその射のホモトピー圏での零性、
`IsDescendableOver` は `algebraAsModule f` の生成する thick ⊗-ideal が同じ単位を含むこと。
両者を先に同値と定義してしまわず、同値は drafts の定理として証明する。

### 66.2 再利用できる宣言と、まだ比較が要る境界

- `DifferentialGraded.LeftModule`・`LeftModuleCategory`・`leftModuleEvaluationDG`・
  `leftModuleEvaluation` は dg 圏上の左加群の実構成。
  `DifferentialGraded.Module.Left.CategoryComparison` の `ringModuleEquivalence` は
  **定数一対象 dg 圏**での比較。一般の E∞ 頂点 R の加群圏の供給とは別。
- `CategoryTheory/Monoidal/Mod/BalancedTensor` の `BalancedTensor.obj`・`projection`・
  `desc`・`moduleBifunctor` は通常の内部加群と実 coequalizer の部品。
  元の環の単なる H⁰、または hD(A) の中の通常の代数対象へ移して終わりにはできない。
  derived relative tensor は適切な置換・bar の実現・native な比較を要する。
- 安定閉包には `StableInfinityCategories/StableVertexExtension`・
  `StableHoGeneration`・`CofiberLocalizingComposition` の既存の閉包の部品を再利用できる。
  これらだけでは相対テンソルでの閉性も、R 加群の台との比較も供給されない。
- 一般の R に関する restriction/extension は、辺の合成、指定された底変換四角形、
  単位・相対テンソルまでの比較が必要。対象ごとに R の厳密模型を選ぶだけでは
  `isDescendableOver_pushout`・`isDescendableOver_tensorMaps` の全自然な主張を閉じない。

BE の厳密代数の模型を使う場合でも、単なる通常の可換 dg 環と同一視してはならない。
BE 代数の可換性は高次の整合を含む。通常の `CommMon` の balanced tensor を
無条件にそのまま適用する経路は、必要な仮定が供給されていない。
BE の実例の内部で module の模型と比較を証明し、BS の利用側は模型の中身を参照しない形が必要。

### 66.3 証明の順序と、供給する比較

1. 一般 R の native な module 準圏、その単位と台の忘却を構成する。
   厳密模型を使う場合は、置換と同値な R に対する module 圏の同値まで含める。
2. 相対テンソル・restriction/extension の随伴、単位・結合性・対称性、
   f に沿う底変換の比較を作る。一般の coherent な R への降下を対象ごとの選択で省かない。
3. 安定性と tensor の有限余極限保存を示し、生成する thick ideal と
   fiber の指数射の零性の同値に進む。ここは E∞ を直接使わない一般補題へ分けられる。
4. 既存 drafts の AmitsurData の同じ増大錐を使って Tot 降下へ進む。
   ③-b の実現・Tot の橋との比較はこの段に置き、単なる次数ごとの同型で代用しない。
5. RHom・Frobenius colimit の指数評価・完備版を一般 R のまま供給する。
   drafts の `True := by trivial` は証明済みの項目とは数えない。

HA の地図の対応は §61.4 のまま：4.2.1.15、4.2.3.5・4.2.3.7、
4.5.1.1・4.5.2.1・4.5.3.1。descendability 自体は Mathew Definition 3.18・
Proposition 3.22、指数の利用は BS17 §11.2・Lemma 11.22。
この節は地図上の対応を一般 module 圏の既証明性と読み替えていない。

### 66.4 規模と後で要る分担判断

§61.4 の **一般 R 加群 2,500〜4,500 行**を、次の内訳で追跡する。

| 束 | 見込み（行） | 必須の出力 |
| --- | ---: | --- |
| 模型・native 比較 | 800〜1,500 | R と射に関する coherent な module 圏と台 |
| 相対テンソル・底変換 | 1,000〜1,800 | 単位・結合・対称・restriction/extension の比較 |
| 安定性・利用側への接続 | 700〜1,200 | fiber・thick ideal の一般性、指定単位と指定辺 |
| **計** | **2,500〜4,500** | |

これは実測ではなく見込み。一般の coherent な module 構成を他レーンが供給する場合は
適用の費用と二重計上しない。現存の通常の module API だけで最初の束を閉じられるとは
まだ確認していないので、M15 着手時に **一般の native module 圏と相対テンソルを誰が供給するか**
を決める必要がある（調整役の既存の予告どおり）。
RHom と完備版の正確な入力は A5 の利用側とすり合わせる。
新しい interface 欄、drafts の型変更、M15 の Lean 実装には着手していない。
この紙の作業にビルド・監査・新しい整理券は使っていない。M14 の (ii) は続行中。

## 67. D79(ii) 続行：指定基本円の照合と Γ の fiber 比較の前段

| 追加モジュール（`PowerOperation/`） | 行数 |
| --- | ---: |
| EilenbergMacLaneAdjointSuspension | 59 |
| EilenbergMacLaneSmashUnit | 70 |
| EilenbergMacLaneSuspensionUnit | 64 |
| EilenbergMacLaneUnitCoefficient | 36 |
| EilenbergMacLaneVertexUnit | 70 |
| PointedSmashUnitSeed | 31 |
| EilenbergMacLaneStandardHom | 46 |
| EilenbergMacLaneFibration | 59 |
| EilenbergMacLaneFiniteLimits | 57 |

追加 **492 行**。コメント警告の修正一行を含め、
(ii) の検証済み実測は **2304 行**。

### 67.1 指定射と零次数の照合

`gammaSmashPair_right_unit` は、基点付きの smash の積でも指定 AW 単位が
元の右単位子そのものを与える厳密な等式。
`gammaSuspension_on_unit` は、単位上の構造射の値を固定した `unitCircle` と
`unitShiftAutomorphism` の合成として元の圏で照合する。
二つの単位比較の差を、恒等射と仮定せず実際の自己同型として保持した。
`gammaAdjointSuspension` は随伴構造射の全複体上の自然変換。
単位の点の像も同じ随伴で厳密に照合した。

`gammaUnitSimplex_zero_coefficient` は実 DK 余単位と実切断包含の下で係数が一である計算。
`gammaVertexUnitHomEquiv` と `gammaUnit_vertex_generates` は **任意の Γ の頂点**を
指定単位の頂点からの複体射の像として厳密に回収する。
ここでも頂点ごとの新しい持ち上げの選択やホモトピー圏への弱化を使っていない。

### 67.2 Ω 条件への fiber 比較で再利用できた一般部分

`gammaStandardHomFunctorIso` は、元の正規化標準単体の Hom の全関手と
同じ Γ の全自然同型。`gammaMap_fibration` は既存の
`normalizedSimplex_reedyCofibrant` と `HomotopyFunctionComplex.cosimplicialHom_fibration`
から実射影 fibration を Γ の Kan fibration へ移す。
使うモデル構造は構成済みの `projectiveModelCategory A` だけで、
`[ModelCategory SSet]` の仮定は加えていない。

`extendSmartTruncationAdjunction` は既存の実 Hom 同値を自然性ごと随伴へ束ねたもの。
`gammaFunctor_preservesFiniteLimits` は smart 切断・実 Γ・加群の台の各因子から有限極限保存を示す。
これにより cone の strict fiber を同じ Γ の strict fiber へ移す経路を使える。
実際の指定随伴構造射がその loop 比較で π 同型になる証明は、まだ完了していない。

### 67.3 検証と登録候補

最終対象ビルドは `/tmp/bsw16/em-smash-unit-02.log`、
`em-suspension-unit-03.log`、`em-unit-coefficient-01.log`、`em-vertex-unit-02.log`、
`em-fibration-limits-02.log`（fibration と随伴の成功）、`em-finite-limits-05.log`。
監査 `/tmp/bsw16/audit-em-cone-prelim.log` は **40 本・397 宣言・標準三公理のみ**。
本体に sorry・追加公理なし。
`EilenbergMacLaneSuspensionNaturality` の heartbeat の理由をコメントに追加し、
その linter 警告も解消した。既存の公開宣言の型・証明の変更はない。

登録候補は表の九本（接頭辞 `SerrePositivity.EInfinity.PowerOperation.`）。
`PointedSmashUnitSeed` は **［一般∞］移動候補**として EInfinity 下に置いた。
共通入口・共通監査は変更していない。監査終了と鍵返却を回収済み。
この区切りでも止まらず、Γ の cone の比較から Ω 条件へ進む。


## 68. D79(ii)：cone の strict fiber と loop 側の保存性

追加五本は `EilenbergMacLaneConeFibration`（62 行）、
`EilenbergMacLaneConePullback`（57 行）、`EilenbergMacLanePointedLimits`（46 行）、
`EilenbergMacLaneLoopProperties`（64 行）、`ShortExactPullbackZero`（35 行）。
計 **264 行**、(ii) の検証済み累計 **2568 行**。
登録候補はこの五本（接頭辞 `SerrePositivity.EInfinity.PowerOperation.`）。
`ShortExactPullbackZero` は **［一般∞］移動候補**。

`coneProjection_projectiveFibration` は実際の cone の第三射について既存の次数付き
section を使う。`gammaCone_isPullback` は回転 cone の短完全列を、同じ四射の
Γ の引き戻しへ移す。`gammaIdentityCone_zero_piIsomorphism` は恒等射の cone から
零複体への指定零射の全基点 π 同型。Γ と loop Γ の有限極限・零射の保存、
loop Γ の実射影 fibration と準同型の保存も証明した。
指定構造射の Ω 条件と native な V の降下は引き続き未完了。

対象ビルド `em-cone-pullback-02.log`、`em-cone-pullback-04.log`、
`em-loop-properties-02.log` は成功（最終版で警告なし）。
監査 `/tmp/bsw16/audit-em-cone-properties.log` は **45 本・420 宣言・標準三公理のみ**。
sorry・追加公理なし。共有入口・共有監査は未変更、鍵返却を回収済み。
夜の規則に従い、報告後も持ち上げ性と接続写像の比較へ続行する。


## 69. D79(ii)：指定構造射の Ω 条件の次数移動

| 追加モジュール（`PowerOperation/`） | 行数 |
| --- | ---: |
| ConeFiberHomotopyComparison | 58 |
| ContractibleTotalConnecting | 46 |
| EilenbergMacLaneConeContractibility | 48 |
| EilenbergMacLaneLoopTrivialFibration | 48 |
| EilenbergMacLaneOmegaDimensionShift | 50 |
| EilenbergMacLanePointedConeFiber | 57 |
| EilenbergMacLaneTrivialFibration | 70 |
| PointedConnectingComparison | 42 |
| PointedContractibleConnecting | 81 |
| PointedHomotopyIso | 34 |
| TerminalKanHomotopy | 48 |

追加 **582 行**、(ii) の検証済み累計 **3150 行**。
表の十一本が登録候補（接頭辞 `SerrePositivity.EInfinity.PowerOperation.`）。
`ContractibleTotalConnecting`、`PointedConnectingComparison`、
`PointedContractibleConnecting`、`PointedHomotopyIso`、`TerminalKanHomotopy` は
**［一般∞］移動候補**。

### 69.1 実際に閉じた主張

`gammaMap_monomorphisms_rlp` は実射影 trivial fibration を同じ Γ の
全単射 RLP へ移す。正規化標準単体の Reedy cofibration を使い、SSet の
モデル構造は仮定しない。loop Γ にも同じ持ち上げ性を移した。
恒等 cone の Γ・loop Γ の全基点・全次数のホモトピー類は一元であり、
終対象射に全境界の充填がある。

`pointedConeFiberIso` は元の回転 cone の kernel と指定点付き fiber の厳密な同型。
その二つの脚と自然変換に対する自然性も元の圏で照合した。
零次数を含む接続同値と自然性を既存の接続写像そのもので束ね、
`gammaAdjointSuspension_bijective_iff_shift` を証明した：指定構造射の M における
π_n の全単射性と、M[1] における π_{n+1} の全単射性が同値になる。

これは **Ω 条件の完成ではない**。全複体での零次数の比較と任意の基点への移送、
その後の native な V の降下・自然な π/H 比較が残る。
(i) の界面の型は変更していない。

### 69.2 検証

対象ビルド `em-pointed-cone-fiber-02.log`、`em-cone-contractible-02.log`、
`em-loop-trivial-fibration-01.log`、`em-pointed-connecting-03.log`、
`em-omega-dimension-shift-01.log` は成功（最終版に警告なし）。
監査 `/tmp/bsw16/audit-em-omega-dimension.log` は **56 本・463 宣言・標準三公理のみ**。
sorry・追加公理なし。鍵返却を回収済み。共有入口・共有監査は未変更。
夜の規則どおり止まらず、零次数への帰着と指定基本円の比較を続ける。


## 70. D79(ii)：標準基点の全次数を零次数へ帰着

`PointedNaturalIsoDetection`（40 行、**［一般∞］移動候補**）と
`EilenbergMacLaneOmegaZeroReduction`（39 行）を追加。
(ii) の検証済み累計 **3229 行**。登録候補はこの二本
（接頭辞 `SerrePositivity.EInfinity.PowerOperation.`）。

`gammaAdjointSuspension_bijective_of_zero` は、全複体での零次数の全単射性を入力に取り、
同じ指定構造射の標準基点での全次数の全単射性を与える。
前節の恒等 cone の次数移動と実際の M[-1][1] ≅ M の同型を用いる。
零次数の全単射性を公理として追加したものではなく、未完了の主張を明示した帰着。
任意の基点での Ω 条件、native な V、安定 π/H 比較はまだ未完了。

対象ビルド `/tmp/bsw16/em-omega-zero-reduction-01.log` は成功、警告なし。
監査 `/tmp/bsw16/audit-em-omega-zero.log` は **58 本・465 宣言・標準三公理のみ**。
sorry・追加公理なし。鍵返却を回収済み。引き続き零次数の指定 π/H 比較を進める。


## 71. D79(ii)：元の Γ の自然な π/H 比較と指定頂点

| 追加モジュール（`PowerOperation/`） | 行数 |
| --- | ---: |
| EilenbergMacLaneGammaCohomotopy | 82 |
| EilenbergMacLaneGammaComponents | 79 |
| EilenbergMacLaneNaturalVertex | 63 |
| EilenbergMacLaneTruncationNaturality | 54 |

追加 **278 行**、(ii) の検証済み累計 **3507 行**。
登録候補は表の四本（接頭辞 `SerrePositivity.EInfinity.PowerOperation.`）。

`smartTruncationHomologyIso_naturality` は指定延長同型と smart 切断包含の自然性。
`gammaPiZeroCohomologyEquiv` と `gammaPiCohomologyEquiv` はシフト零を挟まず、
元の Γ の零・正次数を同じ正規化余単位で元の H へ戻し、全複体射で自然になる。
`gammaAdjointSuspension_vertex_value` は、指定構造射の任意の頂点での値を、
指定単位の頂点からの複体射の像として **元の圏で厳密に**回収する。
同じ原理で、単位の頂点の値が等しい二つの自然変換の連結成分の写像が一致する。

これで Ω 条件の零次数の計算に使う自然性が揃った。
零次数で実際に全単射になるという主張、全基点への移送、native な V の降下、
安定 π/H の自然同型は未完了。型や範囲の変更の判断は新たに発生していない。

対象ビルド `/tmp/bsw16/em-gamma-cohomotopy-03.log` は成功、警告なし。
監査 `/tmp/bsw16/audit-em-gamma-comparison.log` は **62 本・504 宣言・標準三公理のみ**。
sorry・追加公理なし。共有入口・共有監査は未変更、鍵返却を回収済み。
夜の規則どおり、実 π₀/Moore 比較の代表元の計算へ続行する。


## 72. D79(ii)：零単体の実ホモロジー類の計算

追加三本は `MooreZeroRepresentative`、`ChainZeroClassNaturality`、
`EilenbergMacLaneGammaZeroRepresentative`（接頭辞
`SerrePositivity.EInfinity.PowerOperation.`、いずれも登録候補）。
計 **132 行**、(ii) の検証済み累計 **3639 行**。
前二本は **［一般∞］移動候補**。

`modulePiZeroMooreEquiv_mk` は、元の π₀/Moore 比較が代表頂点を
同じ実 opcycles 射で写すことの等式。
`mooreDegreeZeroIso_eq` は二つの既存の零次数同型が同じ正規化包含からなることの照合。
`gammaPiZeroTruncationEquiv_mk` はこれを指定 Dold–Kan 余単位で写し、
元の Γ の頂点の像を指定 smart 切断の零次ホモロジー類として計算する。
元の複体へ戻す比較と単位の類の計算は続行中。

対象ビルド `/tmp/bsw16/em-gamma-zero-representative-03.log` は成功、警告なし。
監査 `/tmp/bsw16/audit-em-gamma-representative.log` は **65 本・513 宣言・標準三公理のみ**。
sorry・追加公理なし。共有入口・共有監査は未変更、鍵返却を回収済み。
夜の規則どおり次の代表元の比較へ進む。


## 73. D79(ii)：指定単位・loop の頂点と零次の自然写像

| 追加モジュール（`PowerOperation/`） | 行数 |
| --- | ---: |
| CochainZeroCycleClass | 43 |
| EilenbergMacLaneGammaUnitClass | 72 |
| EilenbergMacLaneLoopComponents | 62 |
| EilenbergMacLaneSmartZeroCycle | 61 |
| EilenbergMacLaneUnitLoopVertex | 67 |
| EilenbergMacLaneVertexClass | 37 |
| UnitPrecompositionHomology | 77 |
| EilenbergMacLaneZeroCohomologyMap | 76 |

追加 **495 行**、(ii) の検証済み累計 **4134 行**。
登録候補は表の八本（接頭辞 `SerrePositivity.EInfinity.PowerOperation.`）。
`CochainZeroCycleClass` は **［一般∞］移動候補**。

`gammaPiZeroCohomologyEquiv_unit` は同じ π₀/H⁰ 比較が指定 AW 単位を
元の単位類へ写す等式。`gammaPiZeroCohomologyEquiv_mk` は任意の Γ の頂点の像を、
実随伴で回収した指定複体射の元の H⁰ の類として計算する。
`gammaAdjointSuspension_unit_vertex` は単位での構造射の頂点を固定した基本円と
指定自己同型による loop の頂点と **元の圏で厳密に**照合する。
既存の零 loop 比較の下では、その円の基本群の類の逆元になることも照合した。
逆元の向きを消したり、基本円を選び直したりしていない。

`gammaLoopPiZeroCohomologyEquiv` は loop Γ(M[1]) の成分を元の H⁰(M) と比較し、
全複体射に自然。`gammaSuspensionH0Map` は元の構造射を二つの比較で共役した
H⁰ 上の自然写像で、その全単射性と元の零次構造射の全単射性を同値にした。
`homologyZeroNatural_bijective_of_unit_iso` は、この自然写像の単位での値が
実単位自己同型の類なら全複体で全単射になるという検出補題。
**実際の単位自己同型の同定は続行中**で、Ω 条件や V の完成はまだ主張しない。

対象ビルド `em-smart-zero-cycle-03.log`、`em-gamma-unit-class-02.log`、
`em-unit-loop-vertex-01.log`（VertexClass と LoopComponents の成功）、
`em-unit-homology-detection-01.log`（UnitLoopVertex の最終改行版の成功）、
`em-zero-homology-map-01.log`（ZeroCohomologyMap の成功）、
`em-unit-homology-detection-02.log`（UnitPrecompositionHomology の成功）。
最終版の対象に警告なし。監査 `/tmp/bsw16/audit-em-zero-unit.log` は
**73 本・593 宣言・標準三公理のみ**。sorry・追加公理なし。
共有入口・共有監査は未変更、鍵返却を回収済み。夜の規則どおり続行。


## 74. D79(ii)：指定構造射の標準基点での全次数の全単射性

追加三本は `EilenbergMacLaneUnitDeshift`、`EilenbergMacLaneUnitVertexClass`、
`EilenbergMacLaneUnitH0Value`（接頭辞 `SerrePositivity.EInfinity.PowerOperation.`、登録候補）。
計 **221 行**、(ii) の検証済み累計 **4355 行**。

`unitDeshiftAutomorphism` はシフト関手の充満忠実性で同じ指定自己同型を
実単位の自己同型へ戻す。`signedUnitDeshiftAutomorphism` は零 loop 比較の逆元を
その実際の自己同型の負号として保持する。
`gammaSuspensionH0Map_unit` は指定 H⁰ 写像の単位での値を、この自己同型の類と厳密に同定する。
したがって `gammaAdjointSuspension_bijective_at_basepoint` が閉じた：
**同じ指定随伴構造射は、全複体・全自然数次数で標準の零基点のホモトピー類に全単射**。
単位での等式を仮定に残していない。

残りは任意の基点の Ω 条件、native な V の降下、安定 π/H の自然同型。
任意の基点への移送は、可縮な全空間を持つ cone の固定 fiber を、その各頂点を
参照点とする接続同値で比較する。底の他の連結成分の同型を仮定する循環は避ける。

対象ビルド `em-unit-deshift-02.log`、`em-unit-h0-value-01.log`（UnitVertexClass の成功）、
`em-unit-h0-value-02.log` は成功、最終版で警告なし。
監査 `/tmp/bsw16/audit-em-based-omega.log` は **76 本・627 宣言・標準三公理のみ**。
sorry・追加公理なし。共有入口・共有監査は未変更、鍵返却を回収済み。
夜の規則どおり、全基点の比較を続行する。


## 75. D79(ii)：全基点の Ω 列、実スペクトル関手、整数 π/H

| 追加モジュール（`PowerOperation/`） | 行数 |
| --- | ---: |
| ContractibleFiberComparison | 84 |
| EilenbergMacLaneOmegaAllBasepoints | 78 |
| EilenbergMacLaneOmegaSequence | 52 |
| EilenbergMacLaneSpectrumFunctor | 43 |
| EilenbergMacLaneSpectrumCohomology | 51 |

追加 **308 行**、(ii) の検証済み累計 **4663 行**。
登録候補は表の五本（接頭辞 `SerrePositivity.EInfinity.PowerOperation.`）。
`ContractibleFiberComparison` は **［一般∞］移動候補**。

`gammaAdjointSuspension_kanPiIsomorphism` が閉じた：**同じ指定随伴構造射は
全複体・全基点・零次数を含む全次数で π 同型**。
可縮な全空間を持つ固定 fiber を、その各頂点の接続同値で比較した。
底の他の連結成分の同型を入力する循環や、加法による translation の新構成は不要だった。

`eilenbergMacLaneSequence_omega` は添字の加法の同じ同型も含めて元の Kan 列を Ω 列にする。
`eilenbergMacLaneSpectrumFunctor` は全複体と厳密な鎖写像から、既存の逐次単射置換による
実 `OmegaSpectrum` への関手。準同型の像は全段で π 同型になる。
`eilenbergMacLaneSpectrumPiCohomologyEquiv` は実スペクトルの整数 π_j と元の H^{-j} の群同型。
標準計算段の同じ置換射を使い、安定 π を独自の代用品に置き換えていない。
スペクトルの模型は §65 のまま `KST.Spectra.Sp`、対称スペクトルとの同一視は仮定しない。

**未完了**：この整数比較の全鎖写像での自然性、通常の複体圏の nerve から
既存 D(A) の dg nerve への coherent な降下、その上での native π/H の関手同型。
`eilenbergMacLaneOrdinaryNative` は通常の nerve 上の図式であり、V_A 完成とは呼ばない。
界面や drafts の型の追加変更はない。

対象ビルド `em-contractible-fiber-comparison-02.log`、`em-omega-all-basepoints-01.log`、
`em-spectrum-functor-01.log`（SpectrumFunctor の成功）、`em-spectrum-cohomology-01.log`
（OmegaSequence の改行警告修正を含む）は成功。最終版に警告なし。
監査 `/tmp/bsw16/audit-em-spectrum.log` は **81 本・650 宣言・標準三公理のみ**。
sorry・追加公理なし。共有入口・共有監査は未変更、鍵返却を回収済み。
夜の規則どおり、自然性と native な降下へ続行する。


## 76. D79(ii)：native な hammock 因子化と既存 D(A) への比較

| 追加モジュール（`PowerOperation/`） | 行数 |
| --- | ---: |
| EilenbergMacLaneNativeWeak | 49 |
| ComplexHammockSource | 98 |
| EilenbergMacLaneHammockFunctor | 60 |
| ComplexHammockEssentialSurjectivity | 70 |

追加 **277 行**、(ii) の検証済み累計 **4940 行**。
登録候補は表の四本（接頭辞 `SerrePositivity.EInfinity.PowerOperation.`）。
`ComplexHammockSource`、`ComplexHammockEssentialSurjectivity` は **［一般∞］移動候補**。

### 76.1 native な側で閉じた主張

通常の複体図式から Sp への実写像は、元の準同型の辺を可逆辺へ送る。
既存の `modelHammock_isLocalization` と構成済みの実射影モデル・右 frame の族を用い、
全複体の同じ相対圏の hammock から native Sp への実関手
`eilenbergMacLaneHammockFunctor` を構成した。
元の複体図式へ戻る指定同型は点ごとの存在ではなく **全関手の `FunctorIso`**。
満たせないモデル構造の仮定や、関手の存在の追加公理はない。

同じ hammock から既存 `derivedInfinityCategory A` への実比較
`complexHammockDerivedComparison` と、その指定全関手同型も構成した。
元の半自由閉零圏上の比較を頂点へ評価し、
`complexHammockDerivedComparison_essentiallySurjective` まで閉じた。
Hom の宇宙の異なる通常 nerve の写像は元の同じ合成可能射列で作った。
既存 D(A) を別模型へ定義変更していない。

### 76.2 次の橋と現在の不足

残る主張の型は、既存界面の型を変えるものではない：

```lean
-- 未証明の次の比較。まだ本体の宣言としては置いていない。
lemma complexHammockDerivedComparison_fullyFaithful
    (A : Type u) [CommRing A] :
    IsFullyFaithful (complexHammockDerivedComparison A)
```

`normalizedOrdinaryDerivedHomMap_homotopyEquivalence` と
`normalizedTensorElementOrdinaryPinchedMap_weak`（K-projective 入力）は本体にある。
右 frame と hammock の全族比較も `FrameHom/` にある。
これらを二つの写像空間の同値の存在として並べるだけでは不十分で、
**指定比較関手とその sourceIso の下で、元の要素屋根族を運んだ射が一致すること**を
照合する必要がある。その後に本質的全射性と合わせて同じ比較を同値にし、
逆を通して既存 D(A) から Sp への V を作る。
この充満忠実性は現時点で未完了。V の完成や D79(ii) の終了は宣言しない。
整数 π/H の全鎖写像に対する自然性も続行中。

### 76.3 検証

対象ビルド `em-hammock-source-01.log`（NativeWeak の警告修正を含む成功）、
`em-hammock-functor-01.log`（ComplexHammockSource の最終版の成功）、
`em-hammock-essential-01.log`（HammockFunctor の改行版の成功）、
`em-hammock-essential-04.log` は成功。最終版に警告なし。
監査 `/tmp/bsw16/audit-em-native-hammock.log` は **85 本・695 宣言・標準三公理のみ**。
sorry・追加公理なし。共有入口・共有監査は未変更、鍵返却を回収済み。
夜の規則どおり、報告後も自然性と指定屋根族の比較へ進む。

## 77. D79(ii)：同じ置換射を通る段ごとの π/H 自然性

登録候補（接頭辞 `SerrePositivity.EInfinity.PowerOperation.`）：
`EilenbergMacLaneStageCohomologyNaturality`（66 行）、
`EilenbergMacLaneSpectrumLevelNaturality`（78 行）。追加 **144 行**、
(ii) の検証済み累計 **5084 行**。

シフトのホモロジー比較と添字の移送の自然性を、元の Γ の段の自然性へ合成した。
次に `eilenbergMacLaneSpectrumMap_projection` で、同じ実単射置換射の
厳密な可換式を証明し、任意の正次数の計算段の π/H 自然性
`eilenbergMacLaneSpectrumLevelPiCohomologyEquivAt_naturality` を閉じた。
ここでも元の鎖写像の厳密な可換式を保持している。

対象ビルド `em-stage-cohomology-naturality-02.log`、
`em-spectrum-level-naturality-04.log` は成功、最終版に警告なし。
監査 `audit-em-stage-naturality.log` は **87 本・709 宣言・標準三公理のみ**。
sorry・追加公理なし。共有入口・共有監査は未変更。
整数次数の自然性と、§76.2 の指定比較の充満忠実性は続行する。

## 78. D79(ii)：整数 π/H の自然同型と指定正規化屋根の弱同値性

| 登録候補（`SerrePositivity.EInfinity.PowerOperation.`） | 行数 |
| --- | ---: |
| EilenbergMacLaneSpectrumPiNaturality | 85 |
| EilenbergMacLaneSpectrumHomologyIso | 38 |
| ComplexNormalizedCommonFrame | 69 |
| ComplexNormalizedRoofMaps | 58 |
| ComplexNormalizedRoofWeak | 95 |

追加 **345 行**、(ii) の検証済み累計 **5429 行**。
後ろ三本は **［一般∞］移動候補**（複体模型に関する比較）。

### 78.1 整数 π/H の全鎖写像に対する比較

`eilenbergMacLaneSpectrumPiCohomologyEquiv_naturality` を閉じた。
標準計算段への次数移送の既存自然性と、§77 の同じ置換射の自然性を合成した。
`eilenbergMacLaneSpectrumPiCohomologyEquiv_apply` は、元の指定比較の順写像と
計算段の比較の厳密な等式である。局所的な略記を展開して接続することで、
不要な模型の定義展開による elaboration の時間切れを解消した。

`eilenbergMacLaneSpectrumHomologyIso A j` は、全複体の通常の圏上の
**関手全体の自然同型**
`eilenbergMacLaneSpectrumFunctor A ⋙ OmegaSpectrum.homotopyFunctor j ≅
complexMultiplicativeCohomology A j` である。
既存 D(A) 上の自然同型とはまだ区別する。

### 78.2 指定屋根の弱同値性

元の標準 frame と正規化テンソル frame の同じ共通置換を使い、左右の実射、
augmentation の厳密な三角形を明示した。
全要素圏の実比較の反転性を通して、
`complexNormalizedTensorRoof_weak` を閉じた。
これは写像空間の抽象的な同値の存在でなく、同じ全単体の屋根写像そのものの弱同値性。
`[ModelCategory SSet]` の未供給の仮定はない。

次は同じ全要素屋根を相対圏へ送り、`RoofPrefix.native_family_postcomp_column_roof_arrow`
と `NerveColumn.roof_naturality` に指定 sourceIso を代入する。
これで §76.2 の残りの指定比較の実写像空間への作用を照合する。
D(A) から Sp への V と (ii) の終了はまだ宣言しない。

### 78.3 検証

`em-spectrum-pi-naturality-08.log`、`em-pi-and-roof-03.log` の
`ComplexNormalizedRoofWeak`、`em-homology-iso-01.log` は成功。
最終版の五本に警告なし。
監査 `audit-em-pi-roof.log` は **92 本・743 宣言・標準三公理のみ**。
sorry・追加公理なし。共有入口・共有監査は未変更。夜の規則どおり続行する。

## 79. D79(ii)：同じ native な屋根族と指定比較の全パラメータ照合

| 登録候補（`SerrePositivity.EInfinity.PowerOperation.`） | 行数 |
| --- | ---: |
| ComplexRelativeElementColumn | 53 |
| ComplexRelativeElementPinchedFamily | 63 |
| ComplexRelativeElementSourceRoof | 62 |
| FullyFaithfulWeakRoofDetection | 32 |
| ComplexRelativeElementIndexComparison | 75 |
| ComplexRelativeElementRoofMaps | 107 |
| ComplexRelativeColumnHom | 62 |
| ComplexRelativeElementWeak | 58 |

追加 **512 行**、(ii) の検証済み累計 **5941 行**。
全八本が **［一般∞］移動候補**（うち七本は複体模型の比較）。

### 79.1 今回閉じた接続

全要素圏を同じ全複体の相対圏へ送り、
`complexRelativeElementHammockPinchedMap` を構成した。
`complexRelativeElementPinchedFamily_comparison_arrow` は、
**指定した** `complexHammockDerivedComparison` による同じ全族の像が、
同じ augmentation の逆と評価であることの全 Arrow の等式。
`complexRelativeElementSourceRoof_naturality` は、
**指定した sourceIso** と同じ全屋根との全関手の可換式である。

宇宙の表示変更は `complexRelativeElementIndexIso` の実同型。
`complexRelativeElementRoof_graph_image`・`complexRelativeElementRoofMap_image`
は全語の標準射・二脚・全縦射を保つ厳密な等式。
これらで §78 の同じ屋根の弱同値性を運び、
`complexRelativeElementHammockPinchedMap_weak` を閉じた。
`complexRelativeColumnHom_arrow` は元の通常複体円柱への全制限を回収する。

充満忠実性の検出は `fullyFaithful_of_weak_roof` に分離した。
必要な入力は、同じ族 p と **p ≫ pinchedHomMap F** の両方の弱同値性であり、
抽象的な写像空間の同値の存在を代用していない。
次は通常導来屋根への回収を同じ全族へつなぎ、指定比較の誘導射を検出する。
§76.2 の充満忠実性、既存 D(A) 上の V はまだ未完了。

### 79.2 検証

`em-relative-source-roof-01.log`、`em-relative-roof-maps-03.log` の
IndexComparison、`em-relative-roof-maps-04.log` の RoofMaps、
`em-relative-weak-02.log` の ColumnHom、`em-relative-weak-03.log` は成功。
最終版に警告なし。
監査 `audit-em-relative-roof.log` は **100 本・784 宣言・標準三公理のみ**。
sorry・追加公理なし。共有入口・共有監査は未変更。夜の規則どおり続行する。

## 80. D79(ii)：指定 hammock 比較の全写像空間の橋を完了

| 登録候補（`SerrePositivity.EInfinity.PowerOperation.`） | 行数 |
| --- | ---: |
| ComplexRelativeElementDerivedRoofComparison | 59 |
| NerveColumnConstantRestriction | 47 |
| NerveColumnRoofConjugation | 67 |
| ComplexRelativeElementTransport | 66 |
| ComplexRelativeElementReference | 78 |
| ComplexHammockPinchedComparison | 62 |
| ComplexHammockProbeFunctor | 60 |
| FullyFaithfulEquivalencePrecomposition | 30 |
| ComplexHammockProbeVertices | 51 |
| ComplexHammockFullyFaithful | 48 |

追加 **568 行**、(ii) の検証済み累計 **6509 行**。
全十本が **［一般∞］移動候補**（うち七本は複体模型に関する比較）。

### 80.1 §76.2 の不足を閉じた

`complexHammockDerivedComparison_fullyFaithful` を **全頂点・全写像空間**で証明した。
同じ指定 sourceIso の全屋根の自然性を、同じ頂点成分による両端の輸送へつなぎ、
`complexRelativeElementDerivedPinchedMap_reference_family` で元の通常導来屋根と
全パラメータの関手の射として照合した。その元の弱な基準族で反映し、
`complexHammockDerivedComparison_probe_pinched_weak` により
**指定比較そのものの実 pinched 誘導射**を検出した。

元の `framedLimitProbeFunctor` と同じ augmentation が hammock 上で自己同値を
誘導することも証明した。その自己同値の全頂点での値を厳密に照合し、
probe の像での検出を全頂点へ延ばした。
比較を別の関手へ取り替えたり、ホモトピー圏上の充満忠実性で代用したりしていない。

したがって、以前の本質的全射性と合わせて、同じ全複体 hammock 比較を
既存 D(A) との実同値にできる。次はその逆を通して native な V を作り、
既存 D(A) 上の π/H 自然同型へ降ろす。
(ii) の終了はその比較まで検証してから報告する。

### 80.2 検証

`em-relative-derived-roof-02.log`、`em-constant-restriction-01.log`、
`em-relative-transport-reference-02.log` の RoofConjugation、
`em-relative-transport-reference-03.log` の Transport、`em-relative-reference-04.log`、
`em-pinched-probe-01.log` の PinchedComparison、`em-hammock-probe-02.log`、
`em-hammock-fully-faithful-02.log` は成功。最終版の十本に警告なし。
監査 `audit-em-fully-faithful.log` は **110 本・821 宣言・標準三公理のみ**。
sorry・追加公理なし。共有入口・共有監査は未変更。夜の規則どおり続行する。

## 81. D79(ii)：既存 D(A) から native Sp への実 V と全 sourceIso

| 登録候補（`SerrePositivity.EInfinity.PowerOperation.`） | 行数 |
| --- | ---: |
| EilenbergMacLaneDerivedFunctor | 58 |
| ComplexRelativeNerveUp | 35 |
| EilenbergMacLaneDerivedSourceComparison | 47 |
| OrdinaryNerveHomotopyFunctor | 32 |
| OmegaSpectrumHoFunctor | 32 |
| EilenbergMacLaneNativeHomologyIso | 28 |

追加 **232 行**、(ii) の検証済み累計 **6741 行**。
ComplexRelativeNerveUp・OrdinaryNerveHomotopyFunctor・OmegaSpectrumHoFunctor は
**［一般∞］移動候補**。実 V は基礎の k に関する構成なので、将来の基盤移管の対象。

### 81.1 実 V を構成した

同じ比較を本質的全射性と合わせて `complexHammockDerivedEquivalence` にし、
その逆を通して `eilenbergMacLaneDerived : derivedInfinityCategory A ⟶ KST.Spectra.Sp`
を構成した。特に要求された V_{F_p} をこの実関手の実例として取れる。
既存 D(A) や native Sp の定義の変更、関手の存在の追加入力はない。

`eilenbergMacLaneDerived_sourceIso`・`ordinarySourceIso`・`semifreeSourceIso` は、
元の相対全複体・通常全複体・半自由閉零圏での **全関手の指定同型**。
対象ごとの同型の存在だけを結論にしていない。

`eilenbergMacLaneNativeHomologyIso` は、元の全複体の通常関手上で、
native Sp の実際の `SpectrumHo.piFunctor` と H^{-j} との全自然同型。
残るのは、半自由閉零圏上の全 sourceIso を通し、
**既存 D(A) のホモトピー圏上**で界面が要求する π/H 自然同型へ降ろす部分。
したがって (ii) 全体の終了、P⁰ の存在や計算の完了はまだ宣言しない。

### 81.2 検証

`em-derived-functor-02.log`、`em-derived-source-comparison-01.log` の SourceComparison、
`em-ordinary-nerve-ho-02.log`、`em-native-homology-01.log` の
OmegaSpectrumHoFunctor・NativeHomologyIso は成功。最終版の六本に警告なし。
監査 `audit-em-derived-functor.log` は **116 本・849 宣言・標準三公理のみ**。
sorry・追加公理なし。共有入口・共有監査は未変更。
全見込み 14,500 行の半分の 7,250 行にはまだ届いていない。夜の規則どおり続行する。


## 82. D79(ii) 完了：既存 D(A) の全ホモトピー圏上の π/H 自然同型

| 登録候補（`SerrePositivity.EInfinity.PowerOperation.`） | 行数 |
| --- | ---: |
| DGClosedHoComparison | 56 |
| DGClosedHoFull | 43 |
| NatIsoFullEssentialDescent | 37 |
| OrdinaryNerveHoNaturality | 41 |
| OmegaSpectrumNativeHoComparison | 49 |
| EilenbergMacLaneNativeDiagram | 65 |
| SemifreeClosedHoHomology | 56 |
| EilenbergMacLaneSemifreePiComparison | 58 |
| EilenbergMacLaneDerivedHomologyIso | 48 |

追加 **453 行**、(ii) の検証済み累計 **7194 行**。
DGClosedHoComparison・DGClosedHoFull・NatIsoFullEssentialDescent・
OrdinaryNerveHoNaturality・OmegaSpectrumNativeHoComparison・SemifreeClosedHoHomology は
**［一般∞］移動候補**。他の三本も V の基盤移管時の比較の対象。

### 82.1 完成した比較と範囲

`eilenbergMacLaneDerived_homologyIso A i` は、界面と同じ型

```lean
hoMap (eilenbergMacLaneDerived A) ⋙ SpectrumHo.piFunctor (-i) ⋙
  CommGrpCat.toAddCommGrp ≅ additiveCohomologyOnHo A i
```

の **全関手の自然同型**。半自由閉零圏から native D(A) のホモトピー圏への
充満・本質的全射性を証明し、同じ semifreeSourceIso 上の比較を降ろした。
通常の複体のホモロジーだけで結論を代用していない。
§81 の実 V と合わせ、要求された **V_{F_p} と π/H 比較までを完了**した。
一般 A でも同じ構成が使えるが、係数制限に関する全比較は今回の完成範囲に含めない。
P⁰ とその次数計算、離散・Tot の照合は未完了。次は (iii) の Tate 経路を進める。

### 82.2 検証

`em-derived-homology-03.log`：最終対象ビルド成功（12,561 jobs）。
追加九本の最終版に警告なし。依存の Interface/Theory に以前からある長行警告は残る。
`audit-em-derived-homology.log`：**125 本・894 宣言、標準三公理のみ**。
sorry・追加公理なし。共有入口と共有監査は未変更。
見込み上端の半分 7,250 行まであと 56 行。到達時に実測と残見込みを報告し、
夜の規則どおり停止せず (iii) を続行する。


## 83. M14 の半分の途中報告と D79(iii) の周期係数複体

見込み上端 14,500 行の半分 **7,250 行**を通過した。
(ii) 7,194 行に (iii) の最初の CyclicTateComplex 78 行を加えた時点で **7,272 行**。
停止せず、同じ周期複体の左正則表現での全次数の完全性も検証した。

| 登録候補（`SerrePositivity.EInfinity.PowerOperation.`） | 行数 |
| --- | ---: |
| CyclicTateComplex | 78 |
| CyclicTateResolution | 45 |

今回の検証済み追加 **123 行**、(ii)+(iii) の検証済み累計 **7,317 行**。

### 83.1 実測と残りの見込み

| 部品 | §63 の見込み | 現在の実測・残り |
| --- | ---: | --- |
| native Sp の入口と V の全自然比較・局所化 | 3,500〜7,000 | 完成部分 7,194 行。一般係数比較・実現保存は含めない |
| Tate・p 入力・指定類・全自然変換・次数計算 | 3,000〜5,500 | 123 行検証済み。残り暫定 4,500〜8,000 行 |
| 離散・Tot・実現との同じ変換の照合 | 1,000〜2,000 | 未着手、G10 待ち。見込みは据え置き |

現時点の合計見込みは **12,817〜17,317 行**（既検証 7,317 + 残り）。
これは native な Tate 比較を含む暫定値で、完成の保証ではない。
特に Mathlib の `TateCohomology/Basic` は離散な表現の Tate 複体であり、
非有界な p 重テンソルの spectral Tate 関手と、完全加群からの余極限保存延長を
すでに供給するものとして数えない。外枠 **29,000 行**を超える見込みには今はない。
範囲・界面の新しい判断が要る場合は、夜の規則どおり判断点を記して代替の M15 紙へ移る。

### 83.2 証明したもの

`cyclicTateComplexFunctor` は、同じノルムと作用差を交互に用いた整数全次数の
実複体の全関手。全表現射に自然で、二つの微分の合成が零であることを証明した。
群の位数と標数が一致する自明表現では **同じ指定微分そのものが零**。

`cyclicTateComplex_leftRegular_exactAt` は、生成元がある左正則表現の場合に
整数全次数で完全であることを示す。全項の射影性も証明した。
既存の `Rep.FiniteCyclicGroup.leftRegular.range_norm_eq_ker_applyAsHom_sub` と
`range_applyAsHom_sub_eq_ker_norm` を同じ微分へ適用している。
これらは P⁰ の Tate 経路の係数側の部品であり、P⁰ や native Tate 関手の完成ではない。

### 83.3 検証

`cyclic-tate-02.log`・`cyclic-tate-resolution-01.log`：対象ビルド成功、最終版に警告なし。
`audit-cyclic-tate.log`：**127 本・910 宣言、標準三公理のみ**。
sorry・追加公理なし。共有入口・共有監査は未変更。
次は自明表現での指定ホモロジー同型と、その全射に関する自然性を検証する。


## 84. D79(iii)：同じ p 巡回作用・全入力関手・係数類

| 登録候補（`SerrePositivity.EInfinity.PowerOperation.`） | 行数 |
| --- | ---: |
| CyclicTateTrivialHomology | 71 |
| TensorPowerRepresentation | 58 |
| CyclicTensorInput | 59 |
| TateCoefficientClass | 49 |

追加 **237 行**、(iii) の検証済み **360 行**、(ii)+(iii) 累計 **7,554 行**。

### 84.1 指定と全自然性

`tensorPowerRepresentationFunctor` は、元のテンソル冪の Koszul 置換作用を
任意の指定置換群を通して制限し、全複体・全鎖写像について表現の複体へ持ち上げる。
`representationCochainComplex`・`representationCochainMap` と
`tensorPower_permutation_naturality` を再利用した。
作用を忘れる指定同型も元のテンソル複体を保つ。

`PowerOperationCyclicGroup p` は宇宙をそろえた Z/p の加法群。
`powerOperationCyclicPermutation` は Fin p 上の同じ左平行移動、
`powerOperationCyclicGenerator` は同じ 1。
群の位数が p であることと、同じ 1 が全元を生成することを証明した。
`powerOperationTensorInput` が要求された p 入力の全関手となる。

`cyclicTateTrivialHomologyNatIso` は自明作用を付けた **全加群関手**についての
整数全次数のホモロジー同型。
`powerOperationTateCoefficientClass` は、同じ指定周期係数複体の H^{-1} における
1 の逆像。値が 1 であることと、非自明係数環なら非零であることを証明した。
この時点では native spectral Tate の類と同定したとは述べない。

### 84.2 検証と次

`cyclic-tate-trivial-02.log`・`tensor-power-representation-01.log`・
`tate-coefficient-class-01.log`：対象ビルド成功。新規四本の最終版に警告なし。
`audit-tate-input.log`：**131 本・970 宣言、標準三公理のみ**。
sorry・追加公理なし。共有入口・共有監査は未変更。
次は同じ完全周期解像度からの Hom 複体と、完全入力での比較を進める。
非有界入力の全次数の積による Hom を、native Tate 関手と無条件に同定しない。


## 85. D79(iii)：完全周期 Hom の指定係数比較と有界な係数の非輪状性

| 登録候補（`SerrePositivity.EInfinity.PowerOperation.`） | 行数 |
| --- | ---: |
| LinearHomComplexFunctor | 55 |
| CyclicResolutionHomComplex | 38 |
| CyclicResolutionSingleHom | 57 |
| CyclicResolutionSingleHomology | 51 |
| CyclicResolutionHomNaturality | 89 |
| BoundedAcyclicHomotopy | 63 |
| BoundedAcyclicHomComplex | 51 |

追加 **404 行**、(iii) **764 行**、(ii)+(iii) **7,958 行**。
LinearHomComplexFunctor・BoundedAcyclicHomotopy・BoundedAcyclicHomComplex は
一般の線形／アーベル圏での補助で、基盤への移動候補。

### 85.1 同じ係数類と全自然比較

指定した左正則完全周期解像度から、作用付き入力への実 `linearHomComplex` を取った。
`powerOperationTensorResolutionHom` は元の p 入力との合成の全関手。
自明な離散係数では、同じ Hom 微分そのものが整数全次数で零となる。
`cyclicResolutionSingleDegreeEquiv` は、その各次数を同じ左正則表現の評価で係数へ送る。

`cyclicResolutionDiscreteHomologyNatIso` は、この Hom の H^i と元の係数加群との
**全関手の自然同型**。`cyclicResolutionCoefficientClassIso_value` は
Hom の零次数の 1 に対応する類を、§84 の周期係数模型の負一次の指定類へ送る。
この零次／負一次の違いは、採用した解像度の周期の規約によるものとして明示した。
まだ native spectral Tate と同定したという主張ではない。

### 85.2 係数側の有界性を明示した

`homotopyZero_to_acyclic_boundedAbove` は、各項が射影的な P から、
**上に有界な**非輪状 M への全鎖写像が零にホモトピックであることを示す。
双対の帰納法は Mathlib の `isKInjective_of_injective_aux` をそのまま使い、
非輪状な始域側の零範囲から開始する形で証明した。
`linearHomComplex_acyclic_boundedAbove` は全整数次数の Hom 複体の非輪状性を与える。

周期解像度 P が非有界な係数すべてに対して K 射影的であるとは主張しない。
この補題は完全な入力を bounded 模型で扱う比較の前段であり、
一般入力の Tate と余極限保存延長 T_p を区別する。

### 85.3 検証

`cyclic-resolution-hom-01.log`・`cyclic-resolution-single-homology-01.log`・
`bounded-acyclic-homotopy-02.log`・`bounded-acyclic-hom-complex-02.log`：対象成功。
七本の最終版に新規警告なし。
`audit-cyclic-hom.log`：**138 本・1,042 宣言、標準三公理のみ**。
sorry・追加公理なし。共有入口・共有監査は未変更。
次は p 入力の混合色の巡回軌道の自由性と、完全入力の Tate 比較を進める。


## 86. D79(iii)：混合色の実巡回軌道と誘導周期係数の非輪状性

| 登録候補（`SerrePositivity.EInfinity.PowerOperation.`） | 行数 |
| --- | ---: |
| CyclicMixedOrbit | 62 |
| CyclicTensorMixedWords | 50 |
| CyclicTateTensorTrivial | 53 |
| CyclicInducedAcyclic | 51 |
| CyclicResolutionBoundedAcyclic | 29 |

追加 **245 行**、(iii) **1,009 行**、(ii)+(iii) **8,203 行**。

### 86.1 同じ p 入力との接続

`powerOperationCyclicPermutation_mixed_free` は、素数位数の同じ巡回作用について、
非定数な任意の色付けを固定する元が単位だけであることを示す。
`cyclicBinaryTensorWord_fixed` は、これを以前の二色自由比較で使った
**実際の `BinaryTensorWord` と同じ置換作用**に適用する。
軌道写像の単射性と、群から同じ軌道への指定同値も証明した。
これは DAG XIII Proposition 2.2.3 の混合層の自由性の係数側の部分。

`cyclicTateComplex_tensorTrivialIso` は自明係数の右テンソルで
ノルム・作用差の **同じ指定微分そのもの**を保つ複体同型。
`cyclicTateComplex_regularTensor_acyclic` は、平坦な自明係数を付けた左正則周期複体が
全次数で非輪状であることを示す。体上では追加入力の平坦性なしで適用できる。
`cyclicResolutionHom_acyclic_boundedAbove` は §85 の一般補題を同じ指定解像度へ適用した。

native Tate 関手、双加群、P⁰ の全自然変換の完成はまだ宣言しない。
次は上有界係数の準同型を同じ解像度の Hom が保つことを、
同じ cone の全 Hom 比較を通して証明する。

### 86.2 検証

`cyclic-mixed-orbit-02.log`・`cyclic-tensor-mixed-words-02.log`・
`cyclic-coefficient-acyclic-01.log`：対象成功。最終五本に警告なし。
`audit-cyclic-mixed.log`：**143 本・1,065 宣言、標準三公理のみ**。
sorry・追加公理なし。共有入口・共有監査は未変更。夜の規則どおり続行する。


## 87. D79(iii)：同じ周期 Hom は上有界係数の指定準同型を保つ

| 登録候補（`SerrePositivity.EInfinity.PowerOperation.`） | 行数 |
| --- | ---: |
| LinearHomConeDegrees | 46 |
| ModuleConeCoordinates | 75 |
| LinearHomConeComparison | 65 |
| BoundedQuasiIsoCone | 53 |
| BoundedLinearHomQuasiIso | 47 |

追加 **286 行**、(iii) **1,295 行**、(ii)+(iii) **8,489 行**。
前四本および最後の一般補題は、一般の線形・アーベル圏の基盤への移動候補。

### 87.1 指定射の準同型保存

`linearHomConeIso R P f` は

```lean
mappingCone (linearHomComplexPostcompose R P f) ≅
  linearHomComplex R P (mappingCone f)
```

の **実複体同型**。Mathlib の同じ `mappingCone.liftCochain`、
二射影とその直積座標、符号付き微分を照合した。
`coefficientCone_acyclic_of_quasiIso` と逆向きの反映は、
一般のアーベル圏の同じ指定 cone の三角形を通して証明した。

`linearHomComplexPostcompose_quasiIso_boundedAbove` は、P の各項の射影性と
M・N の共通の上界を明示し、**元の指定射 f による後合成そのもの**の準同型性を与える。
`cyclicResolutionHom_quasiIso_boundedAbove` が、同じ指定完全周期解像度への適用。
これで完全入力の係数模型を相対関手として native 側へ運ぶための
準同型保存まで到達した。非有界係数の場合や P⁰ の完成はまだ主張しない。

### 87.2 検証

`linear-hom-cone-degrees-03.log` の Degrees、`linear-hom-cone-comparison-03.log`、
`bounded-linear-hom-quasi-02.log`：対象成功。五本の最終版に新規警告なし。
`audit-bounded-quasi.log`：**148 本・1,103 宣言、標準三公理のみ**。
sorry・追加公理なし。共有入口・共有監査は未変更。
上有界な係数の全部分圏と同じ相対 Hom 関手へまとめる作業を続行する。


## 88. D79(iii)：同じ射影 p 入力の native スペクトル図式と全 sourceIso

| 登録候補（`SerrePositivity.EInfinity.PowerOperation.`） | 行数 |
| --- | ---: |
| BoundedCyclicCoefficients | 64 |
| BoundedCyclicSpectrum | 71 |
| TensorPowerHomotopy | 47 |
| TensorPowerUpperBound | 54 |
| TensorPowerRepresentationQuasiIso | 31 |
| BoundedProjectiveTensorInput | 71 |
| ProjectivePowerSpectrum | 65 |

追加 **403 行**、(iii) **1,698 行**、(ii)+(iii) **8,892 行**。
TensorPowerHomotopy・TensorPowerUpperBound の一般補題は基盤への移動候補。
相対図式の各部品も、Tate の実構成が固まった後に配置を検討できる。

### 88.1 到達した実関手

`boundedCyclicHomLocalizer` は、上有界な作用付き係数の元の準同型を保つ
**同じ完全周期 Hom の実相対関手**。
`boundedCyclicSpectrum` は、その hammock から native Sp への実関手であり、
同じ厳密な係数図式へ戻る全 `boundedCyclicSpectrum_sourceIso` を持つ。
上界は対象ごとに選べ、二対象の間の証明で共通の上界を取った。

`tensorPowerMap_quasiIso_of_KProjective` は、指定射を保つホモトピー同値の
同じテンソル冪を使って証明した。作用付き入力の準同型性は正確な忘却で反映した。
上界 n a も同じ符号付き入力に適用している。

`boundedProjectiveTensorInputLocalizer` は、完全入力を含む
上有界・各項射影の元の複体から、同じ巡回係数模型への相対関手。
その p 入力・完全周期 Hom・実スペクトル化の合成が **`projectivePowerSpectrum`**。
`projectivePowerSpectrum_sourceIso` は元の厳密な合成との **全関手の指定同型**。
対象ごとにスペクトルを選ぶ構成で代用していない。

採用した周期のままの未シフト Hom を使っている。
**native Tate[-1] との比較、完全入力からの余極限保存延長、
スペクトル的な右 k 作用、P⁰ の全自然変換はまだ未完了**。
次は同じ係数類を表す実鎖写像と、そのホモロジー類を照合する。

### 88.2 検証

`bounded-cyclic-coefficients-03.log`・`tensor-input-bounds-homotopy-01.log` の
BoundedCyclicSpectrum、`tensor-input-bounds-homotopy-03.log`・
`bounded-projective-tensor-input-01.log`・`projective-power-spectrum-01.log`：対象成功。
新規七本の最終版に警告なし。
`audit-projective-power.log`：**155 本・1,173 宣言、標準三公理のみ**。
sorry・追加公理なし。共有入口・共有監査は未変更。夜の規則どおり続行する。


## 89. D79(iii)：単位での同じ p 入力と、指定係数類を表す実射

| 登録候補（`SerrePositivity.EInfinity.PowerOperation.`） | 行数 |
| --- | ---: |
| CyclicCoefficientSeed | 53 |
| CyclicCoefficientSeedHomology | 55 |
| CyclicTensorUnitComparison | 67 |

追加 **175 行**、(iii) **1,873 行**、(ii)+(iii) **9,067 行**。

### 89.1 同じ単位と指定類の照合

`powerOperationTensorUnitIso` は、元の p 入力の単位での値を、同じ自明な k 係数の
single 複体へ送る実同型。既存 `tensorUnitPower_permutation` と
`tensorUnitPowerIso` を使い、作用の恒等性と同じ縮約を保持した。
`powerOperationUnitResolutionHomIso` により、同じ p 入力と周期 Hom の単位での値が
元の指定係数 Hom 模型へ実複体同型で戻る。

`powerOperationCoefficientSeed` は、その指定係数 Hom へ単位複体から入る **実鎖写像**。
同じ左正則評価で 1 を回収し、`powerOperationCoefficientSeed_homology_value` で
実 H^0 の類も指定比較で 1 に送られることを示した。
`powerOperationCoefficientSeed_matches_class` はその類を、§84 で固定した
同じ周期係数模型の H^{-1} の指定類へ送る等式。
ホモロジー群に任意の射を後から選んだ構成ではない。

native Tate[-1] との比較、同じ境界射の orbit との比較、T_p の延長と
スペクトル的な右 k 作用の照合はまだ必要。
特にこの鎖模型の k 線形な係数種を、未証明の右 k 作用の射として扱わない。
次は同じ周期解像度の正の部分への全自然な制限と、上有界係数の有限支持を進める。

### 89.2 検証

`cyclic-coefficient-seed-02.log`・`cyclic-unit-seed-homology-02.log`：対象成功。
新規三本の最終版に警告なし。
`audit-cyclic-seed.log`：**158 本・1,209 宣言、標準三公理のみ**。
sorry・追加公理なし。共有入口・共有監査は未変更。夜の規則どおり続行する。


## 90. D79(iii)：同じ周期解像度の正の部分と実スペクトル化

登録候補（`SerrePositivity.EInfinity.PowerOperation.`）：
LinearHomComplexPrecomposition（47 行）、CyclicPeriodicRestriction（56 行）、
RelativeComplexSpectrum（37 行）、CyclicPositiveSpectrum（80 行）。
追加 **220 行**、(iii) **2,093 行**、(ii)+(iii) **9,287 行**。

完全周期解像度の非負次数部分への包含を前合成する、同じ Hom の全自然変換を作った。
上有界係数では次数 n の座標が 0 ≤ i ≤ d−n に限られることも証明した。
正の部分の各項の射影性と、上有界係数の準同型を保つことから、
その実相対関手・native な Sp への関手・厳密な元の図式との全 sourceIso を得た。
RelativeComplexSpectrum は［一般∞］の移動候補。

これはまだ native な orbit との同定や native な Tate 境界ではない。
次は逆生成元の射影解像度によるテンソル余不変の直和全複体と、
同じ正の Hom の有限座標の比較を進める。

対象ビルド `cyclic-positive-spectrum-02.log` 成功、最終版の警告なし。
`audit-cyclic-positive.log`：**162 モジュール・1,242 宣言、標準三公理のみ**。
sorry・追加公理なし。共有入口・共有監査は未変更。夜の規則どおり続行する。


## 91. D79(iii)：orbit の実解像度・指定評価・有限支持

| 登録候補（`SerrePositivity.EInfinity.PowerOperation.`） | 行数 |
| --- | ---: |
| CyclicOrbitModel | 52 |
| CyclicOrbitCoordinateSign | 31 |
| RegularOrbitCoordinates | 68 |
| RegularOrbitNaturality | 62 |
| RegularOrbitDifferential | 55 |
| CyclicPositiveFiniteCoordinates | 79 |
| CyclicOrbitResolutionCoordinates | 52 |
| CofanZeroSupport | 49 |

追加 **448 行**、(iii) **2,541 行**、(ii)+(iii) **9,735 行**。

### 91.1 同じ鎖模型の比較の現在地

逆生成元による Mathlib の実射影解像度を負の余鎖次数へ零延長し、
元のテンソル余不変関手による直和全複体を固定した。
同じ項の同型と同じ指定微分（鎖次数が偶数ならノルム、奇数なら逆生成元の差）を照合した。

Hom 側の左正則評価は係数の元の生成元を使い、
orbit 側の評価は逆元を含む。実余不変射の上でこの差とノルムを証明したので、
逆生成元の選択が同じ係数微分を与えることを確認できる。
係数の全射への自然性も、指定された元の射で証明している。

正の Hom の各次数は、同じ切り詰めの項の同型と左正則評価により
有限な積へ実線形同値で移る。この同値は共通上界を持つ係数射に自然。
直和全複体の符号との比較用に ε_s = (-1)^{binom(s,2)} と隣接次数の比を固定した。
CofanZeroSupport は［一般圏］基盤への移動候補。

**正の Hom と実 orbit 全複体の鎖同型、native orbit/Tate との比較、
T_p の延長、スペクトル的な右 k 作用、P⁰ の全自然変換は未完了**。
いまは零支持を除いた指定余積の同型と、同じ有限対角線の比較を続けている。
現時点で 29,000 行の停止基準を超える見込みはない。

### 91.2 検証

`cyclic-orbit-model-01.log`、`regular-orbit-coordinates-02.log`、
`regular-orbit-naturality-03.log`、`cyclic-orbit-coordinates-01.log`（RegularOrbitDifferential）、
`cyclic-orbit-coordinates-03.log`（CyclicPositiveFiniteCoordinates）、
`cofan-zero-support-01.log`（CyclicOrbitResolutionCoordinates）、
`cofan-zero-support-03.log`：対象成功、最終版の警告なし。
`audit-orbit-coordinates.log`：**170 モジュール・1,307 宣言、標準三公理のみ**。
sorry・追加公理なし。共有入口・共有監査は未変更。夜の規則どおり続行する。


## 92. D79(iii)：同じ orbit 全複体の有限座標と符号付き次数同型

| 登録候補（`SerrePositivity.EInfinity.PowerOperation.`） | 行数 |
| --- | ---: |
| CoproductZeroSupport | 46 |
| CyclicOrbitDiagonal | 67 |
| CyclicOrbitFiniteSum | 42 |
| CyclicOrbitFiniteCoordinates | 55 |
| CyclicPositiveOrbitDegreeIso | 56 |
| CyclicPositiveDifferentialCoordinates | 86 |

追加 **352 行**、(iii) **2,893 行**、(ii)+(iii) **10,087 行**。

### 92.1 実装した同型と残る可換性

`cyclicOrbitTotalDegreeSupportIso` は元の直和全複体の同じ次数の項に対し、
零の成分を除く指定余積の同型。支持する対角線を 0 ≤ s ≤ d−n に取り直し、
同じ正則余不変の評価を使って有限な積への `cyclicOrbitTotalDegreeCoordinatesIso` を得た。
CoproductZeroSupport は［一般圏］基盤への移動候補。

`cyclicPositiveOrbitDegreeIso` は、正の Hom の有限座標と
ε_s = (-1)^{binom(s,2)} の符号を合成した、**同じ次数の実加群同型**。
微分との可換性を仮定に入れて組み立てたものではなく、
**まだ鎖同型とも native orbit 比較とも主張していない**。

Hom 側では、元の切り詰めの包含の可換性から `cyclicPositiveResolution_inv_d` を示した。
`cyclicPositiveHomCoordinate_delta` は元の Hom 微分の一座標が、
係数微分と (-1)^{n+1} を掛けた同じ周期係数微分との和であるという等式。
次は元の orbit 全複体の指定包含射の座標をそろえ、同じ微分との可換性を閉じる。

### 92.2 検証

`cyclic-orbit-diagonal-02.log`、`cyclic-orbit-finite-coordinates-01.log`、
`cyclic-positive-orbit-degree-02.log`、`cyclic-positive-differential-03.log`：対象成功。
六本の最終版に警告なし。
`audit-orbit-finite.log`：**176 モジュール・1,378 宣言、標準三公理のみ**。
sorry・追加公理なし。共有入口・共有監査は未変更。夜の規則どおり続行する。


## 93. D79(iii)：元の orbit 包含射の指定座標まで検証

登録候補（`SerrePositivity.EInfinity.PowerOperation.`）：
FiniteBiproductCoordinates（49 行）、CyclicOrbitSummandCoordinates（80 行）。
追加 **129 行**、(iii) **3,022 行**、(ii)+(iii) **10,216 行**。

`cyclicOrbitTotalDegreeCoordinates_inclusion` は、元の直和全複体の
指定包含射を、同じ正則評価・有限双積の指定包含射で表す **元の圏での等式**。
`cyclicOrbitTotalDegreeCoordinates_inclusion_apply` は、その等式を各座標で評価した
Kronecker の式。FiniteBiproductCoordinates は［一般圏］基盤への移動候補。

正の Hom と orbit の **次数同型**は実装済みだが、微分可換性による鎖同型はまだ未完了。
native Tate[-1] の比較・T_p の延長・スペクトル的な右 k 作用・P⁰ の完成も未完了。

`cyclic-orbit-summand-coordinates-02.log`（FiniteBiproductCoordinates）、
`cyclic-orbit-summand-coordinates-06.log`：対象成功、最終版に警告なし。
`audit-orbit-inclusions.log`：**178 モジュール・1,386 宣言、標準三公理のみ**。
sorry・追加公理なし。共有入口・共有監査は未変更。
ここまでの検証済み分をコミットし、夜の停止規則に従い次節の規模確認を記録する。


## 94. 夜の停止規則：M14 の残りの規模を再評価し、Lean を止める

### 94.1 確認できたものと、まだ供給されていないもの

検証済み実装は §93 のコミットまで保存した。実測は (ii) 7,194 行、
(iii) 3,022 行、合計 **10,216 行**（(i) の既存界面・drafts の変更は別）。
(ii) の native Sp の入口と V・π/H は §63.6 の上端 7,000 行にほぼ収まった。
一方、(iii) の当初 3,000〜5,500 行は、現在の **鎖模型の部品だけで 3,022 行**を使い、
以下の三つをまだ含んでいない。§83 の仮置きの残り 4,500〜8,000 行を
引き続き全体の保証として使うことはできないと判断した。

- `projectivePowerSpectrum`・`boundedCyclicSpectrum`・`cyclicPositiveSpectrum` は
  実相対図式から Sp への関手と全 sourceIso を持つが、
  native な homotopy orbit・norm・Tate[-1] との比較ではない。
  KST の `homotopyFixedPoints` とその native limit cone の部品はあるが、
  今の調査ではこの入力で使える native orbit→fixed の norm と指定 Tate 境界の
  全自然比較を発見していない。固定点だけを Tate と呼び替えることはできない。
- `powerOperationCoefficientSeed` の k 線形な実鎖写像と、その指定 H^0 の計算はある。
  これは DAG XIII Construction 2.2.6 の **スペクトル的な右 k 加群の射 e**を
  供給したものではない。新たな右作用とその coherent な照合が必要である。
  `DGKernelBimoduleIso` 等の dg 双加群の比較も、この非 D(k) 線形な作用の代用にはならない。
- p 入力の準同型保存・上界・混合色の自由性は証明したが、
  完全入力上の Tate 構成の exact 性、元の完全 ∞ 圏への全降下、
  余極限保存延長 T_p と指定類の右作用の比較はまだ必要。
  鎖レベルの混合色の自由性だけで、これらの全自然変換を得たとはしない。

### 94.2 重複を除いた残りの暫定見込み

| 残る束 | 追加 Lean の見込み | 範囲 |
| --- | ---: | --- |
| 正の Hom と実 orbit 全複体 | 900〜1,600 | 同じ指定微分の可換性・全自然な鎖同型 |
| native orbit・norm・Tate の比較 | 3,000〜5,500 | 現在の p 入力で使う範囲、指定境界と全関手。右 k 作用は次々行 |
| 完全入力での exact 性・降下・T_p の延長 | 2,800〜4,800 | 同じ p 入力の混合項、完全 ∞ 圏、全自然な余極限保存延長 |
| スペクトル的な双加群と e | 2,800〜5,000 | 右 k 作用・指定係数類・左作用との区別・全比較 |
| BE の作用による P⁰ と Rem 2.2.7 | 1,800〜3,200 | 同じ境界から BE の p 項作用への射と係数計算。Tot は次行 |
| 離散・Tot の最後の照合 | 1,000〜2,000 | G10 後の (iv)。前行との二重計上なし |
| **残り** | **12,300〜22,100** | |
| **既知実測と合わせた全体** | **22,516〜32,316** | (i) の小さい変更は別 |

これは未証明の部分の工程見込みであり、数学的な不可能性や下界の主張ではない。
ただし現時点で上端を **29,000 行**以内にする、既存宣言による検証済みの短縮経路はない。
当初の「P⁰ の Tate・指定類・全自然変換」の一行の中に、
鎖模型→native の境界、exact な延長、スペクトル的な右作用という別の未供給の束が残る。
これらを表の外へ出して行数から除くこともしない。

したがって coordination.md §2「夜の進め方」の **上限を超えそうな場合**として、
**M14 の Lean はここで止め、M15 の一般 R 加群の段 0 の紙の作業へ移る**。
上限の引き上げや界面の追加は自己承認しない。朝の判断点は、
上の native Tate・スペクトル的な module の供給と分担、および M14 の範囲の切り方。
G10 の有無だけを、現在の鎖同型の未完了の理由にしてはいない。
承認を求めて今夜の作業を止めず、次節へ進む。


## 95. 代わりの作業：M15 の一般 R 加群、§66 の続き（紙のみ）

### 95.1 今夜の実装から再利用できるもの

`eilenbergMacLaneDerived A` は一般の可換係数環 A の既存 D(A) から
native Sp への実関手であり、`eilenbergMacLaneDerived_homologyIso A i` は
その全ホモトピー圏の π/H 比較。M15 で台をスペクトルとして読むときは再利用できる。
一般の E∞ 頂点 R 上の加群をこれで構成したことにはならない。
係数制限と V の全比較も未供給のままである。

§66 の左加群の通常圏の部品に加え、次の **既存の native dg module** の出力を
最初の模型の束で再利用する候補として確認した。

| 既存宣言 | 実際に供給するもの | M15 へ接続する前に要るもの |
| --- | --- | --- |
| `dgAlgebraDerivedInfinityCategory A B` | B : Mon (Complex A) 上の右半自由 dg 加群の実 ∞ 圏 | BE の厳密代数から同じ dg 代数を作る全関手と、一般 R への降下 |
| `dgAlgebraDerivedInfinityCategory_isStable` | 同じ dg 代数上の module ∞ 圏の安定性 | E∞ 頂点 R に対する module 圏との比較 |
| `dgModuleHomSpaceInfinity`・`dgModuleHomSpaceValueEquivalence` | 両変数で coherent な空間値 Hom と同じ Hom end の比較 | R 加群の RHom、相対テンソルとその随伴の比較 |
| `dgModuleExtensionYonedaNerveIso` | 既存 dg 圏の拡大と同じ Yoneda に対する指定比較 | BE の係数射と、同じ単位加群・指定辺への適用 |
| `dgKernelTensorIsoNerveOfBimoduleIso`・`dgKernelDerivedInfinity_bimoduleIso` | 実 dg 双加群同型による kernel 関手の比較 | E∞ の相対テンソルと対称性の整合 |
| `dgBimoduleFunctorHomFunctor_resolvedMap_isIso_of_quasiIso` | 指定した dg 双加群の解決済み射の同型性 | 必要な BE 加群の双加群を実際に供給すること |

`dgAlgebraDerivedInfinityCategory` は一般の非可換 dg 代数を受け取る。
ここで H^0(R) に落とす必要はない。ただし、それだけでは
E∞ の相対テンソルの対称性は供給されない。

### 95.2 最初に検査すべき型と射の範囲

以下は **未実装・未型検査の型案**。本体・界面・drafts の宣言の追加ではない。
`Complex`・BE の operad の名前空間を開いた文脈で記す。

```lean
-- 厳密 BE 代数の同じ台と、指定した単位・積を持つ dg 代数。
barrattEcclesAssociativeForget (A : Type u) [CommRing A] :
  (operad A).Algebra ⥤ Mon (Complex A)

-- 上の関手が構成できた後の、厳密な各入力での候補。
strictModuleInfinity (X : (operad A).Algebra) : SSet.{u+1} :=
  dgAlgebraDerivedInfinityCategory A
    ((barrattEcclesAssociativeForget A).obj X)

-- 同じ唯一の対象で評価して台へ戻す、全射を含む候補。
strictModuleUnderlying (X : (operad A).Algebra) :
  strictModuleInfinity X ⟶ derivedInfinityCategory A
```

最初の検査は、BE の指定零単体の操作から strict な単位・積・結合性が
元の複体で成立することと、全代数射がそれを保つこと。
`homologyCommRing` の供給だけではこの型を満たさない。
この検査が閉じたら、一対象 dg 圏の既存の実 module 構成を適用できる。
閉じない場合の enveloping algebra の経路は別の設計判断であり、ここで採用しない。

一般の native 頂点 R に対する型は §66.1 の `modulesOver`・`moduleUnit`・
`algebraAsModule`・`moduleExtend`・`moduleRestrict` のまま。
これへ進むときは次を同じ指定射で照合する。

1. 厳密 BE の準同型に対する restriction と extension の随伴。
2. BE の弱同値に対する module ∞ 圏の同値と、台の忘却との全比較。
3. native な CAlg の射と合成に対する module 圏の降下。
   頂点ごとに厳密模型を一つ選んで終わりにしない。
4. E∞ の高次の可換性を使った相対テンソルの対称性・結合性・単位。
5. 単位から `algebraAsModule f` への指定辺、その fiber、n 重テンソルの指数射。

### 95.3 地図との対応と見込み

`research/ha-coverage/review/ch4.csv` の記載を再確認した。
4.2.1.15 は通常の `Mon`・`Mod`、4.2.3.5 は通常の内部加群の余極限、
4.5.2.1 は通常の balanced tensor の特殊例という部分一致であり、
4.5.3.1 の変わる代数に関する全 module の射影は未供給という判定。
この地図は native な一般 R の module の既証明性を意味しない。

§66.4 の **2,500〜4,500 行**は、以下の再利用を前提とする暫定見込みとして保持する。
既存の dg module の安定性や Hom 空間を新しく作り直す費用は加算しない。

| 束 | 追加の暫定見込み | 停止前に供給すべき指定比較 |
| --- | ---: | --- |
| 厳密 BE と既存 dg module、native な係数射への降下 | 700〜1,400 | 台・単位・全 restriction/extension・弱同値不変性 |
| E∞ の相対テンソルと底変換 | 1,200〜2,200 | 対称性・結合性・単位、同じ pushout の辺 |
| fiber・thick ideal の利用側への接続 | 600〜900 | 同じ単位と指定辺、テンソルによる有限余極限保存 |
| **計** | **2,500〜4,500** | |

RHom・完備版・Amitsur の Tot の利用側は §66.3 の後続であり、この模型の束と二重計上しない。
M15 に入るときの担当決定では、上の一般 R の module と相対テンソルの供給者を
先に確定する必要がある。M14 の **スペクトル的な右 k 作用**と、
ここでの **R 加群の相対テンソル**には別の比較が要るため、
一方が終われば他方も終わるという見込みは置かない。

この節は紙のみ。M15 の Lean・新たな界面・drafts の型変更には着手していない。
今夜の代わりの作業の段 0 として報告する。


## 96. M14 の範囲の比較・段 0（11-13、§25、紙のみ）

基準は本枝 `e33d5dc1f`。main の指示書 §25 も `git show main:...` で読んだ。
**界面・drafts・Lean は変更していない。ビルド・監査・整理券の取得もしていない。**
以下は設計の判断材料であり、D79 の改訂を実施・自己承認したものではない。

### 96.1 結論と二つの範囲

**BS の Lemma 8.4 の結論には、π_n 上の加法的演算と、CAlg の射への自然性で足りる。**
ただし、現在の五つの欄を成分の型へ機械的に置き換えるだけでは、
現 drafts の証明の筋を全部閉じたことにはならない。
**levelwise Frobenius と、単体的余単体的模型の実現上の演算との比較が別に必要**。
特に π_n は一般の幾何学的実現の各段の π_n の余極限ではない。
filtered 余極限についての議論を、単体的実現へそのまま適用しない。

| 範囲 | BS で受け取る出力 | 残る中心的な比較 | 見込み |
| --- | --- | --- | --- |
| 今の D79、coherent Sp 値の演算 | 実スペクトルの自己変換と π_n の計算 | native Tate・右 k 作用・T_p・指定境界、実現の比較 | §94 の全体 22,516〜32,316 行。上端は基準超過 |
| May の成分の演算 | ho(CAlg F_p) 上の可換群値関手の自己自然変換 | 正規化した May 演算、同じ BE の Tot・実現模型の Frobenius 計算 | 新規 5,500〜9,950 行。後述の模型比較を含む暫定見込み |

May 案なら、native な orbit・norm・Tate、スペクトル的な右 k 加群の e は
この BS の証明に不要となる。May の **代数的な巡回解像度 W** と
`W ⊗_{C_p} X^{⊗p}` は使う。これを native な homotopy orbit の構成と混同しない。
coherent な Sp 値の演算との一致は、新しい BS 界面を埋める前提にはせず補完へ回す案。

### 96.2 利用者の全確認

`powerOp0` と `powerOperationZero*` を本体・drafts 全体で検索した。
直接の消費者は Shared/EInfinityPowerOperation、組み立て関数 Assembly、
Shared/BarrattEcclesTheory の供給欄。A4 の証明本体はまだ sorry と証明方針である。
したがって、以下の「足りる」は **証明に必要なデータの確認**であり、
未実装の A4 の証明を検証したという意味ではない。

| 宣言・箇所 | 現在要求するもの | 成分の演算での扱い |
| --- | --- | --- |
| A4 `prismaticPerfection_coconnective`（277 行以降） | mod p の shift と P⁰ の一致、可逆性、正の π の消滅 | 各 π_n の演算の等式と自然性でよい。filtered 塔の π の比較と、下記の模型の実現比較が必要 |
| A4 `prismaticPerfection_h0_perfectDelta` | H⁰ mod p の Frobenius、C/p の単射、shift の可逆性 | π_0 の等式でよい。P⁰ の高次 coherent 性は使わない。p 完備性・δ 構造は別の既存の工程 |
| Shared `homotopy`・`homotopyCohomology`・`homotopyMap` | H^{-n} と π_0 の環の読み替え | そのままの加法群で利用可能 |
| `powerOperationZero`・`_zero`・`_pos`・`_natural` | 演算の成分、零次、正次数、各辺への自然性 | 弱い型で供給できる |
| `powerOperationZero_natTrans`・`_primeField` | **FunctorHom 自体** | 現在の型は弱いデータからは作れない。BS 側は通常の NatTrans へ書き換える案。元の強い出力は補完側 |
| `powerOperationZero_component` | 実 Sp の成分を π に送った等式 | 現在の等式は弱いデータからは作れない。BS には H^{-n} の成分を読む等式だけを残す案 |
| `powerOperationZero_eq_frobenius_discrete` | ho(Sp) の射の等式 | 全 n の可換群準同型の等式へ弱めればよい |
| `powerOperationZero_eq_frobenius_tot` | ho(Sp) の射の等式、コメントには実現への移行も含む | 全 n の準同型の等式へ弱められるが、証明には May の Tot 模型での直接計算が要る |
| Shared の末尾 172–177 行の証明方針 | coherent な自然変換と極限・実現の比較 | **ここが現在の高次の整合を使う方針**。弱い型ではそのまま使えない |

上の三つの強い補助出力を外部で消費する Lean の呼出しは検索で見つからなかった。
A4 冒頭の coherent という説明も、決定後に成分の説明へ直す対象。
A3/DiscreteCase の G-A3-9 には Shared から π_0 の部分を前倒しする方針の参照がある。
これも π_0 の比較で足りるが、⑤c のファイルなので今回は変更しない。

**filtered の段**：演算を全対象に定義して辺に自然にしておけば、
各余極限の脚との自然性と、π_n と filtered 余極限の比較から、
余極限上の演算は各段の演算の余極限に一致する。
可逆な shift と一致して正の π_n では零なら、その群は零となる。
これには `forget_preservesSifted` の filtered の部分等の供給は要るが、
P⁰ の Sp 値の coherent な持ち上げは要らない。
完備化については π と任意の完備化の可換性を新たに仮定せず、
従来の p 完備性・導来 Nakayama・t 構造の工程を使う。

### 96.3 新しい型の案

最小案は **F_p に限った本欄**とし、π_n を H^{-n} の台の加法群として読む。
以下は未型検査の Lean の型案。既存 `hoMap`・`additiveCohomologyOnHo` を用い、
`E` の欄の記法を省略して `CAlg`・`forget`・`pi0`・`pi0_forget` を書く。
`ν B` は既存 `nerveVertex B` の略記。

```lean
-- 界面の補助。C と U を引数にすれば E の定義中にも循環せず使える。
abbrev homotopyGroupsOnHo (k : Type u) [CommRing k]
    {C : SSet.{u+1}} (U : C ⟶ derivedInfinityCategory k) (n : ℤ) :=
  hoMap U ⋙ additiveCohomologyOnHo k (-n)

-- 以下 Π p n := homotopyGroupsOnHo (ZMod p) (forget (ZMod p)) n。
powerOp0 (p : ℕ) [Fact p.Prime] (n : ℤ) :
  Π p n ⟶ Π p n

powerOp0_zero (p : ℕ) [Fact p.Prime]
    (x : (CAlg (ZMod p)) _⦋0⦌)
    (a : ((pi0 (ZMod p)).obj (SSet.HomotopyCategory.mk x)).right) :
  let e := (pi0_forget (ZMod p)).app (SSet.HomotopyCategory.mk x)
  (powerOp0 p 0).app (SSet.HomotopyCategory.mk x) (e.hom a) = e.hom (a ^ p)

powerOp0_pos (p : ℕ) [Fact p.Prime]
    (x : (CAlg (ZMod p)) _⦋0⦌) (n : ℤ) (hn : 0 < n) :
  (powerOp0 p n).app (SSet.HomotopyCategory.mk x) = 0
```

`powerOp0 p n` は **通常の可換群値関手の NatTrans**。
`FunctorHom` ではない。CAlg の全ホモトピー圏の射で自然性を述べるので、
辺をホモトピーで取り替えた不変性・恒等射・合成もこの型に含まれる。
各 `SSet.Edge` への自然性は `SSet.HomotopyCategory.homMk f` で評価すれば得られる。
辺ごとの等式だけを別々に欄にするより、局所化と照合しやすい。
Sp の π で表記する案も `toSpectra_homologyIso` で共役すれば同じ強さになるが、
この H^{-n} の案では P⁰ のための V や係数制限の V の比較を必要としない。
既存の `toSpectra*` 欄を削除する提案・変更は今回は行わない。

F_p 上では Frobenius は F_p を固定するので、離散 Frobenius は
B → Res_{Frob} B の代わりに **B → B の F_p 代数の射**として書ける。
これにより不要な係数制限の同型を型から外せる。

```lean
powerOp0_discrete (p : ℕ) [Fact p.Prime]
    (B : RingAlgebra (ZMod p)) (f : B ⟶ B)
    (hf : ∀ a : B.right, f.right.hom a = a ^ p) (n : ℤ) :
  let x := atVertex (discrete (ZMod p)) (ν B)
  (powerOp0 p n).app (SSet.HomotopyCategory.mk x) =
    (Π p n).map (SSet.HomotopyCategory.homMk
      ((nerve.edgeMk f).map (discrete (ZMod p))))

powerOp0_tot (p : ℕ) [Fact p.Prime]
    (X : CosimplicialRingAlgebra (ZMod p)) (f : X ⟶ X)
    (hf : ∀ j (a : (X.obj j).right), (f.app j).right.hom a = a ^ p)
    (n : ℤ) :
  let x := atVertex (ofCosimplicial (ZMod p)) (ν X)
  (powerOp0 p n).app (SSet.HomotopyCategory.mk x) =
    (Π p n).map (SSet.HomotopyCategory.homMk
      ((nerve.edgeMk f).map (ofCosimplicial (ZMod p))))
```

いずれも **全整数 n の可換群準同型の等式**。n=0 だけへは弱めない。
一般の `[CharP k p]` での Shared の API を残すなら、F_p → k に沿う CAlg の制限と
`restrict_forget`・`restrictD_homologyIso` から
`Π_k(n) ≅ hoMap(Res) ⋙ Π_{F_p}(n)` を作り、その自然同型で上の演算を共役する。
この一般 k の補助は自然性を運ぶだけで、新たな Sp 値の持ち上げは要らない。
一般 k の `_discrete`・`_tot` は係数制限と同じ模型の比較も運ぶ必要がある。
F_p の本欄を供給することと、全 k に対する欄を別々に新規証明することを混ぜない。

### 96.4 May の構成と局所化までの不足

原典を確認した箇所：
[May, Definitions 1.2・2.1・2.2, Proposition 2.3](https://www.math.uchicago.edu/~may/PAPERS/10.pdf#page=8)、
[より明示的な May–Steenrod の定義、§5・Definitions 8–10](https://arxiv.org/pdf/2010.02571#page=9)。
BE からの作用の出典は [Berger–Fresse](https://arxiv.org/pdf/math/0109158)。
ここで用いる原典の範囲は、巡回解像度からの演算の定義・加法性・自然性と、
その零次の値。Adem 関係・全 Cartan 公式・全ての冪作用を実装する必要はない。

homological な n（本体の H^{-n}）で、W の i 番目の生成元を e_i とし、
同じ BE 作用から D_i[a] を作る。May の正規化を採れば、P⁰ は
p=2 で D_{-n}、奇素数で ν(n)D_{-n(p−1)}。負の添字の D_i は零とする。
したがって n>0 の消滅は添字から、n=0 の値は D_0 の積から得られる。
ν(n) は May の整数次数の符号・階乗の単元であり、負の次数での逆元も含む。
係数を勝手に 1 としない。巡回生成元・Koszul 符号・ν を最初に同じ規約にそろえる。

必要な実装を次の順で切る。

1. **W → E(p)**：非負の巡回射影解像度を、制限した BE の arity p の増大解像度へ写す。
   e_0 の増大は 1 とし、同変な鎖比較を固定する。
   `augmentation_quasiIso`・`complexAugmentation_quasiIso`、左正則の射影性、
   Mathlib の射影解像度の比較・ホモトピーの部品を再利用できる。
   ただし必要な同変比較そのものは未供給。対象ごとに非自然な BE 作用を選ばない。
2. **代表元の独立性・加法性**：θ(e_i ⊗ a^{⊗p}) が cycle となり、
   境界による a の取り替えで同じ類になること、混合項が境界になることを示す。
   固定した θ を全厳密代数で使い、演算を加法準同型として得る。
   `CyclicMixedOrbit`・`CyclicTensorMixedWords` はこの混合項の自由性に再利用できる。
   混合語の自由性だけでは、境界の原像の構成と代表元独立性まで済んではいない。
3. **全厳密 BE 射への自然性**：作用保存から homologyMap と演算の可換性を示す。
   全次数の `homologyFunctor` と `Operad.Algebra.forget` を使える。
   既存 `HomologyAlgebraFunctor` の H⁰ の自然性は実装の手本。
4. **擬同型不変性**：厳密 BE 射 f が擬同型なら H^{-n}(f) は同型。
   3 の可換式を同型で共役すれば、操作を両側で同定できる。
   これに任意の複体への tensor 冪の準同型保存を新たな仮定として加える必要はない。
5. **CAlg の全辺への降下**：`ordinaryAlgebraHoSource_isLocalization` が既存。
   H^{-n} の関手を通常の局所化へ降ろし、Mathlib
   `Localization.liftNatTrans`・`liftNatTrans_app` で操作を降ろす。
   `barrattEcclesPi0`・`barrattEcclesPi0_sourceIso` と同じ局所化を使い、
   既存の忘却先の H^{-n} 関手との自然同型で共役する。
   これで arbitrary な CAlg の辺にも自然となり、coherent Sp 値の変換の局所化は不要。
   残る新規部分は、その全次数の sourceIso と共役・成分の照合。

`powerOperationCoefficientSeed`・`powerOperationCoefficientSeed_homology_value` は、
今夜固定した **完全周期 Hom の単位係数類**の値 1 の検証として再利用できる。
ただし May の W → E(p) の全高次数の比較を供給する宣言ではない。
May の e_0 の規約へ運ぶ比較を明記して使い、既存の H⁰=1 だけから
ν や Tot 上の P⁰ の値を決めない。
`CyclicOrbitProjectiveResolution` は逆生成元で固定されているため、
May の巡回群の同定を合わせるか、元の生成元を引数にした Mathlib の W を使う。
ここは最初の紙・型の区切りで点検し、既存の公開定義を改変して規約を吸収しない。

### 96.5 `_discrete`・`_tot`・A4 の実現比較と G10

**離散**：n=0 は上の D_0 の積、n≠0 は離散代数の H^{-n}=0 で閉じる。
`discrete_forget` と `strictToD_homologyIso` を介する。G10 の待ちは不要。

**cosimplicial な `_tot`**：正規化（または比較射を保持した交代余面）複体の
同じ BE 作用について、正規化した May の top operation が
各 cosimplicial degree の a ↦ a^p を誘導することを直接計算する。
通常の p 重 cup 積は次数を変えるので、この証明として使わない。
n>0 は Tot の coconnectivity、n=0 は零次、**n<0 はこの top operation の計算が核心**。
離散入力上の等式と各射影への自然性だけでは n<0 の等式は得られない。

既存の `TableReduction`、Surjection の実対称列・operad、IntervalCuts の演算、
Alexander–Whitney の構成は部品として再利用できる。
ただし現在の `IntervalCuts.cochainAction` は区間上の構成であり、
任意の余単体的可換環上の top operation の計算済み API とは数えない。
BF のコチェイン作用と、`ofCosimplicial` の **同じ CAlg 対象**の比較が必要。
下の複体の擬同型だけでその BE の冪作用の一致を結論しない。

- 厳密なコチェイン模型での May/Frobenius の計算は G10 なしで進められる。
- 指定された native Tot とその Frobenius 辺へ運ぶ段は、同じ BE 図式・錐と
  実現を比べる G10／③-b の比較を要する。単に成分の型に変えただけでは、この依存は消えない。
- `ofCosimplicial_forget`・`strictToD_homologyIso` の欄を仮定した利用側は、
  その比較を使って H^{-n} 上で読むだけでよいが、BE 実例で欄を供給する工程は別に残る。

**単体的余単体的模型**：BS の [Lemma 8.4 の証明](https://people.mpim-bonn.mpg.de/scholze/prisms.pdf#page=63)
はこの模型の実現上での levelwise Frobenius の一致を使う。
Shared の現在の `_tot` の型が取るのは cosimplicial X **一つだけ**であり、
その文面だけでは外側の単体的実現の比較を供給していない。
現在の「coherent なので実現へ移る」というコメントを、新しい弱い界面の証明に流用できない。

ここは次の **追加の証明義務**として明示して決める必要がある。

- 厳密な simplicial-cosimplicial F_p 代数 X の、指定 BE 実現模型 Y と、
  levelwise Frobenius の誘導する指定辺 F_Y : Y → Y に対し、
  **全整数 n で** `(powerOp0 p n).app (mk Y) = (Π p n).map (homMk F_Y)`。
- 行数には、double complex の同じ BE 作用と正規化・実現の比較を含める。
  π を levelwise に取り、その余極限と書き換えて証明済みにしない。
- これは A4-local な模型比較補題として置くか、`_tot` を二重模型まで含む欄へ広げるかの判断点。
  前者なら五欄の改訂に留められるが、その補題の証明は M14 の BS 用の範囲に含める必要がある。
  **その証明を範囲から外したまま「五欄だけで A4 全体が閉じる」とは報告しない。**

May の鎖操作でこの比較を直接作る経路は紙の上では取れる。
原典の BS の比較主張と整合するが、該当する現モデルの Lean 証明は未供給。
この段では G10／③-b の「同じ厳密模型・指定射・native 実現」の比較を利用する。
filtered な Frobenius 塔へ移る最後の段は 96.2 の辺への自然性で足りる。

### 96.6 再利用の行数と新規見込み

今の **10,216 行**を削除・改変する案ではない。May 経路の必須の新規量からは、
使わない Sp/Tate の構成を外し、既存の完成分としては別に残す。

| 既存分 | 実測 | May 案での位置 |
| --- | ---: | --- |
| D79(ii) の V・π/H とその基盤 | 7,194 | H^{-n} に直接値を取る最小案では必須でない。Sp 表記の共役や補完にはそのまま使える |
| TensorPowerRepresentation・CyclicTensorInput | 117 | p 入力と同じ巡回作用を直接再利用 |
| CyclicMixedOrbit・CyclicTensorMixedWords | 112 | 加法性の混合語の自由性を直接再利用。境界計算は追加 |
| CyclicTensorUnitComparison | 67 | 同じ単位入力の比較を再利用 |
| CyclicOrbitModel | 52 | 代数的な W と全複体の部品。逆生成元の規約を点検した上で一部を使う候補 |
| CyclicCoefficientSeed・CyclicCoefficientSeedHomology | 108 | 単位係数の規約照合の参考・再利用候補。May の全操作を既に供給したとは数えない |
| その他の D79(iii) | 2,566 | 主に周期 Hom・native 図式・有界比較・orbit 座標等。May の最小経路には要求しない |
| **計** | **10,216** | 直接の共通部分 296 行、さらに 160 行が条件付き・規約照合の候補 |

| 新規の束 | 暫定見込み（行） | 完了と数える出力 |
| --- | ---: | --- |
| May の W→BE、cycle・境界・加法性・自然性、ν の規約 | 2,000〜3,500 | 任意次数の厳密 BE ホモロジー上の演算 |
| ho(CAlg) への局所化と全 H^{-n} との比較 | 350〜650 | 全辺に自然な NatTrans |
| 界面・Assembly・Shared/A4 の型の移行 | 250〜450 | 承認された範囲だけの五欄と補助 |
| 離散入力 | 100〜200 | 全 n の `_discrete` |
| cosimplicial 模型の top operation と `_tot` | 1,000〜1,800 | 同じ作用・同じ Frobenius 辺の比較 |
| simplicial-cosimplicial の実現上の比較 | 1,500〜2,800 | 上記の A4 に必要な追加証明義務 |
| filtered 塔と A4 の利用側の成分の照合 | 300〜550 | shift と P⁰、正の π と π_0 の利用 |
| **新規計** | **5,500〜9,950** | |

全既存分を残しても **15,716〜20,166 行**という暫定見込みになり、
元の停止基準 29,000 行は上げない。③-b の一般の G10 の新規実装費を本レーンへ二重計上しないが、
本レーンの BE の模型への適用・指定射の照合は上の Tot・実現の行に含めた。
単に `_tot` の型を弱めて証明済みとする見込みではない。

実装の承認が出た場合の最初の区切りは、W→BE の型・巡回生成元・ν・D_0 の値まで。
その後は代表元独立性と加法性、局所化、Tot、外側の実現の順。
新しい範囲の段ごとの停止基準は、調整役が範囲を決めるときに設定する対象であり、
この表を自己承認の新たな枠として Lean を再開しない。

### 96.7 今回の判断点

成分の May 案を選ぶなら、(1) F_p の本欄＋一般 k は制限で読む補助、
(2) ho(CAlg) 上の可換群値 NatTrans、(3) coherent Sp 値の三つの補助出力は補完、
(4) A4 に必要な二重模型の実現比較を同じ BS 用の範囲へ含める、という切り方が候補。
新しい界面の変更も、May の Lean も今回は実施しない。
**この段 0 の紙の確認はここまで。承認を先取りせず、M15 の段 0 の続きへ進む。**


## 97. M15 の段 0 の続き：BE から dg 代数への最初の接続（紙のみ）

§95.2 の最初の検査を、今回の原典と現ソースの確認でさらに切り分けた。
[Berger–Fresse の冒頭の filtration の説明](https://arxiv.org/pdf/math/0109158#page=2)
では F₁E が結合的 operad である。この部分を使えば、
BE を可換 dg 代数と同一視せずに、通常の **結合的 dg 代数**への忘却を作る経路がある。
この源は現 BE 模型の内部の操作であり、BS のために一般の ∞-operad を新設する案ではない。

ただし現在の `homologyBinary` は `aritySection`（収縮の切断）から作られ、
`homologyBinaryAssociativityHomotopy` は二つの括弧付けの **ホモトピー**を供給する。
この宣言だけを `Mon (Complex A)` の厳密な結合則として使うことはできない。
標準の零単体の係数を使うか、選んだ切断がその係数に一致することを先に証明する。

最初の新規候補の型は次のとおり（紙の型案、未実装・未型検査）。
既存 `coefficientComposite` の添字 m,n,i と同じ規約を用いる。

```lean
standardCoefficient (A : Type u) [CommRing A] (n : ℕ) :
  𝟙_ (Complex A) ⟶ (operad A).arity n

standardCoefficient_unit :
  standardCoefficient A 1 = (operad A).unit

standardCoefficient_composite (m n : ℕ) (i : Fin (m + 1)) :
  coefficientComposite m n i
    (standardCoefficient A (m + 1)) (standardCoefficient A n) =
  standardCoefficient A (m + n)

barrattEcclesAssociativeForget (A : Type u) [CommRing A] :
  (operad A).Algebra ⥤ Mon (Complex A)
```

前二つの等式には零 arity の挿入を含める。これにより、同じ代数の作用へ入力した
μ と η の単位・結合則を **元の複体で**示し、全 BE 射の保存を束ねる。
`aritySection_augmentation`・`coefficientHomotopy` は既存の H⁰ の積との比較には使えるが、
標準係数の厳密な合成の等式をホモトピーだけで代用しない。

この接続ができた後は §95 の既存
`dgAlgebraDerivedInfinityCategory A B`・`dgAlgebraDerivedInfinityCategory_isStable`
を適用する。既存の模型は **右加群**なので、最初からその向きを明記する。
E∞ の高次の可換性から相対テンソルの左右の作用と対称性を供給する工程は、
結合的な忘却だけでは閉じない。

担当を決めるときに最初に受け渡すべき出力は、固定した X での圏だけでなく、
以下を同じ台の忘却と単位について保持したもの。

1. 全厳密 BE 射 f に対する dg 代数射と module の restriction/extension。
2. f が BE の弱同値のときの module ∞ 圏の同値と、同じ単位・台の比較。
3. native CAlg の全辺と合成への降下。
4. 一般の E∞ 頂点 R の相対テンソル、単位・結合性・対称性、および底変換。

1–3 を先の供給者、4 を利用側が別に作る分担も可能だが、
引数の型と同じ指定射を共有しないまま固定 R ごとの圏だけを受け取る形にはしない。
これは §95 の模型と相対テンソルの束の詳細化であり、見込みの行数へ追加加算しない。
一般 R 加群の 2,500〜4,500 行は、既存 dg module の再利用を前提にした暫定値のまま。
M15 の実装担当・界面・相対テンソルの供給者について、今回決定や変更はしていない。

**本ターンの変更は報告 §96〜97 のみ。M14 の Lean の停止は維持し、
M15 も段 0 の紙まで。** 型・範囲の判断を先取りする Lean の下書きも作っていない。

## §98　改訂 D79／May の最初の区切り（11-13）

ユーザー承認の §96.7・指示書 §26 に従い、May 経路を再開した。
main を math/bs-impl に取り込んだ（merge 5a94b4d6c）。界面・Assembly・drafts の
型は、局所化が済むまで変更しない。既存の 10,216 行は保存している。

### 98.1　今回の出力と登録候補

| モジュール（EInfinity/PowerOperation/） | 行数 | 出力 |
|---|---:|---|
| MayCyclicGroup | 75 | 置換群内の巡回部分群、右回転の生成元、位数と生成性 |
| MayNormalization | 58 | 単元としての ν(n)、全整数の指数 −n(p−1)、p=2 の規格化 |
| MayResolution | 66 | 巡回自由解像度 W、制限した BE の射影解像度、増大を保つ W→BE |
| MayZeroCoefficient | 78 | 同じ比較の零次係数、増大が 1、既存 aritySection とのホモトピー |
| MayRepeatedInput | 97 | 同じ代表射の反復入力と、単位を第二因子にした挿入の厳密な照合 |
| MayZeroOperation | 87 | 同じ D₀ の H⁰ 上の値が、既存の可換環構造の p 乗であること |
| 合計 | 461 | 新規 May 実装の実測 |

May, Definitions 1.2・2.1・2.2、Proposition 2.3 の規約を使う。
生成元は既存の加法的な +1 生成元の逆（右回転）を取った。
ν(n) は半階乗の単元の整数乗を使い、負の整数でも定義する。
W→BE は射影解像度の比較を使い、その同じ零次係数を作用へ入力した。
D₀ の計算は、増大が同じ二係数のホモトピーと既存の合成ホモトピーから得た。
全次数での代表元独立性・加法性・局所化を、この零次の計算で代用してはいない。

### 98.2　検証

六本すべての対象ビルドが通った。最後の MayRepeatedInput・MayZeroOperation の
ビルドは /tmp/bsw16/may-zero-operation-07.log、警告なし。
専用監査 /tmp/bsw16/audit-may-first.lean は **184 モジュール・1,495 宣言、
標準三公理のみ**で成功した。sorry・追加公理はない。
既存の公開宣言の型・定義、本体の入口、共通監査スクリプトは変更していない。
上の六本が調整役への登録候補である。

### 98.3　次と凍結への対応

最初の区切りを報告し、そのまま代表元独立性・加法性・自然性へ進む。
新規 461 行は、中間報告の約 10,000 行・停止外枠約 20,000 行に対する実測。
11-13 の凍結は予告段階で、18 時の確定連絡を待つ。
検証済みは夕方までにコミットし、凍結確定後の夜はコミットを控える。

## §99　May の零次の降下と全係数の境界（11-13、途中報告）

§98 の取り込み候補は **1908ec200** にコミットした。その後も承認済みの順序で続行。
今回の登録候補は同じ EInfinity/PowerOperation/ の次の二本。

| モジュール | 行数 | 証明したこと |
|---|---:|---|
| MayZeroHomology | 83 | 同じ D₀ の H⁰ への降下、代表射を選び直しても一致、全厳密 BE 射で自然、F_p 上で加法的 |
| MayResolutionCoordinates | 63 | 同じ W→BE の全係数 e_s の像と、境界のノルム／右回転の差の公式 |

零次の操作は、最初から Frobenius と定義するのではなく、同じ指定係数の作用へ
選んだ代表を入力して定義した。その値が p 乗という §98 の結果から、
代表元独立性を証明した。自然性は既存 homologyAlgebraFunctor の厳密射から得た。
加法性は二項定理と F_p の代数写像による `(p : H⁰ X) = 0` を使う。
H⁰ X が零環の場合も含み、その環で CharP p を無条件に要求しない。

全係数の境界は mayResolutionComparison の鎖写像の可換式を
`.single 1 1` で評価し、既存 regularHomEvaluation_action・_norm へ送って証明した。
新しい同変比較を仮定せず、零次と同じ増大付きの指定射を使っている。

対象ビルド：MayZeroHomology は /tmp/bsw16/may-second-01.log の当該対象成功、
MayResolutionCoordinates は /tmp/bsw16/may-coordinates-02.log で成功。最終ソースの警告なし。
専用監査 /tmp/bsw16/audit-may-new-two.lean は **2 モジュール・26 宣言、標準三公理のみ**。
§98 と合わせて May 新規 **607 行、8 モジュール・85 宣言**を監査済み
（§98 の全 184 モジュール・1,495 宣言に今回の 26 宣言を追加）。sorry・追加公理なし。

残りは、非零の係数次数での cycle、代表元独立性と混合入力による加法性、
全次数の自然性、ho(CAlg) への局所化である。零次での完了を全次数の完了とはしていない。
界面・Assembly・Shared/A4 は未変更、他レーンのファイルとの重複なし。
鍵は今回も各対象ビルド／各監査の間だけ取り、監査完了後に返却済み。
凍結確定の連絡はまだなく、検証済みのこの二本を報告とともにコミットする。

## §100　May の全次数の同次値・巡回不変性・閉性（11-13）

§99 の後も §26 の順で続行した。新規六本、562 行を検証した。

| EInfinity/PowerOperation/ の登録候補 | 行数 | 出力 |
|---|---:|---|
| MayRepeatedCycles | 78 | 全整数次数での同次反復入力、次数 n*q、閉性、全複体射での自然性 |
| MayRepeatedPermutation | 114 | 隣接交換と全置換の作用が sign(σ)^{q*q} になる厳密な等式 |
| MayHomogeneousAction | 119 | 同次 BE 作用の微分公式・二変数線形性・自然性・同時置換の等変性・閉性の判定 |
| MayCoefficientAction | 111 | 同じ実係数表現の作用との一致、生成元の差とノルムの評価、標数 p で係数境界の作用が零 |
| MayCyclicInputInvariant | 64 | 奇素数で巡回置換の符号が 1、標数 2 で整数単元の作用が恒等、反復入力の巡回不変性 |
| MayDValues | 76 | 同じ W→BE 比較による θ(e_s ⊗ a^{⊗p})、全厳密 BE 射に自然、閉入力から実閉元を作る |

May, Definition 2.1 の値を実際の作用で作った。全次数の閉性では、
係数の境界を §99 の同じ指定比較の境界公式へ戻している。
奇数段は生成元の差、偶数段はノルムで、前者は巡回不変性、後者は
p 倍のスカラーが零になることにより作用後に消える。正次数の係数を
零次の収縮で置き換えていない。全置換の符号は、同次純テンソル上の
実 Koszul 交換と隣接互換の生成性から証明した。

反復入力の次数は右括弧に沿う mayRepeatedDegree で保持し、
mayRepeatedDegree_eq が n*q と同定する。これは後の次数移送のための実装上の選択であり、
全複体の無限直和を有限積へ読み替えたり、複体の有界性を追加したりしていない。

対象ビルドは /tmp/bsw16/may-d-values-02.log で成功（最終ソースの警告なし）。
専用監査 /tmp/bsw16/audit-may-cycles.lean は **六本・89 宣言、標準三公理のみ**で成功。
sorry・追加公理はない。既存の宣言・入口・共通監査・界面・drafts は未変更。
May 新規の累計は **1,169 行**（前回 607 + 今回 562）、途中報告の約 10,000 行より下。
鍵は対象ビルドまたは監査の間だけ取り、最後の監査の鍵も返却済み。

次は P⁰ の次数を保つ添字・ν をこの閉元へ接続し、代表元独立性へ進む。
今回の出力は閉元と厳密射に沿う自然性までであり、全次数のホモロジー演算・加法性・
擬同型での不変性・ho(CAlg) への降下はまだ完了していない。
通常のテンソルのホモトピーを同変ホモトピーとして流用することはしない。
凍結は引き続き予告段階なので、検証済みの六本をコミットし、未検証分は分けて進める。

## §101　May の代表元独立性と規格化した P⁰ のホモロジー上の値（11-13）

§100 の六本は **67c62e9d2** にコミットした。その後、下記十一本・745 行を検証した。
今回も EInfinity/PowerOperation/ の新規ファイルのみであり、界面・Assembly・Shared/A4 の
移行は、加法性と局所化が済むまで保留している。

### 101.1　登録候補

| モジュール | 行数 | 出力 |
|---|---:|---|
| MayClosedCycles | 71 | 実微分の kernel、次数の移送、複体射の閉元への制限、指定 D_s の閉元と自然性 |
| MayPowerZeroCycles | 54 | i=−n(p−1) と ν(n) による規格化、全整数次数の P⁰ の閉元、正次数での零、自然性 |
| MayClosedHomology | 122 | 実 cycles・homology との比較、類写像の全射性、零類の境界判定、代表と自然性 |
| MayFreeProbeHomotopy | 49 | 既存の自由 probe のホモロジー関手は擬同型を反転し、鎖ホモトピックな射を同じ射に送る |
| MayProbeCycles | 51 | 同じ probe の自明 fibration による、元の閉元の厳密な持ち上げ |
| MaySphereHomotopy | 85 | 同じホモロジー類の二閉元の sphere 射の鎖ホモトピー、単位生成元の回収 |
| MayProbeEvaluation | 75 | 同じ単位・比較射・自由持ち上げによる評価、普遍閉元の厳密な回収と全ホモロジーでの一致 |
| MayDClasses | 65 | 全指定 D_s の実ホモロジー類・自然性・全次数の代表元独立性 |
| MayPowerZeroClasses | 72 | 規格化した P⁰ の実ホモロジー上の関数、代表元独立性、正次数で零、全厳密 BE 射で自然 |
| MayNormPolynomial | 44 | F_p[X] の (X−1)^{p−1}=∑_{i<p}X^i、非可換 F_p 代数への評価 |
| MayCyclicNorm | 57 | 同じ生成元の位数と冪による列挙、同じ巡回表現での T^{p−1}=N |

### 101.2　代表元独立性の接続

既存の **freeProbeFunctor** と **freeProbeFunctor_map_quasiIso** を再利用した。
自由 probe の全次数ホモロジー関手は、複体の擬同型を反転する。
Mathlib の **ComplexShape.QFactorsThroughHomotopy.areEqualizedByLocalization** と
**AreEqualizedByLocalization.map_eq_of_isInvertedBy** により、鎖ホモトピックな複体射は
この関手の下で厳密に同じホモロジー射になる。

二つの閉元の類が等しいとき、その差は元の複体の境界である。
**complexSphereHomEquiv**・**complexSphereToDisk_comp** と
**complexDiskContractingHomotopy** により、二つの sphere 射の鎖ホモトピーを作った。
同じ sphere の生成元を元の cofibrant probe へ厳密に持ち上げ、自由代数へ含める。
二つの評価射は上の意味で全ホモロジー上で一致するため、同じ普遍元の D_s の類を
二方向へ送った値が一致する。評価が元の入力を回収する等式は元の複体で証明した。
この結果が **mayDClass_independent** であり、規格化後の
**mayPowerZeroClass_independent**・**mayPowerZeroHomology** へ接続した。

この工程は、既存のモデル構造を使った実例側の証明である。
公開する主張に [ModelCategory SSet] を要求せず、実際の
projectiveModelCategory と BE の modelCategory を持つ既存の自由 probe を使った。
通常のテンソルのホモトピーを同変ホモトピーとして流用したり、
以前の未完成な positive-Hom/orbit の次数同型を鎖同型と仮定したりしていない。
既存の 10,216 行は保存している。native な orbit・norm・Tate は使っていない。

### 101.3　検証・現在の範囲

代表元比較の束は /tmp/bsw16/may-power-zero-classes-03.log で、
MayPowerZeroClasses まで成功した。ノルムの最終対象ビルドは
/tmp/bsw16/may-cyclic-norm-02.log で成功した。最終ソースの警告なし。
全 May モジュールを含む専用監査の結果は本節の末尾に記す。

新規 May の累計は **1,914 行**（前回 1,169 + 今回 745）。
途中報告の約 10,000 行・停止外枠約 20,000 行より下である。
mayPowerZeroHomology は、現段階では **ホモロジー上の自然な関数**であり、
まだ AddMonoidHom・ho(CAlg) 上の NatTrans には束ねていない。
零次の既存の p 乗計算と新しい全次数の関数の照合も、これから接続する。
界面の型を変更したとは報告しない。

### 101.4　次の加法性の接続

[May, Proposition 2.3(ii)](https://www.math.uchicago.edu/~may/PAPERS/10.pdf) を再確認した。
混合語の和 Δ(a,b)=(a+b)^{⊗p}−a^{⊗p}−b^{⊗p} を、巡回軌道代表の和 c のノルム Nc として表す。
既存 **cyclicBinaryTensorWord_fixed**・**cyclicBinaryTensorWord_orbit_injective** を再利用する。
残りは、同次の色付き入力の置換公式、反復入力の二項展開、
軌道代表での和の照合、および次の係数による境界表示である。
全ての入力の次数が同じなので、巡回置換の Koszul 符号は §100 と同じ理由で消える。

係数の次の段の微分が N の場合は、その係数に c を入力する。
微分が T の場合は、次の係数に T^{p−2} を作用させ、今回の
**mayCyclicNorm_eq** で T^{p−1}=N と照合する。
同時置換の等変性で係数のノルムと入力のノルムを移し、差が境界であることを示す。
加法性の証明後に可換群値の自然変換へ束ね、ho(CAlg) への局所化へ進む。
この段階の加法性そのものは未実装である。

### 101.5　監査完了・コミット時の状態

専用監査 **/tmp/bsw16/audit-may-all.lean** は **May の全25モジュール・320宣言、
標準三公理のみ**で成功した（/tmp/bsw16/audit-may-all.log）。
本体に sorry・追加公理なし、linter の抑制なし。監査の鍵も返却済み。
今回の十一本を報告とともにコミットする。新規ファイルだけなので他レーンとの重複なし。
共通の入口と監査への登録候補は §100・§101.1 の計十七本。
凍結の確定連絡はまだなく、検証済みを枝に保存した状態にする。


## 102. May の加法性・厳密自然変換・ho(CAlg F_p) への局所化（11-13）

### 102.1 今回閉じた主張

May, Proposition 2.3(i)(ii) の代表元独立性（§101）に、加法性を接続した。
**mayDClass_add** は全 s : ℕ・q : ℤ で、同じ指定 W→BE 比較による D_s の
実ホモロジー類が閉入力の和に加法的であることを示す。
**mayPowerZeroAddHom** は、規格化 ν と次数移送の後の P⁰ を、全整数次数の
実ホモロジーの可換群の準同型に束ねる。

**mayStrictPowerZero** は全厳密 BE 代数射に自然な可換群値の NatTrans。
**mayHomologySourceIso** は既存の忘却比較・厳密複体の全次数ホモロジー比較から、
全厳密代数への引き戻しを実ホモロジー関手と同定する。
**mayLocalizedPowerZero** は ho(CAlg F_p) の全射に自然な同じ P⁰。
**mayLocalizedPowerZero_source** により、源への引き戻しは同じ指定厳密演算の共役であり、
局所化で別の演算を選んでいない。
**mayLocalizedPowerZero_pos** は n > 0 の消滅を自然変換全体の等式で示す。

### 102.2 加法性の実装の筋

[May, Proposition 2.3(ii)](https://www.math.uchicago.edu/~may/PAPERS/10.pdf) の混合差の証明を使った。
二色語に対する隣接交換・一般置換の符号公式を元のテンソル複体で示し、
標数 p の巡回作用では符号が消えることを照合した。
混合語の自由巡回軌道と代表の和から Δ(a,b)=Nc を得る。

同じ W→BE 比較の次の係数に、必要なら T^{p−2} を作用させる。
§101 の T^{p−1}=N により、その微分は前の指定係数のノルムとなる。
実 BE 作用の同時置換の等変性で係数の norm と入力の norm を移す。
ノルム係数そのものが実境界なので、閉混合入力とのテンソルは零類である。
この最後の一般補助 **mayClosedTensor_class_zero_left** は sphere 射の実鎖ホモトピーを
テンソルして証明し、平坦性・有界性の仮定を追加していない。

使用した norm は有限群作用の線形写像の和であり、Sp の orbit・norm・Tate の模型は使わない。

### 102.3 登録候補（今回の新規十八本）

全て SerrePositivity/EInfinity/PowerOperation/ の下。

- MayColoredValues、MayWordAdjacent、MayHomogeneousSwap、MayColoredPermutation
- MayColoredCyclic、MayMixedWordOrbits、MayPureMixedWords、MayMixedInputNorm
- MayCoefficientNormTransfer、MayCoefficientPrimitive、MayClosedTensor、MayNormCoefficient
- MayDClassAdditivity、MayPowerZeroAdditivity、MayStrictNaturalTransformation
- MayHomologySourceComparison、MayLocalizedPowerZero、MayLocalizedPositive

新規十八本 **1,197 行**、検証済み May の累計 **3,111 行・43モジュール**。
約 10,000 行の途中報告・約 20,000 行の外枠より下。
共通入口と全体監査の登録は行っていない。他レーンと重なる既存 Lean ファイルへの変更なし。

### 102.4 検証と残り

対象ビルドは /tmp/bsw16/may-localized-05.log で、MayLocalizedPositive まで成功。
同じ一回のコマンドで追加検査した未検証補助 MayNormBaseField のみが失敗したため、
コマンド全体の終了値は 1 だった。原因は ZMod.castHom の引数（標数零の等式でなく
p ∣ p を要求）であり、当該補助だけ修正して後続で検証する。
検証済み十八本の新規警告は、letI を let に直して消した。依存先の既存の長行警告は残る。
専用監査の最終結果は本節の末尾に追記する。

局所化までの今回の本体は小さい宇宙の F_p に対するもの。
EInfinityTheory.{u} の基底環は Type u なので、界面の本欄に置く F_p は ULift して
同じ宇宙に置く必要がある。そのための素体別名・同じ係数の移送と規格化の補助は、
まだ未検証の下書きとして作業木に置き、今回の十八本とは分ける。
界面・Assembly・Shared/A4 の型の移行はまだ行っていない。

零次の以前の p 乗計算と全次数の P⁰ との照合、離散・cosimplicial の top operation、
_tot・filtered 塔・二重模型の実現比較は残る。最後の実現比較は指示どおり G10 の後。
旧 10,216 行は削除していない。凍結の確定連絡はまだない。


### 102.5 監査完了

/tmp/bsw16/audit-may-additive.lean は、検証済み **43モジュール・467宣言、
標準三公理のみ**で成功した（/tmp/bsw16/audit-may-additive.log）。
全宣言の公理を検査し、sorry・追加公理なし。監査の鍵も返却済み。
今回の十八本と本報告をコミットし、持ち上げた素体の補助の検証へ続ける。


## 103. D79 改訂の界面・Assembly・Shared/A4 への接続（11-13、取り込み点）

### 103.1 本欄と宇宙

**EInfinityPrimeField.{u} p := ULift.{u} (ZMod p)** を、模型に依存しない
Interface/PrimeField.lean に置いた。EInfinityTheory.{u} の基底環は Type u なので、
素体をその宇宙へ置くための同じ環の持ち上げである。
**eInfinityPrimeFieldEquiv** は元の ZMod p との環同型、
**eInfinityPrimeFieldMap p k** は一般の標数 p の k への標準構造射。
一般 k を界面の本欄へ戻す変更は行っていない。

界面の **homotopyGroupsOnHo k U n := hoMap U ⋙ additiveCohomologyOnHo k (-n)** を使い、
powerOp0 は次の型へ変更した。

```lean
powerOp0 (p : ℕ) [Fact p.Prime] (n : ℤ) :
  homotopyGroupsOnHo (EInfinityPrimeField.{u} p) (forget (EInfinityPrimeField.{u} p)) n ⟶
    homotopyGroupsOnHo (EInfinityPrimeField.{u} p) (forget (EInfinityPrimeField.{u} p)) n
```

通常の可換群値の NatTrans で、全整数 n・全 ho(CAlg) 射に自然。
_zero は pi0_forget の成分で p 乗を読む等式、_pos は n > 0 の成分が零の等式。
_discrete・_tot は F_p 上の Frobenius の自己射から誘導する写像との、
**全整数 n の加法群準同型の等式**であり、coherent な Sp 値の辺を要求しない。
型は §96.3 の案の素体を同じ宇宙に持ち上げたもの。
toSpectra とその二つの比較の欄は変更せず、旧 10,216 行も削除していない。

### 103.2 同じ規格化からの実例と一般係数での読み出し

素体の持ち上げに必要な係数計算を、F_p の多項式の等式を標準環準同型で移して示した。
**mayCyclicNorm_baseField**・**mayBaseFieldAdditivityCoefficient_boundary** から、
同じ閉元・境界・実作用の証明で **mayBaseFieldDClass_add** を得る。
これは持ち上げた素体にも使える係数計算の補助であり、一般 k の本欄を増やしていない。

**mayNormalizedClass** は同じ D_i を指定係数 c で規格化し、代表元独立性と加法性を証明する。
実例では c := ULift.up (mayNu p n : ZMod p) とし、全次数のホモロジー比較で局所化する。
**mayPrimeFieldPowerZero**・**mayPrimeFieldPowerZero_source**・**mayPrimeFieldPowerZero_pos** が
任意の宇宙の素体の全関手版と同じ指定演算の引き戻し・正次数消滅を与える。

実例の公開名は **barrattEcclesPowerOp0**・**barrattEcclesPowerOp0_pos**。
Assembly はこの二つを固定し、powerOp0 と powerOp0_pos の引数を外す。
残り十九欄のうち冪作用については _zero・_discrete・_tot の三つだけが引数に残る。
零次の旧 p 乗計算をまだ全次数の P⁰ に同定したとは主張しない。

一般 k の利用者のため、Interface/PowerOperation.lean に
**EInfinityTheory.restrictHomotopyGroupsIso** と **EInfinityTheory.powerOp0Over** を置いた。
前者は restrict_forget と restrictD_homologyIso を合成する自然同型。
後者は素体への制限に本欄を適用し、その自然同型で共役するだけの定義である。
新しい Sp 値の作用や新しい自然性の仮定を追加しない。
Interface/ には模型の直接 import・模型の API を使う宣言・[ModelCategory _] の欄を足していない。

### 103.3 drafts の移行

Shared/EInfinityPowerOperation の powerOperationZero は powerOp0Over の成分を
homotopyCohomology で共役して読む型へ移した。
離散・Tot の比較も、全整数次数のホモロジー写像と係数比較の成分の等式へ移した。
強い三出力 powerOperationZero_natTrans・_primeField・_component は、
本ファイルでは作らず補完へ回すことを明記した。
それらを要求する他の drafts の参照はなかった。

A4/Perfectoidization の Lemma 8.4(a) の証明の筋は、素体へ制限したホモロジー演算を使う形へ変更。
同じ shift の作用は可逆、正次数の P⁰ は零、係数比較で H^{-n} の消滅へ戻す。
二重模型の実現上の Frobenius 比較は A4 の局所補題として、G10 の後に残す。
Lemma 8.4(a)(b) の主張の型は変更していない。
A1 の二本・A0・A3 は触っていない。drafts はビルドしていない。

### 103.4 登録候補

本段の新規モジュールは次の十五本。

- EInfinity/Interface/：PrimeField、PrimeFieldMap、PowerOperation
- EInfinity/BarrattEccles/Theory/：MayPowerOperation
- EInfinity/PowerOperation/：MayNormBaseField、MayBaseFieldPrimitive、MayBaseFieldNormCoefficient、MayBaseFieldDClassAdditivity
- 同上：MayNormalizedClasses、MayNormalizedNaturalTransformation、MayNormalizedSourceComparison
- 同上：MayPrimeFieldLocalization、MayPrimeFieldPositive、MayZeroClassComparison、MayUnitEvaluation

最後の二本は、次の零次の接続に使う同じ類の表示と単位評価の補助。
新規十五本は 693 行、May*.lean の累計は 3,672 行。
新設の界面・実例四本は別に計132行（May の数に含めない）。既存四ファイルの差分は別記する。
本段も約 10,000 行の途中報告・約 20,000 行の外枠より下。
一般∞の五本の移動候補は、指示どおり元の場所のまま。
共通入口と全体監査への登録は行っていない。

### 103.5 検証と残り

may-interface-01.log で新しい界面・Assembly と直接の利用者 TheoryInterface のビルドが成功した。
may-interface-02.log で一般係数の補助・May の公開実例・正次数消滅まで成功した。
後続の最終 Assembly・単位評価・専用監査の結果は、本節の末尾に追記する。
既存の長行警告は残し、新規補助の非推奨名・未使用セクション引数は抑制せず修正した。

この取り込み点は界面の型の移行と P⁰・正次数消滅の供給であり、M14 全体の完了ではない。
残りは零次の p 乗との接続、離散、cosimplicial の top operation と _tot、filtered 塔、
および G10 の後の二重模型の実現比較。次は零次の同じ単位射の照合から続ける。


### 103.6 最終検証・取り込み点

**/tmp/bsw16/may-interface-03.log** で、P⁰ と正次数消滅を固定した Assembly と
MayUnitEvaluation の対象ビルドが成功した。新規十五本の最終ソースに新しい警告なし。
Assembly・Theory・依存先の既存の長行警告は残る。

**/tmp/bsw16/audit-may-interface.lean** は **60モジュール・638宣言、標準三公理のみ**で成功した
（/tmp/bsw16/audit-may-interface.log）。May の全54モジュールと、変更した界面・実例・Assembly を検査した。
本体に sorry・追加公理なし。Interface/ の模型直接 import と [ModelCategory _] の仮定は追加なし。
ビルドと監査は別々の一回の鍵で行い、どちらの鍵も返却済み。
root ビルド・全体監査・入口登録は調整役の取り込み時に委ねる。

**取り込み点**：本節の十五本・界面・Assembly・Shared/A4 の移行と報告をコミットする。
§100〜§102 と未登録分が重ならないよう、登録候補は各節の一覧を使ってほしい。
次の零次比較の MayRepeatedZeroInput.lean は未検証の新規下書きとして作業木に残し、
今回のコミットと監査には含めない。
凍結の確定連絡はまだなく、検証済みの分を18時前に保存した。


## 104. M14 の零次の照合（11-13）

### 104.1 厳密代数で閉じた計算

**MayRepeatedZeroInput** は、同じ同次反復入力を零次に移した値と、
単位複体からの同じ射を全入力へ入れた値の一致を示す。
**MayZeroActionEvaluation** は、同じ W→BE 比較の零次係数の単位射による評価と
全次数の mayHomogeneousAction の評価を照合する。

**MayNormalizedZero** で、全次数の mayNormalizedHomology の零次の値を、
以前の mayDZeroRepresentative_value に接続した。
mayNormalizedHomology_zero_value は、ν(0)=1 の指定演算について、
任意の厳密 BE 代数 X の実 H⁰ の環で x ↦ x^p であることを示す。
源の仮定は [Fact p.Prime]・[CharP k p] であり、H⁰ の環の非自明性は要求しない。
添字の等式を先に指定する mayNormalizedClass_index_view を使い、
依存する次数の移送を指定した。同じ元・同じ係数・同じ作用の厳密な照合である。

### 104.2 native な欄への接続の実装

**MayPiZeroSourceComparison** は、既存 barrattEcclesPi0_forget の構成を、
同じ mayNormalizedHomologySourceIso と照合する。
忘却前の加群値の比較を mayModuleHomologySourceIso として読み、台の加法群へ忘れると
同じ比較になることは定義上の等式である。
mayPiZeroForget_source_square とその各点の等式、および比較による冪の保存を証明した。
環構造は全て既存の homologyCommRing X であり、同じ H⁰ を返す関手の型に合わせて
局所インスタンスを明示しているだけである。

**MayZeroIsoTransport** は通常の圏の補助。
環値関手 P、可換群値関手 H、その指定自然同型、α : H ⟶ H に対し、
α が零次の環で p 乗を誘導する性質は、対象の同型に沿って運べる。
新たな coherent な Sp 値の出力や ∞ 圏の仮定は要求しない。

**MayPrimeFieldZeroSource** は、指定演算の源への引き戻しと ν(0)=1 を使って
上の厳密な計算を源へ運び、ordinaryAlgebraHoSource_isLocalization と
Mathlib の Localization.essSurj で全 ho(CAlg F_p) 対象へ移す実装である。
公開実例の欄の名前は **barrattEcclesPowerOp0_zero**（Theory/MayPowerOperationZero）。
この接続と公開欄は may-native-discrete-02.log でビルドが成功した。公理監査の結果は末尾に記す。

### 104.3 登録候補と検証の範囲

本段の登録候補は、次の七本。

- EInfinity/PowerOperation/：MayRepeatedZeroInput、MayZeroActionEvaluation、MayNormalizedZero
- 同上：MayPiZeroSourceComparison、MayZeroIsoTransport、MayPrimeFieldZeroSource
- EInfinity/BarrattEccles/Theory/：MayPowerOperationZero

対象ビルドのログは /tmp/bsw16/may-zero-input-01.log、may-normalized-zero-*.log、
may-native-zero-*.log。厳密な零次の計算と、π₀ の源の比較・冪の保存までは通っている。
本体の公理監査・公開欄の検証・最終実測・コミットは本節末尾へ追記する。
共通入口と全体監査への登録は行っていない。

離散の欄の MayPowerOperationDiscrete.lean も検証が通った。零次の計算と他次数のホモロジー消滅を使う
実装で、次節に記す。
18時までには、停止点に届かない場合も検証済みの分を保存する。


## 105. M14 の離散比較と Assembly（11-13）

### 105.1 全整数次数の離散比較

**barrattEcclesPowerOp0_discrete** を本体に置いた。
F_p 上の離散代数 B、環射 f : B → B、全ての元で f(a)=a^p という指定に対し、
**全整数 n** で同じ P⁰ がこの f によるホモトピー可換群の写像と一致する。

零次では、mayDiscretePiZero_frobenius が barrattEcclesPi0_discrete の自然性と環同型から
π₀ 上の f を p 乗と同定する。barrattEcclesPowerOp0_zero と
barrattEcclesPi0_forget の自然性で、同じ H⁰ の比較のもとの等式を得る。
零次以外では、既存 discreteCAlgUnderEmbedding_underlyingDisc による IsZero から
台の群を Subsingleton として二つの準同型の一致を示す。
新しいスペクトルの模型・G10・非自明性の仮定を使っていない。

登録候補は **EInfinity/BarrattEccles/Theory/MayPowerOperationDiscrete.lean** の一本。
§104 の七本と合わせて本段の新規は八本。
may-native-discrete-02.log で零次の公開欄と離散の公開欄まで成功した。

### 105.2 組み立て

Assembly は P⁰・零次・正次数・離散比較を全て構成済みのものに固定する。
**barrattEcclesTheoryOfRemaining の引数は十九欄から十七欄へ**減り、
冪作用に関して残るのは powerOp0_tot のみ。
_zero・_discrete を仮定に残した条件付きの供給とはしない。
他の未供給欄は従来どおり引数として残し、全 EInfinityTheory が無条件に出来たとは主張しない。
組み立ての最終ビルドと専用監査・実測・コミットの結果は末尾に追記する。

### 105.3 次の範囲

次は指示書 §26 の順で、cosimplicial の top operation と _tot、filtered 塔の照合、
最後に G10 の後の二重模型の実現比較。
今回の離散の比較から、全次数の演算が任意の Tot・実現と可換すると推論することはしない。
指定された BE 作用・規格化 ν・模型の比較を追う必要がある。


### 105.4 最終検証・保存

**/tmp/bsw16/may-native-discrete-02.log** で native な零次と全整数次数の離散比較が成功した。
**/tmp/bsw16/may-zero-discrete-assembly.log** で、それらを固定した Assembly の対象ビルドも成功した。
新規八本の最終ソースに新しい警告なし。依存先と Assembly の既存の長行警告は残る。

**/tmp/bsw16/audit-may-zero-discrete.lean** は、新規八本と Assembly の
**9モジュール・62宣言、標準三公理のみ**で成功した
（/tmp/bsw16/audit-may-zero-discrete.log、17:11 JST 確認）。
本体に sorry・追加公理なし。[ModelCategory SSet] などの仮定なし。
ビルドと監査はそれぞれ別の一回の鍵で行い、いずれも返却済み。
root ビルドと全体監査・入口登録は調整役に委ねる。

本段の新規八本は **559行**。May*.lean の累計は **4,128行**。
見込みの半分の約10,000行・外枠約20,000行より下である。
§104.3 の七本と §105.1 の一本を登録候補として報告する。
検証済み八本・Assembly・本報告を18時前にコミットして保存する。
凍結の確定連絡はまだ受けていない。

一般 k の補助 powerOp0Over について、この段で新たに示した性質はない。
Shared の一般 k の性質は drafts のままであり、係数制限のホモロジー比較と
π₀ の環比較の整合性も、その証明時に確認する必要がある。
今回の native な F_p の零次・離散比較は、それらの未証明の一般 k の性質を使っていない。

## 106. cosimplicial top operation：切断項の計算と、一般の BF 作用の不足（11-13）

### 106.1 今回の検証済み出力

main の零次・離散比較の登録 f63686a85 を枝へ取り込んだ。その後、
任意次元の単体に対する切断の支持を、既存の ShufflePath で構成した。
登録候補は次の三本（全て EInfinity/SimplexCuts/、計 **162行**）。

| モジュール | 行数 | 証明済みの出力 |
| --- | ---: | --- |
| Expanded | 77 | 切断の展開位置から (色,単体の頂点) への写像。非退化性をその単射性として定義し、同色の頂点列が狭義単調であること、頂点数の上界 |
| Balanced | 35 | top degree の頂点数の等式のもとで、各色の頂点数が q+1 であること |
| TopTerm | 50 | 各色の面写像が同じ q 単体の恒等射であり、一つの非退化切断項の積が X^q の環での a^r になること |

主な型は次のとおり（既に対象ビルドを通した宣言）。

```lean
colorPositions_card_of_top
    (h : Nondegenerate s u) (htop : m + q + 1 = r * (q + 1))
    (a : Fin r) : (colorPositions s u a).card = q + 1

fullColorFace_eq_id
    (h : Nondegenerate s u) (a : Fin r)
    (hcard : (colorPositions s u a).card = q + 1) :
    fullColorFace s u a hcard = 𝟙 ⦋q⦌

topTerm_eq_power (X : CosimplicialObject CommRingCat)
    (h : Nondegenerate s u)
    (hcard : ∀ a, (colorPositions s u a).card = q + 1)
    (a : X.obj ⦋q⦌) : topTerm X s u hcard a = a ^ r
```

r=p、語次数 d=q(p−1)、m+1=p+d の場合に頂点数の等式が成立する。
これは n=−q に必要な **同じ次数 q の各項の値**の計算である。
通常の cup 積によって次数を pq に移す操作ではない。
ただし、まだ符号付き総和の係数を 1 と示しておらず、May の同じ W→BE 比較を評価した
P⁰ の計算でもない。上の三本だけで n<0 の主張を完了と数えない。

TopTerm までの対象ビルドは /tmp/bsw16/simplex-top-term-02.log で成功。
専用監査 /tmp/bsw16/audit-simplex-cuts.lean は **3モジュール・18宣言、標準三公理のみ**で成功
（/tmp/bsw16/audit-simplex-cuts.log）。新しい警告・sorry・追加公理なし。
ビルドと監査は別々の一回の鍵で実行し、鍵を返した。共有入口・全体監査は変更していない。

### 106.2 G10 より前に必要なもの

§96.5 で注意したとおり、既存 IntervalCuts.cochainAction の入力は
Surjection.complex A r ⊗ interval A、出力は power (interval A) r であり、Δ¹ 専用である。
CochainActionComponents・CutSigns・CompositionCutSums も頂点／辺の分岐で証明しており、
q を引数として適用する形にはなっていない。
TableReduction.operadMap と Surjection の operad 自体は再利用できるが、
これらが任意の正規化 cosimplicial 複体に作用するという宣言は、別に供給しなければならない。
Assembly の ofCosimplicial と ofCosimplicial_forget も、現時点では未供給の引数である。

原典 [Berger–Fresse §2.2.6–7](https://arxiv.org/pdf/math/0109158#page=34) の一般の切断公式を
複体射と operad 作用へまとめた後で、TR に沿って同じ BE 作用に制限する必要がある。
同論文 §3.2.3–10 の suspension と係数の評価は top 計算への経路になるが、
既存の公開 API にその全次元版の比較はない。
また §3.2.5 の直後の注意のとおり、下の複体の Eilenberg–Zilber 比較を取るだけでは
BE 代数の比較を得たことにならない。複体の擬同型だけから同じ CAlg 対象とは報告しない。

不足を、次の順の証明義務として切り分ける。以下の bf* は **紙の新規名**で、
新たな仮定を本体に入れたものでも、型検査済みの宣言でもない。

```lean
-- 任意次元の単体の正規化鎖上の χ 作用。
bfSimplexAction (A : Type u) [CommRing A] (q r : ℕ) :
  Surjection.complex A r ⊗ bfSimplexChains A q ⟶
    power (bfSimplexChains A q) r

-- 微分・単位・置換・部分合成・単体の射での自然性を証明して作る。
-- この段では既存 interval 上の作用との一致も照合する。
bfNormalizedAlgebra (A : Type u) [CommRing A] :
  CosimplicialAlgebra A ⥤ (BarrattEccles.operad A).Algebra

bfNormalizedUnderlyingIso (A : Type u) [CommRing A] :
  bfNormalizedAlgebra A ⋙ Operad.Algebra.forget _ ≅
    bfNormalizedCochains A

-- 正規化から交代余面への、指定した自然な擬同型を保持する。
bfNormalizationComparison (A : Type u) [CommRing A] :
  bfNormalizedCochains A ⟶ cosimplicialCochains A

-- 厳密 BF 代数上で、指定係数の演算を直接評価する最終形。
-- κ は界面と同じ EInfinityPrimeField p。ν は mayNormalizationUnit の像。
bfMayTopValue (p : ℕ) [Fact p.Prime]
    (X : CosimplicialAlgebra κ) (n : ℤ)
    (a : MayClosed ((bfNormalizedAlgebra κ).obj X).carrier (-n)) :
  mayNormalizedClass p ((bfNormalizedAlgebra κ).obj X) n ν a =
    mayClosedClass _ (-n) (bfFrobeniusClosed X n a)
```

bfFrobeniusClosed は、同じ次数の a↦a^p が正規化した閉元を保つことを証明して作るもの。
ここを P⁰ の定義に置き換えるのではない。指定 W→BE を計算できる比較へ移す際も、
増大を保つ equivariant な鎖ホモトピーと、反復入力で T・N の項が消える計算を保持する。
ν の逆冪・逆巡回生成元・TR と BF の符号を一致させる必要がある。

同じ CAlg 対象との接続では、bfNormalizedAlgebra の nerve を既存の
algebraCAlgSource へ送った関手を具体的な ofCosimplicial の候補とし、
上の指定した正規化比較から ofCosimplicial_forget を供給する。
任意に選んだ ofCosimplicial と台の比較だけを仮定して、上の演算の一致を結論しない。
その候補と native な Tot の **指定錐・Frobenius の辺**との比較だけが G10 待ちである。
**今回まだ G10 の待ちの境界には到達していない。G10 の部品は作っていない。**

### 106.3 見込みの改訂と規模による中間停止

§96.6 の top operation と _tot の **1,000〜1,800行**は過小な見込みだった。
区間専用であることは §96.5 に記載済みだったが、一般の作用の微分・operad 法則を
再利用済みの部分に近く数えてしまっていた。今回、その証明の入力型を確認して修正する。
IntervalCuts の205本は約20,124行で、下の見込みはその全量を作り直す値ではない。
Surjection・TR・ShufflePath・テンソルの共通 API は再利用し、区間に特殊化した
切断の符号と境界・二段切断の証明を一般次元へ拡張する分を数える。

| 残る束 | 暫定の新規見込み | 再利用／不足の根拠 |
| --- | ---: | --- |
| 一般の切断、符号、正規化での消滅、微分、単体の射での自然性 | 3,000〜5,500 | ShufflePath・χ の微分・tensorLift は既存。IntervalCuts の頂点／辺の境界分類は一般次元版が必要 |
| 単位・置換・部分合成、TR による同じ BE 作用 | 3,000〜5,000 | χ と TR の operad は既存。二段切断と合成の全符号の比較は Δ¹ の証明を直接適用できない |
| 正規化した cosimplicial 代数の全関手と指定比較 | 1,200〜2,200 | Dold–Kan の複体の比較は再利用。BE 作用の保存と同じ CAlg の選択は未供給 |
| May の係数、ν、同じ次数での Frobenius の照合 | 1,200〜2,000 | 今回の各項の積と既存 May のホモトピー不変性を再利用。符号付き総係数は未証明 |
| native Tot の指定比較への適用（G10 自体を除く） | 500〜900 | 全整数 H/π と現在の source 比較を再利用 |
| A4 の二重模型の実現比較（G10 自体を除く） | 1,500〜2,800 | §96.6 の未完了分を保持 |
| filtered 塔・A4 の利用側 | 300〜550 | §96.6 の未完了分を保持 |
| **残り計** | **10,700〜18,950** | |

改訂 May の完成済み4,128行と今回162行を足すと、現時点の完成見込みは
**14,990〜23,240行**。これは必要行数の下界ではなく、現ソースからの暫定見込みである。
ただし上端が指示書 §26 の外枠約20,000行を超えるため、coordination.md §2 の
「上限を超えそうなときは報告して止める（止まる前に、それまでの検証済みの分をコミット）」
に従い、検証済みの三本を保存して **この線の Lean を中間停止**する。
実測が10,000行に達したという停止ではなく、一般 BF 作用を含めた残りの見込みによる停止。

界面・型・範囲は変更しない。一般の BF 作用の供給を含むこの経路の規模・分担を
調整役が判断できるように不足を明示し、代わりの作業である M15 の段0の紙を進める。
G10 の取り込みだけでこの不足が解消するとは報告しない。

## 107. M15 段0の続き：弱同値不変性の既存出力と restriction の条件（紙のみ、11-13）

M14 の §106 の規模停止の後、指定された代わりの紙の作業として §95・§97 を続けた。
M15 の Lean・界面・drafts の型は変更していない。一般 R 加群の担当も自己決定しない。

### 107.1 固定した厳密 BE 模型から既存 dg 加群へ

最初の不足は §97 の barrattEcclesAssociativeForget A のまま。
標準零単体の単位・合成を元の圏で照合して、台を変えずに Mon (Complex A) へ送る。
ホモロジー上の結合性や BE→Comm の増大は、この厳密な忘却の代用にならない。
以下で B_X はその関手の X での値とする。

その後の固定 X の型と、全厳密 BE 射 f による拡大については、
新しい module ∞ 圏を最初から構成する必要はない。既存宣言を確認した。

| 宣言（InfinityCategories/Project/DerivedCategories/） | 確認した仮定・出力 |
| --- | --- |
| dgAlgebraDerivedInfinityCategory A B_X | B_X 上の右半自由 dg 加群の dg nerve |
| dgAlgebraDerivedInfinityCategory_isStable | 同じ圏の安定性。B_X の可換性を仮定しない |
| dgAlgebraExtensionInfinity A g | dg 代数射 g:B_X→B_Y に対する実 ∞ 関手 −⊗ᴸ_{B_X}B_Y |
| dgAlgebraExtensionInfinity_isExactFunctor | その実 ∞ 関手の完全性。A 上の平坦性を追加しない |
| dgAlgebraMap_quasiEquivalence | QuasiIso g.hom から同じ一対象 dg 関手の準同値 |
| dgAlgebraExtensionInfinity_isQCatEquivalence_of_quasiIso | QuasiIso g.hom から同じ拡大関手の実 ∞ 圏同値 |

最後の二つは DGAlgebraMoritaInfinity.lean に証明済みで、Morita 同値を新たな仮定にする必要はない。
特に §95 の「BE の弱同値に対する module 圏の同値」の **厳密な一辺での部分**は、
台を変えない忘却が完成すれば、この宣言へ直接帰着できる。
新しい紙の候補の型は次の形となる（assocForget はまだ未供給、未型検査）。

```lean
strictModuleExtend {X Y : (operad A).Algebra} (f : X ⟶ Y) :
    dgAlgebraDerivedInfinityCategory A (assocForget.obj X) ⟶
    dgAlgebraDerivedInfinityCategory A (assocForget.obj Y) :=
  dgAlgebraExtensionInfinity A (assocForget.map f)

strictModuleExtend_weak {X Y : (operad A).Algebra} (f : X ⟶ Y)
    (hf : QuasiIso f.hom) : IsQCatEquivalence (strictModuleExtend f)
```

hf は忘却の台の一致を介して同じ dg 代数射の QuasiIso へ運ぶ。
ただし、この一辺の同値性だけでは、native CAlg の全辺と合成に対する module 圏の族を
降下したことにはならない。拡大の合成・恒等比較と、その coherence を保つ降下は残る。
既存 dgModuleExtensionYonedaNerveIso は全関手の比較に利用できるが、
変わる BE 代数を含む全族をこれだけで供給しているとは数えない。

### 107.2 restriction と随伴で残る型の条件

通常の閉零射の圏では DifferentialGraded.dgModuleExtensionRestrictionAdjunction が
既に graph 拡大と moduleRestriction の随伴を与えている。
ただし native な半自由模型で右随伴を作るときは、次の条件を飛ばせない。

DGModuleDerivedFunctor.lean の dgModuleDerivedFunctor とその comparisonIso は、
入力の dg 関手 F に対して

```lean
hF : ∀ M, dgModuleProjectiveProperty A D M →
  dgModuleProjectiveProperty A E (F.obj M)
```

を要求する。一般の B_X→B_Y の restriction に、この条件を無条件で入れることはできない。
例えば B_Y 自身は自由な右 B_Y 加群でも、B_X 上の dg 射影的な加群であるとは限らない。
したがって「既存 dgModuleDerivedFunctor を restriction にそのまま適用」で
native な右随伴を供給したとはしない。

受け渡しでは、restriction が擬同型を保つことに沿う局所化、または restriction の後の
指定した解像度との比較を含め、実 ∞ 関手としての右随伴を要求する。
通常圏の随伴の単位・余単位を、その指定した比較で native に運び、三角形を照合する。
この不足は §95 の 700〜1,400行の「台・単位・全 restriction/extension・弱同値不変性」
に含める対象であって、その上へ別枠として二重加算しない。

### 107.3 分担時の受け取り条件と見込み

HA の地図の 4.2.1.15・4.5.2.1 は通常圏の場合の部分一致、4.5.3.1 は未供給という判定のまま。
一般 R の模型の供給者からは、固定 X の安定圏だけでなく、少なくとも次を同時に受け取る必要がある。

1. 同じ台と単位を持つ厳密 BE→dg 代数の忘却。
2. 全厳密射の拡大・制限の実 ∞ 関手、随伴、恒等・合成比較。
3. 弱同値での上記の同値と、native な CAlg の辺・合成への降下。
4. 同じ一般 R 加群の相対テンソルと、その単位・結合性・対称性・底変換。
5. M15 の指定した R→S の辺、その fiber と指数射を、この同じ単位とテンソルで読む比較。

§95 の一般 R の束の2,500〜4,500行は暫定のまま。今回、厳密な拡大の弱同値不変性は
既存宣言で済むことを明確にした一方、restriction の hF を省略できないことも明記した。
相対テンソルの対称性を結合的 dg 代数への忘却だけから供給したとはしない。
担当と受け渡す全関手の型を決める前に、この見込みを実装承認や完了数へ読み替えない。

**保存**：§106 の検証済み三本と報告は 9f27a22de に17:54 JSTにコミットした。
本節は紙のみの追記。凍結確定の連絡はまだ受けていない。

## 108. 5a-5a：一般 BF 作用の固定した型一覧（11-13、実装前の紙）

### 108.1 範囲・数え方・構成

§106 に対するユーザー承認に従い、上の三行を共通の **5a-5a** として切り出す。
見込み7,200〜12,700行、外枠25,400行。M14 の残り四行・native Tot・G10 は含めない。
置き場所は EInfinity/SimplexCuts/ と新設 EInfinity/Cosimplicial/。
既存 IntervalCuts/・Operad/ の公開定義は変えない。共有入口と全体監査への登録は調整役に委ねる。
他レーンの同じ新規ファイルを発見した場合は編集前に止めて報告する。

数え方は inf-supply-w2.md §14 と、今回のユーザー指示のとおり。
下の L01〜L28 が新しい数学の一覧。**証明の分割は数えず、型を追記する。
前提計算（既存構成の単位・自然性・係数移送の法則）は各 L ごとに3本まで。
照合は I01〜I03 の全体3本まで。それ以外の新しい数学は型と漏れた理由を報告して止める。**
定義を作る際の恒等・合成のフィールドも下の法則に含める。
「構造を引数に要求する」ことで下の法則を仮定に逃がさない。

構成は次の二層に分ける。

- 一般の単体集合の正規化鎖 C_A(S) 上に χ の切断余作用を構成し、TR:E→χ に沿って制限。
- 標準単体 Δ[q] のその余代数と X^q の離散 BE 代数から、既存 convolutionAlgebra を作る。
  ∏q Hom(C_A(Δ[q]),disc(X^q)) のうち、全 α:q→r で前合成と後合成が一致するものを、
  **通常の BE 代数の等化子**として取る。この台と正規化したコチェイン複体を同定する。
  native な ∞ 圏の Tot・錐の比較はここでは作らない。

後半の convolutionFunctor・convolutionPre/Post と Operad.AlgebraLimits は再利用する。
一般次元の cochain の operad 法則をもう一度直接証明する経路にはしない。

### 108.2 型のために固定する定義と記号

以下は **紙の Lean 型案、未型検査**。未供給名は新規定義として構成するもので、公理・仮定ではない。
`A : Type u [CommRing A]`、`S T : SSet.{0}`、`X Y : CosimplicialAlgebra A` とする。
`C S := (BarrattEccles.normalizedFunctor A).obj S : Complex A`。
`χ := Surjection.operad A`、`E := BarrattEccles.operad A`。
`cmap f := (BarrattEccles.normalizedFunctor A).map f`。
`gen S q x : (C S).X (-(q:ℤ))` は既存の normalized generator を extend の同型で運んだもの。

組合せの入口では `s : Cut m q`、`u : Surjection.Word r (m+1)`。
`colorPositions s u.val a` は §106 の定義をそのまま使う。
`vertices s u a` は、その順序列を s.vertical で読む OrderHom。
`outputDegree s u a := (colorPositions s u.val a).card-1`。
`face s u a : ⦋outputDegree s u a⦌ ⟶ ⦋q⦌` はその単調写像。
空の色がないことは L01 で証明する。非退化性がなくても face は定義する。
`lo s i`・`hi s i` は水平座標 i の fiber の最初・最後の垂直座標。

BF §2.2.3–6 の符号は次の定義で固定する。

```lean
intervalLength s u i := hi s i - lo s i + if Surjection.Caesura u.val i then 1 else 0
permutationExponent s u := ∑ i, ∑ j,
  if i < j ∧ u.val j < u.val i then intervalLength s u i * intervalLength s u j else 0
positionExponent s u := ∑ i, if Surjection.Caesura u.val i then hi s i else 0
cutSign s u : ℤ := (-1) ^ (permutationExponent s u + positionExponent s u)
```

`cutTensor A S s u x` は、各色の `gen S _ (S.map (face s u a).op x)` の
既存テンソル冪への純粋テンソル。総次数は L02 で合わせる。
`cutTerm` は cutSign 倍の cutTensor、`cutSum` は全 s に関する和。
退化な face は normalized generator によって零となるため、符号の定義を変えずに保持する。
`rawComponent` は係数の自由基底と単体の自由基底から線形拡張した切断和。
`component` は L07 により正規化へ降ろし、整数次数へ延長した双線形成分。

余単体的正規化の入口は `N X : Complex A` とし、
`(N X).X (q:ℤ)` を全 codegeneracy σ_i の核の共通部分、負次数を零とする。
微分は交代余面の和の制限。`normInclusion X : N X ⟶ cosimplicialCochains A |>.obj X`。
これは P⁰ や levelwise Frobenius を用いて定義するものではない。

`P_X := ∏q convolutionAlgebra (hopf A) (simplexBECoalgebra A q) (discAlg(X^q))`。
`Q_X := ∏(α:q→r) convolutionAlgebra (hopf A) (simplexBECoalgebra A q) (discAlg(X^r))`。
`post_X, pre_X : P_X ⟶ Q_X` は各 α における後合成と前合成。
`bfNormalizedAlgebra.obj X := equalizer post_X pre_X`、射は L22 による。
台の族の次数 k を評価するとき、内部 Hom の微分の符号を保持する。
正次数 k の評価と N X の比較には `(-1)^(k*(k+1)/2)` の次数ごとの係数を入れ、
その微分の式を L24 で証明する。符号を省いた評価を複体射と主張しない。

### 108.3 残る数学の型一覧：切断と余作用

以下の `u` の引数は上の Word、degree d の際は BasisWord へ特殊化する。
総次数の eqToHom は L02 が供給する等式で統一する。arity零は L14 で別に処理する。

```lean
-- L01 色の出現と非空性。
colorPositions_nonempty (s : Cut m q) (u : Surjection.Word r (m+1)) (a : Fin r) :
  (colorPositions s u.val a).Nonempty

-- L02 各色の頂点数と全出力次数（非退化性を前提にしない）。
outputDegree_sum (s : Cut m q) (u : Surjection.Word r (m+1)) :
  ∑ a, outputDegree s u a = m + q + 1 - r

-- L03 面の非退化性と §106 の対の単射性の同値。
faces_mono_iff (s : Cut m q) (u : Surjection.Word r (m+1)) :
  (∀ a, Mono (face s u a)) ↔ Nondegenerate s u.val

-- L04 退化な切断項は実テンソルで零。
cutTensor_eq_zero (h : ¬Nondegenerate s u.val) (x : S _⦋q⦌) :
  cutTensor A S s u x = 0

-- L05 正規化生成元と色ごとの面の引き戻しを保つ自然性。
cutTerm_map (f : S ⟶ T) (x : S _⦋q⦌) :
  (TensorPowers.map (cmap f) r).f _ (cutTerm A S s u x) =
    cutTerm A T s u (f.app _ x)

-- L06 切断和の生成元公式（rawComponent の線形拡張の値）。
rawComponent_value (u : Surjection.BasisWord (r+1) d) (x : S _⦋q⦌) :
  rawComponent A S (r+1) d q (Surjection.basis A u) (ModuleCat.freeMk (ULift.up x)) =
    cutSum A S u x

-- L07 入力の退化を消す。標準単体の退化も、一般 S の退化も含む。
cutSum_degenerate (u : Surjection.BasisWord (r+1) d)
    (i : Fin (q+1)) (x : S _⦋q⦌) :
  cutSum A S u (S.σ i x) = 0

-- L08 正規化した成分でも同じ切断和を復元。
component_generator (u : Surjection.BasisWord (r+1) d) (x : S _⦋q⦌) :
  component A S (r+1) (-(d:ℤ)) (-(q:ℤ)) _ (by omega)
    (Surjection.complexBasis A u) (gen S q x) = cutSum A S u x

-- L09 微分の項ごとの切断和の等式。q=0,d=0 の境界も含む。
-- boundaryCoefficient / boundarySimplex は既存の χ の微分／交代面和。
cutSum_boundary (u : Surjection.BasisWord (r+1) d) (x : S _⦋q⦌) :
  dTensor (cutSum A S u x) =
    cutSumLinear A S (boundaryCoefficient u) x +
      (-1 : ℤ)^d • cutSumLinearSimplex A S u (boundarySimplex x)

-- L10 全整数の双線形 Leibniz 則。
component_d (r : ℕ) (i j : ℤ)
    (a : (χ.arity r).X i) (b : (C S).X j) :
  (power (C S) r).d (i+j) (i+j+1) (component A S r i j _ rfl a b) =
    component A S r (i+1) j _ (by omega) ((χ.arity r).d i (i+1) a) b +
      i.negOnePow • component A S r i (j+1) _ (by omega) a ((C S).d j (j+1) b)

-- L11 置換に対する全切断和の Koszul 符号。
cutSum_permutation (σ : Equiv.Perm (Fin r)) (u : Surjection.BasisWord r d)
    (x : S _⦋q⦌) :
  cutSum A S (Surjection.rename σ u) x =
    ((permutationAction (C S) r σ).asIso.hom).f _ (cutSum A S u x)

-- L12 二段の切断と合成語の切断の同じ実テンソルでの一致。
-- compositeCutSum は既存 OverlapPartition と compositionSign の有限和。
-- nestedCutSum は外側の色の一つを内側の切断で置き換えた有限和。
cutSum_composite (u : Surjection.BasisWord (m+1) d)
    (v : Surjection.BasisWord n e) (i : Fin (m+1)) (x : S _⦋q⦌) :
  compositeCutSum A S u v i x = nestedCutSum A S u v i x

-- L13 unary の単位切断。q は任意。
cutSum_unit (x : S _⦋q⦌) :
  cutSum A S Surjection.unitWord x = (oneIso (C S)).inv.f _ (gen S q x)

-- L14 nullary の余作用と、nullary を含む部分合成。
coaction_nullary : coaction A S 0 =
  (nullaryCoefficient A ⊗ₘ chainsAugmentation A S) ≫ (λ_ (𝟙_ (Complex A))).hom
coaction_comp_nullary (m : ℕ) (i : Fin (m+1)) :
  (χ.comp m 0 i ▷ C S) ≫ coaction A S m =
    ((β_ (χ.arity (m+1)) (χ.arity 0)).hom ▷ C S) ≫
    (α_ _ _ _).hom ≫ (χ.arity 0 ◁ coaction A S (m+1)) ≫
    tensorCoInsertionAction (C S) (χ.arity 0) m 0 i (coaction A S 0)

-- L15 全整数の余作用の自然性。正規化生成元上の L05 から。
coaction_natural (f : S ⟶ T) (r : ℕ) :
  (χ.arity r ◁ cmap f) ≫ coaction A T r =
    coaction A S r ≫ TensorPowers.map (cmap f) r

-- L16 正の内側 arity の、実複体射の全部分合成則。
coaction_comp (m n : ℕ) (hn : 0<n) (i : Fin (m+1)) :
  (χ.comp m n i ▷ C S) ≫ coaction A S (m+n) =
    ((β_ (χ.arity (m+1)) (χ.arity n)).hom ▷ C S) ≫
    (α_ _ _ _).hom ≫ (χ.arity n ◁ coaction A S (m+1)) ≫
    tensorCoInsertionAction (C S) (χ.arity n) m n i (coaction A S n)

-- L17 実複体射の等変性・単位（L11,L13 の線形拡張）。
coaction_equivariance (r : ℕ) (σ : Equiv.Perm (Fin r)) :
  (χ.sequence.map (FiniteBijection.permutation r σ) ▷ C S) ≫ coaction A S r =
    coaction A S r ≫ (permutationAction (C S) r σ).asIso.hom
coaction_unit : (χ.unit ▷ C S) ≫ coaction A S 1 ≫ (oneIso (C S)).hom = (λ_ (C S)).hom

-- L18 作用の式を保持して TR による BE 余代数と自然な射へ束ねる。
bfCoalgebra_coaction (r : ℕ) : (bfCoalgebra A S).coaction r =
  ((TableReduction.operadMap A).map.app (FiniteBijection.of r) ▷ C S) ≫ coaction A S r
bfCoalgebraMap_comm (f : S ⟶ T) (r : ℕ) :
  (E.arity r ◁ cmap f) ≫ (bfCoalgebra A T).coaction r =
    (bfCoalgebra A S).coaction r ≫ TensorPowers.map (cmap f) r
```

L09・L12 は境界項の相殺・二段切断の有限添字対応を証明に含む。
退化切断も零として同じ和に保持する。端点・同色の接着・空区間・arity零を捨てない。
L06,L08 の basis 名は現在の自由加群の実 API に合わせて定義する略記であり、
基底の存在や正規化への降下を別の未証明仮定にしない。

### 108.4 残る数学の型一覧：正規化した cosimplicial 代数

```lean
-- L19 正規化部分加群を交代余面の微分が保つ。
normalized_d_mem_exact (q : ℕ) (a : normalizedComponent X q) :
  ∀ i : Fin (q+1), (X.σ i).hom (alternatingCofaces X q a.val) = 0

-- L20 正規化包含の微分・自然性。
normInclusion_d (i j : ℤ) :
  (N X).d i j ≫ (normInclusion X).f j =
    (normInclusion X).f i ≫ ((cosimplicialCochains A).obj X).d i j
normInclusion_naturality (f : X ⟶ Y) :
  (Nmap f) ≫ normInclusion Y = normInclusion X ≫ (cosimplicialCochains A).map f

-- L21 正規化包含の指定ホモトピー逆。余単体的な Dold–Kan の分解を使う。
normalizationHomotopyEquiv (X : CosimplicialAlgebra A) :
  HomotopyEquiv (N X) ((cosimplicialCochains A).obj X)
normalizationHomotopyEquiv_hom : (normalizationHomotopyEquiv X).hom = normInclusion X

-- L22 convolution の等化子への全 X 射。二つの自然性の長方形。
post_naturality (f : X ⟶ Y) : Pmap f ≫ post_Y = post_X ≫ Qmap f
pre_naturality (f : X ⟶ Y) : Pmap f ≫ pre_Y = pre_X ≫ Qmap f
bfNormalizedAlgebra_map_id (X) : bfMap (𝟙 X) = 𝟙 _
bfNormalizedAlgebra_map_comp (f : X ⟶ Y) (g : Y ⟶ Z) : bfMap (f ≫ g) = bfMap f ≫ bfMap g

-- L23 等化子の斉次元を恒等 q 単体で読む評価とその逆。
evaluation_mem (q : ℕ) (a : bfCarrier X |>.X (q:ℤ)) :
  scaledEvaluation X q a ∈ normalizedComponent X q
reconstruction_evaluation (q : ℕ) (a : bfCarrier X |>.X (q:ℤ)) :
  reconstruct X q (scaledEvaluation X q a) = a
evaluation_reconstruction (q : ℕ) (a : normalizedComponent X q) :
  scaledEvaluation X q (reconstruct X q a) = a
bfCarrier_isZero_negative (i : ℤ) (hi : i<0) : IsZero ((bfCarrier X).X i)

-- L24 評価の次数係数と微分の比較。符号なしの評価ではない。
evaluation_d (i j : ℤ) :
  (bfCarrier X).d i j ≫ evaluationComponent X j =
    evaluationComponent X i ≫ (N X).d i j

-- L25 同じ評価の全 X 射での自然性。
evaluation_naturality (f : X ⟶ Y) (i : ℤ) :
  (bfMap f).hom.f i ≫ evaluationComponent Y i =
    evaluationComponent X i ≫ (Nmap f).f i

-- L26 全関手の台の同型と指定された正規化比較。
bfNormalizedUnderlyingIso :
  bfNormalizedAlgebra A ⋙ Operad.Algebra.forget E ≅ bfNormalizedCochains A
bfNormalizationComparison : bfNormalizedCochains A ⟶ cosimplicialCochains A
bfNormalizationComparison_app : (bfNormalizationComparison A).app X = normInclusion X
bfNormalizationComparison_quasiIso (X) : QuasiIso ((bfNormalizationComparison A).app X)

-- L27 構成した代数の作用の、各 q への射影の評価公式。
-- wedgeProjection は等化子から同じ convolution 代数への射。
bfAction_projection (r q : ℕ) :
  ((bfNormalizedAlgebra A).obj X).action r ≫ (wedgeProjection X q).hom =
    (𝟙 _ ⊗ₘ TensorPowers.map (wedgeProjection X q).hom r) ≫
      (simplexConvolution X q).action r

-- L28 同じ作用を正規化コチェインの元で読む明示的な BF 切断公式。
-- lhs は L26 の同型で運んだ「実際の」BE作用。rhs は TR の実係数を用いた切断和。
bfAction_formula (r d : ℕ) (e : (E.arity r).X (-(d:ℤ)))
    (degrees : Fin r → ℕ) (a : ∀ c, normalizedComponent X (degrees c)) :
  normalizedActionValue X e degrees a = bfCutEvaluation X e degrees a
```

L19 の codegeneracy の添字は Fin(q+1)。
L14 の nullaryCoefficient A : χ.arity 0 ⟶ 𝟙_ (Complex A) は、
Surjection.zeroAugmentation と正次数の基底が空であることから定義する同じ係数射。
χ 全体の operad augmentation の存在は仮定しない。
L21 の複体のホモトピー同値には Mathlib の Dold–Kan の分解を反対圏で用いる。
L23 の reconstruction は、各 q 単体の単射 θ:[k]→[q] の生成元を X.map θ の像へ送り、
非単射 θ は零とする式。全 α の自然性と codegeneracy の核の条件の同値もこの主張に含む。
L28 の出力次数は ∑c degrees c−d、負なら零。r=0・d=0 の単位の式も含める。
ここで Frobenius・ν・May の P⁰ の係数の総和はまだ計算しない（M14 側の残り）。

### 108.5 照合の三枠と既存の再利用

I01 は区間の版との必須の照合として予約する。

```lean
-- I01 Δ¹ の同じ正規化鎖の同型に沿う、全部分余作用の厳密な一致。
intervalCoaction_compare (r : ℕ) :
  (χ.arity r ◁ intervalCarrierIso A |>.hom) ≫ IntervalCuts.cochainAction A r =
    coaction A Δ[1] r ≫ TensorPowers.map (intervalCarrierIso A).hom r
```

intervalCarrierIso は定義的に同じ場合は Iso.refl、extend の表現差があればその既存の標準同型。
BE の方は、この同じ式に TableReduction.operadMap を前置した帰結とし、別の新規数学には数えない。
I02・I03 は未使用のまま残す。二項 AW や別の模型の比較を便利さだけで追加しない。

再利用する既存宣言：ShufflePath.horizontal_surjective、vertex_strictMono_on_color、
AlexanderWhitney.generator_map_of_not_mono、normalization_restrictToNormalized、
既存 tensorLift・ι_tensorLift、Surjection の complexPartialComposition と compositionOnWords、
Operad.restrictCoalgebraObj、convolutionAlgebra・convolutionPre・convolutionPost、
AlgebraLimits、Mathlib Dold–Kan の normalized/alternating のホモトピー同値。
[原典 BF §2.2.3–7](https://arxiv.org/pdf/math/0109158#page=33) の一般の切断と符号を用いる。
証明の順は L01〜L18 → I01 → L19〜L28。定義・既存構成の組み立ては依存順に挟む。
完成時が調整役への取り込み点。検証済み小束は枝に保存するが、native Tot の完了とはしない。

### 108.6 実装に伴う証明分割の型と計数（進行中）

L01〜L03 は Outputs・Faces の対象ビルドに成功した（simplex-faces-01.log）。
L04〜L06 は同じ一覧の範囲で実装中。検証中のファイルはまだコミットしていない。
型一覧と数え方の紙は **18ca0ea4a** に保存済み。

証明分割の補題は次の型。L02 の頂点数の分割、L03 の狭義単調性、
L04 の零因子の消滅は、それぞれ一覧の主張の同じ証明を分けたもの。

```lean
-- L02 の分割（検証済み）。
colorPositions_card_eq s u a : (colorPositions s u.val a).card = outputDegree s u a + 1
colorPositions_card_sum s u : ∑ a, (colorPositions s u a).card = m + q + 1
-- L03 の分割（検証済み）。
vertices_strictMono (h : Nondegenerate s u.val) (a : Fin r) : StrictMono (vertices s u a)
-- L04 の分割。
tensorValue_eq_zero (K : Complex A) (n : ℕ) (d : Fin n → ℕ)
  (v : ∀ i, K.X (-(d i:ℤ))) (i : Fin n) (h : v i = 0) : tensorValue K n d v = 0
-- L07 の分割：入力で一つの退化を合成すると、少なくとも一つの色の面が退化する。
face_comp_sigma_not_mono (s : Cut m (q+1)) (u : Surjection.Word r (m+1))
  (i : Fin (q+1)) : ∃ a, ¬Mono (face s u a ≫ SimplexCategory.σ i)
```

L05 の前提計算は次の三本で **3/3**。新しい構成や新しい数学の枠には拡張しない。

```lean
gen_naturality f q x : (cmap f).f (-(q:ℤ)) (gen A S q x) = gen A T q (f.app _ x)
tensorValue_map f n d v : (TensorPowers.map f n).f _ (tensorValue K n d v) =
  tensorValue L n d (fun i => f.f _ (v i))
component_index_naturality (f : K ⟶ L) (h : i=j) (x : K.X i) :
  f.f j ((eqToHom (congrArg K.X h)).hom x) =
    (eqToHom (congrArg L.X h)).hom (f.f i x)
```

lo・hi の定義に用いる intervalPositions_nonempty は、L01 の既存の horizontal_surjective
の評価を切り出したもの。照合 I01〜I03 はまだ0/3、その他の L の前提計算も0/3。
凍結確定の連絡はまだ受けていない。

## 109. L09 の境界計算で一覧外と判定した数学（11-13、型の報告）

L01〜L08 の実装・検証を進める間に、次の L09 の有限和の証明を具体化した。
一般次元では、テンソルの出力面の削除・χ の文字の削除・入力単体の面の削除を
対応させ、残る境界項を符号を反転させて対にする必要がある。
既存 IntervalCuts のその対応は頂点／辺に特殊化されている。
**§108 の一覧は境界の総和の等式だけを L09 に書き、この対応の構成を型に落としていなかった。**

必要と判断した追加候補は次の型。以下は紙のみで、Lean の定義・証明は追加していない。
`u : BasisWord (r+1) d`、`u' := positiveWord u` とする。
全ての退化項・境界次数零の項も零として残した有限添字を使う。

```lean
abbrev BoundaryBalanceIndex (u : Surjection.BasisWord (r+1) d) (q : ℕ) :=
  (Σ s : Cut (r+d) q, Σ a : Fin (r+1), Fin (outputDegree s (positiveWord u) a + 1)) ⊕
  ((Fin (r+d+1) × Cut (r+d-1) q) ⊕ (Fin (q+1) × Cut (r+d) (q-1)))
```

第一群が出力のテンソルの一面を削除する項、第二群が係数語の一文字を削除する項、
第三群が入力単体の一面を削除する項。第二・第三群は L09 の右辺から左辺へ移す符号も含める。
d=0 の第二群、q=0 の第三群、および次数零の出力の面は零とする。
非全射・隣接値が等しくなる係数語の削除も零として保持する。
これらの規約で、各添字の実テンソル値を次の型で定義する必要がある。

```lean
boundaryBalanceTerm (A : Type u) [CommRing A] (S : SSet.{0})
    (u : Surjection.BasisWord (r+1) d) (q : ℕ) :
  BoundaryBalanceIndex u q → S _⦋q⦌ →
    (power (chains A S) (r+1)).X (-((d+q : ℕ):ℤ) + 1)

-- 追加候補 L09a（未承認・未実装）。
boundaryBalance_pairing (u : Surjection.BasisWord (r+1) d) (q : ℕ) :
  ∃ τ : Equiv.Perm (BoundaryBalanceIndex u q),
    Function.Involutive τ ∧
    (∀ j, τ j = j → ∀ (A : Type u) [CommRing A] (S : SSet.{0}) (x : S _⦋q⦌),
      boundaryBalanceTerm A S u q j x = 0) ∧
    (∀ j, τ j ≠ j → ∀ (A : Type u) [CommRing A] (S : SSet.{0}) (x : S _⦋q⦌),
      boundaryBalanceTerm A S u q (τ j) x = -boundaryBalanceTerm A S u q j x)
```

これは既存の構成の単位・自然性・係数移送の式ではなく、任意次元の境界項の
**新しい組合せ的な対応と符号の主張**である。L09 の総和の等式より強い項ごとのデータを作るため、
「heartbeat のための同じ内容の証明分割」や前提計算3本の枠へ自己判断で入れない。
漏れた理由は、§108 の作成時に L09 のゴールの型で境界計算を一括し、
その証明に使う一般次元の有限添字の対応を独立の数学として数えなかったこと。

ユーザーの「それ以外の新しい数学の補題が要ったら止まって報告」に従い、
**L09a の定義・証明には進まない**。先行する L01〜L08 の検証・修正・保存を終えて報告する。
外枠25,400行を理由にした停止ではない。照合I01〜I03も未使用のまま。

## 110. 方針の再比較：May＋一般 BF と coherent Sp 値 P⁰（11-13、紙・判断待ち）

### 110.1 最新の指示と作業状態

**最新の指示により、5a-5a の切り出しは未決に戻す。Lean の編集・ビルド・監査は停止した。**
§108 の「承認された独立段」という扱いは、最新の判断としては採用しない。
以下は実装の再開や界面変更の承認を先取りしない紙の比較である。

指示変更前に、§108 の紙を18ca0ea4aへ保存し、切断の下書きを進めていた。
新しい切断の11本・**568行**は個別の対象ビルドで通過したが、専用監査・コミットは未実施。
RawAction（52行）・DegenerateInput（46行）・Normalization（87行）の**185行**は未検証。
RawAction の語長の cast と自由加群の評価に型検査の失敗が残っている。
これらの修正を含め、指示変更後は Lean を触っていない。
既存の§106の三本162行とは区別する。未検証185行を完成分として見込みから引かない。
最後の対象ビルドのセッションは終了済みで、鍵・整理券を持っていない。
§108.6・§109 の紙と本節は作業木に保持し、この比較中に追加コミットはしない。
凍結確定の連絡はまだ受けていない。

### 110.2 残りの新規量を同じ基準で比較する

**既存実測と残りの見込みを混ぜない。** coherent 案の§94.2は、既にV・π/Hの7,194行と
鎖模型の3,022行を除いた「残り」の表である。そこから10,216行を再度控除しない。
同様に May の4,128行は完成分であり、§106.3はそれと当時の切断162行を除いた残り。

#### (a) May 案＋一般次元の Berger–Fresse 作用

§106.3の一般BFの三行7,200〜12,700行から、今回の個別コンパイル済み568行を暫定控除する。
この568行は切断・面・符号・生成元・その自然性の束で、微分・部分合成・cosimplicial代数の
全関手はまだ含まない。未監査のため、正式な完成認定とは区別した比較用の控除である。

| 残る新規 | §106.3の残り | 現時点の残りの暫定見込み |
| --- | ---: | ---: |
| 一般切断・符号・正規化・微分・自然性 | 3,000〜5,500 | 2,432〜4,932 |
| 単位・置換・部分合成とTRによる同じBE作用 | 3,000〜5,000 | 3,000〜5,000 |
| 正規化cosimplicial代数の全関手と指定比較 | 1,200〜2,200 | 1,200〜2,200 |
| **一般BFの残り** | **7,200〜12,700** | **6,632〜12,132** |
| May係数・ν・Frobeniusの照合 | 1,200〜2,000 | 1,200〜2,000 |
| native Totの指定比較への適用（G10自体を除く） | 500〜900 | 500〜900 |
| A4の二重模型の実現比較（G10自体を除く） | 1,500〜2,800 | 1,500〜2,800 |
| filtered塔・A4の利用側 | 300〜550 | 300〜550 |
| **残り合計** | **10,700〜18,950** | **10,132〜18,382** |

既存May4,128行・以前の切断162行・今回の568行を加えた完成時の見込みは、
§106と同じ14,990〜23,240行。作業を進めた分を控除しただけで、見積もり全体を縮めた値ではない。
568行を正式な完成分と数えない保守的な比較では、残り10,700〜18,950行をそのまま使う。

#### (b) coherent な Sp 値 P⁰

§94以降、こちらの鎖模型→nativeの未完成部分を閉じる実装は進めていない。
新しいMayのho上のNatTransは、Sp値のFunctorHomを供給しない。
W→BE・混合色・零次の環比較は再利用候補だが、coherentな演算との同定は別に要るので、
May4,128行や今回のBF568行を、そのまま次の表から引かない。

| §94.2からの残りの新規 | 現在の見込み | 既存分の控除の扱い |
| --- | ---: | --- |
| 正のHomと実orbit全複体の鎖同型 | 900〜1,600 | 次数同型・指定包含・座標は既存。微分可換性は残る |
| native orbit・norm・Tateの全自然比較 | 3,000〜5,500 | hG本体は既存として既に考慮。比較・norm・指定境界は残る |
| 完全入力のexact性・降下・T_pの延長 | 2,800〜4,800 | p入力・準同型保存・混合色の自由性は既存として控除済み |
| スペクトル的な右k作用とe | 2,800〜5,000 | 鎖のseed・H⁰計算は既存。右作用とcoherentな照合は未供給 |
| BE作用によるP⁰とRem 2.2.7 | 1,800〜3,200 | 既存BE作用を使う。Mayのhoの演算との比較を自動では仮定しない |
| 離散・Totの最後の照合 | 1,000〜2,000 | 原表のG10後の工程。一般BF作用はこの経路の前提にしない |
| **§94.2の範囲での残り** | **12,300〜22,100** | **10,216行はこの外側の完成済み実測** |

ただし、公平なBS用の比較には、原表の一行で明示していなかった次も数える必要がある。
現在のV_AにはsourceIsoとπ/H比較があるが、任意のnative極限・実現を保つという公開定理を
今回の調査では確認できなかった。Gammaの有限極限保存だけではcosimplicial Totの保存にならない。
またA4の外側の単体的実現・filtered塔への指定Frobeniusの比較は、§96.5で明示した追加義務である。

coherent案ではこれを一般の自然変換の移送で処理する候補とし、
Vの必要な極限・実現保存とその指定比較に500〜1,000行、外側の実現・filteredとA4への適用に
500〜1,400行を**暫定の追加リスク**として置く。
原表の離散・Totの1,000〜2,000行は成分計算・同じTotへの適用に使い、この二つの一般比較と分ける。
これを含むBS用の残りは **13,300〜24,500行**。
この追加1,000〜2,400行は未実装の工程見込みであり、既存宣言で短縮を検証した数字ではない。

両案とも、③-bが供給するG10・一般のnative錐の橋そのものは上の新規量へ加えていない。
それがゼロ作業という意味ではなく、どちらにも必要な共通の外部依存として別に扱っている。

### 110.3 Totの群は一般BF作用を必須にしない

ここは§106.2の読みを修正する。
**一般のBerger–Fresse作用が、ofCosimplicialや厳密BE図式のTotを作るために必ず要る、とは言えない。**
それは厳密な正規化コチェイン代数を先に作る一つの経路であり、native極限を先に作る経路がある。

同じUについて、次は既に無条件で証明済みである。

| ファイル・宣言 | 実際の出力 |
| --- | --- |
| BarrattEccles/FreeProbeDerivedFreeForget.lean：cAlgFreeForgetDerivedAdjunction | 既存CAlg_Rと既存D(A)の間の全∞随伴。A可換環のみが入力 |
| 同：cAlgForgetDerived_mapJoinCone_isLimit | 任意のKと同じ指定極限錐cを、同じUで送った錐が極限錐 |
| 同：cAlgForgetDerived_hasLimit_postcomp | CAlg側の極限の存在からD(A)側の存在 |
| BarrattEccles/Theory.lean：barrattEcclesCore.forget_preservesLimits | 上の実定理が既に中核の欄へ代入済み |

OfTransportという条件付き版もあるが、FreeProbeUnitLocalTransport.freeProbeUnitTransportConditionを
代入した上の無条件版が本体にある。係数拡大・制限の随伴と取り違えていない。
**Uの極限保存を新たな数千行のBF構成に帰着させる必要はない。**

native先行の手順は次のとおり。

1. Xを離散CAlgのcosimplicial図式へ送り、その**同じnative極限錐**を作る。
2. Uの上の既存定理で同じ錐をD(A)の極限錐へ送る。
3. discrete_forgetとG10の全関手・射・指定錐の比較を用い、台を指定した交代余面複体と比較する。
4. パラメータX全体での極限の関手性によりofCosimplicialを作り、
   ofCosimplicial_forgetをFunctorIsoとして、_coneを元の指定錐として供給する。

**残る点**：右随伴であることはCAlgの極限の「存在」や、Uが極限を「創出」することの証明ではない。
D(A)で極限を取って、代数構造が自動で付いたとはしない。
第一段のCAlgのnative錐の存在・全関手性・厳密なReedy/frame模型との指定比較が③-bの3b-4の仕事である。
通常のBE代数圏の極限だけを、そのnative極限錐と同一視しない。
G10の一般部品を本レーンで再実装する案でもない。

| 利用先 | May＋BFの場合 | coherent Spの場合 |
| --- | --- | --- |
| ofCosimplicial・_forget・_cone（5a-5） | native先行なら一般BF作用は不要。Mayのn<0の演算計算には別途BF作用が要る | native先行なら一般BF作用は不要 |
| ③-b 3b-4の厳密BE図式のTotとU | Reedy/frameによるnative錐と既存Uの極限保存で進める経路があり、一般BF作用は必須でない | 同じ。P⁰の選択とは独立 |
| M14のcosimplicial Frobeniusとの一致 | 現在の直接計算経路は同じBF作用を要する。台の擬同型だけでは足りない | coherentなSp値自然変換と極限保存の比較で進める候補。BF作用を用いる必要はない |

coherent案の最後の行は「各射影でπ_nが一致する」だけの議論ではない。
離散入力でP⁰とFrobeniusがcoherentな図式の射として一致すること、
W=U⋙Vの必要な極限保存、および同じ極限錐の射の一意性を使う。
離散Eilenberg–MacLane対象間の写像空間の0切断性から離散計算を全図式へ運ぶ比較も明記して証明する。
その後にπ_nを取る。ho上の自然性だけのMay演算にこの手順を適用してはならない。
外側の単体的実現でもWの該当する保存と指定辺の比較が必要であり、「coherentだから」の一語で省略しない。

### 110.4 KSTで減らせる部分と、減らせない部分

KST/SpectraのBFはBousfield–Friedlanderのスペクトル模型であり、
ここで検討しているBerger–Fresseの一般コチェイン作用とは別である。

| 既存KST宣言 | coherent経路で再利用する範囲 | 供給したことにならないもの |
| --- | --- | --- |
| homotopyFixedPoints、GroupAction.diagramFunctor | 実際の厳密作用図式のhG対象 | orbit、norm、Tate |
| homotopyFixedPointsInfinityCone・_vertex・_isLimit | **元のhG対象**を頂点とするnative極限錐 | 今の周期係数模型とこの図式との全自然同定 |
| homotopyFixedPointsMap、OmegaSpectrum.homotopyLimitMap | 同変射・図式の射での実スペクトル射 | orbit→fixedのnorm自然変換 |
| homotopyTotalizationInfinityCone・_isLimit | 実スペクトルの指定Totのnative極限性 | CAlgやVの極限保存そのもの |
| GroupActionCochains.levelMap_piIsomorphism、FreeActionFamily.endMap_piIsomorphism | 自由作用のcochain・endの不変性 | Tateのexact性、T_pの全入力への延長、右k作用 |

従ってhG対象・指定錐を新たに作る費用は**ゼロ**。
ただし§94.1は既にこのKSTのhGとnative錐を認識した上で§94.2を見積もっている。
3,000〜5,500行からその構成費をもう一度引くのは二重控除になる。
同じp入力の実作用図式との比較を作った後で、残額の中のhG側をこの既存APIへつなぐ。

今回KST/SpectraとSpectra/の公開宣言を調べた範囲では、
当該入力のnative homotopy orbit、orbit→fixedのnorm、指定境界を持つTateの全関手、
スペクトル的な右k作用とeは確認できなかった。
スペクトルの安定性や一般のcofiberの道具があっても、norm射の構成と自然性・指定境界の同定は別に要る。
加群上の有限和としてのnormや、鎖の周期Homをnative Tateの定義済み実例と数えない。
GroupNerveNormalizedCohomologyの正次数消滅はCharZeroの体を仮定するため、F_p係数の代用にはならない。

原典[DAG XIII Construction 2.2.6・Remark 2.2.7・Warning 2.2.8](https://www.math.ias.edu/~lurie/papers/DAG-XIII.pdf#page=35)
では、指定Tate類からスペクトルの演算を作る。一般kではk線形な演算ではない。
既存のk線形なpowerOperationCoefficientSeedとそのH⁰の値だけで、
この右作用・指定類の射eを供給したとはしない。
[BS Lemma 8.4](https://people.mpim-bonn.mpg.de/scholze/prisms.pdf#page=63) の
二重模型の実現上のFrobeniusの主張は、どちらの経路でも最後まで範囲に残す。

### 110.5 推奨と判断点

**推奨は、May案を当面維持しつつ、Totの群と3b-4はnative錐先行で進める方針。**
一般BF作用を共通部品として独立承認する理由に「Totの構成にも必須」を使わない。
一般BF作用が要るのは、現May経路の同じ作用でのtop operationを直接計算する工程である。
その仕事の費用はM14の比較から消さず、残り約10,100〜18,400行（保守的には10,700〜18,950行）として示す。

理由は、(1) Mayの演算・局所化・零次・離散までが既に出来ている、
(2) 残りの型は鎖・切断の有限計算と指定されたBE比較であり、
(3) coherentへ戻す場合はnative norm/Tate・exactな延長・右k作用eという
別々の未供給の束が依然として残るため。
ただし二案の見込みの幅は重なっており、行数の下界やMayが必ず短いという証明ではない。
coherent出力を今後の∞基盤にも優先して供給する方針なら、その再利用価値を理由に後者を選ぶ判断はあり得る。

coherentへ戻す場合の判断は、残り12,300〜22,100行の元工程と、
BS用の未積算比較を含めた13,300〜24,500行の暫定見込み、界面を再び強くする範囲・分担をセットで行う。
現ho値の界面のまま内部だけcoherentな実例を作る案も可能であり、界面変更は必須ではない。
いずれも自己判断では採用しない。

**本比較を報告して判断を待つ。5a-5aの独立段の新設・Leanの再開・界面の変更はしない。**
待ちの間はM15の段0の紙だけを進める。

## 111. 判断待ちのM15段0：極限保存と一般R加群の境界（紙のみ、11-13）

§110で再確認したU:CAlg_A→D(A)の全∞随伴と極限保存は完成済みである。
ただし、これは§95・§97・§107の一般R加群の模型の不足をそのまま解消するものではない。

- 固定したAと、変わるE∞頂点Rを区別する。必要なMod_Rの台の忘却は、
  上のCAlg_Aの忘却とは始域が違う。
- §107のdgAlgebraExtensionInfinityと準同型不変性は、厳密BE→同じ台のdg代数という
  忘却が出来た後の固定模型で再利用する。全Rと全辺への降下・restrictionの右随伴は引き続き必要。
- CAlgでAmitsur図式のnative極限錐を作ってUで送れても、M15の指定R加群の単位、
  R→Sのfiber、相対テンソルの反復と指数射の同定は別である。
  D(A)のテンソルをMod_Rの相対テンソルに読み替えない。
- coherentなP⁰に必要な「スペクトル的な右k作用e」は、固定した係数kでの構成。
  それを作るだけで一般のE∞底R上のmodule族・対称相対テンソルを得たとは数えない。
  逆方向にも、既存のk線形dg双加群だけで一般の非k線形P⁰を得たとはしない。

担当を決める際の最初の受け渡しは、§107.3の五点（同じ台の厳密忘却、拡大・制限の全関手と随伴、
弱同値・nativeの辺と合成への降下、相対テンソルと底変換、指定単位とfiber・指数射）を維持する。
一般Rの模型の2,500〜4,500行は暫定のままで、今回の紙の比較から新しい実装の担当や上限を決めない。

本節を含め、最新指示後の作業は報告書のみ。Lean編集・ビルド・監査・追加コミットなし。
§110の二案の判断を待ち、未検証の下書きは作業木に保持する。

## 112. M14再開：残り全体の型一覧（11-13、実装前の紙）

### 112.1 採用範囲と停止規則

§110に対する最新のユーザー承認でMay案を続ける。
一般次元のBF作用は**独立段5a-5aではなく、M14の_totの直接計算の部品**とする。
§108のL01〜L28の数学の型を、このM14の前半の一覧として引き継ぐ。
§108の独立段という呼称・25,400行の枠は採用しない。
外枠は**M14全体25,000行（完成したMay4,128行を含む）**、12,500行で途中報告して続行する。

証明の分割は数えず型を記録。前提計算は一覧のLごとに3本、照合は全体3本。
L05の既存構成の自然性・次数移送の前提計算は§108.6の三本で3/3。
I01（IntervalCutsとの一致）は予約済み・未使用、I02・I03も未使用。
それ以外の新しい数学は、検証済みを保存して型と漏れた理由を報告し停止する。
凍結確定の連絡後はコミットしない。今回まだ確定連絡を受けていない。

最初は未検証185行を修正して検証する。個別ビルド済み568行は専用監査後にコミットする。
以下の紙の一覧を載せた後、承認待ちを挟まずこの順に進める。
G10・③-bのnative錐や一般の実現の橋は作らず、受け渡し後の指定比較を適用する。
5a-5・3b-4に一般BF作用を前提として追加しない。

### 112.2 L01〜L28の補充：境界と合成の有限項の対応

L01〜L28の全型は§108.3・§108.4、証明分割は§108.6に固定したもの。
L09に対して§109で止めた追加候補を、今回の**実装前の全一覧**にL09aとして含める。
BoundaryBalanceIndexとboundaryBalanceTermの型・零次数と退化項の規約も§109のとおり。

```lean
-- L09a：テンソルの面／係数の文字削除／入力の面の符号付き項を対にする。
boundaryBalance_pairing (u : Surjection.BasisWord (r+1) d) (q : ℕ) :
  ∃ τ : Equiv.Perm (BoundaryBalanceIndex u q), Function.Involutive τ ∧
    (∀ j, τ j = j → ∀ (A : Type u) [CommRing A] (S : SSet.{0}) (x : S _⦋q⦌),
      boundaryBalanceTerm A S u q j x = 0) ∧
    (∀ j, τ j ≠ j → ∀ (A : Type u) [CommRing A] (S : SSet.{0}) (x : S _⦋q⦌),
      boundaryBalanceTerm A S u q (τ j) x = -boundaryBalanceTerm A S u q j x)
```

L12の部分合成についても、有限和の等式だけで添字の対応を省かない。
`CompositeBalanceIndex u v i q`は、既存OverlapPartitionによる係数合成と一段切断の項と、
外側の切断のi色の出力を内側で切る二段切断の項の直和。
`compositeBalanceTerm`は第一群を正、第二群を負とする、同じ実テンソルでの符号付き値。
正規化で消える合成語・面は零の項として保持する。新規の型は次。

```lean
-- L12a：二段切断の項の対応。nullaryも含む。
compositeBalance_pairing (u : Surjection.BasisWord (m+1) d)
    (v : Surjection.BasisWord n e) (i : Fin (m+1)) (q : ℕ) :
  ∃ τ : Equiv.Perm (CompositeBalanceIndex u v i q), Function.Involutive τ ∧
    (∀ j, τ j = j → ∀ (A : Type u) [CommRing A] (S : SSet.{0}) (x : S _⦋q⦌),
      compositeBalanceTerm A S u v i q j x = 0) ∧
    (∀ j, τ j ≠ j → ∀ (A : Type u) [CommRing A] (S : SSet.{0}) (x : S _⦋q⦌),
      compositeBalanceTerm A S u v i q (τ j) x = -compositeBalanceTerm A S u v i q j x)
```

上の二つは、既存の符号規約を変えず、各値に現れる面写像の合成とKoszul符号を比較する主張。
L09a→L09→L10、L12a→L12→L14・L16の順に使う。
L11の置換、L13の単位、L14のnullary、L15の自然性、L18のTR制限、
L19〜L28の正規化・convolution等化子・台の指定比較は元の一覧どおり残る。

### 112.3 L29〜L37：同じ係数のtop operationを直接計算する

以下も**紙の新規名・型案（未型検査）**。κ := EInfinityPrimeField.{u} p、
ν p n := ULift.up (mayNu p n : ZMod p)。r>0のBF作用と同じχ・TRを使う。
`bfTopScalar p q e : κ`は、eをTRの実基底係数で展開した切断和のtop degreeのスカラー。
切断符号に加え、L28の**実際の**convolution評価・テンソルの交換・指定次数移送の符号を含める。
νの逆数となるようにこのスカラーを定義しない。
`coefficientOf f s`は、Wの自由生成元e_sにfを適用して実BE係数へ運んだ値。

```lean
-- L29：増大を保つ同変比較の変更が、同じD_iのホモロジー類を変えない。
mayDClass_comparison (f g : (mayResolution p κ).complex ⟶ (mayArityResolution p κ).complex)
    (hf : f ≫ (mayArityResolution p κ).π = (mayResolution p κ).π)
    (hg : g ≫ (mayArityResolution p κ).π = (mayResolution p κ).π)
    (X : (operad κ).Algebra) (i : ℕ) (j : ℤ) (a : MayClosed X.carrier j) :
  mayDClassWith f X i j a = mayDClassWith g X i j a

-- L30：計算可能な標準の周期bar比較。Wと同じ右回転生成元・増大を使う。
canonicalCyclicComparison : (mayResolution p κ).complex ⟶ (mayArityResolution p κ).complex
canonicalCyclicComparison_augmentation :
  canonicalCyclicComparison p ≫ (mayArityResolution p κ).π = (mayResolution p κ).π
canonicalCyclicComparison_even (s : ℕ) :
  coefficientOf (canonicalCyclicComparison p) (2*s) = canonicalEvenBarSum p s
canonicalCyclicComparison_odd (s : ℕ) :
  coefficientOf (canonicalCyclicComparison p) (2*s+1) = canonicalOddBarSum p s

-- L31：非退化top切断の各色は全q単体。§106の積の計算を実作用へ運ぶ。
bfAction_top_value (X : CosimplicialRingAlgebra κ) (q : ℕ)
    (e : (operad κ).arity p |>.X (-((q*(p-1):ℕ):ℤ)))
    (a : normalizedComponent X q) :
  bfRepeatedActionValue X q e a = bfTopScalar p q e • frobeniusNormalizedValue X q a

-- L32：標準bar和のtop係数。全符号を含む零次・一次・帰納式。
canonicalTop_zero : bfTopScalar p 0 (coefficientOf (canonicalCyclicComparison p) 0) = 1
canonicalTop_one :
  bfTopScalar p 1 (coefficientOf (canonicalCyclicComparison p) (p-1)) =
    (-1 : κ)^((p-1)/2) * (((p-1)/2).factorial : κ)
canonicalTop_succ (q : ℕ) :
  bfTopScalar p (q+1) (coefficientOf (canonicalCyclicComparison p) ((q+1)*(p-1))) =
    (-1 : κ)^((q+1)*((p-1)/2)) * (((p-1)/2).factorial : κ) *
      bfTopScalar p q (coefficientOf (canonicalCyclicComparison p) (q*(p-1)))

-- L33：巡回bar和で寄与する隣接対の列挙と符号の集計。
-- SignedTopBarIndexはL32の実有限和の非零添字。signedTopBarWeightはその実係数。
canonicalTop_pair_count (q : ℕ) :
  ∑ b : SignedTopBarIndex p q, signedTopBarWeight p q b =
    (-1 : κ)^(q*(q+1)*((p-1)/2)/2) * (((p-1)/2).factorial : κ)^q

-- L34：逆冪で定義したMayのνとの一致。p=2を含む。
canonicalTop_normalized (q : ℕ) :
  ν p (-(q:ℤ)) *
    bfTopScalar p q (coefficientOf (canonicalCyclicComparison p) (q*(p-1))) = 1

-- L35：同じ正規化した閉元のp乗。codegeneracyと微分を保つ。
frobeniusNormalized_mem (X : CosimplicialRingAlgebra κ) (q : ℕ)
    (a : normalizedComponent X q) : (a.val^p) ∈ normalizedComponent X q
frobeniusNormalized_closed (X : CosimplicialRingAlgebra κ) (q : ℕ)
    (a : MayClosed ((bfNormalizedAlgebra κ).obj X).carrier (q:ℤ)) :
  MayClosed ((bfNormalizedAlgebra κ).obj X).carrier (q:ℤ)

-- L36：全整数nの同じMay演算とlevelwise Frobeniusの実ホモロジーでの一致。
bfMayTopValue (X : CosimplicialRingAlgebra κ) (f : X ⟶ X)
    (hf : ∀ j a, (f.app j).right.hom a = a^p) (n : ℤ)
    (a : MayClosed ((bfNormalizedAlgebra κ).obj X).carrier (-n)) :
  mayNormalizedClass p ((bfNormalizedAlgebra κ).obj X) n ν p n a =
    mayClosedClass _ (-n) (mayClosedMap ((bfNormalizedAlgebra κ).map f).hom (-n) a)

-- L37：標準単体の同じ余代数によるconvolutionはBE代数の右frame。
bfSimplexConvolutionFrame (B : (operad κ).Algebra) :
  SimplexCategory ⥤ (operad κ).Algebraᵒᵖ
bfSimplexConvolutionFrame_obj (B : (operad κ).Algebra) (q : ℕ) :
  ((bfSimplexConvolutionFrame B).obj ⦋q⦌).unop =
    convolutionAlgebra (hopf κ) (simplexBECoalgebra κ q) B
```

canonicalEvenBarSum / OddBarSum は、Wの周期微分T・Nに対し、BEの実bar収縮で
自由生成元の像を再帰的に持ち上げた、同じ置換列の有限和。
偶数では巡回群の元で添字づける各二列の和、奇数では同じ巡回生成元の追加を含む。
L30で実置換列の式を検証し、L33でその寄与と符号を計算してL32へ渡す。
計算中に生成元の逆や係数の符号を公開定義の変更で吸収しない。
L35のclosedは定義の型だけで終わらせず、L26の指定比較でa↦a^pを読む生成元公式も供給する。
L37はframeのmatching射のfibration・各単体の収縮・augmentationを含める。
G10の一般native比較をL37の仮定に入れて作ったことにはしない。

### 112.4 L38〜L44：指定native Tot・filtered塔・A4の二重模型

ここで`nativeTot`とそのcone、実現の全関手と指定比較は③-bの供給物を使う。
以下の型のG10/3b-4の引数は**外部の受け渡しに含まれる証明**であり、
このレーンで新しい同名の構造を作って仮定を隠すものではない。
正式な受け渡しの公開名に合わせる際は、数学の範囲を変えず名前を追従する。

```lean
-- L38：同じBF模型が持つnative錐。標準単体の同じframeで高次成分を作る。
bfCosimplicialCone (X : CosimplicialRingAlgebra κ) :
  JoinCone (cosimplicialNerve X ≫ discreteCAlgUnderEmbedding κ)
bfCosimplicialCone_vertex (X) :
  (bfCosimplicialCone X).vertex =
    atVertex (nerveMap (bfNormalizedAlgebra κ) ≫ algebraCAlgSource κ) (nerveVertex X)

-- L39：G10とnative側の同じ錐の全関手比較を適用する。
bfToNativeTotIso (G10 : SpecifiedG10Comparison κ) (BE : SpecifiedNativeBETotComparison κ) :
  FunctorIso (nerveMap (bfNormalizedAlgebra κ) ≫ algebraCAlgSource κ) (nativeOfCosimplicial κ)
bfToNativeTotIso_frobenius (G10) (BE) (X) (f : X ⟶ X) :
  (bfToNativeTotIso G10 BE).hom.app (nerveVertex X) ≫ nativeTotMap X f =
    bfNativeMap X f ≫ (bfToNativeTotIso G10 BE).hom.app (nerveVertex X)

-- L40：現界面の_tot。指定された同じFrobenius辺で、全整数次数。
barrattEcclesPowerOp0_tot (G10) (BE)
    (X : CosimplicialRingAlgebra κ) (f : X ⟶ X)
    (hf : ∀ j a, (f.app j).right.hom a = a^p) (n : ℤ) :
  (barrattEcclesPowerOp0 p n).app (mk (nativeTotVertex X)) =
    (homotopyGroupsOnHo κ (cAlgForgetDerived κ) n).map
      (homMk (nativeTotFrobeniusEdge X f))

-- L41：filtered群の余極限における自然な演算の一意性。
filteredOperation_desc {I : Type u} [SmallCategory I] [IsFiltered I]
    (D : I ⥤ AddCommGrpCat.{u}) (c : Cocone D) (hc : IsColimit c)
    (P Q : c.pt ⟶ c.pt)
    (h : ∀ i, c.ι.app i ≫ P = c.ι.app i ≫ Q) : P = Q

-- L42：同じFrobenius塔のshiftとP⁰。Πの指定余極限保存を入力として明記。
frobeniusTower_powerOp (D : ℕ ⥤ hoCAlg κ) (f : D ⟶ D)
    (c : Cocone D) (hc : IsColimit c) (n : ℤ)
    (hπ : IsColimit ((Π κ n).mapCocone c))
    (hP : ∀ i, (powerOp0 p n).app (D.obj i) = (Π κ n).map (f.app i)) :
  (powerOp0 p n).app c.pt = (Π κ n).map (colimitEndomorphism c hc f)

-- L43：単体的余単体的可換Fp代数の同じ厳密二重模型でのMay差の境界。
-- doubleRealizationModelはBFの各列の作用と、外側の実際のshuffleを使う模型。
-- F_Xはlevelwise Frobeniusから来る同じ複体射。Hは閉元ごとの明示的な原始元。
doubleMayDifferencePrimitive (X : SimplicialObject (CosimplicialRingAlgebra κ))
    (n : ℤ) (a : MayClosed (doubleRealizationModel X).carrier (-n)) :
  ∃ H : (doubleRealizationModel X).carrier.X (-n-1),
    (doubleRealizationModel X).carrier.d (-n-1) (-n) H =
      mayNormalizedValue p (doubleRealizationModel X) n ν p n a - (F_X.f (-n) a.val)

-- L44：③-bの指定実現の橋を適用したA4-localな全整数次数の比較。
a4_realization_powerOp (G10) (BERealization : SpecifiedBERealizationComparison κ)
    (X : SimplicialObject (CosimplicialRingAlgebra κ)) (n : ℤ) :
  (powerOp0 p n).app (mk (nativeDoubleRealizationVertex X)) =
    (Π κ n).map (homMk (nativeDoubleFrobeniusEdge X))
```

L39のappは紙の記法。実際は既存FunctorIsoの辺・自然性と指定join錐の脚を用いる。
L38〜L40はG10の後。そこに到達したら区切って報告し、外部の橋は作らずM15の紙へ移る。
L41は通常圏の群の余極限の普遍性。L42でΠがfiltered余極限を保つこと自体は、
界面の保存の欄／別工程の忘却のsifted保存と既存のホモロジー比較から受け取る。
その依存を供給せずに、BE実例の全filtered保存までM14で完成したとは報告しない。

L43では単にΠをlevelwiseに取って実現の余極限へ交換しない。
指定のshuffle・係数の微分・全複体のKoszul符号で差の原始元を作る。
必要な数学を次の二つとして一覧に含める。

```lean
-- L43a：同じshuffle実現に沿うBE作用の、全係数・全射での比較。
doubleRealization_action (X) (r : ℕ) :
  realizationAction X r = doubleShuffleAction X r

-- L43b：L43の原始元の明示的有限展開の微分。
-- finiteMayPrimitiveは同じW係数・BF切断・外側のshuffleから定義し、
-- 入力の閉条件で消える項も、係数微分とともに保持する。
finiteMayPrimitive_d (X) (n : ℤ)
    (a : MayClosed (doubleRealizationModel X).carrier (-n)) :
  (doubleRealizationModel X).carrier.d (-n-1) (-n) (finiteMayPrimitive X n a) =
    mayNormalizedValue p (doubleRealizationModel X) n ν p n a - F_X.f (-n) a.val
```

同じ実現模型・指定射・底の全複体との比較は、③-bの正式な受け渡しに照らして適用する。
その前段に新しい一般の厳密化やnative錐の定理を作らない。
この一覧にない新しい数学が要ると分かった時点で、その型と漏れた理由を報告する。

### 112.5 証明順・照合の枠

修正・監査→L01〜L08→L09a,L09,L10→L11〜L18（L12aを先に）→I01→L19〜L28→
L29〜L36→L37,L38→G10/3b-4受け取り後にL39,L40→L41,L42→L43a,L43b,L43,L44。
L32とL33は組合せの和を先に計算して規格化へ運ぶ。
新しい独立段の取り込み点は設けず、M14の途中の検証済み分として保存する。

I01以外のI02・I03は未使用。比較の定義の表現差だけなら型を記録してこの枠で処理する。
比較そのものが新しい数学なら、照合の名で継続しない。
以上を残り全体の開始時の型一覧とする。承認待ちを挟まず、まず568行の監査と185行の修正へ進む。

### 112.6 最初の568行の監査と保存

/tmp/bsw16/audit-m14-cuts-first.log：**11モジュール・101宣言、標準三公理のみ**で成功。
568行を保存する。対象はEInfinity/SimplexCuts/の次の11本。
Outputs、Faces、HomogeneousTensor、NormalizedGenerators、CutTensor、TensorNaturality、
CutNaturality、Signs、SignedTerms、SignedNaturality、CollapsedFace。
いずれも個別対象ビルドに通った版から数学の変更なし。sorry・追加公理なし。

以前のExpanded・Balanced・TopTermの162行と合わせ、切断の検証済み部分は730行。
May4,128行を足した本経路の現在の基礎実測は4,858行。
RawAction・DegenerateInput・Normalizationの修正中の分は、ここに含めない。
新規ファイルのdocstringに残る5a-5a L番号は§108の旧一覧の参照であり、
今後はM14のL番号として読む。独立段を作ったという意味にはしない。

全体の入口登録・rootビルド・全体監査は行っていない。
本コミットは枝の中間保存で、独立した5a-5aの完成／取り込み点ではない。
監査の鍵は返却済み。未検証三本の修正版は別の一回の対象ビルドで検証中。

### 112.7 三本の修正完了・監査と夜の運用

RawAction・DegenerateInput・Normalizationの修正版は **208行**。
/tmp/bsw16/m14-normalization-05.log：三本すべてを含む対象ビルド成功。
最後の三本に新しい警告なし。語長の等式を明示的に移送し、
自由加群の拡張を既存freeDescで作り、現行Type圏の束ねた射を指定して評価した。
退化入力の消滅とMoore正規化への降下、同じ係数と生成元での値は型を変えていない。

/tmp/bsw16/audit-m14-normalization.log：**3モジュール・44宣言、標準三公理のみ**で成功。
sorry・追加公理なし。検証済み三本を枝へ保存する。
May4,128行と切断の検証済み938行を合わせ、本経路の基礎実測は **5,066行**。
L09aのBoundaryIndexの新しい下書きはこの検証済み数とコミットに含めない。

23時の最新連絡で、B3の凍結はmainのみとなった。各枝の編集・コミットは続行してよい。
それ以前の「確定後は枝へコミットしない」は今回は適用しない。
本レーンは対象ビルドと小さい専用監査だけを、一回ごとに鍵を取って実行している。
mainへの取り込み・B4の追従は調整役からの連絡を待つ。

### 112.8 L09aの前提計算1：既存の正規化生成元の微分

既存AlexanderWhitney.generator_dを同じembeddingDownNatへ運ぶ法則を用いる。
新しい境界の分類ではなく、既存の複体射・指定係数移送の法則としてL09aの前提計算**1/3**。
内部のchains_d_negはこの同じ移送の証明分割とする。

```lean
gen_d (A : Type u) [CommRing A] (S : SSet.{0}) (q : ℕ) (x : S _⦋q+1⦌) :
  (chains A S).d (-((q+1:ℕ):ℤ)) (-(q:ℤ)) (gen A S (q+1) x) =
    ∑ i : Fin (q+2), (-1:ℤ)^i.val • gen A S q (S.δ i x)
```

§112.7の三本は **bea1aab1b** に保存済み。次はL09aの有限添字とこの指定微分の計算。

### 112.9 L09aの前提計算2：一つの出力次数を下げる移送

既存の有限和のupdateの式による次数計算を、L09aの前提計算**2/3**として記録する。

```lean
degreeSum_delete (d : Fin n → ℕ) (i : Fin n) (h : 0 < d i) :
  degreeSum n (Function.update d i (d i-1)) + 1 = degreeSum n d
```

これは切断の新しい分類ではなく、境界項を同じ全次数成分へ送るための移送の法則。

## 113. L09aの境界値までの検証と、一覧外の再帰分解での停止（11-13夜）

### 113.1 検証済み・保存する範囲

新しい五本は全てEInfinity/SimplexCuts/。

| モジュール | 行数 | 出力 |
| --- | ---: | --- |
| BoundaryIndex | 33 | 出力面・係数語削除・入力面の三群の有限添字 |
| GeneratorBoundary | 44 | 同じ整数次数の正規化生成元の微分。L09a前提計算1 |
| BoundaryFaces | 35 | 標準面と一因子の次数を下げる指定移送。L09a前提計算2 |
| OutputBoundaryTerms | 63 | 出力の一面を削除した実テンソルとBF・Koszul符号 |
| BoundaryTerms | 71 | 係数語・入力面も含む、同じ次数の三群の境界値 |
| **計** | **246** | |

対象ビルド：m14-boundary-index-01.log、m14-boundary-prerequisites-01.log、
m14-output-boundary-01.log、m14-boundary-terms-01.log（いずれも/tmp/bsw16/）。
BoundaryFacesの未使用変数警告はδの次元を明記して解消し、最終ソースに新しい警告なし。
小さい専用監査audit-m14-boundary-terms.logは **5モジュール・66宣言、標準三公理のみ**で成功。
sorry・追加公理なし。鍵はビルドと監査ごとに取り直し、返却済み。

独立な有限計算として、整数係数のテンソルの微分と、χの文字削除＋入力単体の面を
Pythonで直接比較した。arity1〜3、語次数0〜3、単体次数0〜2の**495例**で一致した。
これはBF符号の点検であり、一般のL09a・L09のLean証明の代用にはしない。

三群の値は型検査済みだが、**boundaryBalance_pairingも微分等式もまだ証明していない**。
May4,128行＋切断の検証済み1,184行で、本経路の基礎実測は **5,312行**。
12,500行の途中報告点・25,000行の外枠で止まったのではない。

### 113.2 一覧外として報告する新しい数学の型

L09aのτを、最後の垂直辺を取り除く再帰で構成する筋を具体化したところ、
次の二つが必要となった。**紙の新規名・型案、未実装・未型検査**。

```lean
-- 追加候補 R01。q+1個目の垂直辺の属する区間pで分類し、末尾を除く。
cutLastVerticalEquiv (m q : ℕ) :
  Cut m (q+1) ≃ Σ p : Fin (m+1), Cut p.val q
```

幾何学的には、各区間の長さの列の最後の正の成分pから一を引き、
pより後の長さ零の区間を除く。逆はその最後に垂直辺を足し、残りの水平辺を戻す。
既存ShufflePath.vertical_edgeは最後の垂直辺の存在と座標を供給するが、
**区間数をp+1へ変えた経路とのこの全単射**は今回調べたAPIには見つからなかった。
ShuffleLastFaceの既存の削除は、経路の最後の辺が垂直という条件の下で固定した水平次数を保つ式で、
この任意の長さ零の末尾を含む分解をそのまま供給するものではない。

この分解だけでなく、色ごとの出力の復元の法則も必要。
以下でverticesListは色のfiberを元の順序で列挙してverticalで写したList。
空のfiberも空リストとして扱い、**ここでは全射性を仮定しない**。

```lean
def verticesList {m q r : ℕ} (s : Cut m q) (v : Fin (m+1) → Fin r) (c : Fin r) :
    List (Fin (q+1)) :=
  ((colorPositions s v c).sort (· ≤ ·)).map (fun i => s.vertical i)

def prefixLabels (v : Fin (m+1) → Fin r) (p : Fin (m+1)) : Fin (p.val+1) → Fin r :=
  fun i => v ⟨i.val, by omega⟩

def terminalMultiplicity (v : Fin (m+1) → Fin r) (p : Fin (m+1)) (c : Fin r) : ℕ :=
  (Finset.univ.filter (fun i => p ≤ i ∧ v i = c)).card

-- 追加候補 R02。欠けた色・末尾の重複も保持する、再帰の値の法則。
verticesList_lastVertical (v : Fin (m+1) → Fin r) (p : Fin (m+1))
    (s : Cut p.val q) (c : Fin r) :
  verticesList ((cutLastVerticalEquiv m q).symm ⟨p,s⟩) v c =
    (verticesList s (prefixLabels v p) c).map Fin.castSucc ++
      List.replicate (terminalMultiplicity v p c) (Fin.last (q+1))
```

例えば語(0,1)の最後の垂直辺が第0区間にある切断では、接頭語は(0)となり色1が欠ける。
それでも元の切断の色1には末尾の頂点が現れる。
既存L01・L02・faceは**全射語で各色が非空**という型なので、
そのまま同じarityの接頭語へ再帰適用はできない。
R02は欠けた色を空のリストとして保持し、末尾で現れる回数を復元する新しい式である。
サフィックスで色が重複すると、List.replicateの重複を正規化で消す必要がある。
存在するかどうかのifで頂点を一つだけ付ける式にはしない。

### 113.3 漏れた理由と停止の扱い

§112ではL09aの**全境界項を対にするτの主張**までを型にしたが、
τを作る再帰のデータと、全射でなくなる接頭部の値の復元を列挙していなかった。
R01・R02は、既存の単位・余単位・自然性・係数移送の式の評価ではなく、
入力の単体次元と区間数を同時に変える新しい組合せ的な分解の主張である。
また単に既存のL09aの証明をelaborationのために同じ式へ分割しただけとは扱わない。

ユーザーの「それ以外の新しい数学の補題が要ったら止まって報告」に従い、
**R01・R02の実装には入らず、ここで停止する**。
L09a前提計算は2/3、照合I01〜I03は0/3のまま。未使用の前提計算枠をこの新しい数学に流用しない。
検証済みの五本と本報告を保存して判断を待つ。
G10・native Totの部品や界面の変更は行っていない。
B3の凍結はmainのみという最新連絡に従い、枝のこの保存は行う。

## 114. R01・R02再開と有限組合せの枠（11-14未明）

BS-W16 §28と最新指示でR01・R02をL09aの部分へ追加し再開する。
mainは凍結中なので取り込まず、mainの指示書§28を読み取りで確認した。
枝の編集・コミットは続行可。対象ビルド・小さい専用監査だけを行う。

### 114.1 実装前の有限計算

/tmp/bsw16/check-terminal-cut.py は、切断を非負の区間長の列として独立に列挙し、
最後の正の区間の長さを一つ下げるR01の逆と、R02の色ごとの頂点列の復元を確認した。
m=0〜4、q=0〜3、色数1〜3の全ての語（非全射も含む）、全ての色で **122,186例**が一致。
うち接頭部の色が空で元の出力が非空の例10,378件、末尾の反復が2以上の例15,366件。
欠けた色を削除したり、末尾を単一の頂点へ潰したりしていない。
この点検はLean証明の代用にはしない。

### 114.2 追加する有限組合せの補題：L09aの枠1/3

最後の垂直辺を補集合の最大元として選び、その前の辺をFinへ詰める構成を使う。
`lowerPart s a` は、sのaより小さい元をFin a.valに圧縮した有限集合。
次を新しい有限組合せの枠 **C01（1/3）** として追加する。

```lean
card_lowerPart_of_max {N : ℕ} (s : Finset (Fin N)) (a : Fin N)
    (ha : a ∈ s) (hm : ∀ i ∈ s, i ≤ a) :
  (lowerPart s a).card + 1 = s.card
```

所属の式と補集合との可換性は、この制限の定義を評価する証明分割。
R01・R02本体は今回承認された二本であり、C01のほかの追加枠へ数えない。
前提計算L09aの2/3、照合の0/3とは別に記録する。

### 114.3 色のfiberのリスト化：有限組合せの枠2/3

R02の定義にある有限集合の昇順列を、経路の頂点の列をfilterする形へ直す。
新しい有限組合せの枠C02（L09aの2/3）は次の型とする。

```lean
sort_filter_univ (N : ℕ) (P : Fin N → Prop) [DecidablePred P] :
  (Finset.univ.filter P).sort (· ≤ ·) =
    (List.finRange N).filter (fun i => decide (P i))
```

接頭部・末尾の水平・垂直座標の評価、リストの連結と写像についての計算は、
R01・R02の同じ構成の証明分割である。新しいBE作用や法則は足していない。

### 114.4 末尾の出現回数：有限組合せの枠3/3

末尾の区間を `terminalSuffixIndex p j = p+j` で列挙する。
新しい有限組合せC03（L09aの3/3）は次の型とする。

```lean
terminalSuffix_card {m r : ℕ} (v : Fin (m + 1) → Fin r)
    (p : Fin (m + 1)) (c : Fin r) :
  (Finset.univ.filter (fun j : Fin (m - p.val + 1) =>
    v (terminalSuffixIndex p j) = c)).card = terminalMultiplicity v p c
```

R02の末尾の `List.replicate` の回数を元のfiberで数える式である。
一般の新しい有限分解がさらに必要なら、この枠では足さず報告して止まる。

### 114.5 R01・R02の完了と検証

次の8本、計607行を対象ビルドで検証した。

| モジュール（`SerrePositivity.EInfinity.SimplexCuts.` 以下） | 行数 | 内容 |
| --- | ---: | --- |
| LowerPart | 60 | 最大元より前の有限集合、C01 |
| TerminalExtension | 84 | 接頭部から最後の垂直辺と末尾を戻す |
| TerminalData | 107 | 最後の垂直辺、その区間番号、接頭部 |
| TerminalEquiv | 72 | 逆写像の一意性、R01 `cutLastVerticalEquiv` |
| TerminalCoordinates | 84 | 復元した切断の接頭部と末尾の座標 |
| VertexLists | 70 | 欠けた色を含む頂点列、C02 |
| TerminalSuffix | 66 | 末尾の反復数、C03 |
| TerminalTrace | 64 | 頂点列の評価、R02 `verticesList_lastVertical` |

R01の逆は `terminalExtend`。元の経路への復元と復元写像の単射性から同値を作った。
R02の型は§113.2の承認された型そのままであり、`List.replicate` の回数も
`terminalMultiplicity` の定義そのまま。全射性の仮定を足していない。

対象ビルド：`lake build SerrePositivity.EInfinity.SimplexCuts.TerminalTrace` 成功
（`/tmp/bsw16/m14-terminal-trace-03.log`）。新規8本にはLeanの警告なし。
専用監査：`/tmp/bsw16/audit-m14-terminal.lean`、**8モジュール・104宣言・標準三公理のみ**。
`/tmp/bsw16/audit-m14-terminal.log` に成功を確認。新規ソースにsorry・追加公理0。
ビルドと監査はそれぞれ `--wait 3600` の鍵を取り、終了時に返した。
rootビルド・全体監査・入口の登録はしていない。上記8本を次の登録候補とする。

今回の607行を足すと、改訂MayのM14本体は **5,919行**
（完成済みMay 4,128 + SimplexCuts既存1,184 + 今回607）。
半分の12,500行と外枠25,000行には届いていない。
旧coherent経路の10,216行は削除せず、この改訂Mayの内訳と分けて保持している。

## 115. L09aの符号の再帰で要る四本目の有限分解（11-14未明、停止）

R01・R02からL09aの境界項の対応へ戻り、接頭部の符号を比較した。
既存の `cutSign` は `intervalLength` と `positionExponent` で
**元の語の `Surjection.Caesura`** を使う。一方、切断の接頭部の語では
後続の色の出現を失うので、caesuraは保存されない。
例：`v=(0,1,0)`、`p=1`、`i=0`。元の語ではcaesuraだが、接頭語 `(0,1)` では違う。
R02は頂点列を戻す主張であり、元の語での「最後の出現」を接頭語に運ぶ主張ではない。
そのまま `cutSign s (prefixLabels v p)` を元の語の符号として使うことはできない。

### 115.1 追加が必要な主張の型

次の `prefixPosition` は報告内の記法で、未実装。

```lean
def prefixPosition {m : ℕ} (p : Fin (m + 1)) (i : Fin (p.val + 1)) :
    Fin (m + 1) :=
  ⟨i.val, by have hi := i.isLt; have hp := p.isLt; omega⟩

caesura_prefix_iff {m r : ℕ} (v : Fin (m + 1) → Fin r)
    (p : Fin (m + 1)) (i : Fin (p.val + 1)) :
  Surjection.Caesura v (prefixPosition p i) ↔
    Surjection.Caesura (prefixLabels v p) i ∨
    ∃ j : Fin (m + 1), p < j ∧ v j = prefixLabels v p i
```

これは後続の同色のfiberを接頭部内と末尾へ分ける有限分解であり、
L09aの同じまとまりの追加補題C04として必要になる。
全射性を足して接頭部に欠ける色を排除することはしない。
m=0〜4、色数1〜3、全ての語・接頭部・位置の5,384例でこの分解を確認した。
そのうち1,396例では元の語と接頭部でcaesuraが変わる。
有限点検は証明の代用ではなく、符号にこの区別が要ることの確認である。

### 115.2 既存APIと停止の理由

`Surjection.Caesuras` には定義、色の置換との可換性、全射語の最後の出現のAPIがある。
しかし、非全射も許す接頭語への上記の分解は見つからなかった。
既存のshuffleの混合角の交換・面の一致は利用候補だが、そちらの符号は
`ShufflePath.sign` であり、BFの色ごとのcaesuraを保持した符号の代わりにはならない。

§113では非全射の接頭部の**頂点列**の復元までを追加として挙げたが、
元の語のcaesuraを接頭語と末尾に分解する主張を挙げていなかった。
これはR02の構成の定義評価や相互逆の証明分割ではなく、
符号計算のための別の色のfiberの分解なので、別枠で記録する。
有限組合せの追加はC01・C02・C03で3/3に達した。
前提計算の残り枠を使ってこの第四の有限分解を足すことはしない。
**承認された枠の停止条件に従い、C04を実装する前にここで停止する。**
R01・R02の検証済み8本と本報告をコミットして判断を待つ。
L09aのτ・符号の相殺・微分の等式はまだ証明していない。
BE作用・operadの法則・Tot・界面は変更せず、G10の部品も作っていない。

## 116. C04とL09a再開（11-14未明、BS-W16 §29）

C04を§115.1の型そのままで実装する。§115の5,384例の点検を先行確認として使う。
`PrefixCaesuras.prefixPosition` と `caesura_prefix_iff` を置き、元の語のcaesuraを保持する。
L09a・L09内の有限組合せは数の枠を撤廃する最新指示に従う。
追加の型と有限点検をその都度記録し、行数1,000ごとに停止せず報告する。
BE作用・operad・Tot・界面や別のまとまりの新しい主張の停止規則は維持する。

累計は、L09aの既存境界データ五本246行とR01・R02八本607行の **853行** から数える。
L09aのために新設した有限組合せのファイルも全て含める。
mainは凍結中なので取り込まず、自枝で対象ビルド・小さい専用監査だけを行う。

### 116.1 次の有限計算と型

`/tmp/bsw16/check-terminal-endpoints.py` で、接頭切断の全ての区間長から
復元切断のlo・hiを独立に計算して比較した（m=0〜5、q=0〜4）。
次のC05・C06は、有限順序の区間fiberの最小・最大で定義したlo・hiの特徴づけ。

```lean
lo_eq_of_bound {m q : ℕ} (s : Cut m q) (i : Fin (m + 1)) (n : ℕ)
    (j : Fin (m + q + 1)) (hj : s.horizontal j = i) (hv : (s.vertical j).val = n)
    (hb : ∀ k, s.horizontal k = i → n ≤ (s.vertical k).val) : lo s i = n
hi_eq_of_bound {m q : ℕ} (s : Cut m q) (i : Fin (m + 1)) (n : ℕ)
    (j : Fin (m + q + 1)) (hj : s.horizontal j = i) (hv : (s.vertical j).val = n)
    (hb : ∀ k, s.horizontal k = i → (s.vertical k).val ≤ n) : hi s i = n
```

所属する頂点での上下界は、この特徴づけの証明分割として置く。

### 116.2 端点の界の型（C07〜C09）

上記の区間長による917例の点検で、それぞれの区間の全頂点が次の界を満たすことも確認した。
`terminalPrefixVertex p k hk` は位置kを同じ値の接頭頂点として読む記法。

```lean
terminal_lo_lower_bound {m q : ℕ} (p : Fin (m + 1)) (s : Cut p.val q)
    (i : Fin (p.val + 1)) (k : Fin (m + (q + 1) + 1))
    (hc : (terminalExtend m q p s).horizontal k = prefixPosition p i) :
  lo s i ≤ ((terminalExtend m q p s).vertical k).val
terminal_hi_upper_bound {m q : ℕ} (p : Fin (m + 1)) (s : Cut p.val q)
    (i : Fin (p.val + 1)) (hip : i.val < p.val) (k : Fin (m + (q + 1) + 1))
    (hc : (terminalExtend m q p s).horizontal k = prefixPosition p i) :
  ((terminalExtend m q p s).vertical k).val ≤ hi s i
terminal_vertical_of_horizontal_gt {m q : ℕ} (p : Fin (m + 1)) (s : Cut p.val q)
    (i : Fin (m + 1)) (hip : p < i) (k : Fin (m + (q + 1) + 1))
    (hc : (terminalExtend m q p s).horizontal k = i) :
  (terminalExtend m q p s).vertical k = Fin.last (q + 1)
```

C07〜C09は色・区間の有限なfiberと端点の評価であり、BE作用の新しい主張ではない。

### 116.3 端点の復元式の型（C10〜C13）

§116.1の917例で次の等式を確認してからLeanへ入る。

```lean
lo_terminalExtend_prefix {m q : ℕ} (p : Fin (m + 1)) (s : Cut p.val q)
    (i : Fin (p.val + 1)) :
  lo (terminalExtend m q p s) (prefixPosition p i) = lo s i
hi_terminalExtend_prefix {m q : ℕ} (p : Fin (m + 1)) (s : Cut p.val q)
    (i : Fin (p.val + 1)) (hip : i.val < p.val) :
  hi (terminalExtend m q p s) (prefixPosition p i) = hi s i
hi_terminalExtend_at {m q : ℕ} (p : Fin (m + 1)) (s : Cut p.val q) :
  hi (terminalExtend m q p s) p = q + 1
endpoints_terminalExtend_suffix {m q : ℕ} (p : Fin (m + 1)) (s : Cut p.val q)
    (i : Fin (m + 1)) (hip : p < i) :
  lo (terminalExtend m q p s) i = q + 1 ∧ hi (terminalExtend m q p s) i = q + 1
```

L09a・L09の累計が1,000行を越えたところで、停止せずチャットでも途中報告した。
この時点ではC04とlo・hiの特徴づけが検証済み、復元区間の界以降を対象ビルド中。
τ・符号の相殺は未証明。C05〜C13は端点の有限計算に限っている。

### 116.4 元の語のcaesuraを保持する符号データ（C14〜C17）

次の式では、接頭部のcaesuraに置き換えず、元の語vのcaesuraを使う。
`prefixIndexOfLE p i h` は値iをFin(p+1)へ読む記法。

```lean
restoredLo p s i := if h : i ≤ p then lo s (prefixIndexOfLE p i h) else q + 1
restoredHi p s i := if h : i < p then hi s (prefixIndexOfLE p i h.le) else q + 1
restoredLength p s v i := restoredHi p s i - restoredLo p s i +
  if Surjection.Caesura v i then 1 else 0
restoredSignExponent p s v :=
  (∑ i, ∑ j, if i < j ∧ v j < v i then
    restoredLength p s v i * restoredLength p s v j else 0) +
  ∑ i, if Surjection.Caesura v i then restoredHi p s i else 0

lo_terminalExtend {m q : ℕ} (p : Fin (m + 1)) (s : Cut p.val q)
    (i : Fin (m + 1)) : lo (terminalExtend m q p s) i = restoredLo p s i
hi_terminalExtend {m q : ℕ} (p : Fin (m + 1)) (s : Cut p.val q)
    (i : Fin (m + 1)) : hi (terminalExtend m q p s) i = restoredHi p s i
intervalLength_terminalExtend {m q r : ℕ} (p : Fin (m + 1)) (s : Cut p.val q)
    (v : Fin (m + 1) → Fin r) (i : Fin (m + 1)) :
  intervalLength (terminalExtend m q p s) v i = restoredLength p s v i
cutSign_terminalExtend {m q r : ℕ} (p : Fin (m + 1)) (s : Cut p.val q)
    (v : Fin (m + 1) → Fin r) :
  cutSign (terminalExtend m q p s) v = (-1 : ℤ) ^ restoredSignExponent p s v
```

C14・C15は917例の端点点検の一括した式。
C16・C17も、以下の符号点検を先行してから実装に入る。
元の語を持つ数値の式であり、新しいBE作用やオペラッドの法則は定義しない。

### 116.5 検証済みの区切り（停止せず続行）

C04と端点・符号データの五本を検証した。`PrefixCaesuras` 42行、`IntervalExtrema` 57行、
`TerminalIntervalBounds` 90行、`TerminalEndpoints` 64行、`TerminalSignData` 77行、計330行。
符号指数の式はm=0〜3、q=0〜3、色数1〜3の全ての語で **8,206例**一致。
対象ビルド `lake build SerrePositivity.EInfinity.SimplexCuts.TerminalSignData` 成功。
専用監査は **5モジュール・47宣言・標準三公理のみ**、sorry・追加公理0。
ログは `/tmp/bsw16/m14-terminal-sign-data-02.log` と
`/tmp/bsw16/audit-m14-terminal-sign.log`。
登録候補はこの五本（名前は全て `SerrePositivity.EInfinity.SimplexCuts.` の下）。

L09a・L09の累計 **1,183行**、改訂MayのM14全体 **6,249行**。
1,000行の途中報告は済み、次は2,000行で報告する。τと境界の相殺は未証明。
最新のBS-W16 §30に従い、M15・G12は⑤dへ移ったので⑤aから進めない。
引継ぎ対象の既存の紙の報告は変更しない。mainへの取り込みも行わない。

## 117. 混合角の削除後の出力列（L09a続行）

`/tmp/bsw16/check-corner-sign.py` で全射・隣接非退化の語と混合角を列挙した。
m=1〜4、q=1〜3、色数1〜3の **9,536例**で、交換後に中間頂点を削除した各色の
出力列が一致し、BF符号とテンソル境界符号の積が反対になることを確認した。
これは符号のLean証明の代用にしない。
C18の列の一致自体は混合角の仮定が要らないので、
`/tmp/bsw16/check-corner-trace.py` で同じ向きの隣接辺も含む全経路を別に点検した。

```lean
def deletedTrace {m q r : ℕ} (s : Cut m q) (v : Fin (m + 1) → Fin r)
    (k : Fin (m + q + 1)) : List (Fin r × Fin (q + 1)) :=
  List.ofFn (fun j => (label s v (k.succAbove j), s.vertical (k.succAbove j)))

deletedTrace_swapSteps {m q r : ℕ} (s : Cut m q) (v : Fin (m + 1) → Fin r)
    (a b : Fin (m + q)) (hab : b.val = a.val + 1) :
  deletedTrace (s.swapSteps a b) v b.castSucc = deletedTrace s v b.castSucc
```

既存の `horizontal_swapSteps`・`vertical_swapSteps` を同じ省略頂点の補集合上で使う。
新しいBE作用ではなく、L09aの境界の二項を対応させるための有限列の照合である。

### 117.1 頂点削除を色の面番号へ運ぶ型（C19・C20）

C18は同向きの辺も含む550例で削除後の経路が一致した。
`check-corner-trace.py` の最初の点検では同向きの辺まで対称差で反転して失敗したため、
二つの位置の**交換**による像へ直した。Leanの `swapSteps` もこの交換を使う。

`/tmp/bsw16/check-color-erasure.py` で、長さ0〜6・色数1〜3の全語、
全ての色と範囲外も含む削除位置について、C20の式を点検してからLeanへ入る。
C19の列はその位置を `succAbove` で飛ばす同じ操作。

```lean
eraseIdx_ofFn {β : Type*} {N : ℕ} (f : Fin (N + 1) → β) (k : Fin (N + 1)) :
  (List.ofFn f).eraseIdx k.val = List.ofFn (fun j => f (k.succAbove j))
selectColor_eraseIdx {r : ℕ} {β : Type*} (c : Fin r) (l : List (Fin r × β)) (k : ℕ) :
  selectColor c (l.eraseIdx k) =
    if (l[k]?.map Prod.fst) = some c then
      (selectColor c l).eraseIdx (selectColor c (l.take k)).length
    else selectColor c l
```

削除される色のfiber内の面番号は、元の頂点より前に出た同色の個数である。

### 117.2 出力の面の位置を一つの経路の頂点へまとめる型（C21・C22）

長さ0〜6、色数1〜3の全ての語で、色と色内順位の組を元の位置へ戻す写像が
全位置を一回ずつ覆い、逆の色と先行同色数も一致することを点検した。
Leanでは既存の `Finset.orderIsoOfFin` と `Equiv.sigmaFiberEquiv` を合成する。

```lean
colorPositionEquiv {m q r : ℕ} (s : Cut m q) (u : Surjection.Word r (m + 1)) :
  (Σ a : Fin r, Fin (outputDegree s u a + 1)) ≃ Fin (m + q + 1)
outputBoundaryPositionEquiv {r d : ℕ} (u : Surjection.BasisWord (r + 1) d) (q : ℕ) :
  OutputBoundaryIndex u q ≃ Σ s : Cut (r + d) q, Fin (r + d + q + 1)
```

前者の正方向は各色の `orderEmbOfFin`、逆の色は `label s u.val k` そのもの。
零となる境界項を添字から先に消さず、零次の色の唯一の面番号も残す。

### 117.3 出力の角交換の対合（C23〜C25）

m=0〜5、q=0〜4の全経路と全指定頂点で、内部の前後の辺の交換が二回で戻ることを
点検してから実装する。同向きの辺では元の経路のまま、両端でも恒等とする。

```lean
def swapAtVertex {m q : ℕ} (s : Cut m q) (k : Fin (m + q + 1)) : Cut m q :=
  if h : 0 < k.val ∧ k.val < m + q then
    s.swapSteps (cornerLeftEdge k h) (cornerRightEdge k h) else s
swapAtVertex_involutive {m q : ℕ} (k : Fin (m + q + 1)) :
  Function.Involutive (fun s : Cut m q => swapAtVertex s k)
vertexCornerPerm (m q : ℕ) : Equiv.Perm (Σ _ : Cut m q, Fin (m + q + 1))
outputCornerPerm {r d : ℕ} (u : Surjection.BasisWord (r + 1) d) (q : ℕ) :
  Equiv.Perm (OutputBoundaryIndex u q)
outputCornerPerm_involutive {r d : ℕ} (u : Surjection.BasisWord (r + 1) d) (q : ℕ) :
  Function.Involutive (outputCornerPerm u q)
```

これは**全境界項のτではない**。混合角以外に残る固定点の境界項は零とは主張せず、
係数の文字削除・入力の面に対応させる段を別に残す。

### 117.4 実際の色の出力列の削除の型（C26〜C28）

C26〜C28は§117・§117.1の点検済みの列の式を切断へ特殊化する。
先行同色数がその色の範囲内であることも、同じ26,430例の点検で保持した。

```lean
vertexRank s v c k :=
  (selectColor c ((List.ofFn (fun i => (label s v i, s.vertical i))).take k.val)).length
deletedVerticesList s v k c :=
  if label s v k = c then (verticesList s v c).eraseIdx (vertexRank s v c k)
  else verticesList s v c

deletedVerticesList_eq_selectColor {m q r : ℕ} (s : Cut m q)
    (v : Fin (m + 1) → Fin r) (k : Fin (m + q + 1)) (c : Fin r) :
  deletedVerticesList s v k c = selectColor c (deletedTrace s v k)
deletedVerticesList_swapSteps {m q r : ℕ} (s : Cut m q)
    (v : Fin (m + 1) → Fin r) (a b : Fin (m + q)) (hab : b.val = a.val + 1)
    (c : Fin r) :
  deletedVerticesList (s.swapSteps a b) v b.castSucc c =
    deletedVerticesList s v b.castSucc c
vertexRank_lt_length {m q r : ℕ} (s : Cut m q) (v : Fin (m + 1) → Fin r)
    (k : Fin (m + q + 1)) :
  vertexRank s v (label s v k) k < (verticesList s v (label s v k)).length
```

### 117.5 昇順fiberの面番号の型（C29・C30）

N=0〜8の全ての部分集合の各昇順位置で、「前の元の数＝順位」を点検してからLeanへ入る。

```lean
card_filter_lt_orderEmbOfFin {α : Type*} [LinearOrder α] (t : Finset α) {N : ℕ}
    (h : t.card = N) (j : Fin N) :
  (t.filter (fun x => x < t.orderEmbOfFin h j)).card = j.val
colorPositionEquiv_rank {m q r : ℕ} (s : Cut m q)
    (u : Surjection.Word r (m + 1)) (a : Fin r) (j : Fin (outputDegree s u a + 1)) :
  ((colorPositions s u.val a).filter (fun k => k < colorPositionEquiv s u ⟨a, j⟩)).card = j.val
```

### 117.6 列の順位と面番号の一致の型（C31〜C33）

§117.1の26,430例と§117.2の1,227語の順位点検から、列の先行同色数と
有限集合の順位が一致する式を使う。C31は範囲外のkも含む点検の式の長さである。

```lean
selectColor_take_ofFn_length {r N : ℕ} {β : Type*} (f : Fin N → Fin r × β)
    (c : Fin r) (k : ℕ) :
  (selectColor c ((List.ofFn f).take k)).length =
    (Finset.univ.filter (fun i => i.val < k ∧ (f i).1 = c)).card
vertexRank_eq_card {m q r : ℕ} (s : Cut m q) (v : Fin (m + 1) → Fin r)
    (c : Fin r) (k : Fin (m + q + 1)) :
  vertexRank s v c k = ((colorPositions s v c).filter (fun i => i < k)).card
vertexRank_colorPositionEquiv {m q r : ℕ} (s : Cut m q)
    (u : Surjection.Word r (m + 1)) (a : Fin r) (j : Fin (outputDegree s u a + 1)) :
  vertexRank s u.val a (colorPositionEquiv s u ⟨a, j⟩) = j.val
```

### 117.7 同じ指定面と頂点列の型（C34〜C36）

正次数0〜4（元の頂点数2〜6）、終域次数0〜3の全ての弱単調写像と全ての削除位置で、
標準面との合成と頂点列の一文字削除が一致することを点検してからLeanへ入る。

```lean
simplexVertexList {n q : ℕ} (f : (⦋n⦌ : SimplexCategory) ⟶ ⦋q⦌) : List (Fin (q + 1))
simplexVertexList_injective (n q : ℕ) :
  Function.Injective (fun f : (⦋n⦌ : SimplexCategory) ⟶ ⦋q⦌ => simplexVertexList f)
simplexVertexList_delta {n q : ℕ}
    (f : (⦋n + 1⦌ : SimplexCategory) ⟶ ⦋q⦌) (j : Fin (n + 2)) :
  simplexVertexList (SimplexCategory.δ j ≫ f) = (simplexVertexList f).eraseIdx j.val
simplexVertexList_face {m q r : ℕ} (s : Cut m q)
    (u : Surjection.Word r (m + 1)) (a : Fin r) :
  simplexVertexList (face s u a) = verticesList s u.val a
```

面の一致をホモトピーで済ませず、元の単体圏の射の一致へ戻すための有限計算。

### 117.8 指定した出力面の列（C37〜C40）

C37〜C39は、§117.2の順位と§117.1の削除の点検の同じ式を指定の面番号で読んだもの。
C40は§117.7の標準面の点検を正次数で述べ直す。始域の等式による移送は定義評価。

```lean
vertexRank_symm_colorPositionEquiv {m q r : ℕ} (s : Cut m q)
    (u : Surjection.Word r (m + 1)) (k : Fin (m + q + 1)) :
  vertexRank s u.val (label s u.val k) k = ((colorPositionEquiv s u).symm k).2.val
label_colorPositionEquiv {m q r : ℕ} (s : Cut m q)
    (u : Surjection.Word r (m + 1)) (a : Fin r) (j : Fin (outputDegree s u a + 1)) :
  label s u.val (colorPositionEquiv s u ⟨a, j⟩) = a
deletedTrace_at_outputFace {m q r : ℕ} (s : Cut m q)
    (u : Surjection.Word r (m + 1)) (a : Fin r) (j : Fin (outputDegree s u a + 1))
    (c : Fin r) :
  selectColor c (deletedTrace s u.val (colorPositionEquiv s u ⟨a, j⟩)) =
    if c = a then (verticesList s u.val a).eraseIdx j.val else verticesList s u.val c
simplexVertexList_boundaryFace {n q : ℕ} (hn : 0 < n)
    (f : (⦋n⦌ : SimplexCategory) ⟶ ⦋q⦌) (j : Fin (n + 1)) :
  simplexVertexList (boundaryFace n hn j ≫ f) = (simplexVertexList f).eraseIdx j.val
simplexVertexList_cast_source {n n' q : ℕ} (h : n = n')
    (f : (⦋n'⦌ : SimplexCategory) ⟶ ⦋q⦌) :
  simplexVertexList (eqToHom (congrArg SimplexCategory.mk h) ≫ f) = simplexVertexList f
```

### 117.9 混合角と固定点の型（C41〜C43）

m=0〜5、q=0〜4の3,829個の指定頂点付き経路で、非固定点と内部の異向きの二辺が
ちょうど一致することを先に点検した。

```lean
swapSteps_eq_self_iff {m q : ℕ} (s : Cut m q) (a b : Fin (m + q)) :
  s.swapSteps a b = s ↔ (a ∈ s.val ↔ b ∈ s.val)
MixedVertex {m q : ℕ} (s : Cut m q) (k : Fin (m + q + 1)) : Prop :=
  ∃ h : 0 < k.val ∧ k.val < m + q,
    cornerLeftEdge k h ∈ s.val ↔ cornerRightEdge k h ∉ s.val
swapAtVertex_ne_iff {m q : ℕ} (s : Cut m q) (k : Fin (m + q + 1)) :
  swapAtVertex s k ≠ s ↔ MixedVertex s k
mixedVertex_swapAtVertex_iff {m q : ℕ} (s : Cut m q) (k : Fin (m + q + 1)) :
  MixedVertex (swapAtVertex s k) k ↔ MixedVertex s k
```

ここでの固定点は「出力の角交換」の固定点であり、全体のτの固定点とは区別する。

## 118. 全境界の有限な対応候補を点検（L09a続行）

`/tmp/bsw16/check-boundary-pairing.py` に、経路の指定頂点の次の対応を独立に書いた。
水平・水平（端点で水平辺の場合も含む）はゼロ長の区間を消して係数の文字削除へ、
垂直・垂直（端点も含む）は垂直辺を一本消して入力面へ、混合角は前後の辺を交換する。
水平次数0の余分な係数添字、入力次数0の入力面添字、総次数0の出力添字は固定する。
逆は、係数位置で水平なゼロ長区間を挿入、入力面の指定レベルで垂直辺を挿入する。

m=0〜5、q=0〜4の **6,070添字**で二回の対応が恒等になることを確認。
さらにm=0〜4、q=0〜3、色数1〜3の全射・隣接非退化の語について、
`cutSign`・`deletionCoefficient`・テンソルの境界のKoszul符号・入力面の負号を保ち、
重複した出力頂点を零とする独立な計算で **38,322項**が反対の値になった。
これからこの候補をLeanで構成する。有限点検だけからτや境界の等式を宣言しない。

### 118.1 分岐の型（C44〜C46）

```lean
inductive BoundaryVertexKind
  | horizontal | vertical | mixed | isolated
boundaryVertexKind {m q : ℕ} (s : Cut m q) (k : Fin (m + q + 1)) : BoundaryVertexKind
boundaryVertexKind_eq_mixed_iff {m q : ℕ} (s : Cut m q) (k : Fin (m + q + 1)) :
  boundaryVertexKind s k = .mixed ↔ MixedVertex s k
boundaryVertexKind_eq_isolated_iff {m q : ℕ} (s : Cut m q) (k : Fin (m + q + 1)) :
  boundaryVertexKind s k = .isolated ↔ m = 0 ∧ q = 0
```

C44は前後の辺の所属の判定、C45・C46は上記6,070添字の分岐を点検した条件。

### 118.2 水平境界に対応する一頂点の区間（C47・C48）

m=0〜5、q=0〜5の全ての区間長の列で、一頂点のfiberと零長区間の条件を点検してから
Leanへ入る。区間の非空性と既存の経路の頂点の単射性から証明する。

```lean
intervalPositions_card_eq_one_iff {m q : ℕ} (s : Cut m q) (i : Fin (m + 1)) :
  (intervalPositions s i).card = 1 ↔ lo s i = hi s i
interval_gap_eq_zero_iff {m q : ℕ} (s : Cut m q) (i : Fin (m + 1)) :
  hi s i - lo s i = 0 ↔ (intervalPositions s i).card = 1
```

### 118.3 語に依らない境界添字と種類の分割（C49・C50）

§118の6,070添字の点検の各分岐を、その種類の部分型に分ける。
有限の直和への分割は、各指定頂点を一回だけ保持する。

```lean
abbrev MarkedCut (m q : ℕ) := Σ _ : Cut m q, Fin (m + q + 1)
abbrev BoundaryVertexOfKind (m q : ℕ) (b : BoundaryVertexKind) :=
  {t : MarkedCut m q // boundaryVertexKind t.1 t.2 = b}
boundaryVertexPartitionEquiv (m q : ℕ) : MarkedCut m q ≃
  BoundaryVertexOfKind m q .horizontal ⊕ (BoundaryVertexOfKind m q .vertical ⊕
    (BoundaryVertexOfKind m q .mixed ⊕ BoundaryVertexOfKind m q .isolated))
abbrev UniversalBoundaryIndex (m q : ℕ) :=
  MarkedCut m q ⊕ ((Fin (m + 1) × Cut (m - 1) q) ⊕ (Fin (q + 1) × Cut m (q - 1)))
boundaryBalanceIndexEquiv {r d : ℕ} (u : Surjection.BasisWord (r + 1) d) (q : ℕ) :
  BoundaryBalanceIndex u q ≃ UniversalBoundaryIndex (r + d) q
```

最後の同値は出力面の位置の同値を直和へ運ぶだけで、元の境界項の型を変更しない。

### 118.4 端点・内部の判定の評価（C51〜C53）

§118の全指定頂点の分岐の点検と同じ形で、定義を次の式へ評価する。

```lean
boundaryVertexKind_zero {m q : ℕ} (s : Cut m q) (hN : 0 < m + q) :
  boundaryVertexKind s 0 =
    if (⟨0, hN⟩ : Fin (m + q)) ∈ s.val then .horizontal else .vertical
boundaryVertexKind_last {m q : ℕ} (s : Cut m q) (hN : 0 < m + q) :
  boundaryVertexKind s (Fin.last (m + q)) =
    if (⟨m + q - 1, by omega⟩ : Fin (m + q)) ∈ s.val then .horizontal else .vertical
boundaryVertexKind_interior {m q : ℕ} (s : Cut m q) (k : Fin (m + q + 1))
    (h : 0 < k.val ∧ k.val < m + q) :
  boundaryVertexKind s k =
    if cornerLeftEdge k h ∈ s.val then
      if cornerRightEdge k h ∈ s.val then .horizontal else .mixed
    else if cornerRightEdge k h ∈ s.val then .mixed else .vertical
```

### 118.5 一頂点のfiberと隣接辺（C54〜C56）

有限単調写像（始域次数0〜5、終域次数0〜3）の全ての指定頂点で、
fiberが一頂点であることと両側の厳密な増分の条件を点検してからLeanへ入る。
水平辺の増分自体は、§118の全経路の既存の辺の向きの点検でも確認している。

```lean
mem_iff_horizontal_lt {m q : ℕ} (s : Cut m q) (a : Fin (m + q)) :
  a ∈ s.val ↔ s.horizontal a.castSucc < s.horizontal a.succ
monotone_fiber_singleton_iff {N M : ℕ} (f : Fin (N + 1) →o Fin (M + 1))
    (k : Fin (N + 1)) :
  (∀ j, f j = f k → j = k) ↔
    (∀ a : Fin N, a.succ = k → f a.castSucc < f k) ∧
    (∀ a : Fin N, a.castSucc = k → f k < f a.succ)
HorizontalVertex {m q : ℕ} (s : Cut m q) (k : Fin (m + q + 1)) : Prop :=
  (∀ a : Fin (m + q), a.succ = k → a ∈ s.val) ∧
  (∀ a : Fin (m + q), a.castSucc = k → a ∈ s.val)
horizontal_fiber_singleton_iff {m q : ℕ} (s : Cut m q) (k : Fin (m + q + 1)) :
  (∀ j, s.horizontal j = s.horizontal k → j = k) ↔ HorizontalVertex s k
```

総次数零では左右の辺の条件は空となる点を保持し、零次の余分な係数添字の分岐を潰さない。

### 118.6 水平境界の判定と隣接辺の型（C57〜C60）

§118の全指定頂点の分岐の点検と§118.5のfiberの点検を、同じ左右の辺の条件で述べる。

```lean
horizontalVertex_interior_iff {m q : ℕ} (s : Cut m q) (k : Fin (m + q + 1))
    (h : 0 < k.val ∧ k.val < m + q) :
  HorizontalVertex s k ↔ cornerLeftEdge k h ∈ s.val ∧ cornerRightEdge k h ∈ s.val
horizontalVertex_zero_iff {m q : ℕ} (s : Cut m q) (hN : 0 < m + q) :
  HorizontalVertex s 0 ↔ (⟨0, hN⟩ : Fin (m + q)) ∈ s.val
horizontalVertex_last_iff {m q : ℕ} (s : Cut m q) (hN : 0 < m + q) :
  HorizontalVertex s (Fin.last (m + q)) ↔
    (⟨m + q - 1, by omega⟩ : Fin (m + q)) ∈ s.val
boundaryVertexKind_eq_horizontal_iff {m q : ℕ} (s : Cut m q)
    (k : Fin (m + q + 1)) :
  boundaryVertexKind s k = .horizontal ↔ 0 < m + q ∧ HorizontalVertex s k
```

### 118.7 水平境界と零長区間の型（C61〜C63）

§118の全指定頂点の点検では、水平に分類した頂点の区間は零長であり、水平次数は正。
§118.2のfiberの点検と同じ条件を合わせる。

```lean
horizontalVertex_iff_card_eq_one {m q : ℕ} (s : Cut m q)
    (k : Fin (m + q + 1)) :
  HorizontalVertex s k ↔ (intervalPositions s (s.horizontal k)).card = 1
boundaryVertexKind_eq_horizontal_gap {m q : ℕ} (s : Cut m q)
    (k : Fin (m + q + 1)) :
  boundaryVertexKind s k = .horizontal ↔
    0 < m + q ∧ hi s (s.horizontal k) - lo s (s.horizontal k) = 0
horizontal_kind_pos {m q : ℕ} (s : Cut m q) (k : Fin (m + q + 1))
    (hk : boundaryVertexKind s k = .horizontal) : 0 < m
```

### 118.8 検証済みの区切りと2,000行の途中報告

§117〜§118.7の17モジュール、計 **1,031行**を対象ビルドで検証した。
`CornerTraces`・`VertexErasure`・`BoundaryPositions`・`CornerInvolution`・`DeletedVertices`・
`FiberRanks`・`VertexRanks`・`FaceVertexLists`・`BoundaryVertexLists`・`CornerFixedPoints`・
`BoundaryKinds`・`IntervalSingletons`・`BoundaryPartition`・`BoundaryKindValues`・
`SingletonFiberSteps`・`HorizontalVertexKinds`・`HorizontalSingletons`。
名前の接頭部は全て `SerrePositivity.EInfinity.SimplexCuts.`。次の登録候補一覧はこの17本。

専用監査 `/tmp/bsw16/audit-m14-boundary-fibers.lean` は
**17モジュール・164宣言・標準三公理のみ**。
対象ビルドは `/tmp/bsw16/m14-horizontal-singletons-01.log` などに成功を確認。
新規ソースにsorry・追加公理0、警告も解消。rootや全体監査は回していない。

この時点でL09a・L09の累計 **2,214行**、改訂MayのM14全体 **7,280行**。
2,000行を越えた途中報告は停止せずチャットでも行った。次は3,000行で報告する。
全体のτ、BFの境界の相殺・微分の等式はまだ証明していない。
水平な端点の挿入の同値へ続ける。

### 118.9 水平端点の挿入の同値の型（C64〜C66）

§118の6,070添字の往復の点検のうち、水平な始点・終点を挿入する分岐を使う。
既存の `BarrattEccles.horizontalInsertionEquiv` へ、固定した頂点の条件を付ける。

```lean
fixedMarkedCutEquiv {m q : ℕ} (b : BoundaryVertexKind) (k : Fin (m + q + 1)) :
  {s : Cut m q // boundaryVertexKind s k = b} ≃
    {t : MarkedCut m q // boundaryVertexKind t.1 t.2 = b ∧ t.2 = k}
horizontalFirstFaceEquiv (m q : ℕ) : Cut m q ≃
  {t : MarkedCut (m + 1) q // boundaryVertexKind t.1 t.2 = .horizontal ∧ t.2 = 0}
horizontalLastFaceEquiv (m q : ℕ) : Cut m q ≃
  {t : MarkedCut (m + 1) q // boundaryVertexKind t.1 t.2 = .horizontal ∧
    t.2 = Fin.last (m + 1 + q)}
```

### 118.10 水平内部面の挿入の同値の型（C67・C68）

§118の6,070添字の往復の点検のうち、内部の水平・水平の分岐を使う。
既存の `horizontalMarkedEdgeEquiv` と `horizontalCornerEquiv` を合成し、
角の中間頂点の値をa+1として指定頂点付き経路へ移す。

```lean
HorizontalInteriorFace (m q : ℕ) :=
  {t : MarkedCut (m + 1) q // boundaryVertexKind t.1 t.2 = .horizontal ∧
    0 < t.2.val ∧ t.2.val < m + 1 + q}
horizontalCornerFaceEquiv (m q : ℕ) :
  BarrattEccles.HorizontalCorner m q ≃ HorizontalInteriorFace m q
horizontalInteriorFaceEquiv (m q : ℕ) :
  Cut m q × Fin m ≃ HorizontalInteriorFace m q
```

### 118.11 水平な三分岐の同値までの検証済み区切り

`HorizontalEndpointFaces` 53行、`HorizontalInteriorFaces` 86行、計139行を対象ビルドで検証した。
水平な始点・終点・内部のそれぞれで、小さい切断から水平辺を挿入する同値が閉じた。
既存のshuffleの角の挿入を利用し、公開宣言の定義は変更していない。

対象ビルド `lake build SerrePositivity.EInfinity.SimplexCuts.HorizontalInteriorFaces` 成功
（`/tmp/bsw16/m14-horizontal-interior-faces-03.log`）。
専用監査 `/tmp/bsw16/audit-m14-horizontal-faces.lean` は
**2モジュール・44宣言・標準三公理のみ**。
新規二本にsorry・追加公理0、Leanの警告なし。次の登録候補はこの二本も含む。
それぞれのビルド・監査だけ鍵を取り、終了時に返した。root・全体監査は回していない。

L09a・L09の累計 **2,353行**、改訂MayのM14全体 **7,419行**。
C04再開後の新規分は、五本330行、十七本1,031行、二本139行、計 **1,500行**。
外枠25,000行と半分の12,500行には届いていない。
有限組合せの追加の数では停止しない最新の規則を維持する。

次に残る有限対応は、水平な三分岐を係数の `Fin (m + 2) × Cut m q` へまとめること、
垂直な始点・終点・内部の対応、および混合角との直和で全体のτを作ること。
その後の符号と正規化した境界項の反対の値のLean証明も未完。
§118の38,322項のPython点検を、それらのLean証明として扱っていない。
G10・Tot・界面・新しいBE作用・operadの法則は作っておらず、M15・G12にも手を付けない。
main凍結を維持し、以上は自枝の検証済み保存の区切りとして記録する。

## 119. 共通の一覧の数え方へ移行して続行（11-14）

最新のcoordination.md §2に従い、既存の構成の法則（単位・余単位・自然性・係数移送・
合成則・貼り合わせ）と証明分割に数の枠を置かない。型を報告に記録し、
200行を超える補題には行数も記す。L09a・L09の有限組合せの事前点検、
1,000行ごとの途中報告、M14全体25,000行の外枠は維持する。
mainは凍結中で、自枝の対象ビルド・小さい専用監査だけを行う。

### 119.1 既存の種類の部分型を三分岐へ貼り合わせる型（C69）

総次数N=1〜12の全90頂点で、始点・内部・終点のちょうど一つに属することを確認。
この有限の位置の判定を、既存の境界種類の部分型に付ける。

```lean
FirstBoundaryFace (m q : ℕ) (b : BoundaryVertexKind) :=
  {t : MarkedCut m q // boundaryVertexKind t.1 t.2 = b ∧ t.2 = 0}
InteriorBoundaryFace (m q : ℕ) (b : BoundaryVertexKind) :=
  {t : MarkedCut m q // boundaryVertexKind t.1 t.2 = b ∧ 0 < t.2.val ∧ t.2.val < m + q}
LastBoundaryFace (m q : ℕ) (b : BoundaryVertexKind) :=
  {t : MarkedCut m q // boundaryVertexKind t.1 t.2 = b ∧ t.2 = Fin.last (m + q)}
boundaryEndpointPartitionEquiv (m q : ℕ) (b : BoundaryVertexKind) (hN : 0 < m + q) :
  BoundaryVertexOfKind m q b ≃ FirstBoundaryFace m q b ⊕
    (InteriorBoundaryFace m q b ⊕ LastBoundaryFace m q b)
```

### 119.2 水平な三分岐の貼り合わせの型（C70・C71）

§118の水平境界の全ての往復の点検と§119.1の位置の分割の点検を使う。
既存の `finSumFinEquiv`、積の直和への分配、三つの挿入同値を合成する。

```lean
singletonSlotProdEquiv (X : Type*) : Fin 1 × X ≃ X
firstInteriorLastIndexEquiv (m : ℕ) : Fin (m + 2) ≃ Fin 1 ⊕ (Fin m ⊕ Fin 1)
coefficientIndexEndpointEquiv (m q : ℕ) :
  Fin (m + 2) × Cut m q ≃ Cut m q ⊕ ((Cut m q × Fin m) ⊕ Cut m q)
horizontalBoundaryFaceEquiv (m q : ℕ) :
  Fin (m + 2) × Cut m q ≃ BoundaryVertexOfKind (m + 1) q .horizontal
```

新しい作用や定理を仮定せず、検証済みの水平な三分岐を同じ有限添字に貼り合わせる。

### 119.3 既存の方向交換と境界種類の照合（C72〜C74）

m=0〜5、q=0〜4の全3,829個の指定頂点付き経路で、水平辺の補集合への交換が
水平・垂直の判定を交換し、混合・単独頂点を保つことを点検してから実装する。
`setBoundaryKind` は既存の `boundaryVertexKind` と同じ有限判定を、全辺数と集合だけで読む記法。

```lean
BoundaryVertexKind.exchange : BoundaryVertexKind → BoundaryVertexKind
BoundaryVertexKind.exchange_involutive : Function.Involutive BoundaryVertexKind.exchange
setBoundaryKind {N : ℕ} (s : Finset (Fin N)) (k : Fin (N + 1)) : BoundaryVertexKind
boundaryVertexKind_eq_setBoundaryKind {m q : ℕ} (s : Cut m q)
    (k : Fin (m + q + 1)) : boundaryVertexKind s k = setBoundaryKind s.val k
setBoundaryKind_compl {N : ℕ} (s : Finset (Fin N)) (k : Fin (N + 1)) :
  setBoundaryKind sᶜ k = (setBoundaryKind s k).exchange
setBoundaryKind_map_finCongr {N N' : ℕ} (h : N = N') (s : Finset (Fin N))
    (k : Fin (N + 1)) :
  setBoundaryKind (s.map (finCongr h).toEmbedding) (Fin.cast (congrArg (· + 1) h) k) =
    setBoundaryKind s k
boundaryVertexKind_exchange {m q : ℕ} (s : Cut m q) (k : Fin (m + q + 1)) :
  boundaryVertexKind s.exchange (Fin.cast (by omega : m + q + 1 = q + m + 1) k) =
    (boundaryVertexKind s k).exchange
```

新しい作用は作らず、既存の `shuffleExchangeEquiv` と有限な辺集合の判定を照合する法則。

### 119.4 垂直境界への既存の同値の移送の型（C75〜C78）

§118の垂直分岐の全ての往復と§119.3の方向交換の点検を使う。
水平側の同値と方向交換の同値を合成し、別に垂直側の三分岐を作り直さない。

```lean
markedCutExchangeEquiv (m q : ℕ) : MarkedCut m q ≃ MarkedCut q m
boundaryKindExchangeEquiv (m q : ℕ) (b : BoundaryVertexKind) :
  BoundaryVertexOfKind m q b ≃ BoundaryVertexOfKind q m b.exchange
verticalBoundaryFaceEquiv (m q : ℕ) :
  Fin (q + 2) × Cut m q ≃ BoundaryVertexOfKind m (q + 1) .vertical
vertical_kind_pos {m q : ℕ} (s : Cut m q) (k : Fin (m + q + 1))
    (hk : boundaryVertexKind s k = .vertical) : 0 < q
```

### 119.5 全境界の同じ添字への書き換え（C79〜C82）

既存の水平・垂直の同値を、正の次数と前者の次数への添字で述べ直す。
混合角の種類の保存と対合の式は、検証済みの角交換の法則の同じ式の書き換え。
点検は§118の全境界の往復と§117.9の混合角の点検に含まれる。

```lean
horizontalBoundaryAllEquiv (m q : ℕ) (hm : 0 < m) :
  Fin (m + 1) × Cut (m - 1) q ≃ BoundaryVertexOfKind m q .horizontal
verticalBoundaryAllEquiv (m q : ℕ) (hq : 0 < q) :
  Fin (q + 1) × Cut m (q - 1) ≃ BoundaryVertexOfKind m q .vertical
mixed_kind_swapAtVertex {m q : ℕ} (s : Cut m q) (k : Fin (m + q + 1))
    (hk : boundaryVertexKind s k = .mixed) :
  boundaryVertexKind (swapAtVertex s k) k = .mixed
vertexCornerPerm_involutive (m q : ℕ) : Function.Involutive (vertexCornerPerm m q)
```

### 119.6 検証済みの同値を全境界へ貼り合わせる型（C83〜C86）

§118の6,070添字の往復の点検で使った対応を、既存の挿入同値・方向交換・角交換で作る。
水平・垂直の正の次数を満たさない余分な右辺添字と、単独の出力頂点は固定する。

```lean
universalBoundaryPartner (m q : ℕ) : UniversalBoundaryIndex m q → UniversalBoundaryIndex m q
universalBoundaryPartner_involutive (m q : ℕ) : Function.Involutive (universalBoundaryPartner m q)
universalBoundaryPerm (m q : ℕ) : Equiv.Perm (UniversalBoundaryIndex m q)
boundaryBalancePerm {r d : ℕ} (u : Surjection.BasisWord (r + 1) d) (q : ℕ) :
  Equiv.Perm (BoundaryBalanceIndex u q)
boundaryBalancePerm_involutive {r d : ℕ} (u : Surjection.BasisWord (r + 1) d) (q : ℕ) :
  Function.Involutive (boundaryBalancePerm u q)
```

これはL09aのτの**添字上の候補**。符号付き境界項の相殺・固定点の値が零であることは
まだこの宣言に含めず、その証明は残す。候補を前提にL09や作用の法則を宣言しない。

### 119.7 全境界の対合候補の固定点の型（C87・C88）

§118の6,070添字の点検では、対合の固定点は次の零次数の余分な添字だけだった。
この点検は候補の往復だけでなく、固定点の条件も分類したものとして使う。
混合角の非固定性は検証済みの `swapAtVertex_ne_iff` の同じ式。

```lean
mixed_vertexCornerPerm_ne {m q : ℕ} (t : MarkedCut m q)
    (ht : boundaryVertexKind t.1 t.2 = .mixed) : vertexCornerPerm m q t ≠ t
universalBoundaryPartner_fixed_iff (m q : ℕ) (i : UniversalBoundaryIndex m q) :
  universalBoundaryPartner m q i = i ↔
    match i with
    | .inl _ => m = 0 ∧ q = 0
    | .inr (.inl _) => m = 0
    | .inr (.inr _) => q = 0
boundaryBalancePerm_fixed_iff {r d : ℕ} (u : Surjection.BasisWord (r + 1) d)
    (q : ℕ) (i : BoundaryBalanceIndex u q) :
  boundaryBalancePerm u q i = i ↔
    universalBoundaryPartner (r + d) q ((boundaryBalanceIndexEquiv u q) i) =
      (boundaryBalanceIndexEquiv u q) i
```

### 119.8 L09aの固定点の零の部分

C87の固定点の条件は6,070添字で明示的に再確認した。
§118の38,322項の符号付き値の点検では、固定点は全て零だった。
その部分を元の境界項の定義へ戻す。L09aの一覧にある固定点の零の主張の証明分割であり、
別の作用・定理を追加するものではない。

```lean
boundaryBalancePerm_fixed_zero (A : Type u) [CommRing A] (S : SSet.{0})
    {r d : ℕ} (w : Surjection.BasisWord (r + 1) d) (q : ℕ)
    (i : BoundaryBalanceIndex w q) (hi : boundaryBalancePerm w q i = i) (x : S _⦋q⦌) :
  boundaryBalanceTerm A S w q i x = 0
```

出力側はr=d=q=0、係数側はd=0、入力側はq=0に帰着する。
出力側の色の次数は、全頂点数が1である有限濃度評価から零と判定する。

### 119.9 貼り合わせた対合の評価式

以下は検証済みの対合の各分岐の定義評価であり、数の枠を置かない既存構成の法則の補題。
点検は§118の同じ6,070添字の対応の式を使う。

```lean
universalBoundaryPartner_horizontal (m q : ℕ) (hm : 0 < m)
    (t : BoundaryVertexOfKind m q .horizontal) :
  universalBoundaryPartner m q (.inl t.val) =
    .inr (.inl ((horizontalBoundaryAllEquiv m q hm).symm t))
universalBoundaryPartner_vertical (m q : ℕ) (hq : 0 < q)
    (t : BoundaryVertexOfKind m q .vertical) :
  universalBoundaryPartner m q (.inl t.val) =
    .inr (.inr ((verticalBoundaryAllEquiv m q hq).symm t))
universalBoundaryPartner_mixed (m q : ℕ) (t : BoundaryVertexOfKind m q .mixed) :
  universalBoundaryPartner m q (.inl t.val) = .inl (vertexCornerPerm m q t.val)
universalBoundaryPartner_coefficient (m q : ℕ) (hm : 0 < m)
    (c : Fin (m + 1) × Cut (m - 1) q) :
  universalBoundaryPartner m q (.inr (.inl c)) = .inl ((horizontalBoundaryAllEquiv m q hm) c).val
universalBoundaryPartner_input (m q : ℕ) (hq : 0 < q)
    (v : Fin (q + 1) × Cut m (q - 1)) :
  universalBoundaryPartner m q (.inr (.inr v)) = .inl ((verticalBoundaryAllEquiv m q hq) v).val
universalBoundaryPartner_isolated (m q : ℕ) (t : BoundaryVertexOfKind m q .isolated) :
  universalBoundaryPartner m q (.inl t.val) = .inl t.val
```

### 119.10 L09aの三群の等式の貼り合わせ

同じ対合の既存の評価式を使う証明分割。三群の仮定は今後閉じる本来の相殺であり、
未供給の等式を公理や暗黙の前提として最終結果へ入れない。

```lean
universalBoundaryPartner_neg_of_cases {B : Type*} [AddCommGroup B] (m q : ℕ)
    (F : UniversalBoundaryIndex m q → B)
    (hfixed : ∀ i, universalBoundaryPartner m q i = i → F i = 0)
    (hc : ∀ (hm : 0 < m) (c : Fin (m + 1) × Cut (m - 1) q),
      F (.inl ((horizontalBoundaryAllEquiv m q hm) c).val) = -F (.inr (.inl c)))
    (hv : ∀ (hq : 0 < q) (v : Fin (q + 1) × Cut m (q - 1)),
      F (.inl ((verticalBoundaryAllEquiv m q hq) v).val) = -F (.inr (.inr v)))
    (hmix : ∀ t : BoundaryVertexOfKind m q .mixed,
      F (.inl (vertexCornerPerm m q t.val)) = -F (.inl t.val))
    (i : UniversalBoundaryIndex m q) :
  F (universalBoundaryPartner m q i) = -F i
```

実際の境界値については `hfixed` は§119.8で証明済み。
`hc`・`hv`・`hmix` の符号と指定面の照合が残る。全項の相殺をこの補題だけから主張しない。

### 119.11 実際の境界値の同じ添字への移送の型

既存の境界値を、検証済みの添字の同値に沿って読む定義とその評価の法則。
元の複体・境界項・界面の型は変えない。

```lean
universalBoundaryValue (A : Type u) [CommRing A] (S : SSet.{0})
    {r d : ℕ} (w : Surjection.BasisWord (r + 1) d) (q : ℕ) (x : S _⦋q⦌) :
  UniversalBoundaryIndex (r + d) q →
    (power (chains A S) (r + 1)).X (-((d + q : ℕ) : ℤ) + 1)
universalBoundaryValue_at_index (A : Type u) [CommRing A] (S : SSet.{0})
    {r d : ℕ} (w : Surjection.BasisWord (r + 1) d) (q : ℕ) (x : S _⦋q⦌)
    (i : BoundaryBalanceIndex w q) :
  universalBoundaryValue A S w q x ((boundaryBalanceIndexEquiv w q) i) =
    boundaryBalanceTerm A S w q i x
universalBoundaryValue_partner (A : Type u) [CommRing A] (S : SSet.{0})
    {r d : ℕ} (w : Surjection.BasisWord (r + 1) d) (q : ℕ) (x : S _⦋q⦌)
    (i : BoundaryBalanceIndex w q) :
  universalBoundaryValue A S w q x
    (universalBoundaryPartner (r + d) q ((boundaryBalanceIndexEquiv w q) i)) =
      boundaryBalanceTerm A S w q (boundaryBalancePerm w q i) x
universalBoundaryValue_fixed_zero (A : Type u) [CommRing A] (S : SSet.{0})
    {r d : ℕ} (w : Surjection.BasisWord (r + 1) d) (q : ℕ) (x : S _⦋q⦌)
    (i : UniversalBoundaryIndex (r + d) q) (hi : universalBoundaryPartner (r + d) q i = i) :
  universalBoundaryValue A S w q x i = 0
```

### 119.12 同方向の削除の指定列の照合（C89・C90）

m=0〜5、q=0〜4の全経路の内部の水平・水平、垂直・垂直の箇所で、
中間頂点の削除の列が、一本の辺を消した小さい経路の指定座標を一つ飛ばす列と一致することを
点検してから実装する。Leanでは既存の `horizontalDeletion_horizontal`・
`horizontalDeletion_vertical`・`verticalDeletion_horizontal`・`verticalDeletion_vertical` を使う。

```lean
horizontal_deletedTrace {m q r : ℕ} (s : Cut (m + 1) q)
    (v : Fin (m + 2) → Fin r) (a b : Fin (m + 1 + q)) (hab : b.val = a.val + 1)
    (ha : a ∈ s.val) (hb : b ∈ s.val) :
  deletedTrace s v a.succ = List.ofFn (fun k : Fin (m + q + 1) =>
    (Surjection.erase v (s.horizontal a.succ)
      (((BarrattEccles.horizontalInsertionEquiv m q a).symm ⟨s, ha⟩).horizontal k),
    ((BarrattEccles.horizontalInsertionEquiv m q a).symm ⟨s, ha⟩).vertical k))
vertical_deletedTrace {m q r : ℕ} (s : Cut m (q + 1))
    (v : Fin (m + 1) → Fin r) (a b : Fin (m + (q + 1))) (hab : b.val = a.val + 1)
    (ha : a ∉ s.val) (hb : b ∉ s.val) :
  deletedTrace s v a.succ = List.ofFn (fun k : Fin (m + q + 1) =>
    (v (((BarrattEccles.verticalInsertionEquiv m q a).symm ⟨s, ha⟩).horizontal k),
    (s.vertical a.succ).succAbove
      (((BarrattEccles.verticalInsertionEquiv m q a).symm ⟨s, ha⟩).vertical k)))
```

### 119.13 符号次数を出力次数へ結ぶ有限濃度の型（C91・C92）

m=0〜5、q=0〜5の4,752個の区間fiberで、位置の連続性と
「頂点数＝両端の垂直座標の差＋1」を点検してからLeanへ入る。

```lean
intervalPositions_eq_Icc {m q : ℕ} (s : Cut m q) (i : Fin (m + 1)) :
  intervalPositions s i = Finset.Icc
    ((intervalPositions s i).min' (intervalPositions_nonempty s i))
    ((intervalPositions s i).max' (intervalPositions_nonempty s i))
intervalPositions_card {m q : ℕ} (s : Cut m q) (i : Fin (m + 1)) :
  (intervalPositions s i).card = hi s i - lo s i + 1
```

### 119.14 各色のcaesuraの濃度（C93〜C95）

長さ1〜6・色数1〜3の全射語の全ての色で、caesuraが最後の一出現を除いた集合であり、
最後より前の位置であることを点検してからLeanへ入る。
既存の `Surjection.Word.lastOccurrence` の値と最大性を使う。

```lean
caesura_iff_lt_lastOccurrence {n l : ℕ} (u : Surjection.Word n l)
    (c : Fin n) (i : Fin l) (hi : u.val i = c) :
  Surjection.Caesura u.val i ↔ i < u.lastOccurrence c
caesura_filter_occurrences {n l : ℕ} (u : Surjection.Word n l) (c : Fin n) :
  (Surjection.occurrences u.val c).filter (Surjection.Caesura u.val) =
    (Surjection.occurrences u.val c).erase (u.lastOccurrence c)
sum_caesura_occurrences_add_one {n l : ℕ} (u : Surjection.Word n l) (c : Fin n) :
  (∑ i ∈ Surjection.occurrences u.val c, if Surjection.Caesura u.val i then 1 else 0) + 1 =
    (Surjection.occurrences u.val c).card
```

### 119.15 出力次数と区間の符号次数（C96・C97）

m=0〜4、q=0〜4の全切断区間長、色数1〜3の全射語の各色で、
「出力次数＝同じ色の区間の符号次数の和」を点検してからLeanへ入る。
C96は同じ列の色のfiberを水平座標のfiberに分ける濃度式で、全射性は不要。

```lean
colorPositions_card_by_intervals {m q r : ℕ} (s : Cut m q)
    (v : Fin (m + 1) → Fin r) (c : Fin r) :
  (colorPositions s v c).card =
    ∑ i ∈ Surjection.occurrences v c, (intervalPositions s i).card
outputDegree_eq_sum_intervalLength {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (c : Fin r) :
  outputDegree s v c = ∑ i ∈ Surjection.occurrences v.val c, intervalLength s v.val i
```

出力の境界のKoszul指数と `permutationExponent` を同じ区間の重みで計算するための有限の濃度評価。

### 119.16 既存の逆転数の削除公式と境界符号（C98・C99）

位置数1〜5、色数1〜3の全ての語・非空位置部分集合・その中の削除位置で、
次の整数指数の式を点検してからLeanへ入る。
既存の `IntervalCuts.positionInversionCount_erase` に各位置の寄与の恒等式を足す。

```lean
colorSorting_boundary_term {N r : ℕ} (v : Fin N → Fin r) (a b : Fin N) :
  positionInversionTerm v a b + positionInversionTerm v b a +
    (if v b < v a then 1 else 0) + (if b < a ∧ v b = v a then 1 else 0) =
  (if b < a then 1 else 0) + 2 * positionInversionTerm v a b
positionInversionCount_boundary {N r : ℕ} (v : Fin N → Fin r)
    (s : Finset (Fin N)) (a : Fin N) (ha : a ∈ s) :
  positionInversionCount v s + (s.filter (fun b => v b < v a)).card +
    (s.filter (fun b => b < a ∧ v b = v a)).card =
  positionInversionCount v (s.erase a) + (s.filter (fun b => b < a)).card +
    2 * (∑ b ∈ s, positionInversionTerm v a b)
colorSorting_boundary_sign {N r : ℕ} (v : Fin N → Fin r)
    (s : Finset (Fin N)) (a : Fin N) (ha : a ∈ s) :
  (-1 : ℤ) ^ (positionInversionCount v s + (s.filter (fun b => v b < v a)).card +
    (s.filter (fun b => b < a ∧ v b = v a)).card) =
  (-1 : ℤ) ^ positionInversionCount v (s.erase a) *
    (-1 : ℤ) ^ (s.filter (fun b => b < a)).card
```

これは有限逆転集合の数え上げと既存の係数の冪の法則に限り、作用やoperadの新しい法則ではない。

### 119.17 検証済みの区切りと3,000行の途中報告

次の15本、計 **902行**を対象ビルドと専用監査で検証した。
名前の接頭部は全て `SerrePositivity.EInfinity.SimplexCuts.`。
`BoundaryEndpointPartition`・`HorizontalBoundaryEquiv`・`BoundaryKindExchange`・
`VerticalBoundaryEquiv`・`BoundaryFaceTransfers`・`UniversalBoundaryPartner`・
`BoundaryPartnerFixedPoints`・`BoundaryFixedTerms`・`BoundaryPartnerValues`・
`BoundaryCancellationReduction`・`UniversalBoundaryValues`・`StraightTraceFaces`・
`IntervalCardinalities`・`ColorCaesuraCounts`・`ColorIntervalDegrees`。
次の登録候補一覧はこの15本。

専用監査 `/tmp/bsw16/audit-m14-universal-boundary.lean` は
**15モジュール・157宣言・標準三公理のみ**。
対象ビルドは `m14-boundary-fixed-terms-01.log`・`m14-boundary-counts-01.log`・
`m14-color-interval-degrees-02.log` などに成功を確認。新規15本にsorry・追加公理0、Leanの警告なし。
全てのビルド・監査で `--wait 3600` の整理券を一枚ずつ使い、終了時に返した。
mainへの取り込み・rootビルド・大きな監査は行っていない。

L09a・L09の累計 **3,255行**、改訂MayのM14全体 **8,321行**。
3,000行を越えた途中報告は停止せずチャットでも行った。次は4,000行で報告する。
個々の補題はいずれも200行以下であり、200行を超える補題の追加はない。

全境界の添字の対合候補と、実際の境界項の固定点での零は閉じた。
水平・垂直の指定列の内部の照合、出力次数と区間の重みの同一視も閉じた。
一方、三群の符号付き値の相殺 `hc`・`hv`・`hmix` は未完。
`universalBoundaryPartner_neg_of_cases` はそれらを明示的な前提に取る貼り合わせの補題であり、
最終のL09aやBFの作用の法則を閉じたとは扱わない。§119.16の有限符号計算へ続ける。

### 119.18 展開した色列のcaesuraと区間の重み（C100・C101）

m=0〜4、q=0〜4、色数1〜3の全ての語と切断で、展開した色列の後続の同色が
「同じ区間の後続頂点、または元の語の後続の同色」の条件と一致することを点検した。
各区間のそのような頂点数が `intervalLength` と一致することも点検してからLeanへ入る。
元の語の全射性・隣接非退化性はこの二式には不要。

```lean
caesura_label_iff {m q r : ℕ} (s : Cut m q) (v : Fin (m + 1) → Fin r)
    (i : Fin (m + 1)) (j : Fin (m + q + 1)) (hj : s.horizontal j = i) :
  Surjection.Caesura (label s v) j ↔
    j < (intervalPositions s i).max' (intervalPositions_nonempty s i) ∨ Surjection.Caesura v i
interval_active_card {m q r : ℕ} (s : Cut m q) (v : Fin (m + 1) → Fin r)
    (i : Fin (m + 1)) :
  ((intervalPositions s i).filter (Surjection.Caesura (label s v))).card = intervalLength s v i
```

`Surjection.Word` は全射性だけでなく隣接非退化性も含む。展開色列には垂直辺で隣接反復が
あるため、それをWordへ包んで既存のlastOccurrenceのAPIを流用することはしない。
同じ色の後続を持つ位置の有限集合として直接扱う。

### 119.19 展開色列の活動頂点の濃度（C102〜C105）

§119.18の全頂点の点検と、m=0〜4、q=0〜4の全切断・色数1〜3の全射語の各色で、
活動頂点数が出力次数に一致し、全活動頂点数が全出力次数になることを点検してから実装。
`activeVertexPositions` は展開色列のcaesuraを選ぶ同じ有限集合の記法。

```lean
activeVertexPositions {m q r : ℕ} (s : Cut m q) (v : Fin (m + 1) → Fin r) :
  Finset (Fin (m + q + 1))
active_fiber_card {m q r : ℕ} (s : Cut m q) (v : Fin (m + 1) → Fin r)
    (i : Fin (m + 1)) :
  ((activeVertexPositions s v).filter (fun j => s.horizontal j = i)).card = intervalLength s v i
active_color_card_eq_sum {m q r : ℕ} (s : Cut m q) (v : Fin (m + 1) → Fin r)
    (c : Fin r) :
  ((activeVertexPositions s v).filter (fun j => label s v j = c)).card =
    ∑ i ∈ Surjection.occurrences v c, intervalLength s v i
active_color_card {m q r : ℕ} (s : Cut m q) (v : Surjection.Word r (m + 1)) (c : Fin r) :
  ((activeVertexPositions s v.val).filter (fun j => label s v.val j = c)).card = outputDegree s v c
activeVertexPositions_card {m q r : ℕ} (s : Cut m q) (v : Surjection.Word r (m + 1)) :
  (activeVertexPositions s v.val).card = m + q + 1 - r
```

### 119.20 単調なfiberでまとめた逆転数（C106・C107）

位置数・中間の位置数1〜4、色数1〜3の全ての弱単調写像・色付け・位置部分集合で、
逆転数がfiberの濃度の積による重み付き逆転数になることを点検してからLeanへ入る。
途中の写像の全射性や色付けの非退化性は要求しない。

```lean
inversion_condition_comp_monotone {N M r : ℕ} (f : Fin N →o Fin M)
    (v : Fin M → Fin r) (x y : Fin N) :
  (x < y ∧ v (f y) < v (f x)) ↔ (f x < f y ∧ v (f y) < v (f x))
positionInversionTerm_comp_monotone {N M r : ℕ} (f : Fin N →o Fin M)
    (v : Fin M → Fin r) (x y : Fin N) :
  positionInversionTerm (v ∘ f) x y = if f x < f y ∧ v (f y) < v (f x) then 1 else 0
positionInversionCount_comp_monotone {N M r : ℕ} (f : Fin N →o Fin M)
    (v : Fin M → Fin r) (s : Finset (Fin N)) :
  positionInversionCount (v ∘ f) s =
    ∑ i : Fin M, ∑ j : Fin M, if i < j ∧ v j < v i then
      (s.filter (fun x => f x = i)).card * (s.filter (fun y => f y = j)).card else 0
permutationExponent_eq_active_inversions {m q r : ℕ} (s : Cut m q)
    (v : Fin (m + 1) → Fin r) :
  permutationExponent s v = positionInversionCount (label s v) (activeVertexPositions s v)
```

有限和のfiber分割の法則を二回使い、C102の活動頂点の濃度で `intervalLength` に戻す。

### 119.21 実際の出力境界符号を活動頂点で読む型（C108〜C111）

m=0〜4、q=0〜3、色数1〜3の全射・隣接非退化の語と全経路の各頂点で、
先行同色数と小さい色の出力次数が活動頂点の数に一致することを点検。
活動頂点を削除するとき、元のBF境界指数と次のC111の指数の偶奇が一致することを
点検してからLeanへ入る。C110・C111は既存の `outputBoundarySign` を同じ添字で評価する法則。

```lean
vertexRank_eq_active_card {m q r : ℕ} (s : Cut m q) (v : Fin (m + 1) → Fin r)
    (k : Fin (m + q + 1)) :
  vertexRank s v (label s v k) k =
    ((activeVertexPositions s v).filter (fun j => j < k ∧ label s v j = label s v k)).card
prefixOutputDegree_eq_active_card {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (c : Fin r) :
  (∑ b ∈ Finset.univ.filter (fun b : Fin r => b < c), outputDegree s v b) =
    ((activeVertexPositions s v.val).filter (fun j => label s v.val j < c)).card
outputBoundarySignAt {m q r : ℕ} (s : Cut m q) (v : Surjection.Word r (m + 1))
    (k : Fin (m + q + 1)) : ℤ
outputBoundarySignAt_active {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (k : Fin (m + q + 1)) :
  outputBoundarySignAt s v k = cutSign s v.val * (-1 : ℤ) ^
    (((activeVertexPositions s v.val).filter (fun j => label s v.val j < label s v.val k)).card +
    ((activeVertexPositions s v.val).filter (fun j => j < k ∧ label s v.val j = label s v.val k)).card)
outputBoundarySignAt_of_active {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (k : Fin (m + q + 1))
    (hk : k ∈ activeVertexPositions s v.val) :
  outputBoundarySignAt s v k = (-1 : ℤ) ^ positionExponent s v.val *
    (-1 : ℤ) ^ positionInversionCount (label s v.val) ((activeVertexPositions s v.val).erase k) *
    (-1 : ℤ) ^ ((activeVertexPositions s v.val).filter (fun j => j < k)).card
```

### 119.22 活動頂点の境界符号までの検証済み区切り

次の五本、計 **379行**を検証した。
`ColorSortingBoundarySigns` 57行、`ExpandedCaesuras` 76行、`ActiveVertexCounts` 78行、
`WeightedVertexInversions` 82行、`ActiveBoundarySigns` 86行。
接頭部は全て `SerrePositivity.EInfinity.SimplexCuts.`。次の登録候補一覧はこの五本。

対象ビルド `lake build SerrePositivity.EInfinity.SimplexCuts.ActiveBoundarySigns` 成功
（`/tmp/bsw16/m14-active-boundary-signs-01.log`）。
専用監査 `/tmp/bsw16/audit-m14-active-boundary-signs.lean` は
**5モジュール・52宣言・標準三公理のみ**。新規五本にsorry・追加公理0、Leanの警告なし。
鍵の待ちは一枚の整理券にまとめ、監査が終わって鍵を返した。

事前点検は、色順の境界符号25,710個の指定色付き部分集合、展開caesura347,822頂点、
活動頂点の濃度26,881個の切断と色付け、単調なfiberの重み付き逆転数89,836例、
実際のBF出力符号14,096活動頂点で一致した。
Leanでは、既存の逆転数の削除公式、有限和のfiber分割、同じ面番号の先行同色数を使った。
個々の補題は全て200行以下。既存の公開宣言・界面・BE作用・operadの法則は変更していない。

L09a・L09の累計 **3,634行**、改訂MayのM14全体 **8,700行**。
この再開後は20本・1,281行を検証済みとして保存した。
3,000行の途中報告は済み、次は4,000行で停止せず報告する。
半分の12,500行・外枠25,000行には未到達。

ここまでで全添字の対合、固定点の実際の零、水平・垂直の有限同値、内部の指定面の列、
活動頂点における実際の出力境界符号の共通化が閉じた。
L09a全体の `hc`・`hv`・`hmix` の符号付き値の相殺はまだ未証明。
次は、最後の非活動頂点の符号を直前同色の活動頂点へ運ぶ法則と、対応する残りの逆転集合の照合。
その準備として、位置数1〜6・色数1〜3の全ての色列で、直前同色位置を持つ3,534位置の
先行同色数が一だけ違い、その交代符号が反対になることを有限点検した。
この準備の点検だけを、未実装の照合や最終相殺の証明として扱わない。
mainの凍結を維持し、root・全体監査やM15・G12の作業は行っていない。

## 120. 次の約4,600行で残りの見込みを再評価する（11-14）

調整役の最新指示に従い、L09a・L09が約4,600行になった報告で、
L09a・L09の残りとM14全体の完成の見込みを、外枠25,000行と照合して出し直す。
その見積もりのために停止せず、現在の符号の三群を閉じる作業を続ける。

### 120.1 直前の同色の頂点（C112〜C115）

`/tmp/bsw16/check-previous-vertices.py` で位置数1〜6・色数1〜3の全色列のうち、
直前同色を持つ3,534位置の集合の削除・先行数の差一・直前位置の活動性を確認した。
前後に同色を持たない1,006位置ではその色のfiberが一頂点であることも確認。
以下は既存の `Surjection.previousOccurrences` の最大とその性質の評価。

```lean
previousVertex {N r : ℕ} (v : Fin N → Fin r) (k : Fin N)
    (h : (Surjection.previousOccurrences v k).Nonempty) : Fin N
previousVertex_mem {N r : ℕ} (v : Fin N → Fin r) (k : Fin N)
    (h : (Surjection.previousOccurrences v k).Nonempty) :
  previousVertex v k h ∈ Surjection.previousOccurrences v k
previousVertex_lt {N r : ℕ} (v : Fin N → Fin r) (k : Fin N)
    (h : (Surjection.previousOccurrences v k).Nonempty) : previousVertex v k h < k
previousVertex_value {N r : ℕ} (v : Fin N → Fin r) (k : Fin N)
    (h : (Surjection.previousOccurrences v k).Nonempty) : v (previousVertex v k h) = v k
previousOccurrences_erase_previousVertex {N r : ℕ} (v : Fin N → Fin r) (k : Fin N)
    (h : (Surjection.previousOccurrences v k).Nonempty) :
  (Surjection.previousOccurrences v k).erase (previousVertex v k h) =
    Surjection.previousOccurrences v (previousVertex v k h)
previousOccurrences_card_previousVertex {N r : ℕ} (v : Fin N → Fin r) (k : Fin N)
    (h : (Surjection.previousOccurrences v k).Nonempty) :
  (Surjection.previousOccurrences v (previousVertex v k h)).card + 1 =
    (Surjection.previousOccurrences v k).card
previousVertex_active {m q r : ℕ} (s : Cut m q) (v : Fin (m + 1) → Fin r)
    (k : Fin (m + q + 1)) (h : (Surjection.previousOccurrences (label s v) k).Nonempty) :
  previousVertex (label s v) k h ∈ activeVertexPositions s v
vertexRank_eq_previousOccurrences_card {m q r : ℕ} (s : Cut m q)
    (v : Fin (m + 1) → Fin r) (k : Fin (m + q + 1)) :
  vertexRank s v (label s v k) k = (Surjection.previousOccurrences (label s v) k).card
vertexRank_previousVertex {m q r : ℕ} (s : Cut m q) (v : Fin (m + 1) → Fin r)
    (k : Fin (m + q + 1)) (h : (Surjection.previousOccurrences (label s v) k).Nonempty) :
  vertexRank s v (label s v k) k =
    vertexRank s v (label s v (previousVertex (label s v) k h))
      (previousVertex (label s v) k h) + 1
```

### 120.2 直前同色の面への符号の移送（C116・C117）

元の語が全射・隣接非退化の場合、m=0〜4、q=0〜3、色数1〜3の全経路の
直前同色を持つ位置で、実際のBF境界指数が一つ違って交代符号が反対になることを
点検してから実装。`outputBoundarySignAt` の既存の係数の冪の法則とC115で証明する。

```lean
outputBoundarySignAt_rank {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (k : Fin (m + q + 1)) :
  outputBoundarySignAt s v k = cutSign s v.val * (-1 : ℤ) ^
    ((∑ c ∈ Finset.univ.filter (fun c : Fin r => c < label s v.val k), outputDegree s v c) +
    vertexRank s v.val (label s v.val k) k)
outputBoundarySignAt_previous {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (k : Fin (m + q + 1))
    (h : (Surjection.previousOccurrences (label s v.val) k).Nonempty) :
  outputBoundarySignAt s v k = -outputBoundarySignAt s v (previousVertex (label s v.val) k h)
outputBoundarySignAt_via_previous {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (k : Fin (m + q + 1))
    (h : (Surjection.previousOccurrences (label s v.val) k).Nonempty) :
  outputBoundarySignAt s v k = -
    ((-1 : ℤ) ^ positionExponent s v.val *
      (-1 : ℤ) ^ positionInversionCount (label s v.val)
        ((activeVertexPositions s v.val).erase (previousVertex (label s v.val) k h)) *
      (-1 : ℤ) ^ ((activeVertexPositions s v.val).filter
        (fun j => j < previousVertex (label s v.val) k h)).card)
```

C117は、k自身が非活動でも直前の同色位置が活動的であるC114と、検証済みのC111の合成。

### 120.3 直前同色を持たない非活動頂点（C118〜C120）

§120.1の1,006個の単独色の位置の点検を使う。前後に同色を持たないなら色のfiberは一頂点、
したがって正の出力次数を持つ非活動頂点には直前同色が必ず存在する。

```lean
colorPositions_singleton_of_inactive_no_previous {m q r : ℕ} (s : Cut m q)
    (v : Fin (m + 1) → Fin r) (k : Fin (m + q + 1))
    (hk : k ∉ activeVertexPositions s v)
    (hp : ¬(Surjection.previousOccurrences (label s v) k).Nonempty) :
  colorPositions s v (label s v k) = {k}
outputDegree_zero_of_inactive_no_previous {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (k : Fin (m + q + 1))
    (hk : k ∉ activeVertexPositions s v.val)
    (hp : ¬(Surjection.previousOccurrences (label s v.val) k).Nonempty) :
  outputDegree s v (label s v.val k) = 0
previousOccurrences_nonempty_of_inactive_degree_pos {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (k : Fin (m + q + 1))
    (hk : k ∉ activeVertexPositions s v.val) (hd : 0 < outputDegree s v (label s v.val k)) :
  (Surjection.previousOccurrences (label s v.val) k).Nonempty
```

### 120.4 既存の一般の単語削除のcaesura公式の再利用（C121〜C124）

位置数1〜6・色数1〜3の全色列・全削除位置で、活動頂点の削除ではその位置だけを、
最後の非活動頂点の削除では直前同色の活動性だけを失うことを点検した。
既存の `IntervalCuts.GeneralDeletionCaesuras.caesura_erase_of_caesura` と
`caesura_erase_final` を使い、同じ集合を像で移す。逆転数の移送は既存の
`positionInversionCount_image` の法則である。

```lean
caesuraPositions {N r : ℕ} (v : Fin N → Fin r) : Finset (Fin N)
caesuraPositions_erase_active_image {N r : ℕ} (v : Fin (N + 1) → Fin r)
    (k : Fin (N + 1)) (hk : Surjection.Caesura v k) :
  (caesuraPositions (Surjection.erase v k)).image k.succAbove = (caesuraPositions v).erase k
caesuraPositions_erase_final_image {N r : ℕ} (v : Fin (N + 1) → Fin r)
    (k : Fin (N + 1)) (hk : ¬ Surjection.Caesura v k)
    (hp : (Surjection.previousOccurrences v k).Nonempty) :
  (caesuraPositions (Surjection.erase v k)).image k.succAbove =
    (caesuraPositions v).erase (previousVertex v k hp)
inversionCount_erase_active {N r : ℕ} (v : Fin (N + 1) → Fin r)
    (k : Fin (N + 1)) (hk : Surjection.Caesura v k) :
  positionInversionCount (Surjection.erase v k) (caesuraPositions (Surjection.erase v k)) =
    positionInversionCount v ((caesuraPositions v).erase k)
inversionCount_erase_final {N r : ℕ} (v : Fin (N + 1) → Fin r)
    (k : Fin (N + 1)) (hk : ¬ Surjection.Caesura v k)
    (hp : (Surjection.previousOccurrences v k).Nonempty) :
  positionInversionCount (Surjection.erase v k) (caesuraPositions (Surjection.erase v k)) =
    positionInversionCount v ((caesuraPositions v).erase (previousVertex v k hp))
```

活動集合の移送を新しく仮定せず、既存の任意の色列での削除公式を使う証明分割。

### 120.5 同じ削除色列へ移した実際のBF境界符号（C125〜C127）

m=0〜4、q=0〜3、色数1〜3の全射・隣接非退化の語の全経路の正出力次数の面で、
実際の境界符号が「位置符号・削除色列の逆転符号・展開色列の単語削除係数」の積に
一致することを点検してから実装。既存の `Surjection.deletionCoefficient` の二分岐と、
C111・C117・C123・C124をそのまま同じ削除色列で貼り合わせる。

```lean
erasedColorSign {N r : ℕ} (v : Fin (N + 1) → Fin r) (k : Fin (N + 1)) : ℤ
caesuraRank_label_eq_active_rank {m q r : ℕ} (s : Cut m q)
    (v : Fin (m + 1) → Fin r) (k : Fin (m + q + 1)) :
  Surjection.caesuraRank (label s v) k =
    ((activeVertexPositions s v).filter (fun j => j < k)).card
outputBoundarySignAt_erase_active {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (k : Fin (m + q + 1))
    (hk : Surjection.Caesura (label s v.val) k) :
  outputBoundarySignAt s v k = (-1 : ℤ) ^ positionExponent s v.val *
    erasedColorSign (label s v.val) k * Surjection.deletionCoefficient (label s v.val) k
outputBoundarySignAt_erase_final {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (k : Fin (m + q + 1))
    (hk : ¬ Surjection.Caesura (label s v.val) k)
    (hp : (Surjection.previousOccurrences (label s v.val) k).Nonempty) :
  outputBoundarySignAt s v k = (-1 : ℤ) ^ positionExponent s v.val *
    erasedColorSign (label s v.val) k * Surjection.deletionCoefficient (label s v.val) k
outputBoundarySignAt_erase {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (k : Fin (m + q + 1))
    (hd : 0 < outputDegree s v (label s v.val k)) :
  outputBoundarySignAt s v k = (-1 : ℤ) ^ positionExponent s v.val *
    erasedColorSign (label s v.val) k * Surjection.deletionCoefficient (label s v.val) k
```

零次数では `outputBoundarySignAt` 自体は±1でも、既存の実際の境界項は零である。
その場合まで誤って符号そのものを削除係数0と同一視する型にはしない。

### 120.6 混合角の座標と区間端点の評価（C128〜C132）

m=0〜5、q=0〜4の全経路の水平辺・垂直辺・水平から垂直への混合角で、
水平辺直前の区間の最後、垂直辺の前後の同色、角交換の一頂点の座標を点検してから実装。
既存の `step_of_mem`・`step_of_notMem`・`horizontal_swapSteps`・`vertical_swapSteps` を合成する。

```lean
interval_max_before_horizontal {m q : ℕ} (s : Cut m q) (a : Fin (m + q))
    (ha : a ∈ s.val) :
  (intervalPositions s (s.horizontal a.castSucc)).max'
    (intervalPositions_nonempty s (s.horizontal a.castSucc)) = a.castSucc
before_horizontal_active_iff {m q r : ℕ} (s : Cut m q) (v : Fin (m + 1) → Fin r)
    (a : Fin (m + q)) (ha : a ∈ s.val) :
  a.castSucc ∈ activeVertexPositions s v ↔ Surjection.Caesura v (s.horizontal a.castSucc)
before_vertical_active {m q r : ℕ} (s : Cut m q) (v : Fin (m + 1) → Fin r)
    (a : Fin (m + q)) (ha : a ∉ s.val) : a.castSucc ∈ activeVertexPositions s v
previousVertex_after_vertical {m q r : ℕ} (s : Cut m q) (v : Fin (m + 1) → Fin r)
    (a : Fin (m + q)) (ha : a ∉ s.val)
    (hp : (Surjection.previousOccurrences (label s v) a.succ).Nonempty) :
  previousVertex (label s v) a.succ hp = a.castSucc
swapSteps_hv_coordinates {m q : ℕ} (s : Cut m q) (a b : Fin (m + q))
    (hab : b.val = a.val + 1) (ha : a ∈ s.val) (hb : b ∉ s.val) :
  (s.swapSteps a b).horizontal b.castSucc = s.horizontal a.castSucc ∧
    ((s.swapSteps a b).vertical b.castSucc).val = (s.vertical b.castSucc).val + 1
```

### 120.7 削除後の同じ番号の順位と隣接順位（C133〜C135）

位置数1〜6、色数1〜3の全色列について、活動頂点を削除した同じ番号の順位と
隣接二位置の順位の差を点検してから実装する。
C133は既存の `caesura_erase_of_caesura` と同値な接頭集合の濃度、
C135は既存の `prefix_count_succ` の同じcaesura集合での評価。

```lean
caesuraRank_erase_active_at {N r : ℕ} (v : Fin (N + 1) → Fin r)
    (a : Fin (N + 1)) (ha : Surjection.Caesura v a) (t : Fin N) (ht : t.val = a.val) :
  Surjection.caesuraRank (Surjection.erase v a) t = Surjection.caesuraRank v a
deletionCoefficient_erase_active_rank {N r : ℕ} (v : Fin (N + 1) → Fin r)
    (a : Fin (N + 1)) (ha : Surjection.Caesura v a) (t : Fin N) (ht : t.val = a.val) :
  Surjection.deletionCoefficient v a = (-1 : ℤ) ^ Surjection.caesuraRank (Surjection.erase v a) t
caesuraRank_eq_filter_card {N r : ℕ} (v : Fin N → Fin r) (k : Fin N) :
  Surjection.caesuraRank v k = ((caesuraPositions v).filter (fun j => j < k)).card
caesuraRank_adjacent {N r : ℕ} (v : Fin N → Fin r) (a b : Fin N)
    (hab : b.val = a.val + 1) :
  Surjection.caesuraRank v b =
    Surjection.caesuraRank v a + if Surjection.Caesura v a then 1 else 0
```

### 120.8 混合角による右端と位置指数の増分（C136〜C139）

m=1〜4、q=1〜3の全経路の水平・垂直の角で、右端が直前の区間だけ一つ進むこと、
色数1〜3の全ての語で位置指数がその区間のcaesuraだけ一つ増えることを点検してから実装。
右端の評価C128と、最大位置の非一致、既存の有限和の一位置更新の法則を使う。

```lean
interval_max_ne_before_vertical {m q : ℕ} (s : Cut m q) (b : Fin (m + q))
    (hb : b ∉ s.val) (i : Fin (m + 1)) :
  (intervalPositions s i).max' (intervalPositions_nonempty s i) ≠ b.castSucc
hi_swapSteps_hv_of_ne {m q : ℕ} (s : Cut m q) (a b : Fin (m + q))
    (hab : b.val = a.val + 1) (ha : a ∈ s.val) (hb : b ∉ s.val)
    (i : Fin (m + 1)) (hi : i ≠ s.horizontal a.castSucc) :
  SimplexCuts.hi (s.swapSteps a b) i = SimplexCuts.hi s i
hi_swapSteps_hv_at {m q : ℕ} (s : Cut m q) (a b : Fin (m + q))
    (hab : b.val = a.val + 1) (ha : a ∈ s.val) (hb : b ∉ s.val) :
  hi (s.swapSteps a b) (s.horizontal a.castSucc) = hi s (s.horizontal a.castSucc) + 1
positionExponent_swapSteps_hv {m q r : ℕ} (s : Cut m q)
    (v : Fin (m + 1) → Fin r) (a b : Fin (m + q))
    (hab : b.val = a.val + 1) (ha : a ∈ s.val) (hb : b ∉ s.val) :
  positionExponent (s.swapSteps a b) v = positionExponent s v +
    if Surjection.Caesura v (s.horizontal a.castSucc) then 1 else 0
```

### 120.9 同じ削除色列と隣接同色の係数（C140〜C143）

位置数2〜6、色数1〜3の全色列で、隣接同色のどちらを削除しても同じ色列になり、
削除係数は反対になることを点検してから実装する。
C142・C143は、既存の混合角の中間以外の座標保存と§117の削除列の点検を同じ色列で評価した法則。

```lean
erase_adjacent_equal {N r : ℕ} (v : Fin (N + 1) → Fin r) (a b : Fin (N + 1))
    (hab : b.val = a.val + 1) (hv : v a = v b) : Surjection.erase v a = Surjection.erase v b
deletionCoefficient_adjacent_equal {N r : ℕ} (v : Fin N → Fin r) (a b : Fin N)
    (hab : b.val = a.val + 1) (hv : v a = v b) :
  Surjection.deletionCoefficient v b = -Surjection.deletionCoefficient v a
erase_label_swapSteps {m q r : ℕ} (s : Cut m q) (v : Fin (m + 1) → Fin r)
    (a b : Fin (m + q)) (hab : b.val = a.val + 1) :
  Surjection.erase (label (s.swapSteps a b) v) b.castSucc = Surjection.erase (label s v) b.castSucc
erasedColorSign_swapSteps {m q r : ℕ} (s : Cut m q) (v : Fin (m + 1) → Fin r)
    (a b : Fin (m + q)) (hab : b.val = a.val + 1) :
  erasedColorSign (label (s.swapSteps a b) v) b.castSucc = erasedColorSign (label s v) b.castSucc
```

### 120.10 混合角の削除係数と位置指数を合わせた符号（C144）

m=1〜4、q=1〜3、色数1〜3の全語で28,398例を点検した。
C134・C135・C139〜C142を、同じ削除色列の二つの隣接順位で評価する法則。
新しい作用やホモトピーは作らない。

```lean
signedDeletionCoefficient_swapSteps_hv {m q r : ℕ} (s : Cut m q)
    (v : Fin (m + 1) → Fin r) (a b : Fin (m + q))
    (hab : b.val = a.val + 1) (ha : a ∈ s.val) (hb : b ∉ s.val) :
  (-1 : ℤ) ^ positionExponent (s.swapSteps a b) v *
      Surjection.deletionCoefficient (label (s.swapSteps a b) v) b.castSucc =
    -((-1 : ℤ) ^ positionExponent s v *
      Surjection.deletionCoefficient (label s v) b.castSucc)
```

§31の追記を受領。約4,600行の区切りにはL10〜L28の各行について、
`convolutionAlgebra`、`restrictCoalgebra`、χ・TRの既存の法則で再利用できる部分と、
一般単体の切断でなお証明する部分を分け、M14全体の残りを数え直す。

### 120.11 実際の出力境界符号への適用（C145〜C148）

既存の活動頂点の色ごとの濃度と直前同色位置から、両側の出力次数が正であることを確認する。
C147は共通の削除色列の逆転符号をくくってC144を適用し、C148は同じ角交換の自己逆性を使う。
数値符号の有限点検は§120.10に含む。実テンソルの一致はまだ主張しない。

```lean
outputDegree_pos_of_active {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (k : Fin (m + q + 1))
    (hk : k ∈ activeVertexPositions s v.val) : 0 < outputDegree s v (label s v.val k)
outputDegree_pos_of_previous {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (k : Fin (m + q + 1))
    (hp : (Surjection.previousOccurrences (label s v.val) k).Nonempty) :
  0 < outputDegree s v (label s v.val k)
outputBoundarySignAt_swapSteps_hv {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (a b : Fin (m + q))
    (hab : b.val = a.val + 1) (ha : a ∈ s.val) (hb : b ∉ s.val) :
  outputBoundarySignAt (s.swapSteps a b) v b.castSucc = -outputBoundarySignAt s v b.castSucc
outputBoundarySignAt_swapSteps_vh {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (a b : Fin (m + q))
    (hab : b.val = a.val + 1) (ha : a ∉ s.val) (hb : b ∈ s.val) :
  outputBoundarySignAt (s.swapSteps a b) v b.castSucc = -outputBoundarySignAt s v b.castSucc
```

### 120.12 同じ削除列による実テンソルの更新次数（C149〜C152）

既存のC27のリストの一致の長さを取り、各色の出力次数を更新した族まで一致させる。
これはテンソルの依存した型を合わせるための既存構成の評価で、新しい次数模型は導入しない。
リストの削除と角交換の有限点検は§117と§120.10のものを引き継ぐ。

```lean
verticesList_length {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (c : Fin r) :
  (verticesList s v.val c).length = outputDegree s v c + 1
deletedVerticesList_length {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (k : Fin (m + q + 1)) (c : Fin r) :
  (deletedVerticesList s v.val k c).length =
    outputDegree s v c + 1 - if label s v.val k = c then 1 else 0
deletedVerticesList_length_update {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (k : Fin (m + q + 1))
    (hk : 0 < outputDegree s v (label s v.val k)) (c : Fin r) :
  (deletedVerticesList s v.val k c).length =
    Function.update (outputDegree s v) (label s v.val k)
      (outputDegree s v (label s v.val k) - 1) c + 1
deletedOutputDegree_swapSteps {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (a b : Fin (m + q))
    (hab : b.val = a.val + 1)
    (ho : 0 < outputDegree s v (label s v.val b.castSucc))
    (hn : 0 < outputDegree (s.swapSteps a b) v (label (s.swapSteps a b) v.val b.castSucc)) :
  Function.update (outputDegree (s.swapSteps a b) v)
      (label (s.swapSteps a b) v.val b.castSucc)
      (outputDegree (s.swapSteps a b) v (label (s.swapSteps a b) v.val b.castSucc) - 1) =
    Function.update (outputDegree s v) (label s v.val b.castSucc)
      (outputDegree s v (label s v.val b.castSucc) - 1)
```

### 120.13 実際の標準面を削除列で読む（既存C40・C154）

既存C40の`simplexVertexList_boundaryFace`とC36を再利用し、C26の指定削除列と同定する。
個別ビルド後の合同監査でC153が既存C40と重複していることが分かり、
重複宣言を除いて`BoundaryVertexLists`のimportへ置き換えた。
式は単体圏の実際の射の頂点列であり、ホモトピー圏へ弱めない。

```lean
simplexVertexList_deletedFace {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (k : Fin (m + q + 1))
    (hd : 0 < outputDegree s v (label s v.val k))
    (j : Fin (outputDegree s v (label s v.val k) + 1))
    (hj : j.val = vertexRank s v.val (label s v.val k) k) :
  simplexVertexList (boundaryFace _ hd j ≫ face s v (label s v.val k)) =
    deletedVerticesList s v.val k (label s v.val k)
```

## 121. 約4,600行の区切り：L09a・L09とM14全体の再見積もり（11-14、§31）

### 121.1 実測と完成範囲

一覧：済み 8／全体 48（うち追加 4）

基準はL01〜L44にL09a・L12a・L43a・L43bを加えた48項目。
済みはL01〜L08。C/R等の既存構成の法則・証明の分割とI01の既存作用の照合は、
共通規則に従い数学の新しい項目として数えない。

§119.22の3,634行から、今回の14モジュール934行を加え、
**L09a・L09の実測4,568行、改訂MayのM14全体9,634行**。
Leanファイルの空行・docstring込みで数え、報告書・監査用ファイルは含めない。
§110の旧coherent経路10,216行は保持するが、今回の改訂Mayの外枠へ重複計上しない。

今回、混合角の交換について、同じ削除色列・その逆転符号・位置指数の差・
単語削除係数を結び、**実際の出力境界符号が反対になることを両向きに証明した**。
削除した色別リストから、実テンソルの更新次数の族も一致した。
指定境界面を削除列で読むC154も検証した。
これらは元の圏・実際の整数係数の等式であり、ホモトピー圏へ弱めていない。

まだL09a全体・L09は閉じていない。とくに、混合角の**実テンソル値**の一致を、
今回の更新次数と指定面から接続するところは残る。
水平・垂直の有限添字の対合は構成済みだが、それぞれの符号と実際の値の照合は残る。

### 121.2 L09a・L09の残り

以下は既存の型一覧L09a・L09の証明の残りで、新しい数学の追加ではない。
実測4,568行からの**追加**を数える。

| 行 | 残りの内容・使える完成分 | 追加見込み |
| --- | --- | ---: |
| 混合角 | C27の削除列、C147・C148の実符号、C152の更新次数、C154の指定面から、依存した次数移送込みの`deletedCutTensor`を一致させる。逆向きと分類の包装も含む | 180〜300 |
| 水平境界と係数微分 | 水平の全添字同値・内点/両端の経路は既存。元の語の削除と展開語の削除の順位・位置指数の比較、無効な削除語と退化面の零、実テンソルの移送が残る | 600〜1,100 |
| 垂直境界と入力面 | 垂直の全添字同値・削除後の座標列は既存。入力面の交代符号と位置指数の差、端点、正規化生成元と実テンソルの移送が残る | 500〜950 |
| L09aの包装・L09 | 構成済みの対合・固定点零・三分岐の合成に実際の値の等式を渡す。有限和の相殺をテンソル微分・語の微分・入力面の和へ戻す | 200〜350 |
| **残り合計** | | **1,480〜2,700** |
| **L09a・L09完成時** | 現在の4,568を加算 | **6,048〜7,268** |

符号の一般的な正規形は今回までに得たので、三分岐ごとに重み付き逆転数を最初から
展開し直す見積もりにはしていない。ただし、実テンソルの依存した型と正規化の零の
処理は未完であり、リストの等式だけで完成と数えない。

### 121.3 L10〜L28：次元によらない既存部分の再利用の確認

ローカルの宣言の引数・結論を読んで、次の境界を確認した。

1. `Surjection.operad`（`Surjection/OperadStructure.lean`）はχの単位・置換・部分合成の
   全法則を持つ。`TableReduction.operadMap`と`operadMap_app`（`TableReduction/OperadMap.lean`）は
   全arityの**実際の**dg operad射と指定TR成分である。χ/TRのoperad則を再証明しない。
2. `Operad.restrictCoalgebraObj`・`restrictCoalgebraMap`・`restrictCoalgebra`
   （`Operad/CoalgebraRestriction.lean`）は任意の複体の余代数に使える。
   一般単体のχ余作用の法則が揃った後、TRによるBE余作用の公理はそのまま引き戻せる。
   ただし、χ自身がoperadであることだけから単体鎖のχ余代数構造は出ない。
3. `Operad.convolutionAlgebra`、`convolutionAction_comp`、`convolutionAction_equivariance`、
   `convolutionAction_unit`は非有界の一般複体・全arityで使える。
   `convolutionPre`・`convolutionPost`・`convolutionPreNat`、
   `convolutionAction_pre`・`convolutionAction_post`も同様。
   正規化コチェインのBE**代数**の公理を切断公式からもう一周証明する必要はない。
   一方、入力となる単体鎖のBE**余代数**と、指定された正規化評価の同定は先に要る。
4. `IntervalCuts.coactionComposition_apply`は`P Q K W X : Complex A`を任意に取り、
   二係数を交換するKoszul符号をそのまま再利用できる。
   `compositeWord_at_non_slot`・`compositeOuterPosition_value`・
   `compositeBasisWord_outerPosition`も単語・OverlapPartitionだけの主張である。
   `GeneralDeletionCaesuras`の削除則、一般の位置逆転数の埋込みの法則は既にL09aで使用している。
5. `IntervalCuts.cochainAction`は`interval A`、
   `cochainAction_comp`・`cochainAction_operad_comp`も`interval A`に固定される。
   `NestedEdgeCut.compositionCoefficient`は`edgeSign`と辺の二段切断、
   `VertexCompositionSigns`は頂点/辺の有限出力族に固定される。
   これらを一般qの定理として直接適用することはできない。
   一般単体のL12aで必要な二段切断の全対応・一般の位置指数の貼り合わせは残る。
   `CutSigns.edgeIntervalLength`もpivot一つの区間用で、一般qの`intervalLength`と同一視しない。

したがって短縮できるのは「χ/TR・convolutionの公理」「任意の複体の係数交換」
「単語代入の接頭部分の評価」であり、一般qの作用則を区間の完成定理だけから出す経路は採らない。
IntervalCutsとの一致I01は指定された同じ作用の照合として残す（下のL28に計上）。

### 121.4 L10〜L28の行ごとの残りの新規見込み

既存宣言は直さず、一般単体に適用する証明・包装・指定比較の行数だけを数える。
L12aの有限対応はL12に重複計上しない。すべて未完成で、以下の数字は実測ではない。

| 行 | 再利用する部分と、新規に残る部分 | 新規見込み |
| --- | --- | ---: |
| L10 | L09と基底/正規化生成元の展開から全整数Leibnizへ。`cochainActionComponent_d`と同じ`TensorProduct.ext`・`tensorLift`の方法。区間のLeibniz定理そのものは流用しない | 130〜230 |
| L11 | 既存の`permutationAction`・Koszulテンソルの置換評価と色別リストを使う。一般qの切断符号の置換と実テンソルの一致は新規 | 250〜450 |
| L12a | 既存OverlapPartition・単語代入の位置/値・`coactionComposition_apply`を使用。一般qの二段切断と一段切断の有限対応、位置符号、退化項零、全色の実テンソルの比較は新規 | 1,400〜2,400 |
| L12 | L12aの同じ添字上の有限和の相殺を`compositeCutSum = nestedCutSum`へ。χの合成係数を再構成しない | 120〜200 |
| L13 | unaryの切断の一意性と同じ生成元。既存`oneIso`を使う | 70〜130 |
| L14 | nullary係数とaugmentationを束ね、L12aの空入力分岐から実余作用へ。区間のnullary完成定理の直接適用はしない | 200〜380 |
| L15 | 既存の生成元自然性L05と線形/テンソル外延性で実複体射の自然性に延長 | 100〜180 |
| L16 | L12の有限和を`tensorCoInsertionAction`の実複体射へ。一般の結合子/交換の評価は既存を使用 | 120〜220 |
| L17 | L11・L13を複体射の等変性/単位へ線形延長。χの対称列を使う | 100〜180 |
| L18 | `restrictCoalgebraObj`・`restrictCoalgebraMap`・`TableReduction.operadMap`でBEへ制限。指定作用の式と射の可換性を包装 | 70〜130 |
| L19 | cosimplicial恒等式の交代和の相殺で正規化部分を保つ。新たなBE法則は不要 | 120〜220 |
| L20 | 同じ包含・微分・写像の制限。既存の交代余面複体の法則を使用 | 100〜180 |
| L21 | Mathlib Dold–Kanの正規化/退化分解・ホモトピーを反対圏で使用。同じ正規化包含が指定homになる接続は新規 | 250〜450 |
| L22 | `convolutionPre`・`convolutionPost`と各自然性、`Algebra.algebraLimitCone`・`algebraLimitIsLimit`で等化子を代数にする。恒等/合成を底のHomで確認 | 140〜260 |
| L23 | convolution等化子の元の恒等単体での評価と逆構成、非単射で零、全単体射の自然性。一般convolutionからは出ない | 450〜850 |
| L24 | 同じ評価の次数係数を保持した微分比較。一般Homの微分は既存だが評価符号の計算は新規 | 180〜340 |
| L25 | L23の評価と既存のpost/pre自然性で全X射に対する自然性を確認 | 80〜160 |
| L26 | L23〜L25を関手同型へ包装し、L20・L21の指定包含/擬同型を接続 | 120〜220 |
| L27 | `convolutionAction_uncurry`・評価自然性と代数の極限射影から指定射影の評価式を得る。BE代数の公理は再証明しない | 80〜160 |
| L28 | L27を実際のTR成分・単体鎖の切断公式で評価し、L26の指定同型で運ぶ。全整数次数とI01の区間との一致を含む | 250〜450 |
| **L10〜L28（L12a込み）合計** | | **4,330〜7,790** |

L21・L23・L24には「既存の同値を選べば終わる」という省略を置かない。
同じ包含・同じ評価・同じ次数係数との照合をこの見込みに含めた。
L12aの上端は区間の有限対応を一般qへ拡張する部分で、実測による不確実性が最も大きい。
一般のoperad則を再利用しても、単体鎖のχ余作用の合成則のこの入力は消えない。

### 121.5 M14全体の完成の見込みと25,000行の外枠

§110の完成見込みをそのまま据え置かず、現在の実測と各未完成行から積み直す。
G10や③-bの橋そのものを作る行数は含めないが、**受け取った指定比較への適用**は含める。

| 部分 | 現時点の実測 / 残りの新規 |
| --- | ---: |
| 完成済みMayと今回までの切断の実装 | **9,634（実測）** |
| L09a・L09の残り | 1,480〜2,700 |
| L10〜L28（L12a・I01込み） | 4,330〜7,790 |
| L29〜L37：同じMay係数・ν・top operationとFrobeniusの照合 | 1,200〜2,000 |
| L38〜L40：G10後の指定native Totと同じFrobenius辺への移送 | 500〜900 |
| L41・L42：filtered塔とA4の利用側 | 300〜550 |
| L43a・L43b・L43・L44：二重模型の実現と同じMay演算の比較 | 1,500〜2,800 |
| **残りの新規合計** | **9,310〜16,740** |
| **M14完成時の見込み** | **18,944〜26,374** |

**上端は25,000行を1,374行上回る。外枠内に必ず閉じるとは報告できない。**
下端は共通符号の正規形・一般convolution・指定Dold–Kan比較の再利用が素直に通る場合、
上端は一般qの二段切断と正規化評価の接続に余裕を取った値である。
現在の実測の余地は15,366行で、残り上端16,740行より1,374行少ない。
これは外枠変更の承認を仮定した見込みではなく、§31の外枠判断のための数値である。

以前の§110の完成上端23,240行との差は3,134行。
L09aの有限添字だけでなく、実際の境界符号・出力次数・指定面までの接続に行数が要り、
一般BFの最初の行の見込みを上方修正したためである。
χ/TR/convolutionの既存の公理を再証明しない短縮を入れても、この増分は全ては吸収できない。

§31の「止まらずに」に従い、この1,000行区切り自体では停止しない。
外枠25,000行を引き上げず、新しい数学の追加もしないまま、型一覧内の混合角の
実テンソルの照合から続ける。今後の実測が残り上端に寄る場合は外枠到達前に明示する。
12,500行の半分報告も別に行う。M15・G12、G10の部品には入らない。

### 121.6 対象ビルド・合同監査と登録候補

今回の14本はすべて対象ビルド成功。合同監査は **14モジュール・104宣言・標準三公理のみ**。
監査ログは `/tmp/bsw16/audit-m14-corner-signs-02.log`。
新規14本のsorry・追加公理0、Leanの警告0、`git diff --check`成功。
合同監査で見つかった既存C40との重複は§120.13のとおり除去し、再監査を通した。
個々の補題は200行以下。共通入口・共通監査は変更していない。mainは凍結中のまま。

登録候補（接頭部 `SerrePositivity.EInfinity.SimplexCuts.`）：

- `AdjacentColorDeletions`（86行）
- `CaesuraVertexDeletion`（85行）
- `CornerBoundarySigns`（74行）
- `CornerDeletionSigns`（59行）
- `CornerEndpointCoordinates`（82行）
- `CornerIntervalMaxima`（52行）
- `CornerPositionExponent`（64行）
- `DeletedFaceVertexLists`（28行）
- `DeletedOutputDegrees`（65行）
- `ErasedBoundarySigns`（70行）
- `ErasedCaesuraRanks`（81行）
- `InactiveColorDegrees`（51行）
- `PreviousBoundarySigns`（49行）
- `PreviousVertexPositions`（88行）

## 122. 約4,600行の報告後：同じ指定面の厳密な移送（11-14、続行）

一覧：済み 8／全体 48（うち追加 4）

§121は **1fc84640c** に保存済み。停止せず、混合角の既存の型の照合を続ける。
`deletedCutFace`は既存`deletedCutTensor`内の色ごとの指定面を、更新次数を始域にして
書き出したもの。新しい作用・正規化・錐は構成しない。
C155・C156は既存の面の頂点列の評価、C157はC27・C152と頂点列の単射性による
元の単体圏の射の一致である。ホモトピー圏の一致で代用しない。

```lean
simplexVertexList_deletedCutFace {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (a : Fin r) (ha : 0 < outputDegree s v a)
    (j : Fin (outputDegree s v a + 1)) (c : Fin r) :
  simplexVertexList (deletedCutFace s v a ha j c) =
    if c = a then (verticesList s v.val a).eraseIdx j.val else verticesList s v.val c
simplexVertexList_deletedCutFace_at_vertex {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (k : Fin (m + q + 1))
    (hd : 0 < outputDegree s v (label s v.val k))
    (j : Fin (outputDegree s v (label s v.val k) + 1))
    (hj : j.val = vertexRank s v.val (label s v.val k) k) (c : Fin r) :
  simplexVertexList (deletedCutFace s v (label s v.val k) hd j c) =
    deletedVerticesList s v.val k c
deletedCutFace_swapSteps {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (a b : Fin (m + q)) (hab : b.val = a.val + 1)
    (ho : 0 < outputDegree s v (label s v.val b.castSucc))
    (hn : 0 < outputDegree (s.swapSteps a b) v (label (s.swapSteps a b) v.val b.castSucc))
    (jo : Fin (outputDegree s v (label s v.val b.castSucc) + 1))
    (jno : jo.val = vertexRank s v.val (label s v.val b.castSucc) b.castSucc)
    (jn : Fin (outputDegree (s.swapSteps a b) v (label (s.swapSteps a b) v.val b.castSucc) + 1))
    (jnn : jn.val = vertexRank (s.swapSteps a b) v.val
      (label (s.swapSteps a b) v.val b.castSucc) b.castSucc) (c : Fin r) :
  deletedCutFace (s.swapSteps a b) v (label (s.swapSteps a b) v.val b.castSucc) hn jn c =
    eqToHom (congrArg SimplexCategory.mk
      (congrFun (deletedOutputDegree_swapSteps s v a b hab ho hn) c)) ≫
      deletedCutFace s v (label s v.val b.castSucc) ho jo c
```

### 122.1 既存生成元と純粋テンソルの次数移送（C158・C159）

同じ等式で型を移す既存構成の法則。等式の帰納法だけで証明し、
新たな作用・ホモトピー・数学の定理は追加しない。

```lean
gen_cast_source (A : Type u) [CommRing A] (S : SSet.{0}) {n n' q : ℕ} (h : n = n')
    (f : (⦋n'⦌ : SimplexCategory) ⟶ ⦋q⦌) (x : S _⦋q⦌) :
  gen A S n (S.map (eqToHom (congrArg SimplexCategory.mk h) ≫ f).op x) =
    (eqToHom (congrArg (fun t : ℤ => (chains A S).X t)
      (congrArg (fun k : ℕ => -(k : ℤ)) h.symm))).hom
      (gen A S n' (S.map f.op x))
tensorValue_congr_degree (A : Type u) [CommRing A] (K : Complex A) (n : ℕ)
    (d e : Fin n → ℕ) (h : d = e)
    (v : ∀ i, K.X (-(d i : ℤ))) (w : ∀ i, K.X (-(e i : ℤ)))
    (hv : ∀ i, (eqToHom (congrArg (fun t : ℤ => K.X t)
      (congrArg (fun k : ℕ => -(k : ℤ)) (congrFun h i)))).hom (v i) = w i) :
  (eqToHom (congrArg (fun t : ℤ => (power K n).X t)
    (congrArg (fun k : ℕ => -(k : ℤ)) (congrArg (degreeSum n) h)))).hom
    (tensorValue K n d v) = tensorValue K n e w
```

### 122.2 指定面と次数移送の検証済み区切り

一覧：済み 8／全体 48（うち追加 4）

§121の報告後も続行して、次の二本 **131行**を追加した。

- `SerrePositivity.EInfinity.SimplexCuts.DeletedCutFaces`（85行）
- `SerrePositivity.EInfinity.SimplexCuts.GeneratorDegreeTransfers`（46行）

対象ビルドは `/tmp/bsw16/m14-deleted-cut-faces-03.log` と
`/tmp/bsw16/m14-deleted-cut-faces-02.log` の各対象で成功。
合同監査 `/tmp/bsw16/audit-m14-deleted-cut-faces.log` は
**2モジュール・10宣言・標準三公理のみ**。sorry・追加公理0、Leanの警告0。
いずれの補題も200行以下、共通入口・共通監査・既存の公開宣言は変更していない。
調整役への登録候補には、この二本も加える。

L09a・L09の実測 **4,699行**、改訂MayのM14全体 **9,765行**。
§121の残り見込みの「混合角」のうち、指定面の厳密な一致と一般の次数移送を進めた。
`deletedCutTensor`内部の各因子をこの指定面の生成元へ実際に書き換え、
全体の次数移送と符号を合わせる接続はまだ残る。L09aの完了には数えない。

## 123. 混合角の実テンソルへ指定面を接続する（11-14）

一覧：済み 8／全体 48（うち追加 4）

前ターンは進捗あり：`1fc84640c`・`3f38e2eec`で対象ビルド・監査済みの実装と
§121の再見積もりを保存した。作業木はクリーンで再開し、G10や新しい作用には入らない。
以下は既存構成の次数移送・係数移送の法則として型を追加する。

```lean
tensorValue_cast_target_congr (A : Type u) [CommRing A]
    (K : Complex A) (n : ℕ) (d e : Fin n → ℕ)
    (h : d = e) (v : ∀ i, K.X (-(d i : ℤ))) (w : ∀ i, K.X (-(e i : ℤ)))
    (hv : ∀ i, v i = (eqToHom (congrArg (fun t : ℤ => K.X t)
      (congrArg (fun k : ℕ => -(k : ℤ)) (congrFun h i).symm))).hom (w i))
    (z : ℤ) (hd : -(degreeSum n d : ℤ) = z) (he : -(degreeSum n e : ℤ) = z) :
  (eqToHom (congrArg (fun t : ℤ => (power K n).X t) hd)).hom (tensorValue K n d v) =
    (eqToHom (congrArg (fun t : ℤ => (power K n).X t) he)).hom (tensorValue K n e w)
deletedCutTensor_eq_faces (A : Type u) [CommRing A] {m q r : ℕ}
    (S : SSet.{0}) (s : Cut m q) (v : Surjection.Word r (m + 1))
    (a : Fin r) (ha : 0 < outputDegree s v a)
    (j : Fin (outputDegree s v a + 1)) (x : S _⦋q⦌)
    (h : -(degreeSum r (Function.update (outputDegree s v) a
      (outputDegree s v a - 1)) : ℤ) = -((m + q + 1 - r : ℕ) : ℤ) + 1) :
  deletedCutTensor A S s v a ha j x =
    (eqToHom (congrArg (fun t : ℤ => (power (chains A S) r).X t) h)).hom
      (tensorValue (chains A S) r
        (Function.update (outputDegree s v) a (outputDegree s v a - 1))
        (fun c => gen A S _ (S.map (deletedCutFace s v a ha j c).op x)))
```

### 123.1 元の削除テンソルの一致（C162・C163）

C157の指定面、C158の生成元、C160の全体の次数移送を順に適用する、
既存構成の貼り合わせの法則。単体圏の厳密な一致から始め、最後も元の加群の等式で述べる。

```lean
deletedCutTensor_eq_of_faces (A : Type u) [CommRing A] {m q r : ℕ}
    (S : SSet.{0}) (s t : Cut m q) (v : Surjection.Word r (m + 1)) (a b : Fin r)
    (ha : 0 < outputDegree s v a) (hb : 0 < outputDegree t v b)
    (ja : Fin (outputDegree s v a + 1)) (jb : Fin (outputDegree t v b + 1))
    (he : Function.update (outputDegree s v) a (outputDegree s v a - 1) =
      Function.update (outputDegree t v) b (outputDegree t v b - 1))
    (hf : ∀ c, deletedCutFace s v a ha ja c =
      eqToHom (congrArg SimplexCategory.mk (congrFun he c)) ≫ deletedCutFace t v b hb jb c)
    (x : S _⦋q⦌) :
  deletedCutTensor A S s v a ha ja x = deletedCutTensor A S t v b hb jb x
deletedCutTensor_swapSteps (A : Type u) [CommRing A] {m q r : ℕ}
    (S : SSet.{0}) (s : Cut m q) (v : Surjection.Word r (m + 1))
    (a b : Fin (m + q)) (hab : b.val = a.val + 1)
    (ho : 0 < outputDegree s v (label s v.val b.castSucc))
    (hn : 0 < outputDegree (s.swapSteps a b) v (label (s.swapSteps a b) v.val b.castSucc))
    (jo : Fin (outputDegree s v (label s v.val b.castSucc) + 1))
    (jno : jo.val = vertexRank s v.val (label s v.val b.castSucc) b.castSucc)
    (jn : Fin (outputDegree (s.swapSteps a b) v (label (s.swapSteps a b) v.val b.castSucc) + 1))
    (jnn : jn.val = vertexRank (s.swapSteps a b) v.val
      (label (s.swapSteps a b) v.val b.castSucc) b.castSucc) (x : S _⦋q⦌) :
  deletedCutTensor A S (s.swapSteps a b) v
      (label (s.swapSteps a b) v.val b.castSucc) hn jn x =
    deletedCutTensor A S s v (label s v.val b.castSucc) ho jo x
```

### 123.2 同じ符号付き境界項への適用（C164・C165）

C164は同じ有限同値の逆の面番号を評価する法則、C165は既存の実テンソルの一致と
既存の境界符号反転の貼り合わせ。新しい相殺の対合は作らない。

```lean
outputBoundarySign_eq_at_of_rank {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (k : Fin (m + q + 1))
    (j : Fin (outputDegree s v (label s v.val k) + 1))
    (hj : j.val = vertexRank s v.val (label s v.val k) k) :
  outputBoundarySign s v (label s v.val k) j = outputBoundarySignAt s v k
outputBoundaryTerm_swapSteps_of_sign (A : Type u) [CommRing A] {m q r : ℕ}
    (S : SSet.{0}) (s : Cut m q) (v : Surjection.Word r (m + 1))
    (a b : Fin (m + q)) (hab : b.val = a.val + 1)
    (ho : 0 < outputDegree s v (label s v.val b.castSucc))
    (hn : 0 < outputDegree (s.swapSteps a b) v (label (s.swapSteps a b) v.val b.castSucc))
    (jo : Fin (outputDegree s v (label s v.val b.castSucc) + 1))
    (jno : jo.val = vertexRank s v.val (label s v.val b.castSucc) b.castSucc)
    (jn : Fin (outputDegree (s.swapSteps a b) v (label (s.swapSteps a b) v.val b.castSucc) + 1))
    (jnn : jn.val = vertexRank (s.swapSteps a b) v.val
      (label (s.swapSteps a b) v.val b.castSucc) b.castSucc)
    (hs : outputBoundarySignAt (s.swapSteps a b) v b.castSucc =
      -outputBoundarySignAt s v b.castSucc) (x : S _⦋q⦌) :
  outputBoundaryTerm A S (s.swapSteps a b) v (label (s.swapSteps a b) v.val b.castSucc) jn x =
    -outputBoundaryTerm A S s v (label s v.val b.castSucc) jo x
```

### 123.3 正次数の確認と両向きへの適用（C166・C167）

C166は直前同色位置の既存の法則、C167は水平/垂直の向きでC147・C148とC165を使い分ける
証明の分割。混合角の両側の元の出力境界項を、追加の正次数仮定なしに述べる。

```lean
outputDegree_pos_after_vertical {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (a : Fin (m + q)) (ha : a ∉ s.val) :
  0 < outputDegree s v (label s v.val a.succ)
outputBoundaryTerm_swapSteps_mixed (A : Type u) [CommRing A] {m q r : ℕ}
    (S : SSet.{0}) (s : Cut m q) (v : Surjection.Word r (m + 1))
    (a b : Fin (m + q)) (hab : b.val = a.val + 1) (hc : a ∈ s.val ↔ b ∉ s.val)
    (jo : Fin (outputDegree s v (label s v.val b.castSucc) + 1))
    (jno : jo.val = vertexRank s v.val (label s v.val b.castSucc) b.castSucc)
    (jn : Fin (outputDegree (s.swapSteps a b) v (label (s.swapSteps a b) v.val b.castSucc) + 1))
    (jnn : jn.val = vertexRank (s.swapSteps a b) v.val
      (label (s.swapSteps a b) v.val b.castSucc) b.castSucc) (x : S _⦋q⦌) :
  outputBoundaryTerm A S (s.swapSteps a b) v (label (s.swapSteps a b) v.val b.castSucc) jn x =
    -outputBoundaryTerm A S s v (label s v.val b.castSucc) jo x
```

### 123.4 構成済みの対合の混合角の分岐へ戻す（C168・C169）

C168は既存の添字同値に沿う値の定義の評価、C169はC167を既存のMixedVertex分類と
既存の全体の次数移送へ適用する証明の分割。
C161の証明内で使う局所的なcastの法則は
`hcast (M N : ModuleCat A) (hMN : M = N) (y : M) : HEq ((eqToHom hMN).hom y) y`。
等式の帰納法で証明し、HEqは依存した型の処理にだけ使う。出力はすべて元の加群の等式。

```lean
universalBoundaryValue_output (A : Type u) [CommRing A] (S : SSet.{0}) {r d : ℕ}
    (w : Surjection.BasisWord (r + 1) d) (q : ℕ) (x : S _⦋q⦌)
    (s : Cut (r + d) q) (k : Fin (r + d + q + 1))
    (h : -((r + d + q + 1 - (r + 1) : ℕ) : ℤ) + 1 = -((d + q : ℕ) : ℤ) + 1) :
  universalBoundaryValue A S w q x (.inl ⟨s, k⟩) =
    (eqToHom (congrArg (fun t : ℤ => (power (chains A S) (r + 1)).X t) h)).hom
      (outputBoundaryTerm A S s (positiveWord w) (label s (positiveWord w).val k)
        ((colorPositionEquiv s (positiveWord w)).symm k).2 x)
universalBoundaryValue_mixed_neg (A : Type u) [CommRing A] (S : SSet.{0}) {r d : ℕ}
    (w : Surjection.BasisWord (r + 1) d) (q : ℕ) (x : S _⦋q⦌)
    (t : BoundaryVertexOfKind (r + d) q .mixed) :
  universalBoundaryValue A S w q x (.inl (vertexCornerPerm (r + d) q t.val)) =
    -universalBoundaryValue A S w q x (.inl t.val)
```

### 123.5 混合角の分岐の完了・検証・保存

一覧：済み 8／全体 48（うち追加 4）

次の五本、**316行**が対象ビルド・合同監査を通った。
登録候補の接頭部は `SerrePositivity.EInfinity.SimplexCuts.`。

- `DeletedFaceTensors`：75行
- `CornerDeletedTensors`：66行
- `CornerBoundaryTerms`：52行
- `MixedCornerTerms`：61行
- `MixedBoundaryValues`：62行

対象ビルド `/tmp/bsw16/m14-mixed-boundary-values-04.log` は五本すべて成功、Leanの警告0。
専用監査 `/tmp/bsw16/audit-m14-mixed-boundary-values.log` は
**5モジュール・19宣言・標準三公理のみ**。新規五本のsorry・追加公理0、
個々の補題200行以下。既存公開宣言・共通入口・共通監査は変更していない。

独立の有限点検では、m=0〜4・q=0〜3・色数1〜3の全射非退化語と全混合角で
**9,536組**の実際の出力境界符号・削除後の全色の列・正規化での零を確認した。
そのうち**4,080組**は削除面の重複により正規化で零となる。
Leanではこの有限点検を仮定せず、既存の指定面の厳密一致と次数移送の法則から証明した。

`universalBoundaryValue_mixed_neg`は、L09aの三群の貼り合わせ
`universalBoundaryPartner_neg_of_cases`の**hmixを、そのまま仮定なく供給する**。
条件を弱めたり符号の仮定を追加したりしていない。
L09a全体・L09は未完了で、残るのは水平のhc・垂直のhvと有限和から微分への包装。
したがって一覧の完了件数はまだ増やさない。

L09a・L09累計 **5,015行**、改訂MayのM14全体 **10,081行**。
§121の混合角の180〜300行の見込みに対し、§122の131行と今回の316行で実測**447行**、
差は**+147〜+267行**。指定面の一致だけでは元の`deletedCutTensor`内の依存した型の
二段の移送を解消できず、因子ごとの生成元と全体の終域次数までを明示的に接続したため。
新しい数学の追加ではなく同じ構成の照合だが、この行数も外枠に含める。
混合角の残りは0行として、ほかの見込みを据え置いたM14完成見込みは
**19,211〜26,521行**。上端は外枠25,000行を1,521行上回るリスクが残る。
外枠の変更は仮定せず、水平の分岐へ続行する。

## 124. 水平・垂直の符号に共通する接頭順位（11-14、続行）

一覧：済み 8／全体 48（うち追加 4）

混合角の完了は **46bd6230f** に保存済み。
次は水平の分岐の符号を照合するため、展開した語の順位を元の語と垂直座標で読む。
m=0〜4・q=0〜3・色数1〜3の全ての語（全射性・非退化性を要求しない）で
**142,272頂点**の順位を点検してから実装した。
これはL09a内の接頭部分の有限の数え上げ。型は次のとおり。

```lean
caesuraRank_label {m q r : ℕ} (s : Cut m q) (v : Fin (m + 1) → Fin r)
    (k : Fin (m + q + 1)) :
  Surjection.caesuraRank (label s v) k =
    (s.vertical k).val + Surjection.caesuraRank v (s.horizontal k)
```

証明は経路の頂点の帰納法で、水平辺では元の語のcaesuraだけが、垂直辺では一つが増える。
既存のC129・C130、`step_of_mem`・`step_of_notMem`と隣接順位C135を使う。
この法則を水平の単語削除係数と垂直の入力面の交代符号の双方へ使い、
重み付き逆転数の二重和の展開を各分岐で繰り返さない。

### 124.1 同じ削除集合の重み付き和（C171・C172）

既存C121・C122の集合の一致に有限和を適用する法則。
位置数1〜6・色数1〜3の全色列の活動/最後の位置について、
重みH(i)=iおよびH(i)=(i+1)²で**11,344例**を点検してから実装する。

```lean
caesura_sum_erase_active {N r : ℕ} (v : Fin (N + 1) → Fin r)
    (a : Fin (N + 1)) (ha : Surjection.Caesura v a) (H : Fin (N + 1) → ℕ) :
  (∑ i ∈ caesuraPositions v, H i) =
    (∑ i ∈ caesuraPositions (Surjection.erase v a), H (a.succAbove i)) + H a
caesura_sum_erase_final {N r : ℕ} (v : Fin (N + 1) → Fin r)
    (a : Fin (N + 1)) (ha : ¬Surjection.Caesura v a)
    (hp : (Surjection.previousOccurrences v a).Nonempty) (H : Fin (N + 1) → ℕ) :
  (∑ i ∈ caesuraPositions v, H i) =
    (∑ i ∈ caesuraPositions (Surjection.erase v a), H (a.succAbove i)) +
      H (previousVertex v a hp)
```

### 124.2 削除後に残る区間の右端（C173）

一般の座標対応について既存C06の達成上界の法則を適用する、L09a内の有限fiberの評価。
水平な二辺の内部の削除と両端の削除で、p=1〜5・q=0〜4の全経路の
残る区間の右端を**5,700例**点検してから実装する。
C173はその座標の対応を引数とする共通法則。水平の具体的な対応への適用は次に行う。

```lean
hi_eq_of_coordinate_cover {m n q : ℕ} (s : Cut m q) (t : Cut n q)
    (ρ : Fin (n + q + 1) → Fin (m + q + 1)) (φ : Fin (n + 1) → Fin (m + 1))
    (hφ : Function.Injective φ)
    (hh : ∀ j, s.horizontal (ρ j) = φ (t.horizontal j))
    (hv : ∀ j, s.vertical (ρ j) = t.vertical j) (i : Fin (n + 1))
    (hcover : ∀ j, s.horizontal j = φ i → ∃ k, ρ k = j) :
  hi t i = hi s (φ i)
```

### 124.3 水平の座標公式と位置指数への適用（C174〜C176）

§124.1・§124.2の有限点検の組合せに対応する法則。
C174は既存の`horizontalDeletion_horizontal`・`horizontalDeletion_vertical`をC173へ渡す。
C175・C176は同じ右端の重みについてC171・C172を評価する。
局所的な法則`positionExponent_eq_caesura_sum`は位置指数の定義を有限集合の和へ戻すだけ。

```lean
hi_horizontalDeletion {m q : ℕ} (s : Cut (m + 1) q)
    (a b : Fin (m + 1 + q)) (hab : b.val = a.val + 1)
    (ha : a ∈ s.val) (hb : b ∈ s.val) (i : Fin (m + 1)) :
  hi ((BarrattEccles.horizontalInsertionEquiv m q a).symm ⟨s, ha⟩) i =
    hi s ((s.horizontal a.succ).succAbove i)
positionExponent_eq_caesura_sum {m q r : ℕ} (s : Cut m q)
    (v : Fin (m + 1) → Fin r) :
  positionExponent s v = ∑ i ∈ caesuraPositions v, hi s i
positionExponent_erase_active {m q r : ℕ} (s : Cut (m + 1) q) (t : Cut m q)
    (v : Fin (m + 2) → Fin r) (a : Fin (m + 2)) (ha : Surjection.Caesura v a)
    (hh : ∀ i, hi t i = hi s (a.succAbove i)) :
  positionExponent s v = positionExponent t (Surjection.erase v a) + hi s a
positionExponent_erase_final {m q r : ℕ} (s : Cut (m + 1) q) (t : Cut m q)
    (v : Fin (m + 2) → Fin r) (a : Fin (m + 2)) (ha : ¬Surjection.Caesura v a)
    (hp : (Surjection.previousOccurrences v a).Nonempty)
    (hh : ∀ i, hi t i = hi s (a.succAbove i)) :
  positionExponent s v = positionExponent t (Surjection.erase v a) +
    hi s (previousVertex v a hp)
```

### 124.4 活動区間の係数削除の符号（C177）

元の語の活動区間を消す場合、C170の垂直座標とC175の右端が等しく、
同じ(-1)の冪が二回現れて消える。m=1〜4・q=0〜3・色数1〜3の全色列の
内部/両端の水平削除で、活動位置を消す**27,644例**を点検してから実装する。
これはL09a内の既存の符号規則の照合で、界面・作用・operad則は変更しない。

```lean
signedDeletionCoefficient_horizontal_active {m q r : ℕ}
    (s : Cut (m + 1) q) (t : Cut m q) (v : Fin (m + 2) → Fin r)
    (a : Fin (m + 2)) (k : Fin (m + 1 + q + 1)) (ha : Surjection.Caesura v a)
    (hk : s.horizontal k = a) (hy : (s.vertical k).val = hi s a)
    (hh : ∀ i, hi t i = hi s (a.succAbove i)) :
  (-1 : ℤ) ^ positionExponent s v * Surjection.deletionCoefficient (label s v) k =
    Surjection.deletionCoefficient v a * (-1 : ℤ) ^ positionExponent t (Surjection.erase v a)
```

C177の局所的な整数積の法則の型は
`cancel (P R : ℤ) (n : ℕ) : (P * (-1 : ℤ)^n) * ((-1 : ℤ)^n * R) = R * P`。
`(-1)^n * (-1)^n = 1`と可換結合法則だけを使う。
最後の非活動区間の分岐と、実テンソル/無効な削除語の零の照合はまだ残る。

### 124.5 最後の位置の前にある同色頂点（C178）

m=1〜4・q=0〜3・色数1〜3の全ての色列について、一頂点の水平区間で元の語に
直前同色位置がある**27,644例**を点検してから実装する。
元の語と展開語の既存の`previousOccurrences`の最大を、同じ水平fiberの最大で照合する
有限の数え上げ。新しいBE作用や削除の構成は作らない。

```lean
previousVertex_label_horizontal_singleton {m q r : ℕ} (s : Cut m q)
    (v : Fin (m + 1) → Fin r) (a : Fin (m + 1)) (k : Fin (m + q + 1))
    (hk : s.horizontal k = a) (hsingle : ∀ j, s.horizontal j = a → j = k)
    (hp : (Surjection.previousOccurrences v a).Nonempty)
    (he : (Surjection.previousOccurrences (label s v) k).Nonempty) :
  previousVertex (label s v) k he =
    (intervalPositions s (previousVertex v a hp)).max'
      (intervalPositions_nonempty s (previousVertex v a hp))
```

### 124.6 最後の非活動区間の係数削除の符号（C179）

m=1〜4・q=0〜3・色数1〜3の全ての色列の内部/両端の水平削除について、
元の語の最後の非活動位置で直前同色位置がある**18,374例**を点検してから実装する。
C178で直前同色区間の最後を指定し、C170・C176と既存の最後の削除係数の法則を適用する。
同じ右端の冪の二乗を消す局所法則`cancel`の型はC177と同じ。

```lean
signedDeletionCoefficient_horizontal_final {m q r : ℕ}
    (s : Cut (m + 1) q) (t : Cut m q) (v : Fin (m + 2) → Fin r)
    (a : Fin (m + 2)) (k : Fin (m + 1 + q + 1)) (ha : ¬Surjection.Caesura v a)
    (hk : s.horizontal k = a) (hsingle : ∀ j, s.horizontal j = a → j = k)
    (hp : (Surjection.previousOccurrences v a).Nonempty)
    (he : (Surjection.previousOccurrences (label s v) k).Nonempty)
    (hh : ∀ i, hi t i = hi s (a.succAbove i)) :
  (-1 : ℤ) ^ positionExponent s v * Surjection.deletionCoefficient (label s v) k =
    Surjection.deletionCoefficient v a *
      (-1 : ℤ) ^ positionExponent t (Surjection.erase v a)
```

### 124.7 接頭順位と水平削除係数の検証済み区切り

一覧：済み 8／全体 48（うち追加 4）

次の七本 **366行**を対象ビルド・監査済みとして保存する。
登録候補の接頭部は `SerrePositivity.EInfinity.SimplexCuts.`。

- `ExpandedCaesuraRanks`：46行
- `CaesuraDeletionSums`：42行
- `DeletedIntervalMaxima`：38行
- `HorizontalDeletionExponents`：79行
- `HorizontalActiveDeletionSigns`：38行
- `HorizontalPreviousVertices`：62行
- `HorizontalFinalDeletionSigns`：61行

対象ビルドは`m14-expanded-caesura-ranks-02.log`、`m14-caesura-deletion-sums-01.log`、
`m14-deleted-interval-maxima-01.log`、`m14-horizontal-deletion-exponents-01.log`、
`m14-horizontal-active-deletion-signs-02.log`、`m14-horizontal-previous-vertices-01.log`、
`m14-horizontal-final-deletion-signs-03.log`（いずれも`/tmp/bsw16/`）で成功。
新規七本のLean警告0、sorry・追加公理0、`git diff --check`成功。
個々の補題は200行以下。
専用監査 `/tmp/bsw16/audit-m14-horizontal-deletion-signs.log` は
**7モジュール・23宣言・標準三公理のみ**。
鍵スクリプトの他レーンの既存ビルド検出通知は出たが、監査のLeanの警告/エラーはない。
鍵を持つ常駐プロセスは作っていない。

C170は全ての色関数で成立し、Wordの非退化性を余分に仮定していない。
C174は内部の水平削除の右端の具体的な対応、C175・C176は同じ右端を受け取る一般の位置指数の法則。
C177・C179により、活動区間・最後の非活動区間の両方で、位置指数と単語削除係数が
元の語の削除係数へ戻るところまで検証した。

**水平のhcはまだ未完了**。共通の削除色列の逆転符号を小さい切断の符号へ移すこと、
始端・終端への具体的な座標対応、実テンソルの一致、削除語が無効な場合の零が残る。
C179の元の語と展開語の先行同色の非空性は、適用時に正の出力次数から供給する必要がある。
その適用を仮定したままhcを証明したとは報告しない。垂直のhvも未完了。

L09a・L09累計 **5,381行**、改訂MayのM14全体 **10,447行**。
次の1,000行の区切りは約5,600行。12,500行の半分報告・25,000行の外枠には未到達。
次は、同じ色列の次数移送で削除後の逆転符号を比較し、活動/最後の二つの係数公式を
実際の水平境界符号へ適用する。共通入口・共通監査・界面の変更は行わない。

## 125. 水平の実際の符号へ接続する（11-14）

一覧：済み 8／全体 48（うち追加 4）

前ターンは進捗あり：`46bd6230f`で混合角の実境界値の相殺、`5f9f9d382`で
水平の二種類の削除係数の照合を対象ビルド・監査後に保存した。クリーンな作業木で再開。
以下は同じ有限順序の次数移送・既存符号の照合・L09a内の有限な先行位置の分類。
C181の事前点検は§124.5の27,644例、C182は§124.4・§124.6の両分岐を使う。

```lean
caesuraInversionCount_congr_length {N M r : ℕ} (h : N = M)
    (v : Fin N → Fin r) (w : Fin M → Fin r) (he : ∀ i, v i = w (Fin.cast h i)) :
  positionInversionCount v (caesuraPositions v) = positionInversionCount w (caesuraPositions w)
erasedColorSign_eq_permutationSign {m q n q' r : ℕ} (s : Cut m q)
    (v : Fin (m + 1) → Fin r) (k : Fin (m + q + 1)) (t : Cut n q')
    (w : Fin (n + 1) → Fin r) (h : m + q = n + q' + 1)
    (he : ∀ i, Surjection.erase (label s v) k i = label t w (Fin.cast h i)) :
  erasedColorSign (label s v) k = (-1 : ℤ) ^ permutationExponent t w
previousOccurrences_of_horizontal_singleton {m q r : ℕ} (s : Cut m q)
    (v : Fin (m + 1) → Fin r) (a : Fin (m + 1)) (k : Fin (m + q + 1))
    (hk : s.horizontal k = a) (hsingle : ∀ j, s.horizontal j = a → j = k)
    (he : (Surjection.previousOccurrences (label s v) k).Nonempty) :
  (Surjection.previousOccurrences v a).Nonempty
signedDeletionCoefficient_horizontal {m q r : ℕ}
    (s : Cut (m + 1) q) (t : Cut m q) (v : Surjection.Word r (m + 2))
    (a : Fin (m + 2)) (k : Fin (m + 1 + q + 1))
    (hk : s.horizontal k = a) (hsingle : ∀ j, s.horizontal j = a → j = k)
    (hd : 0 < outputDegree s v (label s v.val k))
    (hh : ∀ i, hi t i = hi s (a.succAbove i)) :
  (-1 : ℤ) ^ positionExponent s v.val * Surjection.deletionCoefficient (label s v.val) k =
    Surjection.deletionCoefficient v.val a *
      (-1 : ℤ) ^ positionExponent t (Surjection.erase v.val a)
```

### 125.1 同じ小さい切断の実符号へ戻す（C183・C184）

C180・C182を、元のC127の出力符号の式へ適用する既存構成の符号照合。
内部の具体的な対応には、既存の水平削除座標公式とC174を使う。
有効な削除語の実テンソル・無効な語の零はまだ主張しない。
局所的な整数積の法則は`rearrange (P E D : ℤ) : P * E * D = E * (P * D)`。

```lean
outputBoundarySignAt_horizontal_of_coordinates {m q r : ℕ}
    (s : Cut (m + 1) q) (t : Cut m q)
    (v : Surjection.Word r (m + 2)) (w : Surjection.Word r (m + 1))
    (a : Fin (m + 2)) (k : Fin (m + 1 + q + 1))
    (hk : s.horizontal k = a) (hsingle : ∀ j, s.horizontal j = a → j = k)
    (hd : 0 < outputDegree s v (label s v.val k))
    (hh : ∀ i, hi t i = hi s (a.succAbove i)) (hw : w.val = Surjection.erase v.val a)
    (he : ∀ i, Surjection.erase (label s v.val) k i =
      label t w.val (Fin.cast (by omega : m + 1 + q = m + q + 1) i)) :
  outputBoundarySignAt s v k = Surjection.deletionCoefficient v.val a * cutSign t w.val
outputBoundarySignAt_horizontalDeletion {m q r : ℕ} (s : Cut (m + 1) q)
    (v : Surjection.Word r (m + 2)) (a b : Fin (m + 1 + q))
    (hab : b.val = a.val + 1) (ha : a ∈ s.val) (hb : b ∈ s.val)
    (w : Surjection.Word r (m + 1))
    (hw : w.val = Surjection.erase v.val (s.horizontal a.succ))
    (hd : 0 < outputDegree s v (label s v.val a.succ)) :
  outputBoundarySignAt s v a.succ =
    Surjection.deletionCoefficient v.val (s.horizontal a.succ) *
      cutSign ((BarrattEccles.horizontalInsertionEquiv m q a).symm ⟨s, ha⟩) w.val
```

### 125.2 小さい切断の更新次数と指定面（C185・C186）

既存の削除列の一致の長さと、単体圏の頂点列の単射性を使う既存構成の照合。
混合角で使ったC152・C157を、区間数の異なる小さい切断との比較にも使える形で述べる。
削除列の具体的な一致自体を新しい仮定として残してhcを証明したことにはしない。

```lean
deletedOutputDegree_eq_of_vertexLists {m n q r : ℕ} (s : Cut m q) (t : Cut n q)
    (v : Surjection.Word r (m + 1)) (w : Surjection.Word r (n + 1))
    (k : Fin (m + q + 1)) (hd : 0 < outputDegree s v (label s v.val k))
    (hl : ∀ c, deletedVerticesList s v.val k c = verticesList t w.val c) :
  Function.update (outputDegree s v) (label s v.val k)
    (outputDegree s v (label s v.val k) - 1) = outputDegree t w
deletedCutFace_eq_of_vertexLists {m n q r : ℕ} (s : Cut m q) (t : Cut n q)
    (v : Surjection.Word r (m + 1)) (w : Surjection.Word r (n + 1))
    (k : Fin (m + q + 1)) (hd : 0 < outputDegree s v (label s v.val k))
    (hl : ∀ c, deletedVerticesList s v.val k c = verticesList t w.val c)
    (j : Fin (outputDegree s v (label s v.val k) + 1))
    (hj : j.val = vertexRank s v.val (label s v.val k) k) (c : Fin r) :
  deletedCutFace s v (label s v.val k) hd j c =
    eqToHom (congrArg SimplexCategory.mk
      (congrFun (deletedOutputDegree_eq_of_vertexLists s t v w k hd hl) c)) ≫ face t w c
```

### 125.3 約5,600行の区切り・B4前の検証済み保存

一覧：済み 8／全体 48（うち追加 4）

今回の四本 **214行**は対象ビルド成功、専用監査
`/tmp/bsw16/audit-m14-horizontal-boundary-signs.log` も
**4モジュール・14宣言・標準三公理のみ**で成功。Leanの警告0、sorry・追加公理0。
登録候補の接頭部は `SerrePositivity.EInfinity.SimplexCuts.`。

- `ErasedColorSignComparisons`：37行
- `HorizontalDeletionCoefficients`：56行
- `HorizontalBoundarySigns`：74行
- `HorizontalDeletedFaces`：47行

対象ビルドの最終ログは`m14-horizontal-deletion-coefficients-01.log`の後者の対象、
`m14-horizontal-boundary-signs-01.log`、`m14-horizontal-deleted-faces-01.log`（`/tmp/bsw16/`）。
L09a・L09実測 **5,595行**、改訂MayのM14全体 **10,661行**。
約5,600行の1,000行区切りとして報告する。個々の補題は200行以下。

内部の水平境界の**元の実符号**が、元の語の削除係数と小さい切断のcutSignに一致した。
削除列が同じ場合の更新次数と指定面の厳密一致も閉じた。
水平hcの実テンソルへの接続、両端、無効な削除語の零、垂直hvはまだ残る。
§121・§123.5の全体見込みと外枠超過のリスクは、B4を理由に縮小した扱いにはしない。

## 126. B4の追従を先に行う（11-14昼）

一覧：済み 8／全体 48（うち追加 4）

調整役のB4指示を受領しM14の新しい実装より優先する。
mainの`citation-attributes.md` §14と`bulk-w1-b3/B4-README.md`を読んだ。
現在の四本の対象ビルドと監査を完了して先に保存し、main取り込み前のソースから採取する。
基準はc5c4436c0、本体のみ・drafts除外。
昼の採取は`--class impl --wait 3600`で組ごとに取り、280秒の実行上限で分ける。
索引と原ソースを保持し、保留0と差分確認の後にmainを取り込む。
取り込み後のソースには古い索引を適用しない。

### 126.1 B4採取中の記録（main取り込み前）

一覧：済み 8／全体 48（うち追加 4）

M14の検証済み四本は **94c593fe0** に保存済み。
基準c5c4436c0から自枝のコミットが触った本体Leanを再集計し、draftsを除外した対象は
**106本**。既存のB4一覧95本をすべて含み、その後の11本を加えた。
main上には、この106本の同名ファイルはまだないことも確認した。

採取前のソースコミット・全106本のSHA256・改名表のSHA256は
`bulk-w1-b4/bs-impl-before.json`に保存した。
原ソースの完全なコピー、分割した採取のJSON、ログは
`/tmp/bsw16/b4-20261114/`に保持している。
初期の6本の組の鍵内実行時間が約72秒だったため、進行中の組の完了と鍵返却を確認して
12本の組へまとめ直した。採取済み24本は原ソース一致を再検証して引き継ぎ、
未採取分のみを続行している。各組は`--class impl --wait 3600`、実行上限280秒。
整理券を重複して発行していない。

この記録時点の採取完了は **36／106本**。採取ジョブは稼働しており、次の組は鍵待ち。
完了済み36本の26,311件の参照を定義元つき改名表へ照合した範囲では、
移動する宣言への直接参照は0。これは**部分的な事前照合**であり、
全件のrewrite・`review.json`の保留0の確認に代えるものではない。
通常importのmodule-mapへの直接該当と、106本自身のファイル配置の移動の該当はともに0。
非修飾名の最終的な確認には全件の採取と正式rewriteを使う。

取り込み後の対象ビルドの範囲は、106本の自モジュール内のimportグラフから求めた。
次の8本の上位importerをすべてビルドすると、自分の106本を推移的にすべて覆う。
追加の依存が少ない順と被覆数は`bulk-w1-b4/bs-impl-build-scope.json`、
詳細な依存グラフは`/tmp/bsw16/b4-20261114/build-coverage-plan.json`に保存した。
これは計画であり、まだmain取り込み後のビルド成功を主張しない。

- `SerrePositivity.EInfinity.SimplexCuts.GeneratorBoundary`
- `SerrePositivity.EInfinity.SimplexCuts.TopTerm`
- `SerrePositivity.EInfinity.SimplexCuts.StraightTraceFaces`
- `SerrePositivity.EInfinity.SimplexCuts.TerminalSignData`
- `SerrePositivity.EInfinity.SimplexCuts.Normalization`
- `SerrePositivity.EInfinity.SimplexCuts.HorizontalDeletedFaces`
- `SerrePositivity.EInfinity.SimplexCuts.HorizontalBoundarySigns`
- `SerrePositivity.EInfinity.SimplexCuts.MixedBoundaryValues`

106本それぞれに宣言があることと標準三公理のみであることを検査する専用監査も用意した。
採取中のLeanソースは変更せず、M14の次のLean実装には戻っていない。
全件の採取→rewrite・保留/差分確認→main取り込み→対象ビルド/専用監査の順を保つ。

### 126.2 B4の完了：採取・プレビュー・main取り込み・検証

一覧：済み 8／全体 48（うち追加 4）

**B4は完了**。基準以降に自枝で追加・変更した、存在する本体Leanは**106本**で、
対象JSONとの一致と、drafts以外の採取漏れ0を確認した。
原ソースは **94c593fe0** のLeanに対応し、その後の文書コミットでLeanは変更していない。
全106本をmain取り込み前の環境で採取し、索引と原ソースの完全なバイト一致を保って
正式`bulk_namespace.py rewrite`を実行した（終了0）。

- 採取：106／106本、10組、各実行上限280秒。鍵は組ごとに返却。
- プレビュー：`review.json`は空、**保留0件**。
- 差分確認：106本すべてを比較し、**書き換え0ファイル・削除0行・追加0行**。
- 通常import・ファイル配置のmodule-map該当も0。importの追加の変更は不要。
- main取り込み：**923a15dd6**、main側の親は **efa846fe8**（16d6b4547以降）。競合なし。
- 取り込み後：106本が事前に生成したプレビューと一致し、import被覆グラフも不変。
  古い索引を取り込み後のソースへ適用し直していない。

原ソース・索引・分割ログ・プレビューは`/tmp/bsw16/b4-20261114/`に保持。
初期の組をまとめ直す際は、当該採取プロセスの終了と鍵返却を確認し、
旧監視ドライバだけを計画的に終了した。検証済み24本をバイト一致で再検証し、
未採取分のみを新しい監視ドライバへ引き継いだ。
この切替の記録は`batch-transition.json`。旧監視ドライバの終了137を、
採取の失敗や未完の索引の成功扱いにはしていない。
全106本を受け取る正式rewriteでも索引と原ソースの検査を通した。

対象ビルドは、全106本を覆う8対象を、依存の追加が少ない順に3組で実行した。
各組は独立した`with_build_lock.sh --class impl --wait 3600`で鍵を取り、終了後返却した。

| 組 | 対象（接頭部`SerrePositivity.EInfinity.SimplexCuts.`） | 結果 |
| --- | --- | --- |
| 1 | GeneratorBoundary・TopTerm・StraightTraceFaces・TerminalSignData・Normalization | 成功、2,376 jobs |
| 2 | HorizontalDeletedFaces・HorizontalBoundarySigns | 成功、2,257 jobs |
| 3 | MixedBoundaryValues | 成功、2,289 jobs |

続けて別の一回の鍵で、106本をそれぞれ明示した専用監査を実行。
**106モジュール・967宣言・標準三公理のみ**で成功した。
各モジュールの宣言が0でないことも検査しており、狭い一対象だけの監査を106本の証拠にしていない。
新規106本のsorry・追加公理0、Leanの警告0。`git diff --check`成功。
rootビルド・共通入口・共通監査への登録は調整役の持ち分のまま。

永続的な検収資料は`bulk-w1-b4/`の次のファイル。

- `bs-impl-before.json`：全106ファイルの一覧、原ソースと改名表のSHA256、元のソースコミット。
- `bs-impl-rewrite.json`：保留0・106本一致・ソース差分0の結果。
- `bs-impl-build-scope.json`：8対象による106本の被覆と実際のビルド結果。
- `bs-impl-audit-source.lean.txt`：実行した専用監査の原文（本体のLeanではない検証資料）。
- `bs-impl-audit-result.txt`：監査の成功出力。
- `bs-impl-result.json`：merge親・各ログのハッシュ・967宣言の監査結果をまとめた記録。

**登録候補は`bs-impl-before.json`の全106モジュール**。全て
`SerrePositivity.EInfinity.SimplexCuts.*`で、B4による場所・名前の変更はない。
入口のimportは上の8対象で106本を覆う。監査の宣言元を選ぶ際は全106本を対象にできる。

B4で自レーンのLeanの差分は0なので、L09a・L09 **5,595行**、M14 **10,661行**の計数は不変。
B4の検収報告後、承認待ちを挟まず/goalの水平hcの実テンソルの接続へ戻る。

## 127. B4完了後：小さい切断の実テンソルへ戻す（11-14）

一覧：済み 8／全体 48（うち追加 4）

B4完了は **595254e10** に保存した。取り込み済みmainの環境で/goalへ戻る。
以下はC185・C186の同じ削除列の一致を、元の`cutTensor`と`cutTensorAt`へ接続する
既存構成の次数移送・貼り合わせの法則。新しい作用・錐・ホモトピーは作らない。
C188・C189の`h`は型を合わせる次数の等式で、C187と既存の全出力次数の式から導ける。
具体的な水平の削除列の一致は、別に既存C89から供給する。未供給のままhcを閉じたとは扱わない。

```lean
degreeSum_deleted_small_cut {m n q r : ℕ} (s : Cut m q) (t : Cut n q)
    (v : Surjection.Word r (m + 1)) (w : Surjection.Word r (n + 1))
    (k : Fin (m + q + 1)) (hd : 0 < outputDegree s v (label s v.val k))
    (hl : ∀ c, deletedVerticesList s v.val k c = verticesList t w.val c) :
  degreeSum r (outputDegree t w) + 1 = m + q + 1 - r
deletedCutTensor_eq_small_cutTensor (A : Type u) [CommRing A] {m n q r : ℕ}
    (S : SSet.{0}) (s : Cut m q) (t : Cut n q)
    (v : Surjection.Word r (m + 1)) (w : Surjection.Word r (n + 1))
    (k : Fin (m + q + 1)) (hd : 0 < outputDegree s v (label s v.val k))
    (hl : ∀ c, deletedVerticesList s v.val k c = verticesList t w.val c)
    (j : Fin (outputDegree s v (label s v.val k) + 1))
    (hj : j.val = vertexRank s v.val (label s v.val k) k) (x : S _⦋q⦌)
    (h : -(degreeSum r (outputDegree t w) : ℤ) = -((m + q + 1 - r : ℕ) : ℤ) + 1) :
  deletedCutTensor A S s v (label s v.val k) hd j x =
    (eqToHom (congrArg (fun z : ℤ => (power (chains A S) r).X z) h)).hom (cutTensor A S t w x)
deletedCutTensor_eq_small_cutTensorAt (A : Type u) [CommRing A] {m n q r : ℕ}
    (S : SSet.{0}) (s : Cut m q) (t : Cut n q)
    (v : Surjection.Word r (m + 1)) (w : Surjection.Word r (n + 1))
    (k : Fin (m + q + 1)) (hd : 0 < outputDegree s v (label s v.val k))
    (hl : ∀ c, deletedVerticesList s v.val k c = verticesList t w.val c)
    (j : Fin (outputDegree s v (label s v.val k) + 1))
    (hj : j.val = vertexRank s v.val (label s v.val k) k) (x : S _⦋q⦌)
    (h : -((n + q + 1 - r : ℕ) : ℤ) = -((m + q + 1 - r : ℕ) : ℤ) + 1) :
  deletedCutTensor A S s v (label s v.val k) hd j x =
    (eqToHom (congrArg (fun z : ℤ => (power (chains A S) r).X z) h)).hom (cutTensorAt A S t w x)
```

C189の局所法則は`step {M N P : ModuleCat A} (hMN : M = N) (hNP : N = P) (y : M) :
(eqToHom hNP).hom ((eqToHom hMN).hom y) = (eqToHom (hMN.trans hNP)).hom y`。
等式の帰納法だけを使う。

### 127.1 検証

対象ビルド成功（2,189 jobs）。別の一回の鍵で専用監査も成功、1モジュール・3宣言・標準三公理のみ。
新規82行、L09a・L09 5,677行、M14 10,743行。sorry・追加公理0。
登録候補：`SerrePositivity.EInfinity.SimplexCuts.DeletedSmallCutTensors`。
一覧：済み 8／全体 48（うち追加 4）。

## 128. 内部の水平面の元の実テンソル（11-14）

一覧：済み 8／全体 48（うち追加 4）

C190–C192は既存C89・C184・C189の係数移送と貼り合わせの法則。
新しい組合せ分解はなく、有限点検済みのC89の削除列をそのまま各色へ写す。
次数等式`h`を明示して共通次数の指定移送を固定し、ホモトピー圏へは移らない。
型は次のとおり。いずれも200行以内。

```lean
lemma deletedVerticesList_horizontalDeletion {m q r : ℕ} (s : Cut (m + 1) q)
    (v : Fin (m + 2) → Fin r) (a b : Fin (m + 1 + q))
    (hab : b.val = a.val + 1) (ha : a ∈ s.val) (hb : b ∈ s.val)
    (w : Fin (m + 1) → Fin r) (hw : w = Surjection.erase v (s.horizontal a.succ))
    (c : Fin r) :
    deletedVerticesList s v a.succ c =
      verticesList ((BarrattEccles.horizontalInsertionEquiv m q a).symm ⟨s, ha⟩) w c

lemma deletedCutTensor_horizontalDeletion {m q r : ℕ} (S : SSet.{0})
    (s : Cut (m + 1) q) (v : Surjection.Word r (m + 2))
    (a b : Fin (m + 1 + q)) (hab : b.val = a.val + 1) (ha : a ∈ s.val) (hb : b ∈ s.val)
    (w : Surjection.Word r (m + 1))
    (hw : w.val = Surjection.erase v.val (s.horizontal a.succ))
    (hd : 0 < outputDegree s v (label s v.val a.succ))
    (j : Fin (outputDegree s v (label s v.val a.succ) + 1))
    (hj : j.val = vertexRank s v.val (label s v.val a.succ) a.succ) (x : S _⦋q⦌)
    (h : -((m + q + 1 - r : ℕ) : ℤ) = -((m + 1 + q + 1 - r : ℕ) : ℤ) + 1) :
    deletedCutTensor A S s v (label s v.val a.succ) hd j x =
      (eqToHom (congrArg (fun z : ℤ => (power (chains A S) r).X z) h)).hom
        (cutTensorAt A S ((BarrattEccles.horizontalInsertionEquiv m q a).symm ⟨s, ha⟩) w x)

lemma signedDeletedCutTensor_horizontalDeletion {m q r : ℕ} (S : SSet.{0})
    (s : Cut (m + 1) q) (v : Surjection.Word r (m + 2))
    (a b : Fin (m + 1 + q)) (hab : b.val = a.val + 1) (ha : a ∈ s.val) (hb : b ∈ s.val)
    (w : Surjection.Word r (m + 1))
    (hw : w.val = Surjection.erase v.val (s.horizontal a.succ))
    (hd : 0 < outputDegree s v (label s v.val a.succ))
    (j : Fin (outputDegree s v (label s v.val a.succ) + 1))
    (hj : j.val = vertexRank s v.val (label s v.val a.succ) a.succ) (x : S _⦋q⦌)
    (h : -((m + q + 1 - r : ℕ) : ℤ) = -((m + 1 + q + 1 - r : ℕ) : ℤ) + 1) :
    outputBoundarySignAt s v a.succ • deletedCutTensor A S s v (label s v.val a.succ) hd j x =
      Surjection.deletionCoefficient v.val (s.horizontal a.succ) •
        (eqToHom (congrArg (fun z : ℤ => (power (chains A S) r).X z) h)).hom
          (cutTerm A S ((BarrattEccles.horizontalInsertionEquiv m q a).symm ⟨s, ha⟩) w x)
```

### 128.1 元の境界項への貼り合わせ

一覧：済み 8／全体 48（うち追加 4）

C193–C194も既存構成の次数移送・貼り合わせの法則。C193は既存`Surjection.Word.arity_le_length`と整数計算だけ。
C194はC192とC164を合わせ、正の出力次数`hd`を明示した内部面について元の境界項を照合する。
水平の端点・無効な削除語・零出力次数の扱いはなお残り、全hcの完了とは扱わない。

```lean
lemma horizontalDeletion_degree_eq {m q r : ℕ} (w : Surjection.Word r (m + 1)) :
    -((m + q + 1 - r : ℕ) : ℤ) = -((m + 1 + q + 1 - r : ℕ) : ℤ) + 1

lemma outputBoundaryTerm_horizontalDeletion {m q r : ℕ} (S : SSet.{0})
    (s : Cut (m + 1) q) (v : Surjection.Word r (m + 2))
    (a b : Fin (m + 1 + q)) (hab : b.val = a.val + 1) (ha : a ∈ s.val) (hb : b ∈ s.val)
    (w : Surjection.Word r (m + 1))
    (hw : w.val = Surjection.erase v.val (s.horizontal a.succ))
    (hd : 0 < outputDegree s v (label s v.val a.succ))
    (j : Fin (outputDegree s v (label s v.val a.succ) + 1))
    (hj : j.val = vertexRank s v.val (label s v.val a.succ) a.succ) (x : S _⦋q⦌) :
    outputBoundaryTerm A S s v (label s v.val a.succ) j x =
      Surjection.deletionCoefficient v.val (s.horizontal a.succ) •
        (eqToHom (congrArg (fun z : ℤ => (power (chains A S) r).X z)
          (horizontalDeletion_degree_eq (q := q) w))).hom
          (cutTerm A S ((BarrattEccles.horizontalInsertionEquiv m q a).symm ⟨s, ha⟩) w x)
```

### 128.2 正次数の前提の供給

一覧：済み 8／全体 48（うち追加 4）

C195はC150の削除リストの長さとC149の既存の長さの式から従う算術の法則。
C196はC190・C194・C195の貼り合わせで、出力の正次数を外部の仮定として残さない。
無効な削除語と端点はなお別の残作業。いずれも200行以内。

```lean
lemma outputDegree_pos_of_deleted_vertexLists {m n q r : ℕ} (s : Cut m q) (t : Cut n q)
    (v : Surjection.Word r (m + 1)) (w : Surjection.Word r (n + 1))
    (k : Fin (m + q + 1))
    (hl : ∀ c, deletedVerticesList s v.val k c = verticesList t w.val c) :
    0 < outputDegree s v (label s v.val k)

lemma outputBoundaryTerm_horizontalDeletion_valid {m q r : ℕ} (S : SSet.{0})
    (s : Cut (m + 1) q) (v : Surjection.Word r (m + 2))
    (a b : Fin (m + 1 + q)) (hab : b.val = a.val + 1) (ha : a ∈ s.val) (hb : b ∈ s.val)
    (w : Surjection.Word r (m + 1))
    (hw : w.val = Surjection.erase v.val (s.horizontal a.succ))
    (j : Fin (outputDegree s v (label s v.val a.succ) + 1))
    (hj : j.val = vertexRank s v.val (label s v.val a.succ) a.succ) (x : S _⦋q⦌) :
    outputBoundaryTerm A S s v (label s v.val a.succ) j x =
      Surjection.deletionCoefficient v.val (s.horizontal a.succ) •
        (eqToHom (congrArg (fun z : ℤ => (power (chains A S) r).X z)
          (horizontalDeletion_degree_eq (q := q) w))).hom
          (cutTerm A S ((BarrattEccles.horizontalInsertionEquiv m q a).symm ⟨s, ha⟩) w x)
```

### 128.3 検証と取り込み候補

一覧：済み 8／全体 48（うち追加 4）

次の3モジュール、計166行を対象ビルドと小さい監査で検証した。
接頭部は`SerrePositivity.EInfinity.SimplexCuts.`。共通入口・共通監査には触っていない。

- `HorizontalDeletedTensors`：69行（C190–C192）。
- `HorizontalBoundaryTerms`：48行（C193–C194）。
- `HorizontalValidTerms`：49行（C195–C196）。

最終対象ビルドは`/tmp/bsw16/m14-horizontal-valid-terms-02.log`、
**2,271 jobs成功・警告0**。最初の型検査でC194の次数等式の引数の省略が解決されず、
既に証明済みのC193を明示して修正した。次のビルドで出た`if_pos`の非推奨警告は
`ite_eq_left`へ直し、最終ビルドで解消を確認した。
監査は別の一回の鍵で`/tmp/bsw16/audit-m14-horizontal-valid-terms.lean`を実行し、
**3モジュール・10宣言・標準三公理のみ**で成功（`m14-horizontal-valid-terms-audit.log`）。
先の一モジュール監査では内部に生成された補助も含め4宣言を確認し、
最後は上の3モジュールすべてを明示して改めて監査した。
各ビルド・監査で整理券は一枚、鍵は実行中だけで、終了と返却を確認した。
sorry・追加公理0、`git diff --check`成功。

§127の82行と合わせ、B4後の追加は248行。L09a・L09累計 **5,843行**、
改訂MayのM14全体 **10,909行**。次のL09a・L09の1,000行区切りは約6,600行、
M14半分の12,500行と外枠25,000行には未到達。

有効な削除語を持つ内部水平面について、正次数の仮定を供給した上で元の境界項を
小さい切断の指定項へ接続した。等式は元の加群のもので、ホモトピー圏へ弱めていない。
残りは水平の両端・無効な削除語の零・全添字の貼り合わせ、垂直hvと全相殺。
L09a・L09全体を閉じたとは扱わず、§121・§123.5の規模リスクも据え置く。

B4取り込み点は595254e10の106本のまま。B4後の新規4モジュールは§127・§128に
別途登録候補を記したので、B4の106本の監査に含まれるとは扱わない。

## 129. 水平な両端の指定座標を共通の比較へ移す（11-14）

一覧：済み 8／全体 48（うち追加 4）

前ターンはB4と内部面の実境界項を検証・コミットした進捗。B4後の作業木から続行。
ここでは既存の`ShuffleFirstFace`・`ShuffleLastFace`の水平削除の座標公式を使う。
新たな作用や定理を導入せず、既存C173の右端の特徴付けと削除列の定義への貼り合わせを行う。
両端の座標・hi・削除列は、先にPythonでm,q=0〜3、3色の任意の語について
**20,862例**を確認した（`/tmp/bsw16/check-horizontal-endpoint-transport.py`）。

### 129.1 指定座標からの移送法則（C197・C198）

C197は既存C174の証明を、既に供給された水平・垂直座標に依存する形で使う。
局所型は`hne : j ≠ k`と、Fin.cast二回が元の`l`へ戻る等式`hc`。
C198は同じ二座標を削除列の定義へ写すだけ。両方200行以内。

```lean
lemma hi_eq_of_horizontal_deleted_coordinates {m q : ℕ} (s : Cut (m + 1) q) (t : Cut m q)
    (k : Fin (m + 1 + q + 1)) (a : Fin (m + 2)) (hk : s.horizontal k = a)
    (hh : ∀ j : Fin (m + q + 1),
      s.horizontal (k.succAbove (Fin.cast (by omega : m + q + 1 = m + 1 + q) j)) =
        a.succAbove (t.horizontal j))
    (hv : ∀ j : Fin (m + q + 1),
      s.vertical (k.succAbove (Fin.cast (by omega : m + q + 1 = m + 1 + q) j)) = t.vertical j)
    (i : Fin (m + 1)) : hi t i = hi s (a.succAbove i)

lemma deletedTrace_eq_of_horizontal_coordinates {m q r : ℕ} (s : Cut (m + 1) q) (t : Cut m q)
    (v : Fin (m + 2) → Fin r) (k : Fin (m + 1 + q + 1)) (a : Fin (m + 2))
    (hh : ∀ j : Fin (m + q + 1),
      s.horizontal (k.succAbove (Fin.cast (by omega : m + q + 1 = m + 1 + q) j)) =
        a.succAbove (t.horizontal j))
    (hv : ∀ j : Fin (m + q + 1),
      s.vertical (k.succAbove (Fin.cast (by omega : m + q + 1 = m + 1 + q) j)) = t.vertical j) :
    deletedTrace s v k = List.ofFn (fun j : Fin (m + q + 1) =>
      (Surjection.erase v a (t.horizontal j), t.vertical j))
```

### 129.2 同じ境界項の貼り合わせと両端（C199–C201）

一覧：済み 8／全体 48（うち追加 4）

C199はC183の符号・C189の実テンソル・C195の正次数へ、C197・C198の指定座標を供給する法則。
C200・C201は既存の始端・終端の座標公式を代入する。同じ二つの構成の照合で、
作用の新しい法則やホモトピーを作らない。個々の補題は200行以内。
局所の`hl`は全色の削除列の等式、`hd`は正次数、`hs`はC183の符号等式。
`hc`は二回のFin.castの消去、`hk`は末尾の辺の終点がFin.lastである等式、
`he`は末尾の辺の標準添字と指定`a`の等式、`hH`は既存の水平端点の判定である。

```lean
lemma outputBoundaryTerm_horizontal_of_coordinates {m q r : ℕ} (S : SSet.{0})
    (s : Cut (m + 1) q) (t : Cut m q)
    (v : Surjection.Word r (m + 2)) (w : Surjection.Word r (m + 1))
    (k : Fin (m + 1 + q + 1)) (a : Fin (m + 2)) (hk : s.horizontal k = a)
    (hsingle : ∀ l, s.horizontal l = a → l = k)
    (hw : w.val = Surjection.erase v.val a)
    (hh : ∀ l : Fin (m + q + 1),
      s.horizontal (k.succAbove (Fin.cast (by omega : m + q + 1 = m + 1 + q) l)) =
        a.succAbove (t.horizontal l))
    (hv : ∀ l : Fin (m + q + 1),
      s.vertical (k.succAbove (Fin.cast (by omega : m + q + 1 = m + 1 + q) l)) = t.vertical l)
    (j : Fin (outputDegree s v (label s v.val k) + 1))
    (hj : j.val = vertexRank s v.val (label s v.val k) k) (x : S _⦋q⦌) :
    outputBoundaryTerm A S s v (label s v.val k) j x =
      Surjection.deletionCoefficient v.val a •
        (eqToHom (congrArg (fun z : ℤ => (power (chains A S) r).X z)
          (horizontalDeletion_degree_eq (q := q) w))).hom (cutTerm A S t w x)

lemma outputBoundaryTerm_horizontal_first {m q r : ℕ} (S : SSet.{0})
    (s : Cut (m + 1) q) (h₀ : (0 : Fin (m + 1 + q)) ∈ s.val)
    (v : Surjection.Word r (m + 2)) (w : Surjection.Word r (m + 1))
    (hw : w.val = Surjection.erase v.val 0)
    (j : Fin (outputDegree s v (label s v.val 0) + 1))
    (hj : j.val = vertexRank s v.val (label s v.val 0) 0) (x : S _⦋q⦌) :
    outputBoundaryTerm A S s v (label s v.val 0) j x =
      Surjection.deletionCoefficient v.val 0 •
        (eqToHom (congrArg (fun z : ℤ => (power (chains A S) r).X z)
          (horizontalDeletion_degree_eq (q := q) w))).hom
          (cutTerm A S ((BarrattEccles.horizontalInsertionEquiv m q 0).symm ⟨s, h₀⟩) w x)

lemma outputBoundaryTerm_horizontal_last {m q r : ℕ} (S : SSet.{0})
    (s : Cut (m + 1) q) (a : Fin (m + 1 + q)) (ha : a ∈ s.val)
    (hlast : a.val + 1 = m + 1 + q)
    (v : Surjection.Word r (m + 2)) (w : Surjection.Word r (m + 1))
    (hw : w.val = Surjection.erase v.val (Fin.last (m + 1)))
    (j : Fin (outputDegree s v (label s v.val (Fin.last (m + 1 + q))) + 1))
    (hj : j.val = vertexRank s v.val (label s v.val (Fin.last (m + 1 + q)))
      (Fin.last (m + 1 + q))) (x : S _⦋q⦌) :
    outputBoundaryTerm A S s v (label s v.val (Fin.last (m + 1 + q))) j x =
      Surjection.deletionCoefficient v.val (Fin.last (m + 1)) •
        (eqToHom (congrArg (fun z : ℤ => (power (chains A S) r).X z)
          (horizontalDeletion_degree_eq (q := q) w))).hom
          (cutTerm A S ((BarrattEccles.horizontalInsertionEquiv m q a).symm ⟨s, ha⟩) w x)
```

### 129.3 削除しない因子の正規化による消滅（C202–C204）

一覧：済み 8／全体 48（うち追加 4）

既存構成の法則の証明分割。C202は既存`faces_mono_iff`の順方向を一色だけに制限し、
同じfiberの順序同型の逆で二頂点を読む。C203は既存`gen_map_of_not_mono`と
`tensorValue_eq_zero`を、`deletedCutTensor`の削除しない因子に適用。C204は符号を戻す。
新しい非退化性の定理や作用を仮定せず、既存の消滅をそのまま使用する。各補題200行以内。
局所型は色のfiberへの所属`hci`・`hcj`、同じ順序同型の逆の評価`hei`・`hej`、
元の面の値の等式`hval`と単射性からの添字の等式`heq`（既存`faces_mono_iff`と同型の分割）。

```lean
lemma face_not_mono_of_repeated_color {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (c : Fin r) (i j : Fin (m + q + 1))
    (hi : label s v.val i = c) (hj : label s v.val j = c)
    (hne : i ≠ j) (hv : s.vertical i = s.vertical j) : ¬Mono (face s v c)

lemma deletedCutTensor_eq_zero_of_other_face {m q r : ℕ} (S : SSet.{0}) (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (a : Fin r) (ha : 0 < outputDegree s v a)
    (j : Fin (outputDegree s v a + 1)) (c : Fin r) (hc : c ≠ a)
    (hm : ¬Mono (face s v c)) (x : S _⦋q⦌) :
    deletedCutTensor A S s v a ha j x = 0

lemma outputBoundaryTerm_eq_zero_of_other_face {m q r : ℕ} (S : SSet.{0}) (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (a : Fin r) (j : Fin (outputDegree s v a + 1))
    (c : Fin r) (hc : c ≠ a) (hm : ¬Mono (face s v c)) (x : S _⦋q⦌) :
    outputBoundaryTerm A S s v a j x = 0
```

### 129.4 非全射な削除語の零（C205・C206）

一覧：済み 8／全体 48（うち追加 4）

L09a内の有限なfiberの計算。先にPythonでm=1〜4、q=0〜3、arity=1〜3の全非退化全射語を
点検し、非全射な削除の次数零 **2,616例**、退化な削除の別の色の重複 **2,440例**で一致を確認した
（`/tmp/bsw16/check-horizontal-invalid-deletions.py`）。
まず前者を既存`Surjection.erase_surjective_iff`とC56の水平fiberの特徴付けへ戻す。
C205の局所型`hu : ∀ i, v.val i = v.val (s.horizontal k) → i = s.horizontal k`、
`hc : colorPositions s v.val (label s v.val k) = {k}`。C206は次数零の定義への貼り合わせ。
各補題200行以内。後者の退化な削除への適用はまだ閉じたとは数えない。

```lean
lemma outputDegree_zero_horizontal_of_not_surjective {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (k : Fin (m + q + 1)) (hk : HorizontalVertex s k)
    (hns : ¬Function.Surjective (Surjection.erase v.val (s.horizontal k))) :
    outputDegree s v (label s v.val k) = 0

lemma outputBoundaryTerm_horizontal_not_surjective {m q r : ℕ} (S : SSet.{0}) (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (k : Fin (m + q + 1)) (hk : HorizontalVertex s k)
    (hns : ¬Function.Surjective (Surjection.erase v.val (s.horizontal k)))
    (j : Fin (outputDegree s v (label s v.val k) + 1)) (x : S _⦋q⦌) :
    outputBoundaryTerm A S s v (label s v.val k) j x = 0
```

### 129.5 退化した削除の元の二位置（C207）

一覧：済み 8／全体 48（うち追加 4）

上の2,440例の点検で使った有限な位置の計算をLeanにする。
非退化な語で新しく隣接同色が生じるのは、消した位置をちょうど挟むときだけ。
既存`Surjection.succAbove_val_eq`の二分岐と元の語の隣接非退化性を使う。
局所型は削除後の隣接同色対`hij`・`he`、元での隣接の否定`hskip`、
`hleft : i.val + 1 = a.val ∧ j.val = a.val`。200行以内。

```lean
lemma erased_word_degenerate_neighbors {m r : ℕ} (v : Surjection.Word r (m + 2))
    (a : Fin (m + 2)) (h : ¬Surjection.Nondegenerate (Surjection.erase v.val a)) :
    ∃ i j : Fin (m + 2), i.val + 1 = a.val ∧ a.val + 1 = j.val ∧ v.val i = v.val j
```

### 129.6 残る同色の二頂点と、無効な削除全体の零（C208–C210）

一覧：済み 8／全体 48（うち追加 4）

C208は上の2,440例で先に点検した有限な水平隣接辺の計算。
C207から元の区間の両隣`i,j`を取り、水平座標の端点の公式により`0 < k.val < m+1+q`。
その前後の辺`l,e`を読む既存`step_of_mem`で、削除しない別の色の同じ頂点を二つ得る。
C202へ適用するだけで、BEの新しい作用・operad法則を導入しない。
C209は既存の正規化の消滅C204への貼り合わせ、C210は非全射と退化の二場合の貼り合わせ。
個々の補題200行以内。局所型は内部性`hk0`・`hkN`、辺の終始点`hl : l.succ=k`・
`he : e.castSucc=k`、水平座標の一致`hi : s.horizontal l.castSucc=i`・
`hj : s.horizontal e.succ=j`、異なる二頂点`hne : l.castSucc ≠ e.succ`。

```lean
lemma other_face_not_mono_horizontal_degenerate {m q r : ℕ} (s : Cut (m + 1) q)
    (v : Surjection.Word r (m + 2)) (k : Fin (m + 1 + q + 1)) (hk : HorizontalVertex s k)
    (hdeg : ¬Surjection.Nondegenerate (Surjection.erase v.val (s.horizontal k))) :
    ∃ c : Fin r, c ≠ label s v.val k ∧ ¬Mono (face s v c)

lemma outputBoundaryTerm_horizontal_degenerate {m q r : ℕ} (S : SSet.{0}) (s : Cut (m + 1) q)
    (v : Surjection.Word r (m + 2)) (k : Fin (m + 1 + q + 1)) (hk : HorizontalVertex s k)
    (hdeg : ¬Surjection.Nondegenerate (Surjection.erase v.val (s.horizontal k)))
    (j : Fin (outputDegree s v (label s v.val k) + 1)) (x : S _⦋q⦌) :
    outputBoundaryTerm A S s v (label s v.val k) j x = 0

lemma outputBoundaryTerm_horizontal_invalid {m q r : ℕ} (S : SSet.{0}) (s : Cut (m + 1) q)
    (v : Surjection.Word r (m + 2)) (k : Fin (m + 1 + q + 1)) (hk : HorizontalVertex s k)
    (hinvalid : ¬(Function.Surjective (Surjection.erase v.val (s.horizontal k)) ∧
      Surjection.Nondegenerate (Surjection.erase v.val (s.horizontal k))))
    (j : Fin (outputDegree s v (label s v.val k) + 1)) (x : S _⦋q⦌) :
    outputBoundaryTerm A S s v (label s v.val k) j x = 0
```

### 129.7 検証・実測と次の接続

一覧：済み 8／全体 48（うち追加 4）

今回の新規6モジュールは、対象ビルドと専用の小さい監査で検証した。
登録候補の接頭部は`SerrePositivity.EInfinity.SimplexCuts.`。

| モジュール | 実測 | 内容 |
| --- | ---: | --- |
| `HorizontalDeletionCoordinates` | 61行 | 指定座標から右端・削除列への移送 |
| `HorizontalEndpointTerms` | 127行 | 同じ実境界項の比較と水平な両端 |
| `OtherFaceZeroTerms` | 66行 | 削除しない色の非単射な面による正規化の消滅 |
| `NonSurjectiveZeroTerms` | 53行 | 非全射な削除で次数零・元の境界項零 |
| `DegenerateDeletionNeighbors` | 35行 | 退化した削除の元の両隣の二位置 |
| `DegenerateHorizontalTerms` | 96行 | 別の色の重複から退化な削除・無効な削除の境界項零 |
| **合計** | **438行** | |

最終対象ビルドは`/tmp/bsw16/m14-horizontal-invalid-terms-03.log`、
**2,288 jobs成功・Lean警告0**。
初期の型検査では、端点判定の明示import、letの展開、存在命題の表示、
Fin.zero・Fin.lastの値を算術へ明示する処理を修正した。
余分な`rfl`・非推奨名・100字を超える行も直した。
主張の型を弱めたり、非単射性やテンソルの消滅を未証明の前提に足したりしていない。

別の一回の鍵で`/tmp/bsw16/audit-m14-horizontal-endpoint-invalid.lean`を実行し、
**6モジュール・59宣言・標準三公理のみ**で成功した
（`/tmp/bsw16/m14-horizontal-endpoint-invalid-audit.log`）。
全6モジュールを明示し、各モジュールの宣言数が0でないことも検査した。
新規本体のsorry・追加公理0、`git diff --check`成功。
共通入口・共通監査の登録、rootビルドは調整役の持ち分として実行していない。
各実行は`--class impl --wait 3600`、整理券は一枚、
ビルドまたは監査の終了後に鍵を返却し、待ち時間・編集・報告中には鍵を持っていない。

L09a・L09累計 **6,281行**、改訂MayのM14全体 **11,347行**。
次の1,000行区切りは約6,600行、M14の半分報告は12,500行、外枠は25,000行のまま。
§121・§123.5の完成見込みと上端超過のリスクを、今回の局所的な完了で縮小した扱いにはしない。

これで有効な水平削除の内部・始端・終端の元の実境界項、および非全射・隣接退化による
無効な水平削除の元の境界項零がそろった。すべて元の加群の等式である。
次は既存`horizontalBoundaryFaceEquiv`／`horizontalBoundaryAllEquiv`の
指定された語の位置・小さい切断との照合を行い、実際の全水平添字のhcへ接続する。
垂直hv、全相殺とL09a・L09全体は未完。G10や他レーンのファイルには触っていない。

## 130. 全水平添字の同値との厳密な照合（11-14）

一覧：済み 8／全体 48（うち追加 4）

前ターンは§129の6モジュールを検証・コミットした進捗。作業木がクリーンであることを確認して続行。
B4は完了済み。新しい数学や別の同値を作らず、既存C70・C71が選ぶ文字位置と切断を読む。
先にm=0〜5、q=0〜4の全切断・係数位置について、三分割の逆、対応する水平座標、
指定削除で元の切断が復元されることをPythonで **2,771例** 点検した
（`/tmp/bsw16/check-horizontal-index-transport.py`）。

### 130.1 三つの枝での指定添字の評価（C211–C216）

既存の構成の合成・逆の法則と有限の添字の計算。各補題200行以内。
内部の文字位置は`i.castSucc.succ`、両端は0と`Fin.last (m+1)`で、元の添字を保持する。

```lean
lemma coefficientIndexEndpointEquiv_symm_first (m q : ℕ) (t : Cut m q) :
    (coefficientIndexEndpointEquiv m q).symm (.inl t) = (0, t)

lemma coefficientIndexEndpointEquiv_symm_interior (m q : ℕ) (t : Cut m q) (i : Fin m) :
    (coefficientIndexEndpointEquiv m q).symm (.inr (.inl (t, i))) = (i.castSucc.succ, t)

lemma coefficientIndexEndpointEquiv_symm_last (m q : ℕ) (t : Cut m q) :
    (coefficientIndexEndpointEquiv m q).symm (.inr (.inr t)) = (Fin.last (m + 1), t)

lemma horizontalBoundaryFaceEquiv_first (m q : ℕ) (t : Cut m q) :
    (horizontalBoundaryFaceEquiv m q (0, t)).val = (horizontalFirstFaceEquiv m q t).val

lemma horizontalBoundaryFaceEquiv_interior (m q : ℕ) (t : Cut m q) (i : Fin m) :
    (horizontalBoundaryFaceEquiv m q (i.castSucc.succ, t)).val =
      (horizontalInteriorFaceEquiv m q (t, i)).val

lemma horizontalBoundaryFaceEquiv_last (m q : ℕ) (t : Cut m q) :
    (horizontalBoundaryFaceEquiv m q (Fin.last (m + 1), t)).val =
      (horizontalLastFaceEquiv m q t).val
```

### 130.2 元の文字位置の保存（C217・C218）

一覧：済み 8／全体 48（うち追加 4）

点検済みの有限な座標の計算と、既存の同値の法則。
C217は`horizontalCornerEquiv_horizontal`と`horizontalMarkedEdgeEquiv_horizontal`の合成。
C218は同じ既存の三分割の逆で三場合に分け、C214–C217と水平座標の端点の式を使う。
個々の補題200行以内。

```lean
lemma horizontalInteriorFaceEquiv_horizontal (m q : ℕ) (t : Cut m q) (i : Fin m) :
    (horizontalInteriorFaceEquiv m q (t, i)).val.1.horizontal
      (horizontalInteriorFaceEquiv m q (t, i)).val.2 = i.castSucc.succ

lemma horizontalBoundaryFaceEquiv_horizontal (m q : ℕ) (c : Fin (m + 2) × Cut m q) :
    (horizontalBoundaryFaceEquiv m q c).val.1.horizontal
      (horizontalBoundaryFaceEquiv m q c).val.2 = c.1
```

### 130.3 指定された全水平添字での実項の照合（C219・C220）

一覧：済み 8／全体 48（うち追加 4）

C219は既存の構成の貼り合わせの法則。C211–C216で同じ三分割に分け、
C200・C196・C201を適用し、指定挿入の`Equiv.symm_apply_apply`で元の小さい切断へ戻す。
C220はC218の文字位置の一致とC210の無効削除の消滅の貼り合わせ。
どちらも元の加群の等式で、実際の小さい切断`c.2`と削除位置`c.1`を保持する。
各補題200行以内。C219の局所型は挿入辺の所属`ha`・`hb`、
`hh : (e t).val.horizontal a.succ = i.castSucc.succ`と
`hw' : w.val = Surjection.erase v.val ((e t).val.horizontal a.succ)`。

```lean
lemma outputBoundaryTerm_horizontalBoundaryFaceEquiv_valid {m q r : ℕ} (S : SSet.{0})
    (v : Surjection.Word r (m + 2)) (w : Surjection.Word r (m + 1)) :
    ∀ (c : Fin (m + 2) × Cut m q) (_hw : w.val = Surjection.erase v.val c.1)
      (j : Fin (outputDegree (horizontalBoundaryFaceEquiv m q c).val.1 v
        (label (horizontalBoundaryFaceEquiv m q c).val.1 v.val
          (horizontalBoundaryFaceEquiv m q c).val.2) + 1))
      (_hj : j.val = vertexRank (horizontalBoundaryFaceEquiv m q c).val.1 v.val
        (label (horizontalBoundaryFaceEquiv m q c).val.1 v.val
          (horizontalBoundaryFaceEquiv m q c).val.2) (horizontalBoundaryFaceEquiv m q c).val.2)
      (x : S _⦋q⦌),
    outputBoundaryTerm A S (horizontalBoundaryFaceEquiv m q c).val.1 v
        (label (horizontalBoundaryFaceEquiv m q c).val.1 v.val
          (horizontalBoundaryFaceEquiv m q c).val.2) j x =
      Surjection.deletionCoefficient v.val c.1 •
        (eqToHom (congrArg (fun z : ℤ => (power (chains A S) r).X z)
          (horizontalDeletion_degree_eq (q := q) w))).hom (cutTerm A S c.2 w x)

lemma outputBoundaryTerm_horizontalBoundaryFaceEquiv_invalid {m q r : ℕ} (S : SSet.{0})
    (v : Surjection.Word r (m + 2)) (c : Fin (m + 2) × Cut m q)
    (hinvalid : ¬(Function.Surjective (Surjection.erase v.val c.1) ∧
      Surjection.Nondegenerate (Surjection.erase v.val c.1)))
    (j : Fin (outputDegree (horizontalBoundaryFaceEquiv m q c).val.1 v
      (label (horizontalBoundaryFaceEquiv m q c).val.1 v.val
        (horizontalBoundaryFaceEquiv m q c).val.2) + 1)) (x : S _⦋q⦌) :
    outputBoundaryTerm A S (horizontalBoundaryFaceEquiv m q c).val.1 v
      (label (horizontalBoundaryFaceEquiv m q c).val.1 v.val
        (horizontalBoundaryFaceEquiv m q c).val.2) j x = 0
```

### 130.4 元の係数境界値との次数移送（C221–C224）

一覧：済み 8／全体 48（うち追加 4）

既存構成の係数移送・貼り合わせの法則。C221・C222は同じ実境界項を読む定義の照合。
C223はC219・C220を元の全境界値の共通次数へ運び、定義の負号と相殺する。
C224の係数次数零の場合は、削除語の長さがarityより小さいため全射が存在しないことを
既存`Fintype.card_le_of_surjective`から読み、C220へ戻す。新しい非退化性の仮定は足さない。
C223の局所型`ho`・`hc`は書かれている二つの整数次数の等式、
`step {M N P : ModuleCat A} (hMN : M = N) (hNP : N = P) (y : M) :
(eqToHom hNP).hom ((eqToHom hMN).hom y) = (eqToHom (hMN.trans hNP)).hom y`は
§127の同じ移送の合成則。C224の`hns`は削除語の全射性・非退化性の連言の否定。
各補題200行以内。未検証の段階ではhcの完了とは数えない。

```lean
lemma coefficientBoundaryTerm_succ_eq {r d q : ℕ} (S : SSet.{0})
    (u : Surjection.BasisWord (r + 1) (d + 1)) (c : Fin (r + d + 2) × Cut (r + d) q)
    (x : S _⦋q⦌)
    (h : -((r + d + q + 1 - (r + 1) : ℕ) : ℤ) = -(((d + 1) + q : ℕ) : ℤ) + 1) :
    coefficientBoundaryTerm A S r (d + 1) q u c x =
      if hw : Function.Surjective (Surjection.erase (positiveWord u).val c.1) ∧
          Surjection.Nondegenerate (Surjection.erase (positiveWord u).val c.1) then
        -Surjection.deletionCoefficient (positiveWord u).val c.1 •
          (eqToHom (congrArg (fun z : ℤ => (power (chains A S) (r + 1)).X z) h)).hom
            (cutTerm A S c.2 ⟨Surjection.erase (positiveWord u).val c.1, hw⟩ x)
      else 0

lemma universalBoundaryValue_coefficient (S : SSet.{0}) {r d : ℕ}
    (u : Surjection.BasisWord (r + 1) d) (q : ℕ) (x : S _⦋q⦌)
    (c : Fin (r + d + 1) × Cut (r + d - 1) q) :
    universalBoundaryValue A S u q x (.inr (.inl c)) = coefficientBoundaryTerm A S r d q u c x

lemma universalBoundaryValue_horizontal_succ (S : SSet.{0}) {r d : ℕ}
    (u : Surjection.BasisWord (r + 1) (d + 1)) (q : ℕ) (x : S _⦋q⦌)
    (c : Fin (r + d + 2) × Cut (r + d) q) :
    universalBoundaryValue A S u q x (.inl (horizontalBoundaryFaceEquiv (r + d) q c).val) =
      -universalBoundaryValue A S u q x (.inr (.inl c))

lemma universalBoundaryValue_horizontal_neg (S : SSet.{0}) {r d : ℕ}
    (u : Surjection.BasisWord (r + 1) d) (q : ℕ) (x : S _⦋q⦌) (hm : 0 < r + d)
    (c : Fin (r + d + 1) × Cut (r + d - 1) q) :
    universalBoundaryValue A S u q x (.inl ((horizontalBoundaryAllEquiv (r + d) q hm) c).val) =
      -universalBoundaryValue A S u q x (.inr (.inl c))
```

### 130.5 依存する面番号を保つ証明分割

一覧：済み 8／全体 48（うち追加 4）

C219の最初の型検査では、面番号`j`に依存する型の中を部分的にsimpして、
元の同値の値が残った。証明の分割として、次の同じ述語`P`を局所的に置き、
指定頂点を丸ごと書き換えてから面番号を導入する。主張の型・比較する射・前提は変更しない。

```lean
  let P (z : MarkedCut (m + 1) q) (a : Fin (m + 2)) (t : Cut m q) : Prop :=
    ∀ (_hw : w.val = Surjection.erase v.val a)
      (j : Fin (outputDegree z.1 v (label z.1 v.val z.2) + 1))
      (_hj : j.val = vertexRank z.1 v.val (label z.1 v.val z.2) z.2) (x : S _⦋q⦌),
      outputBoundaryTerm A S z.1 v (label z.1 v.val z.2) j x =
        Surjection.deletionCoefficient v.val a •
          (eqToHom (congrArg (fun n : ℤ => (power (chains A S) r).X n)
            (horizontalDeletion_degree_eq (q := q) w))).hom (cutTerm A S t w x)
```

C219の同じ指定切断への戻りは、局所型
`hsmall : e.symm ⟨(e t).val, (e t).property⟩ = t`（内部では所属証明`ha`）を
既存`e.symm_apply_apply t`から明示し、元の等式で書き換える。新しい照合の仮定ではない。

待ち時間には垂直分岐の有限計算も先に点検した。
`/tmp/bsw16/check-vertical-position-signs.py`、**14,942例**で、
C170の接頭順位、位置指数の差が削除区間以後のcaesura数になること、
同色の直前の面の削除係数と実境界符号の一致を確認した。
垂直の新しいLeanはまだ書かず、水平hcの検証を先にする。この点検を垂直hvの証明済み扱いにはしない。

C223・C224の全出力値への移送では、C168で読む`⟨z.val.1,z.val.2⟩`と
元の指定頂点`z.val`を既存`Sigma.eta`で明示的に照合する。
局所型`hout`はC168の等式の左辺をその同じ指定頂点へ戻したもので、
新しい射・仮定・自然性の選択を加えない。

C223では、同じ実境界項の等式`ht`を、指定された共通次数への線形射に
`congrArg`で写した`ht'`として使う。型はC219またはC220の両辺に
`(eqToHom (congrArg (fun n : ℤ => (power (chains A S) (r+1)).X n) ho)).hom`
を適用した等式そのもので、`map_zsmul`・`map_zero`と上の`step`だけを使う。
依存した引数内へのrwの照合に頼らず、既存の係数移送の法則を明示する分割である。

C223の詳細型の比較では、`r+(d+1)`と`(r+d)+1`が式内部に異なる形で残っていた。
`Nat.add_assoc`で同じ正規形へそろえ、上の移送の合成則を適用する。
一時的なppオプションは除去した。型クラス引数を明示した診断ログは
`/tmp/bsw16/m14-horizontal-boundary-values-diag.log`に保持する。

### 130.6 色と面番号の依存した組を保つ（C225）

一覧：済み 8／全体 48（うち追加 4）

より具体的な型検査で、逆同値の`.2`の型が`.1`に依存し、`.1=label`を
semireducibleな定義の展開だけで読むと、通常のimplicit透明性では型が合わないことを確認した。
加法の括弧をそろえるだけでは解消しなかった。C225は元の値を同じ依存した組のまま読む定義の法則。
既存公開宣言は変えず、新しい名前で足す。C223・C224では
`hp : (colorPositionEquiv z.val.1 v).symm z.val.2 = ⟨a,j⟩`で一度だけ分解し、
既存C22から`ha : a = label z.val.1 v.val z.val.2`を得て色を置き換える。
その後の`j`は正しい色のFinとして通常の透明性でも型が合う。
`hj : j.val = vertexRank z.val.1 v.val (label z.val.1 v.val z.val.2) z.val.2`は既存C28の順位の式から得る。
新しい構成や主張の弱化はなく、同じ出力値の評価の分割。C225は200行以内。

```lean
lemma universalBoundaryValue_output_paired (S : SSet.{0}) {r d : ℕ}
    (w : Surjection.BasisWord (r + 1) d) (q : ℕ) (x : S _⦋q⦌)
    (s : Cut (r + d) q) (k : Fin (r + d + q + 1))
    (h : -((r + d + q + 1 - (r + 1) : ℕ) : ℤ) + 1 = -((d + q : ℕ) : ℤ) + 1) :
    universalBoundaryValue A S w q x (.inl ⟨s, k⟩) =
      (eqToHom (congrArg (fun n : ℤ => (power (chains A S) (r + 1)).X n) h)).hom
        (outputBoundaryTerm A S s (positiveWord w)
          ((colorPositionEquiv s (positiveWord w)).symm k).1
          ((colorPositionEquiv s (positiveWord w)).symm k).2 x)
```

### 130.7 待ち時間の垂直の次の型案（紙のみ）

一覧：済み 8／全体 48（うち追加 4）

水平hcの検証待ちの間に、同じL09aの垂直の有限計算を整理した。
以下のC226–C229は**紙の型案で、Lean未実装・未検証**。
新しい数学のまとまりではなく、既存の垂直削除の座標・右端・位置指数の法則。
C229の位置差は非退化性・全射性を仮定しない任意の3色の関数についても
先に **76,407例** 点検した（`/tmp/bsw16/check-vertical-arbitrary-position.py`）。
これは既存C170の接頭順位と、削除後に残る区間の右端を使う経路を確認する点検であり、
Leanでの証明を代用しない。

```lean
-- C226：指定された垂直削除で、削除しない右端を垂直の順序単射で比較する。
hi_eq_of_vertical_deleted_coordinates {m q : ℕ} (s : Cut m (q + 1)) (t : Cut m q)
    (k : Fin (m + (q + 1) + 1))
    (hh : ∀ j : Fin (m + q + 1), s.horizontal (k.succAbove j) = t.horizontal j)
    (hv : ∀ j : Fin (m + q + 1), s.vertical (k.succAbove j) =
      (s.vertical k).succAbove (t.vertical j))
    (i : Fin (m + 1))
    (hmax : (intervalPositions s i).max' (intervalPositions_nonempty s i) ≠ k) :
  hi s i = ((s.vertical k).succAbove ⟨hi t i, by have := hi_le_q t i; omega⟩).val

-- C227：垂直の削除頂点は、活動区間の右端ではない。
hi_vertex_ne_vertical_of_caesura {m q r : ℕ} (s : Cut m (q + 1))
    (v : Fin (m + 1) → Fin r) (k : Fin (m + (q + 1) + 1)) (hk : boundaryVertexKind s k = .vertical)
    (i : Fin (m + 1)) (hi : Surjection.Caesura v i) :
  (intervalPositions s i).max' (intervalPositions_nonempty s i) ≠ k

-- C228：入力の削除頂点以後にある右端は、その区間以後のものに限る。
vertical_vertex_le_hi_iff {m q : ℕ} (s : Cut m (q + 1))
    (k : Fin (m + (q + 1) + 1)) (hk : boundaryVertexKind s k = .vertical) (i : Fin (m + 1)) :
  (s.vertical k).val ≤ hi s i ↔ s.horizontal k ≤ i

-- C229：同じ語の位置指数の差は、削除区間以後のcaesuraの個数。
positionExponent_vertical_deleted_coordinates {m q r : ℕ}
    (s : Cut m (q + 1)) (t : Cut m q) (v : Fin (m + 1) → Fin r)
    (k : Fin (m + (q + 1) + 1)) (hk : boundaryVertexKind s k = .vertical)
    (hh : ∀ j : Fin (m + q + 1), s.horizontal (k.succAbove j) = t.horizontal j)
    (hv : ∀ j : Fin (m + q + 1), s.vertical (k.succAbove j) =
      (s.vertical k).succAbove (t.vertical j)) :
  positionExponent s v = positionExponent t v +
    ((caesuraPositions v).filter (fun i => s.horizontal k ≤ i)).card
```

C226は既存C173・C06と同じ右端の上下界の特徴付けを、
垂直座標の狭義単調な`Fin.succAbove`へ移す。C227は内部・始端の次の垂直辺と、
終端では元の最後の区間がcaesuraにならないことを使う有限な計算。
C228は既存の座標の単調性と直前の垂直辺、C229はこれらと`Fin.succAbove`の値の式を
既存`positionExponent_eq_caesura_sum`へ戻す。
全caesura数は既存`Surjection.Word.card_caesuras`／`Surjection.card_caesuras_basisWord`を使い、
同じ濃度の式を再証明しない。C170の接頭順位と合せて入力面の交代符号へ戻す。

### 130.8 待ち時間のC226のLean下書き

一覧：済み 8／全体 48（うち追加 4）

水平hcの検証順は維持し、待ち時間に紙のC226のみLeanの下書きを置いた。
C227–C229はまだ紙のまま。C226は検証前にはコミットしない。
右端の達成と上界の既存C06を使い、削除前の右端の逆像`j`と削除後の右端`jt`を比較する。
局所型`hji : t.horizontal j = i`、`hsmall : t.vertical j ≤ ⟨hi t i,⋯⟩`、
`hmon`は既存`Fin.strictMono_succAbove`による同じ上界の移送。

実装前の有限点検は`/tmp/bsw16/check-vertical-interval-maxima.py`、
**12,341例**で右端の移送、入力頂点以上の右端と区間番号の閾値の一致、
削除頂点自体が右端なら最後の頂点・最後の区間になることを確認した。
この点検はC226–C228の有限計算の確認であり、Leanの検証結果ではない。

C227・C228に使う隣接辺の証明分割も作業木へ下書きした（未検証、検証前にはコミットしない）。
既存C51–C53の始端・内部・終端の式を指定した辺へ戻すだけで、
垂直のための新しい構造や判定の定義は作らない。各補題200行以内。
有限点検は上の垂直頂点の全候補12,341例と、既存の全境界の対合6,070添字の点検で
用いた同じ前後の辺の条件。局所型`he0`・`helast`は指定終始点の0・Fin.lastとの等式、
`heq`・`hl`・`hr`は指定辺と既存の端点/角の辺番号との等式。

```lean
lemma vertical_kind_outgoing_not_mem {m q : ℕ} (s : Cut m q)
    (k : Fin (m + q + 1)) (hk : boundaryVertexKind s k = .vertical)
    (e : Fin (m + q)) (he : e.castSucc = k) : e ∉ s.val

lemma vertical_kind_incoming_not_mem {m q : ℕ} (s : Cut m q)
    (k : Fin (m + q + 1)) (hk : boundaryVertexKind s k = .vertical)
    (e : Fin (m + q)) (he : e.succ = k) : e ∉ s.val
```

C227も同じ検証待ちの間に下書きした。型は§130.7のまま、未検証。
既存の右端の達成から`hhi : s.horizontal k = i`。次の頂点がある場合は、
上の`vertical_kind_outgoing_not_mem`と既存`step_of_notMem`で同じ区間の次の頂点が得られ、
右端の最大性`hb : e.succ ≤ max' (intervalPositions s i) ⋯`に反する。
終端なら水平座標の端点の式から`i=Fin.last m`で、caesuraの定義に反する。
新しい構成を加えない有限の右端の計算。個々の補題200行以内。

C228も同じ待ち時間に、§130.7の型のまま下書きした（未検証）。
右端の頂点`j`の水平座標は`i`。`i < s.horizontal k`なら単調性で`j<k`となり、
直前の垂直辺の厳密な増分により`hi s i < (s.vertical k).val`。
逆に区間番号が指定区間以後なら、右端が`k`より前にあると同じ区間に`k`を含める
最大性に反する。局所型`hjk : j < k`、`hjle : j ≤ e.castSucc`、
`hm : (s.vertical j).val ≤ (s.vertical e.castSucc).val`、
`hkmem : k ∈ intervalPositions s i`。既存の順序と最大性だけの有限計算で、200行以内。

C229の位置指数の式も、§130.7の型のまま下書きした（未検証）。
局所型は
`hterm : ∀ i ∈ caesuraPositions v, hi s i = hi t i + if s.horizontal k ≤ i then 1 else 0`。
C226・C227の右端の式と既存`Surjection.succAbove_val_eq`、C228の閾値を合わせ、
既存`positionExponent_eq_caesura_sum`・`Finset.sum_add_distrib`・`Finset.sum_filter`へ戻す。
任意の語の位置指数の76,407例の点検は実装前に済ませてある。
200行以内で、同じ有限の分解と加法の法則。検証・監査前にはコミットしない。

### 130.9 依存した組の等式を全体の値へ写す法則

一覧：済み 8／全体 48（うち追加 4）

C225の評価は通ったが、組の等式の部分的なrwは通常の透明性で型を見失うため、
組全体を引数に取る同じ値の関数へ`congrArg`で写す法則を明示する。
新しい構成や仮定ではなく、同じ実境界値への等式の合成。200行以内。
垂直側ではC226・前後の辺の補題がビルド成功。C227・C228に必要な既存
`ShuffleStepMembership`のimportを明示し、同じ主張を再検証する。

```lean
lemma universalBoundaryValue_output_of_pair (S : SSet.{0}) {r d : ℕ}
    (w : Surjection.BasisWord (r + 1) d) (q : ℕ) (x : S _⦋q⦌)
    (s : Cut (r + d) q) (k : Fin (r + d + q + 1))
    (h : -((r + d + q + 1 - (r + 1) : ℕ) : ℤ) + 1 = -((d + q : ℕ) : ℤ) + 1)
    (ij : Σ a : Fin (r + 1), Fin (outputDegree s (positiveWord w) a + 1))
    (hp : (colorPositionEquiv s (positiveWord w)).symm k = ij) :
    universalBoundaryValue A S w q x (.inl ⟨s, k⟩) =
      (eqToHom (congrArg (fun n : ℤ => (power (chains A S) (r + 1)).X n) h)).hom
        (outputBoundaryTerm A S s (positiveWord w) ij.1 ij.2 x)
```

C226〜C228と隣接辺の補題は対象ビルドを通った。C229では`rw [Nat.add_zero]`が
暗黙の次元引数を抽象して型を崩すため、同じ算術の等式を`simpa only`で使う形に直す。
水平C223では、依存した組の評価を通した後、同じ移送の合成の照合が残るため、
新しいこのファイルの補助的なbackward/透明性オプションを外し、通常の設定で検証する。
主張・比較する射・公理の仮定は変更しない。

通常の透明性に戻したC223では移送の合成が通り、C229も対象ビルド成功。
最後のC223の値の照合で、追加していた`Nat.add_assoc`と局所名の展開を外し、
既に指定されている同じ次数・点・語のまま、負号と零だけを簡約して等式を使う。
垂直のC226–C229はここまで検証済みだが、専用監査前にはコミットしない。

C223の最後の値の型の診断では、局所名を除いた式の内部表現でも
`r+(d+1)`と`(r+d)+1`の差が残ることを確認した。一般の結合則の展開ではなく、
定義と同じ向きの既存`Nat.add_succ`だけで両方をそろえる。
一時的な`run_tac`の内部表現出力は除去し、本体には残さない。
診断の生データは`/tmp/bsw16/horizontal-actual-expr.txt`・
`horizontal-expected-expr.txt`に保持する。

### 130.10 水平hcのビルド成功

一覧：済み 8／全体 48（うち追加 4）

`universalBoundaryValue_horizontal_neg`が、係数次数零も含めて対象ビルドを通った。
最後の同じ値の照合は`convert ht' using 1`で合同を明示すると閉じ、
補助的に付けていた`rfl`は未使用なので除去した。
同じ元の加群での等式で、ホモトピー圏への弱化や未供給の数学的仮定はない。
同じ`universalBoundaryPartner_neg_of_cases`のhcをそのまま供給する。
垂直のC226〜C229もビルド済みだが、垂直hvの全体やL09a・L09の完了とは数えない。
この後は警告を除いた対象ビルドと全10モジュールの専用監査を行う。

### 130.11 検証・登録候補と約6,600行の区切りの確定

一覧：済み 8／全体 48（うち追加 4）

以下の10本、計 **663行** を対象ビルドと専用監査で検証した。
接頭部は`SerrePositivity.EInfinity.SimplexCuts.`。

| 登録候補 | 実測 |
| --- | ---: |
| `EndpointCoefficientIndices` | 67行 |
| `HorizontalFaceCoordinates` | 44行 |
| `HorizontalFaceTerms` | 108行 |
| `HorizontalBoundaryValues` | 131行 |
| `OutputBoundaryPairedValues` | 46行 |
| `VerticalDeletedMaxima` | 46行 |
| `VerticalVertexEdges` | 67行 |
| `VerticalActiveMaxima` | 47行 |
| `VerticalIntervalThresholds` | 53行 |
| `VerticalDeletionExponents` | 54行 |

最終対象ビルドは`/tmp/bsw16/m14-horizontal-vertical-final.log`、
`HorizontalBoundaryValues`・`VerticalDeletionExponents`の二対象で **2,320 jobs成功・警告0**。
両対象のimportで新規10本を覆う。
専用監査は別の一回の鍵で`/tmp/bsw16/audit-m14-horizontal-vertical-progress.lean`を実行し、
**10モジュール・54宣言・標準三公理のみ**で成功
（`/tmp/bsw16/m14-horizontal-vertical-audit.log`）。
全10モジュールを明示し、それぞれの宣言数が0でないことも確認した。
新規本体のsorry・追加公理0。`run_tac`や一時的なppの診断は本体に残っていない。
`git diff --check`成功。既存公開宣言・共通入口・共通監査・draftsは変更していない。
共通入口・共通監査への登録は調整役の担当のまま。

ビルド・監査はそれぞれ独立した一回の`--class impl --wait 3600`で実行。
整理券は常に一枚、待ち時間と編集・報告の間に鍵は持たず、各実行の終了と返却を確認した。

実際に閉じたもの：

- `universalBoundaryValue_horizontal_neg`：元の全水平添字のhcを、係数次数零も含め仮定なく供給。
  元の同じ加群・指定射での等式で、ホモトピー圏へ弱めていない。
- `positionExponent_vertical_deleted_coordinates`：C226〜C229の有限な幾何を合わせ、
  任意の語の位置指数の差を同じ語の末尾側のcaesura数へ戻す。
  実際の垂直の指定座標は既存C90と端点の公式から次に供給する。

L09a・L09の約6,600行の区切りは、§130の途中で下書き込みの実測を止まらず報告した。
その検証待ちの間に垂直の267行を進め、今回の検証済みの最終累計は
**L09a・L09 6,944行、改訂MayのM14全体12,010行**。
次は垂直の実際の削除係数と入力面の符号、指定面・生成元・実テンソル、全垂直添字のhv、
L09aの対合への包装とL09の微分の和への戻し。
L09a全体・L09はまだ閉じていないため、一覧の完了件数を増やさない。
M14の半分12,500行までは490行で、その時点でも止まらず途中報告する。
L09a・L09の次の1,000行区切りは約7,600行。

### 130.12 実測による残りと外枠の照合

一覧：済み 8／全体 48（うち追加 4）

§121の水平の600〜1,100行に対し、混合角の完了後の5,015行から
水平hcを閉じるまでの実測は **1,662行**（垂直に再利用する共通の順位・次数移送も含む）。
差は **+562〜+1,062行**。依存した面番号と指定された全添字の同値、
共通次数への実際の移送までの照合を含めた増分で、数学の主張の弱化はしていない。
垂直の267行はこの1,662行に重複計上しない。

垂直の残りの見込みは、位置指数が閉じた実測から次のように置く。

| 残りの部分 | 追加の見込み |
| --- | ---: |
| 元の削除係数・全caesura数を合わせた実符号 | 80〜150行 |
| 入力の面を合成した指定面・正規化生成元・実テンソル | 150〜280行 |
| 方向交換で指定された全垂直添字の座標と小さい切断への照合 | 90〜170行 |
| 元の入力境界値への包装とhv | 80〜150行 |
| **垂直の残り** | **400〜750行** |
| L09aの全対合・L09の微分の和への包装 | 200〜350行 |
| **L09a・L09の残り** | **600〜1,100行** |

垂直全体は今回までの267行を含め667〜1,017行の見込みで、
§121の500〜950行の上端より67行高い。指定射を省いた短縮は見込んでいない。
L09a・L09完成時の見込みは **7,544〜8,044行**。
L10以後の既存部分の再利用は§121.3・§121.4のまま、未実装部分を勝手に控除しない。

| M14の部分 | 実測／残り |
| --- | ---: |
| 完成済みMayと現在までの切断 | **12,010行（実測）** |
| L09a・L09の残り | 600〜1,100行 |
| L10〜L28（L12a込み） | 4,330〜7,790行 |
| L29〜L37の係数・ν・top operation | 1,200〜2,000行 |
| L38〜L40のG10後の指定比較への適用 | 500〜900行 |
| L41・L42のfiltered塔とA4の利用側 | 300〜550行 |
| L43a・L43b・L43・L44の二重模型の比較 | 1,500〜2,800行 |
| **残りの合計** | **8,430〜15,140行** |
| **M14完成時の見込み** | **20,440〜27,150行** |

上端は外枠25,000行より **2,150行高い**。外枠を変更した扱いにはせず、
同じ型一覧の中で続ける。旧coherent経路10,216行は保持し、改訂Mayに二重計上しない。
G10・③-bの橋そのもの、M15・G12のLeanは作っていない。

## 131. 垂直の実際の削除係数を入力符号へ接続する（11-14）

一覧：済み 8／全体 48（うち追加 4）

前ターンは水平hcと垂直C226〜C229を検証・コミットした進捗。
枝a1dabccd9とクリーンな作業木を確認して続行。M14実測12,010行、
12,500行の半分報告まで490行である。B4は完了済み。

### 131.1 同色の直前の位置と、両端を含む垂直頂点（C230〜C233）

同じL09aの有限計算と既存の削除係数の法則。実装前に
`/tmp/bsw16/check-adjacent-deletion-coefficients.py`で任意の語の隣接同色対を
**6,678例** 点検した。垂直頂点の係数の14,942例の点検も§130で先に済ませてある。
C230は直前の出現集合の最大が隣接位置になることと既存C135を使う。
C231は既存の垂直辺の判定、C232は既存C170の接頭順位、C233は既存の正次数の法則へ戻す。
新しい作用や構成は作らない。各補題200行以内。
局所型`hprev : previousVertex v b hp = a`、`hf`は既存の最終出現の削除係数の等式、
`hr`は既存C135の隣接順位の式。C231の`he`は指定辺の始端または終端の一致、
C232の`hcolor`は同じ垂直辺の両端の色の一致。

```lean
lemma deletionCoefficient_eq_rank_of_adjacent {N r : ℕ} (v : Fin N → Fin r)
    (a b : Fin N) (hab : b.val = a.val + 1) (hcolor : v a = v b) :
    Surjection.deletionCoefficient v b = (-1 : ℤ) ^ Surjection.caesuraRank v b

lemma vertical_vertex_active_or_incoming {m q r : ℕ} (s : Cut m (q + 1))
    (v : Fin (m + 1) → Fin r) (k : Fin (m + (q + 1) + 1))
    (hk : boundaryVertexKind s k = .vertical) :
    Surjection.Caesura (label s v) k ∨
      ∃ e : Fin (m + (q + 1)), e.succ = k ∧ e ∉ s.val

lemma deletionCoefficient_vertical {m q r : ℕ} (s : Cut m (q + 1))
    (v : Fin (m + 1) → Fin r) (k : Fin (m + (q + 1) + 1))
    (hk : boundaryVertexKind s k = .vertical) :
    Surjection.deletionCoefficient (label s v) k =
      (-1 : ℤ) ^ ((s.vertical k).val + Surjection.caesuraRank v (s.horizontal k))

lemma outputDegree_pos_vertical {m q r : ℕ} (s : Cut m (q + 1))
    (v : Surjection.Word r (m + 1)) (k : Fin (m + (q + 1) + 1))
    (hk : boundaryVertexKind s k = .vertical) :
    0 < outputDegree s v (label s v.val k)
```

### 131.2 元の語の次数と入力面番号への実符号の比較（C234〜C236）

一覧：済み 8／全体 48（うち追加 4）

既存構成の符号の法則の貼り合わせ。C234は既存`Word.card_caesuras`と有限集合の
接頭/末尾の分割を使い、濃度の新しい定理は作らない。C235はC229とC234の
自然数の加法の等式。実装前に`/tmp/bsw16/check-vertical-exponent-balance.py`で
**14,942例** の指数の整数としての完全な等式を点検した。
C236は既存C127・C180とC232を合わせ、C235で同じ入力面の符号へ戻す。
座標`hh`・`hv`は、既存C90と端点/全添字の式から後で供給する。未供給のままhv全体の完了とは扱わない。
個々の補題200行以内。局所型`hcard : (caesuraPositions v.val).card = m+1-r`、
`hp`はC229の位置指数の式、`hc`はC234の区切り数の式、
`hperm`はC180による同じ削除色列の逆転符号の一致。

```lean
lemma caesuraRank_add_tail_card {m r : ℕ} (v : Surjection.Word r (m + 1))
    (a : Fin (m + 1)) :
    Surjection.caesuraRank v.val a +
      ((caesuraPositions v.val).filter (fun i => a ≤ i)).card = m + 1 - r

lemma positionExponent_plus_vertical_rank {m q r : ℕ} (s : Cut m (q + 1)) (t : Cut m q)
    (v : Surjection.Word r (m + 1)) (k : Fin (m + (q + 1) + 1))
    (hk : boundaryVertexKind s k = .vertical)
    (hh : ∀ j : Fin (m + q + 1), s.horizontal (k.succAbove j) = t.horizontal j)
    (hv : ∀ j : Fin (m + q + 1), s.vertical (k.succAbove j) =
      (s.vertical k).succAbove (t.vertical j)) :
    positionExponent s v.val +
        ((s.vertical k).val + Surjection.caesuraRank v.val (s.horizontal k)) =
      (m + 1 - r + (s.vertical k).val) + positionExponent t v.val

lemma outputBoundarySignAt_vertical_of_coordinates {m q r : ℕ} (s : Cut m (q + 1)) (t : Cut m q)
    (v : Surjection.Word r (m + 1)) (k : Fin (m + (q + 1) + 1))
    (hk : boundaryVertexKind s k = .vertical)
    (hh : ∀ j : Fin (m + q + 1), s.horizontal (k.succAbove j) = t.horizontal j)
    (hv : ∀ j : Fin (m + q + 1), s.vertical (k.succAbove j) =
      (s.vertical k).succAbove (t.vertical j)) :
    outputBoundarySignAt s v k =
      (-1 : ℤ) ^ (m + 1 - r + (s.vertical k).val) * cutSign t v.val
```

### 131.3 入力の単体射を合成した指定面（C237〜C239）

一覧：済み 8／全体 48（うち追加 4）

C230〜C236の対象ビルドが成功。次は既存C185・C186と同じ次数・指定面の照合を、
入力射`g`の像の色列へ使う。既存の公開宣言は変更せず、新しい名前で足す。
C237は既存の単体射の合成とList.mapの法則、C238は既存C150・C151とList.length_map、
C239は既存C156・C40と同じ頂点列の単射性を使う。新しい構成やホモトピーは作らない。
実装前に`/tmp/bsw16/check-vertical-mapped-vertices.py`で
実際の垂直削除の各色の列と入力面による像の列を **76,407例** 点検した。
個々の補題200行以内。局所型`hsrc`はC238の次数の族の等式を一色で評価したもの。

```lean
lemma simplexVertexList_postcomp {n q q' : ℕ}
    (f : (⦋n⦌ : SimplexCategory) ⟶ ⦋q⦌) (g : (⦋q⦌ : SimplexCategory) ⟶ ⦋q'⦌) :
    simplexVertexList (f ≫ g) = (simplexVertexList f).map g.toOrderHom

lemma deletedOutputDegree_eq_of_mapped_vertexLists {m n q q' r : ℕ}
    (s : Cut m q) (t : Cut n q')
    (v : Surjection.Word r (m + 1)) (w : Surjection.Word r (n + 1))
    (k : Fin (m + q + 1)) (hd : 0 < outputDegree s v (label s v.val k))
    (g : (⦋q'⦌ : SimplexCategory) ⟶ ⦋q⦌)
    (hl : ∀ c, deletedVerticesList s v.val k c = (verticesList t w.val c).map g.toOrderHom) :
    Function.update (outputDegree s v) (label s v.val k)
      (outputDegree s v (label s v.val k) - 1) = outputDegree t w

lemma deletedCutFace_eq_of_mapped_vertexLists {m n q q' r : ℕ}
    (s : Cut m q) (t : Cut n q')
    (v : Surjection.Word r (m + 1)) (w : Surjection.Word r (n + 1))
    (k : Fin (m + q + 1)) (hd : 0 < outputDegree s v (label s v.val k))
    (g : (⦋q'⦌ : SimplexCategory) ⟶ ⦋q⦌)
    (hl : ∀ c, deletedVerticesList s v.val k c = (verticesList t w.val c).map g.toOrderHom)
    (j : Fin (outputDegree s v (label s v.val k) + 1))
    (hj : j.val = vertexRank s v.val (label s v.val k) k) (c : Fin r) :
    deletedCutFace s v (label s v.val k) hd j c =
      eqToHom (congrArg SimplexCategory.mk
        (congrFun (deletedOutputDegree_eq_of_mapped_vertexLists s t v w k hd g hl) c)) ≫
          (face t w c ≫ g)
```

### 131.4 入力射を合成した実テンソル（C240・C241）

一覧：済み 8／全体 48（うち追加 4）

C237〜C239の対象ビルド成功。C240・C241は既存C188・C189の同じ次数移送に、
C239の指定面と既存の関手の合成則を代入する法則。新しい構成は足さない。
個々の補題は200行以内。以下は実装する宣言の型（証明は省略）。

```lean
lemma deletedCutTensor_eq_mapped_cutTensor {m n q q' r : ℕ} (S : SSet.{0})
    (s : Cut m q) (t : Cut n q')
    (v : Surjection.Word r (m + 1)) (w : Surjection.Word r (n + 1))
    (k : Fin (m + q + 1)) (hd : 0 < outputDegree s v (label s v.val k))
    (g : (⦋q'⦌ : SimplexCategory) ⟶ ⦋q⦌)
    (hl : ∀ c, deletedVerticesList s v.val k c = (verticesList t w.val c).map g.toOrderHom)
    (j : Fin (outputDegree s v (label s v.val k) + 1))
    (hj : j.val = vertexRank s v.val (label s v.val k) k) (x : S _⦋q⦌)
    (h : -(degreeSum r (outputDegree t w) : ℤ) = -((m + q + 1 - r : ℕ) : ℤ) + 1) :
    deletedCutTensor A S s v (label s v.val k) hd j x =
      (eqToHom (congrArg (fun z : ℤ => (power (chains A S) r).X z) h)).hom
        (cutTensor A S t w (S.map g.op x))

lemma deletedCutTensor_eq_mapped_cutTensorAt {m n q q' r : ℕ} (S : SSet.{0})
    (s : Cut m q) (t : Cut n q')
    (v : Surjection.Word r (m + 1)) (w : Surjection.Word r (n + 1))
    (k : Fin (m + q + 1)) (hd : 0 < outputDegree s v (label s v.val k))
    (g : (⦋q'⦌ : SimplexCategory) ⟶ ⦋q⦌)
    (hl : ∀ c, deletedVerticesList s v.val k c = (verticesList t w.val c).map g.toOrderHom)
    (j : Fin (outputDegree s v (label s v.val k) + 1))
    (hj : j.val = vertexRank s v.val (label s v.val k) k) (x : S _⦋q⦌)
    (h : -((n + q' + 1 - r : ℕ) : ℤ) = -((m + q + 1 - r : ℕ) : ℤ) + 1) :
    deletedCutTensor A S s v (label s v.val k) hd j x =
      (eqToHom (congrArg (fun z : ℤ => (power (chains A S) r).X z) h)).hom
        (cutTensorAt A S t w (S.map g.op x))

```

### 131.5 同じ入力面による各色の列の像（C242・C243）

一覧：済み 8／全体 48（うち追加 4）

C240・C241のビルド成功。既存C90の座標と`selectColor_map`の法則を各色へ適用する。
§131.3の76,407例の点検に含まれる。既存構成の係数移送であり、個々の補題200行以内。

```lean
lemma deletedVerticesList_vertical_of_coordinates {m q r : ℕ}
    (s : Cut m (q + 1)) (t : Cut m q) (v : Fin (m + 1) → Fin r)
    (k : Fin (m + (q + 1) + 1))
    (hh : ∀ j : Fin (m + q + 1), s.horizontal (k.succAbove j) = t.horizontal j)
    (hv : ∀ j : Fin (m + q + 1), s.vertical (k.succAbove j) =
      (s.vertical k).succAbove (t.vertical j)) (c : Fin r) :
    deletedVerticesList s v k c =
      (verticesList t v c).map (s.vertical k).succAbove

lemma deletedVerticesList_vertical_interior {m q r : ℕ} (s : Cut m (q + 1))
    (v : Fin (m + 1) → Fin r) (a b : Fin (m + (q + 1)))
    (hab : b.val = a.val + 1) (ha : a ∉ s.val) (hb : b ∉ s.val) (c : Fin r) :
    deletedVerticesList s v a.succ c =
      (verticesList ((BarrattEccles.verticalInsertionEquiv m q a).symm ⟨s, ha⟩) v c).map
        (s.vertical a.succ).succAbove

```

### 131.6 検証・実測・次の接続

一覧：済み 8／全体 48（うち追加 4）

新規5本・339行。各モジュールの対象ビルドは成功し、Leanの警告0。
小さい独立監査は **5モジュール・24宣言・標準三公理のみ** で成功。
新規5本にsorry・追加公理0。既存の公開宣言・界面・共通入口・共通監査は変更していない。
`git diff --check`成功。鍵は各対象ビルド・各監査の間だけ取り、終了後返却。

| 登録候補（すべて `SerrePositivity.EInfinity.SimplexCuts.` 以下） | 行数 | 対象ビルド |
| --- | ---: | --- |
| VerticalDeletionCoefficients | 92 | 成功、2,234 jobs |
| VerticalBoundarySigns | 64 | 成功、2,274 jobs |
| MappedDeletedFaces | 58 | 成功、2,185 jobs |
| MappedDeletedTensors | 76 | 成功、2,189 jobs |
| VerticalMappedVertices | 49 | 成功、2,039 jobs |

ログは `/tmp/bsw16/m14-vertical-deletion-coefficients-01.log`、
`m14-vertical-boundary-signs-01.log`、`m14-mapped-deleted-faces-02.log`、
`m14-mapped-deleted-tensors-01.log`、`m14-vertical-mapped-vertices-01.log`。
監査ソースは `/tmp/bsw16/audit-m14-vertical-mapped.lean`、
結果は `/tmp/bsw16/m14-vertical-mapped-audit.log`。
C237の初回ビルドは単体射の合成の定義展開の一行が不足して失敗した。
`rfl`で補い、2回目の対象ビルド成功を検収結果とする。

L09a・L09累計は **7,283行**（6,944+339）、M14全体は **12,349行**。
12,500行の途中報告まで151行、L09a・L09の次の約7,600行の区切りまで317行。
§130.12の完成見込み20,440〜27,150行の上側は依然として外枠25,000行を超える。
この見込みを上限の承認とは扱わず、次の途中報告で残りを出し直す。

今回閉じたのは垂直の実符号と、入力射の像の色列から元の圏での実テンソルへ戻す法則。
C242・C243は実際の内部削除に適用済み。一方、端点と全垂直添字への適用、
実境界項の符号付き等式、`universalBoundaryValue_vertical_neg` の組み立ては残る。
L09a全体を完了とは数えない。次は端点を含む同じ座標の供給と、C236・C241の接続。
B4は595254e10で完了済みのまま。/goalは継続中。

## 132. 垂直端点の列と同じ入力面の実境界項（11-14）

一覧：済み 8／全体 48（うち追加 4）

§131は593c7df71で検証・保存済み。C244・C245は既存の始端・終端の座標式を
C242へ代入する法則。先の76,407例の点検には端点も含まれる。
C246は語の全射性からの次数の計算。C247はC236・C241・C242の貼り合わせであり、
同じ入力面に対する元の圏の厳密な等式を示す。既存の公開宣言の型は変えない。
すべて個々の補題200行以内。以下の型を記録してから検証する。

```lean
lemma deletedVerticesList_vertical_first {m q r : ℕ} (s : Cut m (q + 1))
    (v : Fin (m + 1) → Fin r) (h₀ : (0 : Fin (m + (q + 1))) ∉ s.val) (c : Fin r) :
    deletedVerticesList s v 0 c =
      (verticesList ((BarrattEccles.verticalInsertionEquiv m q 0).symm ⟨s, h₀⟩) v c).map
        (0 : Fin (q + 2)).succAbove

lemma deletedVerticesList_vertical_last {m q r : ℕ} (s : Cut m (q + 1))
    (v : Fin (m + 1) → Fin r) (a : Fin (m + (q + 1))) (ha : a ∉ s.val)
    (hlast : a.val + 1 = m + (q + 1)) (c : Fin r) :
    deletedVerticesList s v (Fin.last (m + (q + 1))) c =
      (verticesList ((BarrattEccles.verticalInsertionEquiv m q a).symm ⟨s, ha⟩) v c).map
        (Fin.last (q + 1)).succAbove

lemma verticalDeletion_degree_eq {m q r : ℕ} (v : Surjection.Word r (m + 1)) :
    -((m + q + 1 - r : ℕ) : ℤ) = -((m + (q + 1) + 1 - r : ℕ) : ℤ) + 1

lemma outputBoundaryTerm_vertical_of_coordinates {m q r : ℕ} (S : SSet.{0})
    (s : Cut m (q + 1)) (t : Cut m q) (v : Surjection.Word r (m + 1))
    (k : Fin (m + (q + 1) + 1)) (hk : boundaryVertexKind s k = .vertical)
    (hh : ∀ j : Fin (m + q + 1), s.horizontal (k.succAbove j) = t.horizontal j)
    (hv : ∀ j : Fin (m + q + 1), s.vertical (k.succAbove j) =
      (s.vertical k).succAbove (t.vertical j))
    (j : Fin (outputDegree s v (label s v.val k) + 1))
    (hj : j.val = vertexRank s v.val (label s v.val k) k) (x : S _⦋q + 1⦌) :
    outputBoundaryTerm A S s v (label s v.val k) j x =
      (-1 : ℤ) ^ (m + 1 - r + (s.vertical k).val) •
        (eqToHom (congrArg (fun z : ℤ => (power (chains A S) r).X z)
          (verticalDeletion_degree_eq (q := q) v))).hom
            (cutTerm A S t v (S.δ (s.vertical k) x))

```

### 132.1 全添字への座標の貼り合わせ（C248）

一覧：済み 8／全体 48（うち追加 4）

既存の三分割と水平挿入の座標式を同じ指定切断へ適用する構成の法則。
新しい有限同値は作らない。C248を方向交換して、既存の垂直同値の同じ指定切断を読む。
個々の補題200行以内。以下の型を記録する。

```lean
lemma horizontalBoundaryFaceEquiv_deleted_coordinates (m q : ℕ)
    (c : Fin (m + 2) × Cut m q) (l : Fin (m + q + 1)) :
    let z := (horizontalBoundaryFaceEquiv m q c).val
    z.1.horizontal (z.2.succAbove (Fin.cast (by omega : m + q + 1 = m + 1 + q) l)) =
        c.1.succAbove (c.2.horizontal l) ∧
      z.1.vertical (z.2.succAbove (Fin.cast (by omega : m + q + 1 = m + 1 + q) l)) =
        c.2.vertical l
```

### 132.2 同じ全垂直添字への方向交換（C249・C250）

一覧：済み 8／全体 48（うち追加 4）

C218・C248と既存の`exchange_horizontal`・`exchange_vertical`だけを使う構成の法則。
小さい切断や入力面を別の同値で選び直さない。`hcast`は同じ自然数値のFinの移送と
`succAbove`の可換性、`ht`はC248、`hv`・`hh`は小さい切断の交換公式の適用。
個々の補題200行以内。型は次のとおり。

```lean
lemma verticalBoundaryFaceEquiv_vertical (m q : ℕ) (c : Fin (q + 2) × Cut m q) :
    (verticalBoundaryFaceEquiv m q c).val.1.vertical
      (verticalBoundaryFaceEquiv m q c).val.2 = c.1

lemma verticalBoundaryFaceEquiv_deleted_coordinates (m q : ℕ)
    (c : Fin (q + 2) × Cut m q) (j : Fin (m + q + 1)) :
    let z := (verticalBoundaryFaceEquiv m q c).val
    z.1.horizontal (z.2.succAbove j) = c.2.horizontal j ∧
      z.1.vertical (z.2.succAbove j) = c.1.succAbove (c.2.vertical j)

```

### 132.3 指定された全入力面の実境界項（C251）

一覧：済み 8／全体 48（うち追加 4）

C247へC249・C250を代入する構成の法則。入力面の番号を元の同値の番号で置換し、
型の仮定を追加せず同じ指定項の厳密な一致を得る。個々の補題200行以内。

```lean
lemma outputBoundaryTerm_verticalBoundaryFaceEquiv {m q r : ℕ} (S : SSet.{0})
    (v : Surjection.Word r (m + 1)) (c : Fin (q + 2) × Cut m q)
    (j : Fin (outputDegree (verticalBoundaryFaceEquiv m q c).val.1 v
      (label (verticalBoundaryFaceEquiv m q c).val.1 v.val
        (verticalBoundaryFaceEquiv m q c).val.2) + 1))
    (hj : j.val = vertexRank (verticalBoundaryFaceEquiv m q c).val.1 v.val
      (label (verticalBoundaryFaceEquiv m q c).val.1 v.val
        (verticalBoundaryFaceEquiv m q c).val.2) (verticalBoundaryFaceEquiv m q c).val.2)
    (x : S _⦋q + 1⦌) :
    outputBoundaryTerm A S (verticalBoundaryFaceEquiv m q c).val.1 v
      (label (verticalBoundaryFaceEquiv m q c).val.1 v.val
        (verticalBoundaryFaceEquiv m q c).val.2) j x =
      (-1 : ℤ) ^ (m + 1 - r + c.1.val) •
        (eqToHom (congrArg (fun z : ℤ => (power (chains A S) r).X z)
          (verticalDeletion_degree_eq (q := q) v))).hom
            (cutTerm A S c.2 v (S.δ c.1 x))
```

### 132.4 全垂直分岐とL09aの貼り合わせ（C252〜C255、L09a）

一覧：済み 8／全体 48（うち追加 4）

C249〜C251の対象ビルド成功、警告0。以下は既存の全境界値・依存した色と面の組・
元の対合の貼り合わせ。C253はC223と同じ次数移送の合成を入力境界の分岐に適用する。
新しい数学の補題ではなく、L09aの未供給のhvと既存の三分岐への接続そのもの。
L09aは§112の型のまま。検証するまでは完了数を増やさない。個々の補題200行以内。

```lean
lemma universalBoundaryValue_input (S : SSet.{0}) {r d : ℕ}
    (w : Surjection.BasisWord (r + 1) d) (q : ℕ) (x : S _⦋q⦌)
    (c : Fin (q + 1) × Cut (r + d) (q - 1)) :
    universalBoundaryValue A S w q x (.inr (.inr c)) = simplexBoundaryTerm A S w q c x

lemma universalBoundaryValue_vertical_succ (S : SSet.{0}) {r d : ℕ}
    (w : Surjection.BasisWord (r + 1) d) (q : ℕ) (x : S _⦋q + 1⦌)
    (c : Fin (q + 2) × Cut (r + d) q) :
    universalBoundaryValue A S w (q + 1) x
        (.inl (verticalBoundaryFaceEquiv (r + d) q c).val) =
      -universalBoundaryValue A S w (q + 1) x (.inr (.inr c))

lemma universalBoundaryValue_vertical_neg (S : SSet.{0}) {r d : ℕ}
    (w : Surjection.BasisWord (r + 1) d) (q : ℕ) (x : S _⦋q⦌) (hq : 0 < q)
    (c : Fin (q + 1) × Cut (r + d) (q - 1)) :
    universalBoundaryValue A S w q x
        (.inl ((verticalBoundaryAllEquiv (r + d) q hq) c).val) =
      -universalBoundaryValue A S w q x (.inr (.inr c))

lemma boundaryBalancePerm_neg (A : Type u) [CommRing A] (S : SSet.{0}) {r d : ℕ}
    (w : Surjection.BasisWord (r + 1) d) (q : ℕ) (x : S _⦋q⦌)
    (i : BoundaryBalanceIndex w q) :
    boundaryBalanceTerm A S w q (boundaryBalancePerm w q i) x =
      -boundaryBalanceTerm A S w q i x

theorem boundaryBalance_pairing {r d : ℕ} (w : Surjection.BasisWord (r + 1) d) (q : ℕ) :
    ∃ τ : Equiv.Perm (BoundaryBalanceIndex w q), Function.Involutive τ ∧
      (∀ i, τ i = i → ∀ (A : Type u) [CommRing A] (S : SSet.{0}) (x : S _⦋q⦌),
        boundaryBalanceTerm A S w q i x = 0) ∧
      (∀ i, τ i ≠ i → ∀ (A : Type u) [CommRing A] (S : SSet.{0}) (x : S _⦋q⦌),
        boundaryBalanceTerm A S w q (τ i) x = -boundaryBalanceTerm A S w q i x)

```

### 132.5 同じ有限和の相殺（C256）

一覧：済み 8／全体 48（うち追加 4）

C252〜C254の対象ビルド成功。L09aの包装は混合角モジュールのimportを補って再検証する。
C256は既存`Finset.sum_ninvolution`へ同じ対合を渡す法則であり、固定点零を使うため
2が可逆という仮定も加えない。L09の複体の微分の式への照合は別に残る。
個々の補題200行以内。

```lean
lemma sum_boundaryBalanceTerm_eq_zero (A : Type u) [CommRing A] (S : SSet.{0}) {r d : ℕ}
    (w : Surjection.BasisWord (r + 1) d) (q : ℕ) (x : S _⦋q⦌) :
    ∑ i : BoundaryBalanceIndex w q, boundaryBalanceTerm A S w q i x = 0
```

### 132.6 L09aの完了・取り込み点・検証

一覧：済み 9／全体 48（うち追加 4）

**L09a `boundaryBalance_pairing` は§112の型のまま完成**。同じ有限対合の対合性、
固定点での実境界値の零、非固定点の両側の負号による一致を、任意の係数環・単体的集合・
単体に対して元の加群で示した。三分岐のどれも仮定として残していない。
ホモトピー圏への移行や2の可逆性は使わない。C256で同じ全境界項の和が零まで検証済み。
**L09 `cutSum_boundary` の複体の微分の式への照合は未完**なので、完了数を増やすのはL09aの一件だけ。

新規8モジュール・457行、既存公開宣言・界面・drafts・共通入口・共通監査に変更なし。
対象ビルドと専用監査が成功。監査は **8モジュール・32宣言・標準三公理のみ**。
全8本にsorry・追加公理0、最終ソースのLean警告0、`git diff --check`成功。
鍵は各ビルド・監査ごとに取り、終了を確認して返却。一枚だけ並び、待機中の別レーンの
鍵を使うことも、常駐のビルドセッションを置くこともしていない。

登録候補（接頭部はすべて `SerrePositivity.EInfinity.SimplexCuts.`）：

| モジュール | 行数 | 検証内容 |
| --- | ---: | --- |
| VerticalEndpointVertices | 46 | 始端・終端の削除色列。最初の2対象ビルドでこの対象自体の生成成功、専用監査でも読込成功 |
| VerticalInputTerms | 54 | 座標を指定した実境界項。最終対象ビルド成功、2,278 jobs |
| AllHorizontalDeletionCoordinates | 93 | 全水平添字の両削除座標。下のVerticalFaceTermsの成功ビルドに含む |
| VerticalFaceCoordinates | 61 | 全垂直添字の両削除座標・入力面番号。下の成功ビルドに含む |
| VerticalFaceTerms | 45 | 指定した同じ入力面の実境界項。最終対象ビルド成功、2,303 jobs |
| VerticalBoundaryValues | 78 | 全境界値のhv。下の成功ビルドに含む |
| BoundaryPairingValues | 47 | 三分岐の貼り合わせ・L09a。下の成功ビルドに含む |
| BoundarySumCancellation | 33 | 同じ全有限和の相殺。最終対象ビルド成功、2,334 jobs |

ログ：`/tmp/bsw16/m14-vertical-input-terms-01.log`（端点の対象自体は成功、別対象失敗）、
`m14-vertical-input-terms-02.log`、`m14-all-face-coordinates-03.log`（水平の対象自体は成功、別対象失敗）、
`m14-vertical-face-terms-02.log`、`m14-boundary-sum-cancellation-01.log`。
専用監査は `/tmp/bsw16/audit-m14-boundary-pairing.lean` と
`/tmp/bsw16/m14-boundary-pairing-audit.log`。
失敗した組全体を成功とは扱わず、該当対象の生成成功と後続の成功ビルド・監査で区別している。
途中の修正は、同値の局所略記の展開、同じFin値の移送、入力面の略記の展開、
混合角のimport不足だけ。新しい数学の前提や追加の構成は導入していない。

### 132.7 約12,500行・約7,600行の途中報告（止まらず継続）

一覧：済み 9／全体 48（うち追加 4）

§131の検証済み12,349行に今回457行を加え、**M14全体12,806行**。
L09a・L09は7,283+457=**7,740行**。旧coherent経路の保管済み10,216行、
報告・監査・Pythonの点検はこれに含めない。未検証の本体下書きは現在ない。
半分の12,500行と、L09a・L09の次の約7,600行の区切りを越えたため、ここで出し直す。
外枠25,000行は変更せず、残り実装可能な枠は **12,194行**。

§130.12の垂直の残り400〜750行に対し、§131の339行と今回の実境界値までの377行、
合計716行を使った。差は **−34〜+316行**（今回の包装・有限和の80行は別計上）。
内部だけでなく全添字へ接続するため、
既存の水平三分割の削除座標を明示し、それを方向交換する2本154行が増えた。
この座標の供給を証明済みと見なして見込みから消したり、同じ式の仮定を残してhv完了とはしなかった。
L09aの包装は今回のBoundaryPairingValuesの47行、有限和の相殺は33行で閉じた。

L09aの残りは0。L09の残りは、零次数も含む次の既存構成の法則と貼り合わせ。

| 残り | 現在の不足 | 新規見込み |
| --- | --- | ---: |
| 出力の微分の和 | 右括弧の同じ純粋テンソルの微分則とgen_dを、指定削除面の全和へ戻す。現在の有限和零をこれだけで微分の式とは呼べない | 250〜450 |
| 係数・入力の和 | 非全射・退化語を零にした係数の微分の実基底の式、および入力の交代面和と同じ指定移送を照合 | 100〜180 |
| L09包装 | 三つの和をC256に代入し、零次数の分岐と共通次数の移送をまとめる | 50〜120 |
| **L09残り** | **L09aをやり直す部分は含まない** | **400〜750** |

前の「包装・L09」200〜350行は、純粋テンソルの一般の微分則を既存の同じ型で直接使えるかの
確認が不足していた。IntervalCutsの区間版の境界定理を一般次元の代用にはしない。
同じ右括弧テンソルの再帰と既存のテンソル微分則を使う法則として型を記録して進める。
L09a・L09の完成時は **8,140〜8,490行** の見込み。

L10〜L28の次元によらないconvolution・χ/TR・符号の再利用の筋と行ごとの見込みは
§121.3・§121.4から変更なし。そこを今回の実測なしに控除しない。

| M14全体の残り | 下端 | 上端 |
| --- | ---: | ---: |
| L09 | 400 | 750 |
| L10〜L28（L12a込み） | 4,330 | 7,790 |
| L29〜L37 | 1,200 | 2,000 |
| G10後のnative Totへの適用 | 500 | 900 |
| filtered塔 | 300 | 550 |
| 二重模型の実現の比較 | 1,500 | 2,800 |
| **新規残り** | **8,230** | **14,790** |
| **実測12,806行を含む完成見込み** | **21,036** | **27,596** |

上側は外枠を **2,596行** 超えるリスクが残る。外枠を上げたとは扱わない。
下端は収まり、現在の実測は外枠に届いていないため、指示どおり止まらずL09へ進む。
次のL09a・L09の1,000行区切りは約8,600行。G10の部品、M15・G12は作らない。

## 133. L09への接続：同じテンソルの微分則の型（実装前）

一覧：済み 9／全体 48（うち追加 4）

§132は56fc86f0bで保存した。L09aの対合・固定点零・全有限和零は検証済み。
次のC257・C258は、既存の右括弧純粋テンソル・生成元・有限和の微分の法則を
同じ出力境界項へ書き直すもの。新しい演算や別の鎖模型は作らない。
C257は`tensorValue`の因子数に沿う再帰、既存`ιTensorObj`の二因子の微分則、
既存`gen_d`を使う。因子の次数零は正次数への延長の零で分ける。
`NegativeTensor.degreeMap_D₁`・`degreeMap_D₂`の零次数と符号の処理も参照できるが、
IntervalCutsの区間上の境界定理を一般単体での証明の代用にはしない。
C258はC257と`map_sum`、共通次数への`eqToHom`の自然性の貼り合わせ。
いずれも§112のL09に必要な既存構成の法則の証明分割で、別の一覧IDを増やさない。

```lean
lemma cutTerm_d_eq_sum_outputBoundaryTerm (A : Type u) [CommRing A] (S : SSet.{0})
    {m q r : ℕ} (s : Cut m q) (v : Surjection.Word r (m + 1)) (x : S _⦋q⦌) :
    (power (chains A S) r).d (-((m + q + 1 - r : ℕ) : ℤ))
        (-((m + q + 1 - r : ℕ) : ℤ) + 1) (cutTerm A S s v x) =
      ∑ a : Fin r, ∑ j : Fin (outputDegree s v a + 1),
        outputBoundaryTerm A S s v a j x

lemma cutSum_d_eq_sum_outputBoundaryTerm (A : Type u) [CommRing A] (S : SSet.{0})
    {r d q : ℕ} (w : Surjection.BasisWord (r + 1) d) (x : S _⦋q⦌)
    (h : -((r + d + q + 1 - (r + 1) : ℕ) : ℤ) + 1 = -((d + q : ℕ) : ℤ) + 1) :
    (power (chains A S) (r + 1)).d (-((d + q : ℕ) : ℤ))
        (-((d + q : ℕ) : ℤ) + 1) (cutSum A S w x) =
      ∑ s : Cut (r + d) q, ∑ a : Fin (r + 1),
        ∑ j : Fin (outputDegree s (positiveWord w) a + 1),
          (eqToHom (congrArg (fun z : ℤ => (power (chains A S) (r + 1)).X z) h)).hom
            (outputBoundaryTerm A S s (positiveWord w) a j x)
```

C258の`h`は算術で常に供給できる等式であり、未供給の数学的仮定としてL09へ残さない。
C257・C258はここでは型の記録だけで、実装・検証・完成行数にはまだ数えない。
