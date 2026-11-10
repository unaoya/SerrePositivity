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
