# KB-W2 HTT 第1章

原典の版を目次記載SHA-256と照合したPDFの本文と、現在のソースの宣言の型を読み比べた。kernel実行・Lean変更・ビルド・鍵はなし。

対象71行。旧状態：{'none': 57, 'partial': 14}。新状態：{'none': 55, 'partial': 16}。partial_kind：{'component': 13, 'special': 3}。

既存own・mathlibなど対象外39行は全フィールド・引用符・改行をそのまま保存。対象行でもstatus/declarations/reason/partial_kind以外は不変。axioms/checkは旧記録であり今回のkernel確認結果ではない。

## 全対象行

| 番号 | 旧→新 | partial_kind | 理由 |
| --- | --- | --- | --- |
| 1.1.1.1 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：ActionCategory は一般の monoid action の圏。群準同型集合 Hom(G,H) 上の H の共役作用を実際に構成する比較がなく、射 h の式と groupoid 内の同型 iff 共役を結ぶ型もない。一般の action の受け口はこの具体例の証明の部品にとどまる。 |
| 1.1.1.2 | none → partial | component | 冒頭で明示された同じ連続写像f₀,f₁のhomotopyはContinuousMap.Homotopyそのもので、I×X→Yと端点条件を持つ。X×Iとの積の交換以外の比較を要しない。後続の写像空間の高次圏・ホモトピー圏の主張は含まない。 |
| 1.1.1.4 | partial → partial | special | KB-W2原文・型再照合：仮定：位相空間 X、n を 0 または 1 に限定（Lean が強い特殊形）。結論：ZerothHomotopy は path components、FundamentalGroupoid の対象は X の点、射は端点付きの道を端点固定ホモトピーで割ったものなので、この二つの n の原典の構成に一致。n≥2 と ∞ の比較は含まない。 |
| 1.1.1.5 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：準圏・Kan 複体・Cat 豊穣二圏の各型はあるが、三つの (∞,n) の呼称をまとめた原典の規約は Lean の宣言として見つからなかった。 |
| 1.1.1.6 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：EnrichedCategory/EnrichedCat は任意の既存 monoidal V を入力する。CompactlyGenerated は弱 Hausdorff 条件を要求せず、弱 Hausdorff compactly generated 空間の Cartesian monoidal structure とその Hom への特殊化がない。異なる underlying category の受け口を CG の topological category の定義と数えない。 |
| 1.1.1.7 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：一般の TopCat と特異単体集合の随伴は見つかったが、弱 Hausdorff な CG で積と両立する豊穣圏の比較を与える宣言は見つからなかった。 |
| 1.1.2.2 | partial → partial | component | KB-W2原文・型再照合：仮定：K が通常圏の nerve である、すなわち原典 (1) の場合（Lean が強い特殊形）。結論：Nerve.strictSegal と StrictSegal.quasicategory から各 inner horn の filler の存在を得る。これは (2) の存在部分に一致するが、一意性と (2)⇒(1) の再構成は得ていない。 |
| 1.1.2.3 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：fundamentalGroupoidNerve_kanComplex は既に IsGroupoid C を仮定して外ホーンを満たす向き。原典が指摘する Λ²₂ の全ての延長の存在から C の射の逆を得る必要条件の向きはなく、逆向きの定理を原文の結論と取り違えない。 |
| 1.1.2.5 | partial → partial | component | KB-W2原文・型再照合：仮定：任意の Kan 複体 S（HTT と一致）。結論：Quasicategory S を得るので「Any Kan complex is an ∞-category」という最初の assertion に一致。一般の X の singular complex の Kan 性と π≤∞X の同定は含まない。 |
| 1.1.2.7 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：準圏と Kan 複体の両方が単体集合を台にする宣言を読んだが、用途ごとに筆記体と大文字を分ける原典の表記規約に当たる宣言は見つからなかった。 |
| 1.1.3.1 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：Functor.IsEquivalence は通常圏の充満忠実性・本質的全射性。位相 Hom が離散な enriched category を構成してその strong equivalence と比較する型がない。通常圏の類似条件だけを topological enriched strong equivalence の特殊形にしない。 |
| 1.1.3.2 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：nerveFunctorCompHoFunctorIso は h(N(C))≅C という通常 nerve の随伴に関する定理。位相 enriched C の Hom 空間に π0 を取り合成する同じ hC を構成しない。二つの h の記号だけでは特殊形の比較が成立しない。 |
| 1.1.3.3 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：CWComplex のセル構造と ContinuousMap.Homotopy の端点付き写像を読んだが、CW 複体を対象として連続写像をホモトピーで割った Hom とその合成を備える圏を見つけなかった。 |
| 1.1.3.5 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：豊穣圏の ForgetEnrichment と π₀ の型を読んだが、弱同値で局所化した位相 Hom を持つ圏からの忘却が π₀-Hom 圏を返す比較は見つからなかった。 |
| 1.1.3.6 | partial → partial | component | KB-W2原文・型再照合：仮定：位相豊穣関手 F の各 Hom に誘導される連続写像を入力（HTT の各 Hom の条件と一致）。結論：weakHomotopyEquivalences は π0 と全基点・正次数 πn の全単射を要求するので、明記された第一条件の弱ホモトピー同値の判定を表す。F 全体の hF の本質的全射を組み合わせた定義と hC との比較はない。 |
| 1.1.3.7 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：IsIso と nerveFunctorCompHoFunctorIso は通常圏の hN(C) 上の可逆性である。位相豊穣 hD の Hom=π0Map を構成していないので、D 内の射 f をその hD に送る同じ定義にはならず、通常圏との類似だけを残さない。 |
| 1.1.3.8 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：位相空間の弱同値述語と準圏の同値述語を読んだ。位相 Hom を空間のホモトピー圏に移す関手がなく、豊穣 hF が同値かを検出する主張は見つからなかった。 |
| 1.1.4.2 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：EnrichedCat SSet と SimplicialObject Cat の両方の型を読んだが、対象集合が定値の単体的 Cat 図式から豊穣 Hom を復元する比較は見つからなかった。 |
| 1.1.4.3 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：simplicialNerve_quasicategory は局所 Kan な C の nerve の準圏性という別の結論。原典の準圏値 Hom による ∞-bicategory の解釈や geometric realization/singular による enriched adjunction と hC の比較ではない。局所 Kan 性を仮定に使うだけでは原典の成分の証明としない。 |
| 1.1.4.4 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：局所 Kan 圏の nerve の同値述語と単体集合の幾何学的弱同値を読んだが、一般の単体豊穣関手の hF を H-豊穣同値として定義し比較する宣言は見つからなかった。 |
| 1.1.5.2 | partial → partial | component | KB-W2原文・型再照合：仮定：[n] 内の a<b（Lean が強い特殊形）。結論：pathInteriorNerveIso は原典 C[Δn] の Hom=nerve(Path a b) を内部点の冪集合の nerve と同型にするので、明記された cube の記述に一致。全ての a≤b と [n] への enriched weak equivalence、および cosimplicial cofibrant replacement は含まない。 |
| 1.1.5.4 | partial → partial | component | KB-W2原文・型再照合：仮定：全順序間の単調写像 f,g（HTT と一致）。結論：厚化の functor(g∘f)=functor(f)∘functor(g) を得るので cosimplicial thickening の合成則の assertion に一致。先に述べられた二端点の特別な頂点 pij の像の式をこの宣言では別個に証明していない。 |
| 1.1.5.5 | partial → partial | component | KB-W2原文・型再照合：仮定：単体的圏 C（HTT の最初の文と一致）。結論：SimplicialNerve C は各 n で厚化から C への enriched functors を持つ単体集合で、最初の定義に一致。位相豊穣 C の Hom に Sing を施す base change と topological nerve の定義は含まない。 |
| 1.1.5.6 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：通常 nerve と豊穣 SimplicialNerve の型を読んだが、原典で双方を N(C) と略記する編集上の規約に当たる宣言は見つからなかった。 |
| 1.1.5.7 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：SimplicialNerve と homEquiv′ はそれぞれ全次数の enriched Hom と零単体の ordinary Hom を定義するが、それだけでは二つの nerve が一般に異なることを証明しない。比較の非同型の実例もなく、二つの定義をこの Warning の結論の成分に数えない。 |
| 1.1.5.8 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：nerveToCoherent は任意の既存 simplicial C の普通 nerve から coherent nerve への射を作るだけ。Hom が constant な場合にその射が同型になる宣言がなく、topological discrete enrichment との比較もない。比較射の存在を同型性の partial にしない。 |
| 1.1.5.9 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：SimplicialThickening/Path/compFunctor は全順序上の部分集合と union であり、一般 poset の C[N(A)] を rigidification から同定していない。原典の Hom を鎖の nerve とする同型の比較がなく、全順序で似た式があるだけでは特殊化と数えない。 |
| 1.1.5.11 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：simplicialNerve_quasicategory は局所 Kan C の絶対 nerve の定理であり、与えられた enriched F の同じ N(F) の InnerFibration を供給しない。終対象への場合に読み替えるにも N(terminal enriched category) と一点の比較が未供給で、絶対結果を相対結果の部品として残さない。 |
| 1.1.5.12 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：simplicialNerve_quasicategory は局所 Kan な enrichment を既に与えた場合であり、TopCat.toSSet は個別の Hom 空間の singular set。Sing を全 Hom に施した同じ topological C の enriched category とその Kan 性を構成しておらず、元の N(C) の準圏性ではない。 |
| 1.1.5.13 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：位相弱同値述語、SimplicialNerve、および coherentResolutionAdjunction の余単位を読んだ。後者は単体集合の解像と単体集合の随伴であり、C[N(C)] の Hom を実現した位相豊穣余単位には当たらない。 |
| 1.1.5.14 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：HomotopyCategory は二次切断と辺の homotopy quotient による通常圏、IsPrecompositionEquivalence は準圏への前合成による述語である。原典の C[S] を作って H-enriched hC[S] と比較する宣言がないため、その homotopy category と enriched equivalence の定義には直接対応しない。 |
| 1.1.5.15 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：IsPrecompositionEquivalence と IsQCatEquivalence の定義と相互比較を読んだが、Joyal の旧用語の弱圏同値と強い方の圏同値を区分して比較する宣言は見つからなかった。 |
| 1.1.5.16 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：幾何学的 weakEquivalences と前合成の IsPrecompositionEquivalence は別々に定義されるが、後者と HTT の H-enriched categorical equivalence の定義との比較はない。用語を別に置いたことだけを、原典の二つの元の概念の区別の成分とは数えない。 |
| 1.1.5.17 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：通常 nerve の左随伴と単体集合の幾何学的実現の随伴を読んだが、C[S] とその位相豊穣実現の間で弱同値を比較する豊穣関手は見つからなかった。 |
| 1.1.5.18 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：inner-anodyne resolution は任意の S から準圏への前合成同値を作る。原典の C[S] から定まる H-enriched equivalence とその述語の比較がなく、原典の指定した &#124;C[S]&#124; の topological nerve との比較もない。違う同値述語による置換だけを残さない。 |
| 1.2.2.1 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：pinchedHom_kanComplex は準圏の右 pinched Hom の Kan 性を証明するが、原典の定義は任意の S に対する [MapC[S](x,y)]∈H。C[S] の enriched Hom とその Kan 模型との比較がなく、別の写像空間模型の構成だけでは定義の特殊形にならない。 |
| 1.2.2.2 | none → partial | component | 原文が二つ目の用法として明記する、同じX→S,Y→Sの相対写像空間はrelativeFunctorSpaceの内部Homのfiberの定義そのもの。頂点間のH-enrichedなMapとの同定は含まない。 |
| 1.2.2.4 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：pinchedHomPiZeroEquiv は右 Hom の π0 と普通 hS の Hom の全単射。原典の可縮な全選択空間にわたる composition と C[S] の Hom との H 同型を与えない。成分上の通常合成が読めることをその高次 composition の部分としない。 |
| 1.2.3.2 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：単体集合の π₀Functor と通常 nerve の随伴は見つかったが、単体豊穣圏の Hom ごとに π₀ を取る関手が、定値豊穣化 Cat → Cat∆ の左随伴となる宣言は見つからなかった。 |
| 1.2.3.3 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：coherentUnderlyingHoFunctor は通常の underlying C から hN(C) への関手のみ。Hom に π0 を施した enriched hC を経由する比較と局所 Kan の下での equivalence はない。比較射の存在だけを比較同値の partial にしない。 |
| 1.2.4.1 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：IsInvertibleEdge.nonempty_inverse は準圏の辺の逆と二単体を返す。位相 enriched C の f と hC の同型、左右の Hom 上の weak equivalences を比較する型ではなく、この模型間の比較がない。 |
| 1.2.4.2 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：ContinuousMap.HomotopyEquiv は通常の連続写像の両側 homotopy inverse を束ねる。CW 複体の compactly generated 写像空間での enriched equivalence とその HomotopyEquiv の iff を構成しないため、片側の概念の定義だけは数えない。 |
| 1.2.5.2 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：単一対象圏の nerve、位相弱同値述語、ループの連結成分を調べたが、π₀ が群である位相モノイド M に対する M → ΩBM の弱同値は見つからなかった。 |
| 1.2.5.4 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：quasicategoryCore は元の準圏から可逆辺を残す subcomplex である。位相 enriched C の対象を変えず Hom 空間を可逆成分に制限した C′ の enrichment と比較する型はなく、異なる対象の類似 core を数えない。 |
| 1.2.5.5 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：quasicategoryCore_kanComplex は絶対 core の Kan 性。族の relative core の射影と絶対 core の base-point 特殊化を同定する宣言がなく、原典が参照する Cartesian family の構成そのものの成分とはしない。 |
| 1.2.5.6 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：continuousKanReplacement とその弱同値単位は単体集合の fibrant replacement に相当する構成。具体的 Joyal ModelCategory と通常 Kan ModelCategory の恒等 Quillen adjunction、同じ cofibration 類、model localization の比較はない。置換だけを模型の局所化の partial にしない。 |
| 1.2.6.1 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：strictCoherentDiagram は通常の strict simplicial-enriched diagram を coherent nerve の図式に送る。原典は topological enrichment を入力し、特に豊穣同値 C′→C に沿う coherent lifting を述べる。topological base change とその lifting の比較がなく、別の模型の strict-to-coherent 射のみでは対応しない。 |
| 1.2.6.2 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：strictCoherentDiagram は厳密図式から整合図式への向きだけを与える。Kan 値の切断模型と余単位も読んだが、単体モデル圏で任意の整合図式を厳密図式と比較する一般の宣言は見つからなかった。 |
| 1.2.7.1 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：モデル圏の Cofibrant、通常図式からの nerve 比較、単体集合の整合解像随伴を調べたが、余ファイブラントな位相豊穣圏からの関手による代表の存在や積についての反例は見つからなかった。 |
| 1.2.7.3 | partial → partial | component | KB-W2原文・型再照合：仮定：任意の単体集合 K と準圏 C（HTT と一致）。結論：SSet.instQuasicategoryObjIhom により Fun(K,C) は準圏であり、(1) に一致。(2)(3) の HTT の H-enriched categorical equivalence と前合成同値述語の比較はこの検査には含まない。 |
| 1.2.9.1 | partial → partial | special | KB-W2原文・型再照合：仮定：普通圏 C の nerve と c に限定（Lean が強い特殊形）。結論：nerve(Over c) と準圏 sliceOver(nervePoint c) の実際の同型を得るので、naive overcategory が正しい slice を与えるという原典の存在する場合の明示例に一致。一般の topological/enriched C の naive approximation の基準は含まない。 |
| 1.2.9.3 | partial → partial | component | KB-W2原文・型再照合：仮定：準圏 C と任意の p:K→C（HTT と一致）。結論：sliceOver p の Quasicategory を得るので最初の assertion に一致。後半の任意 categorical equivalence q に対する slice 比較は含まず、trivial Kan fibration の別の十分条件もその代用にはしない。 |
| 1.2.10.1 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：IsFullyFaithful は右 pinched Hom の homotopy equivalence、IsEssentiallySurjective は二次切断 hS 内の VertexIso を用いる。任意 S の H-enriched hC[S] とこの通常 hS/Hom 模型の比較がなく、topological/simplicial enriched F に対しても同じ述語を運べない。定義の類似だけは数えない。 |
| 1.2.10.2 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：isFullyFaithful_comp_iff と IsEssentiallySurjective.comp は pinched-Hom/VertexIso の native 述語の合成則。原典の異なる模型間を往復した際に H-enriched hF の充満忠実性と本質的全射を保つ同じ比較がなく、合成則だけは原典の模型不変性の成分ではない。 |
| 1.2.11.1 | partial → partial | component | KB-W2原文・型再照合：仮定：準圏 C と頂点の集合（原典の full-subcategory 部分と一致）。結論：fullSubcomplexOnVertices は全頂点がその集合に属す単体を全て含む部分複体で、集合が spanned full subcategory を定める記述に一致。一般 fully faithful f の像への同値分解は含まない。 |
| 1.2.12.1 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：isTerminalVertex_iff_pinchedHom_isContractibleKan は slice-extension による strong terminal vertex と右 Hom の可縮性の比較。原典の H-enriched hC[S] あるいは位相 enriched hC の Hom と比較する宣言がなく、この異なる terminal 定義を同じ原典の定義としない。 |
| 1.2.12.2 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：QCatEquivalence.isTerminalVertex_iff は準圏の strong terminal vertex の native 同値に沿う不変性。原典の H-enriched hC の terminal object と模型間の比較が未供給なので、その invariant の片方だけを原典と同定しない。 |
| 1.2.12.5 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：pinched Hom の可縮性 iff strong terminal vertex は準圏内の定理。原典の任意の単体集合 C で strong-final⇒H-enriched final の向き、および準圏での H-enriched final の比較はない。単に「終対象」と呼ぶ別述語の iff を原典の主張の部分にしない。 |
| 1.2.12.7 | partial → partial | component | KB-W2原文・型再照合：仮定：通常圏 C と t（HTT と一致）。結論：IsTerminal t の存在 iff nerveVertex t が strong terminal vertex であるという終対象の部分を得る。始対象側と H-enriched hN(C) の terminal 定義との比較は含まない。 |
| 1.2.12.8 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：任意の単体集合の強終頂点述語と、準圏の同値に関する保存・反映を読んだが、準圏でない単体集合における強終頂点の非不変性を示す反例は見つからなかった。 |
| 1.2.13.1 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：representableHomotopyLimitComparison_discrete_homotopyEquivalence は単体 enriched C の strict Hom-limit から weighted comparison の homotopy equivalence を得る。原典の topological Hom の全 Y についての product comparison と同じ evaluation map の比較がなく、別模型の豊穣積の十分条件を原典の定義の特殊形にしない。 |
| 1.2.13.2 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：spacePullbackCone_isLimitCone は KanObject の strict pullback から coherent-nerve cone の普遍性を得る。原典の topological C の各 Hom の二写像と path の三つ組による homotopy-pullback space と同定する比較がなく、別の limit cone の存在を部分と数えない。 |
| 1.2.13.3 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：weightedCoherentConeSectionsComparison_homotopyEquivalence は単体 enriched 図式の weighted cone と section space の比較。原典の全 Y の topological Map(Y,X) あるいは Map(X,Y) が holim Hom を表す characterization と比較する宣言がなく、証明に用いる別の comparison の同値だけを部分としない。 |
| 1.2.13.6 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：spaceProductCone と spacePullbackCone は KanObject の coherent nerve での限界。topological enrichment から得る nerve と classical homotopy limit の同じ錐を比較していないので、別の模型での積・引戻しを原典の特殊形として残さない。 |
| 1.2.13.7 | partial → partial | component | KB-W2原文・型再照合：仮定：準圏間の fully faithful F と、像で余極限となる同じ余錐（原典の full inclusion の場合を含み、Lean が弱い）。結論：元の余錐は余極限なので、C 内の余極限が C′ に属せば C′ でも余極限という明記された帰結に一致。slice 全体の引戻し同一視は含まない。 |
| 1.2.13.8 | partial → partial | special | KB-W2原文・型再照合：仮定：準圏 C と図式 p（Lean が強い：スライスを定める q の始域 T が一点）。結論：底の余極限余錐を厳密に持ち上げ、与えた余錐が余極限かを射影で検出する（Lean が弱い：任意の T のスライスは含まない）。 |
| 1.2.14.1 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：FreeMonoid、単一対象圏、有限単体集合とコンパクト準圏の宣言を調べたが、一つの自己射で生成される自由準圏と離散無限 Hom を同定する宣言は見つからなかった。 |
| 1.2.14.2 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：CWComplex の有限型と有限空間の Kan 置換を読んだが、高次亜群の有限表示と有限胞体型を相互に与える比較は見つからなかった。 |
| 1.2.14.3 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：区間の写像空間と join での二対象図式、コンパクト対象の判定を調べたが、一方向の Hom の有限胞体型から二対象準圏の有限表示を判定する宣言は見つからなかった。 |
| 1.2.15.1 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：Cardinal.IsInaccessible と universe lift の型を調べたが、強非可到達基数の存在の独立性や、本の各定理でその仮定を除去する比較を述べる宣言は見つからなかった。 |
| 1.2.16.3 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：CWComplex、通常の実現と特異複体の随伴、SpaceInfinity を読んだが、CW の位相豊穣 nerve と SpaceInfinity の圏同値は見つからなかった。 |

## 読取りと再検索

原文・候補の型・現在の引用番号索引・小節ごとの現本体とロックMathlibの再検索はgit外の章別証拠。OE-W1 module-mapと宣言索引を使って移動後の名前・所在・行を確認した。ArchiveとBS draftsの宣言は正の根拠にしない。検索の全ヒットを形式検証したという意味ではない。
