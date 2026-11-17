# KB-W1 / B6 第1章

原文の項目と現在のソースの型による紙の再照合。Lean・ビルド・鍵は使っていない。

対象 69行。partial 40、none 29。判定後：none 50、partial 18、own 1。

既存 own・both・mathlib 111行の全既存フィールドは変更なし。既存7列の末尾に partial_kind を追加し、対象外行は空欄とした。区切り・改行と対象外行の既存引用符を保存した。verdict・axioms・check も変更していない。古いcheck欄は今回のkernel検査結果ではない。

## 全対象行の判定・変更一覧

状態不変でも型/原文の再判定を記録した。各 reason の詳細はCSVと同じ。原文全文・候補の型・検索はgit外の章別証拠。

| 番号 | 旧→新 | partial_kind | 理由 |
| --- | --- | --- | --- |
| 1.1.1.2 | partial → none |  | 原文は任意圏 C の半単体対象 SemiSimplexCategoryᵒᵖ⥤C を定義する。候補の型は半単体圏そのものの構造だけで、対象関手の定義・成分を直接与えない。圏の材料だけを partial に数えない。 |
| 1.1.1.4 | partial → partial | component | 原文は δ と (semi)simplicial object の面作用素を構成する。SimplexCategory.δ は Fin.succAboveOrderEmb による同じ δ、SimplicialObject.δ は X.map δ.op そのものなので、単体対象側の構成を直接与える。半単体対象側は含まない。 |
| 1.1.1.9 | none → none |  | 原文は面の関係式だけから半単体対象を一意に再構成する iff。現本体全体とMathlibを semi(s)implicial・SemiSimplex・nonunital bar で再検索。半単体圏と全Δの生成関係表示はあるが、面だけの関係式を入力に取る同じ関手の再構成宣言は見つからない。 |
| 1.1.2.10 | partial → partial | component | 原文の5条件中、degenerate_eq_iUnion_range_σ は退化作用素の像の和、mem_degenerate_iff は低次元への全射に沿う像との同値で、(1)と(3)の同値を定義の展開で直接与える。(5)の任意次元の非単射による因子化まで含めない。 |
| 1.1.2.12 | none → none |  | 原文は全射順序写像だけの圏Δsurjの記法・構成。Simplex/Surj・DeltaSurj・surjCategoryを現本体とMathlibで再検索。epi_iff_surjective等は個々のΔの射の判定で、全射のみを射とするこの圏の定義ではない。 |
| 1.1.2.13 | none → none |  | 原文は退化作用素の関係式からΔsurjᵒᵖ上の関手を一意に再構成する iff。退化作用素・全射単体圏・presentationを再検索。Δ全体の面と退化の生成関係や全射の補題から、同じΔsurj上の関手を作る追加の構成が要る。 |
| 1.1.3.1 | partial → partial | component | 原文は次元≤k・次元ちょうどk・有限次元を定義する。HasDimensionLT/LE の型は各上位次数の全単体の退化性で、非負kの上界および負kの空の場合を直接表す。次元ちょうど・有限次元の述語はこの引用にはない。 |
| 1.1.3.11 | partial → none |  | 原文は次元上界と任意図式/標準単体からの余極限表示の4条件の同値。hasDimensionLT_iSup_iff は部分複体の和、hasDimensionLT_of_epi は全射像の上界であり、原文の余極限図式・標準比較写像のどれも型にない。余極限と和/全射を結ぶ別の議論が要るため部品としてのみ記録。 |
| 1.1.3.14 | none → none |  | 原文は次元≤kの二対象間の同じ射fを低次数の全単射から同型とする。現本体とMathlibのDimension・truncation・isIsoを再検索。hasDimensionLT_iff_of_isoは逆向きの不変性、SkeletalDimension.stageIsoは骨格包含の別の射の同型。任意fの判定には当たらない。 |
| 1.1.4.6 | partial → none |  | 原文は skeleton の次元上界と、低次元 T からの包含による Hom 全単射。候補は S の非退化単体の所属と低次数の成分一致で、skeleton 自身の次元上界やこの Hom 写像の全単射を直接結論しない。非退化単体分解から組み立てる追加議論は partial に数えない。 |
| 1.1.4.7 | partial → none |  | 原文は skeleton が次元≤k の最大の部分複体。候補は一般の部分複体包含の判定と個々の低次元単体の生成部分複体の包含で、任意の次元≤kの部分複体を包含する結論ではない。最大性と次元上界を導く補助の段階に留まる。 |
| 1.1.4.8 | partial → none |  | 原文は全ての次数≤k の単体圏による標準余極限の単射性と像の skeleton との一致。isColimitCoconeN は全次数の非退化単体の別の添字圏から X 全体への余極限であり、有限次数制限した同じ射の結論ではない。 |
| 1.1.4.9 | partial → none |  | 原文は部分複体の k-skeleton 関手の小余極限保存。skAdj は切断から Truncated.sk への随伴で、SSet.sk と部分複体 skeleton の比較は同ファイルの TODO。異なる関手の随伴と保存から元の主張へは比較の証明が要る。 |
| 1.1.4.13 | partial → partial | component | 原文の境界からの面制限写像の単射性は boundary.hom_ext の型そのもの（n+1≥1）で直接得られる。image の整合条件について boundaryFaceGluing は境界次数n+2の構成を与えるが、全正次数を覆うとはしない。単射性という結論成分に限定する。 |
| 1.1.5.1 | none → none |  | 原文は次元0の充満部分圏からSetへのev₀の圏同値。dimension zero・discrete・HasDimensionLE 0で再検索。定数単体集合やΔ0の次元0のinstance、Hom対応はあるが、この充満部分圏とev₀の同値ではない。別のモデルの自由構成を同値の成分とは数えない。 |
| 1.1.5.5 | partial → none |  | 原文は任意圏の定数単体対象から X への自然変換を0成分で評価する指定写像の全単射。evaluationAdjunctionRight の左辺は Hom 添字の余積で作った evaluationLeftAdjoint で、定数対象ではない。初期対象0での比較同型と評価との整合を別に示す必要がある。 |
| 1.1.5.8 | partial → none |  | 原文の指定随伴は const⊣ev₀。evaluationAdjunctionRight は余積から作る別の左随伴、constLimAdj は const⊣lim で、いずれも同じ左右関手の随伴ではない。ev₀とlim、または左随伴とconstを同定する追加議論を数えない。 |
| 1.1.5.10 | partial → none |  | 原文は X がある定数単体集合と同型であるという離散性の述語。discrete:T↦const T は定数単体集合の構成であり、任意Xの離散性の条件ではない。別の構成を定義の部分と数えない。 |
| 1.1.5.11 | partial → partial | component | 原文の結論の一つは const:Set→SSet の充満忠実性。IsConnected J の下の const の Full/Faithful は J=SimplexCategoryᵒᵖ へ直接適用でき、その結論成分に対応する。本質的像を離散対象とする結論は引用に含めない。 |
| 1.1.5.14 | none → none |  | 原文は定数対象との同型・全作用の全単射・d₀の全単射・次元0の4条件の iff。discrete/次元0/作用素を再検索。定数対象のKan性や単位対象の次元0は、任意Xに対するこの同値の方向を直接与えない。 |
| 1.1.6.5 | partial → none |  | 原文の Graph の射は辺を頂点へ潰す場合を含む。Prefunctor の型は二つの quiver の頂点写像と辺から辺への写像、ReflQuiver は恒等辺のデータであり、原文の非退化辺と頂点の直和上の射ではない。反射的quiverとの対応を別に構成せず同じ主張と認めない。 |
| 1.1.6.8 | none → none |  | 原文は次元1のXからのHomと、退化辺を頂点へ潰すGraphの射の標準写像の全単射。graph/quiver/truncation/次元1を再検索。OneTruncation₂の反射的quiver構造、SchreierGraphの同値は別の対象・写像であり、この標準Hom写像ではない。 |
| 1.1.6.9 | none → none |  | 原文は次元≤1の充満部分圏とGraphの圏同値。graph equivalence・truncation・OneTruncationを再検索。反射的quiverの抽出だけで、原文の辺を潰せるGraphとの同値を返す宣言は見つからない。 |
| 1.2.1.1 | none → none |  | 原文はXの部分単体集合が別の部分単体集合と余積分解するというsummandの述語。summand/componentSubcomplex/成分因子化を再検索。成分類の逆像の部分複体はあるが、その包含をsummandとする条件/分解そのものの宣言ではない。 |
| 1.2.1.8 | partial → none |  | 原文は連結な直和成分としての部分単体集合と、その全体の集合を定義する。SSet.π₀ は辺の同値関係による頂点の商集合であり、この部分複体/直和成分の条件を型で与えない。二つのモデルの比較は追加の議論。 |
| 1.2.1.11 | none → none |  | 原文は連結なSからTへの写像の像を含む一意な連結な直和成分。componentSubcomplexと成分因子化を再検索し、選んだπ₀の部分集合の逆像の型を確認した。像を含む連結summandの一意性を返す型は見つからない。 |
| 1.2.1.12 | partial → none |  | 原文は連結性と全てのIについての指定定数写像 I→Hom(S,const I) の全単射の iff。homEquiv は別の Hom と関数集合の同値、isConnected_iff_nonempty_unique は π₀ の一意性との iff。指定写像の像と Hom 同値を結んで関数集合の判定を行う追加議論が必要で、いずれの方向も引用型が直接返すものではない。 |
| 1.2.1.13 | partial → none |  | 原文は S 自体の連結成分による余積分解。componentSubcomplex と componentClassEquiv は成分類の述語で選んだ部分複体のπ₀を計算するだけで、Sへの余積比較の同型を返さない。対象分解の証明の部品とする。 |
| 1.2.1.21 | partial → partial | component | 原文は π₀⊣const とその指定単位の構成。homEquiv の型 (X→discrete T)≃(π₀X→T) はこの随伴の Hom 同値成分を逆向きにしたものを直接与える。自然性・指定単位まで完成した Adjunction の宣言とせず、構成のこの成分に限定する。 |
| 1.2.1.24 | none → none |  | 原文は非退化辺だけのd₀,d₁の余等化子がπ₀であるという指定cofork。MathlibのisColimitCoforkπ₀は全ての辺を使う別のcofork。非退化辺・coequalizer・coforkを再検索したが、退化辺の除去を実装する同じ比較は見つからず追加議論を要する。 |
| 1.2.1.25 | none → none |  | 原文は全n≥2について∂Δnの連結性。boundaryとconnectedを再検索。KSTのboundaryReducedRealization_isConnectedはS構成の全零境界商、他のboundary connectingは連結準同型であり、標準単体の境界の連結性ではない。 |
| 1.2.1.26 | none → none |  | 原文は連結な単体集合の有限積閉性。IsConnected.prod・π₀とprodを再検索。CategoryTheory.IsConnected.prodは通常圏の連結性、KanKernelPairPiZeroLoopEquiv_productは特定のloop/kernel pairの式であり、SSet.IsConnectedの同じ有限積についての結論ではない。 |
| 1.2.1.27 | none → none |  | 原文はSSet.π₀Functorの有限積保存。π₀/piZero/productの再検索で、Kan置換や特定loopの比較は見つかるが、任意SSetのπ₀(X×Y)→π₀X×π₀Yという指定比較射の全単射/同型ではない。 |
| 1.2.3.1 | partial → none |  | 原文は指定u:S→Sing(Y)が全Xへの合成写像の全単射を満たすという任意Y,uの普遍性の述語。toTop と sSetTopAdj は標準の実現関手と随伴で、任意の指定uに対するその条件の定義ではない。標準単位の例と任意のuの述語を同一視しない。 |
| 1.2.3.7 | none → none |  | 原文は標準単体の下方閉な面族Uに対応する部分単体集合と台条件の位相部分空間を同時に構成する。toTop/Subcomplex/lowerSet/simplexで再検索。一般の部分複体やorder idealはあるが、このUからの二つの指定対象の構成は見つからない。 |
| 1.2.3.10 | none → none |  | 原文は下方閉な面族Uに対する単体部分複体からSing(台条件の部分空間)への指定比較が実現の普遍性を持つ。toTopとSubcomplex・lowerSetを再検索。標準単体全体のtoTopSimplexだけでは、任意Uへのこの制限射と普遍性を直接結論しない。 |
| 1.2.3.13 | none → none |  | 原文は任意の充満部分圏Uが単射沿いのpushout・単射列の余極限・単体の全余積で閉じれば全SSetを含むという帰納原理。induction/Subcomplex/relativeCellComplexOfMonoで再検索。相対セル分解は帰納原理の証明材料であり、このUへの所属を直接返す型ではない。 |
| 1.2.3.18 | none → none |  | 原文は任意Sの実現の弧状連結性・連結性・Sの連結性の3条件同値。toTopとConnected/π₀で再検索。標準位相単体だけの連結性や標準単体の弱同値は、任意Sの指定実現の同値の方向ではない。 |
| 1.2.3.19 | none → none |  | 原文は任意Sのπ₀と実現の位相的π₀の標準全単射。toTopとπ₀/componentを再検索。標準単体の位相的連結性とSSet側のπ₀の普遍性はあるが、両者を結ぶこの同じ比較写像は見つからない。 |
| 1.2.5.8 | none → none |  | 原文は全位相空間XのSing(X)のKan性。現本体全体・MathlibをtoSSet/singular/Kanで再検索。MathlibのSingularSet・KanComplexのTODOと、別のcompatible input unionのtoSSetはあるが、位相空間のsingular setのKan instanceは見つからない。 |
| 1.2.5.9 | partial → partial | special | 原文は全単体群の台がKan。ringSpace_kanComplex の型は単体的環 A の台のKan性であり、その加法単体群へ対象を限定した同じ結論を直接与える。全単体群への拡張は数えない。 |
| 1.2.5.11 | none → none |  | 原文は任意集合添字のKan積のπ₀の指定比較の全単射。π₀/piZero/product・IsConnected.prodを再検索。二項loop/kernel pairの成分式や通常圏の積連結性は異なる対象の主張で、この任意積の比較ではない。 |
| 1.3.2.7 | partial → partial | component | 原文の充満忠実な埋込みという結論は MonCat.toCat の Full/Faithful と nerveFunctor の FullyFaithful の合成から直接得られる。さらに monoidWordEquiv は実際のモノイドの神経の n 単体を Fin n→T に同定する。任意SがSegal条件からその本質的像に入る逆は含めない。 |
| 1.3.2.12 | none → none |  | 原文は単位を仮定しないモノイドの半単体的barとその面の式。semi-simplicial/nonunital barを再検索。通常のMonCatのmonoidWordEquivは単位を持つ圏のnerveであり、非単位的モノイドの同じ半単体関手の構成ではない。 |
| 1.3.2.14 | none → none |  | 原文は非単位的モノイドのbarの半単体集合への充満忠実性と本質的像。nonunital bar/semisimplicialで再検索。単位付きモノイドを通常の圏の神経へ埋める宣言と、その対象上のSegal座標だけでは、原文の別の始域・終域の関手の結論を直接与えない。 |
| 1.3.4.1 | partial → none |  | 原文の特徴づけは全ての内hornの一意充填との iff。nerve の StrictSegal は spine 座標の全単射で、引用型には内hornの一意充填もその逆の再構成もない。StrictSegalから任意内hornの充填・一意性へ移す証明を要するため、必要方向と数えない。 |
| 1.3.4.2 | partial → partial | stronger-hyp | 原文は任意圏の nerve の内hornの一意充填。Quasicategory 性から充填の存在、thinNerve_hom_ext_horn から2次元以上の任意horn制限の単射性を直接組み合わせ、Quiver.IsThin C を追加した場合の同じ一意充填を得る。一般圏の一意性はこの引用にない。 |
| 1.3.4.3 | none → none |  | 原文は一意内horn充填を持つ二つのSSet間のfを頂点・辺の全単射から同型とする。nerve/isIso/Segal/bijectiveで再検索。nerveAdjunctionの余単位の同型や特定のnerve比較は別の射で、任意のこのfに対する判定ではない。 |
| 1.3.6.1 | partial → none |  | 原文は任意の指定u:S→N(C)が全Dへの合成でHom全単射を満たすという普遍性の述語。hoFunctorとnerveAdjunctionは標準のモデルと随伴で、任意uに関するこの述語そのものではない。標準モデルの構成を別の定義の一部とはしない。 |
| 1.3.7.5 | partial → none |  | 原文は指定u:G_•→N(Path[G])によるHom全単射。Paths.lift はquiverの前関手を道の圏へ延長するだけで、単体集合G_•からの射との同定や指定uとの合成を型に持たない。追加の比較が必要な証明部品。 |
| 1.3.7.7 | partial → none |  | 原文は任意圏CがあるPath[G]と同型という自由性の述語。Pathsは対象型の別名とその道の圏構造を作る構成であり、その述語の直接の宣言ではない。 |
| 1.3.7.8 | none → none |  | 原文は圏の非恒等射の全ての2因子分解でどちらかが恒等となるというindecomposableの述語。indecomposable morphism・Paths/freeCategoryで再検索。対象の非直和分解性や自由道の長さは別の述語で、この任意圏の射の定義は見つからない。 |
| 1.3.7.11 | none → none |  | 原文は自由圏・既約射グラフからの標準関手の同型/同値/充満忠実性・既約分解の一意性の5条件 iff。freeCategory/Paths/indecomposableで再検索。Paths.liftの延長普遍性だけでは、原文の既約射グラフと指定関手を直接扱わず追加構成を要する。 |
| 1.4.2.1 | partial → partial | component | 原文には有限線形順序の双対と、Δ上のOp([n])=[n], Op(α)(i)=n−α(m−i)の構成がある。SimplexCategory.rev は Fin.rev による同じΔ上の関手を直接定義するのでこの成分に対応する。空の順序も含むLin全体の比較同値は含めない。 |
| 1.4.3.7 | partial → partial | direction | 原文は辺のホモトピーと両側が恒等辺の正方形の存在の iff。exists_arrowHomotopy_of_homMk_comm に a,b を恒等辺として適用すると、同じ辺のホモトピー圏での一致から指定した両側を保つ正方形ホモトピーが直接得られる。逆向きを含む iff の宣言ではない。 |
| 1.4.5.6 | partial → partial | component | 原文は各n単体をホモトピー類の射列へ送るu:C→N(hC)を構成する。nerveAdjunction の単位成分の型はまさにこの始域・終域の単体写像を直接与える。2切断の homToNerveMk の式は頂点と辺を同じ類へ送る。全nの指定座標の式を照合済みとせず、標準写像と0・1成分に限定する。 |
| 1.5.2.5 | none → none |  | 原文は薄い非巡回の有向グラフ上の圏値図式で全ての道の合成が等しいという可換性の述語。acyclic graph/commutative graph/FreeQuiverCoverで再検索。自由quiver被覆の図式やhomotopy fiberは別の構成で、この述語ではない。 |
| 1.5.2.6 | none → none |  | 原文は指定された薄い非巡回グラフの頂点の順序・標準包含・可換図式の一意延長。acyclic graph/FreeQuiverCoverを再検索。特定scaffoldのbridgeやfree quiver coverのnerveは元の任意グラフの同じ包含ではなく、3結論の成分を直接返さない。 |
| 1.5.3.5 | partial → partial | special | 原文のρSは全次数の単体集合の同型。nerveAdjunction.homEquiv はhS→Dの関手とS→N(D)の全単射で、ρSの0単体（次数0に限定）の同じHom対応を直接与える。全次数・面退化の可換性までは含まない。 |
| 1.5.4.13 | partial → partial | component | 原文のweakly saturatedの条件は押し出し・retract・超限合成で閉じること。三つの IsStableUnder… の型はこの各条件を直接表し、弱飽和性の述語の成分に対応する。三条件をまとめた名前付きの述語や生成閉包そのものと同一視しない。 |
| 1.5.5.5 | partial → partial | component | 原文(a)の切断の存在はexists_sectionの型の結論そのもの（TrivialKanFibrationの全単射RLPを適用）。(b)の指定向きのfiberwise収縮について、引用のexists_vertical_contractionはid→p≫sと逆端点順なので一致としない。(a)だけを数える。 |
| 1.5.5.6 | partial → own |  | 仮定：単射i:A→Bとtrivial Kan fibration p:E→Y（原文と一致）。結論：trivialKanFibration_pullbackObjObjπ は internalHom.PullbackObjObj i p の標準比較射πがtrivial Kan fibration（原文のθと一致）。引き戻しの選択をデータとして明示し、A=空に限定しない。模型圏の追加仮定なし。 |
| 1.5.5.11 | partial → none |  | 原文は始域XのKan・可縮Kan・準圏性を終域Yへ移す3結論。候補の二型は終域の性質を始域へ移す逆の主張で、同じpに対するいずれの結論成分も直接返さない。反対向きに使うには別の議論が必要。 |
| 1.5.6.1 | partial → partial | direction | 原文の(1)⇒(2)は、innerAnodyneExtensions.horn_ι でΛ²₁の包含を指定し trivialKanFibration_pre_of_innerAnodyne に適用して直接得られる。単一の制限射の自明Kan性⇒準圏性の逆向きはこの型に含まない。 |
| 1.5.6.8 | none → none |  | 原文はnerveであることと全inner anodyneに沿う一意延長の iff。innerAnodyne/unique/nerveを再検索。scaffoldやsequential telescopeの特定の包含のinner anodyne性は、一意延長を全inner anodyneで結論する型ではなく、別の射の類似としてのみ記録する。 |
| 1.5.6.9 | partial → partial | component | 原文(a)の単射とΛ²₁包含のpushout-productのinner anodyne性は、innerAnodyneExtensions_pushoutObjObjι に horn_ι を渡した同じ比較射について直接得られる。(b)のこの生成系だけによる弱飽和生成は含めない。 |
| 1.5.7.1 | partial → none |  | 原文は任意のGの指定射G_•→N(Path[G])による制限。候補はsequentialSpine⊂N(ℕ)という別の明示された射のinner anodyne性と一般の前合成定理。これを原文の鎖グラフの指定射と同定する比較は引用型にない。単に可算の類似としてspecialにしない。 |
| 1.5.7.3 | partial → none |  | 原文はグラフの標準射G_•→N(Path[G])のinner anodyne性。sequentialSpineの包含は始域の部分複体と標的が別に定義された射で、同じグラフの標準射との同定が未提示。別の射についての類似の結論は§8.1ではnone。 |
| 1.5.7.9 | partial → partial | direction | 原文の必要方向について、Nerve.strictSegal/IsStrictSegalはnerveのn単体からn本の可合成辺列（spineの射）への全単射を直接与える。Sの一般の再構成はTODOなので、spineの一意延長条件からnerveとの同型を作る逆方向は含めない。 |

## 検査

原文は Kerodon 公式小節の各項目Tagで照合。none は現本体・ロックしたMathlibを再検索し、近隣項目のソース・双対/限定版の候補も照合した。Archiveの宣言をown・partialの根拠にはしていない。宣言の存在と型はソースでの確認で、kernel確認ではない。
