# KB-W1 / B6 第7章

原文の項目と現在のソースの型による紙の再照合。Lean・ビルド・鍵は使っていない。

対象 473行。partial 299、none 174。判定後：none 318、partial 145、own 10。

既存 own・both・mathlib 46行の全既存フィールドは変更なし。既存7列の末尾に partial_kind を追加し、対象外行は空欄とした。区切り・改行と対象外行の既存引用符を保存した。verdict・axioms・check も変更していない。古いcheck欄は今回のkernel検査結果ではない。

## 全対象行の判定・変更一覧

状態不変でも型/原文の再判定を記録した。各 reason の詳細はCSVと同じ。原文全文・候補の型・検索はgit外の章別証拠。

| 番号 | 旧→新 | partial_kind | 理由 |
| --- | --- | --- | --- |
| 7.1.1.1 | partial → none |  | 引用はjoin錐のsliceの終対象性とright-fibration evaluation、余錐のcosliceの始対象性。原文の定値関手へのHomから指定自然変換との合成という同じ写像を比較する型がなく、別の評価の同値判定だけを定義の成分とはしない。 |
| 7.1.1.12 | partial → none |  | HasLimit pは図式に対する極限錐の存在で、原文の指定したYを頂点とする自然変換の存在を直接述べない。join錐と指定自然変換の比較もこの型にはない。 |
| 7.1.1.13 | partial → partial | direction | limitVertexIsoは原文のX,Yがともに同じuの極限ならX≅Yという極限側の向きを直接返す。任意の同型な頂点に極限錐を厳密に持ち上げる逆は含まない。 |
| 7.1.1.14 | partial → partial | component | limitVertexIsoとcolimitVertexIsoは原文のlim/colimの同型類が図式だけで定まるという一意性を直接与える。任意の存在証明からの記法としての選択は含まない。 |
| 7.1.1.15 | partial → partial | component | HasLimitを全p:K→Cで量化すると原文のK-indexed limitsの条件を直接表す。名前付き述語の有無は理由とせず、colimits側は引用にないため数えない。 |
| 7.1.1.16 | partial → partial | component | HasFiniteLimits・HasSmallLimits・HasSmallColimitsはそれぞれ原文の有限極限・小極限・小余極限の存在条件を直接表す。有限余極限と任意の形状族の全定義は含まない。 |
| 7.1.1.18 | partial → partial | component | constantFunctorMapは原文の同じ対角δの実際の射を直接構成する。任意Tの左右随伴によるlimit/colimit functorという二つの述語全体は引用のchosenColimitFunctorだけからは得ない。 |
| 7.1.1.19 | partial → partial | component | chosenColimitAdjunctionは全てのK図式の余極限が存在すれば同じ対角に左随伴が存在するという余極限側の方向を直接返す。極限側と逆は含まない。 |
| 7.1.2.1 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：∞圏の join 錐の極限性はある。豊穣圏の cotensor や presentable 圏の tensor とは別に、任意の∞圏で指定 e:K→Hom(X,Y) から作る普遍性の述語は見つからない。 |
| 7.1.2.5 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：錐の頂点同型は同一の図式に対する極限性から得る。指定 e が冪を与えるときの X の一意性や Yᴷ の構成は見つからない。 |
| 7.1.2.8 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：豊穣写像空間と coherent nerve の比較候補を探した。与えた e が豊穣冪を表すことと nerve 側で冪を表すことの iff は見つからない。 |
| 7.1.2.11 | partial → none |  | presentable圏のtensorSpaceFunctorは、原文の指定κの空間部分圏でeが点のcopowerを表すことと弱ホモトピー同値のiffではない。対象・射・濃度が異なる。 |
| 7.1.2.15 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：一般の極限性の述語はある。大きい添字集合による自己冪の存在を、順序集合の nerve と同値であることと比較する型は見つからない。 |
| 7.1.2.16 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：極限錐と DG nerve の写像空間の型を探索した。正規化鎖からの f が冪を表す条件を DG 側と nerve 側で比較する型は見つからない。 |
| 7.1.2.18 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏で単体的対象の正規化複体はある。係数 A の正規化余鎖を DG nerve 内の指定された余積・極限として特徴付ける型は見つからない。 |
| 7.1.3.1 | partial → none |  | sliceの終対象とその評価の同値判定だけでは、原文の定値対角とuによる指定oriented fiber productの対象αに直接移せない。laxSlice/錐の族の比較はあるが、この指定fiber productとの同定を引用型に含まない。 |
| 7.1.3.2 | partial → none |  | 引用は全ての共変表現可能関手で極限を検出するiff。原文の一つのYが指定right fibrationを表現するという(2),(3)への比較を直接与えない。 |
| 7.1.3.3 | partial → partial | component | HasLimitとIsLimitConeを展開すると同じslice C_/uに終対象が存在するという原文(1)⇔(3)。oriented fiber productの条件(2)は含まない。 |
| 7.1.3.15 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：任意の join 錐の極限性は定義される。終頂点の指示写像 Q で指定された立方体の制限を比較する極限判定は見つからない。 |
| 7.1.3.17 | partial → partial | component | coneIteratedSliceIso_restrictionはC_/cからC_/pへの同じ制限射を(sliceOver p)_/cの射影に同型で対応させる。isLimitCone_iff_trivialKanFibrationをこの同じ射に移せば原文(1)⇔(2)を直接得る。(3),(4)からの逆は含まない。 |
| 7.1.3.18 | partial → partial | stronger-hyp | ρを全錐図式のFunctorIsoと強めるとIsLimitCone.of_functorIsoは同じ全図式の極限性を移し、原文(1)⇒(2)を直接与える。K上の各成分だけの可逆性からの全二取三は含まない。 |
| 7.1.3.19 | partial → own |  | 現本体SquareFunctorTransportのIsLimitCone.of_functorIsoとIsColimitCone.of_functorIsoは全錐／全余錐のFunctorIsoで極限性／余極限性を保つ。逆は同じ同型のsymmに適用するだけで、原文の二つのiff全体を直接得る。slice内の同型だけという従来の理由を訂正。 |
| 7.1.4.1 | partial → partial | component | mapJoinCone F cの極限性は原文前半の同じlimit diagramをFに後合成した極限性そのもの。専用のpreservedという述語名がないことは不足とせず、colimit側の構成は引用に含まない。 |
| 7.1.4.4 | partial → partial | component | PreservesSmallLimits/Colimitsを固定した小形状Kに評価すると、同じ図式・錐の後合成を保存する原文条件を直接得る。任意の大きさのKについての全定義ではない。 |
| 7.1.4.5 | partial → partial | component | PreservesSmallLimitsは原文の小極限保存の定義を直接表す。PreservesFiniteCoproductsは有限余積のみで有限余極限全体とはしない。 |
| 7.1.4.14 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：一般の極限性と右ファイブレーションの別々の述語はある。n-truncated なファイバーと (n+1)-connective な添字を同時に課す保存反映の iff は見つからない。 |
| 7.1.4.15 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：頂点上のスライスの射影で余極限性を比較する双対側はある。対象 X の n-truncated 性と添字の connectivity を使う極限版は見つからない。 |
| 7.1.4.17 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏のスライス引き戻し関手は向きが逆。原文の f₊ による n-truncated 射上の極限性の iff は見つからない。 |
| 7.1.4.18 | partial → partial | direction | 与えられた極限錐cの存在証人にIsQCatEquivalence.isLimitCone_iffの順方向を適用し、原文(1)の存在の順方向を直接得る。添字前合成の存在iffは終域同値の逆方向の代用にしない。 |
| 7.1.4.19 | partial → partial | stronger-hyp | C,Dの一方が全小極限／全小余極限を持つと強めればHasSmallLimits.of_equivalenceとHasSmallColimits.of_equivalenceは、同じ小形状Kについて他方の存在を直接与える。逆はe.symm。Kだけの存在からの一般の比較は含まない。 |
| 7.1.4.21 | partial → partial | component | 原文のK-indexed limitsの存在から証人dを取り、保存性でhFdを得ればisLimitCone_of_conservative_imageは同じcの像から極限性を反映する。順方向は入力の保存性であり、極限側のiff全体が直接従う。余極限側は含まない。 |
| 7.1.4.22 | partial → partial | direction | isLimitCone_of_conservative_imageは原文と同じ保存された証人dと保守性の下で、F(c)が極限ならcが極限となる方向を直接返す。逆をこの引用型だけには含めない。 |
| 7.1.4.23 | partial → none |  | MathlibのCreatesLimit/CreatesColimitは通常圏の錐とその同型による持ち上げ。原文の任意単体形状Kのjoin錐と同じ保存された極限図式へのnerve比較がない。 |
| 7.1.4.25 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の CreatesLimit はある。原文の K 上の極限存在と保存の連言との iff は∞圏の型では見つからない。 |
| 7.1.4.26 | partial → partial | special | A=Δ⁰、fが頂点の場合、sliceOver_hasColimit_of_projectionで余極限錐を取り、sliceOver_isColimitCone_iff_projectionで同じ錐の像の余極限性を直接得る。原文(2)のこの場合のみで、一般Aと(1)は含まない。 |
| 7.1.4.27 | partial → partial | special | A=Δ⁰かつCが全小余極限を持つ場合、sliceOver_hasSmallColimitsは同じsliceの各小Kの余極限存在を直接返す。一般Aでのcosliceの錐の持ち上げは極限性まで述べず、両側のiff全体は含まない。 |
| 7.1.4.29 | partial → partial | stronger-hyp | Cが全小余極限を持つと強めればreflectiveSubcategory_hasSmallColimitsは同じ反射的full subcategoryで指定の小図式uの余極限存在を直接与える。一図式だけの周囲での存在からの一般化は含まない。 |
| 7.1.4.31 | partial → partial | stronger-hyp | 周囲のCが全小余極限を持つと強めると、reflectiveSubcategory_hasSmallColimitsは同じ反射的部分圏について指定小Kの全図式の余極限存在を直接返す。 |
| 7.1.4.33 | partial → partial | component | reflective_isLimitCone_iff_inclusionは原文の既存極限錐の包含による保存・反映を直接与える。さらにPの同型閉性を加えるとmem_limitConeとfullSubcomplex_hasLimit_of_apexで同じ図式の存在も移る。任意Pの存在反映は含まない。 |
| 7.1.4.34 | none → partial | stronger-hyp | 部分圏をrepleteにも強めるとreflective_mem_limitConeの空添字の場合は同じ終頂点Xが部分圏に属すると直接返す。原文最後のrepleteの場合の結論に一致し、任意のreflective部分圏は含まない。 |
| 7.1.4.35 | partial → partial | stronger-hyp | 周囲の全小極限／余極限の存在を加え、極限側はPの同型閉性も加えると、二つのreflectiveSubcategory_hasSmall*は同じ部分圏の指定小Kでの存在を直接返す。Kだけの存在の一般形ではない。 |
| 7.1.5.10 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：相対始性は retract に沿って移る。像の同型を仮定した指定辺で、二頂点の相対始性と辺の可逆性の三条件を比較する型は見つからない。 |
| 7.1.5.11 | partial → partial | stronger-hyp | Uをinner fibrationに強め、相対始／終性をInitial/TerminalBoundaryLiftingで持つ場合、of_vertexIsoと同じeのsymmを使えば指定頂点X,Yの両方向の移送を直接得る。任意のUの写像空間による相対性への比較は含まない。 |
| 7.1.5.12 | partial → partial | stronger-hyp | Uをinner fibration、相対始性をInitialBoundaryLiftingに強めると、relativeInitialVertexIsoは原文のU(X)≅U(Y)からX≅Yを同じ二頂点について直接返す。逆は頂点同型のmap。一般Uへの比較は含まない。 |
| 7.1.5.13 | partial → none |  | adjunctionOfRelativeInitialSectionは厳密sectionと境界充填から随伴を構成するが、原文のcoreflective localizationに要る左随伴の充満忠実性を結論しない。随伴だけは同じ結論の十分条件にならない。 |
| 7.1.5.14 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：相対始頂点の述語はある。その全頂点が張る部分圏への制限が同値で、任意の射の coreflection 性を特徴付ける型は見つからない。 |
| 7.1.5.15 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：全空間の相対始性からファイバーの始性を得る。各ファイバーに相対始対象があることによる coreflective localization の iff は見つからない。 |
| 7.1.5.16 | partial → partial | stronger-hyp | Uをinner fibrationに強めると相対始性をInitialBoundaryLiftingへ移せ、relativeCosliceMap_trivialKanFibration_of_initialBoundaryLiftingは原文(1)の同じ相対coslice比較を自明Kan、従って圏同値と直接返す。逆と相対終側は含まない。 |
| 7.1.5.17 | partial → partial | component | kanRelativeInitialVertex_iff_initialBoundaryは原文(1)⇔(3)、相対cosliceの補題は(3)⇒(2)を同じU,Yで直接返す。三条件の全同値は含まない。 |
| 7.1.5.18 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：自明 Kan ファイブレーションは一頂点からの coslice 比較に対するもの。相対始頂点の充満部分圏の制限とは異なる。 |
| 7.1.5.19 | partial → partial | stronger-hyp | Fもinner fibrationと強めれば、相対始性と境界充填のiffをFとfiberのF_Eに適用できる。total→fiberとcartesian辺保存下のfiber→totalの二型が原文の同じ頂点の結論を返す。任意Fには及ばない。 |
| 7.1.5.22 | partial → none |  | fiberの始対象から境界充填、厳密sectionから随伴を作る型だけでは原文(2)の左随伴の充満忠実性と一般のfiber条件からのsectionの選択を直接返さない。証明の部品のみ。 |
| 7.1.6.9 | partial → none |  | 引用は相対余極限余錐のFunctorIsoでの不変性。原文は相対極限錐であり、relative limit/reverseCoconeの比較はあるが、指定した全錐のFunctorIsoを反転余錐へ移す型を引用に含まない。双対の類似だけでは数えない。 |
| 7.1.6.10 | partial → none |  | 引用はU,V自身の相対始頂点の合成と取消し。原文は図式のslice/coslice後合成に関する相対極限／余極限であり、その合成射・写った錐との比較を欠く。 |
| 7.1.6.11 | partial → partial | stronger-hyp | Vをtrivial Kan fibrationに強めればkanIsRelativeColimitCone_comp_iff_of_trivialKanFibrationは原文(2)の同じ余錐についてのiffを直接返す。一般の充満忠実Vと極限側は含まない。 |
| 7.1.6.12 | partial → partial | component | Uをinner fibrationに強め、相対余極限からKanRelativeCoconeLiftingへのiffを使えば、kanIsColimitCone_of_relativeLifting_of_imageは原文(2)の相対余極限と像の余極限から元の余極限を直接返す。極限側と逆は含まない。 |
| 7.1.6.13 | partial → none |  | 引用は余錐族の相対始性と相対余極限。原文は錐の関手圏の指定相対制限への相対終性であり、同じ射・対象ではない。 |
| 7.1.6.14 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：相対極限錐の述語はある。指定した底上の関手空間の制限のファイバーで終対象となる iff は見つからない。 |
| 7.1.6.15 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：底上の関手空間は構成される。指定された制限ファイバーの可縮性による U-極限性の iff は見つからない。 |
| 7.1.6.17 | partial → none |  | 引用は相対joinのfiberごとの余極限図式からの制限。原文の全極限錐のfull subcategoryからFun(K,C)への制限と違う対象・射。 |
| 7.1.6.19 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：余錐族の相対始性を使う双対の判定はある。任意の錐と定値錐からの Hom の四角形のホモトピー引き戻し性との三条件の iff は見つからない。 |
| 7.1.6.20 | partial → none |  | 初期境界充填からのpinchedHomMap同値は始点固定の射、原文は終点に極限図式を固定する制限作用。terminalBoundaryの極限判定だけではその同じ全Hom制限の同値まで直接結論しない。 |
| 7.1.7.4 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の極限創出はある。弱可縮な K に対し左ファイブレーションで余極限、右ファイブレーションで極限を創出する型は見つからない。 |
| 7.1.7.5 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：一図式の余極限存在は定義される。弱可縮な K の底の存在から全空間の存在と射影の保存を同時に得る型は見つからない。 |
| 7.1.7.6 | partial → none |  | KanRelativeInitialVertex.pullback_sndは対象の相対始性の底変換。原文は相対余極限図式で、図式のcoslice後合成の底変換との同定を引用に含まない。 |
| 7.1.7.7 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：相対始頂点の厳密引き戻しの型はある。任意の categorical pullback で指定 K▷ 図式の相対余極限性を反映する型は見つからない。 |
| 7.1.7.8 | partial → none |  | InitialBoundaryLifting.isInitialVertex_fiberは一つの相対始頂点のfiber内での始対象性。原文の余錐全体のfiber内の余極限性へのcoslice・fiber交換の比較が引用の可換式だけからは得られない。 |
| 7.1.7.9 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：相対余極限性の述語は全体の coslice に基づく。出る全辺 e の Δ¹×_C E 上での余極限を量化した定義は見つからない。 |
| 7.1.7.14 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：個別のファイバーの相対始性を全空間へ移す境界充填補題はある。出る各辺上での余極限条件との iff は見つからない。 |
| 7.1.7.15 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：相対始頂点をファイバー内の始頂点に移す。locally cartesian な仮定で指定ファイバー図式の余極限性を相対余極限性と比較する型は見つからない。 |
| 7.1.7.16 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：全空間の相対余極限性の定義はある。ファイバー内の余極限と各辺の輸送による保存の連言を使う iff は見つからない。 |
| 7.1.7.18 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：相対始頂点に関する単一の引き戻しは扱う。二つの引き戻しと cartesian な対角を仮定して相対余極限を G で運ぶ型は見つからない。 |
| 7.1.8.3 | partial → own |  | hasColimit_of_hasPointwiseColimitsは原文(1)、現本体のisColimitCone_iff_pointwise_of_hasPointwiseColimitsは同じ指定余錐の原文(2)のiffを直接返す。両者を合わせれば結論全体で、従来引用の極限側の補題は不要。 |
| 7.1.8.4 | partial → partial | component | FをcurryしたfにhasColimit_of_hasPointwiseColimitsとisColimitCone_iff_pointwise_of_hasPointwiseColimitsを適用すると、原文(1)と(2)を同じ関手圏で直接得る。(3)の二段余極限と全体の余極限の比較は含まない。通常圏のFubini同型をその∞圏版と同一視しない。 |
| 7.1.8.5 | partial → none |  | MathlibのFubini同型は通常圏の余極限。同じnerve上の∞圏の二段余極限との比較がなく、通常圏の類似公式だけを特殊形として数えない。 |
| 7.1.8.6 | partial → none |  | MathlibのIsColimitは通常圏の積添字の図式。原文の任意単体形状での∞圏の余極限存在と同じ対象・錐であるnerve比較がない。 |
| 7.1.8.7 | partial → none |  | 一般の部分複体の初頂点境界充填の持ち上げはあるが、原文の指定積・pushoutからの射を相対cocone制限の問題へ移す比較と同じf上での等式を引用型に持たない。 |
| 7.1.8.8 | partial → none |  | 点ごとの相対cocone充填をFunctor圏へ移す型と一般の持ち上げ型だけでは、原文の各bに指定された余錐f_bを厳密に保つ同じ全体の持ち上げを直接返さない。 |
| 7.1.8.10 | partial → partial | stronger-hyp | Fをinner fibrationに強めると各F-colimitをKanRelativeCoconeLiftingへ移せ、relativeFunctor_of_first_verticesが同じ相対内部Hom比較πで充填性を返す。πもinnerなので同じF′-colimitへ戻る。任意Fの場合は含まない。 |
| 7.1.8.11 | partial → none |  | 引用の射sj.πはUを含む相対内部Hom比較。原文の単なるpre(A⊆B)への相対余極限性と同じ射に同定する型を欠く。点ごとの絶対充填を移す補題だけではこの指定相対結論は直接出ない。 |
| 7.1.8.13 | partial → partial | stronger-hyp | Fをinner fibrationに制限すると引用のhfの型は全bで同じ評価余錐がF-colimitであるという原文の条件をそのまま表す。inlineの∀で表すこと自体は不足としない。任意Fの条件全体は引用の型の範囲外。 |
| 7.1.8.14 | partial → partial | stronger-hyp | Fをinner fibrationに強めるとkanIsRelativeColimitCone_functor_of_pointwiseは同じ後合成F^Bと転置余錐について原文の相対余極限性を直接返す。 |
| 7.1.9.1 | partial → partial | component | 四角を厳密pullback、一方をEquivalenceLiftingとし、両側の全小余極限と両関手の保存を仮定すると、引用は同じpullback図式の余極限の存在と両射影の成分判定を直接返す。categorical pullback一般・Kだけの仮定ではない。原文第一結論の印字はC、型の結論はC₀₁なのでこの部分は一致と数えない。 |
| 7.1.9.2 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：普通の関手圏での点ごとの余極限判定はある。向き付きファイバー積で一方の合成が余極限のときに二射影で判定する型は見つからない。 |
| 7.1.9.3 | partial → partial | stronger-hyp | 原文の三条件にF₁∘ev₁による同じ余錐の余極限性も追加するとisColimitCone_laxPullback_of_componentsは同じoriented fiber productの余極限性を直接返す。 |
| 7.1.9.4 | partial → partial | component | F₁側の選んだ余極限も保存されると追加すればexists_colimitCone_laxPullback_with_componentsは同じqの余極限と両成分が指定余錐となる等式を直接返す。追加保存なしの存在と任意延長のiff全体は含まない。 |
| 7.1.9.5 | partial → partial | special | Kを有限に限り、両側が全有限余極限を持ちF₀,F₁両方が保存すると強めれば、hasFiniteColimits_laxPullback_of_preservationと有限成分判定は原文と同じoriented fiber productについて存在とiffを直接返す。 |
| 7.1.9.7 | partial → none |  | 引用の対象は一方がisofibrationの厳密pullback。原文のhomotopy fiber productとの比較同値・指定図式をその比較に沿って移す型が引用にないため、別模型の類似としてnone。 |
| 7.1.9.8 | partial → partial | component | 四角を厳密IsPullback、F₀をinner fibrationに強めればisColimitCone_of_isPullback_of_componentsは原文の成分条件から同じqbarが余極限という方向を直接返す。一般categorical pullbackでの存在とiff全体は含まない。 |
| 7.1.9.9 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：Kan 複体の塔の空間圏での極限は扱う。isofibration の∞圏の塔で各段の指定余極限を両立させる型は見つからない。 |
| 7.1.9.10 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：二脚の厳密引き戻しで小余極限の存在を扱う。isofibration の塔の極限に任意の固定形状の余極限を移す型は見つからない。 |
| 7.1.10.1 | partial → none |  | Fun(C,D)の点ごとの余極限と相対内部Hom後合成はあるが、原文の指定section空間をtrivial bundleのFunctor空間へ比較する同型を引用型に含まない。別対象の結果としてnone。 |
| 7.1.10.2 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：全関手圏の各点での余極限から HasColimit を得る。局所 cartesian な非定値ファイバー上の切断と評価に関する主張は見つからない。 |
| 7.1.10.3 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：定値ファイバーに当たる全関手圏の iff はある。辺に沿う輸送が各余極限を保つ仮定での非定値版は見つからない。 |
| 7.1.10.4 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：相対余極限の述語はある。各ファイバーの余極限が edgewise であることを仮定して、全切断の余極限を作る型は見つからない。 |
| 7.1.10.5 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：小余完備性を図式ごとに量化する述語はある。全ファイバーの固定 K-余完備性から locally cartesian な切断の余完備性を得る型は見つからない。 |
| 7.1.10.7 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：小余極限保存はある。各辺の輸送による K-余極限保存から切断の K-余完備性と点ごとの判定を得る型は見つからない。 |
| 7.1.10.8 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：全関手圏では点ごとの余極限性から余極限性を得る。inner fibration 上の切断の評価で edgewise 条件を使う版は見つからない。 |
| 7.2.1.4 | partial → partial | direction | roofTerminalPoint_isRightCofinalは終対象Xの点包含がright cofinalというiffの向きを直接返す。任意準圏の逆とleft側のiff全体は含まない。 |
| 7.2.1.5 | partial → partial | component | IsLeftCofinal.isWeakHomotopyEquivalenceとRight版は原文(1)の両場合を同じfについて直接返す。Kan終域と弱同値からの逆(2)は含まない。 |
| 7.2.1.7 | partial → own |  | 左右それぞれのcofinal/anodyneのmono判定とIsLeft/RightCofinal.cancel_leftを同じf,gに適用すれば、原文の二つのanodyne消去則を直接得る。専用のanodyne_cancelという名前の不足はpartial理由にしない。 |
| 7.2.1.9 | partial → partial | special | Cを一点、Dを通常圏Iのnerve、Fを点包含に制限すれば、通常の始対象cに対するnervePoint_isLeftCofinalは原文の「始対象の像が始対象ならFはleft cofinal」という向きを直接与える。一般のFのiffは含まない。 |
| 7.2.1.10 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：局所化の述語と自明 Kan ファイブレーションから両余終性を得る補題はある。任意の指定辺を反転する局所化写像に両余終性を与える型は見つからない。 |
| 7.2.1.11 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：辺の局所化と左ファイブレーションに沿う右余終性の引き戻しは別々に扱う。すべての基底変換で局所化になる写像に両余終性を与える型は見つからない。 |
| 7.2.1.12 | partial → partial | component | Cを正則κに対してκ-filteredな準圏に強めるとexists_cofinal_kappaFiltered_posetは半順序のnerveから同じCへのright cofinal射の存在を直接返す。原文の存在結論のright成分のみで、同じ射のleft cofinal性・有限版は含まない。 |
| 7.2.1.13 | partial → partial | stronger-hyp | fをtrivial Kan fibrationに強めるとisLeftCofinal_of_trivialKanFibrationとRight版は同じfの左右cofinal性を直接返す。一般のcategorical equivalenceは含まない。 |
| 7.2.1.16 | none → partial | stronger-hyp | 四角をstrict pushout、fをmonoにも強めると、cofinal/anodyneのmono判定、leftAnodyneExtensionsのcobase change閉性、left anodyne⇒left cofinalを同じf,f′に順に適用して原文の結論を直接得る。任意のcategorical pushoutは含まない。 |
| 7.2.1.17 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：個別の左アノダイン射の余終性に関する候補を確認した。矢印圏のフィルター付き図式とその余極限上の左余終性を扱う型は見つからない。 |
| 7.2.1.18 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：左アノダイン性を単射と左余終性で特徴付ける型はある。フィルター付き図式の余極限で性質が閉じる型は見つからない。 |
| 7.2.1.19 | partial → own |  | IsLeftCofinal.opで右側へ移しisRightCofinal_whiskerRightを適用してopで戻す。MathlibのopFunctorのmonoidal構造の積比較はIso.reflなので元と同じf×id_Kに戻り、追加の数学的比較は不要。原文全体を直接得る。 |
| 7.2.1.20 | partial → own |  | opで右側へ移し、左右のwhiskerのright cofinal性とIsRightCofinal.compを合成すれば同じ積射f×f′がright cofinal。opFunctorの積比較は恒等で、CofinalOppositeで戻すと原文のleft cofinal性そのもの。 |
| 7.2.1.21 | partial → partial | stronger-hyp | gを単体集合の厳密同型に強めれば、gと逆射はいずれもleft cofinal。IsLeftCofinal.compを各方向に適用しgf≫g⁻¹=fで戻せば同じfのiffを直接得る。一般の圏同値は含まない。 |
| 7.2.1.22 | partial → partial | stronger-hyp | g,g′を厳密同型に強めると可換四角は同じf,f′のArrow同型。IsLeftCofinal.of_arrow_isoとそのsymmへの適用が原文のiffを直接返す。通常圏のInitialのiffは根拠にしない。 |
| 7.2.1.23 | partial → none |  | of_arrow_isoは始域・終域の厳密同型による移送。原文のFunctor準圏内の二図式の同型から、そのようなArrow同型を作る型はなく、Mathlibの通常圏のFinalも同じ述語への橋がない。 |
| 7.2.2.1 | partial → partial | component | Bを準圏に強めるとsliceOverRestrict_isQCatEquivalence_of_leftCofinalは原文(1)⇒(5)の同じ制限射の圏同値性を直接返す。右cofinalのcoslice版は左側の全七条件の代用にはしない。 |
| 7.2.2.2 | partial → none |  | 引用はright anodyneによる相対余極限余錐の制限。原文はleft cofinalによる相対極限錐であり、反転した制限錐との比較を型に含まない。双対の類似だけでは数えない。 |
| 7.2.2.3 | partial → partial | stronger-hyp | Bを準圏に強めればisLimitCone_iff_restrict_of_leftCofinalは原文の同じ錐とeによる制限の極限性のiffを直接返す。 |
| 7.2.2.5 | partial → none |  | 引用は終対象の点に制限した相対余極限とのiff。原文はその制限したΔ¹の辺がU-cocartesianであることとのiffであり、相対余極限とcocartesian辺を同定する比較がこの型にない。 |
| 7.2.2.6 | partial → none |  | initialCofinalityはnerve上のslice制限の同値。原文の錐の指定辺が可逆というiffまで直接結論する型ではない。 |
| 7.2.2.7 | partial → none |  | join錐の制限の判定と通常圏の錐のwhisker判定はあるが、原文の指定αの定値関手のHom作用が同じ制限の射になる比較を引用型に持たない。 |
| 7.2.2.8 | partial → none |  | MathlibのPreservesLimit_comp_iffは通常圏のInitial/Finalと通常錐に関する型。原文の任意単体形状の∞圏の保存性と比較するnerveの型がない。 |
| 7.2.2.9 | partial → partial | special | Dを一点、Uを終写像、Bを準圏に限ると原文の相対持ち上げは絶対極限錐の存在となり、hasLimit_iff_restrict_of_leftCofinalが同じfとeについてこのiffを直接返す。 |
| 7.2.2.10 | partial → partial | stronger-hyp | Bを準圏に強めるとhasLimit_iff_restrict_of_leftCofinalは原文と同じfの極限存在とeによる制限の極限存在のiffを直接返す。 |
| 7.2.2.11 | partial → partial | stronger-hyp | Bを準圏に強めると、頂点Xを持つ極限錐cにisLimitCone_iff_restrict_of_leftCofinalを適用して、同じ頂点を保った制限錐の極限性を直接得る。Xが制限の極限なら元でも極限となる逆向きの存在は含まない。 |
| 7.2.2.12 | partial → partial | component | Bを準圏に強めると、全A図式の極限存在をu≫Fに適用しhasLimit_of_leftCofinalを使うだけで原文の極限側の全B図式の存在を直接得る。余極限側は含まない。 |
| 7.2.2.13 | partial → none |  | MathlibのcreatesLimitsOfShapeOfInitialとcolimit版は通常圏の錐の創出。原文の∞圏・任意単体形状の保存されたjoin錐との比較がない。 |
| 7.2.2.14 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：相対極限錐の述語はある。底の指定錐と上の図式を受け、形状の終対象を仮定して U-極限となる持ち上げを返す型は見つからない。 |
| 7.2.3.4 | partial → none |  | Monotone.final_functor_iffは通常圏のFinalと順序的cofinalityのiff。原文が判定する同じnerve写像のIsRightCofinalへの比較がなく、通常圏の類似だけは数えない。 |
| 7.2.3.5 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：定値図式の定値錐は構成される。指定錐の全辺が可逆であることと、底の全辺が可逆で錐が極限であることの iff は見つからない。 |
| 7.2.3.6 | partial → none |  | 引用は一点への制限による相対余極限のiff。原文の指定辺の可逆性から、その一点の相対余極限性を直接結論する型が引用にない。 |
| 7.2.3.7 | partial → partial | special | Fを通常圏の随伴L⊣RのnerveMap Lに制限すると、OE-W1後のFrameArrowCofinalityにあるnerveMap_leftAdjoint_isLeftCofinalは同じFのleft cofinal性を直接返す。MathlibのFinal Rだけはright cofinal性の証拠としない。 |
| 7.2.3.10 | partial → partial | stronger-hyp | πをleft fibrationに強めればleftFibration_pullback_isRightCofinalは同じpullback第一射影Fのright cofinal性を直接返す。一般cocartesian fibrationではない。 |
| 7.2.3.11 | partial → partial | stronger-hyp | πをleft fibrationに強めればleftFibration_pullback_rightAnodyneは原文と同じ引き戻したFのright anodyne性を直接返す。 |
| 7.2.3.12 | partial → partial | stronger-hyp | πをleft fibrationに強めればroofLeftFibration_terminalFiber_isRightCofinalは同じfiber包含のright cofinal性を返す。fiber包含はmonoなのでright cofinal/anodyneのmono判定も適用でき、原文のright anodyne性まで直接得る。一般cocartesianの場合は含まない。 |
| 7.2.3.13 | partial → partial | component | leftFibration_pullback_isRightCofinalとIsRightCofinal.isWeakHomotopyEquivalenceの合成は原文(1)⇒(3)を同じFの全left-fibration引き戻しについて直接返す。一般cocartesian版(2)と全逆向きは含まない。 |
| 7.2.3.14 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：各頂点での coslice の弱可縮性との iff はある。cartesian 辺を保つ全空間の写像と指定したファイバー写像の右余終性を比較する型は見つからない。 |
| 7.3.1.1 | partial → partial | component | leftKanShapeとrightKanShapeは原文のK_/CとK_C/という二つの指定pullbackを直接構成する。γ,γ′の自然変換までは引用に含まない。 |
| 7.3.1.14 | partial → none |  | 引用は通常圏のKan拡張の指定自然変換の判定。原文の∞圏での自然変換・任意の単体図式とのnerve比較がなく、相対余極限の添字変更もそのまま同じKan拡張ではない。 |
| 7.3.1.15 | partial → none |  | 通常圏のRightExtensionの圏同値と存在のiffは、原文の∞圏の指定βとGα≫βの右Kan性を同じ変換として比較する型ではない。 |
| 7.3.1.16 | partial → none |  | Mathlibの通常圏の前合成によるKan拡張のiffは、原文の∞圏の指定変換と右Kan性への比較を欠く。通常圏の類似の(2)だけを直接の特殊形としない。 |
| 7.3.1.17 | partial → partial | component | δをinner fibrationにも限るとkanLeftKanExtension_unit_isIsoは、充満忠実な同じδに沿う左Kan拡張の指定単位βが可逆と直接返す。右Kan拡張の余単位の節は含まない。 |
| 7.3.1.18 | partial → partial | special | δをモデル圏のbifibrant部分のhammockLocalizationNerveMap、F₀=δ≫G、αを恒等変換に制限すると、移動後のmodelBifibrantSourceRightKanExtension_refl_of_frameCofinalityは同じαの右Kan性を返す。ModelCategory C・指定resolution・frame余終性を明示入力とするschema（一般の具体的instanceなし）で、任意の局所化ではない。 |
| 7.3.2.1 | partial → partial | component | leftKanCanonicalCocone δ F cは原文のC⁰_/cに沿う同じ標準余錐で、そのIsColimitConeという型が左Kan extended at cの定義を直接与える。右側の定義はこの引用に含まない。 |
| 7.3.2.6 | partial → partial | component | Uを終対象への射として相対余極限と絶対余極限のiffを各輸送余錐に適用すると、kanIsRelativeLeftKanExtendedFrom_iff_refl_extensionは原文の左側の恒等変換のKan性とのiffを直接与える。右側のiffは含まない。 |
| 7.3.2.7 | partial → partial | direction | 全部分圏の包含δについて、kanLeftKanExtension_unit_isIsoとcanonicalColimits_of_unit_isIsoを順に用いると、左Kan拡張⇒単位β可逆かつFが左Kan extendedという同じβについての向きを直接得る。逆向きは引用に含まない。 |
| 7.3.2.9 | partial → partial | component | δ≫F=F₀という厳密延長に対し、leftKanCanonicalCocone δ F cの全cでの余極限性が原文の左Kan延長の定義部分を直接与える。右Kan延長の定義は含まない。別のGの存在だけを定義の証拠とはしない。 |
| 7.3.2.11 | partial → none |  | relativeJoin上の局所余錐と指定βの左Kan性のiffはあるが、原文のF自身が全頂点でKから左Kan extendedであることと、この局所余錐条件を同定する型が引用にない。 |
| 7.3.2.13 | partial → none |  | exists_relativeJoin_local_colimitsは端点と変換の類を保つ相対join表示を返すが、返す条件は局所余錐の余極限性。原文(1)の同じ全関手のleftKanExtendedFromという条件との比較を欠く。 |
| 7.3.2.14 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：prism の持ち上げは cocartesian な輸送を作り、相対 Kan 判定は comma 形状の各局所余極限を調べる。Δ¹ の二ファイバー間で F(β) を与えた二つの左 Kan 条件の比較は見つからない。 |
| 7.3.3.1 | partial → partial | component | IsRelativeLeftKanExtendedFromの定義は全cについて同じleftKanCanonicalCoconeのIsRelativeColimitConeを要求し、原文のU-left Kan条件を直接表す。右Kan側の定義は含まない。 |
| 7.3.3.7 | partial → partial | special | Uを終対象への射、cを包含δの実際の像δkに限ると、kanLeftCanonical_isColimit_at_imageと終対象上の相対余極限のiffは同じ標準余錐のU余極限性を直接与える。δはinnerかつ充満忠実。任意Uや像と同型な全cは含まない。 |
| 7.3.3.11 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：左 Kan 性の型は各 comma ファイバーの相対余極限との iff。充満余反射部分圏を仮定して右随伴が反転する辺、または余反射を表す辺の像の U-cocartesian 性と比較する型は見つからない。 |
| 7.3.3.12 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：左 Kan の単位の可逆性を扱う。余反射の余単位や右随伴で同型となる辺を F が反転する条件との iff は見つからない。 |
| 7.3.3.13 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：値域の底 E が終対象となる制限の自明 Kan ファイブレーションの型を確認した。原文の始対象全体が張る始域側部分圏からの相対左 Kan 性と全辺の U-cocartesian 性との iff は見つからない。 |
| 7.3.3.14 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の始対象の点包含は左余終になる。任意の∞圏の始対象全体からの左 Kan 性、全辺の可逆性、定値図式との同型を比較する型は見つからない。 |
| 7.3.3.18 | partial → none |  | 引用は一つの相対余極限余錐の添字変更。原文は全cのcomma図式と二つの全部分圏の指定Kan条件のiffであり、そのcomma図式の同定は引用の型にない。 |
| 7.3.3.21 | partial → none |  | 相対始頂点のpullback保存とそのHom比較は部品。原文のcubeのcosliceと全ての指定標準Kan余錐を比較する型がなく、同じFの結論は直接得られない。 |
| 7.3.3.22 | partial → none |  | 相対始頂点のpullback保存だけでは、原文のU-leftKan条件をV-leftKan条件へ移すための各comma余錐の比較がない。別のpullbackの普遍性は数えない。 |
| 7.3.3.23 | partial → none |  | 相対始頂点のpullback補題は、原文のfiber中の同じFの標準Kan余錐と全空間の標準余錐との同定、およびcartesian性による逆向きを結論しない。 |
| 7.3.4.1 | partial → none |  | fiberwiseHomの相対始境界とfiber余錐を比較する補題はあるが、原文の任意の指定βの左Kan性とそのfiberwise境界条件を同定する型が引用にない。 |
| 7.3.4.2 | partial → none |  | 全fiber余錐の余極限性から関手制限のInitialBoundaryLiftingは得られるが、原文のFがKからleftKanExtendedFromであるという点ごとの定義への比較は引用にない。境界充填という証明部品だけでは数えない。 |
| 7.3.4.3 | partial → none |  | 相対fiber余錐と相対始境界の両方向の部品は、原文の全FのU-leftKanExtendedFromという条件との比較を含まない。二つの異なる条件の補題があるだけではiffの一部としない。 |
| 7.3.4.4 | partial → none |  | exists_kanRelativeJoin_diagram_of_pointwise_colimitsは相対join上の図式と境界充填を返す。原文のδに沿う指定自然変換の左Kan拡張へ戻す比較がこの引用の型にない。 |
| 7.3.4.5 | partial → partial | special | C,Dを準圏、Uを終対象への射に限ると、fiberwiseHomの随伴で同じ押し出しからの指定F₀を族へ移し、exists_kanRelativeJoin_family_extension_of_colimitsは元と同じF₀を保つ解を直接返す。相対余極限は終対象上では絶対余極限と同値。一般Uは含まない。 |
| 7.3.4.6 | partial → partial | component | Cを準圏に限り、全ての同じ型の持ち上げ問題について局所余錐があると強めると、relativeColimitRestrictionの頂点全射性は同じF₀,Gを保つ大域解の存在を返す。指定された各F_Cとの厳密一致の結論は含まない。 |
| 7.3.4.7 | partial → none |  | 制限の頂点全射性は全fiber余錐が相対余極限な解を返すが、原文(1)のU-leftKanExtendedFromへの比較を引用に含まない。全局所解の存在という強化だけではその不足は埋まらない。 |
| 7.3.4.8 | partial → none |  | 返される図式の条件は関手制限の相対始境界充填であり、原文(1)のKからleftKanExtendedFromという指定条件ではない。その比較なしに存在の片方向とは数えない。 |
| 7.3.5.1 | partial → partial | stronger-hyp | Kも準圏に強めれば左右それぞれのexists_kanLeft/RightExtension_iff_local_colimits/limitsは同じδ,F₀について原文の二つのiffを直接返す。任意の単体集合Kは含まない。 |
| 7.3.5.2 | partial → partial | stronger-hyp | Kを準圏に強めると、全ての形状の余極限存在を各leftKanDiagramに適用しexists_kanLeftExtension_of_local_colimitsから同じF₀の拡張を直接得る。 |
| 7.3.5.3 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：任意の δ に対する相対 Kan 性は comma の各ファイバーの相対余極限と比較できる。原文の G(C) とその lax holim 射影のファイバーを結び、左 Kan 拡張の存在と各 G(C) 上の余極限を比較する型は見つからない。 |
| 7.3.5.7 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：各頂点での相対始性を関手空間の境界充填につなぐ補題はある。cartesian fibration の全ファイバーの始対象から切断を構成し、その始性との iff を得る型は見つからない。 |
| 7.3.5.8 | partial → own |  | 全部分圏の始域は準圏なので、左右のexists_kanExtension_iff_local_colimits/limitsを同じ包含δ,F₀へ適用すると原文の二つのiffを直接得る。右側の既存定理を追記し、専用の一宣言の不足はpartial理由にしない。 |
| 7.3.5.9 | partial → none |  | comma全局所相対余錐の存在から延長を作る型はあるが、原文(2)は余反射の各辺のcocartesian liftだけの条件。その条件を全局所余錐へ変換する型が引用にない。 |
| 7.3.5.10 | none → partial | stronger-hyp | 同じF₀,Gの全comma余錐に指定された相対余極限が存在することも加えると、exists_kanRelativeLeftCanonical_strict_extension_of_comma_colimitsは同じ持ち上げ問題のU-leftKan解を直接返す。始域の余反射性や始対象だけからその入力を得たとはしない。 |
| 7.3.5.11 | none → partial | stronger-hyp | 同じF₀,Gの全comma余錐に指定された相対余極限が存在することも加えると、exists_kanRelativeLeftCanonical_strict_extension_of_comma_colimitsは同じ持ち上げ問題のU-leftKan解を直接返す。始域の余反射性や始対象だけからその入力を得たとはしない。 |
| 7.3.6.1 | partial → none |  | LeftKanHomUniversalはh FunのHom集合の全単射。原文の同じ合成写像のKan複体としてのホモトピー同値までは型にない。π₀の結果は写像空間の同値という結論の成分と数えない。 |
| 7.3.6.3 | partial → none |  | MathlibのlanAdjunctionは通常の関手圏の随伴。原文のFun準圏間の指定制限関手の随伴へのnerve比較が引用にない。 |
| 7.3.6.4 | partial → partial | component | Kを準圏に強めればexists_kanLeftExtension_with_homUniversal_of_local_colimitsは全F₀について同じδに沿う左Kan拡張の存在を直接返す。原文の左随伴の構成およびその単位との同定は含まない。 |
| 7.3.6.5 | partial → partial | component | Kを準圏に強めるとkanLeftKanExtensionHom_homUniversalは同じβについて原文(1)⇒(3)のh Fun上のHom全単射を直接返す。写像空間同値(2)や逆向きは含まない。 |
| 7.3.6.10 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：相対左 Kan 性を入力にした写像空間の比較はある。始対象への評価で、F が全辺を cocartesian に送ることから直接 Hom の同値を得る型は見つからない。 |
| 7.3.6.11 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：相対写像空間の比較と cocartesian な prism の構成はある。始点のファイバーの始対象を使って切断の始対象を構成し、F の全辺と始点像の条件で始性を特徴付ける型は見つからない。 |
| 7.3.6.12 | partial → partial | direction | 全部分圏の包含に対しkanRelativeLeftMappingPullbackComparison_equivalenceは、同じU,F,Gと制限について(1)からホモトピー引き戻しへの比較同値(2)を直接返す。逆向きは含まない。 |
| 7.3.6.13 | partial → partial | component | kanLeftCanonical_pinchedHomMap_trivialKanFibrationは原文(1)⇒(3)を同じF,Gの制限のpinched Homモデルで直接返す。(1)⇒(2)も自然なpinched/interval比較で得るが、その比較だけで別モデルの厳密Kanファイブレーション性を主張しない。全逆向きは含まない。 |
| 7.3.6.14 | partial → partial | stronger-hyp | 全てのF₀,H₀の局所相対余錐があると強めれば、Bは全pullbackとなりkanRelativeLeftKanRestriction_trivialKanFibrationが同じ制限Vを返す。任意の真の充満部分圏Bの場合は含まない。 |
| 7.3.6.15 | partial → partial | stronger-hyp | 全F₀,cで局所余極限があると強めればFun′(C⁰,D)は全関手圏となり、terminal版の制限のtrivialKanFibrationは同じ左Kan関手の制限の結論を直接与える。任意の真の部分圏への制限は含まない。 |
| 7.3.7.1 | partial → partial | special | Bを一点、FをC因子に依らない定値族に限りVをinner fibrationに強めると、kanIsRelativeLeftKanExtendedFrom_constantFamilyは同じ転置fのV′-leftKan条件を直接返す。一般の相対関手圏は含まない。 |
| 7.3.7.3 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：relativeFunctorSpace は底上の固定図式の空間。相対左 Kan 性と comma ファイバーの相対余極限の比較もある。可変ファイバーを持つ Fun(C/B,D) の射影について、引き戻し上の非相対左 Kan 性を移す型は見つからない。 |
| 7.3.7.4 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：相対左 Kan 図式から関手圏内の定値パラメータ族を作って相対左 Kan 性を保つ。A×C 上の任意の図式の左 Kan 性を仮定し curry に渡す型は見つからない。 |
| 7.3.7.5 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：内部 Hom への定値族は扱う。一般の F:A×C→D を A⁰×C から左 Kan 拡張する条件で、その curry が A⁰ から左 Kan 拡張となる型は見つからない。 |
| 7.3.7.6 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：相対 join に含めた特定の底辺の cocartesian 性はある。Δ¹×_B C 上の V-左 Kan 性から関手圏の後合成 V′ に関する辺の cocartesian 性を得る型は見つからない。 |
| 7.3.7.9 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：相対 join の底射影に関する cocartesian fibration はある。Fun(C/B,D)→B の指定辺を、左端ファイバーからの左 Kan 性で判定する型は見つからない。 |
| 7.3.7.10 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：全余錐族の相対始性と指定余錐の相対余極限性の iff を確認した。全 A と底への拡張を量化した join 制限の同値性から、指定充満部分圏の全対象を判定する型は見つからない。 |
| 7.3.7.13 | partial → partial | stronger-hyp | Bを一点、Vをinner fibrationとし、仮定を各aの指定余錐がV余極限であることにも強めると、kanIsRelativeColimitCone_functor_of_pointwiseは同じ転置fのV′余極限性を直接返す。元のleftKan仮定だけから点ごとの条件を得たとはしない。 |
| 7.3.8.1 | partial → partial | special | Uを終対象への射に限れば相対余極限は絶対余極限。同じFの標準左Kan余錐からkanLeftCanonical_pre_initialBoundaryを得てisColimitCone_iff_restrict_of_initialBoundaryへ渡すと、原文の指定余錐の制限とのiffを直接得る。U=idはこの特殊化ではない。 |
| 7.3.8.2 | partial → none |  | colimitConstInitialは通常圏で一つの選択済み定値図式の余極限対象の同型。原文の指定された任意の余錐についての相対余極限性のiffと比較する型がない。 |
| 7.3.8.3 | partial → own |  | 全部分圏の包含と同じFにkanLeftCanonical_pre_initialBoundaryを適用し、isColimitCone_iff_restrict_of_initialBoundaryへ渡せば、原文の指定余錐とその制限の余極限性のiffを直接得る。通常圏の類似だけでなく同じ∞圏の二宣言を追記した。 |
| 7.3.8.4 | partial → none |  | MathlibのFubiniは通常圏の構成済み積余錐。原文の指定二重joinの同じFおよびU相対余極限性との比較がない。 |
| 7.3.8.5 | partial → none |  | 通常圏の反復余極限の構成は、原文の指定Fにおける三つのjoin余錐の相対余極限性のiffを結論しない。 |
| 7.3.8.6 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：相対余極限余錐を定値パラメータ族に写す型はある。相対余極限図式を頂点に持つ任意の族の levelwise U-余極限での閉性は見つからない。 |
| 7.3.8.7 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：準圏の一般の極限性と n-truncation 関連の用語を別々に検索した。全写像空間の n-truncation で定義した対象のクラスが任意の極限に閉じる型は見つからない。 |
| 7.3.8.8 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：関手圏の点ごとの余極限判定と通常圏の積図式の余極限構成はある。各項目が余極限図式である族の、点ごとの余極限も余極限図式となる型は見つからない。 |
| 7.3.8.9 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：点ごとの comma 余錐に相対余極限性を課す形はある。右ファイブレーションで引き戻した部分圏に対し b と V(b) の条件を比較する型は見つからない。 |
| 7.3.8.10 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：全点での条件は comma ファイバーの相対余極限性で特徴付ける。右ファイブレーションに沿う保存と、各ファイバー非空による反映は見つからない。 |
| 7.3.8.11 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：左 Kan 拡張の述語と通常圏の同値による添字変更はある。右ファイブレーションに沿う絶対左 Kan 性の保存と非空ファイバーによる反映は見つからない。 |
| 7.3.8.12 | partial → partial | component | Uを終対象への射、Cの塔を半順序集合の充満部分nerveに限ると、posetSubtype_canonicalColimit_nestedは原文の左辺⇒(2)を同じ制限関手について直接返す。(1)および逆向きは含まない。 |
| 7.3.8.14 | partial → partial | component | 半順序集合のnerveとその充満部分圏の塔に限ればposetSubtype_canonicalColimit_nestedは同じFの左辺⇒(2)を直接返す。通常圏のisLeftKanExtension_iff_postcomposeだけは根拠としない。 |
| 7.3.8.15 | partial → none |  | isPointwiseLeftKanExtensionAtOfIso′は通常圏の点ごとのKan条件の輸送。原文の∞圏の同じ標準相対余錐への比較がなく、類似の輸送だけでは数えない。 |
| 7.3.8.16 | partial → partial | special | Uを終対象への射に限れば、同じFのkanLeftCanonical_pre_initialBoundaryとsliceUnderRestrict_isQCatEquivalence_of_initialBoundaryは原文のθの絶対coslice制限の同値を直接返す。一般Uの相対pullbackは含まない。U=idとはしない。 |
| 7.3.8.17 | partial → partial | stronger-hyp | UをEquivalenceLifting、包含C⁰→CをIsPrecompositionEquivalenceにも強めれば、kanRelativeCosliceMap_trivialKanFibration_of_precompositionEquivalenceは原文と同じ相対coslice制限θのtrivialKanFibrationを直接返す。Fの相対Kan性だけの場合は含まない。 |
| 7.3.8.18 | partial → partial | stronger-hyp | 包含C⁰→CをIsPrecompositionEquivalenceにも強め、Uを終対象への射として相対coslice補題を用いれば、同じ絶対coslice制限θのtrivialKanFibrationを直接得る。個別のpinchedHomMapの結果だけは全cosliceの代用にしない。 |
| 7.3.8.19 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：既存 U-余極限余錐の充填性と、各 comma 余錐からの厳密相対左 Kan 拡張の存在はある。相対左 Kan 性を持つ F の指定底余錐を持ち上げる存在を部分圏で判定する iff は見つからない。 |
| 7.3.8.20 | partial → own |  | 恒等変換のleftKan性は標準余錐の定値輸送で得られるので、hasColimit_iff_leftKanExtensionを同じ包含とFに適用すれば原文の存在のiffを直接得る。通常圏の類似に加えてこの準圏の根拠を追記した。 |
| 7.3.8.22 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：各局所相対余極限からの一段の厳密延長と、通常圏の指定単位に沿う左 Kan 性の推移性はある。既存の F を与えた isofibration の二つの持ち上げ問題の解の存在を比較する型は見つからない。 |
| 7.3.8.23 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏で二段の指定済み変換の左 Kan 性を比較する。∞圏の F と制限からの拡張の存在の iff としての推移性は見つからない。 |
| 7.3.8.24 | partial → partial | special | C₂を一点、Gを全部分圏の包含、αを厳密制限の恒等変換に限る。すると同じβのKan性はその頂点への余錐の余極限性で、kanLeftCanonical_pre_initialBoundaryとisColimitCone_iff_restrict_of_initialBoundaryは原文の(1)⇔(2)を直接返す。一般Hや一般αは含まない。 |
| 7.3.8.25 | partial → partial | special | C₂を一点に限れば左Kan拡張の存在は同じF₁,F₀の余極限の存在。hasColimit_iff_leftKanExtensionはこの場合の(1)⇔(2)を直接返す。一般のHは含まない。 |
| 7.3.8.26 | partial → partial | component | Kを準圏に強めるとhasColimit_iff_leftKanExtensionは原文(1)の同じF,F₀の余極限存在のiffを直接返す。指定βについての余極限性を比較する(2)は含まない。 |
| 7.3.9.1 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：相対余極限の定義と、既存の相対余極限余錐の像に同型な指定底余錐へ移す構成がある。各ファイバーの K-余完備性と全輸送による保存が任意の指定底余錐の持ち上げと同値となる型は見つからない。 |
| 7.3.9.2 | partial → partial | stronger-hyp | 仮定を、同じFと底図式の全comma余錐上に指定された相対余極限が存在することにも強めれば、exists_kanRelativeLeftCanonical_strict_extension_of_comma_colimitsは同じ持ち上げ問題のU-leftKan解を直接返す。fiber余完備性と輸送保存だけからその入力を得たとはしない。 |
| 7.3.9.3 | partial → partial | stronger-hyp | 指定αが全余錐のFunctorIsoも与えると強めればkanIsRelativeColimitCone_iff_of_functorIsoは同じ二余錐の相対余極限性を両方向に直接移す。全成分cocartesianという元の仮定だけは含まない。 |
| 7.3.9.4 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：相対余極限性を全余錐族の相対始性と比較する型はある。弱可縮な K 上の全辺の U-cocartesian 性と、底の各辺と余錐の相対余極限性との iff は見つからない。 |
| 7.3.9.5 | partial → partial | component | cocartesianFibration_lift_prismを原文のc≫gへ適用すれば、同じf₀から指定された底の変換上の成分ごとcocartesianなαを直接構成する。終点が定値Eなのでf₁は同じ終点fiberを通る。後半の余極限存在と輸送保存のiffは含まない。 |
| 7.4.1.1 | partial → partial | special | Cを宇宙で小さく、βとYをcoherentDiagramSectionsCone Fの標準錐と切断空間に指定すると、coherentDiagramSectionsCone_isLimitは原文(1)を同じβについて直接返す。任意のβに対する(1)⇔(2)の判定は含まない。 |
| 7.4.1.2 | partial → partial | special | Cが宇宙で小さい場合、coherentSmallConstantSourceMap_isQCatEquivalenceを点に適用すると原文のMは同じ小さい全切断空間と同値。その切断錐の極限性を同値に沿って移せばMが極限と直接得る。任意の大きなCは含まない。 |
| 7.4.1.4 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：宇宙で小さい図式の極限と定値始域比較はある。非可算 κ を固定して Hom の本質的 κ-small 性を必要十分とし、さらに λ への包含が極限を保つ主張は見つからない。 |
| 7.4.1.6 | partial → partial | special | UをFの標準leftUnstraighteningProjectionに指定すると、全切断のKan性のinstanceとcoherentDiagramSectionsCone_isLimitは同じ全切断空間がFの極限であると直接返す。任意の与えた輸送表現Uは含まない。 |
| 7.4.1.9 | partial → partial | component | Space値の比較データLeftTransportRepresentationを仮定すると、そのcomparisonはLeftTransportRepresentation.isPrecompositionEquivalenceにより同じUからFの標準leftUnstraighteningへの底上の同値を直接与える。(1)から(3)のこの成分だけで、指定αと全三条件のiffは含まない。 |
| 7.4.1.13 | partial → partial | component | simplicialSectionsは原文のFun_/C(C,E)という構成の始域を、同じUについて指定pullbackで直接構成する。αからHom空間への比較射Tの構成は含まない。 |
| 7.4.1.14 | partial → none |  | 極限錐の存在とconeRestrictionの同値は、原文の指定αで定義される比較Tのホモトピー同値ではない。始域と終域だけ似た別の比較を数えない。 |
| 7.4.1.15 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：固定宇宙で次数ごとの関手空間小性と空間圏の小極限を確認した。ecf(λ) の形状境界から切断の本質的 λ-small 性を出す濃度条件は見つからない。 |
| 7.4.1.16 | partial → partial | special | Ūを普遍pointed-space左fibrationの指定F̄によるpullback、Fの極限存在も仮定する場合、spaceCone_isLimit_iff_pointRestriction_of_hasLimitは同じ点からの切断制限の同値と極限性のiffを直接返す。任意の与えた表現Ūは含まない。 |
| 7.4.1.18 | partial → none |  | coneRestriction_iffはU側と普遍pointed-space側の切断制限の同値を比較する。指定した持ち上げのIsRelativeLimitConeを結論する型が引用にないため、原文(2)の解の存在と全解の相対極限性は直接得られない。 |
| 7.4.1.19 | partial → none |  | 切断制限の同値を表現間で移すだけでは、原文の同じ持ち上げF̃が全空間で極限という結論との比較を欠く。 |
| 7.4.1.20 | partial → partial | special | Uを標準smallLeftUnstraighteningProjection Fに指定するとexists_classifiedLimitConeは、同じFの底の極限の保存(1)から、任意のliftに射影で保たれる極限を直接与える。(2)⇒(1)および任意の表現Uは含まない。 |
| 7.4.1.21 | partial → partial | special | Uを標準smallLeftUnstraighteningProjection F、Kを有限離散形状に限りFに全有限積保存を課せば、exists_classifiedLimitConeは任意の同じliftに射影で保たれる極限を直接作り(1)⇒(2)を与える。逆向き・一般Kは含まない。 |
| 7.4.1.22 | partial → none |  | 引用はCᵒᵖ上の図式と反変representablePresheafInfinityによる判定。原文のC上の同じFと共変h^Xによる判定ではない。反対圏で類似の結果というだけでは同じ極限の結論に移せない。 |
| 7.4.1.23 | partial → partial | component | Cを宇宙で小さく取るとyonedaInfinityMap_evaluation_isLimitは同じ共変Hom(x,−)について原文h^Xの極限保存を直接返す。反変h_X側および任意の局所κ-smallな大きなCは含まない。 |
| 7.4.2.1 | partial → partial | special | 宇宙で小さいCと小さい全空間のleft fibrationsに限れば、LeftFibrationObject、leftFibrationObject_enrichedCategory、sHom_kanComplexが原文と同じ対象・底上のHom・局所Kanな豊穣圏を直接構成する。単にcoherent nerveの写像があるという根拠から置き換えた。 |
| 7.4.2.4 | partial → partial | component | Cを宇宙で小さい準圏に限ればleftStraighteningInfinityMap_isQCatEquivalenceからh Funとh LFibの同値そのものを直接得る。指定γとΓの適合を保つという射の指定まではこの型に含まない。 |
| 7.4.2.6 | partial → partial | stronger-hyp | 両left fibrationsにHasSmallSimplexFibersも仮定すると、transportRepresentationMappingSpaceMapの同値と同じ射に対するMappingFamilyWitnessは指定γに適合するΓの存在とホモトピー類の一意性を直接与える。表現だけから小性を得たとはしない。 |
| 7.4.2.11 | partial → partial | stronger-hyp | 両射にHasSmallSimplexFibersを加えると、familyWitness_nonemptyのK=Δ⁰とuniqueは同じΓに適合するγの存在とFunctorIsoによるホモトピー一意性を直接返す。一般の小性のない場合は含まない。 |
| 7.4.2.13 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：輸送表現の比較のデータと、指定左 Kan 変換が Hom 全単射を与える型はある。指定 α の輸送表現性を定値点の左 Kan 拡張性と比較する iff は見つからない。 |
| 7.4.2.14 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：輸送表現のデータは宇宙で小さい空間圏に値を取る。順序集合 nerve の濃度評価もあるが、U の本質的 κ-small 性の下で指定 α の二種類の普遍性を比較する型は見つからない。 |
| 7.4.2.15 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：各局所余極限を入力に指定左 Kan 変換を構成する補題と、輸送表現のデータはある。本質的 κ-small な U で、α を選ばず F の表現性と点の左 Kan 拡張性を比較する iff は見つからない。 |
| 7.4.2.17 | partial → none |  | 引用の比較は二つの全空間の底上の写像から二表現の変換空間への射。原文の指定αによるE上の定値点からのHomへの前合成とは違う射で、その自然な比較を型に含まない。 |
| 7.4.3.1 | partial → partial | special | Uを標準leftUnstraighteningProjection、XをcoherentDiagramTotalCoconeの頂点に限ると、その余極限性とcoherentTotalCoconeFiber_isWeakHomotopyEquivalenceは同じ全空間からXへの標準射の弱同値性を直接返す。任意X・任意の輸送表現のiffは含まない。 |
| 7.4.3.3 | partial → partial | component | hasColimit_coherentSpaceDiagramとspace_hasSmallColimitsは原文前半の全小図式の余極限存在を直接返す。任意Xについて全空間からの弱同値で特徴付ける後半は含まない。 |
| 7.4.3.4 | partial → none |  | 引用はBousfield–Kanの選んだ余錐の余極限性。原文が指定するweighted nerveとその頂点との弱同値をこの型だけでは得られず、任意Xについてのiffの一部とは数えない。 |
| 7.4.3.6 | partial → partial | stronger-hyp | Uを標準leftUnstraighteningProjectionに限り、指定Xへの射がある余錐cのcoconeFiberMapとして与えられる場合、isColimitCone_of_coconeFiberMap_weakEquivalenceはその同じ射が弱同値ならXが余極限という向きを直接返す。任意の全空間射から余錐を構成する議論は含まない。 |
| 7.4.3.8 | partial → none |  | space_hasSmallColimitsは宇宙内の小図式についての存在。原文の特定λで切ったS_<λのcf(λ)-小形状の閉性およびS_<μへの保存への型の比較がなく、濃度を宇宙で代用しない。 |
| 7.4.3.10 | partial → none |  | 固定宇宙の余完備性だけでは、原文の任意の正則基数κに対するS_<κの存在と包含による保存の一部を直接与えない。 |
| 7.4.3.11 | partial → partial | component | isColimitCone_iff_restrict_rightCofinalは、原文(1)⇒(2)の同じ極限対象Xを保つ制限余錐を直接与える。空間値の試験から共終性を検出する逆向きは含まない。 |
| 7.4.3.12 | partial → partial | component | Cを準圏に強めればisLimitCone_iff_restrict_of_leftCofinalは原文(1)⇒(2)を同じ指定極限錐の制限として直接返す。一般の単体集合Cおよび試験から共終性を得る逆向きは含まない。 |
| 7.4.3.13 | partial → partial | stronger-hyp | Uを標準leftUnstraighteningProjection、γを指定余錐cのcoconeFiberMapとした場合、isColimitCone_of_coconeFiberMap_weakEquivalenceは同じγについて(2)⇒(1)を直接返す。任意の表現αの比較と逆向きは含まない。 |
| 7.4.3.14 | partial → partial | component | IsLeftCofinal.isWeakHomotopyEquivalenceを同じ引き戻し包含E→Ēへ適用すると原文(2)⇒(1)を直接得る。輸送表現の余極限条件(3)や逆向きは含まない。 |
| 7.4.3.15 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：左余終性の slice による判定と左輸送表現のデータはある。E⁰↪E の左余終性と C⁰ からの輸送表現の左 Kan 性の iff は見つからない。 |
| 7.4.4.1 | partial → none |  | QC内のpullback錐の極限性は原文のcocartesian切断準圏を頂点とする錐ではない。Space内の全切断の極限性もQC内への保存の比較を含まない。 |
| 7.4.4.2 | partial → none |  | 原文は任意のQC値図式のcocartesian切断準圏そのものの極限性。引用のCat内のpullbackとSpace内の切断極限は別対象で、同じ錐への比較を欠く。 |
| 7.4.4.3 | partial → none |  | MathlibのHasLimits Catは通常圏の極限。原文のQCというcoherent nerve内の極限と比較する型がなく、そのまま小完備性と数えない。 |
| 7.4.4.6 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：始頂点での切断の評価は同値になる。二つの底にまたがる切断制限の同値と、輸送表現の QC_{<κ} 内の極限性を比較する iff は見つからない。 |
| 7.4.4.9 | partial → partial | component | 底C◁を準圏に強めるとcocartesianSectionsEvaluate_trivialKanFibrationとexists_kanCocartesianSectionsEvaluate_sectionは原文の指定evとその切断を直接構成する。θとの合成は書けるが、選択によらないFunctorIsoという残りの結論は含まない。 |
| 7.4.4.12 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：引き戻し後の切断の同定と始頂点評価の同値はある。任意の U を C◁ に延長し、C への切断制限を同値にする拡張の存在は見つからない。 |
| 7.4.4.14 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏 Cat の小極限と、始頂点での cocartesian 切断の評価同値を確認した。ecf(λ) の図式で QC_{<λ} の極限を切断で実現し、μ への包含で保つ型は見つからない。 |
| 7.4.4.15 | partial → partial | special | 極限を二項積X⊗Yで表示する場合、isColimitCone_tensor_of_componentsは同じ余錐q̄の二射影の余極限性からq̄の余極限性を直接返す。一般のQC値図式の極限は含まない。 |
| 7.4.4.16 | partial → partial | component | 極限を二項積で表示する場合、exists_colimitCone_tensor_with_componentsは同じqの余極限を指定された成分余錐から直接構成し、tensor_of_componentsは原文の成分条件⇒余極限性を与える。任意の極限形状と逆向きは含まない。 |
| 7.4.4.17 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：関手圏で点ごとの余極限性を判定する型と、通常圏 Cat の小極限の型はある。各遷移が K-余極限を保つ∞圏図式の極限内で K-余完備性と点ごとの判定を同時に得る型は見つからない。 |
| 7.4.5.1 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：辺の局所化の述語と通常圏 Cat の余完備性はある。輸送表現の余極限を U-cocartesian 辺の局所化と特徴付ける iff は見つからない。 |
| 7.4.5.2 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：空間値図式には全空間の Kan 置換を用いた余極限がある。任意の QC 値図式で全空間の cocartesian 辺だけを反転する局所化を余極限とする型は見つからない。 |
| 7.4.5.3 | partial → none |  | 通常圏CatのHasColimitsは原文のQC内の∞圏的な小余完備性を直接結論しない。coherent nerveの余極限比較が必要。 |
| 7.4.5.5 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：空間値の全空間による余極限はある。通常圏添字の QCat 値厳密図式の weighted nerve を cocartesian 辺で局所化し、QC 内の余極限に同定する型は見つからない。 |
| 7.4.5.8 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：cocartesian な成分を持つ円柱の持ち上げを構成する。C▷ の終点ファイバーへの指定 Rf がこの形の円柱を持つことを、Rf 自体の性質として表す定義は見つからない。 |
| 7.4.5.10 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：指定底円柱に対する cocartesian な持ち上げの存在を確認した。終点ファイバーへの Rf の条件を定義し、同じ関手圏の同型類でその条件を特徴付ける型は見つからない。 |
| 7.4.5.13 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：局所化の述語と空間値の全空間モデルを確認した。QC_{<λ} での指定輸送余錐の余極限性と refraction の局所化性を比較し、逆向きだけに cf(λ) を課す型は見つからない。 |
| 7.4.5.17 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：局所化からの関手の延長と左 Kan 性の述語を確認した。QC 内の輸送余錐の余極限性と cocartesian 辺の反転から、E からの左 Kan 性を得る型は見つからない。 |
| 7.4.5.18 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：既存のファイブレーション上の円柱は持ち上げられ、局所化は別に定義される。底を C▷ へ延長し、新しい頂点ファイバーへの refraction が局所化となる同時存在は見つからない。 |
| 7.4.5.20 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：辺の局所化と通常圏 Cat の小余極限はある。濃度境界つきの QC 値輸送表現に対し局所化を余極限とし、任意の μ≥λ への包含で保つ型は見つからない。 |
| 7.4.5.22 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏 Cat の小余完備性と CatInfinity の準圏性は別々にある。cf(λ) の形状の余完備性を QC_{<λ} に与え、より大きい濃度への包含で保つ型は見つからない。 |
| 7.4.5.23 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏 Cat の小余完備性はある。本質的 κ-small な準圏に制限した QC の小余完備性と、λ への包含による保存を同時に述べる型は見つからない。 |
| 7.4.6.1 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：CatInfinity の inner horn 充填性と辺の局所化の述語はある。0番目の外ホーンで、0→1 の局所化と他の辺の反転を仮定した充填は見つからない。 |
| 7.4.6.2 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：局所化と空間値の全空間による余極限の候補を確認した。指定 refraction の局所化性から κ-small な QC 値輸送余錐が余極限となる型は見つからない。 |
| 7.4.6.3 | partial → none |  | 全空間の前合成同値はあるが、原文は指定cocartesian辺を両側で反転した局所化の間の誘導射。局所化と指定辺の比較を引用の型に持たない。 |
| 7.5.1.5 | partial → none |  | 標準unstraighteningの切断極限と、既存のstrict錐のBK比較による判定はあるが、BK holim自体を同じ図式のnative錐の頂点とする比較はこの引用にない。別の極限対象の存在だけでは数えない。 |
| 7.5.2.1 | partial → own |  | cocartesianSectionsを同じweightedNerveProjection Fと底の恒等射へ適用すれば、原文の全切断中のcocartesian関手を張る全部分準圏をそのまま構成できる。BKの全切断空間とは区別し、実際の構成の宣言を追記した。 |
| 7.5.2.4 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：全切断の BK 同型と cocartesian 切断の準圏はある。通常圏の Grothendieck 構成の cocartesian 切断圏の nerve との指定同型は見つからない。 |
| 7.5.2.6 | partial → partial | component | weightedNerveProjection_cocartesianFibrationとcocartesianSections_quasicategoryは原文の同じholimが準圏であるという前半を直接返す。QC内の極限性という後半はSpace内の極限性で代用しない。 |
| 7.5.2.13 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：切断の始頂点評価が自明 Kan になる。BK 比較が離散添字で同型になる型もある。任意の始対象つき添字圏で通常極限から cocartesian 切断への指定包含を同値とする型は見つからない。 |
| 7.5.3.1 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：固定形状の底上の関手空間の準圏性はある。C の全対象に対する弱輸送図式全体が injective な持ち上げ性を満たす型は見つからない。 |
| 7.5.3.2 | partial → none |  | cocartesianStrictTransportDiagramの定義は図式を構成するだけで、原文のisofibrantという持ち上げ結論を含まない。構成が存在することはこの系の結論の成分ではない。 |
| 7.5.3.3 | partial → partial | special | FをKan値に限るとweightedTransportUnitは同じweighted nerveの全切断によるstrict transportへの自然変換αを構成する。left fibrationでは全切断がcocartesianなので原文の構成のα成分に一致する。universal/taut scaffoldとの可換性と一意性は含まない。 |
| 7.5.3.4 | partial → partial | component | FをKan値に限ればweightedTransportUnitComponent_isQCatEquivalenceは同じαの各成分の圏同値性を直接返す。全図式のisofibrant性とαのmono性は含まない。 |
| 7.5.3.5 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：Kan 値の unit の成分ごとの圏同値はある。任意の単体集合値図式から QCat 値の isofibrant 図式への単射を作る型は見つからない。 |
| 7.5.3.6 | partial → partial | component | functorialなcontinuousKanReplacementとその単位をFに後合成すると、anodyne単位のmono性と弱同値性から、同じFからKan値図式へのlevelwise単射弱同値を直接得る。図式全体のisofibrant性は含まない。 |
| 7.5.3.7 | partial → none |  | 引用のlim→BK holimのホモトピー同値は、原文のholim Fとlim F⁺の指定された単体集合の厳密同型θではない。弱い同値を厳密同型の成分とは数えない。 |
| 7.5.3.8 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：輸送の単体添字 nerve 関手の余極限保存はある。Cᵒᵖ にわたる各 C_{c/} の nerve を C の nerve へ射影する指定余錐の余極限性は見つからない。 |
| 7.5.3.10 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：全切断の BK end 同型と左ファイブレーションの strict transport 図式はある。任意の cocartesian fibration で cocartesian 切断へ制限した strict limit との同型は見つからない。 |
| 7.5.3.12 | partial → partial | stronger-hyp | FをKan値で全levelwise anodyneの図式からの延長条件も満たすと強めると、bousfieldKanLimitComparison_homotopyEquivalence_of_extensionsは同じlim F→holim Fの比較の同値を返す。BKの全切断とcocartesian切断はleft fibrationの場合の同型で比較する。一般QCat値は含まない。 |
| 7.5.4.1 | partial → partial | component | bousfieldKanConeComparisonは同じ増強図式の頂点→lim→BK holimという合成射を直接構成し、そのIsSimplicialHomotopyEquivalenceを条件とすることで原文のKan値の定義を表す。KSTの基点付きπ_*版は根拠としない。専用述語名の欠如は不足にしない。 |
| 7.5.4.4 | partial → own |  | weightedConeComparison_naturalityが同じ増強自然変換の比較四角の可換性を与え、bousfieldKanMap_homotopyEquivalenceが右辺を同値にする。Kan複体の弱同値との同値およびcomp/cancel_left/cancel_rightをこの四角へ適用すると原文の三条件の二つから三つを直接得る。 |
| 7.5.4.7 | partial → partial | stronger-hyp | 全levelwise anodyneに対する延長条件を加えると、strict極限のBK比較同値とkanCone_isLimit_iff_bousfieldKanComparisonは同じKan値の極限錐がSpace内でも極限と直接返す。isofibrantだけから延長条件を得たとはしない。 |
| 7.5.4.8 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：Kan 値の指定錐の比較型と単体集合の弱同値な Kan 置換はある。任意の増強図式について、指定条件を満たす Kan 値増強図式への弱同値の存在を述語にした定義は見つからない。 |
| 7.5.4.10 | partial → none |  | Kan値図式間のBK endの同値不変性だけでは、任意の単体集合値の別々のKan置換を比較する射が得られない。原文(1)⇒(2)の全置換に対する主張への比較が必要。 |
| 7.5.4.11 | partial → partial | special | 両増強図式をKan値に限ると、BK比較の自然性と成分弱同値の不変性、Kan複体の弱同値の二つから三つにより、同じ三条件の判定を直接得る。任意の単体集合値の置換比較は含まない。 |
| 7.5.4.12 | partial → partial | special | 増強図式をKan値に限ると、現本体のbousfieldKanConeComparison_reflection_general_iffは同じ錐と反対錐のhomotopy limit条件のiffを直接返す。古いreflection_iffにあったstrict極限のKan性・lim比較同値の仮定は不要になっている。任意の単体集合値は含まない。 |
| 7.5.4.13 | partial → partial | special | 四対象をKan複体に限るとkanCommSqCone_isLimitとkanCone_isLimit_iff_bousfieldKanComparisonは、同じ可換正方形がhomotopy pullbackならhomotopy limit diagramという向きを直接与える。逆向きと任意の単体集合は含まない。 |
| 7.5.5.1 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：BK end への通常極限の比較と join 錐の極限性の述語は別々にある。QCat 値で cocartesian 切断へ至る指定合成の準圏同値を条件にした定義は見つからない。 |
| 7.5.5.7 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：∞圏の極限錐は全頂点の Hom 比較で判定できる。QCat 値の通常圏添字の増強図式で、全 K の core の条件を Δ¹ だけで検査する型は見つからない。 |
| 7.5.5.8 | partial → none |  | 指定pullback錐のQC内の極限性は、原文の同じ錐がcategorical limit diagramであるという述語と比較する型ではない。片方の別の極限性だけではiffの向きと数えない。 |
| 7.5.5.9 | partial → partial | special | 形状をcospanで一脚がEquivalenceLiftingな図式に限ると、qCatPullbackInfinityCone_isLimitは通常のstrict pullback錐がQC内で極限と直接返す。原文の存在と保存のこの形状の場合に一致し、一般形状は含まない。 |
| 7.5.5.10 | partial → none |  | catPullbackCone_isLimitはQC内での極限性。原文(2)のcategorical limit diagramという指定の比較射条件との型の比較を欠き、別の極限述語への結論だけは数えない。 |
| 7.5.5.11 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：join 錐の極限述語と単体写像の前合成同値はある。QCat 値の categorical limit 図式への成分同値の存在を条件とする単体集合値図式の定義は見つからない。 |
| 7.5.5.13 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：BK end の成分同値不変性は Kan 値の両図式を仮定する。一般の QCat 値への任意の置換に categorical limit 性が移る iff は見つからない。 |
| 7.5.5.14 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：Kan 値の成分同値から BK end の同値を得る。一般の単体集合値の増強図式で categorical limit 性二つと頂点の categorical equivalence の三条件を比較する型は見つからない。 |
| 7.5.5.15 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：準圏間の一射の同値は反対にしても同値。増強図式を各値で反対にした categorical limit 性との iff は見つからない。 |
| 7.5.6.1 | partial → none |  | 一般モデル圏のProjective.modelCategoryとisCofibrant_objは、単体集合図式にlevelwise trivial Kan fibrationを使う原文の持ち上げ定義と比較する型を含まない。SSetの具体的モデル構造のinstanceもない。 |
| 7.5.6.7 | partial → none |  | 引用のmap_weakEquivalenceはモデル圏で置換して作ったhocolim functorのmapについてで、原文の同じ通常colim(α)ではない。SSetの具体的モデル構造とその弱同値の同定もなく、類似だけでは数えない。 |
| 7.5.6.8 | partial → none |  | BK coendの定義と一般モデル圏のreplacementは、原文のN(C_/c)との指定pullbackによるF₊ではない。その自然変換を同定する比較がない。 |
| 7.5.6.9 | partial → none |  | 一般モデル圏のreplacementのcofibrant性は原文の指定F₊の性質ではない。同じ図式との比較なしにcofibrantという語の一致は数えない。 |
| 7.5.6.12 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：重みつきテンソルの coend を余極限にする型はある。N(C_{/c}) による全空間の引き戻しの余極限から元の holim への指定同型と射影による特徴付けは見つからない。 |
| 7.5.6.14 | partial → none |  | comparison_weakEquivalence_of_cofibrantのcomparisonはモデル置換由来のhocolimからcolimへの射。原文のBK coend由来の比較と同じ射とする比較がない。 |
| 7.5.7.1 | partial → partial | special | XをKan置換したBK coend（kanReflectedBousfieldKanColimitObject F）に指定すると、bousfieldKanCoherentCocone_isColimitとそのvertex計算は同じXが余極限と直接返す。一般Xのiffは含まない。 |
| 7.5.7.3 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：BK coend と単体写像の弱ホモトピー同値は定義される。指定増強図式で coend から通常余極限を経て頂点へ至る合成を弱同値とする述語は見つからない。 |
| 7.5.7.5 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：フィルター付き通常余極限は成分ごとの弱ホモトピー同値を保つ。一般の BK 余極限図式と頂点の弱同値を含む三条件の判定は見つからない。 |
| 7.5.7.6 | partial → none |  | 引用はnativeなcoherent余錐の余極限性と反変表現可能比較を判定する。原文は任意の単体集合値の増強図式のhomotopy colimit条件であり、そのBK比較射との同定を型に含まない。 |
| 7.5.7.7 | partial → none |  | strict coherent余錐の反変Homによる判定は、原文のBK coendから頂点への指定比較射の弱同値という条件への比較を含まない。専用述語名の有無でなく、この射の同定が不足。 |
| 7.5.7.8 | partial → none |  | weightedColimitOppositeIsoは重みWも反転する。原文はBKの同じ重みを用いたFとFᵒᵖの増強図式の判定であり、反転した重みを元の重みに戻し頂点への指定射と可換とする比較がない。 |
| 7.5.7.9 | partial → none |  | 標準spanのSpace内での余極限性は原文のhomotopy colimit diagramというBK比較射の弱同値性ではない。その比較がなく、同じ語の極限性で代用しない。 |
| 7.5.8.1 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：辺の局所化と空間値の全空間余極限はある。QCat 値の BK 全空間の横辺を局所化して coherent nerve 図式の余極限となる iff は見つからない。 |
| 7.5.8.2 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：局所化と BK coend は別々に定義される。通常余極限を経る指定合成が全横辺の局所化となる条件を増強図式の述語にした定義は見つからない。 |
| 7.5.8.4 | partial → none |  | BK coendとHomの随伴同型だけでは、原文のcategorical colimitの横辺反転による指定比較に接続しない。Kan値の別の比較同値も全QCat標的の同じ条件を直接返さない。 |
| 7.5.8.5 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：空間圏の指定 span 余錐の余極限性と局所化の述語はある。任意の正方形で categorical pushout と横辺局所化による categorical colimit を比較する型は見つからない。 |
| 7.5.8.6 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：同一図式上の二つの余錐の関手同型で余極限性を移す。任意の単体集合値増強図式の成分同値の下で categorical colimit 性と頂点同値の三条件を比較する型は見つからない。 |
| 7.5.8.7 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：通常の coend 余極限の型はある。projective cofibrancy を仮定して通常の余極限余錐を横辺局所化による categorical colimit と判定する型は見つからない。 |
| 7.5.8.8 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：重みつき余極限の関手と局所化の述語を確認した。projective cofibrant な F の BK coend から通常余極限への射が横辺の局所化を与える型は見つからない。 |
| 7.5.8.9 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：Kan 値の coherent な反対圏側の BK 錐が極限となる型はある。一般の QCat 値の増強図式と CatInfinity の余極限性を比較する iff は見つからない。 |
| 7.5.8.10 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：Kan 複体間の射では弱ホモトピー同値と準圏同値を比較できる。横辺の局所化と BK 全空間から頂点への弱同値で定める二種類の余極限図式の iff は見つからない。 |
| 7.5.8.11 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：個別の準圏同値の反対化と重みつき余極限の反対化の同型はある。反対図式の横辺の局所化を含む categorical colimit 性の iff は見つからない。 |
| 7.5.8.12 | partial → none |  | MathlibのGrothendieck圏のfiberwiseColimitは通常圏値の図式。原文の任意のcategorical colimit単体集合Kとその上の同じqに対するQへの比較がない。 |
| 7.5.8.13 | partial → none |  | 通常圏のGrothendieck形状の余極限存在は、原文の指定categorical colimit K形状への∞圏の余極限と比較する型を持たない。 |
| 7.6.1.1 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：空間圏の離散図式の積錐と余積余錐は構成される。任意の h Kan 豊穣圏で各 Hom の積への同型を条件にする積・余積の述語は見つからない。 |
| 7.6.1.3 | partial → none |  | HasSmallCoproductsと離散形状のIsLimitConeは原文の指定射族が誘導する全写像空間の積比較そのものを型に含まない。hCの二項余積はπ₀だけであり、hKan豊穣普遍性の直接の成分とはしない。 |
| 7.6.1.7 | partial → none |  | 引用は全小余積の存在またはhCの二項余積。原文の指定Y_iに対する写像空間の普遍性を持つ積・余積の対象の記法と一意性への比較がない。 |
| 7.6.1.13 | partial → none |  | spaceProductCone_isLimitConeは選んだ離散図式の極限錐。原文の任意の射対の全写像空間の比較とその記法を同定する型はこの引用にない。 |
| 7.6.1.15 | partial → none |  | 通常圏のprod.liftと射影の等式はあるが、原文の∞圏の指定積をhCのその二項積へ同定する型を引用に持たない。 |
| 7.6.1.16 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の相対対角が同型であることと元の射が単射であることを比較する。一般の n と∞圏の対象の n-truncation を絶対対角の (n−1)-truncation と比較する型は見つからない。 |
| 7.6.1.17 | partial → none |  | Over.forgetAdjStarは通常圏の随伴。∞圏の同じslice忘却関手の右随伴への比較がなく、nerveで自動的に同じ随伴と数えない。 |
| 7.6.1.23 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：離散形状上の対象族の積はある。各 Kᵢ の図式の極限を先に取り、その積を Kᵢ の単体的余積上の図式の極限とする型は見つからない。 |
| 7.6.1.25 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：小さい全形状の極限存在・保存を述べる述語はある。Kᵢ の極限と I-積だけで余積形状の極限存在・保存を得る型は見つからない。本文の保存条件には Kᵢ-indexed colimits とある。 |
| 7.6.1.26 | partial → none |  | Mathlibの有限積生成は通常圏の極限。原文の∞圏の有限積とのnerve比較の型がなく、同じ存在のiffへの直接適用はできない。 |
| 7.6.2.6 | partial → none |  | mono_snd_of_monoは通常圏のMono。原文の∞圏のn-truncated射（写像空間による定義）との比較を引用に持たず、n=−1としても同じ述語ではない。 |
| 7.6.2.8 | partial → partial | component | 同じσのpullbackCone σにIsRelativeLimitCone Uを適用することで、原文のU-pullbackという定義の極限側を直接表す。専用のIsRelativePullbackSquareという名前の欠如は不足としない。余極限側は含まない。 |
| 7.6.2.13 | partial → partial | special | CをQC、二脚のfiber productをcatPullbackで指定するとcatPullbackDiagram_hasLimitとその錐の頂点が原文の存在するfiber productの対象の成分を直接与える。一般Cとpushout側の記法・一意性は含まない。 |
| 7.6.2.14 | partial → partial | component | IsPullbackSquare σ=IsLimitCone(pullbackCone σ)を用い、全cospanにその錐の存在を要求すること、および全σでIsPullbackSquare σ→IsPullbackSquare(σ≫F)を要求することで、原文のpullback存在・保存の定義部分を直接表す。pushout側はこの行の根拠に含まない。 |
| 7.6.2.16 | partial → none |  | terminalTargetPullback_isBinaryProductの結論はhCの通常の二項積。原文のslice準圏のhKan豊穣積との比較がなく、終対象に限っても同じ結論は直接得られない。 |
| 7.6.2.18 | partial → none |  | 通常圏のMonoによるpullback錐の保存は、原文の∞圏のmonoと指定squareの極限性のiffへの比較を含まない。 |
| 7.6.2.19 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：∞圏の指定引き戻し正方形の述語はある。底 X が離散な場合に hC へ送った四角形の通常圏の引き戻し性を得る型は見つからない。 |
| 7.6.2.20 | partial → none |  | Mathlibのpreserves_mono_of_preservesLimitは通常圏のMonoを結論する。原文の∞圏の写像空間で定めるmonoとの同定がなく、同じFの結論として使えない。 |
| 7.6.2.22 | partial → none |  | 通常圏のpullback.diagonalは厳密なpullback対象への射。原文の∞圏の指定相対対角と同じ射・指定ホモトピーを構成する比較を持たない。 |
| 7.6.2.23 | partial → none |  | 通常圏のpushout.codiagonalは原文の∞圏の指定homotopy pushoutでの相対余対角と同じ対象・射への比較を含まない。 |
| 7.6.2.24 | partial → none |  | 通常圏のOverの積と引き戻しの対応は、原文の同じ∞圏のslice準圏との比較がない。両辺に類似の存在があるだけでは数えない。 |
| 7.6.2.27 | partial → none |  | isIso_diagonal_iffは通常圏のMonoとIsIsoの判定。原文のn-truncatedと(n−1)-truncatedの写像空間の条件への比較がなく、n=−1の特殊化としても直接使えない。 |
| 7.6.2.29 | partial → none |  | 通常圏のMono保存は原文の∞圏のn-truncated射の保存への型の比較がない。任意nの結果の一部とは数えない。 |
| 7.6.2.30 | partial → none |  | 終対象上のpullbackから得るのはhCのBinaryFan.IsLimit。原文は同じ二射が∞圏のhKan豊穣積であることのiffであり、写像空間の積比較を引用の型に持たない。 |
| 7.6.2.31 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：四角形の引き戻し述語とファイブレーションの引き戻しで cartesian 辺を移す補題はある。ev₁ 上の指定辺で引き戻し・cartesian・locally cartesian を比較する型は見つからない。 |
| 7.6.2.33 | partial → none |  | Over.pullbackは通常のslice圏の関手で、原文の指定∞圏のslice後合成のQCatAdjunctionによる右随伴の定義とは比較されていない。 |
| 7.6.2.34 | partial → none |  | MathlibのmapPullbackAdjは通常圏のsliceの随伴。原文の向き付きfiber product上の輸送関手とpinch同値を含む可換図式への比較がない。 |
| 7.6.2.35 | partial → none |  | 通常圏のmapPullbackAdjは原文の四つの∞圏条件の同じslice関手やev₁のcartesian性を結論しない。 |
| 7.6.2.37 | partial → none |  | 通常圏の全Over.map fの右随伴は、原文の∞圏のsliceおよび向き付きfiber productとの比較を含まない。ev₁の局所・大域cartesian性も型にない。 |
| 7.6.2.38 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：単体集合の厳密引き戻しの比較では cocartesian 辺の iff がある。∞圏の内在的 U-pullback または U-pushout 四角形を、その上下辺の U-(co)cartesian 性で判定する型は見つからない。 |
| 7.6.2.39 | partial → none |  | 通常圏のIsPullback/IsPushoutとIsIsoのiffはあるが、原文の同じ∞圏の指定正方形と可逆辺の条件への比較がない。 |
| 7.6.2.40 | partial → partial | component | Uを終対象への射に限るとisPullbackSquare_pasting_iffは同じΔ²×Δ¹図式の右squareを仮定した左squareと外周のiff、すなわち原文(1)を直接返す。相対一般Uとpushout側は含まない。 |
| 7.6.2.41 | partial → none |  | 引用のpushout形状の余極限は原文の極限ではなく、opで反転したshape・cone・指定pushoutの比較が必要。有限極限生成だけも任意K₀₁の極限の存在を直接与えない。 |
| 7.6.2.42 | partial → partial | component | HasFiniteLimitsの全有限形状への存在を終対象とcospanへ特殊化する向きと、hasFiniteLimits_of_terminal_pullbacksの逆向きにより、原文の存在のiffを直接得る。任意の関手の有限極限保存のiffは含まない。 |
| 7.6.3.1 | partial → partial | stronger-hyp | 全Homの指定一脚をKan fibrationに強めると、strictCoherentConeのBK Hom比較のiffとKan錐のhomotopy pullback判定から、原文の同じstrict squareの引き戻し性と全Hom squareのhomotopy pullback性を直接比較できる。一般の一脚fibrationでない場合は含まない。 |
| 7.6.3.8 | partial → partial | special | 指定squareを一脚がEquivalenceLiftingなstrict pullback錐に限ると、qCatPullbackInfinityCone_isLimitは同じsquareのQC内のpullback性（原文(1)）を直接返す。一般squareの指定Gの圏同値性とのiffは含まない。 |
| 7.6.3.9 | partial → partial | component | catPullbackCone_isLimitとcatPullbackCone_vertexは元の同じ二脚p,qの図式についてhomotopy fiber productそのものがQC内のfiber product対象となるという最後の結論を直接与える。指定αを備えるsquareの二脚の照合は含まない。 |
| 7.6.3.10 | partial → partial | special | squareを一脚がKan fibrationなstrict pullback錐に指定すると、spacePullbackCone_isLimitConeは同じsquareのSpace内でのpullback性（原文(1)）を直接返す。任意のsquareの指定gによるiffは含まない。 |
| 7.6.3.11 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：Kan 複体の厳密引き戻しを空間圏の引き戻し錐とする型はある。任意の n の二種類の連結性条件を引き戻しで移す型は見つからない。 |
| 7.6.3.14 | partial → none |  | strictCoherentConeの判定の終域はBK holimで、原文の指定α₀,α₁で作る二重homotopy fiber productへの比較ではない。その自然な比較が引用にない。 |
| 7.6.4.1 | partial → none |  | MathlibのparallelPairは通常圏の二射の図式。原文の指定した単体集合のpushout形状と任意の準圏への射との全単射への比較がない。 |
| 7.6.4.4 | partial → none |  | 通常圏のWalkingParallelPairに対するequalizerとHasEqualizersは、原文の指定pushout単体形状の∞圏の極限・余極限との比較がない。 |
| 7.6.4.5 | partial → none |  | 通常圏のequalizerという対象は原文の∞圏のEq(f₀,f₁)との比較を含まない。同じ表記だけでは数えない。 |
| 7.6.4.9 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：左余終な制限の極限から元の極限を得る一般の向きはある。自由一生成モノイドの nerve への単体円の包含の inner anodyne 性と、その制限の（余）等化子表示は見つからない。 |
| 7.6.4.10 | partial → none |  | 通常圏のForkは原文の単体的な平行射形状のjoinからの極限図式と比較されていない。 |
| 7.6.4.14 | partial → none |  | isPullback_equalizer_prodは通常圏の等化子のstrict pullback。原文のQC内のequalizer diagramとcategorical pullbackの同じ二条件への比較がない。 |
| 7.6.4.15 | partial → none |  | 通常の等化子とSpaceのstrict pullback錐の極限性だけでは、原文の同じ平行射図式の∞等化子性とhomotopy pullback性のiffへ直接接続しない。 |
| 7.6.4.16 | partial → none |  | 一般のstrictCoherentConeのBK Hom比較は、原文の指定平行二射のHom squareのhomotopy pullback条件と同じ射とする比較がない。通常圏の対角表示だけで代用しない。 |
| 7.6.4.18 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の等化子と対角の引き戻しは対応する。指定 E から categorical homotopy pullback への T が同値であることと QC での等化子性を比較する型は見つからない。 |
| 7.6.4.19 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：準圏の同値辺の空間と端点評価、写像の path replacement の inner fibration 性はある。二関手の組 D→C×C に沿って両端点を引き戻す homotopy equalizer の指定構成は見つからない。 |
| 7.6.4.20 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の等化子から対角引き戻しへの型はある。同値辺空間を使った指定 hEq が QC で等化子となる型は見つからない。 |
| 7.6.4.21 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：片脚がファイブレーションである Kan 複体の引き戻しは空間圏の引き戻しになる。hEq の具体的 path モデルを指定し、その Kan 性と平行射の等化子性を結ぶ型は見つからない。 |
| 7.6.4.22 | partial → none |  | Mathlibの通常圏のequalizerConeIsLimitは原文の∞圏の指定二射の等化子対象とfiber product対象のiffへの比較を欠く。 |
| 7.6.4.23 | partial → none |  | 通常圏のcospan極限を積と等化子で作る型は、原文の同じ∞圏の対象と指定二射の極限性との比較を含まない。 |
| 7.6.4.25 | partial → none |  | 通常圏の有限極限生成と保存は原文の∞圏の同じ積・等化子条件への比較を含まない。本体の終対象とpullbackによる生成も等化子からの方向には直接適用できない。 |
| 7.6.5.1 | partial → none |  | spaceTowerCone_isLimitConeは一つのstrict towerの選んだ錐の極限性。原文の任意の∞圏のtowerおよび全towerの存在・保存の定義と同じ型を直接構成する根拠ではない。 |
| 7.6.5.2 | partial → none |  | ofSequence/ofOpSequenceは通常圏の関手を構成する型。原文の準圏のnerve図式から同じ頂点と辺を読み出す記法の型との比較がない。 |
| 7.6.5.12 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：Kan 値で遷移がファイブレーションの塔の空間極限と、一写像の path replacement の inner fibration 性がある。任意の準圏の塔を指定した反復ホモトピー引き戻しで置換して QC の極限とする型は見つからない。 |
| 7.6.5.13 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：既に与えられた Kan 値の塔の極限と、左余終な形状制限による極限性の iff はある。形状の逐次余極限から各段の極限をつなぐ塔を構成する型は見つからない。 |
| 7.6.5.14 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：小形状全体の極限存在と、左余終な写像に沿う極限性の制限はある。逐次完備性と各 K(n) 上の極限から余極限形状 K での存在・保存を得る型は見つからない。本文の存在の箇所には K-indexed colimits とある。 |
| 7.6.5.16 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：Kan 値の塔の極限と、通常圏の等化子の対角引き戻し表示はある。任意の∞圏の塔で指定積上の shift をホモトピーまで一意に構成し、その恒等射との等化子で塔極限を判定する型は見つからない。 |
| 7.6.6.5 | none → partial | component | PreservesSmallLimitsとPreservesSmallColimitsは原文のcontinuous/cocontinuousな頂点の条件を直接与える。専用のFunᶜᵒⁿᵗという名前の欠如は不足としないが、大きさの異なる全形状と全部分準圏の構成全体は含まない。 |
| 7.6.6.6 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：宇宙で小さい全形状の完備性・余完備性と κ-small の濃度条件は別々にある。任意の κ を取ってその全 κ-small 形状に量化する四つの述語は見つからない。 |
| 7.6.6.7 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：全頂点が張る部分複体を作る一般の構成はある。κ-small な形状の極限・余極限を保存する関手の充満部分圏としての指定定義は見つからない。 |
| 7.6.6.15 | partial → none |  | 通常圏の積・等化子による完備性生成は原文の∞圏のκ完備性と比較する型を持たない。本体の終対象とpullbackによる有限極限生成だけでは、右辺の小積と有限極限から一般κ完備という同じ結論は直接得られない。 |
| 7.6.6.18 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：宇宙で小さい全極限の述語と濃度制限はある。特異 λ で全 κ<λ にわたる完備性から λ⁺-完備性を得る同値は見つからない。 |
| 7.6.6.19 | partial → partial | stronger-hyp | Kを準圏とし同じrightKanDiagram δ F₀ cの全てに極限があることも仮定すれば、exists_kanRightExtension_iff_local_limitsは原文の同じF₀の右Kan拡張存在を直接返す。局所κ-small性から各形状の小性を得る議論は含まない。 |
| 7.6.6.20 | partial → partial | special | 𝕂を宇宙内の全小形状またはsifted小形状に限ればHasSmallLimits/HasSmallSiftedColimitsは、原文の各Kでの同じHasLimit/HasColimitの全称条件そのもの。任意の形状集合𝕂は含まない。 |
| 7.6.6.22 | partial → partial | special | 𝕂を宇宙内の全小形状に限ればPreservesSmallLimitsとPreservesSmallColimitsが原文の同じ図式の極限・余極限保存の条件を直接表す。任意𝕂およびそれを張る全部分関手準圏は含まない。 |
| 7.6.6.24 | partial → none |  | 引用は余極限保存関手のstrict pullbackの小余完備性。原文は極限とK-continuityであり、反対化した図式・coneの比較を持たない。双対に似た主張だけでは数えない。 |
| 7.6.6.26 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：対象の完備性と関手の保存性の述語はある。指定形状集合に対応し、それぞれを対象条件・辺条件とする QC_{<λ} の部分圏は見つからない。 |
| 7.6.6.27 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏 Cat の小極限と、既に頂点が属する充満部分複体への極限性移送はある。濃度境界つき QC の完備・余完備部分圏で κ-極限が存在し包含で保つ型は見つからない。 |
| 7.6.6.28 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：全空間の相対余極限性を coslice 上で定義する。各ファイバーの図式に edgewise U-余極限余錐が存在することを全 K で量化した述語は見つからない。 |
| 7.6.6.29 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：相対余極限と κ-small の述語はある。κ-small、有限、宇宙で小さい形状に対する edgewise 余極限付きファイブレーションの三種類の定義は見つからない。 |
| 7.6.6.39 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：固定 U に対する相対余極限は定義される。二つの edgewise 余完備なファイブレーションの合成で、上側が cocartesian のとき余完備性を保つ型は見つからない。 |
| 7.6.6.40 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：全空間の小余極限存在と射影の保存を別々に書く述語はある。底の余完備性の下で、それらの連言を edgewise なファイブレーションの余完備性と比較する iff は見つからない。 |
| 7.6.6.41 | partial → none |  | isColimitCone_of_pointwiseは全関手準圏の余錐についての型。原文の一般のファイブレーションのsection準圏との比較を欠き、積射影へ限るだけで同じ指定section余錐の結論と数えない。 |
| 7.7.0.1 | partial → none |  | MathlibのIsUniversalColimitは通常圏のNatTransとIsPullbackで定義される。原文の∞圏の指定βとlevelwise pullbackとの比較がない。 |
| 7.7.0.4 | partial → none |  | span円筒と単射列の自然性squareのhomotopy pullback保存は部品。原文の全小図式についてcartesian変換の切断準圏の制限が同値となるstrongly universalの結論に直接は達しない。 |
| 7.7.0.6 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：左ファイブレーション分類での基底変換は κ-filtered 余極限を保ち、空間値図式の全空間モデルは余極限を与える。任意の β の余極限性と全点ファイバーの可縮余極限を含む四条件の iff は見つからない。 |
| 7.7.1.1 | partial → none |  | NatTrans.Equifiberedは通常圏のstrict自然性squareを判定する述語。原文の∞圏の指定自然変換の各2単体のpullback条件との比較がない。 |
| 7.7.1.13 | partial → none |  | 通常圏のEquifiberedの定義は、原文のK▷上の同じ自然変換のcartesian性と頂点への制限のlevelwise pullback性のiffを結論しない。 |
| 7.7.1.14 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の辺ごとの引き戻し述語と join 余錐の頂点への収縮はある。指定 γ の cartesian 性と定値図式への点ごとの引き戻し表示を比較する型は見つからない。 |
| 7.7.1.15 | partial → none |  | 通常圏のIsUniversalColimitは、原文の任意のcartesianな増強自然変換による∞余極限性の定義と比較する型を持たない。 |
| 7.7.1.19 | partial → none |  | 通常圏のIsUniversalColimitの定義だけでは、原文の指定∞自然変換βについての二表現のiffに接続しない。 |
| 7.7.1.20 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の一つの余錐に対する基底変換閉性は定義される。任意の∞圏の形状 K で全余極限がその性質を持つことと、圏の K-余極限の普遍性を比較する型は見つからない。 |
| 7.7.1.21 | partial → none |  | 通常圏のIsUniversalColimitの存在と原文の∞圏の指定図式のuniversal colimit diagramの存在との比較がない。 |
| 7.7.2.1 | partial → partial | component | relativeFunctorSpace U Fは原文の底上の同じ全関手単体集合を直接構成する。cartesian fibrationならinnerなのでその準圏性も既存instanceで得る。cartesianな全辺という頂点条件の全部分圏は、引用のcocartesianSectionsで代用しない。 |
| 7.7.2.5 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：双対の cocartesian 切断を前合成で制限する射と充満忠実の述語はある。K▷→K の cartesian 切断制限に対する descent と effective descent の二定義は見つからない。 |
| 7.7.2.8 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の余極限の普遍性と、双対の切断制限は別々にある。ev₁ に対する descent の順方向と、K-余極限または終対象を仮定した逆方向は見つからない。 |
| 7.7.2.10 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の equifibered 述語と頂点が張る部分複体の一般構成はある。Fun(K,C) の指定スライスで cartesian な γ のみを集めた充満部分圏は見つからない。 |
| 7.7.2.12 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の普遍余極限述語と準圏の充満忠実はある。任意の指定余極限に対する cartesian なスライスの制限が充満忠実であることとの同値は見つからない。 |
| 7.7.2.13 | partial → none |  | IsVanKampenColimitは通常圏のIsColimit/IsPullbackのiffであり、原文のcartesianな関手の切断準圏の制限の圏同値性と同じ条件への比較を持たない。 |
| 7.7.2.15 | partial → none |  | 通常圏のvan Kampen余錐は、原文の∞圏の指定colimitのstrongly universal性と選択不変性への比較がない。 |
| 7.7.2.19 | partial → none |  | 通常圏のvan Kampen条件は原文の∞圏のcartesian変換の条件と比較されていない。形式が類似するiffだけでは数えない。 |
| 7.7.2.23 | partial → none |  | 通常のIsVanKampenColimitを全余錐で量化しても、原文の同じ∞圏の強普遍性とcartesian変換のiffへの比較がない。 |
| 7.7.2.24 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：任意に与えたスライス余錐を元の圏への射影で判定する。K⋆Δ¹ の縮退から指定した lift を作り、それにより弱余極限を定義する型は見つからない。 |
| 7.7.2.26 | partial → none |  | sliceOver_isColimitCone_iff_projectionは既に与えたslice余錐の極限性を比較する。原文のweak colimitを定める縮退による指定liftとの同定と、任意のFからそのliftを得る型を引用に持たない。 |
| 7.7.2.28 | partial → none |  | 引用は固定sliceの一余錐と射影の余極限性のiff。原文のweak colimitという指定標準liftの条件および全lift/あるliftの量化への比較がない。 |
| 7.7.2.30 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：相対左 Kan 性を仮定した四つの Hom の引き戻し比較はある。弱余極限図式を入力に、cartesian な相手に対するスライス Hom の制限を同値にする iff は見つからない。 |
| 7.7.2.31 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：指定スライス余錐の余極限性を台で判定する。ev₁ の descent と、全 cartesian な変換の上側が弱余極限となる条件の iff は見つからない。 |
| 7.7.2.32 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏で引き戻しが後合成の右随伴になる。∞圏の向き付きスライスに lift した指定図式の余極限性を全 u* に要求する descent 判定は見つからない。 |
| 7.7.2.33 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：左ファイブレーション分類の特定の基底変換が κ-filtered 余極限を保つ。任意のスライス引き戻しの保存と全弱余極限の descent との iff は見つからない。 |
| 7.7.2.34 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の余錐の引き戻し不変性と、左ファイブレーション分類の κ-filtered 保存を確認した。任意の∞圏の K-余極限が普遍であることと全 u* の K-余極限保存の iff は見つからない。 |
| 7.7.3.4 | partial → none |  | Closed/MonoidalClosedは通常圏のHom集合の随伴で、原文の∞圏の同じ評価射による全写像空間のホモトピー同値への比較がない。 |
| 7.7.3.13 | partial → none |  | 通常圏のtoOverSectionsAdjは原文の∞圏の指数対象と指定slice準圏の関手の右随伴への比較を持たない。 |
| 7.7.3.14 | partial → none |  | ExponentiableMorphismは通常圏の選んだpullback関手の右随伴の条件。原文の全slice準圏のcartesian closed性への比較がない。 |
| 7.7.3.17 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の指数可能な射の右随伴データと空間圏の小極限はある。SpaceInfinity の各スライスが Cartesian closed である型は見つからない。 |
| 7.7.3.19 | partial → none |  | 通常圏のpullbackPushforwardAdjは原文の∞圏のsliceの同じf*の右随伴との型の比較を含まない。 |
| 7.7.3.20 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏で指数可能な射の引き戻しを左随伴にし、左随伴は余極限を保つ。∞圏の ev₁ に対する弱余極限の descent を得る型は見つからない。 |
| 7.7.3.21 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の引き戻しが左随伴であれば余極限を保つ。終対象または K-余極限存在を仮定した∞圏で、K-余極限の普遍性までを述べる型は見つからない。 |
| 7.7.3.23 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：左ファイブレーション分類の特定の基底変換で κ-filtered 余極限の保存はある。SpaceInfinity で任意の小形状の余極限が普遍である型は見つからない。 |
| 7.7.4.1 | partial → none |  | CoproductDisjointの通常圏のMonoとIsInitialなstrict pullbackは、原文の∞圏の同じ余積・monomorphism・pullback条件との比較がない。 |
| 7.7.4.5 | partial → none |  | 通常圏のBinaryCoproductsDisjointは、原文の始対象と∞圏の二項余積の非交差性への型の比較を持たない。 |
| 7.7.4.8 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏で各余射影が単射かつ相異なる射影の引き戻しが始対象なら非交差余積を得る。CatInfinity の余積とその二射影がこの条件を満たす型は見つからない。 |
| 7.7.4.9 | partial → none |  | 通常圏のCoproductDisjoint.of_hasCoproductは原文の∞圏の二項非交差性から任意の同じIへの推論を結論しない。 |
| 7.7.4.10 | partial → none |  | 通常圏のvan Kampenと始対象のpullbackの結果は、原文の∞圏のstrongly universal性と非交差性のiffへの比較を持たない。 |
| 7.7.4.11 | partial → none |  | 通常圏のvan Kampen⇒universalと余射影のpullbackの始性は、原文の∞圏の三条件の同じ強普遍性への比較を欠く。 |
| 7.7.4.12 | partial → none |  | 通常のTypeの有限余積のvan Kampen性は、原文のSpaceまたはQC内の余積の強普遍性と同じ述語ではなく、その比較もない。 |
| 7.7.5.1 | partial → none |  | 通常圏のIsPushout.IsVanKampenはstrict cubeの条件。原文の∞圏のcoherentなcubeの二条件との比較を持たない。 |
| 7.7.5.6 | partial → none |  | 通常圏の厳密始対象のvan Kampen性は、原文の∞圏の全有限余極限の普遍性と二条件のiffに直接接続しない。 |
| 7.7.5.7 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の立方体判定と指定余錐の普遍性はある。κ-small な全余極限を κ-small 余積と第二立方体条件に還元する型は見つからない。 |
| 7.7.5.8 | partial → none |  | 通常圏のvan Kampenな始対象とcube条件は、原文の∞圏の二Mather条件による全有限余極限の強普遍性と比較されていない。 |
| 7.7.5.9 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏で指定押し出しの立方体条件と個別余錐の普遍性を記述する。両立方体条件と κ-small 余積の普遍性で全 κ-small 余極限を判定する型は見つからない。 |
| 7.7.5.10 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：空間圏の小余完備性と通常圏の van Kampen 述語はある。空間圏の全小余極限が強普遍である型は見つからない。 |
| 7.7.6.1 | partial → none |  | span・単射列・fat realizationのhomotopy pullback保存は部品。原文の指定Space余錐がstrongly universalであるという切断準圏の制限同値を直接結論しない。 |
| 7.7.6.2 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：左ファイブレーションの可縮ファイバーと filtered な底から全空間の Kan 置換が可縮となる。二つの引き戻しで指定された包含の弱同値性と延長射影の Kan 性を比較する iff は見つからない。 |
| 7.7.6.3 | partial → partial | direction | E′,Eを準圏に強めると、Γ自身がleft fibration⇒innerかつEquivalenceLiftingという二宣言が同じΓのisofibration性を直接与える。isofibration⇒left fibrationおよび任意の単体集合上ではない。 |
| 7.7.6.5 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：小さい左ファイブレーションの表現間で相対 Hom と変換空間を比較する型はある。Γ の Kan 性、Δ¹ の終点制限、各辺の引き戻し、γ の cartesian 性を比較する iff は見つからない。 |
| 7.7.6.6 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：固定宇宙での空間の小余極限はある。cf(λ)-small な形状で S_{<λ} の各余極限が強普遍となる型は見つからない。 |
| 7.7.6.7 | partial → none |  | 通常圏のIsVanKampenColimitのiffは、原文のS_<λの指定増強自然変換のcartesian性と余極限性への比較を持たない。 |
| 7.7.7.1 | none → partial | special | CをSpace、Kを小さいfiltered準圏、Lを有限形状に限るとsmallSpaceFilteredColimit_map_isLimit_finiteは同じcolimit functorのL極限保存（7.7.7.1の条件(3)）を直接返す。任意K,Lの四条件の全同値と閉性の判定は含まない。 |
| 7.7.7.2 | none → partial | special | CをSpace、Kを小さいfiltered準圏、Lを有限形状に限るとsmallSpaceFilteredColimit_map_isLimit_finiteは同じcolimit functorのL極限保存（7.7.7.1の条件(3)）を直接返す。任意K,Lの四条件の全同値と閉性の判定は含まない。 |
| 7.7.7.3 | partial → none |  | filtered余極限の有限極限保存はあるが、原文の「余極限が可縮な図式を張る全部分圏」の閉性を型に含まない。片側の交換性だけの証明はこのiffの一方向ではない。 |
| 7.7.7.4 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：切断で検出する局所対象の極限閉性と、固定宇宙の空間の小極限はある。濃度 μ の空間値関手のうち可縮余極限を持つ充満部分圏の極限閉性と、K-余極限・L-極限の交換との iff は見つからない。 |

## 検査

原文は Kerodon 公式小節の各項目Tagで照合。none は現本体・ロックしたMathlibを再検索し、近隣項目のソース・双対/限定版の候補も照合した。Archiveの宣言をown・partialの根拠にはしていない。宣言の存在と型はソースでの確認で、kernel確認ではない。
