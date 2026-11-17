# KB-W2 HA 第A章

原典の版を目次記載SHA-256と照合したPDFの本文と、現在のソースの宣言の型を読み比べた。kernel実行・Lean変更・ビルド・鍵はなし。

対象133行。旧状態：{'none': 123, 'partial': 10}。新状態：{'none': 125, 'partial': 8}。partial_kind：{'component': 7, 'stronger-hyp': 1}。

既存own・mathlibなど対象外2行は全フィールド・引用符・改行をそのまま保存。対象行でもstatus/declarations/reason/partial_kind以外は不変。axioms/checkは旧記録であり今回のkernel確認結果ではない。

## 全対象行

| 番号 | 旧→新 | partial_kind | 理由 |
| --- | --- | --- | --- |
| A.1.1 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：∞トポスのℼ∗ℼ∗のcorepresentabilityによるconstant shapeの定義は見つからない。通常のconstantSheafは、全空間のpro-objectとしてのshapeを持たない。 |
| A.1.2 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：shapeのpro-objectが定数であるという再表示は見つからない。通常の層の定数性は、∞トポス自体のshapeのcorepresentationとは異なる。 |
| A.1.3 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：constant shapeとℼ∗ℼ∗の全小極限保存のiffは見つからない。通常の随伴の極限保存は、shapeのcorepresentabilityの全判定を備えない。 |
| A.1.4 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：paracompact XのshapeをCW空間へのMapで計算する結果は見つからない。通常のCW複体の有限性は、Shv(X)の空間値global sectionと全Mapの比較を持たない。 |
| A.1.5 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：sliceのconstant shapeによるobjectのconstant shapeと局所constant shapeの定義は見つからない。通常のsliceと層は、この全∞トポスのshape述語を備えない。 |
| A.1.6 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：constant-shape objectの全小余極限閉性は見つからない。通常の層圏の余極限は、未構成のshape条件への閉性を比較しない。 |
| A.1.7 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：effective epiなcoverによるlocally constant shapeの局所判定は見つからない。通常のcoverは、この全sliceのshapeとeffective epimorphismの比較を持たない。 |
| A.1.8 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：locally constant shapeとgeometric morphism ℼ∗の左随伴の存在のiffは見つからない。通常のconstantSheafAdjは右側のglobal sectionsとの随伴であり、さらに左側のℼ!の存在判定ではない。 |
| A.1.9 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：ℼ!とℼ∗のhomotopy pullbackに沿うpush-pull同値は見つからない。通常のsheafの随伴は、このshapeの左随伴と全空間のfiber積の比較を持たない。 |
| A.1.10 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：ℼ!1と∞トポスのshapeの同定は見つからない。通常のglobal sectionsとconstantSheafは、この左随伴の空間値を構成しない。 |
| A.1.11 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：shape上のslice空間からXへのfully faithfulなψ∗は見つからない。通常の層の定数性は、この全空間sliceによる埋め込みを持たない。 |
| A.1.12 | partial → none |  | 通常の層の圏と原文の空間値Shv(X)・∞toposの同じ対象・射との比較が候補の型にない。通常の層の類似結果は、比較なしには原文の成分や特殊例としない。仮定：通常のsite上の集合値などの層、sheafificationが存在（Leanが強い：通常の層の場合）。結論：constantSheafを定数前層の層化で定め、constantをそのessential imageへの所属で定義する（最初のconstant objectの定義に一致する部分）。任意∞トポスの空間値objectとeffective epi coverによるlocally constantの定義は含まれない。 |
| A.1.13 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：任意geometric morphismによるconstant・locally constant objectの保存は見つからない。通常のconstantSheafのdense-site同値の不変性はあるが、全geometric morphismとeffective-epi局所化での両保存への比較はない。 |
| A.1.14 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：局所定数objectの開coverによる表示とparacompactならopen Fσへの改良は見つからない。通常の局所定数関数の有限clopen分割は、この空間値層と全open Fσ coverの構成ではない。 |
| A.1.15 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：S/shape(X)と局所定数objectの全圏の同値は見つからない。通常の定数層のessential imageは、この全空間値局所系の分類を持たない。 |
| A.1.16 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：局所constant shapeの∞トポスのlocally constant objectの全小余極限閉性は見つからない。通常の局所定数関数は、この全層objectの余極限との比較を持たない。 |
| A.1.17 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：locally constant objectのPostnikov完備性とhypercomplete性は見つからない。通常の集合値層は、この全高次truncationの逆極限の比較を備えない。 |
| A.2.1 | partial → none |  | 通常の層の圏と原文の空間値Shv(X)・∞toposの同じ対象・射との比較が候補の型にない。通常の層の類似結果は、比較なしには原文の成分や特殊例としない。仮定：閉区間の通常の集合値層に限定し、constantSheaf関手のFull・Faithfulを追加（Leanが強い：通常の模型とfully faithfulの追加仮定）。結論：定数層であることとconstant/global-sections随伴のcounitが同型であることが同値（(ii)⇔(iii)のこの場合に一致）。可縮区間からfully faithfulを導く部分、(i)の局所定数からの大域定数化、空間値層の高次比較は含まれない。 |
| A.2.2 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：可縮paracompact空間での空間値constant層関手のfully faithfulnessは見つからない。通常のconstantSheafはあるが、Xの可縮性から全高次Mapの同値を導く宣言はない。原典はπ∗をright adjointと印刷するが、前後のconstant層の文脈でもこの結論の比較はない。 |
| A.2.3 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：開・半開区間での局所定数・定数・counit同値の全同値は見つからない。通常の定数層のcounit判定はあるが、これらの区間の局所定数層をすべて定数にする比較はない。 |
| A.2.4 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：X×Rのhypercompleteかつ各R-leafでconstantなfoliated層の定義は見つからない。通常の局所定数関数は、この空間値層の全leaf制限とhypercompletionを持たない。 |
| A.2.5 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：foliated層と射影のpushforwardのhypercompletenessおよびcounit同値のiffは見つからない。通常のsheafのpullback/pushforwardは、このleafwise条件と全高次descentの比較を持たない。 |
| A.2.6 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：左随伴を持つgeometric morphismのhypercomplete object保存は見つからない。通常の随伴の極限保存は、∞connected射とhypercompletionの比較を持たない。 |
| A.2.7 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：étaleな∞トポスの射とsliceへのhypercomplete objectの保存は見つからない。通常のétaleサイトやsliceは、この空間値∞トポスのhypercompletionの比較ではない。 |
| A.2.8 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：locally compact・locally constant shapeな因子の射影のhypercomplete保存と追加条件でのfully faithfulnessは見つからない。通常のsheafのtensorや空間の積は、PrLのtensorとshapeの左随伴を構成しない。 |
| A.2.9 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：X×(0,1)の射影の空間値層pullbackのfully faithfulnessは見つからない。通常のcontinuous mapのpullbackは、この全層の高次Mapとunitの同値を持たない。 |
| A.2.10 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：閉・半開区間でも射影の空間値層pullbackがfully faithfulとなる結果は見つからない。通常の位相的区間の同相や可縮性は、sheaf pullbackの全Mapの比較を持たない。 |
| A.3.1 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：各点の開集合添字fiberの弱可縮性からSing(X)のhomotopy colimit表示を得るvan Kampenは見つからない。通常のcoverと相対関手空間は、全Sing図式のcoherent余極限を構成しない。 |
| A.3.2 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：covering sieveのSing図式のhomotopy colimitがSing(X)となる結果は見つからない。通常のsheafのcover descentは、Singのこのcosheaf側の∞余極限の比較ではない。 |
| A.3.3 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：開cover内に入るsmall singular simplexの部分集合の包含が弱同値となる結果は見つからない。単体細分関手はあるが、任意位相空間の全coverと特異単体の像の制御を持たない。 |
| A.3.4 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：compact Xから単体集合の実現への連続写像が有限部分単体集合の実現を経由する定理は見つからない。通常のCW複体の有限性はあるが、一般SSetの実現とのCW比較と当該有限部分複体への因子化はない。 |
| A.3.5 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：各有限部分集合の実現を相対homotopyでK0へ動かせることから包含の弱同値を導く定理は見つからない。一般のKan弱同値判定は、この位相的実現の有限homotopy仮定からの比較を持たない。 |
| A.3.6 | partial → partial | component | KB-W2原文・型再照合：仮定：単体集合Kと各有限順序[n]（HAと一致）。結論：非空有限鎖（[n]では非空部分集合）のnerveからsdを左Kan延長で構成し、exとの随伴からsdが余極限を保つ（最初の細分functorの構成に一致する部分）。拡大posetによるsd-barとその実現の実現(K)×[0,1]への同相、両端の貼込みは含まれない。 |
| A.3.7 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：paracompact Xのcovering sieveをopen Fσに制限したvan Kampenは見つからない。通常のparacompact性は、このSing図式のhomotopy colimitへの比較を持たない。 |
| A.3.8 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：Sing(U)のYoneda延長がShv(X)を経由する余極限保存関手となる構成は見つからない。通常の層化は、この空間値Singのcosheaf側の全余極限普遍性を持たない。 |
| A.3.9 | partial → none |  | 通常の層の圏と原文の空間値Shv(X)・∞toposの同じ対象・射との比較が候補の型にない。通常の層の類似結果は、比較なしには原文の成分や特殊例としない。仮定：通常の集合値層の射α（Leanが強い：0-truncatedな通常の層模型）。結論：αが同型であることと全点のstalk射が同型であることが同値（通常の集合値層でのstalkによる同値判定に一致）。一般空間値層の∞connective射の述語、0-truncated模型との比較、および非hypercomplete対象も含む全主張は含まれない。 |
| A.3.10 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：Singから作るShv(X)→Sが∞connective射を同値に送る結果は見つからない。通常のstalk同型判定は、この全高次hypercompletionとshape functorの比較を持たない。 |
| A.4.1 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：CW空間での局所系の文献上の議論は見つからない。通常のCW複体はあるが、当該局所定数層の理論への比較を形式化しない。 |
| A.4.2 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：geometric morphismのshape equivalenceの定義は見つからない。通常の層の随伴は、ℼ∗ℼ∗の空間値shape比較を持たない。 |
| A.4.3 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：constant shapeと空間sliceからのshape equivalenceの存在のiffは見つからない。通常のsliceは、この全空間のpro-shapeのcorepresentationを構成しない。 |
| A.4.4 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：連続写像の引き起こすgeometric morphismによるshape equivalenceの定義は見つからない。通常のsheaf pullbackは、この∞shapeの述語を持たない。 |
| A.4.5 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：paracompact空間のshape同値を全CW空間へのMapの同値で判定するiffは見つからない。通常のcontinuous mapは、この全高次Mapとsheafのshapeの比較を持たない。 |
| A.4.6 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：X×R→Xのshape equivalenceは見つからない。通常の射影のhomotopy equivalenceは材料だが、shapeの全空間値関手の比較への接続はない。 |
| A.4.7 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：全topological homotopy equivalenceがshape equivalenceとなる結果は見つからない。通常のhomotopyはあるが、このsheafのshapeの比較を構成しない。 |
| A.4.8 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：一般空間とparacompact空間での古典的strong shape equivalenceとの違いは見つからない。通常の位相同値は、pro-shapeと強shapeの二概念の比較ではない。 |
| A.4.9 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：実現とSingのcounitのshape同値によるsingular shapeの定義は見つからない。実現・Singの随伴はあるが、shape equivalenceという追加の型を備えない。 |
| A.4.10 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：singular shapeなXのShv(X)がconstant shapeとなる結果は見つからない。実現の模型はあるが、空間値層のpro-shapeとの同定はない。 |
| A.4.11 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：homotopy equivalenceによるsingular shapeのiffは見つからない。通常のSingのhomotopy不変性は、未構成のshape述語の不変性を持たない。 |
| A.4.12 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：paracompact Xのsingular shapeと全CW終域のMap(X,Y)→Map(SingX,SingY)の同値のiffは見つからない。通常のSing随伴は、このshapeの全CW試験の判定を備えない。 |
| A.4.13 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：Singによる弱型とCWへのMapによるpro-shapeの二つの型の比較は見つからない。通常のKan複体はあるが、SingX→Sh(X)とそのshape判定はない。 |
| A.4.14 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：開coverの全非空有限交叉のsingular shapeからXのsingular shapeを得る結果は見つからない。通常の有限交叉とcoverは、この全Sing-shapeのdescent比較を持たない。 |
| A.4.15 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：全開部分集合のsingular shapeによるlocally singular shapeの定義は見つからない。通常の開集合は、このshapeの専用述語を持たない。 |
| A.4.16 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：locally singular shapeの開coverによる局所性は見つからない。通常の局所定数関数の局所性は、この全open subsetのshape同値の比較ではない。 |
| A.4.17 | partial → partial | component | KB-W2原文・型再照合：仮定：Y→Sing(X)とSing(U)→Sing(X)を指定（HAの入力に一致する単体集合模型）。結論：底上の全単体的写像空間Fun_SingX(Sing(U),Y)をinternal Homのfiberで構成する（θ(U,Y)の値の式に一致する部分）。θ全体の関手性、モデル圏のfibrant-cofibrant比較、層条件、ΨXとその全nerveの構成は含まれない。 |
| A.4.18 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：K↦K×SingXから空間値層ψとconstant sheafへの比較を作りsingular shapeを判定する構成は見つからない。相対functor spaceはあるが、この全sheafificationとshapeの比較がない。 |
| A.4.19 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：SingX上のKan fibrationのnerveから局所定数空間値層へのfully faithfulなΨと本質像の分類は見つからない。相対関手空間はあるが、全層条件と局所定数層を回復する同値の比較はない。 |
| A.5.1 | partial → partial | component | KB-W2原文・型再照合：仮定：半順序集合A（HAと一致）。結論：開集合を上方閉集合とするAlexandrov位相を与える（冒頭の位相の定義に一致）。任意Xからの連続写像にstratificationという名を与える専用型と五つのstratumの族は含まれない。 |
| A.5.2 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：各stratumへの制限が局所定数となるconstructible空間値層の全部分圏は見つからない。通常の局所定数関数と層は、この全strataの高次sheaf pullback条件を持たない。 |
| A.5.3 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：弱位相を持つopen coneとWithBot(A)へのstratificationは見つからない。通常のWithBotと積は、この無限遠点に近づく一様な近傍位相と連続な全射を構成しない。 |
| A.5.4 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：compact Hausdorff Xのopen coneとR≥0上のpushoutとの同相は見つからない。通常のpushoutは、このopen coneの特有の近傍位相との比較を持たない。 |
| A.5.5 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：stratifiedなZ×C(Y)のopen embeddingによるconical stratificationは見つからない。通常の開埋込みは、open coneと全strata条件を組にした型を備えない。 |
| A.5.6 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：conical stratificationのlink Yに再帰的conical性を要求しないという規約は見つからない。通常の層・空間は、この専用述語とその非再帰的な定義を持たない。 |
| A.5.9 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：paracompact・locally singular shape・conical ACCでのconstructible層のPostnikov完備性は見つからない。通常のstalk判定は、この全空間値層のtruncation逆極限と高次convergenceを備えない。 |
| A.5.10 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：open-closed recollementの三つの弱可縮図式の極限条件から全体の極限を得る結果は見つからない。通常のsheafの極限は、この∞トポスの三関手のjoint limit判定に比較されていない。 |
| A.5.11 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：openとclosed complementへの制限が同値なら全体が同値となる結果は見つからない。通常のstalk同型判定はあるが、両制限のstalkを組み合わせる当該recollementの宣言はない。 |
| A.5.12 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：X×C(Y)の零sectionの全開近傍内に正の連続半径fで定めるVfを選ぶ結果は見つからない。一般のparacompact性は、この未構成のopen coneの一様近傍と連続minorantの比較を持たない。 |
| A.5.13 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：Vfの非空性・minによる交叉閉性・全零section近傍でのcofinal性は見つからない。通常の連続関数のminはあるが、open cone上のVfと全近傍posetのcofinal性を構成しない。 |
| A.5.14 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：半直線の開部分からのsheaf direct imageと射影pullbackの比較同値は見つからない。通常のsheaf pullbackは、この空間値sheafの境界での全比較を持たない。 |
| A.5.15 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：open coneの零sectionとlinkのpushforwardに関する三つの自然同値は見つからない。通常の層の随伴は、このconeの近傍と空間値global sectionの比較を備えない。 |
| A.5.16 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：conically stratifiedなparacompact空間にopen Fσのconical chartを選ぶ結果は見つからない。通常の局所定数のclopen chartは、この全stratificationのcone chartへの改良ではない。 |
| A.5.17 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：ACC posetのmexで特徴づけるordinal rankとstratified空間のrankは見つからない。WellFounded.rankはあるが、上方元のrankの最小欠落ordinalという式とその一意性の比較、および全strataのrankは確認できない。 |
| A.5.18 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：Z×C(Y)がparacompact・singular shapeならZもそうなる結果は見つからない。閉部分集合のparacompact性は部品だが、open coneの閉embedding・homotopy equivalenceとshapeへの接続がない。 |
| A.5.19 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：conical ACC stratificationの各stratumがlocally singular shapeなら全体もそうなる結果は見つからない。通常のwell-founded帰納と開coverは、この全shapeの近傍descentを構成しない。 |
| A.6.1 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：MacPherson・Treumannのexit path 2圏との関係の文献上の説明は見つからない。通常のpathはあるが、このstratified exit pathの高次比較を持たない。 |
| A.6.2 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：重心座標の最終非零成分のstratum条件によるSingA(X)の部分単体集合は見つからない。Singと順序のnerveはあるが、当該stratifiedな全単体の族を構成しない。 |
| A.6.3 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：N(A)→Sing(A)の最終非零成分による自然射とSingAのpullback表示は見つからない。upper-set位相はあるが、この特定の連続単体の族とexit pathの比較がない。 |
| A.6.4 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：conical stratificationからSingA→N(A)のinner fibration・準圏性・同値辺の判定を得る三結論は見つからない。一般のinner fibrationの充填は、この位相的conical仮定からの全inner horn liftingを持たない。 |
| A.6.5 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：準圏SingAをexit path圏と呼ぶ記法は見つからない。通常のSingのKan性は、当該stratifiedな部分単体集合の準圏性を構成しない。 |
| A.6.6 | partial → partial | component | KB-W2原文・型再照合：仮定：頂点の型V（HAと一致）。結論：非空有限部分集合の下方閉族をfacesとして持つ抽象単体複体のデータを定義する（(1)(2)に一致する部分）。locally finiteの専用述語、線形順序を選んだ単体集合とその実現、重み付き点による全表示は含まれない。 |
| A.6.7 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：単体複体の実現のsupportによるface-posetへの連続stratificationは見つからない。abstract complexのfacesはあるが、この実現上のsupport mapとupper-set位相の連続性の比較はない。 |
| A.6.8 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：locally finite抽象複体のsupport stratificationがconicalとなる結果は見つからない。abstract complexはあるが、幾何的実現のlinkとopen coneのchartを構成しない。 |
| A.6.9 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：任意抽象複体のsupport exit pathの準圏性は見つからない。通常の複体のfacesは、この全exit pathのinner horn充填の比較を持たない。 |
| A.6.10 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：抽象複体のexit path圏とface-posetのnerveの圏同値は見つからない。通常の細分関手はあるが、この特定の実現上のexit pathと全Mapの同値の比較はない。 |
| A.6.11 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：faceの重心の線形補間によるexit-path圏同値の明示的逆と細分の同相は見つからない。sdの単体的構成はあるが、実現とstratum条件に沿うこの逆写像と全同相を構成しない。 |
| A.7.1 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：開coverの点添字の弱可縮性からexit-path圏のCat∞余極限表示を得るvan Kampenは見つからない。一般の相対関手空間は、この全conical位相空間のSingAの余極限を構成しない。 |
| A.7.2 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：単一stratumでexit-path van Kampenが通常のSingの定理に還元される比較は見つからない。Singはあるが、未構成のSingAと全余極限の二定理を比較しない。 |
| A.7.3 | partial → partial | component | KB-W2原文・型再照合：仮定：p:E→N(A)をexit-path射影の入力模型として指定し、chain aを∆n→N(A)で与える（HAの式の入力に一致）。結論：内部Homからchainの点へのfiberでFun_{N(A)}(∆n,E)を構成する（SingA(X)[a]の表示に一致）。位相空間からのE=SingA(X)自体の構成は含まれない。 |
| A.7.4 | partial → partial | stronger-hyp | KB-W2原文・型再照合：仮定：p:E→N(A)がleft fibrationである場合に限定（Leanが強い：HAのinner fibrationに代えてleft fibrationを追加）。結論：任意∆n→N(A)上のrelativeFunctorSpaceはKan complex（表示された固定chainのfiberのKan性に一致）。conicalなXからSingAを構成し一般inner fibrationの場合にも適用する比較は含まれない。 |
| A.7.5 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：単一頂点aの固定stratumの相対図式空間をSing(Xa)に同定する結果は見つからない。一般のrelativeFunctorSpaceはあるが、SingAとstratumへの制限を構成しない。 |
| A.7.6 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：正の長さのstratified pathを初点近くで割ったgermの単体集合は見つからない。通常のgermとpathは、この各次数の全連続族の同値関係を備えない。 |
| A.7.7 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：全exit pathからgermへの射が弱同値となる結果は見つからない。一般のgermとKan弱同値は、この特定の全pathの延長と初点制御を持たない。 |
| A.7.8 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：conical stratificationでgermから初点stratumへの射がKan fibrationとなる結果は見つからない。一般のleft/inner fibrationは、この位相的germの全境界充填を構成しない。 |
| A.7.9 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：開部分集合の固定stratum-chainのexit path空間のsquareがhomotopy pullbackとなる定理は見つからない。一般のpullbackは、この全path-germ比較と初点の位相的制限を持たない。 |
| A.7.10 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：Cat∞の各∆nからのMapで作るsimplicial spaceへのfully faithfulな埋込みは見つからない。通常のnerveはあるが、全Cat∞の空間値Rezk nerveと全Mapの比較はない。 |
| A.7.11 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：上記埋込みの本質像をcomplete Segal spaceと同定する結果は見つからない。通常のnerveと豊穣関手は、この全simplicial spaceのSegal・complete条件と圏同値を構成しない。 |
| A.8.1 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：有限極限圏の二つの反射的全部分圏の五条件によるrecollementの定義は見つからない。native半直交分解はあるが、二つともleft-exactな左随伴とjoint conservativityを持つこの全型とは比較されていない。 |
| A.8.2 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：recollementの二因子の順序が一般には交換できないという注意は見つからない。通常の片側半直交性はあるが、二つの全recollement述語と反例の比較がない。 |
| A.8.3 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：反対圏によるcolocalization版のrecollementの定義は見つからない。通常のopと半直交分解は、この全五条件の双対版の専用型を持たない。 |
| A.8.4 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：集合値層の開・閉部分へのpushforwardの像によるrecollementは見つからない。stalk同型判定とsheafの随伴はあるが、これら二反射の全五条件を束ねる宣言はない。 |
| A.8.5 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：recollementのC0をL1の終対象kernelと同定しpointedならi*の右随伴をfiberで作る結果は見つからない。lax半直交分解のkernel同定はあるが、HAの二つのleft localizationを備えた任意recollementと右随伴の全比較には新しい表示・証明が必要である。 |
| A.8.6 | none → partial | component | 同じ対応p:M→Δ¹についてCartesianFibrationは条件(ii)そのもの。各fiberの有限極限はHasFiniteLimitsで表す。分類される関手のleft exact性は含まない。 |
| A.8.7 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：left-exact correspondenceのsection圏の二反射によるrecollementは見つからない。通常の相対functor spaceはあるが、sectionの終対象・Cartesian条件の二反射を構成しない。 |
| A.8.8 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：correspondence間の関手をsection圏のlocalization同値保存関手で分類するfully faithfulな埋込みは見つからない。一般の相対関手空間は、この二種類のL同値と全Mapの比較を持たない。 |
| A.8.9 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：上記fully faithfulnessで始域Cartesianと一方fiberの終対象に仮定を弱める結果は見つからない。通常のsectionは、この全局所同値保存による本質像を分類しない。 |
| A.8.10 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：section圏の関手の左完全性を二fiberで判定しCartesian辺保存をC1の保存に同定する結果は見つからない。一般のCartesian射は、この二反射付きsection圏の全比較を持たない。 |
| A.8.11 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：任意recollementをleft-exact correspondenceのsection圏として表す存在は見つからない。native lax gluingはあるが、任意の二反射からこの全対応を作る同値はない。 |
| A.8.12 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：recollementとC1→C0の左完全関手との辞書は見つからない。個別のnative gluingはあるが、任意recollementに関するこの全分類の比較を持たない。 |
| A.8.13 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：C0に始対象があればj*のfully faithfulな左随伴j!が存在する定理は見つからない。native半直交分解は二つの随伴を持つが、任意recollementの追加のj!の構成ではない。 |
| A.8.14 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：二因子上の同値・左完全性・gluing変換両立からrecollement全体の圏同値を得る判定は見つからない。一般のfully faithful判定は、この全二反射とgluingの比較を持たない。 |
| A.8.15 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：recollement全体が∞トポスとなることと両因子の∞トポス性・accessibleなgluingのiffは見つからない。通常の層とpresentable圏は、この二反射の全トポス認識とopen-closed objectの分類を持たない。 |
| A.8.16 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：accessible左完全関手による二つの∞トポスのgluingと全幾何学的射の辞書は見つからない。通常のDG gluingは、この全空間値∞トポスの反射による分類とは異なる。 |
| A.8.17 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：recollement全体のstable性と両因子stable・gluing exactのiffは見つからない。laxPullback_isStableとDG gluingの無条件stable構造はあるが、任意HA-recollementをそのlax模型に表示する比較がなく、このiffを直接結論しない。 |
| A.8.18 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：stable recollementとexact gluing functorの分類は見つからない。native安定lax gluingはあるが、任意の二因子recollementの全Mapと逆構成の比較がない。 |
| A.8.19 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：stable recollementの六つの随伴を備える図式は見つからない。DGのH0射影の随伴とnative半直交分解の二随伴はあるが、任意recollementの三組の∞随伴と全fully faithfulnessの構成ではない。 |
| A.8.20 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：stable全部分圏の包含が両随伴を持つこととrecollementの存在のiffおよび直交補圏の同定は見つからない。native半直交分解のkernelとMap可縮性はあるが、任意のadmissible部分圏から二反射を作る比較を持たない。 |
| A.9.1 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：SingA上のcovariant model categoryとopen Fσの空間値sheaf圏およびstraighteningの同値の鎖は見つからない。一般のleft fibration模型はあるが、未構成のSingAと当該全層圏への比較を持たない。 |
| A.9.2 | partial → partial | component | KB-W2原文・型再照合：仮定：p:Y→SingA(X)をleft fibration、a:SingA(U)→SingA(X)を指定（HAのfibrant入力の単体的条件に一致）。結論：底上のrelativeFunctorSpaceを定め、その値がKan complexとなる（θ(U,Y)の式とKan性に一致する部分）。位相的SingAの構成、全(U,Y)でのfunctoriality、covariant model structureとcoherent nerve、およびΨX全体の構成は含まれない。 |
| A.9.3 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：conical ACC・locally singular shapeでのleft fibrationとconstructible sheafの圏同値は見つからない。一般のrelativeFunctorSpaceは、この全sheaf条件とconstructibilityの本質像を分類しない。 |
| A.9.4 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：exit path圏から全Singへの包含の弱homotopy同値は見つからない。通常のSingと弱同値判定はあるが、stratified部分単体集合とshapeの比較がない。 |
| A.9.5 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：left fibrationから作るΨXのsheaf条件は見つからない。相対関手空間のKan性はあるが、open Fσ coverに対する高次descentの全比較を持たない。 |
| A.9.6 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：ΨXの各開集合の評価のcorepresentabilityと全小極限保存は見つからない。一般のrepresentableの極限保存は、当該未構成のΨと層条件との比較を持たない。 |
| A.9.7 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：ΨXのn-truncated object保存と全像のhypercompletenessは見つからない。通常の集合値層は、この全Postnikov極限と空間値Ψの比較を持たない。 |
| A.9.8 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：open Fσ部分集合でのΨXのsheaf pullbackと相対left fibrationのpullbackの厳密同型は見つからない。一般のpullbackは、この全層のΨの自然変換への比較を持たない。 |
| A.9.9 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：stratumへの制限に対するΨの基底変換同値は見つからない。通常のstalk pullbackは、この空間値ΨとSingAのstratum比較を構成しない。 |
| A.9.10 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：ΨXの像のconstructibilityは見つからない。通常の局所定数関数は、この全stratumの空間値層の局所定数性を結論しない。 |
| A.9.11 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：Z×C(Y)→Zのsheaf pullbackのfully faithfulnessは見つからない。通常のhomotopy equivalenceは、このopen coneと全空間値sheafのMap比較を備えない。 |
| A.9.12 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：coneから零sectionへのfoliated層のglobal sectionの同値は見つからない。通常のsheafのgermは、このleafwise空間値層と境界sectionの比較を持たない。 |
| A.9.13 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：constructible層の開部分へのj!と零sectionpullbackの本質像による双対recollementは見つからない。nativeDG gluingは、この位相的cone上の空間値層の二反射を構成しない。 |
| A.9.14 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：conical・locally singular shapeでのconstructible層の有限余極限閉性は見つからない。通常のsheaf余極限は、この全stratumの高次局所定数性の条件と比較されていない。 |
| A.9.15 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：ACC stratificationでのΨXの有限余極限保存は見つからない。一般のleft fibrationは、この全sheaf-valued Ψのfinite colimit比較を持たない。 |
| A.9.16 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：conical ACC stratified空間の全連続写像でのΨのsheaf pullback基底変換同値は見つからない。通常の随伴は、この全SingAとconstructible sheafの同値に沿う自然性を持たない。 |
| A.9.17 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：singular-shape空間の各点にSing(U)→Sing(X)がnullhomotopicとなる開近傍を選ぶ結果は見つからない。通常のcontractible近傍は、このshape仮定だけからの局所nullhomotopyを与えない。 |
| A.9.18 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：retraction付きcorrespondence上のfunctor圏の二種類の右Kan・Cartesian条件によるrecollementは見つからない。相対functor spaceとKan普遍性はあるが、この二反射とjoint conservativityの全比較を持たない。 |

## 読取りと再検索

原文・候補の型・現在の引用番号索引・小節ごとの現本体とロックMathlibの再検索はgit外の章別証拠。OE-W1 module-mapと宣言索引を使って移動後の名前・所在・行を確認した。ArchiveとBS draftsの宣言は正の根拠にしない。検索の全ヒットを形式検証したという意味ではない。
