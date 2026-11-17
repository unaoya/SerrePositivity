# KB-W1 / B6 第3章

原文の項目と現在のソースの型による紙の再照合。Lean・ビルド・鍵は使っていない。

対象 274行。partial 121、none 153。判定後：none 232、partial 42。

既存 own・both・mathlib 65行の全既存フィールドは変更なし。既存7列の末尾に partial_kind を追加し、対象外行は空欄とした。区切り・改行と対象外行の既存引用符を保存した。verdict・axioms・check も変更していない。古いcheck欄は今回のkernel検査結果ではない。

## 全対象行の判定・変更一覧

状態不変でも型/原文の再判定を記録した。各 reason の詳細はCSVと同じ。原文全文・候補の型・検索はgit外の章別証拠。

| 番号 | 旧→新 | partial_kind | 理由 |
| --- | --- | --- | --- |
| 3.1.2.10 | partial → none |  | B6：anodyne 性は原文の指定射間の retract の射と往復恒等式を与えない。 候補：指定形状の積の部分複体の包含の anodyne 性は pairing で示される。ホーン包含からの指定のレトラクトは未確認。 |
| 3.1.2.11 | partial → partial | stronger-hyp | B6：isPushout_prism_mono_cell は原文の和と逆像の条件から同じ押し出し正方形を直接返す。セル σ に Mono を加える場合に限定。 |
| 3.1.3.5 | partial → partial | special | B6：trivialKanFibration_pre_of_anodyne は底 S が終対象のときの同じ制限射の自明 Kan 性。pullbackObjObjπ は p 自身が自明 Kan の場合も直接扱う。一般の底上の任意の Kan fibration の主張は含まない。 |
| 3.1.3.13 | partial → partial | stronger-hyp | B6：relativeFunctorExtensionSpace_isContractibleKan は同じ指定境界と底を持つ延長空間の可縮 Kan 性を直接返す。i を left anodyne とする追加仮定で、Kan fibration は left fibration でもある。一般の anodyne i 全体の後半は含まない。 |
| 3.1.3.14 | partial → partial | component | B6：anodyneExtensionChoices_isContractibleKan は原文後半の、i が anodyne の場合の指定延長空間の可縮 Kan 性を直接返す。単射だけの場合の前半を含まない。 |
| 3.1.4.1 | none → none |  | B6：現本体・固定Mathlibを再検索。確認済み・なし。全ホーンに一意な持ち上げを要求する単体集合の被覆写像の型は未発見。位相・箙の被覆は別。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.1.4.7 | none → none |  | B6：現本体・固定Mathlibを再検索。確認済み・なし。相対内部 Hom の Kan fibration 性はあるが、一意な持ち上げを保つ被覆版は未発見。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.1.4.8 | none → none |  | B6：現本体・固定Mathlibを再検索。確認済み・なし。後合成の fibration 性はあるが、一意持ち上げの被覆版は未発見。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.1.4.9 | none → none |  | B6：現本体・固定Mathlibを再検索。確認済み・なし。位相被覆と特異単体集合はあるが、特異化が一意なホーン持ち上げを保つ宣言は未発見。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.1.4.12 | none → none |  | B6：現本体・固定Mathlibを再検索。確認済み・なし。単体写像による全引き戻し条件や、標準単体上の成分ごとの同型による被覆の特徴づけは未発見。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.1.4.14 | none → none |  | B6：現本体・固定Mathlibを再検索。確認済み・なし。単射に対する直和成分・被覆・Kan fibration の三条件の比較は未発見。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.1.5.10 | partial → partial | component | B6：HomotopyClasses.obj は π₀ Fun(X,Y)、pre/post は代表の合成による写像を直接構成する。Kan に対象を限れば原文の Hom と前後合成の構成成分。同じ Hom を射とする束ねた圏そのものは含まない。 |
| 3.1.6.3 | partial → none |  | B6：包含順の coherent nerve の構成であり、原文の逆包含 nerve と低次比較への同定がない。 候補：一般の単体圏で普通 nerve から coherent nerve への写像があり、KanObject に特殊化できる。単射性と全低次単体の比較は未確認。 |
| 3.1.6.9 | none → none |  | B6：現本体・固定Mathlibを再検索。確認済み・なし。KanObject の単体的 Hom はあるが、各 Hom のホモトピー圏を持つ厳密双圏 h₂Kan は未発見。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.1.7.1 | partial → partial | stronger-hyp | B6：IsSimplicialHomotopyEquivalence は同じ f,g の両合成について一段の区間ホモトピーを持つ場合を直接表す。原文の有限鎖によるホモトピーより強い仮定に限定。 |
| 3.1.7.6 | partial → partial | special | B6：isSimplicialHomotopyEquivalence_of_postcomposition_piZero_bijective は原文の第三条件から第一条件への向きを Kan の始域・終域に限って直接返す。三条件一般の iff は含まない。 |
| 3.1.7.9 | partial → none |  | B6：自然変換からのホモトピーは証明部品であり、随伴関手の nerve の逆と両側ホモトピーを結論していない。 候補：自然変換から nerve の単体ホモトピーを構成する補助宣言はある。任意の左・右随伴についてのホモトピー同値の結論は未確認。 |
| 3.1.7.10 | partial → none |  | B6：切断の存在と同じ底上のホモトピーは材料。ホモトピー逆の存在をまとめる直接の結論はなく、原文の有限鎖との比較も必要。 候補：一般の自明 Kan fibration に切断があり、同じ底上の二つの持ち上げはホモトピック。一般のホモトピー同値を一つにまとめた宣言は未確認。 |
| 3.1.7.13 | partial → partial | stronger-hyp | B6：前向きの型は一段のホモトピー逆を持つ f から同じ f の弱同値性を直接返す。有限鎖での逆だけより強い仮定。Kan の場合の逆向きも引用型にある。 |
| 3.1.7.18 | none → none |  | B6：現本体・固定Mathlibを再検索。確認済み・なし。引用は単体加群の正規化の擬同型を検査する。単体集合の自由整数鎖写像の鎖ホモトピー同値は未発見。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.1.8.6 | partial → none |  | B6：引用は anodyne を反転する SSet 上の関手。原文は Kan 上の任意の関手で、二つの条件のいずれの含意も引用の結論ではない。 候補：SSet 上で anodyne を反転する関手はホモトピックな射を同じ射へ送る。Kan 上の関手の二条件の同値は未確認。 |
| 3.1.8.7 | partial → none |  | B6：homEquiv は対象ごとの局所化 Hom の比較で、原文の関手圏間の同型の構成ではない。 候補：anodyne 局所化で Kan 標的への射をホモトピー類と比較。hKan からの関手圏の指定同型は未発見。 |
| 3.1.8.8 | partial → none |  | B6：自明 fibration の反転と局所化 Hom の比較は、指定の関手圏の同値という結論の成分でなく材料。 候補：anodyne 局所化の射の比較と自明 Kan fibration の反転はある。弱同値を反転する関手の圏と Fun(hKan,C) の同値は未確認。 |
| 3.1.8.12 | none → none |  | B6：現本体・固定Mathlibを再検索。確認済み・なし。全ホーンの分解はあるが、閾値より高次のホーンだけを添付し低次の単体を保つ分解は未発見。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.2.1.1 | partial → none |  | B6：RelativeMorphism の生成同値の商と、原文の相対内部 Hom の頂点ファイバーの π₀ の同定がない。 候補：同じ K 上の制限を固定した写像を、K 上一定の円柱ホモトピーで生成する関係で割る。引用では原文の相対内部 Hom の頂点ファイバーの π₀ と直接同定していない。 |
| 3.2.1.4 | partial → none |  | B6：引用の exists_extension は既に指定された H の延長であり、原文の相対ホモトピー関係の有限鎖/一段との iff を直接述べない。 候補：一般の RelativeMorphism.HomotopyClass は相対ホモトピーの生成同値で割る。原文の写像空間の成分との比較と、Kan 標的で一段に縮める一般の相対同値は未確認。 |
| 3.2.1.5 | partial → partial | component | B6：PointedSimplicialSet は PointedObject SSet で、原文の点付き単体集合と基点を保つ射を直接与える。Kan の対象だけに絞る Kan_* の圏の構成は含まない。 |
| 3.2.1.7 | partial → partial | component | B6：pointedRelativeHomotopy は円柱が全時刻で基点を保つという原文の pointed homotopy のデータを直接構成する。生成した点付きホモトピー関係と写像空間の成分との iff は含まない。 |
| 3.2.1.10 | partial → none |  | B6：一点の相対ホモトピー商と、原文の点付き写像空間の π₀ の比較がない。 候補：RelativeMorphism.HomotopyClass を一点の部分複体に特殊化すると、基点固定ホモトピーで生成した商を得る。原文の点付き写像空間の π₀ との同定は未確認。 |
| 3.2.1.12 | none → none |  | B6：現本体・固定Mathlibを再検索。点付き単体集合の普通圏と相対ホモトピー類の型は別々にある。点付き Kan 複体を対象、基点固定ホモトピー類を射とする商圏は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.2.1.13 | partial → partial | stronger-hyp | B6：exists_pointedHomotopyInverse は全基点・全次数の π 同型という強い仮定から、原文の基点固定の両側逆と二つのホモトピーを直接返す。kanPiIsomorphism_of_homotopyEquivalence も同じ f に対する一段の逆からこの仮定を返す。有限鎖だけの非点付き逆からの完全な iff は含めない。 |
| 3.2.1.14 | none → none |  | B6：現本体・固定Mathlibを再検索。PointedKanWhitehead は全次数の π 同型から点付き両側逆を作る。任意に指定した片側の逆と非点付きホモトピーだけを基点固定へ直す宣言は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.2.1.15 | none → none |  | B6：現本体・固定Mathlibを再検索。pointedRelativeHomotopy は既に基点を固定する円柱を受け取る。自由な null homotopy の存在から基点固定の null homotopy を得る宣言は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.2.2.4 | partial → none |  | B6：球面からの点付き写像のホモトピー類との比較がなく、境界定値単体の別の商だけでは同じ π_n の構成を得ない。 候補：KanHomotopy X n x は境界を x に固定した標準 n 単体の商で、n=0 と正次数を分ける。球面は cofiber で構成できるが、球面からの点付きホモトピー類との比較は未確認。 |
| 3.2.2.5 | partial → partial | component | B6：PtSimplex は境界が x に定値な標準単体という原文前半の代表データを直接与える。球面からの射との同定と、類の等式 iff 境界固定のホモトピーという後半は含まない。 |
| 3.2.2.10 | partial → none |  | B6：定義された群の台は独自の境界定値単体の商で、原文の球面からの写像の商との同一視がない。群構造の存在・可換性だけでも同じ対象の結論にする比較が要る。 候補：KanHomotopyGroup X n x は π_(n+1) で群、n≥1 なら可換群。SphericalBoundary.boundary_filler_iff は面がすべて基点に境界固定のとき、π_(n+2) の交代和零と充填の同値を与える。π₁ での順序付き交代積と、条件を満たす群構造の一意性は未確認。 |
| 3.2.3.1 | partial → partial | component | B6：PtSimplex は原文の Σ の定義を直接与える。SphericalBoundary の引用は高次の面族についてだが、全次数での bounds と π への全射の一式は含めない。 |
| 3.2.3.2 | partial → partial | special | B6：boundary_filler_iff では n+2 次元の全ての球面的面族の充填可能性が alternatingClass=0 のみで決まる。各代表の類を固定すればこの式は変わらず、原文の不変性が直接得られる。π₁ の一般の面族は含まない。 |
| 3.2.3.4 | partial → none |  | B6：MulStruct/FourStruct は特定の定数面を置く充填。任意の他の全ての面を与えたときの残る類の一意存在は直接返さない。 候補：三面の積の充填と特定の四面の充填がある。任意の i を欠いた全ての面族に対する残る類の一意存在の宣言は未確認。 |
| 3.2.3.5 | partial → none |  | B6：mul_unique_at は同じ二つの MulStruct の出力の類が等しい命題。原文の任意の η の bounds iff η_i=m_i(...) と関数の一意存在は含まず材料。 候補：最後の三面で定まる群の積と、その充填での類の決定を確認。各 i の m_i の一意性は未確認。 |
| 3.2.3.6 | partial → partial | component | B6：degenerate_face は原文に明記された二面が σ、他の面が e という退化単体の式そのもの。全ての m_i についての両単位則まではこの宣言の結論にない。 |
| 3.2.3.7 | partial → none |  | B6：FourReduction は特定の四面の式であり、任意の全ての面族が bounds のままであるという原文の結論ではない。 候補：最後の四面で充填を合成して類の等式を得る。全ての i で面二つを左から掛け直しても元の列が境界を成すという全体の主張は未確認。 |
| 3.2.3.8 | none → none |  | B6：現本体・固定Mathlibを再検索。AdjacentProduct.flip は特定の隣接位置の二つの積を反転する。任意の i での m_i と m_(i−1) の三変数交換則は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.2.3.9 | partial → none |  | B6：AdjacentProduct.flip は三つの非定数面の代表での充填を移す部品。原文の m_i を全ての類の上で同定する宣言がない。 候補：隣接位置の特別な充填と高次群の可換性を確認。任意の i の m_i を m_(i−1) の引数交換と同定する命題は未確認。 |
| 3.2.4.1 | partial → none |  | B6：IsContractibleKan は全境界充填で、原文は終射のホモトピー逆の存在。保存/反映の定理だけではこの定義の一致は直接得ない。 候補：IsContractibleKan はすべての境界の充填を要求する。Kan 複体間のホモトピー同値でこの性質を移せるが、原文の任意の単体集合で終射がホモトピー同値という定義には及ばない。 |
| 3.2.4.3 | partial → none |  | B6：型の IsContractibleKan は境界充填の定義で、原文(1)の終射のホモトピー同値への比較がない。π による定理も独自商を用い、原文の三条件への同定が必要。 候補：非空で全基点・全次数のホモトピー類が一元なら終射は自明 Kan fibration、境界充填との同値もある。原文の三条件のうち、任意の正次数の π の消滅を返す向きと終射のホモトピー同値による表記を一緒に確認できていない。 |
| 3.2.4.5 | partial → partial | special | B6：exists_nullHomotopy_of_isFilteredInfinity は有限な始域 K と filtered 準圏 C の任意の p を定値写像に結ぶ一段のホモトピーを直接与える。この範囲で原文の nullhomotopic が成立する。一般の判定述語は含まない。 |
| 3.2.4.11 | partial → partial | special | B6：LastHornContraction.homotopy を任意の σ₀ で後合成すると σ₀ から定値写像へのホモトピーになる。最後のホーン i=n>0 に限った原文の同じ主張。他の番号は含まない。 |
| 3.2.4.12 | partial → partial | stronger-hyp | B6：exists_filler_of_homotopy の g と s を定値写像に取れば、原文の nullhomotopic⇒延長の向きを直接得る。有限鎖だけでなく一段のホモトピーを与えた場合。延長⇒nullhomotopic は含まない。 |
| 3.2.4.13 | partial → partial | stronger-hyp | B6：exists_boundary_filler_of_homotopySubsingleton は指定 n の境界写像の延長を直接返す。頂点 x₀ と全基点・全次数の消滅を仮定するので、一つの π_(n−1) の消滅だけの原文より強い。逆向きは含まない。 |
| 3.2.4.14 | partial → none |  | B6：全次数の消滅と指定頂点からの充填は、n=0/1にそれぞれ一つの π₀ 条件だけを使う iff の結論ではない。 候補：AcyclicKanLifting は指定頂点を零次の充填に使い、零次のホモトピー類の一元性を高次の充填の仮定に含める。n=0 の非空性と n=1 の連結性の個別の同値は未確認。 |
| 3.2.4.15 | none → none |  | B6：現本体・固定Mathlibを再検索。点ごとの弱同値を保つ filtered colimit 定理はある。各段の transition だけが零ホモトピックな列の余極限が可縮という宣言は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.2.5.1 | partial → none |  | B6：BoundaryLift は最後の面の incidence。原文の第0面と逆順にする比較がなく、別の面を指定した型を partial としない。 候補：境界定値の底の単体を、最後の面以外が基点に定値となるよう持ち上げる型。Kerodon は最初の面以外を固定し、第0面を指定する incidence を定める。面の反転を含む比較は未確認。 |
| 3.2.5.2 | partial → none |  | B6：connecting は最後の面の持ち上げで定める。原文の第0面の incidence iff との比較と一意性がなく、違う連結写像の構成だけでは不足。 候補：選んだ最後の面の持ち上げから連結写像を定め、選択に依存しない。本文の第0面を指定した incidence との双方向および写像の一意性は未確認。 |
| 3.2.5.5 | partial → none |  | B6：componentConnecting も最後の面の連結写像で、全成分上の原文の作用と同一視されていない。作用の単位則・合成則を型に持たない。 候補：任意の指定ファイバー頂点から出発する π₁(B) → π₀(fiber) の連結写像はある。π₀(fiber) 全体で代表に依らない作用と単位・合成則は未確認。 |
| 3.2.6.3 | partial → partial | special | B6：componentFiber_exact は s=p(e) とファイバーの頂点 e を指定した場合の、π₀(E) の底での像が [s] iff ファイバーの像に属する、という同じ結論。任意の s と空ファイバーの場合には及ばない。 |
| 3.2.6.5 | partial → none |  | B6：componentConnecting_exact は原文の作用・軌道の同定の部品。最後の面で作る connecting を第0面の作用と比較する宣言が必要。 候補：componentConnecting_exact は、指定頂点の成分と同じ全空間の成分に写るファイバー成分を、π₁(B) からの連結写像の像として特徴づける。π₁ の全成分上の作用・軌道集合との比較は未確認。 |
| 3.2.6.7 | partial → none |  | B6：componentConnecting_kernel は最後の面の connecting の核であり、原文の第0面による作用の安定化群との比較が必要。 候補：componentConnecting_kernel は、指定ファイバー成分に戻る底のループ類と全空間の基本群の像を同定する。π₁ の全成分上の作用としての安定化群は未確認。 |
| 3.2.6.8 | partial → partial | stronger-hyp | B6：fiberHomotopySubsingleton は同じ指定ファイバーの π_n の消滅を直接返す。二つの隣接次数だけの単射/全射でなく全基点・全次数の π 同型を仮定。消滅からの逆方向は含まない。 |
| 3.2.6.9 | none → none |  | B6：現本体・固定Mathlibを再検索。連結写像の基点の逆像と、ファイバーから全空間への成分写像の像は計算する。指定底成分の逆像の一意性と π₁ の全射性によるファイバー連結性の同値は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.2.7.2 | partial → partial | stronger-hyp | B6：fibration_rlp_of_piIsomorphism は条件(3)の全 π 同型と全空間の頂点 e₀ を仮定して、条件(1)の全単射 RLP を直接与える。e₀ は原文より強い。四条件全体の iff は含まない。 |
| 3.2.7.4 | partial → none |  | B6：単体加群の核型正規化の QuasiIso と弱同値の iff で、原文の指定 K(C) と整数次数の C への比較はない。 候補：単体加群写像を正規化した擬同型と、忘却した単体写像の弱ホモトピー同値の同値。原文の任意の整数次数の鎖写像に K を施し、非負次数ホモロジーと比較する形は未確認。 |
| 3.2.8.1 | partial → none |  | B6：fiberMap_piIsomorphism は独自の π の全単射であって原文のホモトピー同値への比較が要る。切断空間の宣言は原文とは別の射。 候補：全空間と底の π 同型からファイバーの π 同型を得る方向がある。ファイバー同値からの逆方向として引用されていた宣言は切断空間の比較で、全空間の同値を直接返さない。 |
| 3.2.8.4 | partial → partial | special | B6：finiteSubsetColimit_isWeaklyContractible は任意の型 Q の有限部分集合の圏を添字にした filtered colimit に対し、原文と同じ弱可縮性の結論を直接返す。任意の filtered 小圏は含まない。 |
| 3.2.8.5 | partial → none |  | B6：filtered 準圏の定理には普通の線形順序の nerve の filtered 性の適用が必要。contractionSpan も任意の線形順序に対する T と自然変換を型で与えず材料。 候補：filtered 準圏の弱可縮性と、縮約の span が指定される普通圏の nerve の弱可縮性を確認。非空線形順序からの適用を一つにまとめた宣言は未確認。 |
| 3.3.0.1 | partial → partial | component | B6：exInfinity の自然な単位・Kan 性・anodyne 性・Kan fibration 保存で、同じ置換正方形の (a),(b),(c) を直接与える。任意の指定ファイバーの比較がホモトピー同値という (d) は含まない。 |
| 3.3.1.1 | partial → partial | stronger-hyp | B6：nonDegenerate_δ は Nonsingular X の非退化単体の各面も非退化と直接述べるので、原文の braced 条件を返す。単体の写像自体が Mono という強い仮定に限る。 |
| 3.3.1.4 | partial → partial | component | B6：nonDegenerate は任意 X の原文の次数別部分集合を直接与える。nonDegenerate_δ は Nonsingular の追加仮定で面閉性を返す。braced 一般の半単体集合の束ねた構造は含まない。 |
| 3.3.1.5 | partial → none |  | B6：非退化面の余極限表示は半単体写像からの延長全単射と同じ宣言ではなく、原文との比較が要る。 候補：Nonsingular の X は非退化単体の順序圏の標準単体の余極限。braced 一般の半単体写像がただ一つの単体写像へ延長する形は確認できない。 |
| 3.3.1.6 | partial → none |  | B6：既存単体集合の fat realization の定義で、原文の半単体集合の全射/単射分解による作用との同定は引用の型にない。 候補：freeDegeneracies は単体集合の次数データを離散行から fat realization する。任意の半単体集合 S を直接受け取る自由退化関手は未確認。 |
| 3.3.1.7 | partial → none |  | B6：freeDegeneracies と augmentation だけは、原文の η の単射性・braced 性・非退化像のいずれも結論しない。 候補：freeDegeneracies とその augmentation は既存の単体集合を受け取る。任意の半単体集合 S からの次数ごとの包含とその単射性、非退化像の主張は未確認。 |
| 3.3.1.8 | none → none |  | B6：現本体・固定Mathlibを再検索。SemiSimplexCategory は単射な単体圏の射を扱う添字圏。braced な単体集合と半単体集合の二つの圏の同値は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.3.1.9 | none → none |  | B6：現本体・固定Mathlibを再検索。freeDegeneraciesAugmentation は既存の単体集合を終域に取る。半単体集合 S からの任意の半単体写像を自由退化 S⁺ へ一意に延長する型は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.3.1.10 | none → none |  | B6：現本体・固定Mathlibを再検索。SemiSimplexCategory の単体圏への包含と、単体集合の freeDegeneracies は別々にある。半単体集合への忘却の左随伴を与える宣言は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.3.1.11 | none → none |  | B6：現本体・固定Mathlibを再検索。Nonsingular の非退化単体での余極限表示はある。braced な X で非退化半単体集合への自由退化を施したものが X に同型という型は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.3.2.3 | none → none |  | B6：現本体・固定Mathlibを再検索。標準単体の細分を鎖の nerve として作る宣言はある。重心に各頂点を送り各小単体でアフィンとなる幾何学的実現の同相は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.3.2.10 | none → none |  | B6：現本体・固定Mathlibを再検索。SSet.ex は Δᵒᵖ 全体の単体集合の関手。半単体集合への適用として Ex の次数と面の構成を与える宣言は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.3.3.1 | partial → none |  | B6：sdExAdjunction は選ばれた unit の普遍性で、任意の u を判定する原文の述語との比較を欠く。 候補：sd ⊣ ex が表現対象と普遍写像を与える。原文の任意の u : X→Ex(Y) がこの普遍性を満たすという条件を独立の述語にはしていない。 |
| 3.3.3.7 | none → none |  | B6：現本体・固定Mathlibを再検索。標準単体やホーンの組合せ的な細分の比較はある。braced X について実現した 幾何学的実現 Sd X と X の標準同相は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.3.3.10 | none → none |  | B6：現本体・固定Mathlibを再検索。Subdivision の標準単体同型と、順序集合・ホーンでの比較はある。任意 X の単体の圏 Δ_X の nerve から Sd X への比較写像 ψ_X は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.3.3.12 | partial → none |  | B6：N は部分単体関係の順序集合で、原文の非退化単体の充満部分圏の全ての単体圏の射を保たない。 候補：X.N は非退化単体を部分単体関係で順序づける。原文の Δ_X の充満部分圏であり得る複数の異なる単体圏の射まで保持しない。 |
| 3.3.3.17 | partial → none |  | B6：HornFacePoset との比較は原文の非退化単体の充満部分圏を使う特定 ψ_X と比較されていない。 候補：ホーンの細分から非退化面の順序集合の nerve への比較は同型。任意の braced X での原文の ψ_X の同型性は確認できない。 |
| 3.3.3.19 | none → none |  | B6：現本体・固定Mathlibを再検索。Nonsingular の非退化面の表示はある。原文の半単体集合を対象とする関手についての充満忠実性の主張は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.3.3.20 | none → none |  | B6：現本体・固定Mathlibを再検索。非退化単体の順序型と面写像の計算はある。半単体集合全体を対象とした変形版の関手と射の同定は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.3.4.8 | none → none |  | B6：現本体・固定Mathlibを再検索。subdivisionLastVertexMap は λ_X を定めるが、弱同値の定理 exUnitAt_anodyne は随伴先の ρ_X の性質。元の λ_X の弱ホモトピー同値性を結論する宣言は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.3.5.2 | partial → none |  | B6：Ex∞ についての iff は一段の Ex と異なる関手。exUnitAt_anodyne は自然性による弱同値判定のための材料。 候補：Ex∞ 版の anodyne 局所化同型の同値と、単一の Ex の単位の anodyne 性を確認。単一の Ex による弱ホモトピー同値の両方向を述べる宣言は未確認。 |
| 3.3.5.5 | partial → none |  | B6：ex_map_rlp は Ex.map p の J.rlp を返す。Ex の終対象保存との比較を使って終射に移す議論が必要で、KanComplex(Ex X) 自体は引用の型にない。 候補：ex_map_rlp は射の全ホーン RLP を保存する。終射に適用できるが、引用は Ex X の KanComplex インスタンスまたはその終射についての型を直接返さない。 |
| 3.3.5.6 | none → none |  | B6：現本体・固定Mathlibを再検索。subdivisionHomEquiv_app_down は随伴の各単体の像を計算する。Kan 標的への二写像がホモトピックであることをこの転置が保存・反映する宣言は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.3.5.7 | partial → none |  | B6：kanHomotopyEquivOfLocalizedIso の結論は π の台の同値で、名から想像されるホモトピー逆ではない。ρ_Y の anodyne 性だけは原文のホモトピー同値性の部品。 候補：ρ_Y の anodyne 性と、両端が Kan のときの局所化同型のホモトピー逆がある。ρ_Y に対する一体の命題と Ex Y の Kan 性は引用にない。 |
| 3.3.5.8 | none → none |  | B6：現本体・固定Mathlibを再検索。exUnitAt_naturality は射に関する自然性。ρ_(Ex X) と Ex(ρ_X) の間の円柱ホモトピーの存在は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.3.5.9 | none → none |  | B6：現本体・固定Mathlibを再検索。orderSubtypeNerve_anodyne は部分順序の指定点を通る上向きの変形を要求する。上面一枚を欠く立方体の補題もあるが、最大頂点だけを除いた部分順序集合の nerve の指定包含とは異なる。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.3.6.2 | partial → partial | component | B6：exInfinityUnit_anodyne と anodyne_mono から同じ ρ_X^∞ の Mono を直接得る。零単体での全射性は含まない。 |
| 3.3.6.4 | partial → partial | component | B6：exInfinity_preservesFiniteLimits は原文の二つの保存性のうち有限極限保存を直接述べる。入力の filtered colimit 保存を、有限始域からの段階因子化と取り違えない。 |
| 3.3.6.5 | partial → none |  | B6：有限極限保存の一般instanceだけで、原文の指定した頂点を通じる比較写像の同型性は述べていない。Ex∞(1)と1を同定し自然な単位との整合を確かめる比較が必要。 候補：Ex∞ の有限極限保存はファイバーの引き戻しに適用できる。原文の Ex∞(X_s)→Ex∞(X)_s を同型とし、頂点と終対象の同定を明示する専用の型は未確認。 |
| 3.3.7.1 | partial → none |  | B6：left fibration と準圏同値の判定は一般の Kan fibration の弱同値判定と異なる。引き戻し局所化同型は特定の正方形だけの性質。 候補：left fibration のファイバー比較は準圏の底を要求し、底の弱同値を伴う一般の Kan fibration の正方形の同値条件ではない。基底変換の引き戻しが弱同値になる場合は確認。 |
| 3.3.7.5 | partial → partial | stronger-hyp | B6：leftFibration_isQCatEquivalence_iff_fibers は同じ三角形とファイバー射の iff。E,F,B を Kan 複体に強めると Kan fibration は left fibration で、引用の isWeakHomotopyEquivalence_iff_isQCatEquivalence と isSimplicialHomotopyEquivalence への比較をそのまま適用できる。任意の底 S については含まない。 |
| 3.3.7.6 | partial → partial | direction | B6：rightFibration_trivialKanFibration_of_contractible_fibers は Kan fibration（特に right fibration）に全ファイバーの可縮性を仮定し、同じ f の自明 Kan 性を返す。(4)⇒(1)の向き。一般の弱同値からの逆方向は含まない。 |
| 3.3.7.7 | partial → partial | component | B6：anodyne_mono は条件(1)から条件(2)の単射性成分を直接返す。一般 ModelCategory SSet を要求する別宣言は根拠にせず、モデル圏のinstanceなしで逆向きや仮定なしの一致を主張しない。 |
| 3.3.8.1 | partial → partial | stronger-hyp | B6：trivialFibrationExtension は同じ q を p に沿う引き戻しで延長し、延長先にも全単射 RLP を返す。原文の Kan fibration を自明 Kan fibration に強める場合。p は任意の単射なので anodyne も含む。 |
| 3.3.8.4 | none → none |  | B6：現本体・固定Mathlibを再検索。自明 Kan fibration の延長や相対持ち上げの宣言はある。指定の二部分集合とファイバー同値を仮定し、制限が X を通る単体だけを残した Y'→T の Kan fibration 性は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.4.0.3 | partial → none |  | B6：anodyne–Kan 置換による pullback と equivalencePathReplacement は、原文の全区間写像を使う特定の二重 pullback との比較がない別模型。 候補：homotopyPullbackObject は右脚を anodyne–Kan 分解してから引き戻す。equivalencePathReplacement は可逆 path を使う別模型。Kerodon の全区間写像 X^Δ¹ に沿う両端の具体的な引き戻しとの同定は引用にない。 |
| 3.4.0.7 | partial → none |  | B6：原文の指定の通常pullback→全区間模型の射との比較がない。 候補：一脚が Kan fibration のとき通常の引き戻しがホモトピー引き戻しになる。原文の Kan 底の全区間写像を使う模型への指定の包含との同定は未確認。 |
| 3.4.0.9 | partial → none |  | B6：右脚を置換する模型の比較射であり、原文の区間模型の比較射との自然な同定がない。 候補：三頂点の局所化同型から選んだ右脚の Kan 置換を使う引き戻しの比較が局所化同型。原文の区間写像模型での比較との自然な同定は未確認。 |
| 3.4.1.5 | partial → none |  | B6：IsHomotopyPullback の定義と右固有性は原文の任意の正方形の iff を直接述べず、区間模型との比較が必要。 候補：一般の引き戻しの比較の型と、Kan fibration に沿う弱同値の引き戻しはある。右脚が弱同値の正方形で左脚の弱同値性とホモトピー引き戻し性を直接同値にする宣言は未確認。 |
| 3.4.1.6 | partial → none |  | B6：原文の指定 θ と置換模型の比較射を同一視する宣言が必要。 候補：一脚が Kan fibration のとき、厳密な引き戻しへの射の局所化同型性で判定できる。本文の Kan 底における区間模型への合成 θ に対する判定は未確認。 |
| 3.4.1.13 | partial → none |  | B6：四頂点とも弱同値の場合の保存/反映はあるが、原文のホモトピー引き戻しの区間模型との同定がなく、同じ正方形の結論とは未確認。 候補：四頂点の比較射が局所化同型ならホモトピー引き戻し性を保存・反映する。三頂点のみを仮定して残る頂点の弱同値を導く三条件のうち二つから三つ目、という形は未確認。 |
| 3.4.1.16 | none → none |  | B6：現本体・固定Mathlibを再検索。simplicialSumReindex_homotopyPullback_of_fibrations は各成分のホモトピー引き戻しを余積にまとめる。原文の一つの正方形から指定した直和因子を取り出す方向は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.4.2.1 | partial → none |  | B6：Bousfield–Kan cone の比較射の同値は、原文の区間模型で定義した任意の正方形の homotopy pullback 性との比較を欠く。 候補：任意の Kan 標的への内部 Hom の cospan の比較を、元の span が Kan 値かつ単射の脚を持つ場合に計算する。任意の正方形で全 Kan 標的へのホモトピー引き戻し性を要求する述語は未確認。 |
| 3.4.2.2 | partial → partial | component | B6：doubleMappingCylinder は区間の両端と二脚を貼る原文のホモトピー押し出しを直接構成し、collapse もその区間を潰す比較を与える。比較の Epi 性までは引用型にない。 |
| 3.4.2.5 | none → none |  | B6：現本体・固定Mathlibを再検索。二重写像円筒とその collapse、片脚が単射の collapse の弱同値性はある。任意の正方形を指定の二重写像円筒からの比較で判定する iff は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.4.2.6 | none → none |  | B6：現本体・固定Mathlibを再検索。単体集合の op で弱可縮性を保つ補題はある。正方形全体に op を適用したときのホモトピー押し出し性の両方向は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.4.2.7 | none → none |  | B6：現本体・固定Mathlibを再検索。ホモトピー引き戻し性の flip 同値と通常の押し出しの対称性はある。任意の単体集合のホモトピー押し出し性の flip 同値は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.4.2.8 | none → none |  | B6：現本体・固定Mathlibを再検索。通常の押し出しの貼り合わせとホモトピー引き戻しの貼り合わせはある。左のホモトピー押し出しから右と外周の同値を述べる双対の宣言は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.4.2.9 | partial → none |  | B6：二重写像円筒の比較の弱同値だけでは、原文の任意の終端頂点を含む三条件のいずれの含意も直接述べない。 候補：点ごとの弱同値から二重写像円筒間の弱同値を得る。任意の終端頂点を含む二つの正方形で、押し出し性と終端頂点の弱同値性を組み合わせた三条件は未確認。 |
| 3.4.2.10 | partial → none |  | B6：通常の押し出しの弱同値保存は原文の任意の正方形のホモトピー押し出し性との iff とは異なる。 候補：左固有性に当たる引用は通常の押し出しで一脚が単射などの条件下で局所化同型を保つ。任意の可換正方形について本文の iff を与えない。 |
| 3.4.2.11 | partial → none |  | B6：一般モデル圏の追加仮定を SSet で解消できず、通常pushoutを内部Homでpullbackに送る命題も原文のホモトピーpullbackとの比較が必要。 候補：仮定：Kerodon は単体集合の可換正方形で左上の脚が単射。候補の一般定理は [ModelCategory C]、局所可呈示性、cofibrantly generated と弱同値の cofibration に沿う押し出し安定性を要求する。具体的な C = SSet では ModelCategory の instance なし。結論：単体集合については Kan 複体の span の通常の押し出しの場合と、内部 Hom が押し出しを引き戻しに送ることを確認。任意の比較先に対する同値条件までは確認できない。 |
| 3.4.2.13 | partial → partial | direction | B6：doubleMappingCylinderCollapse_localized_isIso は原文の指定の collapse が右脚 Mono のとき弱同値になる向きを直接与える。左脚だけ Mono の側は含まない。 |
| 3.4.2.16 | partial → none |  | B6：単体の解消のaugmentation と積への Quillen A は任意の二対象の引き戻し比較という同じ射を直接扱わない。 候補：各単体上での左ファイバーから固定した単体集合への比較と、単体ファイバーの図式の増大による解消はある。共通底への任意の二対象を、単体への引き戻し全体の比較で判定する型は未確認。 |
| 3.4.2.17 | partial → partial | special | B6：simplicialProductQuillenA で Z を終対象、g を終射に取ると仮定は各単体ファイバーの弱可縮性となり、結論は f の弱同値性（X→Y×1 を標準同型で同定）になる。同じ射への明示的な特殊化。 |
| 3.4.3.2 | partial → none |  | B6：通常の IsPushout の保存はホモトピー押し出し性の保存の証明部品で、同じ結論ではない。 候補：sliceFiberFunctor は厳密な押し出しを保存する。ホモトピー押し出し正方形を Kan fibration で基底変換する一般の型は未確認。 |
| 3.4.3.3 | none → none |  | B6：現本体・固定Mathlibを再検索。単射に沿う厳密な押し出しの van Kampen 性と、slice の引き戻しによる厳密押し出し保存はある。四面がホモトピー引き戻しという仮定で上面のホモトピー押し出しを得る第二立方体定理は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.4.4.4 | partial → none |  | B6：厳密pushoutへの特殊化の候補はあるが、原文の区間模型のhomotopy pullbackとの比較を欠く。 候補：二重写像円筒での結果と、通常の押し出しで単射の脚がある場合は確認。任意のホモトピー押し出しを上下に指定した立方体で二面を回収する一般の型は未確認。 |
| 3.4.5.1 | none → none |  | B6：現本体・固定Mathlibを再検索。freeDegeneracies は既存の単体集合の次数を使う。任意の半単体集合の写像の弱同値を自由退化により定義する述語は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.4.5.5 | partial → none |  | B6：augmentation の弱同値性は写像 f での半単体弱同値との iff ではなく、その比較の部品。 候補：元の単体集合について自由退化の augmentation が弱同値であることを確認。忘却した半単体集合の弱同値述語との iff は未確認。 |
| 3.4.5.6 | none → none |  | B6：現本体・固定Mathlibを再検索。自由退化の既存の比較は X⁺→X。半単体集合 X から X⁺ への包含が半単体集合の弱同値になる宣言は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.4.5.7 | none → none |  | B6：現本体・固定Mathlibを再検索。単体集合での freeDegeneracies と Ex の別々の構成はある。半単体の包含に Ex をかけた指定射の弱同値性は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.4.5.8 | none → none |  | B6：現本体・固定Mathlibを再検索。Ex∞ の単体集合の弱同値保存・反映はある。半単体写像と一段の Ex の間の弱同値の同値は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.4.5.9 | partial → none |  | B6：弱同値という候補の結論から、Kan と限らない nerve のホモトピー逆は得ない。 候補：任意の単体集合の freeDegeneraciesAugmentation の弱ホモトピー同値性は確認。非恒等射の合成条件を持つ普通圏の nerve で、実ホモトピー逆まで得る強化は未確認。 |
| 3.4.6.1 | none → none |  | B6：現本体・固定Mathlibを再検索。単体集合の相対整数ホモロジーと単射に沿う押し出しはある。位相空間の内部被覆を入力して特異単体集合のホモトピー押し出しを得る宣言は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.4.6.4 | none → none |  | B6：現本体・固定Mathlibを再検索。特異単体集合の関手はある。各単体が被覆族の一つの部分空間に入るという条件で定める部分複体は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.4.6.6 | none → none |  | B6：現本体・固定Mathlibを再検索。標準単体の細分と一般の弱同値の比較はある。被覆に従属する特異小単体の部分複体の包含が弱同値という宣言は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.4.6.7 | none → none |  | B6：現本体・固定Mathlibを再検索。凸包と直径の一般 API はある。重心細分の一単体の像について n/(n+1) の係数で直径を抑える型は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.4.7.1 | none → none |  | B6：現本体・固定Mathlibを再検索。Mathlib の基本群と普通の群の押し出しの API はある。交わり・両側・全体の基本群の指定正方形を押し出しとする位相的 van Kampen 定理は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.4.7.2 | none → none |  | B6：現本体・固定Mathlibを再検索。基本亜群と圏の押し出しの API はある。位相空間の被覆に対して基本亜群の指定の押し出しを与える宣言は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.4.7.3 | partial → none |  | B6：単体集合のpushoutでの結果は位相的被覆の特異鎖へのexcisionの結論ではない。 候補：単体集合の厳密な押し出しから整数ホモロジー同型を得る補題はある。位相的被覆の特異鎖を入力して相対ホモロジー同型を結論する excision は未確認。 |
| 3.5.0.1 | none → none |  | B6：現本体・固定Mathlibを再検索。Kan の Whitehead 判定は既にある比較写像の同値を判定する。ホモトピー群が一つの次数に集中する X から比較先 K(G,n) と同値を作る分類は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.5.1.1 | partial → partial | special | B6：IsConnected は π₀ が一元かつ頂点が存在する条件を直接表し、原文の n=1 の連結性を与える。任意 n の高次群消滅を含む述語は与えない。 |
| 3.5.1.6 | partial → none |  | B6：anodyne Kan 置換の存在は証明部品。n-connective の定義や置換からの独立性を述べない。 候補：連続 Kan 置換と Ex∞ の単位が弱同値であることは確認。置換を通じた任意 n の連結性を定義し、置換からの独立性を示す型は未確認。 |
| 3.5.1.12 | none → none |  | B6：現本体・固定Mathlibを再検索。SkeletalSphericalRealization は球面的 cochain の指定条件での実現。低次元の任意の A から n-connective Kan 複体への全写像を零ホモトピックとする宣言は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.5.1.13 | partial → none |  | B6：KanPiIsomorphism は各頂点における全単射で、空の始域では π₀ の全射性も返さず、有限範囲の n-connective の定義とは異なる。 候補：KanPiIsomorphism はすべての基点・次数で同型を要求。低次数で同型、境界次数で全射という有限段の条件は型にない。 |
| 3.5.1.15 | none → none |  | B6：現本体・固定Mathlibを再検索。Ex∞ と弱同値の保存・反映はある。任意の射を Kan 置換の正方形で n-connective と判定する述語と選択独立性は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.5.1.22 | none → none |  | B6：現本体・固定Mathlibを再検索。全次数の π 同型でファイバーが acyclic となる方向はある。有限次数の n-connective と各頂点ファイバーの連結性との同値は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.5.1.24 | none → none |  | B6：現本体・固定Mathlibを再検索。任意の底で Kan fibration に沿う引き戻しの弱同値性はある。n-connectivity の基底変換での保存と、底の π₀ 全射性による反映は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.5.1.25 | none → none |  | B6：現本体・固定Mathlibを再検索。Kan fibration の通常ファイバーとホモトピー引き戻しの比較はある。任意の射の n-connectivity をホモトピーファイバーごとに特徴づける型は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.5.1.26 | none → none |  | B6：現本体・固定Mathlibを再検索。弱同値での可縮性移送や K 理論のファイバーの負次数消滅はある。n-connective な射の両端の連結度を比較する三条件は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.5.1.27 | none → none |  | B6：現本体・固定Mathlibを再検索。π₀ の連結性と頂点は扱える。非空 Kan 複体の連結度を基点包含の (n−1)-connectivity と比較する型は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.5.1.28 | none → none |  | B6：現本体・固定Mathlibを再検索。弱ホモトピー同値の合成・消去は全次数の同値の結果。n と n+1 の連結度を混ぜて合成を判定する三条件は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.5.1.29 | none → none |  | B6：現本体・固定Mathlibを再検索。Kan ファイバーと対角の pullback の比較はある。相対対角でちょうど一つ下がる連結度の iff は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.5.1.30 | none → none |  | B6：現本体・固定Mathlibを再検索。pinchedHom や端点を固定した path 空間の構成はある。各頂点対の path 空間の連結度から射の n-connectivity を判定する型は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.5.1.31 | none → none |  | B6：現本体・固定Mathlibを再検索。mono・左 fibration のファイバー判定は別条件。π₀ 全射を仮定した相対対角の弱同値性による一般の弱同値判定は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.5.1.32 | none → none |  | B6：現本体・固定Mathlibを再検索。π₀ による連結性と対角の pullback の API はある。非空性と絶対対角の (n−1)-connectivity で X の連結度を特徴づける型は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.5.1.33 | none → none |  | B6：現本体・固定Mathlibを再検索。終射による弱可縮性と弱同値での移送はある。非空性と絶対対角の弱ホモトピー同値性による判定は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.5.2.1 | partial → partial | stronger-hyp | B6：fibration_rlp_of_piIsomorphism は全基点・全次数の π 同型と頂点 e₀ を加えた場合、原文(3),(4)の持ち上げを全ての単射に対して直接与える。指定次数以下の連結度だけからの一般の iff は含まない。 |
| 3.5.2.2 | none → none |  | B6：現本体・固定Mathlibを再検索。全境界に対する持ち上げ性による自明 Kan fibration はある。次数を上から制限した境界だけで一般の射の n-connectivity を結論する宣言は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.5.2.4 | none → none |  | B6：現本体・固定Mathlibを再検索。ホーンの小対象論法による分解は全次元を使う。低次単体の全単射を保ちながら指定の連結度を得る分解条件は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.5.2.5 | none → none |  | B6：現本体・固定Mathlibを再検索。単体集合を Kan 置換する自然射はある。次数の閾値まで全単射で、行き先を n-connective にする置換は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.5.2.6 | none → none |  | B6：現本体・固定Mathlibを再検索。標準単体の境界と次元上限は定義される。境界が (n−1)-connective であることをホモトピー群で保証する宣言は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.5.2.7 | none → none |  | B6：現本体・固定Mathlibを再検索。anodyne の押し出し閉性は全ホーンの弱飽和の結果。任意の n-connective 射の指定押し出しで連結度を保つ型は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.5.2.8 | none → none |  | B6：現本体・固定Mathlibを再検索。SSet.sk は骨格関手を与える。sk_n X が Δ⁰ と同型である n-reduced の述語と API は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.5.2.9 | none → none |  | B6：現本体・固定Mathlibを再検索。Kan 置換と骨格の関手は独立にある。所定の連結度と n-reduced な弱同値模型の存在を同値にする宣言は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.5.2.11 | partial → none |  | B6：相対内部Homのfibration性は n-connective 性という結論の成分ではない。 候補：相対内部 Hom の比較射が Kan fibration になる定理はある。骨格を含む条件や n-connectivity の下限を比較射に移す結論は含まれない。 |
| 3.5.2.12 | partial → none |  | B6：制限射のfibration性は有限次数の連結度の結論を含まない。 候補：Kan 標的への単射沿いの前合成は fibration。原文で要求する制限写像の有限次数の連結度は未確認。 |
| 3.5.2.13 | partial → none |  | B6：内部Homのfibration保存は n-connective 性の保存を結論しない。 候補：Kan fibration による内部 Hom の後合成が fibration になる。f の有限次数の連結度がそのまま保たれる結論は未確認。 |
| 3.5.2.14 | partial → none |  | B6：写像空間のKan性だけは n-connective 性という主結論を含まない。 候補：任意の B への写像空間は標的が Kan なら Kan。標的の連結度と B の次元を用いた写像空間の連結度の主張は確認できない。 |
| 3.5.3.1 | partial → none |  | B6：右Kan拡張によるIsCoskeletalと原文の全高次境界の一意充填との比較がない。 候補：Mathlib の IsCoskeletal は自然数 n に対する切断からの右 Kan 拡張。Kerodon の整数 n で、m>n の全境界の一意な延長という定義との比較は未確認。 |
| 3.5.3.9 | none → none |  | B6：現本体・固定Mathlibを再検索。Dold–Kan の正規化と coskeleton の構成はある。単体アーベル群の coskeletal 性を正規化鎖群の消滅と n-サイクルへの境界射の像で判定する型は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.5.3.10 | partial → none |  | B6：次数切断からの右Kan拡張の普遍性は原文の sk_n(S) からの制限との iff の直接の型ではない。 候補：IsCoskeletal.isUniversalOfIsRightKanExtension は次数切断への右 Kan 拡張の普遍性を与える。任意の S と sk_n S の間の制限の全単射を用いた原文の iff は未確認。元の 2-coskeletal な nerve の引用は対象が違う。 |
| 3.5.3.12 | none → none |  | B6：現本体・固定Mathlibを再検索。内部 Hom と右 Kan 拡張の coskeleton は定義される。任意 K について X の coskeletal 性を Fun(K,X) に移す宣言は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.5.3.13 | partial → none |  | B6：cosk単位の同型性のiffは原文の単体圏の極限の特定 θ_m と比較されていない。 候補：自然数 n での右 Kan 拡張とその単位の同型性を確認。原文の各 m での単体の圏による極限と、境界一意充填による定義からの iff は引用で確認できない。 |
| 3.5.3.15 | partial → none |  | B6：選んだcoskAdjのunitだけでは原文の任意の f の二条件を述べる型は得られない。 候補：自然数 n の cosk への選択済み単位はある。任意の f が低次全単射で n-coskeleton を与えるという条件の型は未確認。 |
| 3.5.3.16 | partial → none |  | B6：自然数次数の右Kan拡張coskはあるが、原文の境界充填と低次全単射という定義との比較がない。 候補：自然数 n では cosk_n X と随伴の単位が存在する。整数 n を許す本文に対し負次数の coskeleton と境界による性質は引用にない。 |
| 3.5.3.17 | partial → none |  | B6：coskeletalな対象のunitの同型は、原文の任意 f についての三条件のどの含意でもない。 候補：coskeletal なら標準の cosk への単位が同型。任意の f と coskeletal な標的について、低次全単射・内部 Hom の同型・Hom の全単射の三条件は未確認。 |
| 3.5.3.18 | partial → none |  | B6：右Kan拡張のcoskという模型と、原文のHom(sk_nΔ[m],X)の式との比較を直接述べる型がない。 候補：SSet.cosk は自然数 n の選択済み coskeleton を与える。本文の任意の整数 n のうち負次数はこの型に含まれない。 |
| 3.5.3.19 | partial → none |  | B6：Truncated.coskの本質像を原文の境界一意充填の充満部分圏と同定する宣言が必要。 候補：Truncated.cosk n は自然数 n で充満忠実な右随伴として reflective。原文の整数 n と、境界一意充填で指定した充満部分圏への左随伴の形は未確認。 |
| 3.5.3.23 | none → none |  | B6：現本体・固定Mathlibを再検索。cosk₂Iso は普通圏の nerve の coskeleton 表示で、群oid の nerve には Kan の結果がある。任意 Kan 複体の任意 n の cosk の Kan 性は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.5.4.1 | none → none |  | B6：現本体・固定Mathlibを再検索。IsCoskeletal は切断からの右 Kan 拡張で、存在しない充填を許す「存在すれば一意」の weakly coskeletal とは異なる。該当述語は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.5.4.12 | none → none |  | B6：現本体・固定Mathlibを再検索。通常の coskeleton の普遍性ではすべての制限写像が延長する。弱い版で制限の像を延長可能な写像に絞る型は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.5.4.13 | none → none |  | B6：現本体・固定Mathlibを再検索。SSet の内部 Hom の Kan 性の保存はある。weakly coskeletal の制限写像の単射性を内部 Hom に移す宣言は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.5.4.14 | none → none |  | B6：現本体・固定Mathlibを再検索。通常の cosk の選択済みの単位と低次の切断はある。低次全単射に加え次の次数での全射を要求する弱 coskeleton の写像の型は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.5.4.17 | none → none |  | B6：現本体・固定Mathlibを再検索。通常の cosk_n への単位はある。cosk_(n+1) から像で定める弱 cosk_n への全射とその合成の性質は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.5.4.18 | none → none |  | B6：現本体・固定Mathlibを再検索。通常の右 Kan 拡張には Hom の普遍性がある。弱 coskeletal の標的に限定した三条件の同値は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.5.4.19 | none → none |  | B6：現本体・固定Mathlibを再検索。単体写像の像の部分複体はある。cosk_(n+1)→cosk_n の像により弱 coskeleton を定義する宣言は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.5.4.20 | none → none |  | B6：現本体・固定Mathlibを再検索。通常の Truncated.cosk の反射性はある。弱 coskeletal 単体集合の充満部分圏の包含の左随伴は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.5.4.22 | none → none |  | B6：現本体・固定Mathlibを再検索。cosk の間の切断と一般の Kan fibration は別々にある。通常の cosk_(n+1) から弱 cosk_n への比較の持ち上げ性は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.5.4.23 | none → none |  | B6：現本体・固定Mathlibを再検索。通常の cosk と Kan 置換はある。任意の Kan X の弱 cosk_n が Kan である宣言は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.5.4.24 | none → none |  | B6：現本体・固定Mathlibを再検索。IsCoskeletal の単位の同型性はある。弱 cosk と通常の cosk が一致する条件を比較する三条件は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.5.4.26 | none → none |  | B6：現本体・固定Mathlibを再検索。anodyne–Kan 分解はあるが、指定の X→弱 cosk_n X 自体が Kan fibration という宣言は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.5.5.1 | none → none |  | B6：現本体・固定Mathlibを再検索。KanComplex は全角の存在を要求する。次数 n を超える角の一意な充填も要求する n-groupoid の型は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.5.5.7 | none → none |  | B6：現本体・固定Mathlibを再検索。discrete と KanObject への包含はある。角の一意性で定義した 0-groupoid と定値単体集合との iff は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.5.5.8 | partial → none |  | B6：groupoidNerve_kanComplex は(1)を特定nerveに限ったときの(3)のKan性のみで、原文の1-groupoidや特定の基本亜群への射との同定がない。 候補：亜群の nerve が Kan であることを確認。高次角が一意である 1-groupoid の条件と、基本亜群の nerve への標準写像が同型という特徴づけは未確認。 |
| 3.5.5.9 | none → none |  | B6：現本体・固定Mathlibを再検索。正規化 Moore 複体は定義される。単体アーベル群の角の高次一意性と次数 m>n の鎖群の消滅を比較する型は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.5.5.10 | none → none |  | B6：現本体・固定Mathlibを再検索。普通圏の nerve について 2-coskeletal の結果がある。任意 n の n-groupoid から弱 n-coskeletal を導く宣言は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.5.5.11 | none → none |  | B6：現本体・固定Mathlibを再検索。通常の nerve には 2-coskeletal のインスタンスがある。n-groupoid の一般の (n+1)-coskeletal 性は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.5.5.12 | none → none |  | B6：現本体・固定Mathlibを再検索。StrictSegal の nerve での単体の外延性はある。一般の n-groupoid で指定の面の一致から二つの単体の等式を導く型は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.5.5.13 | partial → none |  | B6：Kan性の保存だけでは高次ホーン充填の一意性を結論しない。 候補：標的が Kan なら写像空間が Kan になる。高次の角充填の一意性を保つ n-groupoid の主張は未確認。 |
| 3.5.5.14 | none → none |  | B6：現本体・固定Mathlibを再検索。Whitehead 判定はすべての π 同型でホモトピー同値を得る。n-groupoid の間での低次数の条件による三条件の比較は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.5.5.16 | none → none |  | B6：現本体・固定Mathlibを再検索。単体写像の同型性は全次数の全単射で判定できる。n-groupoid の間で m<n に限った全単射から同型を導く型は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.5.5.17 | none → none |  | B6：現本体・固定Mathlibを再検索。Dold–Kan は非負次数の複体を単体アーベル群に戻す。一点の低次単体を持つ n-groupoid を K(G,n) と同定する型は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.5.6.1 | none → none |  | B6：現本体・固定Mathlibを再検索。KanHomotopy は固定境界の代表を割る。低次単体を保ち n 単体だけを相対ホモトピーで割る homotopy n-groupoid の写像の条件は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.5.6.5 | none → none |  | B6：現本体・固定Mathlibを再検索。基本圏と nerve の普通の Hom の転置がある。任意 n の n-groupoid 標的で Fun(Y,Z)→Fun(X,Z) の単体同型を与える型は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.5.6.6 | none → none |  | B6：現本体・固定Mathlibを再検索。SSet.truncation n は添字の切断であり、n 次元のホモトピー類で割る π_{≤n}(X) は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.5.6.10 | none → none |  | B6：現本体・固定Mathlibを再検索。cosk と部分複体の像の API はある。弱 cosk_n から π_{≤n} への相対ホモトピーによる商写像は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.5.6.12 | none → none |  | B6：現本体・固定Mathlibを再検索。相対ホモトピーの商は二写像の類を同定する。弱 cosk_n の写像の像が同じという条件との比較は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.5.6.14 | none → none |  | B6：現本体・固定Mathlibを再検索。普通の coskeleton と一般の自明 fibration はある。弱 cosk_n からホモトピー n-groupoid への q について本文の持ち上げ性は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.5.6.15 | none → none |  | B6：現本体・固定Mathlibを再検索。任意の単射への RLP で自明 Kan fibration を表す型はある。cosk_(n+1) の指定商がその RLP を持つ宣言は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.5.6.16 | none → none |  | B6：現本体・固定Mathlibを再検索。基本亜群の nerve は Kan。任意 n の π_{≤n}(X) の Kan 性と高次の角の一意性は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.5.6.17 | none → none |  | B6：現本体・固定Mathlibを再検索。Kan 置換の存在と、相対ホモトピーの商はある。指定の v が任意次数の homotopy n-groupoid を与える一般の定理は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.5.7.1 | partial → none |  | B6：Is0TruncatedSpace は離散対象への準圏同型で、原文の境界充填と同定されていない別の定義。 候補：Is0TruncatedSpace は空間の準圏の頂点が離散空間と同型である条件。全 m≥n+2 の境界を埋める任意 n の定義ではない。 |
| 3.5.7.7 | none → none |  | B6：現本体・固定Mathlibを再検索。ホモトピー retract での可縮性移送はある。n-truncated の境界条件を指定の写像と片側逆の条件で移す型は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.5.7.8 | none → none |  | B6：現本体・固定Mathlibを再検索。弱可縮性や π 同型のホモトピー不変性はある。任意 n の truncation の iff は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.5.7.9 | none → none |  | B6：現本体・固定Mathlibを再検索。AcyclicKanLifting は全基点・全次数の消滅から全境界を埋める。m>n の消滅だけで高次境界を判定する iff は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.5.7.14 | none → none |  | B6：現本体・固定Mathlibを再検索。Whitehead の全次数版はある。n-truncated の始域・終域で (n+1)-connectivity だけを用いる型は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.5.7.15 | none → none |  | B6：現本体・固定Mathlibを再検索。cosk は関手である。所定の連結度の射に cosk_n をかけると同値となるという宣言は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.5.7.16 | none → none |  | B6：現本体・固定Mathlibを再検索。coskeletal なら cosk への単位は同型。n-truncated、n-groupoid 模型、cosk_(n+1) へのホモトピー同値の四条件は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.5.7.17 | none → none |  | B6：現本体・固定Mathlibを再検索。切断関手と Whitehead 判定はある。π_{≤n}(X) への標準写像のホモトピー同値性による特徴づけは見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.5.7.19 | none → none |  | B6：現本体・固定Mathlibを再検索。単体アーベル群の Dold–Kan はある。n-connective かつ n-truncated な任意の Kan 複体を K(G,n) と特徴づける型は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.5.7.20 | none → none |  | B6：現本体・固定Mathlibを再検索。骨格と添字切断はある。n-truncated な標的への比較の存在により対象の n-truncation を定義する型は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.5.7.30 | none → none |  | B6：現本体・固定Mathlibを再検索。全 Kan 標的への写像空間で弱同値を判定する型はある。n-truncated 標的に限る Hom の全単射による n-truncation の普遍性は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.5.7.31 | none → none |  | B6：現本体・固定Mathlibを再検索。普通の cosk は reflective。n-truncated Kan 複体のホモトピー圏の包含への左随伴は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.5.8.1 | none → none |  | B6：現本体・固定Mathlibを再検索。Kan fibration の塔の極限と dg 代数の Postnikov はある。任意 Kan 複体の n-truncation を各段に指定する Postnikov tower の定義は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.5.8.7 | none → none |  | B6：現本体・固定Mathlibを再検索。Kan ファイバーの高次ホモトピーと dg Hom の Dold–Kan 模型はある。弱 cosk の特定のファイバーと Eilenberg–MacLane 空間の同型は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.5.8.9 | none → none |  | B6：現本体・固定Mathlibを再検索。fibration tower の極限と標準射はある。Postnikov 塔の各段のファイバーを K(π_n,n) とする標準ホモトピー同値は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.5.8.10 | none → none |  | B6：現本体・固定Mathlibを再検索。任意の指定した Kan fibration の塔の極限はある。弱 cosk の transition が Kan fibration であるという型は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.5.9.1 | none → none |  | B6：現本体・固定Mathlibを再検索。Is0TruncatedSpace は対象の零次の場合。負次数も含む任意の射の truncation を π の単射・全射で定義する型は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.5.9.8 | none → none |  | B6：現本体・固定Mathlibを再検索。ファイバーが可縮なら自明 Kan fibration という全次数の結果はある。任意 n の相対 truncation を各ファイバーで判定する iff は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.5.9.10 | none → none |  | B6：現本体・固定Mathlibを再検索。片脚の Kan 置換によるホモトピー引き戻しはある。一般の写像の n-truncation をホモトピーファイバーに移す型は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.5.9.11 | none → none |  | B6：現本体・固定Mathlibを再検索。基底変換での弱同値保存はある。n-truncated な射の引き戻しでの保存と π₀ 全射による反映は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.5.9.12 | none → none |  | B6：現本体・固定Mathlibを再検索。Kan 置換と通常ファイバーによる判定は全次数の弱同値に限る。ホモトピーファイバーの n-truncation と原文の三条件の比較は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.5.9.13 | none → none |  | B6：現本体・固定Mathlibを再検索。全次数の π 同型や π₀ 全射に基づく Whitehead 判定はある。始域の n-truncation と (n−1)-truncated な射から終域へ移す型は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.5.9.14 | none → none |  | B6：現本体・固定Mathlibを再検索。ホモトピー引き戻しの模型と弱同値保存はある。四頂点の異なる切断次数から残りの頂点の n-truncation を得る型は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.5.9.15 | none → none |  | B6：現本体・固定Mathlibを再検索。弱同値の二対三性はある。n と n−1 を混ぜた相対 truncation の合成・消去の三条件は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.5.9.16 | none → none |  | B6：現本体・固定Mathlibを再検索。任意の Kan fibration のホーン持ち上げ性はある。k と n+2 の大小で境界条件から相対 truncation を回収する条件は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.5.9.17 | none → none |  | B6：現本体・固定Mathlibを再検索。全境界に対する自明 Kan fibration の判定はある。k≥n+2 の指定次元で境界充填の有無を相対 truncation に結び付ける宣言は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.5.9.18 | none → none |  | B6：現本体・固定Mathlibを再検索。相対対角の pullback とファイバー比較はある。対角が (n−1)-truncated であることによる相対 n-truncation の再帰判定は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.5.9.20 | none → none |  | B6：現本体・固定Mathlibを再検索。fibration の高次境界充填を全 π 同型から得る結果はある。原文の有限次元での相対 truncation の特徴づけは見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.5.9.21 | none → none |  | B6：現本体・固定Mathlibを再検索。境界包含に対する相対内部 Hom の比較は fibration になる。指定の写像空間の正方形のホモトピー引き戻し性による truncation 判定は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.5.9.23 | none → none |  | B6：現本体・固定Mathlibを再検索。境界からの内部 Hom はある。定値写像を送る対角の弱同値性と X の n-truncation の iff は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.5.9.24 | none → none |  | B6：現本体・固定Mathlibを再検索。骨格と部分複体に沿う制限の fibration 性はある。所定骨格を含む場合の弱同値性を相対 n-truncation と比較する四条件は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.5.9.25 | partial → none |  | B6：極限への射のfibration性は指定の n-truncation の保存を結論しない。 候補：FibrationTower.projection_zero_fibration は Kan fibration の塔の極限から初項への射が fibration と示す。transition の有限次数の truncation が保たれる結論は未確認。 |
| 3.5.9.26 | partial → none |  | B6：極限のKan性は n-truncation の保存という結論ではない。 候補：Kan fibration の塔で初項が Kan なら極限も Kan となるインスタンスはある。各段の n-truncation を極限へ移す結論は未確認。 |
| 3.5.9.27 | partial → none |  | B6：比較射のfibration性は (n−k)-truncation の結論ではない。 候補：相対内部 Hom の比較が Kan fibration になる。入力の n-truncation と包含の次元を用いた比較の (n−k)-truncation は未確認。 |
| 3.5.9.28 | partial → none |  | B6：制限射のfibration性は (n−k)-truncation の結論ではない。 候補：Kan 標的と単射に沿う制限写像の fibration 性はある。次元 k によって truncation が n−k になる主張は未確認。 |
| 3.5.9.29 | none → none |  | B6：現本体・固定Mathlibを再検索。内部 Hom への定値写像はある。A の連結度に応じて対角 X→Fun(A,X) の truncation を n−k とする型は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.5.9.30 | partial → none |  | B6：内部Homのfibration保存は n-truncation の結論ではない。 候補：内部 Hom の後合成が Kan fibration を保存する。有限次数の n-truncation を保つ型は未確認。 |
| 3.5.9.31 | partial → none |  | B6：内部HomのKan性は n-truncation の結論ではない。 候補：任意の単体集合 B から Kan X への Fun(B,X) の Kan 性はある。X の n-truncation を保つ型は未確認。 |
| 3.5.9.32 | none → none |  | B6：現本体・固定Mathlibを再検索。境界での相対内部 Hom の Kan fibration 性はある。対象の truncation と境界への定値写像の比較図式を結ぶ三条件は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.5.9.33 | none → none |  | B6：現本体・固定Mathlibを再検索。全 Kan 標的への前合成による弱同値の判定はある。n-truncated 標的と (n+1)-connective 射の間の直交性を述べる五条件は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.6.0.1 | partial → none |  | B6：普通の実現/特異の随伴は原文のCW型を持つ空間のホモトピー圏との同値の部品。 候補：幾何学的実現 SSet.toTop と特異単体集合 TopCat.toSSet の随伴はある。両方の弱ホモトピー同値を反転した圏の同値は未確認。 |
| 3.6.1.9 | partial → partial | direction | B6：Finite.instIsFinitelyPresentable は X.Finite から Hom(X,−) が filtered colimit を保つという原文の向きを直接与える。逆向きの有限性は含まない。 |
| 3.6.1.11 | none → none |  | B6：現本体・固定Mathlibを再検索。有限単体集合と CW 部分複体の API はある。実現のコンパクト部分集合を有限単体部分複体の実現に含める判定は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.6.1.12 | none → none |  | B6：現本体・固定Mathlibを再検索。単体集合の有限性と CW の有限性は別々に定義される。幾何学的実現の CompactSpace との iff は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.6.1.13 | none → none |  | B6：現本体・固定Mathlibを再検索。CW の閉性公理はある。指定の各非退化単体に対する条件から実現中の部分集合 S の閉性を得る宣言は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.6.2.1 | none → none |  | B6：現本体・固定Mathlibを再検索。SSet.toTop は左随伴で余極限を保つ。有限極限を保つ便利な位相空間の実現の型は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.6.2.2 | none → none |  | B6：現本体・固定Mathlibを再検索。標準単体の実現の同相と、一般の位相空間の積はある。片方が有限単体集合のとき実現の積比較が同相という宣言は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.6.2.6 | none → none |  | B6：現本体・固定Mathlibを再検索。通常の実現は標準単体からの左 Kan 拡張。有限分割 S に依存する 実現 X_S の余極限模型は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.6.2.8 | partial → partial | component | B6：NonemptyFinLinOrd は原文の Lin_{≠∅} の対象と単調写像を直接束ねる構成成分。[0,1]から有限集合を除いた成分集合の有限性・順序は含まない。 |
| 3.6.2.9 | none → none |  | B6：現本体・固定Mathlibを再検索。標準単体の通常の実現は位相的単体と同相。有限分割模型の値を線形順序集合の Hom とする全単射は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.6.3.1 | partial → none |  | B6：位相のπで定義した弱同値を Sing(f) のホモトピー同値と比較する宣言がない。 候補：位相空間の weakHomotopyEquivalences は π₀ と全基点・正次数の π_n の全単射で定義する。Sing(f) の単体的な弱ホモトピー同値性との iff は未確認。 |
| 3.6.3.8 | none → none |  | B6：現本体・固定Mathlibを再検索。モデル圏一般の Whitehead 型と位相空間の弱ホモトピー同値の定義はある。CW の仮定で位相的ホモトピー逆を返す定理は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.6.3.10 | none → none |  | B6：現本体・固定Mathlibを再検索。位相的な全基点の π の全単射は弱同値の定義である。それを CW のホモトピー同値へ強める Whitehead の結論は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.6.3.11 | none → none |  | B6：現本体・固定Mathlibを再検索。被覆写像のホモトピー持ち上げはある。弱ホモトピー同値に沿う CW の任意写像のホモトピーまでの持ち上げは見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.6.4.1 | partial → none |  | B6：随伴のunitの存在は原文のunitの弱同値性の直接の部分結論ではなく、その対象射の構成だけ。 候補：実現と特異単体集合の随伴の単位 u_X を確認。u_X の弱ホモトピー同値性を述べる Milnor の定理は未確認。 |
| 3.6.4.2 | partial → none |  | B6：随伴のcounitの存在はその弱同値性を結論しない。 候補：実現と特異単体集合の随伴の余単位 v_X はある。位相空間での v_X の弱ホモトピー同値性は未確認。 |
| 3.6.4.3 | none → none |  | B6：現本体・固定Mathlibを再検索。実現関手と弱ホモトピー同値は別々に定義される。f の弱同値性、実現した写像の弱同値性とホモトピー同値性を結ぶ三条件は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.6.5.1 | none → none |  | B6：現本体・固定Mathlibを再検索。実現は普通の関手として定義される。Top の豊穣 Hom を特異単体集合としたときの実現の豊穣構造は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.6.5.2 | none → none |  | B6：現本体・固定Mathlibを再検索。実現と特異単体集合の随伴は普通の Hom の全単射。Kan 標的で二つの豊穣 Hom の比較の弱同値性は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.6.5.3 | none → none |  | B6：現本体・固定Mathlibを再検索。CWComplex と実現関手はある。CW 型を持つことと本文の四つの特徴づけを結ぶ宣言は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.6.5.4 | none → none |  | B6：現本体・固定Mathlibを再検索。普通の Hom の随伴全単射はある。CW 型の位相空間に対する本文の四条件とホモトピー類での普遍性は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.6.5.6 | none → none |  | B6：現本体・固定Mathlibを再検索。実現の左随伴性と弱同値を反転する局所化の API はある。本文で指定する二つの関手圏を結ぶ圏同値は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.6.6.1 | none → partial | stronger-hyp | B6：IsCoveringMap.liftHomotopy と liftHomotopy_lifts/zero は任意の位相空間 A に対し初時刻の持ち上げを直接返す。q を被覆写像に強め、A を標準単体の実現（3.6.6.8では任意 B の実現）に取ると、原文の区間持ち上げ条件が直接成立。一般の Serre fibration と相対条件全体の iff は含まない。 |
| 3.6.6.5 | none → none |  | B6：現本体・固定Mathlibを再検索。特異単体集合と単体の Kan fibration はそれぞれ定義される。位相の Serre fibration と Sing(q) の Kan fibration 性の同値は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.6.6.8 | none → partial | stronger-hyp | B6：IsCoveringMap.liftHomotopy と liftHomotopy_lifts/zero は任意の位相空間 A に対し初時刻の持ち上げを直接返す。q を被覆写像に強め、A を標準単体の実現（3.6.6.8では任意 B の実現）に取ると、原文の区間持ち上げ条件が直接成立。一般の Serre fibration と相対条件全体の iff は含まない。 |
| 3.6.6.10 | none → none |  | B6：現本体・固定Mathlibを再検索。位相の被覆写像の持ち上げと局所同相の API はある。本文の局所条件を満たす一般の q が Serre fibration になる宣言は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。 |
| 3.6.6.11 | partial → partial | special | B6：IsCoveringMap.liftHomotopy と lifts/zero は全空間が離散ファイバーの被覆である場合、任意のパラメータ（特に実現した標準単体）で初時刻を固定する区間持ち上げを直接返す。一般のファイバー束の全体は含まない。 |

## 検査

原文は Kerodon 公式小節の各項目Tagで照合。none は現本体・ロックしたMathlibを再検索し、近隣項目のソース・双対/限定版の候補も照合した。Archiveの宣言をown・partialの根拠にはしていない。宣言の存在と型はソースでの確認で、kernel確認ではない。
