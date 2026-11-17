# KB-W1 / B6 第4章

原文の項目と現在のソースの型による紙の再照合。Lean・ビルド・鍵は使っていない。

対象 454行。partial 267、none 187。判定後：partial 130、none 318、own 6。

既存 own・both・mathlib 134行の全既存フィールドは変更なし。既存7列の末尾に partial_kind を追加し、対象外行は空欄とした。区切り・改行と対象外行の既存引用符を保存した。verdict・axioms・check も変更していない。古いcheck欄は今回のkernel検査結果ではない。

## 全対象行の判定・変更一覧

状態不変でも型/原文の再判定を記録した。各 reason の詳細はCSVと同じ。原文全文・候補の型・検索はgit外の章別証拠。

| 番号 | 旧→新 | partial_kind | 理由 |
| --- | --- | --- | --- |
| 4.1.1.10 | partial → partial | direction | quasicategory_of_innerFibration を標的 nerve に適用すると q が inner fibration⇒X が準圏という原文の向きを直接得る。逆向きの引用は薄い圏に限る。 |
| 4.1.1.11 | partial → partial | special | thinNerve_innerFibration は標的 D が薄い圏のとき、同じ nerveMap F の内ファイブレーション性を直接与える。任意の通常圏 D は含まない。 |
| 4.1.2.2 | partial → partial | component | InnerFibration を部分複体の包含 A.ι に適用した型は原文のホーン持ち上げ条件そのもの。部分圏として束ねる専用の型は含まない。 |
| 4.1.2.10 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：通常圏の部分圏・ホモトピー圏・頂点指定または全可逆辺を照合。hC の任意の部分圏と C の部分複体の全単射。全部分複体の頂点指定は射集合を動かさない。 |
| 4.1.2.11 | partial → none |  | posetFullSubcomplexNerveLift は一つの比較写像の構成だけ。部分圏の二集合の全単射やその制限版を直接返す型ではない。 |
| 4.1.2.12 | partial → partial | special | fullSubcomplexOnVertices は T を選んだ S の頂点間の全ての辺とする場合の部分複体を直接作る。任意に指定する T の四条件による存在と一意性全体は含まない。 |
| 4.1.2.13 | partial → partial | special | 頂点条件による充満部分圏と全対象・可逆辺に限る core は、原文の S,T をこの二種類に制限した構成を直接与える。任意の S,T の構成は含まない。 |
| 4.1.2.15 | partial → partial | special | fullSubcomplexOnVertices の次数別の条件から、この構成で得た部分複体は全頂点が入る単体を全て含む。任意の部分複体についての充満性の述語・包含の inner fibration 性の一般命題は含まない。 |
| 4.1.2.16 | partial → partial | component | fullSubcomplexOnVertices の条件は全頂点の所属であり、頂点集合が S である充満部分複体の存在を直接与える。一意性は含まない。 |
| 4.1.3.2 | partial → partial | component | exists_innerAnodyne_innerFibration_factorization は同じ f の指定二種類の射への分解の存在を直接返す。関手性・filtered colimit 保存は含まない。 |
| 4.1.3.3 | partial → partial | component | exists_quasicategory_resolution_over を終対象への射に適用すると原文の inner anodyne な準圏置換の存在を直接得る。関手性・filtered colimit 保存は含まない。 |
| 4.1.4.4 | partial → partial | special | trivialKanFibration_pre_of_innerAnodyne は底が終対象の場合に同じ制限射の自明 Kan 性を直接与える。一般の相対評価は含まない。 |
| 4.1.4.5 | partial → partial | special | trivialKanFibration_pre_of_innerAnodyne と内ホーン Λ²₁ の所属から、底が終対象・X が準圏の場合の同じ制限射の自明 Kan 性を直接得る。一般の底と逆向きは含まない。 |
| 4.1.4.6 | partial → none |  | 引用は相対内部Homの比較射の内ファイブレーション性と一般の頂点ファイバーの準圏性という部品。原文の特定の延長空間との同定を型に持たず、可縮性も結論しない。 |
| 4.1.4.7 | partial → none |  | 一般の頂点ファイバーと特定制限射を別々に扱う部品で、Fun_{A/}(B,C) という指定延長空間の構成との同定がない。自明 Kan 性だけもそのファイバーの可縮性とは別。 |
| 4.1.5.1 | partial → none |  | strictSegal は spine の延長一意性で、原文は相対内ホーンの一意持ち上げ。nerve の特殊形でもホーンとspineの比較がさらに必要。 |
| 4.1.5.10 | partial → none |  | strictSegal だけは原文の inner covering のホーン持ち上げを直接返さない。始域がnerve・底が一点に限っても比較の議論が必要。 |
| 4.1.5.11 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：通常圏・離散ファイバー・ホーン一意性・双対と底変換を照合。各 Δⁿ への底変換の nerve 表示による一意内ホーン充填の判定。引き戻しの補題は解の存在のみ。 |
| 4.2.2.1 | partial → partial | component | IsFibered の cartesian lift の存在から原文(A)の任意の底の射の持ち上げが直接得られる。全ての射についてのHomのpullback条件(B)は含まない。 |
| 4.2.2.4 | partial → none |  | IsStronglyCocartesian は選んだ一つの射についての普遍性。原文の任意の底の射の持ち上げの存在も、全ての射に対するpullback条件もこの型だけでは返さない。 |
| 4.2.2.9 | partial → partial | special | costructuredArrowProjection_rightFibration は U=CostructuredArrow.proj Q V の同じ nerveMap U の right fibration 性を直接返す。このUでの右側の結論だけで、一般のiffやopfibration側は含まない。 |
| 4.2.3.1 | partial → partial | stronger-hyp | Prefunctor.IsCovering は star と costar の全単射で、関手の基礎quiverについて仮定すると原文の左・右の一意持ち上げを直接得る。片側だけでよい原文より強い。 |
| 4.2.3.7 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：離散ファイバーの場合・全ホーンの一意性・1圏の圏 of elementsを照合。一意な通常圏の辺の持ち上げと離散ファイバーの判定。Quiver の star/costar はファイバー圏の離散性を参照しない。 |
| 4.2.3.8 | partial → partial | component | LeftFibration/RightFibration は原文と同じホーン族について持ち上げの存在部分を直接表す。一意性を要求するcoveringの条件は含まない。 |
| 4.2.3.16 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：離散ファイバーの場合・全ホーンの一意性・1圏の圏 of elementsを照合。nerve を底とする左・右被覆と通常圏の被覆関手の両方向の比較。Quiver の被覆には nerve の比較がない。 |
| 4.2.3.18 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：離散ファイバーの場合・全ホーンの一意性・1圏の圏 of elementsを照合。左被覆を各標準単体への底変換における通常圏の左被覆で判定する iff。ホーンの持ち上げの底変換は一意性を扱わない。 |
| 4.2.3.19 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：離散ファイバーの場合・全ホーンの一意性・1圏の圏 of elementsを照合。左または右の一意ホーン充填と頂点全単射から同型を得る iff。頂点全射な充満忠実射の結論は圏同値。 |
| 4.2.3.20 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：離散ファイバーの場合・全ホーンの一意性・1圏の圏 of elementsを照合。左／右の一意ホーン充填と Kan fibration の組で被覆を判定する iff。LeftFibration と Kan fibration の型は一意性を含まない。 |
| 4.2.4.1 | partial → partial | component | leftAnodyneExtensions は指定生成ホーンの所属と弱飽和の各閉性を直接持つ。原文の最小性との同定は含まない。 |
| 4.2.4.2 | partial → partial | component | rightAnodyneExtensions は指定生成ホーンの所属と弱飽和の各閉性を直接持つ。最小弱飽和閉包との逆包含は含まない。 |
| 4.2.4.7 | partial → partial | component | exists_leftAnodyne_leftFibration_factorization は同じ f の指定分解の存在を直接返す。関手性とfiltered colimit保存は含まない。 |
| 4.2.4.8 | partial → partial | component | exists_rightAnodyne_rightFibration_factorization は同じ f の指定分解の存在を直接返す。関手性とfiltered colimit保存は含まない。 |
| 4.2.4.10 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：ホーン生成・単体ごとの分解・反対と通常モデル圏を照合。第0頂点から Λⁿⱼ へ低次元の左ホーンを一枚ずつ付ける有限フィルトレーション。標準単体への包含の補題は終域が Δⁿ。 |
| 4.2.4.12 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：ホーン生成・単体ごとの分解・反対と通常モデル圏を照合。左アノダインに対する一意な持ち上げと次数ごとの集合の引き戻しとの同値。rlp の既存等式は存在しか扱わない。 |
| 4.2.6.1 | partial → partial | direction | relativeEdgeSource_trivialKanFibration は left fibration⇒ev₀の自明Kan性という原文の向きを直接返す。右側のiffと逆向きは含まない。 |
| 4.2.6.2 | partial → partial | special | kanIntervalEvaluation_trivialKanFibration は底が一点で X が Kan のときの ev₁ の自明Kan性を直接返す。相対の二端点の同時判定・逆向きは含まない。 |
| 4.3.2.9 | partial → none |  | Join.inclLeft/inclRight と edge は元の包含と混合辺。原文の slice/coslice への特定の持ち上げとその一意性の結論ではなく、構成の材料。 |
| 4.3.2.10 | partial → none |  | mkFunctor の入力は自然変換で、原文の E_{/G} 値の関手ではない。isoMkFunctor も同型までの復元で、指定のslice関手への全単射を得る比較が要る。 |
| 4.3.2.13 | partial → none |  | mkFunctor と isoMkFunctor は制限を同型まで復元する。原文の厳密な指定制限を持つ関手と自然変換の全単射へ移す比較と逆写像の法則が型にない。 |
| 4.3.2.16 | partial → none |  | mkFunctor の入力は自然変換で、原文の E_{F/} 値の関手ではない。cosliceとの比較と指定制限の一致がさらに要る。 |
| 4.3.2.17 | partial → none |  | mkFunctor と isoMkFunctor は対象ごとの延長の部品。指定のCat上のjoinとslice/cosliceの随伴のいずれの構造も直接与えない。 |
| 4.3.3.2 | partial → partial | special | Join.Simplex は空区間の値が一点である通常単体集合のcanonicalな増大の場合、初期区間の長さと左右の単体の組という原文の次数別データを直接与える。任意のLin上の増大関手とその全作用は含まない。 |
| 4.3.3.9 | partial → none |  | augObj は次数別の値だけで、Linの反対圏からの関手もその充満部分圏も直接構成しない。空次数の値の一致だけは原文の関手圏の構成ではない。 |
| 4.3.3.11 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：反転・左右交換・空・一点の縮約・通常圏版を照合。空順序の値が一点の Linᵒᵖ 上の関手と SSet の圏同値。augObj は次数ごとの増大単体を定めるだけ。 |
| 4.3.3.13 | partial → partial | component | join と joinMap はcanonicalな増大の初期区間の分割式で原文のjoinの単体と射を直接構成する。Lin上の関手圏との可換図式を束ねる同型は含まない。 |
| 4.3.4.1 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：位相空間の join・幾何実現・単体集合版・一点・球面・縮約を照合。位相空間の X×[0,1]×Y の両端を射影で潰す join。fatJoin の対象と押し出しは SSet。 |
| 4.3.4.8 | partial → none |  | joinStdSimplexIso は単体集合のjoinの同型。原文は位相的joinからの特定関数 H_{p,q} の同相性であり、実現のjoin比較がさらに要る。 |
| 4.3.4.9 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：位相空間の join・幾何実現・単体集合版・一点・球面・縮約を照合。&#124;X⋆Y&#124; から位相空間の join &#124;X&#124;⋆&#124;Y&#124; への連続写像。joinCylinderMap は単体集合の射。 |
| 4.3.4.11 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：位相空間の join・幾何実現・単体集合版・一点・球面・縮約を照合。片方が有限のときの実現と位相的 join の比較の同相性。単体集合内の太い join の比較は別。 |
| 4.3.4.12 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：位相空間の join・幾何実現・単体集合版・一点・球面・縮約を照合。実現した左右の錐と位相的錐の同相。pointJoinStdSimplexIso は標準単体上の単体的な錐。 |
| 4.3.4.13 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：位相空間の join・幾何実現・単体集合版・一点・球面・縮約を照合。任意の X,Y に対する実現と位相的 join の比較の全単射。fatJoinComparison は実現を含まない。 |
| 4.3.5.12 | partial → partial | component | sliceOverUncurry と sliceUnderUncurry をそれぞれ恒等射に適用すると、原文のslice/cosliceの評価による収縮写像を直接構成する。指定の各制限の等式の一式までは引用型にない。 |
| 4.3.5.17 | partial → partial | special | nerveOverIso/nerveUnderIso は図式 K が一点で F が一つの対象 c を選ぶ場合の同じslice/cosliceのnerve比較同型。任意Kとそのホモトピー圏を経由する比較は含まない。 |
| 4.3.5.18 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：通常圏の slice・左右と反転・頂点または同値での比較を照合。h(A⋆B) と hA⋆hB の比較。slice の随伴と通常の Join は双方あるが、この h の交換を示さない。 |
| 4.3.6.6 | partial → none |  | joinUnion はA₀⋆BとA⋆B₀の和で、B₀を空にしても左の全頂点Aが残り、原文のA₀⋆Bそのものではない。別の包含の内anodyne性は証明部品。 |
| 4.3.6.10 | partial → none |  | relativeCosliceMap/relativeSliceOverMap は相対fiber productへの射。原文の単なる後合成への比較・射影との合成とその性質がさらに要る。 |
| 4.3.6.11 | partial → partial | special | sliceOverPostcomp_trivialKanFibration_of_rightFibration は K=Δ⁰ の同じ後合成射の自明Kan性を直接返し、従ってright fibrationでもある。一般Kと双対側は含まない。 |
| 4.3.6.12 | partial → partial | component | sliceUnderRestrict_leftFibration は原文のcoslice側の同じ制限射のleft fibration性。Archiveのslice側は根拠に含めない。 |
| 4.3.6.13 | partial → partial | component | relativeCosliceMap_trivialKanFibration_of_rightAnodyne は原文のright anodyne包含でのcoslice側の同じ相対射の自明Kan性を直接返す。slice側は含まない。 |
| 4.3.6.17 | partial → partial | direction | 準圏を仮定する二つのprojectionのinstanceは原文(1)⇒(2),(3)を直接返す。(2)または(3)から準圏性への逆方向は含まない。 |
| 4.3.7.1 | partial → none |  | joinUnion_pointBoundary_anodyne はanodyneだけで、原文のleft/right anodyneの結論とは異なる。joinPoint_monoの二宣言も、点を置く側では原文が要求する反対側のanodyne性を返さず同じ特殊形の結論にならない。 |
| 4.3.7.2 | partial → partial | special | relativePointSliceUnderMap_fibration は K=Δ⁰、K₀=∅、qがKan fibrationの場合の原文coslice側と同じ相対射のKan fibration性。一般K・right fibrationだけの仮定は含まない。 |
| 4.3.7.3 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：単射の制限・左/右の底変換と Kan の特例・片側が一点を照合。左 fibration による slice と右 fibration による coslice の、X×_S を終域とする Kan fibration。相対比較の右／左 fibration だけでは結論が異なる。 |
| 4.3.7.4 | partial → partial | stronger-hyp | cosliceの二端をKanとも仮定すれば sliceUnderRestrict_leftFibration と leftFibration_fibration_of_kanComplex から同じ制限射のKan fibration性を直接得る。この全空間Kan性の追加仮定とcoslice側だけに限る。 |
| 4.3.7.5 | partial → partial | stronger-hyp | 原文のslice/cosliceの全空間もKanと仮定すると、両projectionのleft/right性とKan昇格の型から同じ二つの射影のKan fibration性を直接得る。全空間のKan性を原文の仮定だけから示したとはしない。 |
| 4.3.7.6 | partial → partial | stronger-hyp | coslice側について、包含をanodyneかつright anodyneに強めれば relativeCosliceMap_trivialKanFibration_of_rightAnodyne が同じ相対射の自明Kan性を直接返す。一般anodyneだけの場合とslice側は含まない。 |
| 4.3.7.7 | partial → partial | stronger-hyp | 包含に IsPrecompositionEquivalence も仮定すると、二つの restrict_trivialKanFibration 宣言が原文と同じ制限射の自明Kan性を直接返す。Kan–Quillen anodyneだけからこの追加仮定を得たとはしない。 |
| 4.3.7.9 | partial → partial | special | joinPoint_mono_leftAnodyne と joinPoint_mono_rightAnodyne は原文で可縮とする因子がそれぞれ Δ⁰ の場合の同じ joinMap の結論。一般の弱可縮な因子は含まない。 |
| 4.3.7.12 | partial → partial | special | sliceUnderPostcomp_trivialKanFibration は K=Δ⁰ と left fibration q の場合の同じcoslice後合成の自明Kan性。任意の弱可縮K・slice側は含まない。 |
| 4.3.7.13 | partial → own |  | coslice側は sliceUnderPostcomp_trivialKanFibration、slice側も現本体の sliceOverPostcomp_trivialKanFibration_of_rightFibration が点図式の同じ後合成射の自明Kan性を直接返す。両側を満たし、定理名の不足だけでpartialにはしない。 |
| 4.3.7.14 | partial → none |  | sliceUnder_isWeaklyContractible は弱可縮性だけで、原文のslice/cosliceのKan性と終射のホモトピー逆の存在を直接返さない。原文の可縮Kanという同じ結論へ比較する議論が要る。 |
| 4.3.7.15 | partial → none |  | 原文の K₀=∅ でも値域は X×_S S_{/qf} 等であり、単なる S_{/qf} ではない。引用の後合成は始点の指定を忘れる別の射で、同じ特殊形の自明Kan性にはならない。 |
| 4.3.7.16 | partial → none |  | 引用は S_{/qf} または S_{qf/} への後合成で、原文は X×_S S_{/qf} などへの始点を保持する比較。異なる射の類似の性質はpartialに数えない。 |
| 4.3.7.18 | partial → partial | stronger-hyp | 包含に IsPrecompositionEquivalence も仮定すると二つのrestrict宣言から同じ射の自明Kan性を直接得る。可縮Kan値域だけでは任意の包含についてこの追加仮定を解消していない。 |
| 4.3.7.19 | partial → none |  | 射影のleft/right fibration性は自明Kan性という結論そのものではない。可縮な底という仮定だけから全空間・全ファイバーの可縮性を得る比較がさらに要る。 |
| 4.4.1.1 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：1圏の同型持ち上げ・辺の向きの反転・nerve と hCを照合。通常の圏で指定した終点への同型の厳密な持ち上げ。InvertibleTargetLifting の対象は単体集合。 |
| 4.4.1.3 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：1圏の同型持ち上げ・辺の向きの反転・nerve と hCを照合。通常の圏の isofibration が F.op と同値。EquivalenceLifting.op の対象は SSet。 |
| 4.4.1.4 | partial → own |  | equivalenceLifting_iff_inner_and_invertibleTargetLifting の右辺は、原文と同じ inner 性と終点指定の可逆辺の可逆な持ち上げ。原文と同じ準圏間の仮定で EquivalenceLifting が二条件と同値になるので、別名でも定義全体を表す。 |
| 4.4.1.7 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：1圏の同型持ち上げ・辺の向きの反転・nerve と hCを照合。F の isofibration と hF における同型の厳密な持ち上げの iff。既存の持ち上げ条件は辺を直接取る。 |
| 4.4.1.9 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：1圏の同型持ち上げ・辺の向きの反転・nerve と hCを照合。正準写像 C→N(hC) の isofibration 性。h の随伴の単位が存在することだけでは同型の持ち上げは得られない。 |
| 4.4.1.11 | partial → partial | component | leftFibration_invertibleTargetLifting は原文のleft fibration側の可逆辺を可逆な辺へ持ち上げる条件を直接返す。一般のright側とisofibrationとの同値の一式は引用に含まない。 |
| 4.4.2.1 | partial → partial | component | kanComplex_iff_isGroupoid と kanComplex_of_leftHornFillers は原文の (b)⇔(c) の準圏上での比較と (e)⇒(b) を直接与える。right fibrationを含む六条件全体は含まない。 |
| 4.4.2.2 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：逆辺または Kan・Δ¹ と可逆区間・通常圏の同型を照合。Duskin nerve の Kan 性と 2-groupoid 性の iff。通常圏の nerve と IsGroupoid の比較は次元が異なる。 |
| 4.4.2.4 | partial → partial | special | relativeFunctorSpace_kanComplex は A=∅、qがleft fibrationの場合の同じ底上の写像空間のKan性を直接返す。任意の境界制限とanodyne時の可縮性は含まない。 |
| 4.4.2.7 | partial → none |  | isLimitCone_of_conservative_image は原文の保守性を入力仮定に使う別の極限反映の定理。入力仮定の文字列の一致だけは保守性を定義する宣言の対応としない。 |
| 4.4.2.12 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：逆辺または Kan・Δ¹ と可逆区間・通常圏の同型を照合。F が同型を反映することから左右の slice の後合成も同型を反映する主張。相対制限の fibration 補題は別の条件。 |
| 4.4.2.14 | partial → partial | direction | rightFibration_trivialKanFibration_of_contractible_fibers は原文(3)⇒(1)を直接返す。vertexFiber_isContractibleKanも逆向きの可縮性成分を持つが、left側の全比較は含まない。 |
| 4.4.2.15 | partial → none |  | 引用はright fibrationと標準単体の最初の頂点の可縮fiber。原文はleft fibrationと最後の頂点を指定しており、opを取る比較をさらに必要とする双対命題そのものはpartialにしない。 |
| 4.4.3.6 | partial → own |  | coreInclusion_equivalenceLifting と equivalenceLifting_iff_inner_and_invertibleTargetLifting により、同じcore包含は原文のisofibrationの二条件をともに満たす。coreInclusion_innerFibrationも直接あり、名称の差だけでpartialにしない。 |
| 4.4.3.8 | partial → partial | stronger-hyp | rightFibration_fibration_of_kanComplex は始域もKanと仮定すると原文(3)⇒(1)を同じqについて直接返す。fibration_leftFibrationは(1)⇒(2)。始域が任意の場合と保守的isofibrationの条件は含まない。 |
| 4.4.3.9 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：通常圏と Kan からの因子化・左/右または引き戻し・単体の条件を照合。Kan 複体を底にする左／右被覆の同値。Quiver の被覆はホーンを用いない。 |
| 4.4.3.13 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：通常圏と Kan からの因子化・左/右または引き戻し・単体の条件を照合。replete 部分圏の core が元の core の直和因子になる主張。全部分複体の包含に直和分解を与える型がない。 |
| 4.4.3.14 | partial → partial | direction | kanSource_edge_isInvertible と IsInvertibleEdge.map により、Kan複体の辺をFで送ったuは可逆で、原文(2)⇒(1)を直接得る。逆にKan/可縮Kanからの表示を構成する方向は含まない。 |
| 4.4.3.15 | partial → partial | direction | exists_equivalenceInterval_map_of_vertexIso は、二対象の同型から同じ二頂点を持つ可逆区間からの射を直接与える。可逆区間はcodiscreteな二点亜群のnerveで可縮Kanであり、(1)から存在条件への向き。一般の逆方向は含まない。 |
| 4.4.3.16 | partial → partial | component | nonempty_vertexIso_of_piZero_eq をKan coreに適用し包含で送ると、同じπ₀成分の二対象が元のCで同型になる方向を直接得る。同型類の集合との全単射・逆方向は含まない。 |
| 4.4.3.18 | partial → partial | component | kanSourceCoreMap と包含との厳密な回収式をKan部分複体Aの包含に適用するとA⊆coreを直接得る。原文の最大性の成分。core自身のKan性はこの引用の結論に含まない。 |
| 4.4.3.19 | partial → partial | component | quasicategoryCoreMap_isPullback_of_isPullback は同じ指定したcore四角形の厳密なpullback性を直接返す。ホモトピーpullback性・同型の反映・q′のisofibration性は含まない。 |
| 4.4.3.22 | partial → partial | stronger-hyp | qにさらにrightまたはleft fibrationを仮定すると、vertexFiber_kanComplexの二宣言から同じ指定fiberのKan性を直接得る。保守的isofibrationだけからの導出は含まない。 |
| 4.4.3.23 | partial → none |  | equivalencePathι_isIso_of_kanComplex の始域は可逆辺の部分複体で、原文はKanパラメータからの関手空間のcore比較。Δ¹はKanでもなく、原文の特殊形としてこの型をそのまま使えない。 |
| 4.4.4.1 | partial → none |  | FunctorIsoは関手空間のホモトピー圏の同型データ。原文の実際の可逆な自然変換の辺を与える型ではなく、代表を選んで比較する宣言がさらに必要。 |
| 4.4.4.6 | partial → none |  | quasicategoryCoreProduct は比較射の構成だけで同型性・普遍性を述べない。指定関手の極限保存の特殊形を直接結論しない。 |
| 4.4.4.7 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：普通の自然同型・二項積と core・一点と prismを照合。Δᵐ×Δⁿ の指定始辺を保つ外ホーン付き有限フィルトレーション。prism の既存分解は Δ¹ または別の境界を使う。 |
| 4.4.4.8 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：普通の自然同型・二項積と core・一点と prismを照合。全頂点を含む A 上の相対ホーン図式を与え、各点のファイバーの辺が可逆なときの延長。一般の inner fibration での当該比較は未発見。 |
| 4.4.4.9 | partial → none |  | isInvertibleEdge_vertexFiber_iff はfiberの辺と全空間の辺の可逆性の比較。原文は底上の関手空間での可逆性と各評価fiberでの可逆性の比較で、Bが一点でも対象同定がさらに必要。 |
| 4.4.5.4 | partial → own |  | equivalenceLifting_pre が同じ制限射にEquivalenceLiftingを返し、それをcoreMap_fibration_of_kanEquivalenceLiftingにそのまま代入すると原文のcore制限射のKan fibration性を得る。仮定・対象・射が一致し追加の数学的比較は要らない。 |
| 4.4.5.5 | partial → none |  | 二つの端点への各射影の自明Kan性は、両端の組への原文の射のisofibration性ではない。別の射の性質だけをcomponentにしない。 |
| 4.4.5.7 | partial → own |  | EquivalenceLifting.internalHom に任意Bを代入し、coreMap_fibration_of_kanEquivalenceLiftingをその結果に適用すると、原文の同じ内部Homのcore後合成のKan fibration性を得る。isofibrationとの比較は二条件のiffで確認済み。 |
| 4.4.5.8 | partial → partial | special | prism_lift_boundary_with_final_endpoint は B=Δ^(n+1)、A=その境界で最後の垂直辺が可逆な原文と同じprism持ち上げを直接返す。Aが全頂点を含む次元とその境界形に限る。 |
| 4.4.5.9 | partial → none |  | relativeEquivalencePathMapAtの自明Kan性は特定の可逆path空間の持ち上げ。原文の点ごとに可逆なprism全体をその空間に入れる比較と条件の同定を型で与えず、証明部品にとどまる。 |
| 4.4.5.11 | partial → partial | stronger-hyp | FにさらにEquivalenceLifting（isofibration）を仮定すると relativeInternalHom が同じ比較射F′のEquivalenceLiftingを直接返す。inner fibrationだけの場合は含まない。 |
| 4.4.5.12 | partial → partial | stronger-hyp | kanEquivalenceLifting_relativeFunctorOverPre_of_cocartesian はFがcocartesian fibrationである場合、同じ底上の関手空間の制限射のEquivalenceLiftingを直接返す。inner fibrationだけの場合は含まない。 |
| 4.5.1.5 | partial → none |  | Kan始域のrawな写像のcoreへの因子化はあるが、hQCat/hKanのHomの同じ商とその指定の包含による全単射の比較は型にない。商への降下の部品だけは数えない。 |
| 4.5.1.6 | partial → none |  | quasicategoryCoreLift は対象ごとの因子化という部品。hQCatとhKanの指定包含の右随伴の型を直接構成しない。 |
| 4.5.1.8 | partial → none |  | continuousKanReplacementとstrictKanCompletionはSSet上の置換関手。原文のhQCat/hKanの包含の左随伴へ降ろす比較と普遍性がさらに要る。 |
| 4.5.1.16 | partial → partial | component | QCatEquivalence.postcompose は原文に明記された、同値Fによる同じ内部Hom後合成の同値性を直接与える。hQCat上に束ねた関手の構成は含まない。 |
| 4.5.1.22 | partial → partial | direction | IsQCatEquivalence.postcompose は全てのXに対して同じ後合成の同値性を返し、原文(1)⇒(2)を直接与える。他の条件と逆向きは含まない。 |
| 4.5.2.1 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：Kan の最小モデル・最小ファイブレーション・レトラクト・通常圏・skeletalを照合。A 上で恒等となる Fun(B,C) の同型の述語。FunctorIso は固定部分の条件を持たない。 |
| 4.5.2.4 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：Kan の最小モデル・最小ファイブレーション・レトラクト・通常圏・skeletalを照合。境界に相対的に同型な n 単体が等しいという極小性。Mathlib の Minimal は順序の極小元。 |
| 4.5.2.12 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：Kan の最小モデル・最小ファイブレーション・レトラクト・通常圏・skeletalを照合。極小な始域を持つ圏同値の単射性。全部分複体の包含の単射性とは仮定が異なる。 |
| 4.5.2.13 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：Kan の最小モデル・最小ファイブレーション・レトラクト・通常圏・skeletalを照合。両端が極小なら圏同値の単体写像自体が同型という主張。Quasicategory の同値は逆を同型までしか与えない。 |
| 4.5.2.14 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：Kan の最小モデル・最小ファイブレーション・レトラクト・通常圏・skeletalを照合。極小な二つの ∞ 圏について圏同値と厳密同型が同値。極小性の定義を使う候補がない。 |
| 4.5.2.15 | partial → none |  | 通常圏のskeletonは対象の同型類についての骨格で、原文の単体の相対ホモトピーを使うminimal性の型ではない。nerveへの特殊化でもminimalとの比較がさらに要る。 |
| 4.5.2.16 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：Kan の最小モデル・最小ファイブレーション・レトラクト・通常圏・skeletalを照合。極小 ∞ 圏の厳密同型類と一般の圏同値類の全単射。HomotopyQCat の商は関手の同型類。 |
| 4.5.3.8 | partial → none |  | catPullbackとその極限錐は選択した比較先の構成。原文の任意の四角形についての特定の比較写像が圏同値という述語を直接与えない。 |
| 4.5.3.11 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：厳密 pullback の特例・片側 isofibration・通常圏の iso commaを照合。Kan の正方形で categorical pullback とホモトピー引き戻しを同定する iff。Kan 置換の比較は categorical pullback を仮定しない。 |
| 4.5.3.12 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：厳密 pullback の特例・片側 isofibration・通常圏の iso commaを照合。底の一点が Kan である categorical pullback から弱ホモトピー引き戻しを得る方向。Kan 置換補題の前提は別。 |
| 4.5.3.15 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：厳密 pullback の特例・片側 isofibration・通常圏の iso commaを照合。任意の試験対象からの Fun の core による categorical pullback の判定。個別の catPullback の表現性は図式を固定する。 |
| 4.5.3.17 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：厳密 pullback の特例・片側 isofibration・通常圏の iso commaを照合。categorical pullback 正方形を反対 ∞ 圏に移す iff。通常の IsPullback の圏同値による保存は別条件。 |
| 4.5.3.18 | partial → none |  | 引用はKan–Quillenの局所化とKan置換模型のIsHomotopyPullbackの対称性。原文の可逆path模型への圏同値との比較がなく、Kanの特殊形でも同じ述語と確認できない。 |
| 4.5.3.19 | partial → none |  | Kan置換模型の局所化によるホモトピーpullbackの貼り合わせは別の述語。原文のcategorical pullbackとの同定がさらに必要。 |
| 4.5.3.20 | partial → partial | special | pullbackMap_isQCatEquivalence_of_components は両面が指定した厳密pullbackで、左脚がEquivalenceLiftingの場合に、同じ比較射F₀₁=pullback.mapの圏同値性を直接返す。任意のcategorical pullbackの三条件全体は含まない。 |
| 4.5.3.21 | partial → none |  | exists_catPullbackEquivalence は二つの選んだ模型の間に何らかの圏同値があるという結論。原文の特定の誘導射が同値であるという同じ射の結論ではない。 |
| 4.5.3.22 | partial → partial | special | pullback_snd_of_relativePath は四角が厳密なpullbackで、もう一方の脚にInnerFibrationと相対pathの自明Kan性を加えた場合、同じF′=pullback.sndの圏同値性を直接返す。任意の四角のcategorical pullbackとのiffは含まない。 |
| 4.5.3.23 | partial → none |  | laxPullbackEquivalenceSubcomplexの包含の充満忠実性とcatPullbackとの同型はあるが、原文のδはCからの対角埋め込みで包含とは異なる射。その像との比較がさらに要る。 |
| 4.5.3.24 | partial → none |  | path置換のUのEquivalenceLiftingはKが準圏の追加仮定で得られるが、引用型にはjのMono性・圏同値性・分解式を合わせた結論がない。sectionという構成の材料だけは数えない。 |
| 4.5.3.27 | partial → none |  | Cat∞での厳密pullbackの極限錐という性質は、原文の可逆path模型への特定比較射の同値性とのiffを直接返さない。Kan–Quillenの別模型のiffも同定が必要。 |
| 4.5.3.28 | partial → none |  | qCatPullbackInfinityCone_isLimit は錐としての極限性。原文のcategorical pullbackの定義の指定比較射の同値性と結ぶ宣言がなく、別の特徴づけへの比較が必要。 |
| 4.5.3.29 | partial → none |  | exists_strictPullback_catPullback_equivalence は何らかの圏同値の存在。原文の(C₀,C₁)↦(C₀,C₁,id)という特定射が同値という型ではない。 |
| 4.5.3.30 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：厳密 pullback の特例・片側 isofibration・通常圏の iso commaを照合。categorical pullback 正方形での任意の点の二つのファイバーの比較同値。Kan の cospan の比較は設定が異なる。 |
| 4.5.3.31 | partial → partial | special | vertexFiberMap_isQCatEquivalence_of_precompositionEquivalence は同じ底上のleft fibrationで、比較fに前合成同値も仮定する場合の同じfiberMapの圏同値性。底のFが恒等である範囲とこの追加仮定に限る。 |
| 4.5.3.34 | partial → partial | stronger-hyp | 指定した相対pathの0端点評価の自明Kan性も仮定すると、spanPullbackMapについてIsPrecompositionEquivalenceを直接得る。pullbackの準圏性の下では同じ射の圏同値となる。原文のisofibrationだけから追加仮定を解消していない。 |
| 4.5.3.35 | partial → partial | stronger-hyp | relativeFunctorPre/OverPreの二宣言はUがleft fibrationで、fがIsPrecompositionEquivalenceの場合に同じ底上の制限射の圏同値性を直接返す。isofibrationだけ・π₀での原文のcategorical equivalenceだけの場合は含まない。 |
| 4.5.3.36 | partial → none |  | relativeFunctorPost は底B上の関手空間の後合成で、原文のA上を固定するFun_{A/}(B,C)とは別の空間。境界制限を保つ比較が必要。 |
| 4.5.4.1 | partial → partial | stronger-hyp | IsPrecompositionEquivalenceは全試験準圏で前合成が圏同値という強い条件。そのcoreの同値をπ₀に送れば原文の同型類の全単射条件を直接満たすが、逆の比較は含まない。 |
| 4.5.4.4 | partial → partial | stronger-hyp | IsPrecompositionEquivalence.isWeakHomotopyEquivalence は同じfの弱ホモトピー同値性を直接返す。原文の試験準圏でのπ₀全単射より強い前合成の圏同値を仮定した場合だけ。 |
| 4.5.4.8 | partial → partial | direction | IsPrecompositionEquivalenceは原文(3)。各前合成の圏同値をcoreに送りπ₀を取ると(3)⇒(1)の向きを直接得る。原文のπ₀条件からの逆向きは含まない。 |
| 4.5.4.10 | partial → none |  | 引用は自然変換の成分t.app(∐objs)の前合成同値性。原文の任意の族f_iの余積射とはそのまま同じ射でなく、関手の余極限比較の同定がさらに要る。 |
| 4.5.4.11 | partial → partial | stronger-hyp | isQCatEquivalence_of_trivialKanFibration は始域・終域も準圏の場合に同じpの圏同値性を直接返す。一般の単体集合上の自明Kan射の主張は含まない。 |
| 4.5.4.13 | partial → none |  | 引用は端点への射影の自明Kan性とその圏同値性。原文の反対方向のδと恒等辺の切断式・二対三則を組み合わせる議論が型の結論にないため、別の射だけではpartialとしない。 |
| 4.5.5.1 | partial → none |  | isPullback_pre_of_isPushout は内部Homの厳密pullback性。原文の全試験準圏のcoreでのホモトピーpullback性の述語や、その比較を直接与えない。 |
| 4.5.5.4 | partial → none |  | 通常pushoutを内部Homが通常pullbackに送る部品。任意の正方形のcategorical pushoutとcategorical pullbackのいずれの含意も型の結論ではない。 |
| 4.5.5.5 | partial → none |  | 引用は底上のrelativeFunctorOverPreの厳密pullbackで、原文の境界を固定したFun_{A/}の圏同値とは対象・射・結論が異なる。 |
| 4.5.5.6 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：厳密 pushout の特例・単射・アノダイン・双対と通常圏を照合。反対単体集合で categorical pushout 性が同値。op の IsPushout 保存だけではホモトピーの述語を移さない。 |
| 4.5.5.7 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：厳密 pushout の特例・単射・アノダイン・双対と通常圏を照合。categorical pushout の転置不変性。厳密な IsPushout.flip は別の普遍性。 |
| 4.5.5.8 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：厳密 pushout の特例・単射・アノダイン・双対と通常圏を照合。左の categorical pushout を仮定した横貼り合わせの消去則。厳密な押し出しの貼り合わせでは不足。 |
| 4.5.5.9 | partial → partial | special | isPrecompositionEquivalence_of_pushout_gluing は両面が厳密pushoutで指定脚がMono、三成分がIsPrecompositionEquivalenceの場合に、同じ第4成分dの前合成同値性を直接返す。一般のcategorical pushoutの三条件全部は含まない。 |
| 4.5.5.10 | partial → partial | stronger-hyp | IsPrecompositionEquivalence.of_isPushout と of_isPushout_of_mono_other は四角が厳密pushoutで一方の脚がMonoの場合に、同じf′の前合成同値性を直接返す。原文の任意の四角のiffやπ₀だけの仮定は含まない。 |
| 4.5.5.11 | partial → none |  | 内部Homの厳密pullback性だけは、原文の任意の比較ρがcategorical equivalenceであることとcategorical pushout性とのiffを直接述べない。 |
| 4.5.5.15 | partial → partial | stronger-hyp | pushoutObjObj はiにIsPrecompositionEquivalenceを仮定する場合の同じpushout-productの結論を直接返す。i′側からの引用はi′にもMonoを追加する。π₀だけの原文のcategorical equivalenceとの逆比較は含まない。 |
| 4.5.6.3 | partial → partial | stronger-hyp | exists_kanPrism_extension_of_precompositionEquivalence はiに強い前合成同値を仮定すると同じ二端点とA上の制限を持つ延長の存在を直接返す。可逆なu₀なら全延長が可逆という後半は含まない。 |
| 4.5.6.4 | partial → partial | stronger-hyp | EquivalenceLiftingの定義は単射かつIsPrecompositionEquivalenceのiに対するHasLiftingPropertyそのもの。isofibrationとの二条件のiffを通じて原文の持ち上げ条件を直接得るが、π₀だけの仮定や逆向きは含まない。 |
| 4.5.6.16 | partial → partial | stronger-hyp | kanEquivalenceLifting_relativeFunctorOverPre_of_cocartesian はqをcocartesian fibrationに強めた場合の、同じ底上の制限射のEquivalenceLiftingを直接返す。一般isofibrationでは相対内部Homのfiberとの同定が必要。 |
| 4.5.6.18 | partial → partial | special | trivialKanFibration_relative_pre はqが単射jによる前合成射である場合の同じ相対指数比較の自明Kan性を直接返す。iにも原文より強いIsPrecompositionEquivalenceを仮定する。一般qは含まない。 |
| 4.5.6.20 | partial → partial | stronger-hyp | 準圏間で圏同値をIsQCatEquivalenceとして与えた場合、trivialKanFibration_of_kanEquivalenceLifting と逆の自明Kan射の同値性が同じqの二方向を返す。任意単体集合の原文のπ₀による定義の範囲は含まない。 |
| 4.5.7.1 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：一次元・通常圏・各段の比較・点wise の同値を照合。自然変換の全成分が圏同値という SSet 値図式の述語。equivalenceDiagrams は特定の関手の比較。 |
| 4.5.7.3 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：一次元・通常圏・各段の比較・点wise の同値を照合。単射かつ点ごとの圏同値に対する図式全体の延長条件。Reedy の Kan ファイブレーション版は別の弱同値。 |
| 4.5.7.6 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：一次元・通常圏・各段の比較・点wise の同値を照合。整礎半順序上の図式の matching map の isofibration 判定。Reedy モデルの matching fibration はモデル圏構造に依存。 |
| 4.5.7.10 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：一次元・通常圏・各段の比較・点wise の同値を照合。Kan 複体の弱余骨格の塔の isofibrant 性と通常の余骨格塔の反例。IsCoskeletal は単体集合一つの条件。 |
| 4.5.7.11 | partial → partial | special | Reedy Kan fibrantな余単体図式とReedy単射な重みの場合、fibrationは同じweightedSectionsPreのKan fibration性を直接返す。Kan空間のisofibrationという範囲に限り、一般のisofibrant図式とlevelwise categorical equivalence時の後半は含まない。 |
| 4.5.7.12 | none → partial | special | 添字圏をAsSmall ℕop、零段Kan・隣接遷移fibrationの塔に制限すると、weightedSections_tower_kanComplexは同じ豊穣HomのKan性を直接与え、従って準圏になる。任意の小圏上のisofibrant図式全体ではない。 |
| 4.5.7.13 | partial → partial | special | quasicategory_of_discrete_limit と quasicategory_of_inverseSequence_limit は離散図式および内ファイブレーションの可算逆列の厳密極限に同じ準圏性を直接返す。任意小圏のisofibrant図式は含まない。 |
| 4.5.7.14 | none → partial | special | 添字をAsSmall ℕopの塔、標的を零段Kan・隣接遷移fibrationに制限し、原文のlevelwise categorical equivalenceに加えて重みの各成分のanodyne性を仮定すると、同じweightedSectionsPreがtrivial Kan fibration（従って圏同値）。anodyneだけから原文のlevelwise圏同値を主張しない。 |
| 4.5.7.15 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：一次元・通常圏・各段の比較・点wise の同値を照合。isofibrant 図式の点ごとの圏同値に対する豊穣逆の構成。点ごとの通常の自然同型は強い仮定。 |
| 4.5.7.16 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：一次元・通常圏・各段の比較・点wise の同値を照合。標的の点ごとの圏同値に対する豊穣 Hom の後合成同値。標的図式の isofibrant 性で述べる型がない。 |
| 4.5.7.17 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：一次元・通常圏・各段の比較・点wise の同値を照合。isofibrant な二図式の点ごとの圏同値が極限の圏同値を誘導。Kan 型の特殊な図式の比較では仮定が異なる。 |
| 4.5.7.19 | partial → none |  | limit_kanComplex は厳密極限のKan性だけで、原文のshiftと対角を使う指定四角のcategorical pullback性を述べない。極限のKan性はその結論の成分ではない。 |
| 4.5.7.20 | partial → partial | special | weightedSectionsの三つのKan性の宣言はcospan・可算塔・Reedy fibrant余単体図式について原文と同じHom(E,F)のKan性を直接返す。重みや遷移射にも明記された仮定があり、任意小圏は含まない。 |
| 4.5.7.21 | partial → partial | special | limit_kanComplex はKan fibrationの可算塔で初項がKanのときの同じ厳密極限のKan性。任意小圏の図式の結論は含まない。 |
| 4.5.7.22 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：一次元・通常圏・各段の比較・点wise の同値を照合。isofibrant 図式で極限と core を交換する同型。relativized core の個別包含の定義だけでは極限を同定しない。 |
| 4.5.7.23 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：一次元・通常圏・各段の比較・点wise の同値を照合。isofibration の塔で core と逆極限を交換し可逆性を各段で判定。core の二脚の引き戻し補題は塔を扱わない。 |
| 4.5.7.24 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：一次元・通常圏・各段の比較・点wise の同値を照合。単体図式で面写像による matching object に対する isofibration 判定。通常の matching object の構成だけでは足りない。 |
| 4.5.8.10 | partial → none |  | fiberwiseHomProjection_innerFibration_iff は内ホーン上の延長と指数のinner性の特徴づけ。原文の任意の基底変換でcategorical equivalenceを保つという定義ではなく、別の判定を結ぶ比較が必要。 |
| 4.5.8.18 | partial → partial | component | fiberwiseHomPostcomp_innerFibration はUがcocartesianでVがEquivalenceLiftingの場合、同じ相対指数の後合成射のinner fibration性を直接返す。原文のisofibrationのinner性成分のみで、追加仮定と可逆辺持ち上げの不足がある。 |
| 4.5.8.19 | partial → partial | component | fiberwiseHomProjection_innerFibration_of_hornEquivalences は内ホーンの逆像射にIsPrecompositionEquivalenceも仮定すると、同じ指数射影のinner fibration性を直接返す。原文のisofibrationのこの成分だけで、exponentiableだけの仮定との比較は含まない。 |
| 4.6.1.16 | partial → none |  | 引用に現れるのは右pinchedHomMapの頂点fiberで、原文の区間模型のHom_C(X,Y)上の指定辺のfiberとの比較がない。定義の対象と相対写像の同一視が必要。 |
| 4.6.1.21 | partial → none |  | 右pinched模型の指定fiberのKan性で、原文の区間模型のfiberのKan性ではない。両模型の弱同値だけでもKan性は移らず、特定fiberの同型などの比較が要る。 |
| 4.6.1.22 | partial → none |  | pinchedHomMapのホーン持ち上げは別模型の射の性質。原文の区間模型のHomへの誘導射と厳密に比較する宣言を欠く。 |
| 4.6.1.24 | partial → partial | special | kanComplex_preFiber_of_vertexSurjective は底Dが終対象の場合の同じ、全頂点を含むAからの制限の指定fiberのKan性を直接返す。右pinched模型の候補は区間模型との比較がなく数えない。一般の相対底は含まない。 |
| 4.6.2.1 | partial → partial | component | joinCylinderMap は原文の順序の切断による同じcollapseの写像を直接構成する。指定両端だけからの一意性は引用型に含まない。 |
| 4.6.2.2 | partial → none |  | fatJoinComparisonの前合成同値性は関連する比較射の命題。原文の指定四角がcoreのホモトピーpullbackを与えることへの判定の比較がさらに必要で、同値な言い換えという説明だけではpartialにしない。 |
| 4.6.2.14 | partial → none |  | fatJoinComparisonは原文の相対pushoutからB◇Δ⁰へのθとは異なる射。通常joinとの比較の前合成同値性だけはθの同値性の直接の一部ではない。 |
| 4.6.3.1 | partial → partial | special | 可逆区間JによるB×Jの円柱に限ると、二つのEquivalenceCylinderFunctorIsoの型は同じ二端点を持つ延長とFunctorIsoを双方向に直接結ぶ。任意の分解B̄での三条件全部は含まない。 |
| 4.6.3.3 | partial → partial | component | relativeEquivalenceCylinderの二端点はA上で一致し、同じ射影への切断であることをendpoint_fixed/projectionが直接返す。B∐_A Bからの合わせた射のMono性と一般の円柱を束ねる型は含まない。 |
| 4.6.3.7 | partial → partial | stronger-hyp | exists_relativeCylinder_extension は元の二図式を結ぶ点ごとに可逆な実際の区間ホモトピーも入力すると、指定の単射円柱への同じ延長を直接返す。FunctorIsoだけからこの入力を作る方向と逆方向は含まない。 |
| 4.6.3.8 | partial → partial | special | S=Δ⁰、A=∅、B̄=B×Jの可逆区間円柱に限ると、二つのEquivalenceCylinderFunctorIsoの型が同じ延長とFunctorIsoを双方向に結ぶ。一般のisofibration上の相対版は含まない。 |
| 4.6.3.9 | partial → partial | stronger-hyp | exists_relativeCylinder_extension はA上で固定され点ごとに可逆な区間ホモトピーを追加入力すると、原文(3)の任意の単射円柱への同じ延長を直接返す。相対関手空間での同型だけからの入力の比較と逆方向は含まない。 |
| 4.6.3.10 | partial → partial | special | 底Sを終対象にし、A上固定で点ごとに可逆な区間ホモトピーも与える場合、exists_relativeCylinder_extension は指定円柱への同じ延長を返す。一般の相対底の持ち上げとiffは含まない。 |
| 4.6.3.11 | partial → partial | stronger-hyp | exists_relativeCylinder_extension はA上で固定され点ごとに可逆な区間ホモトピーを追加入力すると、指定円柱への同じ延長を直接返す。相対関手空間での同型との比較・逆向きは含まない。 |
| 4.6.4.2 | partial → none |  | arrowEndpointPairのisofibration性は引き戻す前の射の性質。原文のlax pullbackの特定の射影θとの基底変換の同定が必要。 |
| 4.6.4.13 | partial → partial | component | pointedConeProjectionをK=Δ⁰に取りjoinStdSimplexIso 0 0でΔ¹に移すと、原文の始点Xを固定した向き付き積の同じ射影のleft fibration性を直接得る。終点固定のright側は含まない。 |
| 4.6.4.14 | partial → none |  | 通常joinによるslice/coslice射影は原文の向き付き積の射影と別模型。sliceLaxMapの圏同値性だけではその射のleft/right fibration性は移らず、厳密な比較が必要。 |
| 4.6.4.21 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：片側を点とする場合・同値および厳密基底変換・左右と Kan ファイバーを照合。同値 G で基底図式を押し出した slice と coslice の双方の同値。図式制限や両者の op 比較は G による変換を扱わない。 |
| 4.6.4.22 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：片側を点とする場合・同値および厳密基底変換・左右と Kan ファイバーを照合。categorical pullback を図式に沿う slice に移す比較四角。点上の pullback や pinched Hom の四角では slice 全体に及ばない。 |
| 4.6.4.23 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：片側を点とする場合・同値および厳密基底変換・左右と Kan ファイバーを照合。右ファイブレーションのファイバーと K の連結度から slice 射の連結度を見積もる型。右ファイブレーションの基底変換には n と k の次数がない。 |
| 4.6.4.24 | partial → partial | special | sliceOverPostcomp_trivialKanFibration_of_rightFibration はK=Δ⁰の同じ射U_/Fの自明Kan性を直接返す。この図式は全次数で連結で、任意の指定のfiber切断次数に依存しない。一般Kは含まない。 |
| 4.6.6.1 | partial → partial | special | 片方の図式が空の場合、sliceOverまたはsliceUnderが原文の両側sliceの一側だけを固定した構成を直接与える。二つの非空図式を同時に固定するtilde fと反復構成全体は含まない。 |
| 4.6.6.4 | partial → partial | special | sliceConeFamilyMapはK₋=∅、K=Δ⁰のとき、原文の同じsliceからcone familyへの評価比較を直接構成する。両側の一般図式と一般Kは含まない。 |
| 4.6.6.5 | partial → partial | special | sliceConeFamilyMapとcosliceCoconeFamilyMapの圏同値性は、それぞれ片側の図式が空、K=Δ⁰の場合の同じ比較射の結論。一般の両側slice・任意Kは含まない。 |
| 4.6.6.7 | partial → partial | special | isQCatEquivalence_sliceConeFamilyMap はK=Δ⁰で同じslice→cone familyの比較が圏同値となる結論を直接返す。任意Kの関手空間版は含まない。 |
| 4.6.6.9 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：片側が空・点・両側の拡張・関手圏の点の版を照合。mixed slice に対する A⊂B の延長比較の持ち上げ性。片側の restriction の型には二端の固定がない。 |
| 4.6.6.10 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：片側が空・点・両側の拡張・関手圏の点の版を照合。join で作る slice/coslice から Fun(K,C) の点上の slice/coslice への両比較。join と over の定義があってもこの比較射を扱う型がない。 |
| 4.6.7.1 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：一つの豊穣 Hom・二対象・局所 Kan の特例・次数を固定した解像を照合。二対象 x,y の simplicial category E[K] の一方向 Hom が K で逆向きは空。enriched pair object は積でこの自由構成ではない。 |
| 4.6.7.3 | partial → none |  | coherentHomComparison は右pinched写像空間への比較で、原文は左pinchedへの特定のθ。Pathの包含順の規約も異なり、指定射の比較がない。 |
| 4.6.7.5 | partial → none |  | 右pinchedのcoherentHomComparisonのホモトピー同値性であり、原文の左pinchedの指定θの同値性ではない。対象だけでなく比較射を同定する宣言が必要。 |
| 4.6.7.8 | partial → none |  | 右pinched/旗の解像についての型で、原文の左pinchedの指定θまたはPath[ΣK]の特定のΦ・ρとの同定がない。Hom が Kan 複体の場合（Thm 4.6.7.5）だけ。Hom が ∞ 圏のときの同値は未。 |
| 4.6.7.9 | partial → none |  | 右pinched/旗の解像についての型で、原文の左pinchedの指定θまたはPath[ΣK]の特定のΦ・ρとの同定がない。右 pinched で直接作っているので op 経由の主張はない。Kan の場合だけ。 |
| 4.6.7.10 | partial → none |  | 右pinched/旗の解像についての型で、原文の左pinchedの指定θまたはPath[ΣK]の特定のΦ・ρとの同定がない。仮定：任意の単体集合 K（Kerodon と一致）。結論：coherentResolution は標準単体上の旗から拡張した関手（Lean が弱い：Path[ΣK] の指定二点間の Hom と同定する型がない）。 |
| 4.6.7.15 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：一つの豊穣 Hom・二対象・局所 Kan の特例・次数を固定した解像を照合。E[K] からの対象固定 enriched functor と K から Hom(X,Y) への射の全単射。通常 nerve の完全忠実性はこの対応の型ではない。 |
| 4.6.7.16 | partial → none |  | 右pinched/旗の解像についての型で、原文の左pinchedの指定θまたはPath[ΣK]の特定のΦ・ρとの同定がない。仮定：任意の単体集合 K、単体豊穣圏 C と対象 X,Y（Kerodon と一致）。結論：右 pinched の R(Hom_C(X,Y)) との同型と Φ⊣R が Hom 全単射を与える（Lean が弱い：原文の左 pinched 版との同定を欠く）。 |
| 4.6.7.18 | partial → none |  | 右pinched/旗の解像についての型で、原文の左pinchedの指定θまたはPath[ΣK]の特定のΦ・ρとの同定がない。E[B] の構成がないので、随伴 Φ ⊣ R だけ。 |
| 4.6.7.19 | partial → none |  | 右pinched/旗の解像についての型で、原文の左pinchedの指定θまたはPath[ΣK]の特定のΦ・ρとの同定がない。右随伴は抽象的に定義していて、Hom^L_{N(E[B])}(x,y) との同一視はない。 |
| 4.6.7.21 | partial → none |  | 右pinched/旗の解像についての型で、原文の左pinchedの指定θまたはPath[ΣK]の特定のΦ・ρとの同定がない。仮定：任意の単体集合の図式（Kerodon と一致）。結論：旗で定めた coherentResolution が余極限を保存（Lean が弱い：原文の Path[ΣK] の Φ との同定は未確認）。 |
| 4.6.7.22 | partial → none |  | 右pinched/旗の解像についての型で、原文の左pinchedの指定θまたはPath[ΣK]の特定のΦ・ρとの同定がない。仮定：任意の単体集合 K（Kerodon と一致）。結論：coherentResolutionProjectionAll は旗の解像から K への自然変換（Lean が弱い：原文の E[K] の左 pinched 比較を転置した射との一致は型にない）。 |
| 4.6.7.23 | partial → none |  | 右pinched/旗の解像についての型で、原文の左pinchedの指定θまたはPath[ΣK]の特定のΦ・ρとの同定がない。仮定：任意の単体集合 K（Kerodon と一致）。結論：coherentResolutionProjectionAll.app K は前合成同値（Lean が弱い：原文の指定 ρ_K と同じ射であることを引用先から確認できない）。 |
| 4.6.7.24 | partial → none |  | 右pinched/旗の解像についての型で、原文の左pinchedの指定θまたはPath[ΣK]の特定のΦ・ρとの同定がない。仮定：K→K′ が前合成同値（Lean が強い：原文の π₀ 条件との橋渡しが引用にない）。結論：旗の解像による像は前合成同値（Lean が弱い：Path[Σ−] の関手との比較を欠く）。 |
| 4.6.7.25 | partial → none |  | 右pinched/旗の解像についての型で、原文の左pinchedの指定θまたはPath[ΣK]の特定のΦ・ρとの同定がない。仮定：単体豊穣圏 C の Hom_C(X,Y) が ∞ 圏（Kerodon と一致）。結論：右随伴 R の値が ∞ 圏であり、右 pinched と同型（Lean が弱い：原文の左 pinched の模型との比較を欠く）。 |
| 4.6.7.26 | partial → none |  | 右pinched/旗の解像についての型で、原文の左pinchedの指定θまたはPath[ΣK]の特定のΦ・ρとの同定がない。仮定：単体集合 K の解像に沿う豊穣比較。型は解像側の指定ホモトピーを仮定。結論：指定ホモトピーを随伴で移す方向がある。原文の一つの豊穣 Hom の準圏性で二つの像の同型を比較する iff は未確認。 |
| 4.6.7.27 | partial → none |  | 右pinched/旗の解像についての型で、原文の左pinchedの指定θまたはPath[ΣK]の特定のΦ・ρとの同定がない。仮定：m,n が非負整数（Kerodon と一致）。結論：CoherentResolutionFlag n m は最小元から始まる増大旗（Lean が弱い：ΣΔⁿ の非退化単体と両端固定の減少旗による原文の集合との全単射が型にない）。 |
| 4.6.7.28 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：一つの豊穣 Hom・二対象・局所 Kan の特例・次数を固定した解像を照合。部分集合鎖で定める Φ(Δⁿ)×Δ¹→Φ(Δⁿ⁺¹) の指定写像。rigidification の頂点鎖・necklace はこの二変数射を定めない。 |
| 4.6.7.29 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：一つの豊穣 Hom・二対象・局所 Kan の特例・次数を固定した解像を照合。指定された Φ(Δⁿ)×Δ¹→Φ(Δⁿ⁺¹) の性質。通常の Δ¹ cylinder 比較には部分集合鎖モデル Φ の端点条件がない。 |
| 4.6.8.1 | partial → partial | special | intervalMappingSpaceは頂点列が二つ、n=1の場合の原文と同じ区間関手空間の両端固定fiberを直接構成する。任意長の列は含まない。 |
| 4.6.8.4 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：二端・1 圏・dg の特例・片方向の比較と基底変換・ホモトピー圏に降りる形を照合。内ファイブレーションが誘導する有限頂点列 Hom の Kan ファイブレーション。二点間の pinched Hom の比較だけでは任意列を固定できない。 |
| 4.6.8.5 | partial → none |  | compositionCorrespondenceFirstは第二辺gを固定したfiberからの射。原文の二つのHomがともに変動する積への制限射と異なり、全空間のRLPを直接返さない。 |
| 4.6.8.8 | partial → none |  | compositionCorrespondenceは第二辺を固定した別のfiber。原文の三頂点だけを固定したHom(X₀,X₁,X₂)全体のKan性と同一視する宣言がない。 |
| 4.6.8.9 | partial → none |  | compositionCorrespondenceとKanMappingCompositionは特定の辺・三角形を固定した対応。原文の二つの写像空間の積からhKanでの合成射を構成する型ではない。 |
| 4.6.8.11 | partial → none |  | dg nerveの右pinchedのAW合成の単位則で、原文の区間模型のhKan合成と同定されていない。対象・合成の比較なしに類似の律だけをspecialにしない。 |
| 4.6.8.12 | partial → none |  | dg nerveの右pinchedのAW合成の結合則で、原文の区間模型のhKan合成と同定されていない。 |
| 4.6.8.13 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：二端・1 圏・dg の特例・片方向の比較と基底変換・ホモトピー圏に降りる形を照合。hKan の直積モノイダル構造上の enrichment としての hC。通常の HomotopyCategory は Hom 集合に π₀ を取る。 |
| 4.6.8.15 | partial → none |  | 固定辺のcompositionCorrespondenceの構成だけは、原文のhKanの前後合成の射とそのホモトピー類だけへの依存を結論しない。 |
| 4.6.8.16 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：二端・1 圏・dg の特例・片方向の比較と基底変換・ホモトピー圏に降りる形を照合。f による合成と二種 Hom の比較が作る四角のホモトピー可換性。成分上の合成や単一の比較同値にはその四角がない。 |
| 4.6.8.18 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：二端・1 圏・dg の特例・片方向の比較と基底変換・ホモトピー圏に降りる形を照合。coslice の Hom と合成写像の指定値でのホモトピーファイバーの比較。coslice 全体の制限は f,g を固定した空間を計算しない。 |
| 4.6.8.19 | partial → none |  | coherentCompositionCorrespondenceは射を一つ固定した対応への写像。原文の両因子が変動する積とhKan合成の可換正方形を直接返さず、canonicalなθの規約の比較も要る。 |
| 4.6.8.20 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：二端・1 圏・dg の特例・片方向の比較と基底変換・ホモトピー圏に降りる形を照合。locally Kan enriched category と hc nerve の Hom 比較が合成と両立。hC の通常圏同型だけでは空間レベルの合成を扱わない。 |
| 4.6.8.21 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：二端・1 圏・dg の特例・片方向の比較と基底変換・ホモトピー圏に降りる形を照合。dg Hom のテンソル合成と dg nerve の写像空間合成のホモトピー可換性。Dold–Kan の比較や dg nerve の定義だけでは合成四角を与えない。 |
| 4.7.1.1 | partial → partial | special | n=−2では全ての入射Homの境界充填による可縮性を要求する。terminalとpinchedHom可縮性のiffを、区間比較の圏同値と可縮Kan性の保存/反映で移せば、同じ入射intervalMappingSpaceの可縮性という条件を直接得る。任意nと離散空間の一般の述語は含まない。 |
| 4.7.1.4 | partial → partial | special | isInitialVertex_iff_intervalMappingSpace_isContractibleKan はn=−2で原文の全ての出射Homの可縮Kan性の条件を直接表す。任意の整数nのcotruncated条件は含まない。 |
| 4.7.1.16 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：n＝-2 の端対象・空間の 0 切断・双対・境界を照合。n+3 以上の単体に対する指定端点付き境界条件と対象 n-truncation の同値。coskeleton の一意延長は指定端点の存在条件ではない。 |
| 4.7.2.1 | partial → none |  | 通常圏のMonoはHom集合の合成単射性。原文のnerveの区間写像空間への合成作用と(n=−1の)truncationの比較を欠く。 |
| 4.7.2.7 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：n＝-2 の同値・n＝-1 の単射・通常圏の mono の合成・取消し・ファイバー・左右ホーンを照合。射 f の n-truncation と slice の対象としての n-truncation の同値。slice の構成と制限の型だけではこの二つの述語を結ばない。 |
| 4.7.2.8 | partial → none |  | 可逆辺の保存/反映の型は、原文の各写像空間への合成作用のn-truncationの保存/反映ではない。n=−2への特殊化にもこの特徴づけとの比較が必要。 |
| 4.7.2.9 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：n＝-2 の同値・n＝-1 の単射・通常圏の mono の合成・取消し・ファイバー・左右ホーンを照合。右ファイブレーションに沿う truncated 射の保存と反映。右ファイブレーションの pullback 安定性は射の切断度を比較しない。 |
| 4.7.2.10 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：n＝-2 の同値・n＝-1 の単射・通常圏の mono の合成・取消し・ファイバー・左右ホーンを照合。指定外ホーンに沿う持ち上げと f の n-truncation の同値。右ファイブレーションはすべての右ホーンに対する別の性質。 |
| 4.7.2.11 | partial → none |  | 通常圏の終対象へのmonoからsubterminalという定理であり、原文のnerveの写像空間での切断条件との同定がない。 |
| 4.7.2.12 | partial → none |  | 通常圏でのmonoとsubterminalの片側で、原文のn-truncated対象・射の定義への比較がない。 |
| 4.7.2.14 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：n＝-2 の同値・n＝-1 の単射・通常圏の mono の合成・取消し・ファイバー・左右ホーンを照合。2-単体における n-truncated な射の合成と取消し。Mono の同型・合成や内ホーン充填は任意次数の取消しを述べない。 |
| 4.7.3.6 | partial → none |  | coherentHomComparisonは包含順nerveの右pinchedへの射。原文の逆包含coherent nerveでの指定対象と豊穣Homへの同定を欠き、terminal判定と組み合わせる前にこの比較が要る。 |
| 4.7.3.8 | partial → none |  | dgNerve_contractingElement_isTerminalVertexはHA余鎖符号のdg nerveについての型。原文のdg nerveの符号規約に移す比較がなく、同じ対象の(3)⇒(2)とは確認できない。 |
| 4.7.3.13 | partial → partial | direction | IsContractibleKan.isTerminalVertex/isInitialVertexは、原文(3)の可縮Kan複体の任意の頂点について(1),(2)を直接返す。initial/finalから可縮性へ戻す方向は含まない。 |
| 4.7.3.15 | partial → none |  | 通常圏の選ばれたinitial/terminalとその記法で、原文の準圏の頂点と一意な可縮選択空間の記法への比較がない。 |
| 4.7.3.16 | partial → partial | direction | isTerminalVertex_iff_of_vertexIsoは、Xが終対象でYがXに同型ならYも終対象という原文の向きを直接返す。二つの終対象から頂点同型を作る逆方向は含まない。 |
| 4.7.3.19 | partial → partial | component | IsTerminalVertex.exists_sliceLiftはK→C_/Xという錐を直接与え、sliceのjoin転置で同じ図式f上のcosliceの頂点となり頂点Xへの射影を保つ。原文(1)の存在成分のみで、その頂点のcosliceでの終対象性は含まない。 |
| 4.7.3.20 | partial → partial | special | cosliceIdentityCone_isInitialVertexはf=id_Xの場合、同じcosliceの恒等錐が始対象という原文(1)⇒(3)の特殊形を直接返す。任意の同型fと他の同値条件は含まない。 |
| 4.7.3.21 | partial → partial | direction | exists_fixed_slice_sectionは終対象から同じprojectionの切断でXをid_Xに送るものの存在を直接返す。(1)の順方向だけで、逆向きとinitial側は含まない。 |
| 4.7.3.22 | partial → partial | direction | terminalPoint_rightAnodyneは終対象Xからその一点包含がright anodyneという原文(1)⇒(3)を直接返す。錐上のFの構成と逆方向は含まない。 |
| 4.7.4.1 | partial → none |  | IsSubterminalは通常圏のHom集合の高々一元性。原文のnerveの区間写像空間が空または可縮という条件への比較がない。 |
| 4.7.4.8 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：空間の 0 切断・離散化・通常圏の subterminal・heart の代わりに hC と nerveを照合。slice 射がその像の充満部分圏上で自明 Kan ファイブレーションとなる subterminal の判定。slice の右ファイブレーション性だけでは弱い。 |
| 4.7.4.9 | partial → none |  | 通常圏のSubterminalsとMonoOverの圏同値・Subobjectの順序であり、原文の準圏のsubterminal性からの同型類と2単体による順序との同定がない。 |
| 4.7.4.11 | partial → none |  | 通常圏の薄さとThinSkeletonとの圏同値だけは、原文の指定の[X]への射の自明Kan性を返さない。 |
| 4.7.4.12 | partial → none |  | ThinSkeletonとの通常圏の圏同値はあるが、原文の写像空間のsubterminal条件とnerve上の準圏同値とを直接結ぶ型がない。 |
| 4.7.4.13 | partial → none |  | Is0TruncatedSpaceは空間の∞圏で離散模型と同値という述語。原文の任意のCからの写像空間の成分の可縮性を直接述べない。 |
| 4.7.4.21 | partial → none |  | discreteSpaceInclusionは選んだ離散模型の像。原文の全てのdiscrete objectsの充満部分圏との同定がなく、任意の圏のheartの構成ではない。 |
| 4.7.4.22 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：空間の 0 切断・離散化・通常圏の subterminal・heart の代わりに hC と nerveを照合。heart からそのホモトピー圏の nerve への自明 Kan ファイブレーション。一般の homotopy category 比較には discrete 対象への制限がない。 |
| 4.7.4.23 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：空間の 0 切断・離散化・通常圏の subterminal・heart の代わりに hC と nerveを照合。通常圏の nerve と同値であることと全対象の discrete 性などの同値。nerve が ∞ 圏という一方向とは異なる。 |
| 4.7.5.1 | partial → none |  | 通常圏のMonoのHom集合の単射性は、nerveの写像空間への合成が直和因子へのホモトピー同値という結論に移す比較を要する。 |
| 4.7.5.2 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：通常圏の mono/epi と subobject・同値・充満忠実の特例・左右反転と sliceを照合。∞ 圏の mono を鉤付き矢印で記す規約。通常圏の Mono はこの表記を導入しない。 |
| 4.7.5.3 | partial → none |  | 通常圏のEpiのHom集合の単射性は、nerveの写像空間への前合成が直和因子へのホモトピー同値という原文の条件への比較を要する。 |
| 4.7.5.19 | partial → none |  | MonoOverは通常圏のmonoの充満部分圏。原文の準圏のslice内のsubterminal性との同定がない。 |
| 4.7.5.20 | partial → none |  | 通常圏のMonoOverのThinSkeletonと順序。原文の準圏のsliceのsubterminal objectsの商と2単体での順序の同定がない。 |
| 4.7.6.1 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：n＝0/1 の通常圏・groupoid・空間の切断と cosk・普遍性の片方向を照合。各 X,Y の Hom(X,Y) の n-truncation としての局所 n-truncation。単体集合自体の coskeletal 性を述べる型と区別した。 |
| 4.7.6.9 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：n＝0/1 の通常圏・groupoid・空間の切断と cosk・普遍性の片方向を照合。dg nerve の局所 n-truncation と dg Hom のホモロジー消滅の同値。dg Hom の複体と nerve の定義には消滅の次数比較がない。 |
| 4.7.6.13 | partial → none |  | nerveAdjunctionは普通のHomの随伴全単射で、原文の任意Fのlocal n-truncationを判定する関手∞圏の同値と局所切断条件を直接与えない。 |
| 4.7.6.15 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：n＝0/1 の通常圏・groupoid・空間の切断と cosk・普遍性の片方向を照合。C の局所 (n−2)-truncation と coskₙ 比較の条件の同値。coskeleton adjunction 自体は写像空間の次数を判定しない。 |
| 4.7.6.16 | partial → none |  | cosk₂Isoは通常圏のnerveの2-coskeletal性を表す同型。原文の結論の局所(n−2)-truncationを型に持たず、n=2の特殊形でも写像空間の比較が要る。 |
| 4.7.6.17 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：n＝0/1 の通常圏・groupoid・空間の切断と cosk・普遍性の片方向を照合。coskₙ(C) 自身の局所 (n−2)-truncation と ∞ 圏性。truncated simplicial set からの右随伴の型は両性質を主張しない。 |
| 4.7.6.18 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：n＝0/1 の通常圏・groupoid・空間の切断と cosk・普遍性の片方向を照合。局所 (n−2)-truncation と C→coskₙ(C) の圏同値の判定。coskeleton 反射の同型判定は圏同値より強い別条件。 |
| 4.7.6.19 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：n＝0/1 の通常圏・groupoid・空間の切断と cosk・普遍性の片方向を照合。C→coskₙ(C) が局所 (n−2)-truncation を表示する普遍性。骨格との随伴では標的が局所 truncated な ∞ 圏とは限らない。 |
| 4.7.6.20 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：n＝0/1 の通常圏・groupoid・空間の切断と cosk・普遍性の片方向を照合。hQCat 上で局所 n-truncated な対象への反射。通常の hC や coskeleton の随伴の圏が異なる。 |
| 4.7.6.22 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：n＝0/1 の通常圏・groupoid・空間の切断と cosk・普遍性の片方向を照合。Kan 複体を始域とする局所 n-truncation と空間の truncation の比較。C の Kan 性だけを運ぶ比較は局所普遍性を与えない。 |
| 4.7.6.24 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：n＝0/1 の通常圏・groupoid・空間の切断と cosk・普遍性の片方向を照合。局所 n-truncation が各 Hom 上で誘導する n-truncation。pinched Hom の比較同値は次数付き切断射ではない。 |
| 4.7.6.25 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：n＝0/1 の通常圏・groupoid・空間の切断と cosk・普遍性の片方向を照合。各 f における Hom の πₙ が一元となる局所 truncation 判定。Kan 複体の連結度や π 群単体の補題だけでは全 f を結ばない。 |
| 4.7.7.1 | partial → none |  | StrictSegalはspineからの一意延長で、原文の内ホーンの存在・高次一意性とは異なる条件。nerveの場合にもホーンとの比較が必要。 |
| 4.7.7.8 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：n＝1 の nerve と n＝0 の薄い圏・Kan の特例と次数付き骨格・閉性の一部を照合。正次数 n-category と weak n-coskeletal かつ次元 n で minimal の同値。一般の minimal モデルの型には次元の制限がない。 |
| 4.7.7.9 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：n＝1 の nerve と n＝0 の薄い圏・Kan の特例と次数付き骨格・閉性の一部を照合。負次数も含め weak coskeleton と次数付き minimality で定める n-category。全次元の coskeletal や minimal で代用できない。 |
| 4.7.7.16 | partial → partial | component | thinNerve_hom_ext_hornは半順序Qのnerveで次数2以上の同じホーンに一致する二充填の等式を直接返す。この特殊形の高次充填の一意性成分のみで、0-category全体のiffは含まない。 |
| 4.7.7.20 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：n＝1 の nerve と n＝0 の薄い圏・Kan の特例と次数付き骨格・閉性の一部を照合。n-category の左右 pinched Hom が (n−1)-groupoid となる次数降下。左右比較同値や Kan 性だけには次数がない。 |
| 4.7.7.22 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：n＝1 の nerve と n＝0 の薄い圏・Kan の特例と次数付き骨格・閉性の一部を照合。n-category の Fun(K,C) による閉性。Fun(K,C) の ∞ 圏性を導く型には高次ホーンの一意性がない。 |
| 4.7.7.23 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：n＝1 の nerve と n＝0 の薄い圏・Kan の特例と次数付き骨格・閉性の一部を照合。oriented と homotopy fiber product の n-category 性。既存 pullback の ∞ 圏性からは次数 n を保持する型を得ない。 |
| 4.7.7.24 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：n＝1 の nerve と n＝0 の薄い圏・Kan の特例と次数付き骨格・閉性の一部を照合。slice と coslice の n-category 性。join から得る ∞ 圏性・ファイブレーション性には一意充填の次数がない。 |
| 4.7.8.1 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：Kan 最小性・0-reduced・通常の coskeleton と nerve・有限次数での比較を照合。非空条件を含む (n+1)-coskeletal の判定と n-category 性の関係。通常 coskeletal だけの型では負次数と weak 条件を扱わない。 |
| 4.7.8.2 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：Kan 最小性・0-reduced・通常の coskeleton と nerve・有限次数での比較を照合。minimal ∞ 圏で n-category と局所 (n−1)-truncation が同値。minimal Kan fibration の一意性には任意の ∞ 圏の局所次数がない。 |
| 4.7.8.3 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：Kan 最小性・0-reduced・通常の coskeleton と nerve・有限次数での比較を照合。局所 (n−1)-truncation と n-category に同値であることの同値。minimal モデルの比較だけでは n-category への次数評価がない。 |
| 4.7.8.4 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：Kan 最小性・0-reduced・通常の coskeleton と nerve・有限次数での比較を照合。weak (n−1)-coskeletal な ∞ 圏から n-category 性を得る含意。通常 coskeleton と内ホーンの一意充填の次数が異なる。 |
| 4.7.8.5 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：Kan 最小性・0-reduced・通常の coskeleton と nerve・有限次数での比較を照合。n-category の Hom が weak (n−1)-coskeletal となる結論。interval Hom の Kan 性だけでは weak coskeleton の次数を与えない。 |
| 4.7.8.6 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：Kan 最小性・0-reduced・通常の coskeleton と nerve・有限次数での比較を照合。m-単体から (m−1)-骨格への制限 θₘ による n-category 判定。sk/cosk の随伴には一意充填を反映するこの判定がない。 |
| 4.7.8.8 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：Kan 最小性・0-reduced・通常の coskeleton と nerve・有限次数での比較を照合。n-reduced の次数 ≤n での単体一意性の同値条件。Reduced は頂点一意の特別な場合。 |
| 4.7.8.9 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：Kan 最小性・0-reduced・通常の coskeleton と nerve・有限次数での比較を照合。minimal Kan で n-reduced と (n+1)-connective の同値。π による連結度の型に n 以下の単体の一意性はない。 |
| 4.7.8.10 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：Kan 最小性・0-reduced・通常の coskeleton と nerve・有限次数での比較を照合。weak coskₙ の ∞ 圏性と局所 truncation の表示。通常 coskₙ を取る右随伴とは対象も普遍性も異なる。 |
| 4.7.9.1 | partial → none |  | hoFunctorとnerveAdjunctionはcanonicalなホモトピー圏の普遍性。原文の任意のFのn-category性と全てのn-category標的についての条件を直接判定しない。 |
| 4.7.9.2 | partial → none |  | 随伴の単位はC→N(hC)の射を構成するが、n-categoryの型・原文の普遍性と同定されていないので、ホモトピーn-categoryの同じ構成の特殊形とは数えない。 |
| 4.7.9.7 | partial → none |  | 随伴は選んだunitの普通のHom全単射。原文の任意のFの前合成での集合全単射と関手∞圏の同型という二条件の含意を型に持たない。 |
| 4.7.9.8 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：n＝1 の普遍性・n＝0 の成分と n＝∞ の恒等・骨格・相対化の片側を照合。homotopy n-category の表示から局所 (n−1)-truncation の表示へ移す含意。通常 hC の Hom の定義にこの次数付き普遍性がない。 |
| 4.7.9.9 | partial → none |  | 原文は弱coskeletonの相対同型の商からの特定比較射。hoFunctorの別構成とそのunitはその商・射と比較されていない。 |
| 4.7.9.11 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：n＝1 の普遍性・n＝0 の成分と n＝∞ の恒等・骨格・相対化の片側を照合。skₙ(A) からの指定射に対する h≤n の比較写像の性質。通常の sk/cosk 随伴は h≤n の商との比較ではない。 |
| 4.7.9.13 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：n＝1 の普遍性・n＝0 の成分と n＝∞ の恒等・骨格・相対化の片側を照合。weak coskₙ から h≤n への比較射の単体ごとの性質。普通の coskeleton の unit と h≤n への商射は別の射。 |
| 4.7.9.14 | partial → none |  | strictSegalとhoFunctorは別構成のnerveについての結果。原文の弱coskeletonの指定商のn-category性を直接返さない。 |
| 4.7.9.15 | partial → none |  | nerveAdjunctionはcanonicalなunitの普遍性で、原文の弱coskeletonからの商への指定比較射と同定する宣言がない。 |
| 4.7.9.16 | partial → none |  | unitの存在だけは、原文のhomotopy n-categoryの普遍性・低次全単射・因子化・自明Kan性・局所切断・isofibrationのいずれも直接結論しない。 |
| 4.7.9.17 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：n＝1 の普遍性・n＝0 の成分と n＝∞ の恒等・骨格・相対化の片側を照合。dim B≤n+1 とそれ以下で区別される h≤n 比較の持ち上げ。一般の内アノダイン持ち上げに次元上限とこの比較射がない。 |
| 4.7.9.20 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：n＝1 の普遍性・n＝0 の成分と n＝∞ の恒等・骨格・相対化の片側を照合。n-category を底とする pullback と h≤n の比較四角。一般の simplicial pullback は切断を施した四角を保証しない。 |
| 4.7.9.21 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：n＝1 の普遍性・n＝0 の成分と n＝∞ の恒等・骨格・相対化の片側を照合。下辺が homotopy n-category を表示する pullback から得る h≤n の同型。通常の pullback の比較同型では表示条件が異なる。 |
| 4.7.9.22 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：n＝1 の普遍性・n＝0 の成分と n＝∞ の恒等・骨格・相対化の片側を照合。X 上の slice と homotopy n-category の比較射。slice の op や基底制限の構成に h≤n が現れない。 |
| 4.7.9.23 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：n＝1 の普遍性・n＝0 の成分と n＝∞ の恒等・骨格・相対化の片側を照合。(n−1)-truncated な X における slice の h≤n と h≤n の slice の比較。一般 slice 同値の型には対象の切断度がない。 |
| 4.8.0.4 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：通常圏の full・境界持ち上げの全次数を照合。isofibration に対する次数 n の境界持ち上げによる n-full。EquivalenceLifting の試験射は前合成同値な単射。 |
| 4.8.1.7 | partial → partial | component | IsEssentiallySurjective.compは原文の三つの結論のうち、本質的全射な二関手の合成も本質的全射という第一成分を同じ合成について直接返す。後二条件は含まない。 |
| 4.8.1.11 | partial → own |  | fullSubcomplexOnVerticesにP(y):=∃x,Nonempty(VertexIso(F(x),y))を代入すると、原文と同じ「像の対象に同型な全頂点で張る充満部分圏」を直接構成する。VertexIsoが対象の同型を表し、fullSubcomplexOnVertices_quasicategoryも現本体にある。専用のessImageという名前の欠如だけではpartialにしない。 |
| 4.8.2.1 | partial → none |  | Fullは通常圏のHom集合の全射性。原文のnerveの区間写像空間のπ₀との比較を引用型に含まず、単なる類似の定義だけは数えない。 |
| 4.8.2.7 | partial → partial | component | IsEssentiallySurjectiveは原文の0-fullの定義の頂点同型による存在条件そのもの。1-fullと高次n-fullの定義は含まない。 |
| 4.8.2.20 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：通常圏の full と合成・全次数の境界とファイバー・Kan の π₀・πₙを照合。Kan 複体の n-full と π₀ 又は πₙ の全射性の判定。ホモトピー群への誘導射にはこの n-full との同値がない。 |
| 4.8.2.22 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：通常圏の full と合成・全次数の境界とファイバー・Kan の π₀・πₙを照合。n≥1 の n-full 性と対象対ごとの Hom 射の次数を一つ下げた full 性。pinched Hom の同値は任意次数の判定ではない。 |
| 4.8.2.24 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：通常圏の full と合成・全次数の境界とファイバー・Kan の π₀・πₙを照合。内ファイブレーションの n-full と各像射の上の持ち上げ空間の連結度の同値。頂点上ファイバーの計算は射 u を固定しない。 |
| 4.8.2.25 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：通常圏の full と合成・全次数の境界とファイバー・Kan の π₀・πₙを照合。n-full 性を各ファイバーで判定する条件と基底変換の条件の同値。pullback の内ファイブレーション性だけでは判定を与えない。 |
| 4.8.2.26 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：通常圏の full と合成・全次数の境界とファイバー・Kan の π₀・πₙを照合。内ファイブレーション間の四角で、指定ファイバーの写像空間の条件から n-full 性を移す結論。単なる基底変換の型では対象が違う。 |
| 4.8.2.27 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：通常圏の full と合成・全次数の境界とファイバー・Kan の π₀・πₙを照合。categorical pullback による n-full の保存。通常圏の Full.pullback や厳密 pullback の ∞ 圏性では任意 n を扱わない。 |
| 4.8.2.28 | partial → none |  | Full.of_comp_faithfulは通常圏のFull/Faithfulの消去。原文のnerveの写像空間でのn-fullの条件への比較がなく、類似の通常圏命題だけでは数えない。 |
| 4.8.2.30 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：通常圏の full と合成・全次数の境界とファイバー・Kan の π₀・πₙを照合。前段の本質的全射性・full 性・(n−1)-full 性から合成の n-full 性を後段に移す結論。通常の full 合成は仮定も次数も異なる。 |
| 4.8.3.7 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：通常圏の faithful・充満忠実な場合・対角とファイバーを照合。内ファイブレーションで strict pullback を homotopy pullback に入れる包含の充満忠実性。strict pullback の射影に対する候補は比較射を変えている。 |
| 4.8.3.8 | partial → none |  | Faithfulは通常圏のHom集合の単射性。原文の写像空間の直和因子への同値との比較を欠く。 |
| 4.8.3.9 | partial → partial | direction | IsFullyFaithfulの各pinchedHomMapのホモトピー同値は、自然なpinched→interval比較の同値と可換式で同じinterval作用の同値へ移る。従ってπ₀全射と全標的を直和因子とする同値を直接得る。fully faithful⇒fullかつfaithfulの向きのみ。 |
| 4.8.3.12 | partial → partial | special | n=0の(n−2)-truncationは各Hom作用のホモトピー同値の条件。IsFullyFaithfulのpinchedHomMapを自然な区間比較で移すと同じinterval作用のこの条件を直接得る。任意の正のnの定義は含まない。 |
| 4.8.3.15 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：通常圏の faithful・充満忠実な場合・対角とファイバーを照合。負次数に拡張した n-faithful の規約。fully faithful の宣言は負次数を含む族ではない。 |
| 4.8.3.32 | partial → none |  | pinchedHomPullbackBaseMapは一つの比較射、追加の充満忠実性下での帰結もpinched模型。自然な区間比較の圏同値だけでは厳密pullback性やfibration性は移らず、原文の指定四角の比較が必要。 |
| 4.8.3.35 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：通常圏の faithful・充満忠実な場合・対角とファイバーを照合。n-faithful と対角の n に依存する条件の同値。fully faithful の境界持ち上げの型は対角と次数の関係を述べない。 |
| 4.8.3.36 | partial → partial | special | n=0でIsFullyFaithful.pullback_sndは同じinner fibrationの各底変換の充満忠実性を直接返す。pinched/interval比較は自然な同値なのでこの性質は原文の同じHom作用へ移る。一般nの四条件は含まない。 |
| 4.8.3.38 | partial → none |  | 区間上の端点fiberとcrossingの条件からの充満忠実性は、原文の全ての辺uへの引き戻しの同値条件とは異なる判定。h0/h1/hcを原文の仮定から回収する比較が要る。 |
| 4.8.3.39 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：通常圏の faithful・充満忠実な場合・対角とファイバーを照合。内ファイブレーションの四角でファイバー側の条件から n-faithful 性を移す結論。四角の通常の忠実性や厳密 pullback の型ではない。 |
| 4.8.4.1 | partial → partial | component | isQCatEquivalence_iff_fullyFaithful_essentiallySurjectiveは同じFの原文(1)⇔(2)を直接返す。pinchedとintervalの自然な比較によるHom作用の同値性も確認する。(3),(4)を含む四条件全体ではない。 |
| 4.8.4.4 | partial → none |  | fullSubcomplexVertexImageLiftは頂点のliteral imageが張る部分複体への射。原文の同型で閉じたessential imageとは対象が異なり、この射が同値という型だけでは同じ結論にならない。 |
| 4.8.4.5 | partial → partial | stronger-hyp | IsFullyFaithful.hasLiftingProperty_boundary_succはFを充満忠実なinner fibrationに強めると同じ∂Δⁿに対する持ち上げを全ての正のnで直接返す。一つのn-fullだけの仮定と逆向きは含まない。 |
| 4.8.4.6 | partial → partial | direction | Fの圏同値からpostcomposeをΔ¹に適用し、IsQCatEquivalence.coreとKan上のホモトピー同値への比較を適用すると、原文の同じ矢印関手圏coreの射のホモトピー同値性を直接得る。逆向きは含まない。 |
| 4.8.4.7 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：完全忠実な場合・通常圏の full/faithful・相対関手圏・引き戻しを照合。categorical pullback の四角から原文で指定した比較四角を構成する判定。pinched Hom pullback のみではその比較の全ての条件を与えない。 |
| 4.8.4.8 | partial → partial | special | coherentNerveMap_isFullyFaithful_iffの右辺は局所Kanな豊穣圏で全てのF.map X Yが圏同値という条件で、Kan上の弱ホモトピー同値との比較により原文のweakly fully faithfulの条件を直接与える。この範囲と前半の条件のみで、weakly essentially surjectiveと一般のweak equivalenceの定義は含まない。 |
| 4.8.4.9 | partial → none |  | 引用は包含順coherent nerveの右pinchedの判定。原文の逆包含Pathによるcoherent nerveと特定の比較射との同定がなく、原文の同じN^hc(F)の三つのiffとして直接適用できない。 |
| 4.8.4.10 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：完全忠実な場合・通常圏の full/faithful・相対関手圏・引き戻しを照合。局所 n-truncation を表示することと各 Hom の n-truncation の条件の同値。fully faithful の Hom 同値は切断の普遍性と異なる。 |
| 4.8.4.11 | partial → none |  | Faithfulは通常圏のHom集合上の述語。原文の∞圏のfaithful性とhFのfaithful性・指定categorical pullbackの二条件を結ぶ型ではない。 |
| 4.8.4.13 | partial → partial | special | n=0では充満忠実性と全ての正次元境界のRLPを、hasLiftingProperty_boundary_succとisFullyFaithful_of_boundary_succが同じFについて直接結ぶ。自然なpinched/interval比較でHom作用を同定できる。一般nと全てのA⊂Bの条件(3)は含まない。 |
| 4.8.4.14 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：完全忠実な場合・通常圏の full/faithful・相対関手圏・引き戻しを照合。n-faithful な射から A⊂B に沿う相対的関手圏射の n-faithful 性。ihom の内ファイブレーション性には次数付き忠実性がない。 |
| 4.8.4.15 | partial → partial | component | IsFullyFaithful.postcomposeは原文が明記する「特に充満忠実なら内部Homの同じ後合成も充満忠実」を直接返す。写像空間模型の自然な比較を通じる性質で、一般n-faithfulは含まない。 |
| 4.8.4.16 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：完全忠実な場合・通常圏の full/faithful・相対関手圏・引き戻しを照合。n-faithful な F の上の Fun_{/D}(B,C) の局所 (n−2)-truncation。相対関手圏の ∞ 圏性からは指定次数を得ない。 |
| 4.8.4.17 | partial → partial | special | fullSubcomplex_coslicePostcomp_isFullyFaithfulはGが同型で閉じた頂点集合の充満部分複体の包含の場合の同じcoslice後合成の充満忠実性。一般G・slice側・一般nは含まない。 |
| 4.8.5.1 | partial → partial | special | IsEssentiallySurjectiveはn=0で唯一要求される0-fullの条件をそのまま与える。他のnでの全てのm-fullの条件は含まない。 |
| 4.8.5.15 | none → partial | special | n=0ではcategorically 0-connectiveは0-fullすなわち本質的全射だけ。IsEssentiallySurjective.compは同じF,Gの合成についてこの結論を直接返す。(1)のn=0の場合に限り、一般nや(2),(3)は含まない。 |
| 4.8.5.17 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：n を固定する等価の場合・空間版の連結・次元・持ち上げを照合。isofibration の圏的 n-connectivity と dim≤n の包含に対する持ち上げの同値。一般の同値持ち上げは全ての低次元包含を試験しない。 |
| 4.8.5.18 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：n を固定する等価の場合・空間版の連結・次元・持ち上げを照合。n 未満で全単射・n で全射となる F の圏的 n-connectivity。単体レベルの全射条件だけを扱う型では結論が違う。 |
| 4.8.5.20 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：n を固定する等価の場合・空間版の連結・次元・持ち上げを照合。isofibration の圏的 n-connectivity と単体次数で全単射となる因子をもつ分解の同値。内アノダイン分解は n を指定しない。 |
| 4.8.5.21 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：n を固定する等価の場合・空間版の連結・次元・持ち上げを照合。圏的 n-connective な ∞ 圏射の dim≤n の因子を伴う分解とその逆。通常の horn small-object factorization には次元の上限がない。 |
| 4.8.5.22 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：n を固定する等価の場合・空間版の連結・次元・持ち上げを照合。圏的 n-connectivity が空間的 n-connectivity を含意する比較。piConnective の定義は後者側だけで前者との含意を述べない。 |
| 4.8.5.23 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：n を固定する等価の場合・空間版の連結・次元・持ち上げを照合。圏的 n-connective と n-faithful の直交性。Mathlib の HasLiftingProperty だけでは指定二クラスの直交性を得ない。 |
| 4.8.5.25 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：n を固定する等価の場合・空間版の連結・次元・持ち上げを照合。dim B≤m で圏的 (m+n)-connective 射が Fun(B,−) 上誘導する次数 n の結論。指数対象のファイブレーション性は次数を評価しない。 |
| 4.8.5.26 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：n を固定する等価の場合・空間版の連結・次元・持ち上げを照合。dim B≤m で圏的 (m+n)-connective な F が誘導する相対 Fun 比較の次数 n。絶対 Fun の前合成同値はこの相対比較と異なる。 |
| 4.8.6.1 | partial → partial | special | 始域・標的を薄い通常圏のnerveとしn=1に取ると、thinNerve_innerFibrationが同じpの存在、thinNerve_hom_ext_hornを始域に適用して次数2以上の一意性を直接得る。一般n・任意の始域は含まない。 |
| 4.8.6.2 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：n＝1 の nerve の内ホーンと相対 hC・n＝∞ の内ファイブレーション・左・右・Kan の特例を照合。0 次及び負次数の categorical inner fibration の各 Δᵐ 上のファイバーによる定義。内ファイブレーションの基底変換だけでは 0-category 条件がない。 |
| 4.8.6.9 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：n＝1 の nerve の内ホーンと相対 hC・n＝∞ の内ファイブレーション・左・右・Kan の特例を照合。n-category の底を持つ内ファイブレーションの n-categorical 性と全空間の n-category 性の同値。Quasicategory の伝播に次数はない。 |
| 4.8.6.11 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：n＝1 の nerve の内ホーンと相対 hC・n＝∞ の内ファイブレーション・左・右・Kan の特例を照合。n-categorical な G を仮定した F と G∘F の n-categorical 性の同値。内ファイブレーションの合成だけでは一意性を反映しない。 |
| 4.8.6.12 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：n＝1 の nerve の内ホーンと相対 hC・n＝∞ の内ファイブレーション・左・右・Kan の特例を照合。n-categorical inner fibration の (n+1)-faithful 性。fully faithful の基底変換には n-categorical の仮定がない。 |
| 4.8.6.13 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：n＝1 の nerve の内ホーンと相対 hC・n＝∞ の内ファイブレーション・左・右・Kan の特例を照合。各 Δᵐ 上の相対ファイバーから構成する h≤n(C/D)。絶対 HomotopyCategory の構成は D 上の単体ごとの比較を与えない。 |
| 4.8.6.17 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：n＝1 の nerve の内ホーンと相対 hC・n＝∞ の内ファイブレーション・左・右・Kan の特例を照合。相対 h≤n(C/D)→D の n-categorical inner fibration 性。内ファイブレーションの射影型には相対商構成と n の一意性がない。 |
| 4.8.6.19 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：n＝1 の nerve の内ホーンと相対 hC・n＝∞ の内ファイブレーション・左・右・Kan の特例を照合。任意 n における h≤n(C/D) と比較因子の ∞ 圏の性質。通常の pullback の ∞ 圏性には相対 h≤n がない。 |
| 4.8.6.20 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：n＝1 の nerve の内ホーンと相対 hC・n＝∞ の内ファイブレーション・左・右・Kan の特例を照合。n-categorical な D′→D に対する相対 h≤n の指定 Fun 比較の性質。slice の通常の普遍性は対象の次数を制限しない。 |
| 4.8.6.22 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：n＝1 の nerve の内ホーンと相対 hC・n＝∞ の内ファイブレーション・左・右・Kan の特例を照合。C→h≤n(C/D) 自身の内ファイブレーション性。一般の inner anodyne 分解は指定の比較射を扱わない。 |
| 4.8.6.23 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：n＝1 の nerve の内ホーンと相対 hC・n＝∞ の内ファイブレーション・左・右・Kan の特例を照合。h≤n(C/D)→D の categorical/左/右/Kan ファイブレーション等の移行。op による左右反転は相対 h≤n の射に適用した型を与えない。 |
| 4.8.6.24 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：n＝1 の nerve の内ホーンと相対 hC・n＝∞ の内ファイブレーション・左・右・Kan の特例を照合。内ファイブレーションの (n+1)-faithful 性と h≤n への比較の性質の同値。IsFullyFaithful の判定とは次数も比較も異なる。 |
| 4.8.6.25 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：n＝1 の nerve の内ホーンと相対 hC・n＝∞ の内ファイブレーション・左・右・Kan の特例を照合。一般 F の (n+1)-faithful 性を n-categorical な因子で判定。通常圏の image 分解にはこの切断次数がない。 |
| 4.8.6.26 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：n＝1 の nerve の内ホーンと相対 hC・n＝∞ の内ファイブレーション・左・右・Kan の特例を照合。categorical pullback と相対 h≤n の比較の両立。厳密 pullback の交換則だけでは h≤n を通した型がない。 |
| 4.8.6.27 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：n＝1 の nerve の内ホーンと相対 hC・n＝∞ の内ファイブレーション・左・右・Kan の特例を照合。h≤n(C/D)→D の比較の性質と原文のファイバー条件の同値。単なるファイバー Kan 性は相対 h≤n の結論を含まない。 |
| 4.8.7.3 | partial → none |  | 通常圏の商によるFull/EssSurj/Faithfulの分解で、原文のn-full/n-faithfulに関するnerve上の型と分解射の比較を欠く。 |
| 4.8.7.8 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：通常圏の商と因子分解・∞ 圏の本質像・切断・空間のモデル圏を照合。Kan 複体射を n-connective と (n−1)-truncated に分解。モデル圏の cofibration/fibration 分解のクラスは切断次数を指定しない。 |
| 4.8.8.1 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：圏同値・内アノダインの特例・空間連結と次数・通常圏の直交と余極限を照合。圏的 n-connective 性を全ての n-faithful 射に対する Fun 比較で判定。前合成同値の定義は n-faithful の試験クラスを指定しない。 |
| 4.8.8.2 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：圏同値・内アノダインの特例・空間連結と次数・通常圏の直交と余極限を照合。任意の単体集合射への圏的 n-connective の拡張定義。境界集合に対する通常の llp には ∞ 圏間の n-faithful を試験する条件がない。 |
| 4.8.8.10 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：圏同値・内アノダインの特例・空間連結と次数・通常圏の直交と余極限を照合。圏的 n-connective 射で張る arrow 圏のフィルター余極限閉性。一般の射のクラスの余極限補題に当該クラスの同定がない。 |
| 4.8.8.11 | partial → none |  | 引用の結論はt.app c.ptの前合成同値性。原文のArrow SSetでの余極限射との比較同型を直接述べず、ℕ列に限る場合にもF,Gの余極限比較の同定が必要。 |
| 4.8.8.12 | partial → none |  | 厳密pushoutでのIsPrecompositionEquivalence保存は、原文の指定次数nのn-full条件によるcategorical connectivityの結論ではない。その比較がなく、同じnの特殊形とは確認できない。 |
| 4.8.8.13 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：圏同値・内アノダインの特例・空間連結と次数・通常圏の直交と余極限を照合。各 Δᵏ での基底変換上の圏的 n-connectivity から大域的圏的 n-connectivity。個別の pullback 型ではこの局所判定がない。 |
| 4.8.8.14 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：圏同値・内アノダインの特例・空間連結と次数・通常圏の直交と余極限を照合。各 Δᵏ 上で categorical equivalence のときの大域比較。同値の基底変換の閉性では局所から大域への向きが逆。 |
| 4.8.8.15 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：圏同値・内アノダインの特例・空間連結と次数・通常圏の直交と余極限を照合。単射の圏的 n-connectivity と指定した持ち上げ条件の同値。anodyne の定義は次数と n-faithful の試験を持たない。 |
| 4.8.8.17 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：圏同値・内アノダインの特例・空間連結と次数・通常圏の直交と余極限を照合。任意の単体集合射で n 未満全単射・n で全射なら圏的 n-connective。通常の sk の単体ごとの同型の型に圏的結論がない。 |
| 4.8.8.18 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：圏同値・内アノダインの特例・空間連結と次数・通常圏の直交と余極限を照合。二つの単体境界の pushout-product 包含の圏的連結度の評価。一般の pushout-product の mono 性は n+m の評価を与えない。 |
| 4.8.8.19 | partial → none |  | pushout-productの前合成同値性は全次数の圏同値に関する命題。原文の二つの有限連結度からm+n−1を得る結論やその同じ定義への比較を型に持たない。 |
| 4.8.8.20 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：圏同値・内アノダインの特例・空間連結と次数・通常圏の直交と余極限を照合。n-faithful な U と圏的連結な f の相対 Fun 比較の結論。trivial Kan の指数随伴による移送の型には n-faithful がない。 |
| 4.8.8.21 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：圏同値・内アノダインの特例・空間連結と次数・通常圏の直交と余極限を照合。局所 (n−2)-truncated な C と圏的 m-connective な f の前合成の性質。precomposition equivalence の定義はこの二次数の条件を判定しない。 |
| 4.9.1.8 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：通常の順序数と表記・別表記・双対を照合。順序数に小文字ギリシャ文字を使う原文の表記規約。Ordinal は型で文字の選び方を宣言しない。 |
| 4.9.1.14 | partial → none |  | InitialSeg.le_apply_iffは一つの始切片埋め込みの下方閉性。原文の別の任意の狭義単調f′との点ごとの比較f(s)≤f′(s)ではなく、その証明部品。 |
| 4.9.1.26 | partial → partial | component | Order.IsCofinal(range f)は原文の∀t∃s,t≤f(s)という非有界性の成分そのもの。単調性を含む写像の共終性の全定義は含まない。 |
| 4.9.1.27 | partial → partial | stronger-hyp | T自身も整列順序と仮定すれば、exists_cof_eqの共終部分集合は誘導順序でも整列し、包含は単調なので原文と同じ存在結論を直接得る。任意の線形順序Tではない。 |
| 4.9.1.28 | partial → none |  | Order.cof/Ordinal.cofは共終部分集合の最小基数。原文の整列順序からの共終写像の最小順序型との同定を型に持たず、基数値を取るというだけでは同じ定義のcomponentではない。 |
| 4.9.1.33 | partial → none |  | cof_le/le_cof_iffは像集合の基数による下界。原文は非単調な非有界写像の始域の順序型の最小性で、基数の不等式を順序数の最小性に移す比較が必要。 |
| 4.9.2.15 | partial → none |  | Cardinal値のOrder.cofを定義することは、原文のOrdinal値の最小順序型が始順序数であることの証明ではない。exists_ord_cof_eqも整列Tの共終部分集合の型で、原文の最小性との比較を欠く。 |
| 4.9.3.5 | partial → partial | special | Cardinal.mul_lt_of_ltは二つのκ-small集合の積の濃度がκ未満と直接返す。一般の無限κでよいが、任意有限個の積の一括した閉性は含まない。 |
| 4.9.3.6 | partial → partial | special | Cardinal.add_lt_of_ltは二つのκ-small集合の余積の濃度がκ未満と直接返す。任意有限個の余積の一括した閉性は含まない。 |
| 4.9.3.7 | partial → partial | special | λが正則の場合、sum_lt_of_isRegularは添字濃度<λと各項<λから同じ余積濃度<λを直接返す。原文(1)⇒(2)のこの場合で、一般の特異λと逆向きは含まない。 |
| 4.9.3.8 | partial → none |  | sum_lt_of_isRegularは正則λについての小さい余積の上界。原文の最小の失敗する添字κの存在・下限のいずれも型の結論ではない。 |
| 4.9.3.9 | partial → partial | stronger-hyp | λも正則と仮定するとsum_lt_of_isRegularは同じ添字族の余積がλ-smallという結論を直接返す。cf(λ)=λであるこの場合に限り、特異λは含まない。 |
| 4.9.3.16 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：通常の cf と正則性・指数の評価・有界・共終を照合。非有界な濃度の積族の最小添字濃度としての ecf(λ)。通常の Cardinal.cof は順序の共終性を測る。 |
| 4.9.3.20 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：通常の cf と正則性・指数の評価・有界・共終を照合。ecf(λ) が正則であること。通常の Cardinal.cof の正則性は積の濃度を用いる ecf の正則性ではない。 |
| 4.9.3.21 | partial → none |  | IsInaccessibleは正則かつ強極限と非可算性の定義。原文のκ-smallな全ての族の積への閉性と結ぶ型は引用にないので、同じ述語のcomponentとはしない。 |
| 4.9.4.10 | partial → partial | stronger-hyp | hasCardinalLT_obj_of_NとhasCardinalLT_N_of_objはκを非可算正則に強めると原文(1)⇔(2)の同じ非退化単体全体/各次数の濃度条件を直接結ぶ。有限KからのHomの条件(3)と一般の共終数仮定は含まない。 |
| 4.9.4.12 | partial → partial | stronger-hyp | isKappaSmall_prodはκを正則に強めると二項積の同じκ-small性を直接返す。任意の無限κと任意有限個への一般化は含まない。 |
| 4.9.4.13 | partial → partial | stronger-hyp | isKappaSmall_joinはκを正則に強めると同じjoinのκ-small性を直接返す。任意の非正則な無限κは含まない。 |
| 4.9.4.14 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：有限単体・小さい単体数・指数と Ex∞・通常圏での小ささを照合。有限 K に対する Fun(K,S) が非可算 κ 未満の単体数を保つ評価。小さい圏や κ-presentable の型にこの指数対象の評価がない。 |
| 4.9.4.16 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：有限単体・小さい単体数・指数と Ex∞・通常圏での小ささを照合。Ex∞(S) の単体数が非可算 κ 未満であること。Ex∞ の Kan 性・弱同値性の型は濃度に言及しない。 |
| 4.9.4.18 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：有限単体・小さい単体数・指数と Ex∞・通常圏での小ささを照合。ecf(λ) 未満の個数の積で λ-small な単体集合が閉じる評価。通常の κ-正則性による小図式の補題の濃度条件が異なる。 |
| 4.9.4.19 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：有限単体・小さい単体数・指数と Ex∞・通常圏での小ささを照合。ecf(λ) 未満の K に対する Fun(K,S) の λ-small 性。有限図式への制限や universe lift ではこの指数共終数条件がない。 |
| 4.9.4.20 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：有限単体・小さい単体数・指数と Ex∞・通常圏での小ささを照合。κ⁺-small 単体集合の同型類全体の濃度を 2^κ で抑える評価。一個の単体集合の universe lift と区別した。 |
| 4.9.4.21 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：有限単体・小さい単体数・指数と Ex∞・通常圏での小ささを照合。次元 d 以下かつ非退化単体数 n の単体集合の同型類の有限性。個々の finite simplicial set の補題は同型類全体を数えない。 |
| 4.9.5.1 | partial → none |  | HasSmallKanModelは大小の宇宙間のKan模型の述語で、原文の指定の非可算基数κとκ-small性の評価を型に持たない。数値κへの比較なしに宇宙版の類似をspecialとしない。 |
| 4.9.5.4 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：通常圏の本質的小・圏同値と core・全部分複体・積・引き戻し・関手圏を照合。minimal ∞ 圏の κ-small 性と本質的 κ-small 性の同値。通常圏の本質像の小ささと異なり minimality が比較に必要。 |
| 4.9.5.5 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：通常圏の本質的小・圏同値と core・全部分複体・積・引き戻し・関手圏を照合。各単体集合を本質的に小さくする最小非可算濃度の存在と後続性。universe による EssentiallySmall に最小濃度の添字がない。 |
| 4.9.5.6 | partial → partial | special | HasSmallKanModelは準圏Xが小さいKan模型と圏同値という条件。逆同値を取ればXから小さいKan準圏へのcategorical equivalenceを直接与え、原文の小さい比較先をKanに制限した場合。任意の小さい準圏の模型の条件は含まない。 |
| 4.9.5.7 | partial → none |  | Hullは与えたambient準圏の中の種を含む小さい準圏と因子化性で、Aからの射のinner anodyne性を場に持たない。原文の指定inner anodyneな小さい準圏置換を直接構成しない。 |
| 4.9.5.11 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：通常圏の本質的小・圏同値と core・全部分複体・積・引き戻し・関手圏を照合。本質的 κ-small な ∞ 圏の族の非交和が添字数の条件下で本質的 κ-small。通常圏の Small の coproduct は単体数の κ 上限を述べない。 |
| 4.9.5.14 | partial → none |  | 通常圏・宇宙のEssentiallySmallに関する結果で、原文の数値κの評価と準圏のreplete subcategoryに関する同じ結論への比較を欠く。 |
| 4.9.5.15 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：通常圏の本質的小・圏同値と core・全部分複体・積・引き戻し・関手圏を照合。本質的 κ-small な C の core の本質的 κ-small 性。quasicategoryCore_kanComplex は core の Kan 性だけを扱う。 |
| 4.9.5.16 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：通常圏の本質的小・圏同値と core・全部分複体・積・引き戻し・関手圏を照合。本質的 κ-small な C の任意の充満部分 ∞ 圏の本質的 κ-small 性。通常圏の Small や頂点部分複体の κ 制約なしの型とは異なる。 |
| 4.9.5.17 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：通常圏の本質的小・圏同値と core・全部分複体・積・引き戻し・関手圏を照合。三つの本質的 κ-small な ∞ 圏から作る oriented fiber product の本質的 κ-small 性。厳密 pullback の通常の small 性では oriented product を評価しない。 |
| 4.9.5.18 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：通常圏の本質的小・圏同値と core・全部分複体・積・引き戻し・関手圏を照合。本質的 κ-small 性の homotopy fiber product での閉性。lax pullback の同値部分複体の比較には濃度の上限がない。 |
| 4.9.5.19 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：通常圏の本質的小・圏同値と core・全部分複体・積・引き戻し・関手圏を照合。categorical pullback の四角での本質的 κ-small 性の伝播。既存の categorical pullback の判定は三隅の κ 制約を比較しない。 |
| 4.9.5.20 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：通常圏の本質的小・圏同値と core・全部分複体・積・引き戻し・関手圏を照合。ecf(λ) の制約を持つ K と本質的 λ-small な C から Fun(K,C) の本質的 λ-small 性。通常の functor category の Small の型はこの濃度条件を持たない。 |
| 4.9.6.1 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：Kan の連結成分と π 群・有限・小さいモデル・ファイバーと基底変換を照合。非可算正則 κ における Kan 複体の本質的 κ-small 性を成分数と各 π 群の濃度で判定。π の補題や Small モデルは両条件を結ばない。 |
| 4.9.6.2 | partial → none |  | 全空間の各次数のSmallから単体fiberのSmallという宇宙の主張。原文の指定κでの本質的小ささと各頂点fiberの本質的小ささのiffのいずれの向きも直接述べない。 |
| 4.9.7.1 | partial → none |  | IsLocallySmallはu+1/uの宇宙差の述語。原文の指定κと各Homのessentiallyκ-smallの濃度条件を結ぶ型がなく、宇宙版の類似だけは数えない。 |
| 4.9.7.6 | partial → partial | special | IsLocallySmallはu+1の準圏Cの各頂点対にuのKan模型を与える。自然なpinched→interval比較の圏同値を合成し、Kan上でホモトピー同値へ移すと原文の各interval Homのessential smallnessを直接得る。この宇宙を指定した範囲だけ。 |
| 4.9.7.7 | partial → none |  | essentiallySmall_iffは通常圏の宇宙版。原文の指定κの濃度条件・準圏のcoreのπ₀・関手∞圏の比較への型の対応がない。 |
| 4.9.7.8 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：1 圏の局所小性・空間の局所小性・有限・正則基数の場合を照合。ecf(λ)≥κ のもとで Fun(C,D) の局所 λ-small 性を写像空間から評価。universe lift と本質的小の補題には ecf 条件がない。 |
| 4.9.7.9 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：1 圏の局所小性・空間の局所小性・有限・正則基数の場合を照合。本質的に小さい C と局所小な ∞ 圏 D による Fun(C,D) の局所小性。1 圏版の LocallySmall は Kan 写像空間の本質的小ささを意味しない。 |
| 4.9.7.10 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：1 圏の局所小性・空間の局所小性・有限・正則基数の場合を照合。κ-small な K と局所 λ-small な C から Fun(K,C) の局所 λ-small 性。局所小な通常圏の指数対象に単体数と λ の制約がない。 |
| 4.9.8.1 | partial → none |  | HasEssentiallySmallFibersはleft fibrationの頂点fiberの宇宙版で、原文の指定κと全ての単体への引き戻しの本質的κ-small性・局所κ-small性を型に持たない。 |
| 4.9.8.2 | partial → partial | component | HasEssentiallySmallFibersはleft fibrationの各頂点fiberに小さいKan模型を直接要求する。原文のessentially smallの全単体条件のうちn=0の成分に限り、任意の高次単体・locally smallの条件は含まない。 |
| 4.9.8.7 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：頂点と Δ¹ のファイバー・通常圏の局所小性と合成・濃度と正則性を照合。内ファイブレーションの本質的 κ-small 性を各辺 Δ¹ 上の引き戻し等で判定。個別の pullback の small 型にはこの局所判定がない。 |
| 4.9.8.8 | partial → none |  | left fibrationの頂点fiberの宇宙版の基底変換であり、原文の指定κでの各辺全体のessential smallnessを直接返す型ではない。 |
| 4.9.8.10 | partial → none |  | total_obj_smallは各次数のSmallという宇宙の結論。原文の数値λ・cf(λ)と本質的λ-smallな準圏模型の存在を直接結論する型がない。 |
| 4.9.8.11 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：頂点と Δ¹ のファイバー・通常圏の局所小性と合成・濃度と正則性を照合。ecf(λ) を使った内ファイブレーションの本質的 λ-small 性の判定。通常の κ-正則性に基づく small 補題に指数共終数条件がない。 |
| 4.9.8.12 | partial → none |  | total_obj_smallは各次数のSmallという宇宙の結論。原文の指定正則κでの本質的小さい模型へのcategorical equivalenceの存在は直接述べない。 |
| 4.9.8.14 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：頂点と Δ¹ のファイバー・通常圏の局所小性と合成・濃度と正則性を照合。本質的 κ-small な内ファイブレーションを二つ合成したときの本質的小ささ。InnerFibration.comp は濃度を評価しない。 |
| 4.9.8.15 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：頂点と Δ¹ のファイバー・通常圏の局所小性と合成・濃度と正則性を照合。局所 κ-small な底の上の内ファイブレーションにおける本質的 κ-small 性の同値条件。通常圏の局所小性の伝播は Kan Hom の濃度を比較しない。 |
| 4.9.8.16 | none → none |  | B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：頂点と Δ¹ のファイバー・通常圏の局所小性と合成・濃度と正則性を照合。局所 κ-small な底の上で本質的 κ-small な二つの内ファイブレーションを合成する条件。合成の内ファイブレーション性と違い局所・本質的小の両条件が必要。 |

## 検査

原文は Kerodon 公式小節の各項目Tagで照合。none は現本体・ロックしたMathlibを再検索し、近隣項目のソース・双対/限定版の候補も照合した。Archiveの宣言をown・partialの根拠にはしていない。宣言の存在と型はソースでの確認で、kernel確認ではない。
