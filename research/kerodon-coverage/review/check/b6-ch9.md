# KB-W1 / B6 第9章

原文の項目と現在のソースの型による紙の再照合。Lean・ビルド・鍵は使っていない。

対象 567行。partial 304、none 263。判定後：partial 137、none 423、own 7。

既存 own・both・mathlib 30行の全既存フィールドは変更なし。既存7列の末尾に partial_kind を追加し、対象外行は空欄とした。区切り・改行と対象外行の既存引用符を保存した。verdict・axioms・check も変更していない。古いcheck欄は今回のkernel検査結果ではない。

## 全対象行の判定・変更一覧

状態不変でも型/原文の再判定を記録した。各 reason の詳細はCSVと同じ。原文全文・候補の型・検索はgit外の章別証拠。

| 番号 | 旧→新 | partial_kind | 理由 |
| --- | --- | --- | --- |
| 9.1.1.3 | partial → partial | direction | 有限な全図式の同じ錐の存在を仮定するとisFilteredInfinity_op_of_finiteConesは同じCopのfiltered性を返す。逆向きはこの引用だけに含まない。 |
| 9.1.1.16 | partial → partial | stronger-hyp | κを正則にも限るとisKappaFiltered_sliceUnderは同じfのcosliceのκ-filtered性を直接返す。特異な無限κは含まない。 |
| 9.1.1.18 | partial → partial | stronger-hyp | κを正則に限ると本体のcosliceのκ-filtered性・弱可縮性・対角右余終性は同じ条件(1)から(2)(4)(5)を直接与える。Archiveの逆向きは採用しない。 |
| 9.1.1.20 | partial → none |  | 原文と一致するiffの候補はArchiveにあり対象外。本体のfiltered⇒弱可縮だけではKanの可縮性を返す型と同じiffをここで確認できていない。 |
| 9.1.2.1 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：本体の filtered 性は準圏への有限図式に余錐を課す。有限図式の零ホモトピーも全体 C を標的とする。h Kan 豊穣圏で各 Hom 内の境界写像をある射で後合成して零ホモトピーにする述語は見つからない。 |
| 9.1.2.5 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：全有限図式の余錐から C 内の定値図式へのホモトピーを得る型はある。hC の豊穣 Hom での後合成による消去と比較する iff は見つからない。 |
| 9.1.2.6 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：準圏に頂点が存在することと、通常圏での IsFiltered の定義を確認した。hC に対して頂点の非空性に加え二対象・平行射の条件をまとめた型は見つからない。 |
| 9.1.2.8 | partial → partial | special | Cをcardinal-filtered前順序の圏、κ=ℵ0に限るとisKappaFiltered_nerve_of_cardinalFilteredが同じnerveのfiltered性を直接返す。任意通常圏と逆向きは含まない。 |
| 9.1.2.9 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：通常の順序集合の nerve に κ-filtered 性を移す一方向はある。局所 Kan 豊穣圏の coherent nerve と h Kan 豊穣側の条件との iff は見つからない。 |
| 9.1.2.11 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：κ-small 図式の余錐と有限図式を C 内で収縮する型はある。固定 Hom(X,Y) への任意の κ-small 図式を Y→Z の後合成で Hom(X,Z) 内で収縮する型は見つからない。 |
| 9.1.2.12 | partial → partial | direction | IsFilteredInfinity.cocone_nonemptyを有限な同じ境界∂Δnの図式に適用すると右側の全延長条件を直接得る。逆向きは引用に含まない。 |
| 9.1.2.14 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：全有限形状の余錐は定値面を持つ境界も含む。指定次元で一面が定値な境界の余錐存在だけから一般の境界に移す型は見つからない。 |
| 9.1.3.1 | partial → partial | stronger-hyp | Uをleft fibrationにも強めるとtransport_to_cocone_fiberはκ-filtered性が供給する同じfUの余錐から、同じfの定値底ファイバーへの自然変換を直接返す。有限版だけでなくこの一般形状の型を使う。 |
| 9.1.3.2 | partial → partial | direction | 全空間EがfilteredならisWeaklyContractible_of_isFilteredInfinityは同じEの弱可縮性を直接返す。逆向きは含まない。 |
| 9.1.3.3 | partial → none |  | 固定宇宙の標準unstraighteningと余極限の比較は、原文の指定κ値輸送表現と任意Uの同じ全空間の比較を型に含まない。 |
| 9.1.3.4 | partial → partial | direction | 同じFの標準category of elementsがfilteredならその弱可縮性とcoherentDiagramTotalUnitの弱同値から、coherentDiagramTotalCoconeの同じ余極限が可縮となる。逆向きは含まない。 |
| 9.1.3.5 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：単射の像の κ-small 性はある。任意の小さい K→X の像を含み、なお弱可縮で小さい部分複体 Y を構成する型は見つからない。 |
| 9.1.3.6 | partial → partial | direction | 無限κのκ-filtered性をfilteredへ忘れ、その同じEの弱可縮性を返す二つの型を合成して左⇒右を直接得る。逆向きは含まない。 |
| 9.1.3.8 | none → partial | component | IsKappaFiltered.cocone_nonemptyを同じファイバー図式のEへの合成に適用し、coconeNullHomotopyで元の図式から同じ頂点の定値図式への自然変換を得る。(1)⇒(2)を直接満たし、全三条件の同値は含まない。 |
| 9.1.3.11 | partial → none |  | 通常圏のGrothendieck全体のfiltered性は、nerveのcocartesian射・各ファイバーの∞filtered性との比較が引用にない。通常圏の結論だけを同じ∞圏の特殊形と数えない。 |
| 9.1.3.12 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の Grothendieck 構成は各ファイバーの filtered 性を仮定する。原文の全空間ごとの filtered 性と底の I 個の射の共通因子条件で同じ底上の積を扱う型は見つからない。 |
| 9.1.3.14 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の Grothendieck 構成では各ファイバーの filtered 性を課す。準圏の二 coslice 射影の引き戻しには弱可縮性の補題がある。任意の二 cocartesian fibration で両全空間と底の filtered 性から引き戻しの filtered 性を得る型は見つからない。 |
| 9.1.4.1 | none → own |  | 同じFについて∀d, ∃c, Nonempty (D.Edge d (F.app _ c))と量化すれば、原文の弱右余終性の定義全体をそのまま表す。SSet.Edgeは指定両端の1単体であり専用述語名は不要。 |
| 9.1.4.5 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏では対象からの射と平行な二射の後合成による同一化で Final を判定する。準圏の C_{c/}→D_{F(c)/} の弱右余終性だけを全 c に課す iff は見つからない。 |
| 9.1.4.7 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：ホモトピー圏と nerve の随伴、通常圏の Final 判定はある。filtered な二準圏間の F と N(hF) の右余終性を往復する型は見つからない。 |
| 9.1.4.8 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：標準写像 C→N(hC) は通常の nerve 随伴の単位として取れる。filtered な C についてこの単位の右余終性を示す型は見つからない。 |
| 9.1.4.9 | partial → none |  | Monotone.final_functor_iffは通常圏のFinalの型。原文のnerve上のright/weakly right cofinal性との同じ射の比較が引用にない。 |
| 9.1.4.13 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：既知の右余終写像を左ファイブレーションに沿って引き戻す結果と、coslice 判定はある。filtered な全空間と底を持つ任意の cocartesian ファイブレーション自身を右余終とする型は見つからない。 |
| 9.1.4.14 | partial → partial | component | isWeaklyContractible_of_isFilteredInfinityは同じCについて(1)⇒(3)を直接返す。原文の三条件の残りの含意は含まない。 |
| 9.1.4.15 | partial → partial | special | κ=ℵ0・有限Kに限ればisRightCofinal_sliceUnderProjection_of_filteredは同じcoslice忘却射の右余終性を直接返す。 |
| 9.1.4.17 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：両因子が右余終なら合成も右余終で、前の因子が右余終なら後ろの因子を消去で判定できる。filtered 準圏間の左ファイブレーション G を後ろに置き、合成から F の右余終性を反映する型は見つからない。 |
| 9.1.4.18 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：小さい q の coslice 自体の κ-filtered 性と、左ファイブレーションに沿う右余終性の基底変更はある。異なる準圏の q と F∘q の coslice 間で誘導される F_{q/} が右余終となる型は見つからない。 |
| 9.1.4.19 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：同じ filtered 準圏への coslice 射影の右余終性と、通常の structured arrow での二つの Final 関手による後合成はある。F に沿った C_{c/}→D_{F(c)/} 自体の右余終性は見つからない。 |
| 9.1.5.1 | partial → partial | direction | coherentFilteredLimitExchangeShape_finiteは同じfiltered Cの点ごとの余極限を取る写像が任意有限形状の極限錐を保存することを直接返す。filtered性を戻す逆向きは含まない。 |
| 9.1.5.2 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：有限形状に対する filtered 準圏の定値図式の右余終性と、通常圏での有限極限との比較から filtered 性を得る結果はある。空間値の特定 Kᵒᵖ 形状について交換を仮定して C→Fun(K,C) を右余終とする型は見つからない。 |
| 9.1.5.4 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：κ-filtered 性と κ-small な形状を入力して定値図式を右余終にする型はある。κ・λ・μ の三濃度の下で S_{<μ} の交換を仮定して右余終性を得る型は見つからない。 |
| 9.1.5.6 | partial → partial | stronger-hyp | 中間底Ctildeもfilteredと仮定するとfiberProductToProductの右余終性と弱同値性により、二つの弱可縮な全空間の積と同じfiber productの弱可縮性を直接移せる。中間底の弱可縮性だけからの議論は含まない。 |
| 9.1.5.7 | partial → partial | component | 本体の対角右余終性は同じCについて(1)⇒(2)を直接返す。Archiveの逆向きと数値λ値の交換条件は採用しない。 |
| 9.1.5.9 | partial → partial | component | 正則κとcardinal change boundを備え、極限形状をμ-small posetのnerveに限ると同じfiltered余極限の極限保存を直接返す。全μ-small単体形状と逆向きは含まない。 |
| 9.1.5.10 | partial → partial | stronger-hyp | κを正則に強めると同じ全κ-small Kの対角右余終性、すなわち(1)⇒(2)が直接得られる。残りの同値条件は含まない。 |
| 9.1.5.12 | partial → partial | direction | κ≤κ+をisKappaFiltered_of_leに入れると同じCのκ+-filtered⇒κ-filteredを直接得る。特異性による逆向きは含まない。 |
| 9.1.5.13 | partial → none |  | IsCardinalFiltered.of_finalは通常圏のFinalによる保存。原文の∞圏のκ-filtered性とright cofinal性への比較が引用にない。 |
| 9.1.5.14 | partial → none |  | IsFiltered.of_finalは通常圏の型であり、原文のleft fibrationの同じ三条件に含意を与えるためのnerveとcofinal性の比較を引用に持たない。 |
| 9.1.5.15 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：ホモトピー retract への κ-filtered 性の移送と任意の局所化の述語はある。任意の W の局所化へ有限または κ-small 図式の余錐を送る型は見つからない。 |
| 9.1.5.16 | partial → none |  | isKappaFiltered_of_strict_isColimitはSSet内の通常余極限。原文の指定QC内の∞余極限との比較を引用に含まない。 |
| 9.1.5.17 | partial → none |  | 通常圏のFinalによるκ-filtered性の移送は、原文の同じ∞部分圏包含のright cofinal性との比較がない。 |
| 9.1.5.18 | partial → none |  | 指定されたC自体のQC内の余極限表示ではなく、Cとcodiscrete nerveの積の通常SSet余極限表示。両方の比較を追加しない限り同じ結論成分でない。 |
| 9.1.6.1 | partial → none |  | 通常filtered余極限の準圏性や自然変換上の弱同値保存は、原文の同じ余錐がcategorical colimit diagramとなる結論を直接返さない。 |
| 9.1.6.3 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：厳密な単体集合の filtered 余極限の準圏性と、Kan 複体の厳密な余錐の比較はある。通常の QCat の nerve から coherent nerve QC への包含が filtered 余極限を保つ型は見つからない。 |
| 9.1.6.4 | partial → partial | stronger-hyp | 同じKan値図式について、忘却した単体集合の指定余錐が通常余極限でもあると追加するとstrictNativeCocone_isColimit_of_filtered_forgetは同じ余錐のSpace内余極限性を直接返す。Kan圏での通常余極限という入力だけから忘却後の余極限性を得たとはしない。 |
| 9.1.6.6 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：添字形状の通常余極限から切断空間の極限を得る型と、左ファイブレーションから空間の余極限を作る型はある。任意の D と G で各 F(c) と N(C) の余極限の存在・保存を K へ移す結論は見つからない。 |
| 9.1.6.7 | partial → partial | stronger-hyp | ModelCategoryと生成系・局所表示可能性など射影モデル構造の入力を置くと、射影モデル構造の分解により同じ図式へのcofibrant置換と各点trivial fibrationを得る。SSetに具体的ModelCategory instanceなし。 |
| 9.1.6.8 | partial → none |  | modelCategoryとcofibrations_le_objectwiseは射影cofibrationの各点cofibration性で、原文の全各点trivial Kan fibrationに対する同じLLPの定義との比較を型に含まない。 |
| 9.1.6.12 | partial → partial | stronger-hyp | 射影モデル構造のModelCategory・生成系等を入力すると同じ自然変換をcofibrationと各点trivial fibrationへ分解できる。SSetへの具体的instanceなし、一般schemaとしての条件つき対応。 |
| 9.1.6.13 | partial → none |  | 一般生成系からの射影モデル構造は、原文の具体的∂Δn×hCによる最小弱飽和閉包との比較を型に含まない。 |
| 9.1.7.1 | partial → partial | stronger-hyp | λを正則にも強めるとinnerHornClosureの包含・準圏性・濃度上界が同じC0の小準圏への拡大を直接与える。非正則λは含まない。 |
| 9.1.7.2 | partial → partial | component | 準圏性をPに取りinnerHornClosureの小性と包含を渡すと、smallSubcomplexFamilyの同じ小準圏族のλ-filtered性と通常SSet余極限表示を直接得る。QC内の余極限表示は含まない。 |
| 9.1.7.3 | partial → none |  | posetの部分集合の小性だけでは、そのnerveの全非退化単体のλ-small性への比較がなく、原文の小単体部分集合の拡大を直接返さない。 |
| 9.1.7.4 | partial → none |  | posetの部分集合族の被覆とfiltered性は、原文の単体部分集合の濃度・SSet余極限・QC余極限を同じ対象に対して返さない。 |
| 9.1.7.5 | partial → partial | component | SharplyLTとexists_cofinalは厳密κ◁λについて同じ小部分集合のcofinal族の条件を直接与える。非厳密κ⊴λの等号の場合を含む全定義はこの引用だけに含まない。 |
| 9.1.7.8 | partial → partial | component | Cardinal.SharplyLT.of_pow_ltは原文の指数条件を同じ基数に適用して最後のκ◁λを直接返す。全κ-small部分集合族自体のλ-small性の成分は含まない。 |
| 9.1.7.9 | partial → partial | special | κ<λに限るとof_pow_ltは同じκ◁λを返すのでκ⊴λの要求を満たす。κ=λの場合は引用の型外。 |
| 9.1.7.12 | partial → partial | direction | 同じκ<λの指数条件からof_pow_ltがκ◁λを直接返す。GCHを使う逆向きは含まない。 |
| 9.1.7.13 | partial → partial | special | κ<λ<μに限ればSharplyLT.transが同じκ◁μを返す。等号を許す非厳密版全体は含まない。 |
| 9.1.7.14 | partial → none |  | 通常posetの部分集合のλ-small性とκ-directed性は、そのnerveの小性と∞filtered性の同時比較を型に含まず、原文の指定単体部分集合の拡大は直接得られない。 |
| 9.1.7.16 | partial → none |  | poset被覆のfiltered性だけでは、原文の小準圏の単体的な濃度と二つの圏での余極限表示を返さない。 |
| 9.1.7.18 | partial → none |  | 集合の小部分集合のcofinal族は、原文の面・退化で閉じた単体部分集合族の小性との比較を含まない。 |
| 9.1.7.20 | partial → none |  | poset被覆のfiltered性と各nerveのκ-filtered性はあるが、原文のλ-smallな単体部分圏とμ-small添字の同じ余極限表示を直接返さない。 |
| 9.1.7.21 | partial → partial | component | B6型照合：濃度変更条件を満たす filtered poset の nerve は、小さい filtered 部分 poset の nerve の通常の SSet 余極限になる。部分集合の添字の filtered 性もある。任意の μ-small 準圏の表示と、原文の λ,μ による添字の濃度境界は残る。 |
| 9.1.8.1 | partial → partial | direction | B6型照合：κ=ℵ₀ として「filtered ⇒ cofinal な directed poset が存在」の向きのみ。逆向き（cofinal poset から filtered）の宣言は見当たらない。 |
| 9.1.8.2 | partial → partial | stronger-hyp | B6型照合：仮定：Lean の小部分複体の拡張には κ の正則性と κ≤#T が必要。原文は無限基数 κ（Lean が強い）。結論：C×N(Codiscrete T)→C は非空 T で自明 Kan ファイブレーション。積で小さい単射余錐を得る宣言はあるが、任意の無限 κ に対する原文の存在は覆わない。 |
| 9.1.8.4 | partial → none |  | 原文の指定C自体とKα▷による表示ではなくC×N(Codiscrete T)上の終対象付き部分複体の右余終性。 |
| 9.1.8.5 | partial → none |  | C×N(Codiscrete T)の通常余極限表示は指定QC_<λ内のCの余極限表示と比較されていない。 |
| 9.1.8.7 | partial → partial | component | B6型照合：右 cofinal な κ-directed poset の存在は確認。κ◁λ と C の λ-small 性から、添字 poset も λ-small に取る原文の基数評価は引用型にない。 |
| 9.1.8.8 | partial → partial | direction | B6型照合：「κ-filtered ⇒ cofinal な κ-directed poset が存在」の向きのみ。逆向きの宣言は見当たらない。 |
| 9.1.8.9 | partial → none |  | 任意のcofinal posetの存在は指定Ord_<κを始域にする存在と異なり、ordinalNerveのfiltered性だけは証明の部品。 |
| 9.1.8.10 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：可算個の単体を持つ X の有限段階の通常余極限と、一般の κ-directed poset からの右余終関手はある。自然数の nerve 自体から可算 filtered 準圏へ右余終関手を構成する型は見つからない。 |
| 9.1.8.11 | partial → partial | component | 終対象を持つ場合にisKappaFiltered_of_terminalは同じCのκ-filtered性を直接返す。原文の終対象条件からfiltered性への成分に一致し、その他の同値条件と逆向きは含まない。 |
| 9.1.8.12 | partial → partial | direction | B6型照合：終対象 ⇒ κ-filtered の向きのみ。有限な filtered ∞ 圏が終対象を持つ向きはない。 |
| 9.1.9.1 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：通常の filtered 余極限の準圏性と空間の 0-truncated の述語はある。QC 内の余極限で写像空間の一様な n-truncation を保存する型は見つからない。 |
| 9.1.9.3 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：Kan 複体の filtered 図式の正準余錐と、個別の空間の 0-truncated 述語はある。任意の整数 n で全頂点が n-truncated のとき、その空間値余極限も n-truncated となる型は見つからない。 |
| 9.1.9.4 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：単独の準圏では walking idempotent の余極限存在によって冪等完備性を判定できる。filtered 準圏図式の QC 内の余極限でこの性質を保存する型は見つからない。 |
| 9.1.9.5 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：厳密な κ-filtered 余極限では κ-small な図式の写像がある段で因数分解し、各段の κ-filtered 性も移る。QC 内の余極限で、遷移関手が K 余極限を保つとき各余錐脚も保つという型は見つからない。 |
| 9.1.9.6 | partial → none |  | κ-small写像の段への因数分解は、原文のcoslice余極限比較θの同型性とは異なる結論。 |
| 9.1.9.7 | partial → partial | component | B6型照合：指定された通常 filtered 余極限の頂点が準圏となる結論はある。互換な K▷ 図式が各段で普遍余錐なら、同じ余錐が頂点の準圏でも普遍になる型は見つからない。 |
| 9.1.9.8 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：厳密な余極限への小図式の因数分解と Kan 複体の余錐比較はある。一般の QC の余極限で K 余極限が存在し、そこから出る任意の T の保存性を全段で判定する型は見つからない。 |
| 9.1.9.9 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：全小余極限を保つ射を持つ presentable 圏の模型と、関手の κ-filtered 余極限保存の述語はある。任意の形状族 K について K-余完備な準圏の部分圏に小 κ-filtered 余極限を作り包含の保存まで与える型は見つからない。 |
| 9.1.9.10 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：presentable 圏の PrL は一宇宙の全小余極限保存を用い、strict な補題は単体集合の余極限の filtered 性を扱う。非可算 λ で QC_{<λ} の K-余完備部分に λ-small な余極限を作る型は見つからない。 |
| 9.1.9.11 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：全小余極限保存から κ-finitary 性を得る型と特定の Ind 左 Kan 延長の保存性はある。指数余終性の下で任意の K-余完備化関手が λ-small κ-filtered 余極限を保つ型は見つからない。 |
| 9.2.0.1 | partial → partial | special | B6型照合：有限自由加群の有限表示があり、階数1では free 随伴と PUnit の coyoneda で Hom 関手を forget と比較し、filtered 余極限保存を得る。任意の左 R-加群で代数的有限表示と Hom の保存性を結ぶ iff は見つからない。 |
| 9.2.0.5 | partial → partial | direction | B6型照合：有限 ⇒ finitely presentable の向きのみ（Mathlib）。自前は κ-small ⇒ κ-presentable。逆向きはない。 |
| 9.2.1.1 | partial → none |  | 余積と幾何実現からの全小余極限生成は、有限余極限とfiltered余極限からの同じ生成命題ではない。 |
| 9.2.1.3 | partial → none |  | 宇宙で小さい全κ-filtered形状を量化する述語は、原文の指定λ-smallだけに限った二濃度の定義と同じではない。 |
| 9.2.1.7 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：宇宙小の κ-filtered 余極限の存在述語と、余積・幾何学的実現から全小余極限を作る型はある。κ-small な余極限と λ-small κ-filtered な余極限から λ-余完備性を得る濃度分解は見つからない。 |
| 9.2.1.9 | partial → partial | component | B6型照合：全小余極限があれば小さい κ-filtered 余極限もある型は確認できる。任意の小さい κ について κ-small な余極限と小 κ-filtered 余極限を合わせて全小余極限を得る逆向きは見つからない。 |
| 9.2.1.10 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：全小余極限から小 filtered 余極限への制限と、余積・実現による全小余極限の構成はある。有限余極限と λ-small filtered 余極限を仮定して λ-small な任意の形状に余極限を作る型は見つからない。 |
| 9.2.1.11 | partial → none |  | cofinal posetの存在に原文の必要なλ-small性の型がなく、同じλにおける余極限存在のiffは導けない。 |
| 9.2.1.12 | partial → own |  | 小さい同じκ-filtered形状にexists_cofinal_kappaFiltered_posetを適用し、全poset余極限の仮定をその制限へ入れてhasColimit_of_rightCofinalRestrictionで戻す。逆はnerveのκ-filtered性による特殊化で直接得る。専用の合成iff名は不要。 |
| 9.2.1.13 | partial → none |  | κ=ℵ0のcofinal posetが得られても指定λ-small性が型にない。原文の同じ濃度境界のiffとしない。 |
| 9.2.1.14 | partial → none |  | N(Idem)のfiltered性とその余極限による冪等完備性は、指定κ-smallな形状の小性と全形状の余極限存在を結ぶ型を含まない。 |
| 9.2.1.15 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：準圏と通常圏に宇宙小の濃度別余極限の述語はある。三つの正則濃度で (κ,μ) の存在を (κ,λ) と (λ,μ) の存在に分解する型は見つからない。 |
| 9.2.1.16 | partial → none |  | 通常圏のHasCardinalFilteredColimits.of_leは原文の∞圏の余極限への比較を含まない。 |
| 9.2.1.17 | partial → none |  | 通常圏の余極限存在の単調性は原文の∞圏におけるλ-small/λ-filteredの分解と比較されていない。 |
| 9.2.2.1 | partial → partial | component | PreservesSmallKappaFilteredColimitsのκ=ℵ0は原文の同じFのfinitary条件を直接与える。全関手準圏のその条件による全部分圏という追加の構成成分はこの引用だけに含まない。 |
| 9.2.2.3 | partial → partial | component | PreservesSmallKappaFilteredColimitsの同じκは原文の同じFのfinitary条件を直接与える。全関手準圏のその条件による全部分圏という追加の構成成分はこの引用だけに含まない。 |
| 9.2.2.6 | partial → none |  | 宇宙小形状すべてでの保存述語は原文の指定λ-smallだけの保存と同じ条件ではない。二つの大きさを比較する型がない。 |
| 9.2.2.14 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：PrL の対象は presentable、射は全小余極限を保つ。κ-filtered かつ λ-small な形状で対象と射を制限し、さらに μ-small な対象へ絞る QC 部分圏は見つからない。 |
| 9.2.2.21 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：全小余極限保存を小余積と有限余極限の保存から導く型はある。κ-small な全形状と λ-small κ-filtered 形状の保存を組み合わせる二濃度の判定は見つからない。 |
| 9.2.2.22 | partial → none |  | 引用は余極限の存在とaccessible性の入力で、同じFのκ-small余極限保存と全保存を結ぶ型ではない。 |
| 9.2.2.23 | partial → partial | stronger-hyp | Cを全小余完備、Fを全小filtered余極限保存にも強めると二つのpreservesSmall補題により同じFの全小余極限保存を直接得る。指定λ-smallだけを仮定する場合は含まない。 |
| 9.2.2.24 | partial → partial | direction | 有限余極限保存から有限余積保存を取り、preservesSmallCoproducts_of_finite_filteredで小余積保存、preservesSmallColimits_of_coproducts_finiteで同じFの全小余極限保存を得る。右⇒左の向きに一致する。 |
| 9.2.2.25 | partial → none |  | 全宇宙小posetでの判定は原文の指定λ-small posetに対する判定と異なる量化。必要な添字のλ-small性が引用にない。 |
| 9.2.2.27 | partial → none |  | 全宇宙小posetでの保存判定は指定λ-smallだけの量化に比較されていない。 |
| 9.2.2.29 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：宇宙小の κ-filtered 余極限保存と、より大きい濃度で filtered な形状への制限はある。(κ,μ)-finitary 性を (κ,λ) と (λ,μ) の二条件に分ける iff は見つからない。 |
| 9.2.2.30 | partial → none |  | 引用of_leはcompact性の基数単調性で、原文の同じFの二種類の保存性を分解する型ではない。 |
| 9.2.2.31 | partial → none |  | compact性の基数単調性は同じ関手Fのfinitary判定の型ではない。 |
| 9.2.3.1 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：κ の始順序の nerve の filtered 性、個別図式の保存余極限、および自然数列についての保存定理はある。任意の正則 κ の Ord_{<κ} を固定した存在と保存の一対の定義は見つからない。 |
| 9.2.3.4 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：全小余極限を保つ presentable 圏の準圏と、自然数列の余極限保存の定理はある。κ-順次余完備な対象と κ-順次余極限保存射だけを持つ QC の部分圏および λ-small 版は見つからない。 |
| 9.2.3.5 | partial → none |  | 線形順序の共終性と指定cofinal写像に沿う余極限比較は候補だが、原文の同じQへOrd_<cf(Q)からのcofinal写像を供給する型を確認していない。自然数部分列の比較だけをこのiffの特殊化と数えない。 |
| 9.2.3.6 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：κ の順序の nerve が κ-filtered であることと、一般の κ-filtered 準圏へのある poset からの余終写像はある。κ⁺-small な任意の形状を指定の順序 κ で検査できる型は見つからない。 |
| 9.2.3.8 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：可算個の単体を持つ X の有限段階の通常余極限と、自然数列の余終部分列の比較はある。可算 filtered 準圏の全図式に対して自然数列へ制限し、存在と保存を往復する型は見つからない。 |
| 9.2.3.9 | partial → partial | special | B6型照合：一般の κ の順序形状の filtered 性と、有限余極限・自然数列を使った可算形状の保存余極限の構成はある。任意の正則 κ と κ⁺ に対する存在・保存の判定は見つからない。 |
| 9.2.3.10 | partial → partial | component | B6型照合：一つの宇宙の小さい可算 B に対し、有限形状と自然数列の余極限の存在・保存を仮定して Bᵒᵖ 上の保存余極限を作る。濃度による aleph1 の一般の存在・保存 iff としては確認できない。 |
| 9.2.3.11 | partial → none |  | 通常圏の余極限存在とcompact性の単調性は、原文の∞圏と関手のsequential余極限による判定と異なる主張。 |
| 9.2.3.12 | partial → none |  | 通常圏の余極限存在とcompact性の単調性を∞圏の同じ逐次余極限判定へ移す比較がない。 |
| 9.2.4.1 | partial → none |  | 積射影に沿うstrict pullbackのfiltered性は原文の一般categorical pullbackと同じものではなく、right cofinalな二射影との比較もない。 |
| 9.2.4.3 | partial → none |  | pullbackのκ-filtered余極限の存在と保存は、そのpullback自体のλ-filtered性や射影のright cofinal性ではない。 |
| 9.2.4.5 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：右余終射の左ファイブレーションに沿う厳密引き戻しは右余終。両脚が右余終で逐次余極限を保つという条件からホモトピー引き戻しに頂点を得る型は見つからない。 |
| 9.2.5.10 | partial → partial | direction | B6型照合：κ-small ⇒ κ-presentable の向きのみ（ℵ₀ は Mathlib）。逆向きはない。 |
| 9.2.5.11 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：通常のコンパクト束要素について有限個の原子による判定はある。任意の正則 κ に対し、部分集合の濃度と Sub(Y) の nerve 内の共表現可能関手の κ-filtered 余極限保存を比較する iff は見つからない。 |
| 9.2.5.12 | partial → none |  | IsKappaCompactの宇宙小形状の全保存は、原文の指定λ-smallかつκ-filtered形状と数値μのHom対象を同時に扱う定義ではない。 |
| 9.2.5.21 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：宇宙小の κ-compact 性の定義とより大きい濃度への単調性はある。三濃度の (κ,μ)-compact 性を (κ,λ) と (λ,μ) の両条件に分ける iff は見つからない。 |
| 9.2.5.22 | partial → partial | component | PreservesKappaFilteredColimits.of_leを同じcovariantRepresentableInfinityに適用すると原文のκ-compact⇒λ-compactという右辺一成分を直接得る。(κ,λ)-compactとの全同値は含まない。 |
| 9.2.5.23 | partial → partial | component | κ=ℵ0のcompact判定と保存の基数単調性から同じ対象のcompact⇒λ-compactを直接得る。二濃度の残りの条件は含まない。 |
| 9.2.5.24 | partial → none |  | 宇宙小の全κ-filtered余極限についてのκ-compact性の閉性は、λ-smallのみをテストする(κ,λ)-compact性とは異なる仮定・結論。 |
| 9.2.5.25 | partial → partial | special | B6型照合：原文は任意の小さい正則 κ について κ-small 余極限で閉じる主張。引用は非可算の小 quasicategory・poset 形状と有限形状の結果。 |
| 9.2.6.1 | none → own |  | 同じKan複体Xについて∃K:SSet, K.Finiteかつ∃f:K⟶X, IsWeakHomotopyEquivalence fという既存の型の存在量化が原文の定義全体に一致する。専用名の欠如を不足としない。 |
| 9.2.6.3 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：有限単体集合の Kan 置換の族と単体集合の有限形状を押し出しで組む帰納法はある。空間圏内で一点の有限余極限閉包に入ることと本質的有限性の iff は見つからない。 |
| 9.2.6.4 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：有限 CW 複体の細胞数による判定と有限単体集合の Kan 置換はある。Sing(Y) とのホモトピー同値があることを任意の Kan 複体の本質的有限性と往復する型は見つからない。 |
| 9.2.6.5 | partial → partial | special | Xを有限単体集合の標準Kan置換に限ると、有限生成対象のcompact性は同じXのSpace内compact性を直接返す。任意のessentially finite Xへの輸送と逆向きは含まない。 |
| 9.2.6.6 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：指定の生成族の像の頂点 retract と空間の有限単体集合由来の生成族はある。任意の本質的有限な Kan 複体から h Kan 内で retract となることを一つにした述語は見つからない。 |
| 9.2.6.7 | partial → none |  | compact generatingのretract判定は、原文の有限単体集合によるdominationと全空間のhS内retractを結ぶ同じ比較を型に含まない。 |
| 9.2.6.9 | partial → partial | stronger-hyp | B6型照合：非可算正則 μ について μ-small Kan 複体が μ-compact の向きのみ。 |
| 9.2.6.10 | partial → none |  | 固定宇宙のκ-compact性は、数値λで切った空間圏の(κ,λ)-compact性と同じ対象・保存条件への比較がない。 |
| 9.2.7.1 | none → own |  | 同じ準圏Cについて∃K:SSet, K.Finiteかつ∃f:K⟶C, IsPrecompositionEquivalence fという既存の型の存在量化が原文の定義全体に一致する。有限模型にKan性を課さない。 |
| 9.2.7.2 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：Kan 置換への有限な相対図式を、境界単射を備える有限模型とホモトピーで近似する型はある。本質的有限な任意の準圏 C に対して有限 K₀→K→C の厳密因数分解を作り、K→C を categorical equivalence とする型は見つからない。 |
| 9.2.7.3 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：辺の族の局所化の述語と有限写像円柱の始域射はある。有限の反転指定を付けた後も局所化が有限単体集合からの categorical equivalence を持つ型は見つからない。 |
| 9.2.7.4 | partial → partial | direction | B6型照合：任意の前合成同値な単体写像は弱ホモトピー同値なので、有限 K を使う categorical equivalence から弱同値の証人が得られる。Kan 同士の Whitehead 型には K の Kan 性も必要で、任意の有限な弱同値模型から有限 categorical 模型を得る逆向きは残る。 |
| 9.2.7.6 | partial → none |  | 厳密SSet pushoutの有限性だけでは、原文のcategorical pushoutへの比較と本質的有限性を返さない。 |
| 9.2.7.7 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：通常の単体集合の圏で有限個の有限単体集合を余極限すると有限になる。QC 内の有限図式で各準圏の本質的有限性がその余極限へ移る型は見つからない。 |
| 9.2.7.8 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：有限な単体集合の形状を境界の pushout で組む型はある。QC 内の Δ¹ の有限余極限閉包を本質的有限な準圏全体と同定する型は見つからない。 |
| 9.2.7.9 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：有限単体集合の通常圏での presentability と有限 Kan 置換の空間圏での compact 性はある。有限の categorical 模型を持つ準圏が QC の対象として compact になる型は見つからない。 |
| 9.2.7.10 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：準圏の頂点 retract と、写像の categorical equivalence の候補述語はある。QC の対象が本質的有限な準圏の h QCat 内の retract であることをまとめる述語は見つからない。 |
| 9.2.7.12 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：一般の compact 生成族の像の retract 判定と、その空間圏での適用はある。小さい準圏を QC の対象とし、本質的有限な準圏からの retract で判定する適用は見つからない。 |
| 9.2.7.13 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：有限単体集合由来の空間の小さい生成圏はある。QC の有限支配対象全体の小さい模型は見つからない。取得本文は ℵ₁-small の直後に有限個の単体と記しており、濃度の文言に差がある。 |
| 9.2.7.14 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：κ-small な通常の単体集合の presentability と空間圏の κ-small Kan 対象の compact 性はある。QC 内の Δ¹ の κ-small 余極限閉包、準圏の本質的小ささ、QC 内の κ-compact 性を結ぶ型は見つからない。 |
| 9.2.7.15 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：固定宇宙の空間圏で κ-small な Kan 対象を compact とする型と濃度変更の条件はある。λ-small 準圏の QC_{<λ} での (κ,λ)-compact 性と Δ¹ の生成閉包を往復する型は見つからない。 |
| 9.2.8.1 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：点または辺からの coslice で compact 性を扱う補題はある。任意の (κ,λ)-finitary な右ファイブレーションで U(X) の相対 compact 性から X の相対 compact 性を導く型は見つからない。 |
| 9.2.8.2 | partial → none |  | pointCosliceVertexは始点固定の矢印で、原文の終点図式固定のsliceとは逆向き。入力両端のcompact性も異なり、同じsliceの結論でない。 |
| 9.2.8.3 | partial → partial | component | B6型照合：(1) の形だけ。lax pullback（= oriented fiber product, Fun(Δ¹,C) の strict pullback）で、両入力が余極限を持ち F± が保てば余極限が存在し、余極限錐は両射影で判定（任意の形状 J、(κ,λ) の制限なし）。(2) の compact 性の主張はない。名前空間 SerrePositivity.InfinityCategories.F2。 |
| 9.2.8.5 | partial → none |  | 宇宙小のcompact性とstrict pullbackの定理は指定λ-small形状の(κ,λ)-compact性の主張に比較されていない。 |
| 9.2.8.6 | partial → none |  | 二脚pullbackのcompact性は原文の任意個の積の各因子のcompact性の判定と別対象。 |
| 9.2.8.7 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：小さい通常圏の単体集合値極限と濃度つき filtered 余極限の交換、および Kan 複体の塔極限はある。二濃度で余完備な準圏の isofibration 塔で、成分の compact 性から極限準圏の compact 性を得る型は見つからない。 |
| 9.2.8.9 | partial → none |  | 定値一点図式のcompact性はあるが、原文の指定λ-smallだけをテストする条件との比較を持たない。 |
| 9.2.8.11 | partial → none |  | 小準圏Aのcosliceにおける全κ-filtered余極限のcompact性は、原文の指定λ-smallのみでのcompact性と同じ型ではない。 |
| 9.2.9.1 | partial → none |  | strict pullbackのcompact性は原文の指定QC_<μ内のκ-small図式の極限との比較がなく、二濃度compact性も異なる。 |
| 9.2.9.2 | partial → none |  | 引用は非可算μ-compact性についての型で、原文の有限図式でのℵ0-compact性を返さない。 |
| 9.2.9.4 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：単独の準圏の小 κ-filtered 余極限と指定二脚の引き戻しでの存在はある。内ファイブレーションを任意の Δⁿ 上に引き戻し、全ての引き戻しに (κ,λ)-余完備性を課す述語は見つからない。 |
| 9.2.9.5 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：ordinal nerve の κ-filtered 性と自然数列から可算形状の保存余極限を得る型はある。任意の Δⁿ への引き戻しで κ-順次余極限を要求する定義、および (κ,κ⁺)-余完備性との同一視は見つからない。 |
| 9.2.9.7 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：相対余極限性と小さい κ-filtered 余極限存在の述語はある。Δ¹ 上への引き戻しごとの二濃度余完備性と、頂点上の全余極限が edgewise となる条件との三条件の iff は見つからない。 |
| 9.2.9.14 | partial → none |  | 全関手圏内のcompact性は原文のΔ1上の指定section準圏のcompact性と別の対象。比較を含まない。 |
| 9.2.9.16 | partial → none |  | 全関手圏のcompact性は原文のUのsection準圏におけるcompact性を直接返さない。 |
| 9.2.9.19 | partial → none |  | 全関手圏のcompact性はcocartesian sectionの全部分圏への同じcompact性に移す比較がない。 |
| 9.3.1.1 | partial → partial | special | B6型照合：「Ind 完備化を与える」述語はなし。具体的な模型 IndInfinity ℵ0 C（C 小）とその性質（compact 生成・普遍性）。Mathlib の Ind C は 1 圏。 |
| 9.3.1.2 | partial → partial | component | 小さい準圏Cの標準IndInfinityとindYonedaの充満忠実性・filtered余極限存在・普遍性は原文の同じCに対するInd完備化の存在成分を直接実現する。一意性と関手性の全体は含まない。 |
| 9.3.1.3 | partial → none |  | Indの制限同値は原文の指定Pro完備化と反転同値を構成しない。 |
| 9.3.1.4 | partial → partial | special | B6型照合：9.3.1.1 と同じ：述語はなく κ の模型 IndInfinity κ C とその性質。 |
| 9.3.1.5 | partial → partial | component | 小さい準圏Cの標準IndInfinityとindYonedaの充満忠実性・filtered余極限存在・普遍性は原文の同じCに対するInd完備化の存在成分を直接実現する。一意性と関手性の全体は含まない。 |
| 9.3.1.7 | partial → none |  | IndInfinityの宇宙小κ-filtered閉包は原文の指定λ-smallだけの完備化ではない。 |
| 9.3.1.8 | partial → none |  | 同じく数値λのIndκλ完備化の存在と一意性を返す型ではない。 |
| 9.3.1.12 | partial → partial | special | B6型照合：Ind 延長という名前の述語はない。κ-連続な左 Kan 延長の存在と制限の同値で代用。λ=∞（Ind_κ）の場合だけ。 |
| 9.3.1.13 | partial → partial | special | B6型照合：名前の付いた Ind(F) はない。F ≫ indYoneda に exists_indComparison を当てれば得られる。 |
| 9.3.1.16 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：一つの Ind-Yoneda の局所添字の射影が右ファイブレーションで、左 Kan 延長には κ-filtered 余極限保存がある。任意の U:E→C を同じ二濃度の Ind 完備化の間の右ファイブレーションへ延長する指定引き戻しは見つからない。 |
| 9.3.2.1 | partial → partial | special | B6型照合：充満忠実・像 compact ⇒ 延長が充満忠実。λ=∞（Ind_κ）の場合だけ、C は小さい（宇宙 u）場合。 |
| 9.3.2.2 | partial → partial | special | B6型照合：Ind(F) の充満忠実性の明示的な宣言はなし。CFF から導ける形。 |
| 9.3.2.3 | partial → partial | special | B6型照合：Ind 完備化の判定。「もし」の向き（compact 生成 ⇒ Ind 同値）と模型の性質。λ=∞（Ind_κ）の場合だけ、C は小さい（宇宙 u）場合。 |
| 9.3.2.5 | partial → partial | special | B6型照合：compact な余極限頂点は filtered 図式の項の retract。生成の閉包一般ではなく単一の κ-filtered 表示がある場合。λ=∞（Ind_κ）の場合だけ。 |
| 9.3.2.6 | partial → partial | special | B6型照合：Ind_κ(C) の κ-compact 部分 ≃ Idem(C)（冪等完備化）。模型について、λ=∞（Ind_κ）の場合だけ。 |
| 9.3.2.8 | partial → partial | special | B6型照合：冪等完備な C ≃ Ind_κ(C) の κ-compact 部分。λ=∞（Ind_κ）の場合だけ。 |
| 9.3.2.9 | partial → partial | component | 小さいCの標準Indとcompact生成表示についてindComparison_isFullyFaithful_of_compactは同じ拡張関手の充満忠実性を直接与える。任意のfの全四条件のiffは含まない。 |
| 9.3.2.10 | partial → partial | component | 小さいCの標準Indとcompact生成表示についてindComparison_isFullyFaithful_of_compactは同じ拡張関手の充満忠実性を直接与える。任意のfの全四条件のiffは含まない。 |
| 9.3.2.13 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：有限表示加群から平坦加群への射が有限階数自由加群を経由する型と、加群の忘却による filtered 余極限保存はある。平坦加群自体の有限自由加群による filtered 余極限表示と、その全体の Ind 同値は見つからない。 |
| 9.3.2.17 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：Ind-Yoneda は元の写像空間を比較する充満忠実な包含で、空間の 0-truncated 述語もある。一般の整数 n について (κ,λ) の Ind 全体の局所 n-truncation を元の C と比較する iff は見つからない。 |
| 9.3.2.18 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：準圏の IndInfinity と通常圏の Ind はそれぞれある。一般の通常圏 C の nerve に対し、前者を通常圏の Ind の nerve と同定する型は見つからない。 |
| 9.3.2.20 | partial → none |  | spaceCompactGeneratorInclusionは指定された有限generator像であり、原文の全essentially finite空間の全部分圏との同一視を引用に含まない。 |
| 9.3.2.21 | partial → none |  | 宇宙パラメータのInd・空間・unstraighteningの型は、原文の指定数値κ・λ・μの値圏と同じ余極限・小性条件へ比較されていない。固定宇宙の空間の κ-small Kan 対象は非可算正則 κ で κ-compact であり、一般の compact 生成表示から Ind 比較の充満忠実性や同値を得られる。二つの濃度で切った空間部分圏の指定包含と sharply below による同値は見つからない。 |
| 9.3.2.22 | partial → none |  | 宇宙パラメータのInd・空間・unstraighteningの型は、原文の指定数値κ・λ・μの値圏と同じ余極限・小性条件へ比較されていない。空間圏の ℵ₀-accessibility と非可算正則 κ で κ-small な Kan 対象の κ-compact 性はある。任意の非可算正則 κ に対して S_{<κ} の指定包含が空間圏全体の Indκ 完備化となる型は見つからない。 |
| 9.3.2.24 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：有限単体集合の Kan 置換を生成族とする空間圏の表示と、任意の指定 compact 生成圏に対する Ind 比較はある。本質的有限な準圏の部分から QC 全体を Ind で得る型は見つからない。 |
| 9.3.2.25 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：小さい生成準圏と単一 κ の Ind の制限同値はある。QC_{<κ} の包含から QC_{<λ} への充満忠実性と sharply below の場合の同値は見つからない。 |
| 9.3.2.26 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：固定宇宙の CatInfinity は準圏で、別途任意の小さい準圏の IndInfinity は構成される。濃度 κ の QC を生成対象に取ったとき全 QC と同定する型は見つからない。 |
| 9.3.3.1 | partial → none |  | 宇宙パラメータのInd・空間・unstraighteningの型は、原文の指定数値κ・λ・μの値圏と同じ余極限・小性条件へ比較されていない。μ-small の一般形はない。小さい C で Ind の固定頂点写像が小さい（宇宙の意味の局所小）。 |
| 9.3.3.2 | partial → partial | special | Cを宇宙で小さく標準Indℵ0に限るとind_hasSmallFixedVertexMapsは同じIndの写像の局所小性を直接返す。一般の大きい局所小Cは含まない。 |
| 9.3.3.3 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：IndInfinity は固定宇宙の前層の充満部分複体。左ファイブレーションのファイバーの本質的小性とは別に、Ind 全体の本質的 μ-small 性を与える濃度評価は見つからない。 |
| 9.3.3.5 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：個別の準圏上の Ind の普遍性と延長の保存はある。QC_{<μ} の自己関手に自然単位を指定し、全対象の二濃度の完備化と全辺の相対 finitary 性を要求する定義は見つからない。 |
| 9.3.3.7 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：対象ごとの IndInfinity と、その関手制限の普遍同値がある。濃度制限された QC 上で Ind_{κ}^{λ} が一つの関手となる存在と自然同型までの一意性は見つからない。 |
| 9.3.3.8 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：指定関手から Ind の左 Kan 拡張を構成する型はある。κ,λ を固定した QC 上の一意な完備化関手と、その F に対する作用を同時に与える型は見つからない。 |
| 9.3.3.12 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：固定 C の Ind から前層への包含は κ-filtered 余極限を保ち、濃度変更の条件もある。Ind が C を変数とする QC_{<μ} の関手として μ-small λ-filtered 余極限を保つ型は見つからない。 |
| 9.3.3.13 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：一つの準圏の Ind 制限同値と、Ind-Yoneda の局所添字への射影の右ファイブレーション性はある。C 上の二つの内ファイブレーションで、全 Δⁿ への基底変更後に (κ,λ) の完備化を要求する定義は見つからない。 |
| 9.3.3.15 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：一点の底に当たる通常の Ind の制限同値はある。一般の内ファイブレーションで二濃度余完備性、各ファイバーの完備化、各辺上の compact 性をまとめた iff は見つからない。 |
| 9.3.3.17 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：単一準圏の IndInfinity とその小 κ-filtered 余完備性を確認した。与えた U の底を保つ二濃度相対完備化と、その構造射の inner fibration 性の存在は見つからない。 |
| 9.3.3.18 | partial → none |  | 絶対Indの全関手準圏の制限同値は、原文の底上のsection準圏とfiberwise finitary部分圏の同じ制限への比較を含まない。底を点に限る比較も引用で未確認。 |
| 9.3.3.19 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：単独の準圏での Ind 延長と cocartesian fibration の述語はある。相対完備化した射影が cocartesian になる主張と、輸送への二濃度 Ind の適用の比較は見つからない。 |
| 9.3.3.20 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：対象ごとの Ind と関手延長はある。本文の輸送表現の四角形で、同じ底 C 上の相対完備化との自然同型を返す型は見つからない。 |
| 9.3.4.1 | partial → none |  | HasKappaFilteredElementsはpresheafのright unstraightening全体のfiltered性。原文は共変のcategory of elementsのcofiltered性で、反転した同じ積分との比較を引用に持たない。 |
| 9.3.4.5 | partial → none |  | HasKappaFilteredElementsはright unstraighteningのfiltered条件。原文の共変積分のcofiltered条件への反転比較を含まず、IsIndVertexのiffだけを同じflat性の主張としない。 |
| 9.3.4.7 | partial → none |  | HasKappaFilteredElementsはright unstraighteningのfiltered条件。原文の共変積分のcofiltered条件への反転比較と指定数値λ値圏への大きさの比較を含まず、IsIndVertexのiffだけを同じflat性の主張としない。 |
| 9.3.4.14 | partial → none |  | HasKappaFilteredElementsはright unstraighteningのfiltered条件。原文の共変積分のcofiltered条件への反転比較と指定数値λ値圏への大きさの比較を含まず、IsIndVertexのiffだけを同じflat性の主張としない。 |
| 9.3.4.15 | partial → none |  | elementsから標準commaへの同値と密度余錐はあるが、原文の指定λ-small性と元の全comma形状でのκ-filtered性を移す同じ比較を引用に含まない。 |
| 9.3.4.16 | partial → none |  | 型がfilteredとするのはsmallRightUnstraightening。原文が指定するC×_Chat Chat_/Xそのものへの比較とfiltered性の同値不変性を引用に揃えていない。 |
| 9.3.4.17 | partial → none |  | 宇宙パラメータのInd・空間・unstraighteningの型は、原文の指定数値κ・λ・μの値圏と同じ余極限・小性条件へ比較されていない。Ind_κ の各対象は C の小さい κ-filtered 図式の余極限。λ=∞（Ind_κ）の場合だけ。Mathlib は 1 圏版。 |
| 9.3.4.18 | partial → none |  | 宇宙パラメータのInd・空間・unstraighteningの型は、原文の指定数値κ・λ・μの値圏と同じ余極限・小性条件へ比較されていない。標準前層圏で各前層は小さい元の圏上の表現可能図式の余極限となる。任意の λ-余完備化 h の像から明示の λ-small な図式で表す型は見つからない。 |
| 9.3.4.19 | partial → none |  | 宇宙パラメータのInd・空間・unstraighteningの型は、原文の指定数値κ・λ・μの値圏と同じ余極限・小性条件へ比較されていない。各前層 F から小さい全空間と C への right fibration を構成する。任意の正則 λ の濃度制限と、全空間を取る関手が λ-余極限を保つ型は残る。 |
| 9.3.4.20 | partial → none |  | HasKappaFilteredElementsはright unstraighteningのfiltered条件。原文の共変積分のcofiltered条件への反転比較と指定数値λ値圏への大きさの比較を含まず、IsIndVertexのiffだけを同じflat性の主張としない。 |
| 9.3.4.21 | partial → none |  | HasKappaFilteredElementsはright unstraighteningのfiltered条件。原文の共変積分のcofiltered条件への反転比較と指定数値λ値圏への大きさの比較を含まず、IsIndVertexのiffだけを同じflat性の主張としない。 |
| 9.3.4.23 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の有限余極限を持つ生成圏では、集合値の Ind 前層であることと有限極限保存が同値。原文の一般の κ-flat 空間値関手で既存の κ-small 極限を保つ型は見つからない。 |
| 9.3.4.25 | partial → none |  | HasKappaFilteredElementsはright unstraighteningのfiltered条件。原文の共変積分のcofiltered条件への反転比較と指定数値λ値圏への大きさの比較を含まず、IsIndVertexのiffだけを同じflat性の主張としない。 |
| 9.3.4.26 | partial → none |  | HasKappaFilteredElementsはright unstraighteningのfiltered条件。原文の共変積分のcofiltered条件への反転比較と指定数値λ値圏への大きさの比較を含まず、IsIndVertexのiffだけを同じflat性の主張としない。 |
| 9.3.4.27 | partial → none |  | HasKappaFilteredElementsはright unstraighteningのfiltered条件。原文の共変積分のcofiltered条件への反転比較を含まず、IsIndVertexのiffだけを同じflat性の主張としない。 |
| 9.3.4.28 | partial → none |  | HasKappaFilteredElementsはright unstraighteningのfiltered条件。原文の共変積分のcofiltered条件への反転比較を含まず、IsIndVertexのiffだけを同じflat性の主張としない。 |
| 9.3.5.4 | partial → partial | component | PreservesFiniteColimitsは原文前半の通常圏のright exactという定義を直接与える。加法的な場合のexact sequenceによる同値とmonoへの限定は含まない。 |
| 9.3.5.5 | partial → none |  | 引用は通常圏のRepresentablyFlatについての型。原文の準圏のleft/right fibrationによるexact性やSpace値関手との同じ比較を含まず、通常圏での類似結果だけをpartialとしない。 |
| 9.3.5.6 | partial → none |  | 引用は通常圏のRepresentablyCoflatについての型。原文の準圏のleft/right fibrationによるexact性やSpace値関手との同じ比較を含まず、通常圏での類似結果だけをpartialとしない。 |
| 9.3.5.7 | partial → none |  | 引用は通常圏のLeftExactFunctorについての型。原文の準圏のleft/right fibrationによるexact性やSpace値関手との同じ比較を含まず、通常圏での類似結果だけをpartialとしない。 |
| 9.3.5.8 | partial → none |  | 引用は通常圏のpreservesFiniteColimits_iff_coflatについての型。原文の準圏のleft/right fibrationによるexact性やSpace値関手との同じ比較を含まず、通常圏での類似結果だけをpartialとしない。 |
| 9.3.5.9 | partial → none |  | 引用は通常圏のpreservesFiniteLimits_iff_flatについての型。原文の準圏のleft/right fibrationによるexact性やSpace値関手との同じ比較を含まず、通常圏での類似結果だけをpartialとしない。 |
| 9.3.5.10 | partial → none |  | 引用は通常圏のRepresentablyFlatについての型。原文の準圏のleft/right fibrationによるexact性やSpace値関手との同じ比較を含まず、通常圏での類似結果だけをpartialとしない。 |
| 9.3.5.15 | partial → none |  | 引用は通常圏のRepresentablyFlatについての型。原文の準圏のleft/right fibrationによるexact性やSpace値関手との同じ比較を含まず、通常圏での類似結果だけをpartialとしない。 |
| 9.3.5.17 | partial → none |  | 引用は通常圏のfinal_of_representablyFlatについての型。原文の準圏のleft/right fibrationによるexact性やSpace値関手との同じ比較を含まず、通常圏での類似結果だけをpartialとしない。 |
| 9.3.5.18 | partial → none |  | 引用は通常圏のof_isRightAdjointについての型。原文の準圏のleft/right fibrationによるexact性やSpace値関手との同じ比較を含まず、通常圏での類似結果だけをpartialとしない。 |
| 9.3.5.19 | partial → none |  | 右随伴の小極限保存は原文のκ-left exactのleft fibration引戻し条件と異なる結論。両条件の比較を型に持たない。 |
| 9.3.5.21 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：一点上の slice の後合成については全小余極限または小 κ-filtered 余極限を保つ型がある。κ-small な任意図式 G の上の slice で、κ-左完全性を移す型は見つからない。 |
| 9.3.5.22 | partial → none |  | 引用は通常圏のinstRepresentablyCoflatIndYonedaについての型。原文の準圏のleft/right fibrationによるexact性やSpace値関手との同じ比較を含まず、通常圏での類似結果だけをpartialとしない。 |
| 9.3.5.23 | partial → none |  | 引用は通常圏のpreservesFiniteLimits_of_flatについての型。原文の準圏のleft/right fibrationによるexact性やSpace値関手との同じ比較を含まず、通常圏での類似結果だけをpartialとしない。 |
| 9.3.5.25 | partial → none |  | 引用は通常圏のisIndObject_iff_preservesFiniteLimitsについての型。原文の準圏のleft/right fibrationによるexact性やSpace値関手との同じ比較を含まず、通常圏での類似結果だけをpartialとしない。 |
| 9.3.5.27 | partial → none |  | nativeの有限余極限保存にはhexという追加の交換入力があり、数値λのIndκλの対象との比較もない。通常圏Indの有限余極限保存は同じ∞圏の主張ではない。 |
| 9.3.5.28 | partial → none |  | 引用は通常圏のleftExactFunctorEquivalenceについての型。原文の準圏のleft/right fibrationによるexact性やSpace値関手との同じ比較を含まず、通常圏での類似結果だけをpartialとしない。 |
| 9.3.5.29 | partial → none |  | 引用は通常圏のleftExactFunctorEquivalenceについての型。原文の準圏のleft/right fibrationによるexact性やSpace値関手との同じ比較を含まず、通常圏での類似結果だけをpartialとしない。 |
| 9.3.5.30 | partial → none |  | 引用は通常圏のleftExactFunctorEquivalenceについての型。原文の準圏のleft/right fibrationによるexact性やSpace値関手との同じ比較を含まず、通常圏での類似結果だけをpartialとしない。 |
| 9.3.6.2 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：一濃度の Ind-Yoneda の回収同型つきの延長と、濃度を上げた accessibility はある。Indκ^λ の Indλ^μ から Indκ^μ への指定包含の延長を関手として作る型は見つからない。 |
| 9.3.6.3 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：単一の Ind の前層圏への包含は充満忠実。Ind の二段の濃度変更の指定推移関手の充満忠実性は見つからない。 |
| 9.3.6.4 | partial → none |  | B6型照合：Ind_κ(A) が μ-accessible ⇒ ある小さい B で Ind_μ(B) ≃ Ind_κ(A) までは得られる。推移性関手の同値の形はない。 原文と同じ対象・射・濃度条件の結論はこの引用型から直接得られない。 |
| 9.3.6.7 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：小さい冪等完備な生成準圏の場合に単一 κ の compact 対象を Yoneda 像で判定する。λ,μ の比較で小さい Ind の充満部分圏を compact 対象として同定する型は見つからない。 |
| 9.3.6.8 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：単一 κ の compact 対象の Yoneda 像の判定はある。λ-compact 対象を λ-small な κ-filtered 表示による Ind 部分圏と比較する型は見つからない。 |
| 9.3.6.10 | partial → none |  | 引用は通常圏のinstHasColimitsIndOfHasFiniteColimitsについての型。原文の準圏のleft/right fibrationによるexact性やSpace値関手との同じ比較を含まず、通常圏での類似結果だけをpartialとしない。 |
| 9.3.6.11 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：単一 κ の指定 Ind 左 Kan 拡張は小 κ-filtered 余極限を保つ。生成圏の h と H の κ での保存を上限 λ,μ の違いも含めて比較する三条件の iff は見つからない。 |
| 9.3.6.12 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：単一 κ の Ind 左 Kan 拡張による κ-filtered 余極限保存の型はある。両側の二濃度余完備性を仮定して Ind_{λ}^{μ}(F) と F の finitary 性を比較する型は見つからない。 |
| 9.3.7.1 | partial → partial | stronger-hyp | Cに終対象zがある場合、indYoneda_isTerminal_of_terminalのκ=ℵ0は同じInd(C)の終対象を直接返す。filtered性だけからの場合は含まない。 |
| 9.3.7.2 | partial → none |  | Cの終対象をIndへ送る型はあるが、原文のX=colim Fがその終対象となる同じ余極限の比較を引用に含まない。 |
| 9.3.7.4 | partial → none |  | 終対象⇒filteredは一般には直接使えるが、引用IndInfinityと原文の数値λのIndκλが同じ対象という比較がない。 |
| 9.3.7.5 | partial → partial | stronger-hyp | Cに終対象もあるとindYoneda_isTerminal_of_terminalは同じ標準Indκ(C)の終対象を直接返す。κ-filtered性だけを仮定する向きは含まない。 |
| 9.3.7.6 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：Ind の小 κ-filtered 余極限の存在はある。Ind 自体が κ または λ-filtered であることを元の C の κ-filtered 性と比較する三条件の iff は見つからない。 |
| 9.3.7.9 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：元の終対象を Ind-Yoneda が保つ型と、Ind 左 Kan 延長の filtered 余極限保存はある。任意の小 filtered C,D で、Ind(F) の終対象保存を元の F の右余終性で判定する型は見つからない。 |
| 9.3.7.10 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：任意の関手の右余終性を coslice の弱可縮性で判定する。Ind 上で得た各 coslice の弱可縮性を元の F の coslice へ反映する型は見つからない。 |
| 9.3.7.11 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：一つの Ind の終対象と関手の右余終性は別々に扱う。F と二濃度 Ind 延長の右余終性および終対象保存を比較する三条件の iff は見つからない。 |
| 9.3.7.12 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の終対象への定値関手が Final となる類例と、Ind の Yoneda による終対象保存はある。任意の F の右余終性とその Ind 延長による終対象保存の iff は見つからない。 |
| 9.3.7.13 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：一般の右余終性の coslice 判定はある。sharply below の下で元の F と二濃度 Ind 延長の右余終性を往復する型は見つからない。 |
| 9.4.1.1 | partial → partial | stronger-hyp | IsKappaAccessibleとIsKappaCompactGeneratingのfieldsは、κ=ℵ0で小さいcompact generator圏の存在も仮定し、同じCのκ-filtered余極限存在と各対象のcompact図式による表示を直接与える。原文の生成族全体に小ささを要求しない定義全体は含まない。 |
| 9.4.1.5 | partial → partial | stronger-hyp | IsKappaAccessibleとIsKappaCompactGeneratingのfieldsは、同じκで小さいcompact generator圏の存在も仮定し、同じCのκ-filtered余極限存在と各対象のcompact図式による表示を直接与える。原文の生成族全体に小ささを要求しない定義全体は含まない。 |
| 9.4.1.7 | partial → none |  | B6型照合：(κ,λ) 版はなし。λ=∞ かつ小さい生成圏の場合だけ。 原文と同じ対象・射・濃度条件の結論はこの引用型から直接得られない。 |
| 9.4.1.11 | partial → none |  | B6型照合：κ-accessible ⇔ ある小さい A で Ind_κ(A) ≃ C。λ=∞（Ind_κ）の場合だけ、C' 小。 原文と同じ対象・射・濃度条件の結論はこの引用型から直接得られない。 |
| 9.4.1.13 | partial → partial | stronger-hyp | Cが同じκでaccessibleという小さい生成圏の仮定も加えると、isKappaAccessible_iff_indEquivalenceが原文(2)の同じCのInd表示を直接返す。任意の大きさのcompact生成と(3)の全比較は含まない。 |
| 9.4.1.14 | partial → partial | stronger-hyp | Cが同じκ=ℵ0でaccessibleという小さい生成圏の仮定も加えると、isKappaAccessible_iff_indEquivalenceが原文(2)の同じCのInd表示を直接返す。任意の大きさのcompact生成と(3)の全比較は含まない。 |
| 9.4.1.17 | partial → partial | special | 標的Cを小準圏Aの標準Indκ(A)、数値λ制限のない全小κ-filtered形状に限ると、isKappaAccessibleFunctor_of_indHomTests_nativeのμ=κへ全compact対象のテストを特殊化して同じGの保存性を得る。任意二濃度の場合は含まない。 |
| 9.4.1.18 | partial → none |  | B6型照合：全単射としての主張はない。冪等完備 C ≃ Ind_κ(C)^κ と accessible ⇔ Ind_κ 同値の二つの半分（C 小、λ=∞（Ind_κ）の場合だけ）。 原文と同じ対象・射・濃度条件の結論はこの引用型から直接得られない。 |
| 9.4.1.19 | partial → partial | component | compactGenerationEquivalenceは、冪等完備な小さいCをIndκへ送りcompact対象の全部分圏へ戻したとき同じCを回収する同値を直接与える。全同値類への全単射の構成全体は含まない。 |
| 9.4.1.20 | partial → partial | component | compactGenerationEquivalenceのκ=ℵ0は、冪等完備な小さいCをIndκへ送りcompact対象の全部分圏へ戻したとき同じCを回収する同値を直接与える。全同値類への全単射の構成全体は含まない。 |
| 9.4.1.21 | partial → none |  | B6型照合：κ-accessible な Indκ(C) の構成と Yoneda の κ-compact 生成性。原文の三基数の関係と、C が冪等完備な場合の逆向きは未確認。 原文と同じ対象・射・濃度条件の結論はこの引用型から直接得られない。 |
| 9.4.1.22 | partial → none |  | B6型照合：κ ◁ μ で κ-accessible ⇒ μ-accessible の向きに関連するのみ。(κ,μ) の同値の判定はなし。 原文と同じ対象・射・濃度条件の結論はこの引用型から直接得られない。 |
| 9.4.2.1 | partial → partial | component | PreservesKappaFilteredColimitsのκ=ℵ0は同じFのfinitaryという定義の一成分を直接与える。compact対象を全てcompactへ送る一般条件とその全部分圏の構成は含まない。 |
| 9.4.2.2 | partial → partial | component | PreservesKappaFilteredColimitsは同じFのfinitaryという定義の一成分を直接与える。compact対象を全てcompactへ送る一般条件とその全部分圏の構成は含まない。 |
| 9.4.2.4 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：既存の関手の κ-accessibility は小 κ-filtered 余極限の保存であり、PrL は小余極限の保存を課す。κ≤λ における finitary 条件と compact 対象保存の両方を課した全部分圏は確認できない。 |
| 9.4.2.15 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：presentable 圏を集める構成と単独の κ-accessibility はある。原文の (κ,λ)-compactly generated 圏を対象とし、compact 対象も保つ関手を射にする QC の部分圏は未確認。 |
| 9.4.2.18 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：小 κ-filtered な半順序の κ-compact 図式から選んだ余極限頂点が μ-compact となる部分はある。三濃度での関手の compact 性、制限上の (κ,λ)-compact 性、余域生成を仮定した逆向きは見つからない。 |
| 9.4.2.19 | partial → none |  | B6型照合：一つの κ について小 κ-filtered 余極限を保つ関手の Ind 制限同値はある。冪等完備な D に対し、双方を λ から μ へ延長し、compact 対象も保つ関手に制限する同値は確認できない。 原文と同じ対象・射・濃度条件の結論はこの引用型から直接得られない。 |
| 9.4.3.1 | partial → partial | stronger-hyp | Cをℵ0-accessibleかつ全小余完備、部分圏をrepleteとし、その包含のℵ0-filtered余極限保存を与えるとreflectiveSubcategory_isKappaAccessibleは同じ部分圏のℵ0-accessibility、従ってcompact生成を返す。一般のcompact生成だけの場合は含まない。 |
| 9.4.3.4 | partial → none |  | B6型照合：(κ,λ)-compactly generated 版はなし。κ-accessible の反射部分圏の場合のみ。「(κ,λ)-compactly generated」の述語は SerrePositivity にない（κ-accessible のみ）。 原文と同じ対象・射・濃度条件の結論はこの引用型から直接得られない。 |
| 9.4.3.5 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：離散空間と同値である述語と、有限単体集合の Kan 置換を有限コードで表す宣言はある。任意の n に対する空間の n 切断、および有限な K からの (n+1)-連結な射との同値は確認できない。 |
| 9.4.3.6 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：離散空間の充満忠実な埋め込みと全空間の有限模型の生成圏を確認した。n 切断と本質的有限性の両方を課す S^{≤n}_fin という全部分圏は未確認。 |
| 9.4.3.9 | partial → none |  | 全Spaceでの有限generatorのcompact性は、原文のn-truncated部分圏内のcompact性やn-truncationとの比較を返さない。 |
| 9.4.3.10 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：ホモトピー圏と有限単体集合のコードは確認した。mapping space の局所 (n−1) 切断と K→C の (n+1)-圏論的連結性をつなぐ原文の二条件は未確認。 |
| 9.4.3.12 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：有限な単体集合のコードと、離散空間の述語を確認した。局所 (n−1) 切断で有限模型から来る準圏を選ぶ QC^{≤n}_fin の宣言は未確認。 |
| 9.4.3.13 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：空間の離散性と離散空間の充満忠実な表示はある。Kan 複体を準圏と見たとき、空間としての有限模型条件と局所切断による圏としての有限模型条件が一致する定理は未確認。 |
| 9.4.3.14 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：有限余極限のある一般の準圏で κ-コンパクト対象が有限余極限で閉じる結果は確認した。QC^{≤n} における有限模型の部分圏を同定する段がないため、原文の閉性はこの型から確認できない。 |
| 9.4.3.15 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：一般のコンパクト対象の閉性と空間側の有限模型はある。局所切断された圏における Δ¹ を含む最小の有限余極限閉部分圏の同定は未確認。 |
| 9.4.3.16 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：全空間のコンパクト生成と一般のコンパクト対象の有限余極限閉性を確認した。切断空間における有限模型の部分圏と、その圏で計算した有限余極限の閉性は未確認。 |
| 9.4.3.17 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：既存の空間の生成族は全ての有限単体集合の Kan 置換。原文が特定する Δ⁰ 一つからの有限余極限閉包を、S^{≤n}_fin と同定する結論は確認できない。 |
| 9.4.3.18 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：任意の準圏の冪等完備化は作れる。原文の二つの有限切断部分圏がそのまま冪等完備であることや、有限模型が retract を取っても存在することは未確認。 |
| 9.4.3.19 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：有限単体集合を定義域にした内部 Hom のアクセス可能性は確認した。局所切断圏の圏でのコンパクト性から有限模型を回収する向きも、その逆向きも確認できない。 |
| 9.4.3.20 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：全空間が有限単体模型で ℵ₀-アクセス可能になる結果はある。原文の n 切断空間および局所切断圏を、それぞれの有限模型の Ind 完備化とする二つの同定は未確認。 |
| 9.4.3.21 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：全空間のアクセス可能性と有限単体模型のコードを確認した。κ-小かつ n 切断という制約を持つ空間や準圏を、同じ基数で制限した Ind_{ℵ₀}^{κ} と同定する型は未確認。 |
| 9.4.4.1 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：コンパクトな図式を指定して作る slice 射影と、右ファイブレーションの厳密な filtered 余極限を調べた。任意の右ファイブレーションの全空間への (κ,λ)-compact 生成の移送、および射影による compact 性の両向きは未確認。 |
| 9.4.4.2 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：slice の余極限を射影の余極限から得る型と、指定した compact source slice の密度余錐はある。任意の図式上の slice の compact 生成と射影での compact 性判定は確認できない。 |
| 9.4.4.4 | partial → none |  | 引用は通常圏のisCardinalAccessibleCategoryについての型。原文の準圏のleft/right fibrationによるexact性やSpace値関手との同じ比較を含まず、通常圏での類似結果だけをpartialとしない。 |
| 9.4.4.6 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：同時に二脚の濃度別保存と compact 性を仮定した通常の引き戻しの accessibility はある。任意の向き付き引き戻しで、一方の脚だけが compact 対象を保つときの同じ κ での生成と両成分による compact 性判定は見つからない。 |
| 9.4.4.7 | partial → none |  | B6型照合：非可算な μ と小余完備性のもとで、小さい図式の各頂点と余錐頂点の μ-compact 性から coslice 内の compact 性を導く型がある。二濃度での coslice の compact 生成と compact 性の逆向きは確認できない。 原文と同じ対象・射・濃度条件の結論はこの引用型から直接得られない。 |
| 9.4.4.9 | partial → none |  | 全関手準圏のcompact性の型には追加のend familyが必要で、原文の二濃度compact生成・全頂点判定との比較を持たない。有限posetや小形状というだけでは同じ結論を直接得られない。 |
| 9.4.4.12 | partial → none |  | presentableであることは存在するある基数でのcompact生成を与えるが、原文の指定κ（9.4.4.12ではℵ0）でのcompact生成とcompact対象のiffを返さない。 |
| 9.4.4.13 | partial → none |  | presentableであることは存在するある基数でのcompact生成を与えるが、原文の指定κ（9.4.4.12ではℵ0）でのcompact生成とcompact対象のiffを返さない。 |
| 9.4.4.14 | partial → none |  | presentableであることは存在するある基数でのcompact生成を与えるが、原文の指定κ（9.4.4.12ではℵ0）でのcompact生成とcompact対象のiffを返さない。 |
| 9.4.4.15 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：選んだ部分複体への左ファイブレーションの引き戻しを使う比較と単射像の小ささはある。弱可縮な全空間から、同時に弱可縮かつ λ-small で、制限が左ファイブレーションとなる部分を選ぶ型は見つからない。 |
| 9.4.5.2 | partial → partial | stronger-hyp | pullback_isKappaAccessible_of_relativeCardinalsでμを原文のκとし、より小さい正則基数とのcardinal change bound、底のμ-accessibility、strict pullbackとequivalence liftingなど追加入力を置くと同じpullbackのμ-accessibilityを直接返す。一般のcategorical pullbackとcompact対象の逆向きは含まない。 |
| 9.4.5.4 | partial → none |  | pullback_isAccessibleの結論はある基数でのaccessible性。原文の指定(κ,λ)でのcompact生成とcompact対象判定ではなく、同じ濃度の結論が型にない。 |
| 9.4.5.7 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：空間の Kan ファイブレーション塔における極限と、二脚の引戻しの accessibility は確認した。κ₀-sequential 余極限を保つ compact な isofibration の塔で、逆極限の compact 生成および各段による判定を得る型は未確認。 |
| 9.4.5.8 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：二脚の引き戻しの accessibility と厳密な単体集合極限の filtered 余極限保存はある。可算 isofibration 塔の準圏極限に同じ κ の compact 生成を与え、各段で compact かどうかで判定する型は見つからない。 |
| 9.4.5.9 | partial → none |  | pullback_isAccessibleの結論はある基数でのaccessible性。原文の指定(κ,λ)でのcompact生成とcompact対象判定ではなく、同じ濃度の結論が型にない。 |
| 9.4.5.10 | partial → none |  | pullback_isAccessibleの結論はある基数でのaccessible性。原文の指定(κ,λ)でのcompact生成とcompact対象判定ではなく、同じ濃度の結論が型にない。 |
| 9.4.5.11 | partial → none |  | pullback_isAccessibleの結論はある基数でのaccessible性。原文の指定(κ,λ)でのcompact生成とcompact対象判定ではなく、同じ濃度の結論が型にない。 |
| 9.4.6.1 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：単独の準圏に対する生成関手の述語と任意の底変換はある。内ファイブレーションを各標準単体へ引き戻した全空間に、ℵ₀-compact 生成を要求する述語は未確認。 |
| 9.4.6.2 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：単独の準圏の κ-accessibility と指定二脚の引き戻しを扱う宣言はある。内ファイブレーションを任意の Δⁿ 上に引き戻して κ-compact 生成を要求する述語は見つからない。 |
| 9.4.6.4 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：濃度変更を使う指定引き戻しの定理はある。引き戻しをすべての Δⁿ 上で取り、その各全空間に (κ,λ)-compact 生成を要求する定義は見つからない。 |
| 9.4.6.8 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：余カルテシアンな辺での輸送と二脚の引戻しの accessibility はある。全単体上の compact 生成を、頂点ファイバーと Δ¹ 上の始点包含の finitary 性・compact 保存だけで特徴付ける型は未確認。 |
| 9.4.6.9 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：単独の Ind の κ-compact 生成と compact 部分の冪等完備化はある。底上で U を U₀ の相対 Ind とする条件と、U₀ を各ファイバーの compact 対象から選ぶ構成は未確認。 |
| 9.4.6.10 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：大域的なカルテシアン・ファイブレーションから反変輸送を作れる。局所的な射に対し、その各輸送の (κ,λ)-finitary 性とファイバーの生成が全単体での生成と同値になる結論は未確認。 |
| 9.4.6.11 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：大域的な余カルテシアン射の輸送関手を確認した。局所余カルテシアンな場合に、各輸送の (κ,λ)-compact 性とファイバーの生成を全単体での生成と結ぶ同値は未確認。 |
| 9.4.6.12 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：任意の射の切断を相対関手空間で表す構成と、固定標的への関手の点ごとの余極限および条件付き compact 性はある。変動ファイバーでの切断の余完備性、点ごとの compact 性、切断圏の相対 Ind の充満忠実性は未確認。 |
| 9.4.6.13 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：小さい生成モデルと一つの圏の Ind 比較を確認した。κ₀-sequential 余極限を使い、切断が compact 部分を経由することを compact 性と同値にし、その切断圏を相対 Ind と同定する定理は未確認。 |
| 9.4.6.14 | partial → none |  | 全関手準圏のcompact性の型には追加のend familyが必要で、原文の二濃度compact生成・全頂点判定との比較を持たない。有限posetや小形状というだけでは同じ結論を直接得られない。 |
| 9.4.6.16 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：固定形状の余カルテシアン切断の準圏性と、通常圏の重み付き切断関手の filtered 余極限保存を確認した。コンパクトなファイバーへの因子化と切断の compact 性の同値、さらに相対 Ind 同値は未確認。 |
| 9.4.6.17 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：二脚の引戻しの accessibility と厳密な単体集合極限の交換はある。任意の κ-小図式の QC での極限を同じ二濃度で compact 生成し、各評価で compact 性を特徴付ける型は未確認。 |
| 9.4.6.20 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：Ind の制限の普遍性と厳密な単体集合極限の交換を確認した。逐次余極限を保存する関手からなる QC 部分圏上で、相対 Ind_{κ}^{λ} が κ-小極限を保存する宣言は未確認。 |
| 9.4.7.2 | partial → partial | component | isKappaAccessible_iff_indEquivalenceは小さいAからの同じCのIndκ表示という条件(1)の実現を直接与える。essentially smallへの拡張とcompact対象全体の小性を含む全同値は含まない。 |
| 9.4.7.3 | partial → partial | component | indInfinity_isKappaAccessibleは同じ小さい冪等完備CをIndκへ送った圏のκ-accessibilityを直接返す。全同値類の単射・全射の両方はこの引用だけでは含まない。 |
| 9.4.7.5 | partial → partial | stronger-hyp | κ⊴λを指数によるIsCardinalChangeBound κ λへ強めるとof_cardinalChangeBoundは同じCのλ-accessibilityを直接返す。任意の非厳密sharply条件の場合は含まない。 |
| 9.4.7.6 | partial → partial | stronger-hyp | ℵ0<κを満たす正則κについてIsCardinalChangeBound ℵ0 κも入力すると、of_cardinalChangeBoundは同じℵ0-accessibleなCのκ-accessibilityを直接返す。正則性だけからこの追加入力を得たとはしない。 |
| 9.4.7.7 | partial → partial | component | IsKappaAccessibleのκ-filtered余極限存在とfiltered性の基数単調性により、同じCの全小λ-filtered余極限存在という前半を直接得る。λ-compact対象全体の小性は含まない。 |
| 9.4.7.18 | partial → partial | stronger-hyp | 各Ciをpresentableにも強めるとpiSSet_isPresentableの同じ小積はpresentable、従ってaccessibleである。単にaccessibleな因子の場合は含まない。 |
| 9.4.7.19 | partial → partial | component | IsKappaAccessibleの定義とisAccessibleから、同じCのκ-accessible⇒accessibleという右辺一成分を直接得る。compact生成を併せた全右辺と逆向きは含まない。 |
| 9.4.7.20 | partial → none |  | Indκ(A)がaccessibleかつ冪等完備という型は、原文の本質的小さい同じC自体のiffではない。compact部分圏をwhole Indと同一視しない。 |
| 9.4.7.21 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の κ-filtered 性を nerve に移す型はある。大きな半順序 Q も許して N(Q) の accessibility と Q の小ささを結ぶ iff は見つからない。 |
| 9.4.7.22 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：通常の集合の余極限における成分からの代表元と、集合を小部分集合の余極限で書く結果を調べた。λ-directed 性を使い、各項が κ 未満なら余極限全体も κ 未満とする濃度評価は未確認。 |
| 9.4.7.23 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：小空間の余極限を取る関手と、κ-small な始域から余極限への写像の因数分解はある。λ-filtered 図式の頂点に課したより小さい本質的 κ-small 性が余極限で保たれる型は見つからない。 |
| 9.4.7.24 | partial → none |  | compactIndYonedaはInd内のcompact対象の部分圏への射であり、原文のwhole Indλμへの同じhではない。 |
| 9.4.7.25 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：指定された図式の retract に余極限を移す補題と Ind の小 κ-filtered 余極限存在はある。本質的 λ-small・局所 κ-small な任意の冪等完備 C の λ-filtered 余極限の存在と、任意の関手による保存は見つからない。 |
| 9.4.8.8 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：圏と関手それぞれの accessibility、および一つの具体的な部分圏の頂点同型に関する述語はある。replete 性、部分圏の accessibility、包含の accessibility を任意の部分圏について束ねる定義は未確認。 |
| 9.4.8.9 | partial → partial | stronger-hyp | Cを全小余完備にも強め、同じreplete反射部分圏の包含がある固定κのfiltered余極限を保存するとreflectiveSubcategory_isKappaAccessibleはその部分圏のκ-accessibilityを返す。原文(4)⇒(2)のこの場合に一致する。 |
| 9.4.8.11 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：対象を presentable に、射を小余極限保存または accessible な小極限保存の条件で絞った構成と、単独の accessible 関手の述語はある。固定された強到達不能濃度で全 accessible 準圏と全 accessible 関手を集めた QC^Acc の構成は見つからない。 |
| 9.4.8.12 | partial → partial | component | exists_common_accessibilityCardinalを同じ二圏へ適用すると、同じ共通λでのaccessibilityを直接返す。Fiが全λ-compact対象を保存する成分は含まない。 |
| 9.4.8.15 | partial → partial | component | exists_common_accessibilityCardinalを同じ二圏の小さい全族へ適用すると、同じ共通λでのaccessibilityを直接返す。Fiが全λ-compact対象を保存する成分は含まない。 |
| 9.4.8.17 | partial → partial | stronger-hyp | 標的を小準圏AのIndκ、全表現可能Homテストが共通の正則μでfiltered余極限を保存することも追加すると、isKappaAccessibleFunctor_of_indHomTests_nativeは同じFのμ-accessibilityを返す。対象ごとに異なる基数しかない場合は含まない。 |
| 9.4.9.1 | partial → partial | stronger-hyp | Cをpresentable、Kを小準圏にも強めるとfunctor_isPresentableは同じFun(K,C)のpresentability、従ってaccessibilityを直接返す。任意KとaccessibleだけのCは含まない。 |
| 9.4.9.4 | partial → none |  | 通常圏Commaのaccessible性と∞圏Arrowのpresentabilityは、原文の指定二関手のoriented fiber productと同じ対象への比較を含まない。 |
| 9.4.9.6 | partial → none |  | 通常圏のOver/StructuredArrowのaccessible性は、原文の∞圏の指定slice/cosliceへのnerve比較を含まない。 |
| 9.4.9.9 | partial → partial | stronger-hyp | 一方の脚pがequivalence liftingであり、homotopy fiber productを同じstrict pullback模型で与えるとpullback_isAccessibleが同じ全空間のaccessibilityを直接返す。任意に指定された模型への輸送は含まない。 |
| 9.4.9.11 | partial → partial | component | 片脚equivalence liftingのstrict pullback模型ではpullback_isAccessibleと射影のκ-accessibilityから同じ全空間と二射影のaccessibilityを得る。任意の指定categorical pullbackへの比較とTのiffは含まない。 |
| 9.4.9.12 | partial → partial | stronger-hyp | 逆像をstrict pullbackで取り、Fにequivalence liftingを追加するとpullbackのaccessible性と射影の保存性は同じ逆像部分のaccessibly embedded条件を直接返す。一般のFは含まない。 |
| 9.4.9.13 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：片脚に同値持ち上げを課した二つの accessible 関手の引き戻しの accessibility はある。accessibly embedded な任意の小族の共通部分と、元の C への包含が accessibly embedded であることを一緒に与える型は見つからない。 |
| 9.4.9.14 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：空間に限った 0 切断とその充満忠実な表示はある。任意の accessible 準圏で n 切断対象を選ぶ構成と、包含および部分圏そのものの accessibility は未確認。 |
| 9.4.9.15 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：二脚の引戻しで得る圏の accessibility と、厳密な単体集合の交換定理を確認した。accessible 圏・関手の QC 部分圏の任意の小極限、および QC_{≤Ω} への包含での保存は未確認。 |
| 9.4.9.16 | none → own |  | 同じinner fibration Uについて∀n, ∀σ:Δ[n]⟶C, IsAccessible (pullback σ U)という既存の型の全称量化が原文の定義全体に一致する。引戻しの準圏性は標準単体の準圏性とinner fibrationの底変換から得る。 |
| 9.4.9.19 | none → own |  | 同じinner fibration Uについて∀n, ∀σ:Δ[n]⟶C, IsKappaAccessible κ (pullback σ U)という既存の型の全称量化が原文の定義全体に一致する。引戻しの準圏性は標準単体の準圏性とinner fibrationの底変換から得る。 |
| 9.4.9.23 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：一つの κ-accessible 準圏の compact 生成モデルと、小さい compact source slice はある。内ファイブレーション全体での四条件、特に各ファイバーの compact 頂点を集めた制限の本質的小ささとの比較は未確認。 |
| 9.4.9.25 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：二脚引戻しの accessibility とカルテシアン辺の輸送を確認した。Δ¹ 上だけの accessibility から任意の Δⁿ 上の accessibility を導く iff は未確認。 |
| 9.4.9.26 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：大域的なカルテシアン射の反変輸送と、指定 κ の余極限保存述語はある。局所カルテシアン射で、各輸送の κ-finitary 性と頂点ファイバーの条件が全単体上の κ-accessibility と同値になる型は未確認。 |
| 9.4.9.27 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：大域的な反変輸送の持ち上げと、二脚の accessible 関手に共通濃度を選ぶ結果はある。任意の局所カルテシアン射について各ファイバーと各輸送の accessibility から全単体上の accessibility を得る比較は未確認。 |
| 9.4.9.28 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：余カルテシアン辺の共変輸送、compact 生成、および余極限保存は個別にある。局所余カルテシアン射における、輸送の κ-compact 性とファイバーの κ-accessibility による全単体の判定は未確認。 |
| 9.4.9.29 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：共変の辺輸送とそのホモトピー圏での計算を確認した。各ファイバーと各輸送が濃度を固定せず accessible であることと、全単体上の accessibility の iff は未確認。 |
| 9.4.9.32 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：相対関手空間と通常圏での重み付き切断関手の余極限保存はある。小さい底の上の内ファイブレーションに逐次余完備性を課して、全切断圏の λ-accessibility を得る型は未確認。 |
| 9.4.9.33 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：切断の相対関手空間、二脚引戻しの accessibility、左ファイブレーションの切断比較を確認した。任意の小さい底上の edgewise accessible な内ファイブレーションの全切断圏の accessibility は未確認。 |
| 9.5.1.1 | partial → partial | direction | accessibleかつcocompleteはIsPresentableの定義そのもので、hasSmallLimitsは同じCの完備性を直接返す。complete⇒cocompleteは含まない。 |
| 9.5.1.8 | partial → partial | direction | IsPresentableの同じCと同じFにpresentableContinuous_isRepresentableを適用して小極限保存⇒表現可能を直接得る。逆向きはこの引用に含まない。 |
| 9.5.1.9 | partial → partial | direction | accessible_preservesLimits_isCorepresentableは同じC,Fについてaccessibleかつ全小極限保存⇒corepresentableを直接返す。逆向きは含まない。 |
| 9.5.1.11 | partial → none |  | 固定宇宙の全小極限保存による表現定理は、原文の指定数値λ,μでの保存・小性と指定compact対象による表現の同じ条件に比較されていない。 |
| 9.5.1.12 | partial → partial | stronger-hyp | Cをpresentableにも強め、Kを宇宙小形状に限るとhasSmallLimitsの同じKへの適用が原文の同じCのK極限の存在を直接返す。二濃度の入力だけの場合は含まない。 |
| 9.5.1.13 | partial → none |  | 固定宇宙の全小極限保存による表現定理は、原文の指定数値λ,μでの保存・小性と指定compact対象による表現の同じ条件に比較されていない。 |
| 9.5.2.2 | partial → partial | stronger-hyp | Dをaccessibleにも強め、presentableなCからの全連続前層の表現定理をhRepへ入れると、native判定は同じFの右随伴存在と全小余極限保存のiffを直接返す。Dをpresentableとする必要はなく、局所小だけの場合は含まない。 |
| 9.5.2.3 | partial → partial | component | Dをpresentableとする原文の仮定の下でrightAdjoint_isAccessibleとadjunction_preservesSmallLimitsは同じGの左随伴存在⇒accessibleかつ小極限保存を直接与える。引用のiffが要求するCのpresentabilityは逆向きに限る追加入力。 |
| 9.5.2.5 | partial → none |  | 全小余極限/極限保存による随伴判定は、原文の指定λ-small保存と指定写像空間のλ-small性という同じ二条件のiffではない。 |
| 9.5.2.6 | partial → none |  | 全小余極限/極限保存による随伴判定は、原文の指定λ-small保存と指定写像空間のλ-small性という同じ二条件のiffではない。 |
| 9.5.3.5 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：単独の presentable 圏と、大域的な余カルテシアン射の輸送および小余極限保存はある。任意の局所余カルテシアン射の全ファイバー・全輸送に原文の条件を束ねる述語は未確認。 |
| 9.5.3.7 | partial → none |  | 固定された二つのpresentable圏の随伴存在判定は、原文のUのlocally cartesian/cocartesian性とその輸送関手への同一視を型に含まない。 |
| 9.5.3.8 | partial → none |  | PrL/PrRの構成と固定二対象の随伴同値は、原文の指定Uの輸送表現の因数分解とファイブレーション性の四条件を結ぶ型ではない。 |
| 9.5.3.9 | partial → none |  | 固定二対象のpresentableAdjointFunctorEquivalenceは、原文の準圏そのものを動かす全PrLop→PrRの指定Ψとは別の射。 |
| 9.5.4.1 | partial → none |  | generatedSourceCategoryのpresentabilityは、指定slice/coslice準圏全体との同一視を引用に持たない。通常Overのaccessible性も別の模型。 |
| 9.5.4.2 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：Mathlib には通常圏の普遍余極限と指数可能性の述語があり、厳密な単体集合の slice には右随伴がある。presentable な準圏で局所カルテシアン閉性と全・小普遍余極限を同値にする型は未確認。 |
| 9.5.4.3 | partial → partial | special | Kを小準圏に限るとfunctor_isPresentableが同じFun(K,C)のpresentabilityを直接返す。任意の単体集合Kは含まない。 |
| 9.5.4.4 | partial → none |  | Arrow(C)のpresentabilityは原文の指定F−,F+のoriented fiber productとの比較を持たない。恒等の特殊化でも指定模型との比較が未確認。 |
| 9.5.4.6 | partial → partial | special | 両脚cocontinuous、一方equivalence lifting、strict pullback模型に限りpullback_isAccessibleを入力してisPresentable_of_isAccessibleを適用すると同じ全空間のpresentabilityを直接得る。continuous側と任意の指定模型は含まない。 |
| 9.5.4.7 | partial → none |  | 積・pullback・関手準圏のpresentabilityを、原文の指定QC内の一般図式の極限と同一視する型を引用に持たない。各構成を組む議論だけをpartialとしない。 |
| 9.5.4.10 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：二脚の補題は余極限を保つ脚を要求し、strict な単体集合の小極限の補題は filtered 余極限との交換までを与える。小さい任意形状の accessible な極限保存関手の図式の極限が presentable となる型は見つからない。 |
| 9.5.4.12 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：PrL・PrR の模型と個別の積・引戻しの presentability を確認した。これらは PrL・PrR 内の任意の小極限も、QC_{≤Ω} への包含での保存も与えない。 |
| 9.5.4.13 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：PrL・PrR の準圏模型と単独の presentable 圏の小極限存在はある。PrL と PrR 自体への小余極限の存在を与える型は見つからない。 |
| 9.5.4.17 | partial → none |  | 全関手準圏のpresentabilityと評価保存は、原文のUのsection準圏と同じものへの比較がない。積束に限るだけで同じ指定対象と数えない。 |
| 9.5.4.19 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：余 cartesian 切断の部分空間と coslice の κ-filtered 余極限はある。各頂点が presentable で辺ごとに accessible な局所 (co)cartesian ファイブレーションの切断圏を presentable とする型は見つからない。 |
| 9.5.5.1 | partial → own |  | 同じCのIsPresentable CとIsKappaAccessible κ Cの論理積が原文のκ-presentableの定義全体を直接表す。専用名がないことは不足としない。 |
| 9.5.5.3 | partial → none |  | isPresentable_iff_cocompleteIndEquivalenceはある基数の存在であり、原文の指定κに固定した小さいκ余完備な生成圏の表示を返さない。 |
| 9.5.5.5 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：一濃度の Ind の制限同値と前層余完備化への左 Kan 延長を確認した。κ-余完備化を相対 Ind_{κ}^{λ} に入れた合成が λ-余完備化になる主張は未確認。 |
| 9.5.5.6 | partial → none |  | Indのκ-filtered余極限存在だけでは指定λ-small全余極限存在は出ない。通常圏Indの全余極限存在はnerve比較なし。 |
| 9.5.5.7 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：コンパクト対象の有限余極限閉性と小準圏形状での結果はある。二濃度の生成のもとで C の λ-余完備性、κ-余完備性、compact 部分の κ-余完備性を相互に導く型は未確認。 |
| 9.5.5.8 | partial → partial | special | κ=ℵ0としCが有限余極限を持つ場合、hasFiniteColimits_kappaCompactObjectsは同じcompact対象部分圏の有限余極限存在、すなわち(2)⇒(3)を直接返す。全iffと任意κは含まない。 |
| 9.5.5.9 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：Ind-Yoneda に沿う左 Kan 延長が小 κ-filtered 余極限を保つ型はある。原文が比較する元の f と拡張 F の κ・λ 右完全性は異なる形状の条件であり、その三条件の同値は未確認。 |
| 9.5.5.10 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：小余極限保存から κ-filtered 保存への含意と、Ind 延長の同種の保存を確認した。元の f の κ-小余極限保存から F の λ-小な全余極限保存を導く、二濃度の iff は未確認。 |
| 9.5.5.11 | partial → none |  | Indのκ-filtered余極限保存関手の制限同値は、原文の全λ-small余極限保存関手への同じ制限ではない。 |
| 9.5.5.12 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：空間の 0 切断、有限模型による全空間の生成、全関手圏の presentability を確認した。S^{≤n}_fin 上の有限余極限保存関手の Δ⁰ 評価の充満忠実性と n-余切断対象による本質像は未確認。 |
| 9.5.5.13 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：小余極限保存が κ-filtered 保存を含む向きはある。二濃度で、finitary 性と compact 部分の κ-余連続性から任意の λ-小余極限保存を復元する向きは未確認。 |
| 9.5.5.14 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：一濃度の Ind の制限同値と compact 生成モデルはある。原文の C の λ-余連続関手を C_{<κ} 上の κ-余連続関手へ送る、全ての小形状に関する制限同値は未確認。 |
| 9.5.5.15 | partial → partial | special | Cを標準Indκ(A)に限り同じFが左Kan拡張である場合、indLeftKanExtension_preservesSmallKappaFilteredColimitsは原文右辺の同じFのκ-finitary成分を直接返す。compact部分への保存条件と全iffは含まない。 |
| 9.5.5.16 | partial → none |  | PrLFunctorSpaceの準圏性と全Fun(K,D)のpresentabilityは、cocontinuous全部分圏自身のpresentabilityを返さない。 |
| 9.5.5.17 | partial → partial | component | IsPresentableの同じCの局所小性と全小余極限存在は原文の右辺(a)(b)を直接返す。小生成族の全余極限生成と全対象のcompact基数はこの引用だけでは含まない。 |
| 9.5.5.18 | partial → partial | special | 数値λ制限のない標準Indκの小始域の場合、indComparison_isFullyFaithful_of_compactは同じhのκ-finitary拡張Hの充満忠実性を直接返す。全λ-small余極限閉包としての像の判定は含まない。 |
| 9.5.5.19 | partial → none |  | κ-filtered生成によるInd比較は指定λ-small全余極限生成と数値λの同じ完備化に比較されていない。 |
| 9.5.5.21 | partial → partial | component | κ-presentableのpresentable成分から同じCの局所小性と余完備性(a)(b)が直接得られる。小κ-compact族による全小余極限生成を含む全iffは含まない。 |
| 9.5.5.22 | partial → partial | stronger-hyp | κ≤λをIsCardinalChangeBound κ λへ強めると同じCのκ-accessibilityをλ-accessibilityへ移せる。元のpresentabilityと論理積にして同じCのλ-presentabilityを得る。任意の基数比較は含まない。 |
| 9.5.6.1 | partial → partial | special | FをrepleteなReflectiveSubcategoryのreflectorに限り、始域・その部分圏のIsPresentableを課すと、その構造の随伴と充満包含は原文の同じFのBousfield条件を直接表す。任意のFによる定義全体は含まない。 |
| 9.5.6.2 | partial → partial | direction | 同じ反射のreflectorには随伴による余極限保存とisLocalizationがあり、原文のBousfield⇒(1)(2)を直接返す。逆向きは含まない。 |
| 9.5.6.9 | partial → partial | component | IsReflectiveSubcategoryは同じ部分圏に要求する定義のreflective成分を直接与える。accessibly embedded成分と併せた全定義はこの引用だけでは含まない。 |
| 9.5.6.15 | partial → partial | component | 部分圏をrepleteにも強めればreflective_mem_limitConeは同じ部分圏の小極限閉性という右辺一成分を直接返す。accessibilityと逆向きは含まない。 |
| 9.5.6.19 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：辺の集合に関する局所対象の presentability と accessible な引戻しの結果はある。連続 accessible な G の逆像が反射部分圏になるための左随伴まで組み立てる型は未確認。 |
| 9.5.6.20 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：局所対象の presentability と随伴間の変換の同値はある。任意の二つの連続 accessible な関手間の α が可逆な頂点の全部分圏が Bousfield 局所化となる結果は未確認。 |
| 9.5.6.21 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：一組の辺に対する局所対象と生成辺の増加に対する反単調性はある。任意の小族の反射部分圏の共通部分を、共通の生成辺集合で表して局所化する型は未確認。 |
| 9.5.7.2 | partial → none |  | IsLocalizationの前合成は全関手準圏の型。原文の両側のcocontinuous全部分圏へ同じ射を制限した充満忠実性・像との比較を引用に持たない。 |
| 9.5.7.5 | partial → partial | component | 小さい同じWからbousfield_isReflectiveSubcategoryとbousfieldLocalObjects_isPresentableによりW-local部分圏の反射性とaccessibilityを得る。包含のaccessibilityは別入力なので右⇒左の全体ではなく反射性・部分圏のaccessibilityの成分。 |
| 9.5.7.6 | partial → none |  | IsLocalizationの全関手圏への前合成の充満忠実性は、原文のPrLの指定写像空間の(-1)-truncated比較と直接同じ型ではない。 |
| 9.5.7.8 | partial → partial | direction | W-local部分圏のpresentability、presheaf_isPresentableと同値不変性から、原文のそのような小K,Wの表示が存在⇒Cがpresentableを直接得る。一般反射を小Wで表す逆向きは含まない。 |
| 9.5.7.10 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：指定の生成辺による反射局所化と、辺を反転する関手の延長はある。任意の余連続 H に対し、延長が保存的かつ余連続である形の分解をまとめる型は未確認。 |
| 9.6.0.1 | partial → partial | component | 通常圏のIsWeakFactorizationSystemのfieldsは同じ左右クラスの因数分解とLLPを与える。原文がさらに要求する持ち上げの一意性は含まない。 |
| 9.6.1.1 | partial → none |  | 通常圏の持ち上げ・超限合成・因数分解の型は、原文の準圏内の指定2単体・3単体の持ち上げや∞余極限との比較を含まない。Mathlib の通常圏では整列形状の極限段の余極限と後続射の W 所属を記録し、始点同型と余錐で合成射を指定する。準圏における指定された閉順序数の神経による構成は未確認。 |
| 9.6.1.3 | partial → none |  | 通常圏の持ち上げ・超限合成・因数分解の型は、原文の準圏内の指定2単体・3単体の持ち上げや∞余極限との比較を含まない。通常圏の整列形状を指定する超限合成と、順序数の区間の濃度評価はある。一般の準圏で α<κ を条件にする超限合成とその閉性の述語は未確認。 |
| 9.6.1.4 | partial → partial | component | Ordinal.enumは同じ整列集合Aとその順序型の初切片との順序保存全単射を直接与える。原文のnerveと右joinの同型および超限合成の条件の全比較は含まない。 |
| 9.6.1.10 | partial → none |  | 通常圏の持ち上げ・超限合成・因数分解の型は、原文の準圏内の指定2単体・3単体の持ち上げや∞余極限との比較を含まない。通常圏では恒等・合成・同型に関する閉性と整列形状の射圏余極限から、超限合成の閉性を得る。原文の非可算正則 κ で制限した準圏 Fun(Δ¹,C) における閉性は未確認。 |
| 9.6.1.12 | partial → none |  | 通常圏の持ち上げ・超限合成・因数分解の型は、原文の準圏内の指定2単体・3単体の持ち上げや∞余極限との比較を含まない。Mathlib では通常圏の同型射について超限合成の閉性をインスタンスで得る。準圏では可逆辺の有限合成を調べたが、任意の順序数の連続図式での閉性は未確認。 |
| 9.6.1.13 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の超限合成の下限・上限と、準圏で余極限・二対三を課す別の強飽和閉包を確認した。任意の準圏の κ-小超限合成だけについて最小な閉包を与える宣言は未確認。 |
| 9.6.1.16 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の上限性は既に超限合成で閉じた標的を要求する。別の強飽和閉包には冪等性があるが、恒等射を含む W の κ-小超限合成を再合成して同じ形に平坦化する型は未確認。 |
| 9.6.1.17 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：自然数列の spine の内アノダイン性と薄い圏の神経への外延性はある。一般の線形順序の隣接端点条件で定義した K(A,B) の包含の圏同値は未確認。 |
| 9.6.1.18 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：整列形状の順序同型による添字変更と W の単調性はある。非同型の合成射を保ったまま同型な後続射を全て削る別の形状への縮約は確認できない。 |
| 9.6.1.19 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の全整列形状での合成と準圏での別の最小閉包を確認した。κ-小閉包の元を同型か指定 W の一つの κ-小超限合成に分類する iff は未確認。 |
| 9.6.2.1 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の持ち上げで終対象への射を使うと射の延長を表せる。原文は終対象の仮定を置かず、各 w の Hom 写像の全射性を弱い局所性と呼ぶ。既存の通常圏の isLocal は全単射の条件であり、この弱い述語は未確認。 |
| 9.6.2.5 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：局所対象の既存の述語は前合成の写像空間の同値を課す。原文の各 f に対して三角形を延長できればよい弱い局所性を独立に課す型は未確認。 |
| 9.6.2.12 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：射圏の retract という通常圏側の概念と、準圏で余錐の普遍性を retract へ移す定理はある。弱い局所性と強い局所性を Fun(Δ¹,C) 内の辺の retract で移す型は未確認。 |
| 9.6.2.13 | partial → partial | stronger-hyp | 同じwについてXをstrongly localにも強めるとisLocalForHom_pushout_right_of_leftが同じpushout射w′のstrong localityを返すのでweak localityを得る。weak localityだけの入力ではない。 |
| 9.6.2.14 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：局所対象の写像空間での条件とその pushout 版はある。相対余対角が W に残るという仮定だけで弱い局所性から同値性を導く原文の iff は未確認。 |
| 9.6.2.16 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏では左持ち上げクラスが超限合成で閉じる。原文の準圏の三角形延長だけで定めた X に対する弱い局所射のクラスが閉じる型は未確認。 |
| 9.6.3.1 | partial → none |  | 通常圏の持ち上げ・超限合成・因数分解の型は、原文の準圏内の指定2単体・3単体の持ち上げや∞余極限との比較を含まない。通常圏で W の pushout 射を作り、そのクラスの超限合成を取る定義がある。準圏における pushout と κ-小な形状に制限した超限合成での対応は未確認。 |
| 9.6.3.3 | partial → partial | component | exists_bousfieldLocalReplacementは同じ小WとXに対しX→YとW-local（従ってweakly local）なYを直接返す。射がgeneratedEdgesに属する条件はあるが、指定超限pushoutであるという比較は含まない。 |
| 9.6.3.6 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の余積と pushout を使う超限合成の持ち上げ結論を確認した。準圏の指定図式の余極限による一斉付加を個別 pushout の λ-小超限合成にする型は未確認。 |
| 9.6.3.7 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の小対象論法の後続段と準圏の強飽和局所置換を確認した。hC の λ-小な Hom 類を一斉に付加し、原文の全ての正方形を与える λ-小超限 pushout は未確認。 |
| 9.6.3.8 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の整列連続性と反射の特定の超限列はある。始点と任意の U の各頂点での後続射だけを与えて、準圏内に指定 α までの連続列を作る一般形は未確認。 |
| 9.6.3.9 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：小さい辺族の局所対象を作る presentable 版と、通常圏の超限合成の持ち上げ結論はある。λ-余完備性と κ-コンパクトな始域を使い、指定 λ の範囲内で弱い局所対象への射を元の W の超限 pushout にする型は未確認。 |
| 9.6.3.10 | partial → partial | stronger-hyp | Cをpresentable、Wを宇宙小族にも強めるとbousfield_isReflectiveSubcategoryは同じW-local部分圏のreflectivityを直接返す。指定λでの生成辺集合の等式全体は含まない。 |
| 9.6.3.12 | partial → none |  | 局所化による全関手の延長存在と充満忠実性は、原文のcocontinuousな両部分圏への同じ制限の比較を含まない。 |
| 9.6.4.1 | partial → none |  | 通常圏の持ち上げ・超限合成・因数分解の型は、原文の準圏内の指定2単体・3単体の持ち上げや∞余極限との比較を含まない。通常圏の可換正方形と解の構造はある。CatInfinity では四面体から合成の正方形を読む別の宣言があるが、任意の準圏で Δ¹×Δ¹ の指定の頂点配置を Δ³ へ延長する形の定義は未確認。 |
| 9.6.4.3 | partial → none |  | 通常圏の持ち上げ・超限合成・因数分解の型は、原文の準圏内の指定2単体・3単体の持ち上げや∞余極限との比較を含まない。通常圏の正方形の解は対角射と二つの合成の等式を持つ。準圏で二面に加えてそれらを貼る 3 単体を指定する原文の解データは未確認。 |
| 9.6.4.8 | partial → none |  | 通常圏の持ち上げ・超限合成・因数分解の型は、原文の準圏内の指定2単体・3単体の持ち上げや∞余極限との比較を含まない。通常圏では任意の可換正方形の対角射と整合の存在を表す持ち上げ性がある。準圏で全ての正方形の指定四面体延長を要求する弱直交は未確認。 |
| 9.6.4.11 | partial → none |  | 通常圏の持ち上げ・超限合成・因数分解の型は、原文の準圏内の指定2単体・3単体の持ち上げや∞余極限との比較を含まない。Mathlib の llp と rlp は通常圏の射のクラスに対して全称量化する。準圏内の弱直交と、それを二つのクラスへ拡張する定義は未確認。 |
| 9.6.4.14 | partial → none |  | 通常圏の持ち上げ・超限合成・因数分解の型は、原文の準圏内の指定2単体・3単体の持ち上げや∞余極限との比較を含まない。Mathlib では通常圏の左持ち上げクラスは射圏の retract で閉じる。準圏の Fun(Δ¹,C) 内の retract と四面体の弱直交に対する結果は未確認。 |
| 9.6.4.15 | partial → none |  | 通常圏の持ち上げ・超限合成・因数分解の型は、原文の準圏内の指定2単体・3単体の持ち上げや∞余極限との比較を含まない。通常圏の左持ち上げクラスは pushout で閉じる。準圏における pushout と四面体での解の存在を結ぶ一般形は未確認。 |
| 9.6.4.16 | partial → none |  | 通常圏の持ち上げ・超限合成・因数分解の型は、原文の準圏内の指定2単体・3単体の持ち上げや∞余極限との比較を含まない。通常圏では任意の整列形状の超限合成で左持ち上げ性が保たれる。準圏の四面体解について極限順序数での連続性から弱直交を保つ結果は未確認。 |
| 9.6.4.17 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：頂点ファイバーと相対関手空間はある。原文で指定された四面体の部分複体 Q への制限と、その指定正方形 σ 上のファイバーを Sol とする構成は未確認。 |
| 9.6.4.20 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：join の単体、相対カリー化、片側 coslice の三角形比較を調べた。両端を固定した二重 slice の写像空間から、Q 上の指定正方形を持つ四面体のファイバーへの比較 θ は未確認。 |
| 9.6.4.21 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：片側の三角形制限と twisted Hom の別の比較はある。二重 slice の写像空間から指定正方形の Sol への同じ θ が Kan ホモトピー同値となる型は未確認。 |
| 9.6.4.23 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：余カルテシアン・カルテシアン辺の持ち上げ性と逆圏比較を確認した。指定正方形の四面体解の全空間が U を通じて基底の解空間とホモトピー同値になる型は未確認。 |
| 9.6.5.1 | partial → none |  | 通常圏の持ち上げ・超限合成・因数分解の型は、原文の準圏内の指定2単体・3単体の持ち上げや∞余極限との比較を含まない。Mathlib では通常圏の弱分解系を、分解・retract 閉性・持ち上げの存在から構成できる。準圏で 2 単体により分解し四面体で持ち上げる構造は未確認。 |
| 9.6.5.5 | partial → none |  | 通常圏の持ち上げ・超限合成・因数分解の型は、原文の準圏内の指定2単体・3単体の持ち上げや∞余極限との比較を含まない。通常圏の弱分解系で両クラスが相手への持ち上げ性で特徴付けられる。準圏で弱直交により双方を特徴付ける型は未確認。 |
| 9.6.5.6 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏では三つの閉性の述語は別々にあり、準圏の強飽和性は余極限と二対三を使う。一般の W で準圏の pushout・retract・小超限合成の三条件を課す定義は未確認。 |
| 9.6.5.12 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の小対象論法の分解と左クラスの記述、準圏の局所対象への強飽和置換はある。任意の presentable 準圏で弱飽和閉包と弱直交を両クラスとする分解系は未確認。 |
| 9.6.6.1 | partial → none |  | IsLocalForHomは対象zへの前合成同値であり、原文の二つの任意射f,gの四つのHomのpullback条件そのものではない。gを終対象への射にした比較も型で未確認。 |
| 9.6.6.4 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の llp・rlp は解の存在を課し、準圏の局所性は特定の対象への前合成同値を課す。一般の二射の直交を二つの集合へ量化する原文の定義は未確認。 |
| 9.6.6.7 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：充満忠実性と CatInfinity の準圏性はある。原文の整数 n での圏論的連結性・n-faithfulness による CatInfinity 内の直交は未確認。 |
| 9.6.6.10 | partial → none |  | 対象局所性の合成・取消しは、任意の射gに対する直交性の同じpullback条件と比較されていない。 |
| 9.6.6.12 | partial → none |  | localEquivalencesは全W-local対象への前合成同値を判定する。原文の指定一射gへの直交クラスとは異なる集合。 |
| 9.6.6.13 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の弱い持ち上げの retract 閉性と、準圏の余錐の retract による普遍性を確認した。任意の二射で可縮な解空間を持つ直交が Fun(Δ¹,C) の retract で保たれる型は未確認。 |
| 9.6.6.14 | partial → none |  | 対象zのlocalityのpushout保存は、原文の指定射gに対するHom四角のpullbackを同じものとする比較がない。 |
| 9.6.6.15 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：固定した対象への局所性と通常圏の弱い持ち上げ性はある。任意の g の f への強直交から、f の相対余対角への強直交を得る宣言は未確認。 |
| 9.6.6.16 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：特定の Kan 標的への三角形評価と端点対のファイブレーション性はある。指定 f,g を固定した 3 点・4 点の Hom の三つの引戻しとそれぞれの自明 Kan ファイブレーション性は未確認。 |
| 9.6.6.18 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：lax pullback の写像空間について厳密な引戻しと図式を構成する宣言はある。原文の f,g 付き三点・四点 Hom の正方形が、強直交を定義する Hom 正方形と同型になる比較は未確認。 |
| 9.6.6.19 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：lax pullback の写像空間の極限と、別の三角形空間の可縮性はある。指定の θ のホモトピー同値・自明 Kan 性と、各 Sol の可縮性を結ぶ五条件の iff は未確認。 |
| 9.6.6.23 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：持ち上げ辺の比較と逆圏での交換はある。片側が指定持ち上げ辺のとき、基底の二射の強直交を全空間へ反映する型は未確認。 |
| 9.6.6.24 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：三角形の評価と固定二辺の充填の可縮性を確認した。全ての指定正方形に対する二重 slice の写像空間の可縮性による強直交の判定は未確認。 |
| 9.6.6.25 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：局所対象の Hom 条件と slice 射影の一般論はある。任意の持ち上げ辺 f̃ で g を表す slice 対象が局所になる条件と、f と g の強直交を結ぶ iff は未確認。 |
| 9.6.6.26 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の弱い持ち上げ性と、準圏の固定対象への局所性はある。S に相対余対角が残るとき、弱直交から任意の右側の射の強直交を復元する型は未確認。 |
| 9.6.6.27 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：始点が点のとき coslice と Tw の始点固定部分を同値にする比較はある。両側の一般の図式 F,G を固定したときの、指定された二本のホモトピー同値と形状に関する関手性は未確認。 |
| 9.6.7.1 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の関手的分解のデータと、準圏の指定辺を保存する相対関手の部分圏はある。原文の Δ² の左・右短辺が任意の S_L,S_R に属する部分圏を個別に作り、その共通部分を取る宣言は未確認。 |
| 9.6.7.2 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：全三角形の内ホーン延長空間の可縮性と全部分圏の包含の充満忠実性はある。分解三角形の長辺への制限を、二つのクラスの直交で判定する iff は未確認。 |
| 9.6.7.3 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：両端評価の写像空間と通常圏の持ち上げの構造を確認した。id_X→g の指定された正方形との合成のホモトピー同値で強直交を判定する iff は未確認。 |
| 9.6.7.4 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：固定短辺の三角形充填と Kan 標的への三角形長辺評価はある。異なる二つの分解三角形間の Hom の長辺制限が、左辺と相手の右辺の直交で同値になる型は未確認。 |
| 9.6.8.1 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の弱分解系と、準圏の持ち上げ辺の構造を確認した。準圏での直交、2 単体の分解、矢印の同型閉性をまとめる強い分解系の述語は未確認。 |
| 9.6.8.6 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：準圏の圏の模型、単体的集合の射の内アノダイン分解、充満忠実性はある。整数 n ごとの圏論的連結な関手と n-faithful な関手の強分解系は未確認。 |
| 9.6.8.8 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：固定短辺の充填空間の可縮性と、通常圏の関手的分解データを確認した。原文の分解系の全三角形から長辺を取る写像の自明 Kan 性は未確認。 |
| 9.6.8.9 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の弱分解系の両クラスの持ち上げ性による記述はある。準圏の強分解系の両クラスが、全ての可逆辺を含む型は未確認。 |
| 9.6.8.10 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の左・右持ち上げクラスは retract で閉じる。準圏の強分解系から Fun(Δ¹,C) 内の retract 閉性を得る型は未確認。 |
| 9.6.8.11 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の retract と弱い持ち上げから弱分解系を組み立てる型はある。準圏の強分解系から retract 閉性と四面体解の存在を備えた弱分解系へ移す型は未確認。 |
| 9.6.8.13 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の弱分解系では左クラスと弱い持ち上げが一致する。準圏の強分解系で、この一致に可縮な解空間の直交を加えた三条件の同値は未確認。 |
| 9.6.8.14 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の弱持ち上げクラスの pushout 閉性と、準圏の局所同値の閉性はある。弱分解系の強直交を左消去または相対余対角の閉性で判定する三条件は未確認。 |
| 9.6.8.15 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の関手的分解の選択と一般の圏同値判定はある。指定した全分解三角形の長辺制限が同値であることを含む三条件から準圏の分解系を回収する iff は未確認。 |
| 9.6.8.16 | partial → none |  | 通常圏の持ち上げ・超限合成・因数分解の型は、原文の準圏内の指定2単体・3単体の持ち上げや∞余極限との比較を含まない。通常圏で関手的分解を各対象に適用して関手圏の分解を作れる。準圏の任意の単体集合形状について、点ごとの両クラスの強直交まで得る分解系は未確認。 |
| 9.6.8.17 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：準圏の反変輸送の持ち上げと通常圏の分解データを確認した。カルテシアン右辺を指定して底の強分解系を全空間へ移す結果は未確認。 |
| 9.6.9.2 | partial → partial | stronger-hyp | IsStronglySaturatedEdgeSetOfShapesは同じSに2-of-3などを追加し、原文の同型包含・合成閉性・小arrow余極限閉性を直接与える。saturatedだけの全定義とは差がある。 |
| 9.6.9.8 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：小辺族からの強飽和な局所同値とその射圏部分の presentability はある。任意の飽和生成クラスと元の W に強直交する右クラスを対にした準圏の分解系は未確認。 |
| 9.6.9.10 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：特定の生成辺の Ind 像の包含が accessible になる結果はある。任意の分解系の左・右の accessibly embedded 性と、長辺制限の切断の accessibility を結ぶ三条件は未確認。 |
| 9.6.9.11 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の関手的分解と準圏の関手の accessibility は別々にある。分解系のいずれかのクラスの包含または分解の切断に accessibility を課す定義は未確認。 |
| 9.6.9.12 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：小辺族からの強飽和閉包の射圏と、通常圏の小対象論法を確認した。準圏の accessible 分解系を、右クラスを強直交で決める小さい辺族の存在と同値にする型は未確認。 |
| 9.6.9.13 | partial → partial | special | Wbarを同じ小族からのgeneratedEdgesとしgeneratedArrowCategoryを取る場合、presentabilityは原文(3)の同じarrow部分圏のaccessibilityを直接返す。任意のsaturatedクラスの全iffは含まない。 |
| 9.6.9.14 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：特定の強飽和な局所同値の記述と、通常圏の弱分解系での左クラスの一意性を確認した。原文の accessible な強分解系と accessibly saturated クラスの全単射は未確認。 |
| 9.6.9.15 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の小対象論法の左クラスの記述と両クラスの直交による特徴付けはある。準圏で小辺族から作る弱飽和クラスと弱分解系の全単射は未確認。 |
| 9.6.9.23 | partial → partial | component | 小Wから生成した同じgeneratedEdgesについてlocalEquivalencesとの等式とstrong saturationは、原文のlocal equivalence表示とstrong saturationの成分を直接与える。小集合によるcolimit生成を含む全三条件の同値は含まない。 |
| 9.6.9.25 | partial → partial | component | 小Wに対するlocal部分圏と生成辺集合の等式は、原文の対応の同じ小生成入力に対する値を直接与える。全Bousfield部分圏からの回収と全単射の型は含まない。 |
| 9.7.1.1 | partial → partial | special | Qを空、Kを全小κ-filtered形状、Hを小準圏Cの標準indYonedaに限ると、Indのκ-filtered余完備性とindKappaContinuousRestriction_isQCatEquivalenceは同じHの余完備化条件を直接満たす。任意の関係Qは含まない。 |
| 9.7.1.4 | partial → partial | special | Qを空、Kを全小κ-filtered形状、Hを小準圏Cの標準indYonedaに限ると、Indのκ-filtered余完備性とindKappaContinuousRestriction_isQCatEquivalenceは同じHの余完備化条件を直接満たす。任意の関係Qは含まない。 |
| 9.7.1.6 | partial → partial | component | Cが有限余積を持ちQをその余積図式とする標準Σ前層の場合、sigma_exists_reflectorは同じ有限余積を積へ送る前層部分の反射随伴という(1)の成分を直接返す。任意Qと数値λでの(2)は含まない。 |
| 9.7.1.10 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：小 κ-filtered 余極限で閉じた Ind の頂点と、別途指定した辺族での Bousfield 局所化はある。指定した余錐を余極限にする相対前層模型で、任意の K に関する最小閉部分圏を取る原文の H は未確認。 |
| 9.7.1.11 | partial → partial | special | Qを空、Hを標準indYoneda、Kを全小κ-filtered形状に限ると、ind_exists_leftKanExtension_with_recoveryとindLeftKanExtension_preservesSmallKappaFilteredColimitsは原文の同じfの左Kan延長F、その回収同型、FのK-余連続性という存在の結論を直接与える。任意Qと指定変換αの全iffは含まない。 |
| 9.7.1.12 | partial → partial | special | Qを空、Hを標準indYoneda、Kを全小κ-filtered形状に限ると、indLeftKanExtension_preservesSmallKappaFilteredColimitsは同じFと恒等単位の左Kan性からFのκ-filtered余極限保存を直接返す。(1)⇒(2)のこの場合で、任意Qと逆向きは含まない。 |
| 9.7.1.13 | partial → partial | special | Qを空、Kを全小形状、Hを標準Yonedaに限るとpresheafIdentity_isLeftKanExtensionは同じ恒等関手の恒等単位の左Kan性、すなわち原文のdenseを直接返す。 |
| 9.7.1.14 | partial → partial | special | Qを空、Hを小準圏Cの標準indYonedaに限るとindYoneda_isFullyFaithfulは原文の同じHの充満忠実性を直接返す。この場合右辺の関係条件は空であり、任意Qのiffは含まない。 |
| 9.7.1.15 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：単体集合の濃度制限と、コンパクト生成モデルの濃度変更はある。指定余錐を持つ相対 K-余完備化の本質的 λ-小ささを、λ の指数共終性から導く型は未確認。 |
| 9.7.1.16 | partial → none |  | Σ前層上の保存性のiffは原文のK0⊂Kによる指定制限関手の全準圏同値を返さない。 |
| 9.7.1.20 | partial → none |  | Σ前層上の保存性判定とsifted関手の制限同値は、原文の全K-余連続関手とK0-余連続関手の同じ制限を比較していない。 |
| 9.7.1.22 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：固定された圏からの Ind の制限同値と小余極限を保つ関手の PrL の構成はある。二つの形状族の準圏の圏の包含に対し、相対余完備化を左随伴にする結果は未確認。 |
| 9.7.2.1 | partial → partial | component | IsSiftedInfinityのfield diagonal_rightCofinalは原文の有限集合Iが二点の場合の同じ対角のright cofinal性を直接与える。nonemptyFiniteDiagonal_isRightCofinalは非空有限反復積へ拡張するが、任意有限集合と空添字を含む定義全体の比較は含まない。 |
| 9.7.2.3 | partial → partial | component | 反対のIsSiftedInfinityとisLeftCofinal_iff_isRightCofinal_opにより同じ有限対角の左余終性の条件を与える。空集合の場合と積・opの全比較はこの引用だけに含まない。 |
| 9.7.2.5 | partial → none |  | 通常圏のsifted性のFinal/同値不変性は、原文の単体集合のright cofinal性・categorical equivalenceへの比較を含まない。 |
| 9.7.2.6 | partial → none |  | 通常圏のsifted性のFinal/同値不変性は、原文の単体集合のright cofinal性・categorical equivalenceへの比較を含まない。 |
| 9.7.2.8 | partial → partial | direction | IsSiftedInfinityの二つのfields nonempty_verticesとdiagonal_rightCofinalは同じKの非空性と同じ二項対角のright cofinal性を直接返す。任意有限集合による原文の定義との比較を含む逆向きはこの引用だけで主張しない。 |
| 9.7.2.9 | partial → none |  | 二項余積からsifted性を得る型は、原文の二つのcosliceのfiber productの弱可縮性を同じ条件と判定する型ではない。 |
| 9.7.2.12 | partial → partial | direction | 同じ二つの空間値図式のunstraighteningにtotalKanProductComparisonを適用すると、siftedなKの余極限と二項積の比較が弱同値となる向きを直接得る。分類と全体余極限の同じ比較も併用し、逆向きは含まない。 |
| 9.7.2.13 | partial → none |  | 全空間値のproduct比較は原文の数値κで切ったS_<κにおける同じ余極限比較への大きさの比較がない。 |
| 9.7.3.1 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：二つの固定圏の余連続関手の全部分圏と、固定対象を空間でテンソルする一変数関手はある。任意の T:C×D→E が各変数で K-余連続という述語とその全部分圏は未確認。 |
| 9.7.3.5 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：定数関手の sifted 余極限保存と対角の右共終性はある。積を余域に持つ関手の成分ごとの保存の定理は、積を始域に持つ T の別々の変数の保存と全体の保存を比較する原文とは向きが異なる。 |
| 9.7.3.6 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：有限余積と sifted 余極限による一変数の保存判定はある。二変数での有限余極限保存と、積からの関手の κ-小 filtered 余極限保存を組み合わせる iff は未確認。 |
| 9.7.3.7 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：単体集合の直積の余完備性と随伴の直積はある。原文は各変数で余連続な関手を表現する別のテンソルであり、その制限同値を含む定義は未確認。 |
| 9.7.3.9 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：直積の presentability と、固定圏の前層への左 Kan 延長はある。別々に K-余連続な関手を表現する圏を任意の K について構成する存在は未確認。 |
| 9.7.3.10 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：直積に沿う同値・随伴と、絶対 Ind の制限同値を確認した。K-双線形関手を表すテンソル圏と指定の二変数関手を同値まで一意に選ぶ型は未確認。 |
| 9.7.3.14 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：単体集合の直積の小ささとその準圏の小余極限はある。κ-小形状の余極限を各変数で保つ関手を表現する κ-余完備テンソルの定義は未確認。 |
| 9.7.3.15 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：単体集合の直積とその随伴はある。全小余極限について双線形な関手を表現する余完備テンソルの定義は未確認。 |
| 9.7.4.1 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：固定対象を空間でテンソルする関手はある。原文の空間の圏を単位とする余完備テンソルへの X↦Δ⁰⊗X が圏同値になる型は未確認。 |
| 9.7.4.2 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：有限単体模型による全空間の compact 生成と、別の前層の Ind 閉性はある。Δ⁰ 一点を含む任意 K の最小余極限閉部分圏を S_{<κ} に構成する定義は未確認。 |
| 9.7.4.8 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：固定対象に空間をテンソルする随伴と、二空間の直積はある。任意 K の S_{<K}×C で双線形である全関手、単位での同型、さらに余完備テンソルを表す性質を一緒に得る型は未確認。 |
| 9.7.4.12 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：空間を固定対象に作用させる随伴と全空間の生成はある。S_{<K} を使う K-余完備テンソルへの点による挿入が同値となる結果は未確認。 |
| 9.7.5.1 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：既存の tensor_isPresentable は SSet のカルテシアンな積 C×D の presentability を示す。原文の双線形関手を表現する余完備テンソルの presentability は未確認。 |
| 9.7.5.2 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：単体集合の積では成分射の積を作り、その余極限保存や同型を比較できる。異なる形状族の余完備テンソル間の F⊗G と指定の可換同型正方形は未確認。 |
| 9.7.5.3 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：絶対 Ind の制限同値と直積上の随伴はある。相対完備化する二つの関手の余完備テンソルが、K から K̂ への相対余完備化となる比較は未確認。 |
| 9.7.5.5 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：二つの Ind の直積には presentability を得る型がある。λ-余完備テンソルを同じ κ,λ で compact 生成する結論は未確認。 |
| 9.7.5.6 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：直積の presentability はあるが、同じ κ における二圏の生成を余完備テンソルへ移す型は未確認。 |
| 9.7.5.7 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：直積の Ind 模型と、空間が ℵ₀-accessible である結果はある。ℵ₀-compact 生成が双線形関手を表現するテンソルで保存される型は未確認。 |
| 9.7.5.8 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：既存の定理は直積がある濃度で presentable になる結果と、成分射の積が指定濃度で accessible になる結果。原文の余完備テンソルが同じ κ で presentable になる型は未確認。 |
| 9.7.5.9 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：右随伴側の関手空間と直積の presentability はある。原文の Dᵒᵖ から C への小極限保存関手の全部分圏と余完備テンソルの標準同値は未確認。 |
| 9.7.5.13 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：反射の随伴と余単位を単体集合の直積で合成する型はある。双線形の余完備テンソルで二つの局所化をテンソルし、Bousfield 局所化になる結果は未確認。 |
| 9.7.6.1 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：離散空間と同値である述語および直積の定理を確認した。任意の n で一方の局所切断性が余完備テンソルへ移る型は未確認。 |
| 9.7.6.2 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：空間の 0 切断と固定対象への空間作用、余連続関手圏はある。S^{≤n}_{<κ} によるテンソルが局所 n 切断され、点による制限で指定の圏同値を与える結論は未確認。 |
| 9.7.6.3 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：離散空間の表示と固定対象を空間でテンソルする関手はある。局所 n 切断性を切断空間による余完備テンソルへの点の射が同値かどうかで判定する iff は未確認。 |
| 9.7.6.5 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：小辺族に対する一般の反射局所化と離散空間の充満忠実な埋め込みを確認した。任意の presentable C の n 切断対象を指定テンソルの充満忠実右随伴の本質像とする型は未確認。 |
| 9.7.6.10 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：有限単体集合の Kan 置換のコンパクト性と、κ-コンパクト対象の有限余極限閉性はある。有限切断空間との余完備テンソル、有限余極限保存関手の制限同値および局所 n 切断性の判定は未確認。 |
| 9.7.7.1 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：単体集合の直積による関手圏の比較や随伴はある。三圏からの双線形・多重線形関手を表現する二つの括りの間に、指定正方形を持つ結合の同値は未確認。 |
| 9.7.7.2 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：固定二圏の余連続関手圏と、余域が積の場合の成分判定はある。始域の有限個の変数を一つずつ固定し K-余連続性を課す全部分圏は未確認。 |
| 9.7.7.6 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：有限個の積の presentability や、一つの Ind の制限同値はある。有限族からの各変数で余連続な関手を表す圏を定義する三条件は未確認。 |
| 9.7.7.9 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：直積の presentability と固定圏への米田の左 Kan 延長はある。任意の有限族の K-多重線形関手を表現するテンソル圏の存在は未確認。 |
| 9.7.7.10 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：直積を余域とする関手圏の同型と、一つの Ind の制限同値はある。有限集合間の写像に沿う各テンソルで前合成して、多重線形関手圏の同値を得る主張は未確認。 |
| 9.7.7.11 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：余連続関手の合成と、絶対的な Ind の制限同値はある。有限族をまとめるテンソル射と、まとめた族をテンソルする射の合成が元の族の普遍性を満たす型は未確認。 |
| 9.7.7.14 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：PrL と準圏のホモトピー圏を扱う構成、および直積の同値はある。κ-小形状族で制限した QC のホモトピー圏に、余完備テンソルと S_{<K} を単位とするモノイド構造は未確認。 |
| 9.7.8.1 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：準圏内の冪等射の分裂と直積の presentability はある。原文は圏自体の余完備テンソルの冪等性であり、指定対象でのテンソル挿入が圏同値となる述語は未確認。 |
| 9.7.8.5 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：PrL と余連続関手空間および固定対象への空間作用はある。圏 E による余完備テンソルが恒等と同値である presentable 圏の全部分圏は未確認。 |
| 9.7.8.10 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：単独の準圏内の反射、余連続関手圏、直積の随伴を確認した。PrL における E 加群の包含が両随伴を持ち、指定の余完備テンソル・関手圏で表す型は未確認。 |
| 9.7.8.12 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：固定対象での空間テンソルの写像空間随伴と、別の冪等完備性はある。E×E の K-双線形関手の評価が余連続関手圏への同値になるという圏 E の述語は未確認。 |
| 9.7.8.16 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：固定対象への空間作用と余連続関手空間はある。原文の圏 E の加群性について、テンソル模型・関手圏模型・評価のホモトピー逆・双線形作用を結ぶ同値は未確認。 |
| 9.7.8.17 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：余完備な準圏と余連続関手の模型はある。K-余完備な C が圏 E の加群であることを、指定の余完備テンソルによる条件で定義する型は未確認。 |
| 9.7.8.20 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：絶対的な Ind の制限と単独の反射はある。E によるテンソル挿入との前合成と、E の関手圏からの評価との後合成が、任意の E 加群に対し同値となる二結果は未確認。 |
| 9.7.8.27 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：Ind 内の compact 部分の冪等完備化と絶対的な制限同値はある。原文の「圏を余完備テンソルすると冪等」の性質を相対 Ind で移し、冪等完備性のもとで反映する型は未確認。 |
| 9.7.8.29 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：特定形状の絶対的な余完備化の制限同値はある。二つの形状族の間で余完備冪等圏を相対完備化したとき、同じ C の E と E₀ に対する加群性が同値になる型は未確認。 |

## 検査

原文は Kerodon 公式小節の各項目Tagで照合。none は現本体・ロックしたMathlibを再検索し、近隣項目のソース・双対/限定版の候補も照合した。Archiveの宣言をown・partialの根拠にはしていない。宣言の存在と型はソースでの確認で、kernel確認ではない。
