# KB-W1 / B6 第6章

原文の項目と現在のソースの型による紙の再照合。Lean・ビルド・鍵は使っていない。

対象 114行。partial 62、none 52。判定後：partial 44、none 65、mathlib 4、own 1。

既存 own・both・mathlib 31行の全既存フィールドは変更なし。既存7列の末尾に partial_kind を追加し、対象外行は空欄とした。区切り・改行と対象外行の既存引用符を保存した。verdict・axioms・check も変更していない。古いcheck欄は今回のkernel検査結果ではない。

## 全対象行の判定・変更一覧

状態不変でも型/原文の再判定を記録した。各 reason の詳細はCSVと同じ。原文全文・候補の型・検索はgit外の章別証拠。

| 番号 | 旧→新 | partial_kind | 理由 |
| --- | --- | --- | --- |
| 6.1.2.1 | partial → partial | component | bicategoryUnitHomMapは任意の単位型ηによる原文のright adjunctそのものを直接構成する。homEquiv₂は随伴を仮定するので、任意のεだけによるleft adjunct全体までは数えない。 |
| 6.1.2.5 | partial → partial | stronger-hyp | (η,ε)が両三角恒等式を満たすAdjunctionに強めればhomEquiv₂のleft_inv/right_invから同じadjunctの二つの含意を直接得る。片方の三角式だけの各主張には一般化しない。 |
| 6.1.2.6 | partial → partial | direction | AdjunctionのhomEquiv₂は原文(1)から、同じunit/counitによるleft/right adjunctが互いに逆という(2)を直接返す。任意の指定η,εについての逆方向は含まない。 |
| 6.1.2.11 | partial → none |  | 一般双圏のUnitHomCriterionは全試験対象Tの全Hom関手上の全単射を要求する。原文の通常圏で指定ηの各対象のHomだけによる判定・指定単位の比較・余単位の一意性の型ではない。StructuredArrowからの左随伴も指定ηとの比較を欠く。 |
| 6.1.2.12 | partial → partial | direction | 随伴のhomEquiv₁の逆は原文の指定ηを使った前合成側のHom全単射そのもの。(ηがunit)⇒判定の向きを直接与え、逆は含まない。 |
| 6.1.2.13 | partial → partial | component | 随伴を与えるとhomEquiv₁は原文(3)⇒(2)の指定εによるHom全単射を直接与える。任意εからunitを回収する逆・一意性は含まない。 |
| 6.1.2.14 | partial → mathlib |  | Bicategory.Adjunctionはunit・counitと二つの三角恒等式を持つ。∃a:Adjunction f g,a.counit=εと置けば、指定εに対するunitの存在という原文の定義をそのまま表す。専用述語名の不足をpartial理由にしない。 |
| 6.1.3.3 | partial → partial | component | homEquiv₁に適切な恒等1射を代入すれば、指定η′をunit経由に因子化するβの存在・一意性を直接得る。βの可逆性とη′がunitとなることの一般iffとε′側の全体は含まない。 |
| 6.1.3.5 | partial → partial | component | IsLeftAdjointは原文のLHomを張る1射の条件（右随伴が存在）そのもの。選んだ右随伴を反変な関手にする構成は含まない。 |
| 6.1.3.7 | partial → partial | component | homEquiv₂を恒等1射で特殊化すれば、指定η′のunitを経由するβによる因子化の存在・一意性を直接得る。可逆性のiffとε′側の全体は含まない。 |
| 6.1.3.8 | partial → partial | component | IsRightAdjointは原文のRHomを張る1射の条件そのもの。LHomの反対への圏同値と準逆は含まない。 |
| 6.1.4.1 | partial → none |  | e.adjは指定同値の標準unitの随伴、adjointifyCounitはunitとcounit両方の同型からの修正。原文の片方の1射が同値のとき任意の指定ηがunit iff ηが同型、という判定ではない。 |
| 6.1.4.4 | partial → partial | special | 通常圏の双圏に制限するとAdjunction.toEquivalenceはunit/counitの成分同型から同じF,Gを逆関手とする圏同値を直接作り、原文(3)⇒(1),(2)を与える。一般双圏の三条件のiffは含まない。 |
| 6.1.4.6 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：指定 η の左右 whiskering が同型で、g による各 Hom の後合成が充満忠実なら η が可逆な余単位を持つ随伴の単位となる判定。BicategoryHomCorrespondence.ofUnit は最初から指定した Hom 全単射を仮定。 |
| 6.1.4.7 | partial → partial | component | bicategory_whiskerLeft_unit_isIso_of_counitとwhiskerRight版は原文(1)から(2)の二つのwhiskerの可逆性を同じηについて直接返す。本質的全射の部分と他のiffは含まない。 |
| 6.1.5.1 | partial → partial | stronger-hyp | η,η′を指定随伴のunitに強めればcompUnitは原文と同じwhiskeringと結合子による合成unitを構成する。任意のunit型2射だけの構成は含まない。 |
| 6.1.5.3 | partial → partial | special | 双圏をCat、試験圏Tを一点、η,η′を随伴のunitに限るとAdjunction.comp_homEquivは原文の同じ二段のadjunctと合成adjunctの一致を直接返す。任意双圏と任意ηの可換四角には及ばない。 |
| 6.1.5.6 | partial → mathlib |  | Bicategory.Adjunction.compは二つの随伴の合成を直接作る。存在する左右随伴の証人を取り合成すれば原文の二つの存在結論をともに得る。IsLeftAdjointの名の合成補題がなくても主張全体が直接従う。 |
| 6.1.5.7 | partial → partial | stronger-hyp | ε,ε′を指定随伴のcounitに強めればcompCounitは原文と同じwhiskering・結合子による合成counitを直接構成する。 |
| 6.1.6.5 | partial → partial | direction | 評価evが指定ExactPairing Y Xの評価であれば、tensorLeftHomEquivの逆は原文第一条件の同じevによる全単射を直接返す。duality datum⇒第一条件の向きで、任意evからの逆判定は含まない。 |
| 6.1.6.6 | partial → mathlib |  | ExactPairing Y Xはcoev:1→Y⊗X、ev:X⊗Y→1と二つのzigzag等式を持つ。∃p:ExactPairing Y X,p.evaluation′=evという存在命題は原文の指定evがduality datumという定義そのもの。専用名は要らない。 |
| 6.1.6.7 | partial → partial | component | 指定coevを持つExactPairing Y Xを仮定するとtensorRightHomEquivは原文第二条件の同じcoevによる全単射を直接与える。任意coevから評価を回収する逆と一意性は含まない。 |
| 6.1.6.8 | partial → mathlib |  | ∃p:ExactPairing Y X,p.coevaluation′=coevは指定coevと組になるevおよび二つのzigzag等式の存在で、原文の定義全体をそのまま表す。 |
| 6.1.6.13 | partial → partial | component | 評価evをExactPairing Y Xの評価に強めるとtensorRightHomEquiv Z Y X 1の逆と単位子が、原文後半の弱left dualの全単射Hom(Z,X)→Hom(Z⊗Y,1)を直接返す。任意evとweak right側は含まない。 |
| 6.1.6.15 | partial → partial | direction | tensorLeftHomEquivを終域1に特殊化すると、同じevによるduality datumからweak right dualの全単射が直接得られる。原文(1)の順方向のみで、任意指定evに関する逆は含まない。 |
| 6.2.1.3 | partial → partial | component | QCatAdjunctionの存在量化は原文のFがleft adjoint・Gがright adjointであるという二つの条件を直接表す。Functor準圏のLFun/RFun全体の構成は含まない。 |
| 6.2.1.13 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：η と ε が指定充満部分圏上で同型となることを使う F,G の制限と同値。通常の Adjunction.restrict や QCatAdjunction の定義はこの選択による制限を述べない。 |
| 6.2.1.14 | partial → partial | direction | QCatAdjunction.toHoAdjunctionは同じF,Gの随伴をホモトピー圏へ降ろすので原文(1)⇒(2)の方向。全試験準圏のHomを調べるunit判定は、hFとhGだけを使う逆判定の代用としない。 |
| 6.2.1.19 | partial → partial | component | rightAdjointFunctorIsoは同じFの二つの右随伴G,G′のFunctor空間内の同型を直接構成する。LFunとRFunの反対の同値全体は含まない。 |
| 6.2.1.21 | none → partial | special | n=−2、D=Δ⁰に制限するとpointAdjunction_isTerminalは同じ右随伴Gが点の頂点を終対象へ送ると直接返す。終対象の全Homの可縮性とpinched/interval比較により、この場合の(−2)-truncated対象の保存になる。一般n・任意Dは含まない。 |
| 6.2.2.1 | partial → partial | special | C′をW-localな頂点で張るfull subcategoryに制限するとLocalEquivalenceHomは全てのそのZについての同じ前合成の同値性。isLocalForHom_iff_intervalで原文の写像空間作用と直接比較できる。任意のC′を名付ける述語は含まない。 |
| 6.2.2.6 | partial → partial | special | C′をW-local対象のfull subcategoryに限り、各xからそこへのlocal equivalenceを指定するとisReflectiveSubcategory_of_localReplacementsは同じ部分圏の反射を構成する。一般の反射・余反射の全定義は含まない。 |
| 6.2.2.13 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：本質的 κ-small な Kan 複体の切断が本質的 κ-small であり指定の共通部分が反射的となる結論。coskeleton の随伴に κ 評価はない。 |
| 6.2.2.14 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：QC の辺 F の切断条件と、濃度・局所次数で指定する QC の部分圏の比較。CatInfinity と宇宙 lift には整数次数と基数の組がない。 |
| 6.2.2.16 | partial → none |  | 引用はreflectorがfを反転することと局所性のiff。原文の(2)〜(5)のcoslice制限やouter horn充填と同じ条件ではなく、原文の五条件の同値の方向を直接返さない。 |
| 6.2.2.17 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：充満部分圏上の図式 q に対する slice の辺が元の C′-local equivalence のときの局所同値性。IsLocalForHom の比較だけでは slice の局所 Hom を同定しない。 |
| 6.2.2.18 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：反射的 C′ の図式 q 上の slice が C の同じ図式上の slice に反射的。通常圏の Over の随伴と、任意の単体図式の slice を区別した。 |
| 6.2.2.19 | partial → partial | direction | ReflectiveSubcategoryの随伴からreflectionMappingEquivalenceと同じunitのadjunct比較を使えば、各xのunitが同じPに関するreflectionとなる。包含が左随伴を持つ⇒reflectiveという反射側の方向のみ。 |
| 6.2.2.20 | partial → partial | component | 選んだ反射rについてlocalizationとunitは原文のLと指定ηの構成を直接与える。任意の指定ηがreflection functorを与えるという述語・coreflectionの定義全体は含まない。 |
| 6.2.2.23 | partial → partial | direction | 選んだReflectiveSubcategoryのreflectorとunit、および同じunitの写像空間比較から、原文のreflective⇒L,ηの存在という方向を直接得る。任意のηから随伴を回収する逆は含まない。 |
| 6.2.2.24 | partial → partial | direction | reflectedUnitIsoとunitOnInclusionIsoは、同じ反射随伴のunitについて原文(1)⇒(3)のLηと部分圏上のηの可逆性を直接返す。ηだけからの逆判定と任意counitの主張は含まない。 |
| 6.2.2.26 | partial → partial | stronger-hyp | 原文(2)に加え、GによるFunctor(Y,−)のホモトピー圏上の後合成が充満忠実と強めるとcounitHom_isIso_of_postcompFullyFaithfulは同じ随伴のcounitを可逆にし(3)を直接返す。G自体の充満忠実性だけから追加条件を回収する部分は含まない。 |
| 6.2.2.28 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：∞ 圏同値と、同型を反映し充満忠実な右随伴を持つことの同値。通常圏の反射的関手の同値判定と、QCat の unit/counit 判定は仮定の形が異なる。 |
| 6.2.2.29 | partial → partial | stronger-hyp | L,ηを選んだ反射随伴rのlocalizationとunitと仮定すると、unitOnLocalizationIsoとreflectedUnitIsoから原文(1)のη_LとLηの可逆性を直接得る。任意のreflection functorから随伴を作る逆は含まない。 |
| 6.2.3.1 | partial → partial | component | IsLocalForHomとIsLocalObjectは同じhomotopy classによる前合成の同値性を定義し、isLocalForHom_iff_intervalで原文の写像空間作用と一致する。w-local・W-localの二条件のみで、colocal側は含まない。 |
| 6.2.3.9 | partial → none |  | 引用は可逆counitを持つ随伴から左関手が局所化となる逆向き。原文の局所化Fと右随伴GからGの充満忠実性・本質的像の判定を結論する型ではない。 |
| 6.2.3.11 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：辺の集合 W が localizing であることを恒等・合成・局所対象への置換と双対条件で定める述語。IsLocalization は指定された射の普遍性。 |
| 6.2.3.14 | partial → none |  | 局所置換から反射を構成する型と反射が反転する辺の集合の閉性は、原文の(a)〜(d)の同じ仮定間の含意を直接返さない。localizing条件や(d)との比較が不足する。 |
| 6.2.3.15 | partial → none |  | 引用は指定反射からinvertedEdgesの局所同値閉性と指定W-local部分圏の局所対象の同定。原文のlocalizing collectionsとreplete reflective subcategoriesの全単射を直接構成せず、その商・逆写像への比較がない。 |
| 6.2.3.16 | partial → partial | component | 原文のlocalizingの仮定に各xのW-local replacementの存在を明示的に追加すれば、isReflectiveSubcategory_of_localReplacementsは同じW-local部分圏の反射随伴を直接作り(1),(2)を与える。元のWと反転される辺の一致および(3),(4)は含まない。 |
| 6.2.3.17 | partial → partial | component | localObjectsSubcomplexは原文がC[W⁻¹]と名付ける同じW-local頂点で張るfull subcategoryを直接構成する。局所化としての普遍性は含まない。 |
| 6.2.4.1 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：指定した C′ と W の片側取消し・C′ への置換から反射と W の同定を導く結論。W-局所対象を先に定める局所置換の補題では任意の C′ の同定がない。 |
| 6.2.4.2 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：cocartesian fibration による反射的部分圏の引き戻しと、局所同値の cocartesian な辺による判定。通常の反射からの局所化には底変換がない。 |
| 6.2.4.3 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：cocartesian fibration の各ファイバーの反射と輸送による局所同値保存から大域的反射性を得る主張。各ファイバーの随伴データを全空間に貼る型がない。 |
| 6.2.4.5 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：cartesian fibration の反変輸送が指定された反射的ファイバー部分圏を保つときの大域的反射性。op で辺を反転する補題はファイバー反射を組み立てない。 |
| 6.2.4.8 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：oriented fiber product の指定充満部分圏で、射影の像の cocartesian 性等による局所同値の判定。laxPullbackEquivalenceSubcomplex の充満忠実性は局所同値を分類しない。 |
| 6.2.4.9 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：oriented fiber product の反射に伴う局所同値と三つの射影条件の同値。pullback 射影の cartesian 性だけでは反射の像が決まらない。 |
| 6.2.5.1 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：Δ¹ 上の fibration の crossing edge の cartesian/cocartesian 性をファイバーへの反射・余反射で判定する結果。標準 collage の構造射の持ち上げは任意の crossing edge を判定しない。 |
| 6.2.5.2 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：任意の E→Δ¹ の cartesian 性と左ファイバーの余反射性、cocartesian 性と右ファイバーの反射性の同値。Quillen cf collage はモデル圏由来の特例。 |
| 6.2.5.4 | partial → partial | special | EをQuillenのcf collage、Fをその指定共変輸送の左導来関手に制限すると、quillenCfDerivedAdjunction_existsとcartesian射影の型は原文の同じ輸送の右随伴およびUのcartesian性を直接与える。一般の模型圏・単体豊穣・SM7・関手的分解を仮定し、具体例のModelCategory instanceなし（§6）。一般のEのiffは含まない。 |
| 6.2.5.5 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：任意の inner fibration で局所的な左右の lift の条件が同値となり、底辺ごとの輸送が随伴する結論。Quillen の随伴を入力する collage からの型とは向きが逆。 |
| 6.2.5.6 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：cocartesian fibration の下で、同じ辺の大域・局所 cartesian 性が同値。CartesianInitialBoundary の op での持ち上げ補題は逆向きの局所判定を述べない。 |
| 6.2.5.7 | partial → partial | component | UをQuillenのcf collage射影に限ればquillenCfCollageProjection_cartesianFibrationは原文(2)のcartesian性を直接返す。ModelCategory C,D・単体豊穣・SM7・関手的分解を仮定し具体例のinstanceなし（§6）。全辺の輸送の随伴と一般Uのiffは含まない。 |
| 6.2.6.1 | partial → none |  | 引用の右辺は共変Hom関手とのFunctorIsoの存在。原文が指定する単一辺uを使う各Hom作用との比較が型にない。commaの始対象から随伴を作る補題も、その同じuの普遍性との橋を欠く。 |
| 6.2.6.2 | partial → partial | component | exists_qcatAdjunction_of_commaFiberInitialは原文と同じD×_C C_{X/}の全fiberの始対象から左随伴を作るので(3)⇒(1)を直接返す。任意left fibrationや全五条件の同値は含まない。 |
| 6.2.6.6 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：右随伴 G が任意の図式 u に対して誘導する coslice 比較も右随伴を持つこと。通常の圏の under や随伴の Hom 全単射は単体図式 u を扱わない。 |
| 6.2.7.1 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：S の辺に沿う 2-単体の因子化を指定の普遍性で optimal とする定義。一般の射の factorization のデータにはこの普遍性がない。 |
| 6.2.7.4 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：恒等・同型条件と S-optimal factorization などで定義する short morphism のクラス。MorphismProperty の通常の閉性だけでは一連の公理を表さない。 |
| 6.2.7.6 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：隣接辺の条件で C の短射部分複体 C^short を作る定義。全頂点での充満部分複体や core では選別する辺が異なる。 |
| 6.2.7.10 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：C^short⊂C の内アノダイン性。spine の標準単体への包含は対象 C の short morphism による部分複体を扱わない。 |
| 6.2.7.12 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：f を short 辺で分解する最小の長さ ℓ(f) とその基本性質。通常の鎖の length は ∞ 圏の射の最小分解ではない。 |
| 6.2.7.13 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：三角形の optimal factorization と両辺の ℓ の評価。内ホーンの合成や通常のリスト長の加法性にこの最小分解条件がない。 |
| 6.2.7.14 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：単体の principal rank と面を取った場合の階数の不等式。単体の次数や退化の判定では short 辺の最初の位置を測らない。 |
| 6.2.7.15 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：非 short な単体 σ へ選んだ σ⁺ を割り当て、面と指定三角形が条件を満たす関数。spine の個別のホーン充填ではこの一貫した割当てがない。 |
| 6.3.0.6 | partial → partial | component | MathlibのFunctor.IsLocalizationからfull_whiskeringLeftおよびfaithfulの既存instanceにより、原文の全試験圏への前合成の充満忠実性を直接得る。本質的像の全判定と普遍性からの逆は含まない。 |
| 6.3.1.13 | partial → partial | component | IsLocalizationは同じFの全準圏への指定localizationPrecompositionの同値性、すなわち原文(2)を直接条件にする。(3),(4)のcoreのπ₀からの逆を含む四条件のiffは含まない。 |
| 6.3.1.21 | partial → partial | component | localization_all_isKanは同じFの全辺の局所化から原文の標的DのKan性を直接返す。Fの弱ホモトピー同値と逆方向は含まない。 |
| 6.3.1.22 | partial → partial | special | W′=∅、F′を前合成同値に限るとlocalization_postcomp_precompositionEquivalenceは同じ合成F≫F′がW=W∪∅の局所化になると直接返す。一般の第二の辺集合の局所化ではない。 |
| 6.3.2.4 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：上辺が局所化の四角で categorical pushout と下辺が像の辺を反転する局所化との同値。初頂点射の strict pushout の閉性は指定射の特別な場合。 |
| 6.3.2.5 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：互いに重ならない指定辺を Δ⁰ へ潰す商の局所化性。inverseAttachment は各辺に walking equivalence を貼る別の pushout。 |
| 6.3.2.7 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：Δ³ の二つの指定辺を縮約した Q→Δ⁰ の圏同値。walking equivalence の一点への同値はこの Q を比較しない。 |
| 6.3.2.8 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：Δ³ の二辺を潰した Q に残る中央の辺 Δ¹→Q が全辺に関する局所化。KST の付着模型とこの Q の比較は未確認。 |
| 6.3.2.9 | partial → none |  | inverseAttachmentはwalkingEquivalenceを貼るpushout。原文の指定Qを貼るpushoutとは別の対象・射であり、Qとの比較なしには同じ局所化の特殊形ではない。 |
| 6.3.2.11 | partial → partial | component | exists_quasicategory_localizationは原文の全ての(C,W)について準圏と局所化射の存在を直接返す。関手性とfiltered colimitの保存は含まない。 |
| 6.3.2.12 | partial → none |  | 引用はcolimitの単体集合c.ptに対する初頂点写像の局所化。原文のarrow categoryのcolimitとなる射との比較、指定辺集合Sが初頂点保存辺集合と一致する比較を型に持たない。 |
| 6.3.2.13 | partial → none |  | 同じ宇宙の局所化の存在は、原文の指定κのessential smallnessが任意の局所化へ移る主張ではない。数値κへの評価と任意標的との比較を欠く。 |
| 6.3.3.1 | partial → own |  | IsLocalization F WをWで存在量化すれば原文の定義そのもの。さらにIsLocalization.saturateでFが反転する全辺をWに選べる。専用のlocalization functorという名前がないことをpartial理由にしない。 |
| 6.3.3.4 | partial → partial | special | Fを選んだReflectiveSubcategoryのreflectorに限ると、構造のadjunctionは同じFの右随伴が充満包含であると直接与える。任意Fを指定して定める述語全体は含まない。 |
| 6.3.3.7 | partial → partial | stronger-hyp | 右随伴と可逆counitを指定した場合、QCatAdjunction.isLocalizationは同じFの局所化性を直接与え、右随伴の存在と合わせて原文(2)を返す。右随伴の充満忠実性からのcounit比較・逆方向は含まない。 |
| 6.3.3.9 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：充満忠実な左随伴を持つ右関手としての coreflective localization。AdjointLocalization は可逆余単位をもつ左関手側。 |
| 6.3.4.1 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：cocartesian fibration の四角でファイバー局所化と底の局所化から全空間の局所化を得る主張。通常の ∞ 圏の局所化はこの輸送条件を持たない。 |
| 6.3.4.2 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：同じ底上の cocartesian fibration 間でファイバーごとの指定辺を反転した局所化の比較。relativeFunctorPost の同値は各ファイバーが局所化である条件を使わない。 |
| 6.3.4.3 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：弱可縮なファイバーをもつ cocartesian fibration が垂直辺に関する局所化。Kan ファイバーの可縮性から同値を得る型では一般の垂直辺を反転しない。 |
| 6.3.4.4 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：底の局所化を cocartesian fibration に沿って引き戻し、像が指定の辺となる cocartesian 辺を反転。任意の底変換での cocartesian 性だけでは局所化がない。 |
| 6.3.4.5 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：底の局所化を left fibration に沿って引き戻したときの局所化。Space 値分類の自然性は反転すべき辺を定めない。 |
| 6.3.4.6 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：積 K×F が K 側で退化する指定辺に関する局所化。precomposition equivalence の積安定性は局所化の対象となる関手の充満部分圏を指定しない。 |
| 6.3.5.1 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：すべての底変換が、退化辺に写る辺に関する局所化となる universally localizing の定義。IsLocalization は単一の射と辺集合についての条件。 |
| 6.3.5.3 | partial → none |  | 引用は単体圏の初頂点写像を各頂点とする特定のcubeの局所化。原文の任意の二つのcategorical pushoutと指定Wの和集合の比較への型の対応がない。 |
| 6.3.5.4 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：各 Δⁿ 上の局所化と任意の底変換に対する局所化の条件の同値。頂点ごとの通常の pullback 比較は全単体を試す局所判定ではない。 |
| 6.3.5.5 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：universally localizing なら恒等底変換で退化像の辺の局所化になる帰結。IsLocalization の単調性には universally localizing の入力がない。 |
| 6.3.5.9 | partial → partial | component | sectionを持つfについて、指定した単体ホモトピーとその全成分をfが反転する条件を明示的に加えればisLocalization_of_deformationは同じfの局所化を直接返す。universalに要求される底変換のうち恒等底変換の成分だけで、任意底変換ではない。 |
| 6.3.5.10 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：universally localizing なら各次数で全射。dgUniversalCommaTarget_degree_surjective は特定の dg 比較写像だけの全射性。 |
| 6.3.5.11 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：任意の二つの universally localizing 射の合成安定性。一般の射のクラスの universally 構成と局所化クラスの合成との同定はない。 |
| 6.3.5.12 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：弱可縮な K を積に足した X×K→S が universally localizing。弱ホモトピー同値な射影の型に任意の底変換の辺の局所化はない。 |
| 6.3.5.13 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：arrow 圏で universally localizing 射がフィルター余極限に閉じること。初頂点写像の可算余極限は任意の引き戻しを量化しない。 |
| 6.3.5.14 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：指定 pushout の三射が universally localizing なら残りの射も同様。pushout の anodyne 閉性では退化像の辺の局所化にならない。 |
| 6.3.6.1 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：任意の単体集合 S に半順序の nerve から universally localizing 射があること。単体の圏の初頂点射の局所化は定義域が半順序とは限らない。 |
| 6.3.6.2 | partial → none |  | sdとsubdivisionLastVertexMapは原文の射の構成まで。局所化・任意の底変換の局所化のいずれもこの型の結論にはない。 |
| 6.3.6.4 | partial → none |  | transportSimplexFirstVertexMapはN(Δ_S)からSへの初頂点写像。原文はN(Δ_S)からSd(S)への指定ψであり、始域が同じだけで別の射。 |
| 6.3.6.5 | partial → none |  | 引用は初頂点写像の局所化。原文はSdを経由する最終頂点写像の合成で、同じ射に比較する型がない。局所化性とuniversal性の差に先立ち射が異なる。 |
| 6.3.6.13 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：nonsingular S を半順序 nerve から universally localizing に解消。薄い nerve の内ファイブレーションにはこの存在条件がない。 |
| 6.3.6.14 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：任意の S に対して nonsingular な始域を持つ universally localizing 射の存在。inner anodyne resolution は通常逆向き。 |
| 6.3.6.15 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：nonsingular 単体集合の極限での閉性。presheaf の点ごとの極限は非退化単体の頂点が相異なる性質を特定しない。 |
| 6.3.6.17 | none → none |  | B6再検索（現本体・ロックMathlib、移動後を含む）：有限な S に対し有限半順序の nerve からの universally localizing な表示。一般の単体圏からの局所化は有限性と半順序性を同時に主張しない。 |

## 検査

原文は Kerodon 公式小節の各項目Tagで照合。none は現本体・ロックしたMathlibを再検索し、近隣項目のソース・双対/限定版の候補も照合した。Archiveの宣言をown・partialの根拠にはしていない。宣言の存在と型はソースでの確認で、kernel確認ではない。
