# KB-W2 HA 第B章

原典の版を目次記載SHA-256と照合したPDFの本文と、現在のソースの宣言の型を読み比べた。kernel実行・Lean変更・ビルド・鍵はなし。

対象67行。旧状態：{'none': 60, 'partial': 7}。新状態：{'none': 59, 'partial': 7, 'own': 1}。partial_kind：{'stronger-hyp': 6, 'component': 1}。

既存own・mathlibなど対象外1行は全フィールド・引用符・改行をそのまま保存。対象行でもstatus/declarations/reason/partial_kind以外は不変。axioms/checkは旧記録であり今回のkernel確認結果ではない。

## 全対象行

| 番号 | 旧→新 | partial_kind | 理由 |
| --- | --- | --- | --- |
| B.0.19 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：marked edge・指定2単体・指定coneのcategorical patternとP-fiberedの六条件の定義は見つからない。指定辺を保つ相対functor spaceはあるが、全marked simplicial set圏とT・coneの条件を束ねた型はない。 |
| B.0.20 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：P上のmarked simplicial setに対するleft proper combinatorial simplicial model構造は見つからない。一般のpatternとそのanodyne生成族がなく、ModelCategory SSetを要求する条件付き構成もこのmarked圏の実在instanceの代替にはならない。 |
| B.0.21 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：全辺・全2単体・coneなしのcanonical patternがcoCartesian model構造を与える結果は見つからない。native coCartesian fibrationはあるが、marked圏の全弱同値・factorizationを持つmodel構造の比較はない。 |
| B.0.22 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：categorical patternの一般性と技術的な扱いの注意は見つからない。一般のmarked相対Homはあるが、当該patternのモデル構造の説明を形式化しない。 |
| B.0.23 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：P-fiberedな射からmarkingが一意に決まる結果は見つからない。個別のcoCartesian辺はあるが、Tと指定coneを持つP-fibered述語とmarkingを比較する型がない。 |
| B.0.24 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：弱可縮Kαと定数coneでP-fiberedの条件(5)(6)が自動となる結果は見つからない。通常の可縮Kanは、この全coCartesian分類図式の極限と相対limitの二条件を比較しない。 |
| B.0.25 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：K#×Xからのmarked写像を表現するMap#Sとsimplicial enrichmentは見つからない。指定辺をcoCartesianに送る頂点の全部分複体はあるが、任意P・任意二marked objectに対するこの全パラメータのmarked Homの普遍性ではない。 |
| B.0.26 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：P-fiberedの分類図式の極限条件をcoCartesian sectionの延長存在に弱める同値は見つからない。相対Kanの普遍性はあるが、当該Pの指定coneとsection制限の全比較がない。 |
| B.0.27 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：P-fibered Xへの引き戻しpattern π∗Pは見つからない。一般のmarkingの逆像は部品だが、指定coneの全liftを持つ新しいpatternの型を構成しない。 |
| B.0.28 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：全辺・全2単体・定数弱可縮coneでP-model構造がcoCartesian modelと一致する結果は見つからない。native fibrationはあるが、両marked model圏の実在instanceと全弱同値の比較がない。 |
| B.1.1 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：七種類のmarked生成射から弱飽和閉包で作るP-anodyne射の定義は見つからない。通常のinner anodyneはあるが、markingの追加と指定coneを含む全生成族の型はない。 |
| B.1.2 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：inner anodyne射をminimal markingでP-anodyneに送る結果は見つからない。通常のinner anodyneはあるが、全Pに対するmarked生成族への包含宣言がない。 |
| B.1.3 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：marked辺上のconeを作る任意cofibrationからのP-anodyne射は見つからない。通常のjoinとhorn生成は、このmarked coneの生成族への全移送を持たない。 |
| B.1.4 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：最終頂点を含む単体を追加して得るjoinのP-anodyne性は見つからない。通常のjoinのanodyneは、この全指定coneとmarkingの貼付けを備えない。 |
| B.1.5 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：任意marked object上の引き戻しpatternのanodyne射が元のP-anodyneと一致するiffは見つからない。通常の引き戻しは、この全pattern生成族の比較を持たない。 |
| B.1.6 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：P-anodyneに対する全延長性とP-fiberedの六条件のiffは見つからない。一般のhorn liftingはあるが、指定T・coneの全生成族とfibrancyの比較がない。 |
| B.1.7 | partial → partial | stronger-hyp | KB-W2原文・型再照合：仮定：p:X→∆nと外側hornの先頭辺を指定し、その辺がX全体でp-coCartesianのhorn liftingを持つ（Leanが強い：局所∆{0,1,n}での条件を全体のcoCartesian条件に強める）。結論：同じ底上で外側hornを充填する∆n→Xが存在（原典の延長の結論に一致）。局所triangleでのcoCartesian性だけからこの全体条件を導く部分は含まれない。 |
| B.1.8 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：categorical patternの積の指定coneを両側から作る定義は見つからない。通常のmarkingの積は部品だが、二種類のconeの全族を持つpattern型はない。 |
| B.1.9 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：cofibrationとP-anodyneのpushout productのP×P′-anodyne性は見つからない。通常のinner hornのpushout productはあるが、全marked生成族とcone条件に拡張する比較がない。 |
| B.1.10 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：Tとmarked辺の条件を持つ相対interval境界のP-anodyne性は見つからない。通常のprismのinner anodyneは、この全PとTによる相対markingの追加を持たない。 |
| B.1.11 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：T上のmarked outer 2-hornの包含のP-anodyne性は見つからない。通常のouter horn liftingは、このmarkingだけを増やすP生成族の比較ではない。 |
| B.1.12 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：指定cone上の∆1 joinの初辺を除いたmarkingから全markedへのP-anodyne性は見つからない。通常のjoinは、この二つのmarkingと指定coneの生成射を構成しない。 |
| B.1.13 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：点上のcanonical patternでleft anodyneを全markedのP-anodyneに送る結果は見つからない。通常のleft anodyneはあるが、marked P-modelの全生成族への比較がない。 |
| B.1.14 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：P-fibered終域へのmarked写像空間の制限がKan fibration、anodyneならtrivialとなる結果は見つからない。通常のrelativeFunctorSpaceのKan性はあるが、全Pとmarked cofibrationのMap#制限を構成しない。 |
| B.2.1 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：全P-fibered対象へのMap#で検出するP-equivalenceの定義は見つからない。通常の前合成同値はあるが、全patternとmarked試験対象の専用型を持たない。 |
| B.2.2 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：P-anodyneならP-equivalenceとなる結果は見つからない。通常のinner anodyneの前合成同値は、この全marked生成族と全P-fibered試験への比較ではない。 |
| B.2.3 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：cofibrationを縦に持つpushoutがP-equivalenceを保つ結果は見つからない。通常の単射と弱同値の貼付けは、この全P-equivalenceの試験条件を構成しない。 |
| B.2.4 | partial → partial | stronger-hyp | KB-W2原文・型再照合：仮定：X→S・Y→Sがleft fibrationであり全空間が準圏、fが底上で全頂点fiberの圏同値を誘導（Leanが強い：一般P-fiberedよりleft fibrationに限定）。結論：全空間のfは圏同値であり、この判定を∆1への引き戻しにも使える（(3′)から各辺上の圏同値(3)を得る方向のleft-fibrationの場合）。P-equivalenceとmarkedなhomotopy逆の全iffは含まれない。 |
| B.2.5 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：pattern圏のCartesian積がleft Quillen bifunctorとなる結果は見つからない。通常のinner pushout productはあるが、P×P′の全markedモデル構造の実在instanceへの比較がない。 |
| B.2.6 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：P-modelの弱同値とMap#によるP-equivalenceの一致は見つからない。一般の前合成同値は、このmarked圏のモデル構造の全弱同値を定めない。 |
| B.2.7 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：P-fibered終域へのfibrationの三条件のiffは見つからない。一般のcategorical fibrationのRLPはあるが、指定coneとmarkingを持つP-fibrancyとそのpullback patternの比較がない。 |
| B.2.8 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：辺・2単体・指定coneを保存するpattern-compatible射の定義は見つからない。通常の相対functor spaceの辺保存は、この三つのpatternデータの専用型を持たない。 |
| B.2.9 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：pattern-compatible射の後合成がleft Quillenとなる結果は見つからない。通常のOver.mapはあるが、全P-anodyneとmarkedモデル構造の保存の比較がない。 |
| B.2.10 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：pattern圏からmarked simplicial setへの忘却のleft Quillen性は見つからない。通常の忘却は、このconeを保持する点上patternのmodel構造の比較ではない。 |
| B.2.11 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：baseの同値だけをmarkするpatternで全空間のmarkingが全同値辺となる結果は見つからない。native coCartesian辺の可逆性判定はあるが、P-fiberedの全六条件とmarkingを構成していないため、そのまま適用する比較がない。 |
| B.3.1 | none → own |  | 原文の同じp:X→Δ²に対し、pullback.fst p (horn 2 1).ι はX×Δ²Λ²₁→Xそのものである。その射のIsQCatEquivalenceが原文のflatという定義全体と一致する。後続のhomotopy pushoutの説明は独立の番号付き主張ではない。 |
| B.3.2 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：flatnessと全C→E射のmiddle factorization圏の弱可縮性のiffは見つからない。通常のcomma圏の可縮性は、この全∆2上のfactorizationとflat条件を比較しない。 |
| B.3.3 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：distributorのcoendによる合成としてのflatnessの表示は見つからない。通常のtensor/coendは、この準圏のmiddle-factorizationの全Mapと比較されていない。 |
| B.3.4 | partial → partial | stronger-hyp | KB-W2原文・型再照合：仮定：p:X→∆2が全体でcoCartesian fibration（Leanが強い：各0頂点からmiddleへのcoCartesian liftだけでなく全辺のliftを仮定）。結論：inner horn Λ²₁の逆像包含は前合成同値、従ってcategorical equivalence（原典のflatnessの結論に一致）。原典の弱い片側lift仮定だけからの判定は含まれない。 |
| B.3.5 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：全終点にmiddle fiberからのCartesian liftが存在すればflatとなる結果は見つからない。coCartesian側の全fibrationでのhorn逆像の同値はあるが、この片側の局所Cartesian lift仮定からの比較宣言はない。 |
| B.3.6 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：simplicial categoryのcofibration包含からHom diagramのprojective cofibrancyを得る結果は見つからない。通常のprojective図式模型はあるが、この二fiberのenriched categoryのcofibrationとの全比較はない。 |
| B.3.7 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：inner horn上の両側初終対象を結ぶ局所化後Mapをmiddle fiberの型と同定する結果は見つからない。一般のlocalizationとcommaは、この特定のhorn分解の全Map比較を持たない。 |
| B.3.8 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：全2単体への引き戻しでのflatnessの定義は見つからない。coCartesianの場合のhorn逆像同値はあるが、全inner fibrationのこの局所flat述語を持たない。 |
| B.3.9 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：flatnessと各2単体・指定射のfactorization fiberの弱可縮性のiffは見つからない。一般のcosliceは、この全2単体上のmiddle頂点での型と比較されていない。 |
| B.3.10 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：全degenerate 2単体上のflatnessと∆2上の二定義の一致は見つからない。一般のinner fibrationは、degenerate simplexに沿うhorn逆像の同値の専用の比較を持たない。 |
| B.3.11 | partial → partial | component | KB-W2原文・型再照合：仮定：p:X→SがcoCartesian fibration（HAの前半と一致）。結論：各2単体に引き戻したinner hornの逆像包含は前合成同値、従ってcategorical equivalence（coCartesianなpがflatという前半のflatnessの結論に一致）。Cartesian側の対称な主張とcategorical fibrationの全比較をこの行の宣言だけでは含まない。 |
| B.3.12 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：flat inner fibrationの任意基底変換による保存は見つからない。一般のinner fibrationの基底変換はあるが、任意flat pのhorn逆像同値を束ねた保存を構成しない。 |
| B.3.13 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：flat inner fibrationのcoslice間の誘導射のflatnessは見つからない。一般のcoslice fibrationはあるが、flatnessに必要な全horn逆像の比較がない。 |
| B.3.14 | partial → partial | stronger-hyp | KB-W2原文・型再照合：仮定：pがcoCartesian fibrationで任意inner-anodyne A→Bと底への射を指定（Leanが強い：一般flat inner fibrationよりcoCartesianの場合に限定）。結論：その引き戻しの射が前合成同値、従ってcategorical equivalence（条件(1)にこの場合一致）。全inner fibrationに対する(1)⇔flatnessの一般のiffは含まれない。 |
| B.3.15 | partial → partial | stronger-hyp | KB-W2原文・型再照合：仮定：A,B,Cは準圏、A→Bは圏同値、p:C→Bは全単射な前合成同値を持ち上げるEquivalenceLiftingを満たす（Leanが強い：A,Bの準圏性と操作的RLPを明記）。結論：同じpullback射A×B C→Cは前合成同値、従って圏同値（指定された引き戻し比較の結論に一致）。任意simplicial set A,Bおよびflat categorical fibrationの定義だけからの全比較は含まれない。 |
| B.3.16 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：flat categorical fibrationの合成のflat categorical性は見つからない。通常のfibrationの合成はあるが、任意flatの逆像同値の全合成を構成する宣言はない。 |
| B.3.17 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：対応M→∆1をsection圏のcylinderと両端で貼った図式のcategorical equivalenceは見つからない。通常のsectionとpushoutはあるが、この全対応のcylinderによる表示の普遍比較を持たない。 |
| B.3.18 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：∆3上のflat fibrationの両端間のmiddle二頂点factorization圏の弱可縮性は見つからない。一般のhorn逆像同値は、任意flatから当該二段factorizationへの比較を持たない。 |
| B.3.19 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：標準単体の頂点全射によるflat inner fibrationの合成保存は見つからない。通常の単体写像は、この全flat射のhorn逆像と区間collapseの比較を持たない。 |
| B.3.20 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：∆n上のflat fibrationの全middle頂点factorization圏の弱可縮性は見つからない。一般のcommaは、この任意nのflatnessからの全中間表示を構成しない。 |
| B.3.21 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：∆n×∆m上のflat fibrationの第二射影との合成のflatnessは見つからない。通常のproduct射影は、この全flat条件と任意2単体の逆像同値の比較を持たない。 |
| B.4.1 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：九つの辺・2単体・cone条件を持つpatternの引き戻しのleft Quillen性は見つからない。通常のpullbackの随伴はあるが、全P-model構造とmarked生成族の保存を持たない。 |
| B.4.2 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：marked spanと八条件によるpattern間のpull-pushのleft Quillen性は見つからない。通常のOverのbase changeは、この全patternのcone条件とmodel構造の比較を持たない。 |
| B.4.3 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：同値辺のみmarkしconeなしの場合の八条件の簡略化は見つからない。一般の同値辺はあるが、この二つのpatternの全Quillen条件の比較がない。 |
| B.4.5 | partial → partial | stronger-hyp | KB-W2原文・型再照合：仮定：π:Y→ZをcoCartesian fibration、φを自明な積束Y×D→Y、Dを準圏に限定（Leanが強い：coCartesian π・定数のfiber）。結論：πの各逆像からDへの写像を表す相対指数の射影はCartesian fibrationとなる（この定数束模型でのcategorical fibration保存の強い部分）。一般flat categorical π・任意categorical φの右Quillen性と、右随伴で選んだ依存積との全比較は含まれない。 |
| B.4.6 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：trivial Kan fibration πに対する依存積への比較θのcategorical equivalenceは見つからない。通常の依存積とtrivial Kanのsectionはあるが、原典に記されたθ:X→π∗Xとそのfiberwise homotopy逆の指定比較を与える宣言はない。 |
| B.4.7 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：trivial Kanな基底の置換による依存積の制限比較のcategorical equivalenceは見つからない。通常の依存積はあるが、この全categorical fibration上での基底置換と弱同値保存の比較を持たない。 |
| B.4.8 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：cosieveと各fiberのCartesian liftおよび相対right Kan条件から最終outer hornの全延長を得る結果は見つからない。一般の相対Kan延長はあるが、この特定のcosieveと全基底hornの制約下でのextension宣言ではない。 |
| B.4.9 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：依存積のcosieveへの制限と相対right Kan条件による相対limit判定は見つからない。通常のfiberwiseHomはあるが、一般flat p・cosieve・指定coneを持つ全相対極限の比較がない。 |
| B.4.10 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：Cartesian πとφのcoCartesian lift条件による依存積のcoCartesian性と辺の点別判定は見つからない。coCartesian πと定数終域の相対HomのCartesian性はあるが、反対の向きかつ任意φの当該依存積と辺の比較には新しい構成が必要である。 |
| B.4.11 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：marked辺と指定2単体上のlift条件から依存積のcategorical fibration・局所coCartesian性・辺判定を得る四結論は見つからない。一般のfiberwiseHomは、この全Pの相対遷移とTの条件を持たない。 |
| B.4.12 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：依存積の指定coneの相対limit条件とfiberごとの極限延長の存在は見つからない。通常の相対Kanの全Hom普遍性はあるが、任意flat categorical fibrationとcoCartesianなcone逆像に対する全族の比較がない。 |

## 読取りと再検索

原文・候補の型・現在の引用番号索引・小節ごとの現本体とロックMathlibの再検索はgit外の章別証拠。OE-W1 module-mapと宣言索引を使って移動後の名前・所在・行を確認した。ArchiveとBS draftsの宣言は正の根拠にしない。検索の全ヒットを形式検証したという意味ではない。
