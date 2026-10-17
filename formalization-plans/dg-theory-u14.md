# U14：指定dg生成元とendomorphism表示

正本は `dg-theory.md` §15冒頭・§15.4。任意可換環、非有界cochain複体、
微分次数+1、ホモトピー次数−1、Mathlib Enrichedを主モデルとする。
引用・追加公理・sorryは導入しない。U14全受入はまだ未完。

## U14a.1：一対象EndとHom bimodule（2026-10-17）

- `Endomorphism/Basic.lean`：指定対象で添字付けした一対象型、元の全Hom複体・
  単位・forward合成を継承するdg構造、指定対象への包含。
  dg関手に沿うEndの写像と包含の可換正方形も証明。
- `Endomorphism/HomBimodule.lean`：右End(E)・左Dのbimoduleの値はHom(E,X)。
  右作用は既存representableの制限、左作用はdg Yonedaの全次数Hom写像のE成分。
  左右の交換は主Hom endの豊穣自然性で保持する。
  E自身の像がEnd(E)の正則representableになることを、作用も含めて証明。
  U13の `SmallPerfectDGModuleOver` 内の指定対象への適用を公開。
- 対象宇宙は独立。大きいenhancement全体のsmall性を仮定せず、
  U13の小さい代表系を用いる。生成集合を無限直和で一対象化する操作はしていない。
- 検証：`lake build SerrePositivity.DifferentialGraded.Endomorphism.ChecksBasic` 成功。
  同ファイルの8主要宣言の `#print axioms` は全て
  `propext`, `Classical.choice`, `Quot.sound` の標準3公理のみ。

## U14a.2：balanced評価と複体値随伴との比較（2026-10-17）

- `Endomorphism/Evaluation.lean`：Hom(X,E)の左End(E)加群と
  Hom(E,Y) ⊗_End(E) Hom(X,E) → Hom(X,Y)を構成。
  純粋斉次元の評価は `(-1)^(rs) forward(t,m)`。
  balanced関係の証明は結合則と指数
  `rp + (r+p)s = r(p+s) + ps` を使い、負次数も除外しない。
- `Endomorphism/EvaluationAdjunction.lean`：評価の転置を閉零End(E)加群射として構成し、
  U11のtensor–Hom随伴の単位との式と余単位による評価の因子化を証明。
  これはHom(X,E)を固定する複体値随伴であり、enhancementとEnd(E)加群の間の
  再構成随伴の完成を主張するものではない。
- `ChecksEvaluation.lean`：整数係数の次数−1・+1での評価、およびZMod 2係数の
  非有界複体に対する一対象構造を検証。
  対象ビルド成功。8主要宣言の公理は標準3公理のみ。

## U14a.3：U12dの導来tensorとの評価比較（2026-10-17）

- `Endomorphism/DerivedEvaluation.lean`：Hom(E,Y)の右End(E)射影解像度のaugmentationを
  tensorしてbalanced評価と合成する。既存 `moduleDerivedTensorRight` の計算同型を使い、
  導来tensorからQ(Hom(X,Y))への射を構成。
- 比較射のaugmentationとの因子化はKでのみ成立する。
  chain-levelで厳密可換とはせず、tensorのホモトピー保存を通じてD(A)での可換性を証明。
  `endomorphismDerivedEvaluation_resolution` により、任意の右射影解像度で計算できる。
  評価の同型性や再構成随伴の存在は、この比較からは主張しない。
- `lake build SerrePositivity.DifferentialGraded.Endomorphism.ChecksDerived` 成功。
  4主要宣言の公理監査は標準3公理のみ。

## U14a.4：Endのshift・underived係数変更図式（2026-10-17）

- `Endomorphism/Compatibility.lean`：Endのunderived係数変更から、係数変更した指定対象の
  Endへのdg関手を構成し、指定対象への包含の正方形を証明。
  U12fの `ScalarExtension.DGBaseChange` を使い、平坦性は仮定しない。
  全Homの係数変更比較の同型性や導来版との一致は含まない。
- U13の実際のdg shiftについて、Endの写像と指定対象の包含の正方形を証明。
  再構成関手の三角性はなお未証明。
- `lake build SerrePositivity.DifferentialGraded.Endomorphism.ChecksCompatibility` 成功。
  3主要宣言の公理は標準3公理のみ。
- ルートにはこの公開入口のimportだけを追加し、`git add -p`で当該hunkのみstage。
  `dg-theory.md`・README・Stageおよび既存Perfect/Tensor/Derived/Bimodule/Quotientは未編集。

## U14a.5：大きい全加群dg圏上のHom・tensor関手（2026-10-17）

- `Endomorphism/LargeHomBimodule.lean`：Small Dを仮定せずHom(E,−)を構成。
  Yoneda拡張のE成分を直接用い、D上のHom endは取らない。
  Small DがあるときにはU14a.1の構成と一致する。
- `Endomorphism/ModuleComparison.lean`：実際の右D加群Eに対して、
  全加群dg圏から右End(E)加群へのHom関手と、逆向きのtensor関手を構成。
  後者は既存のbimodule tensor合成に恒等dg関手を代入したもの。
  全加群の対象型のsmall性を仮定していない。
- Hom(E,E)が正則End(E)加群になる等式、および正則加群のtensor像がEに戻る
  実際のD加群同型を証明。後者は既存 `BimoduleTensor.rightUnitIso` を使う。
  U13の指定perfect dg加群への適用を公開。
- `ChecksModuleComparison` と更新した `ChecksCompatibility` の対象ビルド成功。
  新規9主要宣言の公理監査は標準3公理のみ。

## 並行作業との境界で生じたコミット混入

`f01103ce` のルート変更には、自分のimportに加え、並行作業が追加した
`public import SerrePositivity.CLMST.PerfectoidIdealTorCover` が1行含まれた。
`git add -p`では自分のhunkだけをstageしたが、その後の
`git commit --only SerrePositivity.lean ...` が作業ツリーの別hunkも含めたのが原因。
検出時には他作業の後続コミットが進んでいたため、共有履歴を書き換えず当該行を保持した。
この混入を除き、既存の他系列ファイルの内容は変更していない。
以後のコミットはU14専用ファイルだけに限定する。

## U14a.6：再構成tensorから実際のdg加群への評価（2026-10-17）

- `ModuleTensorElements.lean`：再構成tensorに残る右D作用の全次数成分を証明。
  次数pのD作用は次数rのEnd加群成分を越えるので符号 `(-1)^(pr)` を持つ。
- `ModuleEvaluation.lean`：Hom(E,M) ⊗_End(E) E(d) → M(d)をbalancedなchain mapとして構成し、
  全次数のD作用との自然性を証明して実際の閉零D加群射へ組み立てた。
  単に各成分の複体射を置いたものではなく、主Hom endの射である。
- `lake build SerrePositivity.DifferentialGraded.Endomorphism.ChecksModuleEvaluation` 成功。
  9主要宣言の公理は標準3公理のみ。

## U14a.7：再構成Homへの実際のEnd(E)加群挿入（2026-10-17）

- `ModuleInsertion.lean`：Nの元mを、Eの元tにm⊗tを対応させるHom要素に送るchain mapを構成。
  D上の全次数自然性を主Hom endの普遍性で課し、balanced関係を使ってEnd(E)作用との
  可換性も証明した。結果は実際の閉零End(E)加群射 `N → Hom(E,N⊗_End(E)E)`。
- 入力総次数を任意の和表示にしたD作用公式を `ModuleTensorElements.lean` に追加。
  中間次数s+pを固定し、p+sとの比較に暗黙の型同一視を使わない。
- `lake build SerrePositivity.DifferentialGraded.Endomorphism.ChecksModuleInsertion` 成功。
  新規8主要宣言の公理は標準3公理のみ。
- 単位・余単位としての両加群変数の自然性と三角恒等式は次の証明義務。
  作業は通常の追加コミットのみで進め、amend・rebase・resetは行わない。

## U14a.8：Hom・tensor関手の全Hom写像と閉零成分（2026-10-17）

- `ModuleFunctorMaps.lean`：Hom関手の全Hom写像を共変representableの写像として計算。
  tensor関手の全Hom写像は既存balanced tensorの右Hom写像となることを証明。
  双方の生成元公式と、閉零の通常射との比較も公開。
- Hom側の閉零射の成分は、元のD加群射によるHom要素の後合成として計算できる。
  tensor側はEnd(E)加群成分だけを動かす。随伴の自然性・三角恒等式の検証に使う。
- `lake build SerrePositivity.DifferentialGraded.Endomorphism.ChecksModuleFunctorMaps` 成功。
  7主要宣言の公理は標準3公理のみ。

## U14a.9：実際の加群圏上の再構成随伴（2026-10-17）

- `ModuleAdjunction.lean`：挿入と評価の加群変数についての自然性を証明し、
  閉零加群圏上の単位・余単位の自然変換へまとめた。
  純粋斉次tensorおよび全Hom要素で両三角恒等式を直接証明し、
  `endomorphismModuleAdjunction : (-⊗_End(E) E) ⊣ Hom(E,-)` を構成。
- Eには任意の実際の右D加群を許し、このunderived随伴に射影性・compact性は不要。
  Dのsmall性だけを仮定し、全加群dg圏をsmallとはしていない。
  U13の実際のperfect dg加群にも適用できる例を監査ファイルに置いた。
- `ChecksModuleAdjunction` と更新した `ChecksCompatibility` の対象ビルド成功。
  単位・余単位・両三角恒等式・随伴の5主要宣言の公理は標準3公理のみ。
  既存公開入口 `Compatibility.lean` へimportを追加し、ルートは編集していない。
- 導来随伴、Perf比較、Hom擬同型と本質的全射の証明、三角性との整合性は未完。

## U14a.10：射影的指定対象からの導来Hom（2026-10-17）

- `DerivedHom.lean`：Hom関手の閉零成分が既存 `eHomWhiskerLeft` に一致することを証明。
  Eのホモトピー射影性の下で、既存 `moduleHomotopicallyProjective_postcompose_quasiIso`
  によりHom(E,−)の擬同型保存を得る。
- `moduleDerivedLift` を使い主導来加群圏間の関手へ降ろした。
  指定局所化と厳密に可換となる因子化等式を公開し、U13のperfect dg代表に保持された
  射影性から得る導来Homも構成した。Eをcompact generatorと仮定したことにはしない。
- `ChecksDerivedHom` と更新した `ChecksCompatibility` の対象ビルド成功。
  6主要宣言の公理は標準3公理のみ。新規sorry・axiom・引用はない。
- 次はtensor側をEnd(E)上の射影解像度で導来化し、解像度計算・Hom側との導来随伴を
  接続する。その後でthick生成によるPerf比較の二つの証拠を証明する。

## U14a.11：再構成tensorの導来化と任意解像度計算（2026-10-17）

- `DerivedTensor.lean`：End(E)上の任意の右射影解像度族からK(End(E))を経由して
  主D(D)へ送る関手を構成。標準semifree解像度族を使う主導来tensorも定義。
  Eの成分のA-flat性やEのホモトピー射影性は、この構成には不要。
- 族の選択独立な自然同型と自己一致・推移整合性を証明。
  二つの任意射影解像度の実際のtensor計算も比較し、任意解像度での計算同型を公開。
  tensor後の擬同型保存は、射影的右加群間の擬同型に限定して証明した。
  一般の右加群間の擬同型をunderived tensorが保つとはしていない。
- `lake build SerrePositivity.DifferentialGraded.Endomorphism.ChecksDerivedTensor` 成功。
  14主要宣言の公理は標準3公理のみ。

## U14a.12：U12d導来tensorとの全射自然な評価比較（2026-10-17）

- `DerivedTensorEvaluation.lean`：underived tensorのD評価を既存balanced tensor関手と
  自然同型で比較。主Kの境界商を通じ、任意射影解像度族の再構成導来tensorを
  各D対象で評価するとU12dの既存導来tensorになるという自然同型を構成。
  標準解像度の場合の正方形も公開した。全導来射に自然であり、対象ごとの同型だけではない。
- `lake build SerrePositivity.DifferentialGraded.Endomorphism.ChecksDerivedTensorEvaluation` 成功。
  6主要宣言の公理は標準3公理のみ。

## U14a.13：再構成随伴の主ホモトピー圏への降下（2026-10-17）

- `HomotopyAdjunction.lean`：閉零加群圏上の単位・余単位を境界商に送り、
  主K(End(E))と主K(D)の間の随伴を構成。商関手の充満性で任意の商射に自然性を拡張し、
  両三角恒等式を元の加群圏上の恒等式から証明した。
- `lake build SerrePositivity.DifferentialGraded.Endomorphism.ChecksHomotopyAdjunction` 成功。
  5主要宣言の公理は標準3公理のみ。

## U14a.14：主Kのcoyonedaによる射影性判定（2026-10-17）

- `ProjectiveCriterion.lean`：K内の射影的加群のretractはホモトピー射影的であることを証明。
  前合成のHom複体へのホモトピー保存を使い、各Homologyを零対象のretractとして計算した。
- Kのcoyoneda Hom(P,−)が指定擬同型を反転するなら、標準射影解像度のaugmentationが
  K内で分裂することを証明し、ホモトピー射影性との同値な判定を得た。
  compact生成定理・引用・新たな仮定は導入していない。
- `lake build SerrePositivity.DifferentialGraded.Endomorphism.ChecksProjectiveCriterion` 成功。
  3主要宣言の公理は標準3公理のみ。

## U14a.15：再構成tensorのホモトピー射影性保存（2026-10-17）

- `TensorProjective.lean`：Eがホモトピー射影的なとき、Homの主K関手が指定擬同型を保つ
  ことを証明。主Kの再構成随伴とU14a.14の判定を使い、再構成tensorが射影的右End(E)
  加群を射影的右D加群へ送ることを証明した。
- 証明では始域のprojectivityをHomの擬同型不変性へ移し、随伴のHom同値で輸送している。
  EやHom(E,E)のA上のflat性で代用していない。
- `lake build SerrePositivity.DifferentialGraded.Endomorphism.ChecksTensorProjective` 成功。
  2主要宣言の公理は標準3公理のみ。

## U14a.16：主導来圏の任意対象でのtensor–Hom射集合同値（2026-10-17）

- `DerivedHomEquiv.lean`：Eのホモトピー射影性の下で、射影的右End(E)加群Pについて
  `Hom_D(D)(P⊗E,M) ≃ Hom_D(End(E))(P,RHom(E,M))` を構成。
  tensorの射影性保存、主Kの随伴、既存の射影的始域の局所化Hom計算を順に使った。
- 標準射影解像度と任意解像度計算同型を用い、主導来圏の任意対象X,Yについて
  `Hom(LTensor(X),Y) ≃ Hom(X,RHom(Y))` を得た。
  射集合同値の両変数自然性はまだ別の証明義務であり、導来随伴の完成とはしていない。
- `ChecksDerivedHomEquiv` と更新した `ChecksCompatibility` の対象ビルド成功。
  4主要宣言の公理は標準3公理のみ。最新APIを既存のU14公開入口へimportし、ルートは未編集。

## U14a.17：射影的始域における導来Hom同値の自然性（2026-10-17）

- `DerivedProjectiveHomNaturality.lean`：主Kの随伴Hom同値が実際の加群射上で
  閉零加群圏の随伴と一致することを証明。射影的始域の導来Hom同値の具体的計算式を得た。
- 導来Homの計算同型の逆の自然性と、導来Hom同値の両変数における
  実際の加群射に対する自然性を証明。導来射自体には射影的始域からの持上げを使った。
  任意対象の解像度比較および局所化で追加される逆射への自然性の拡張は次の段階。
- `lake build SerrePositivity.DifferentialGraded.Endomorphism.ChecksDerivedProjectiveHomNaturality`
  成功。5主要宣言の公理は標準3公理のみ。

## U14a.18：解像度計算と導来Hom同値の加群射自然性（2026-10-17）

- `DerivedTensorNaturality.lean`：任意の射影解像度族に対し、導来tensorの計算同型と
  解像度間に持ち上げた加群射の可換図式を証明。標準解像度での逆同型の図式も得た。
- `DerivedHomNaturality.lean`：解像度augmentationの導来可換図式と逆同型の図式を証明し、
  任意の加群対象の導来tensor–Hom同値について、両変数の実際の加群射に対する自然性を証明。
- `lake build SerrePositivity.DifferentialGraded.Endomorphism.ChecksDerivedHomNaturality`
  成功。8主要宣言の公理は標準3公理のみ。局所化の逆射への拡張は次の段階。

## U14a.19：主導来再構成随伴の完成（2026-10-17）

- `LocalizationHomNaturality.lean`：局所化で生成される合成・逆射について自然性を証明し、
  局所化前の射で検証したHom比較の自然性を全局所化射へ拡張する一般補題を構成。
- `DerivedAdjunction.lean`：任意対象のtensor–Hom射集合同値の両変数自然性を全導来射で証明。
  `endomorphismDerivedAdjunction` とその単位・余単位、両三角恒等式を構成した。
  仮定はEのホモトピー射影性であり、compact生成性やMorita同値は主張していない。
- `ChecksDerivedAdjunction` と更新した `ChecksCompatibility` の対象ビルド成功。
  新規9主要宣言の公理は標準3公理のみ。既存のU14公開入口からimportし、ルートは未編集。

## U14a.20：指定enhancementのEndと導来生成対象の比較（2026-10-17）

- `DerivedGenerators.lean`：射影的加群の恒等解像度で導来tensorを計算。
  正則End(E)加群の導来tensor像とEとの同型、およびEの導来Hom像と正則加群との同型を構成。
  前者は既存のYoneda balanced tensor単位を導来圏へ送ったもの。
- `EnhancementComparison.lean`：U13の充満dg enhancement内のEnd(E)と全加群内のEnd(E.val)
  の比較を構成。全Homの恒等写像による擬同型とH⁰の本質的全射を個別に証明。
  これは同じEndの二つの表示の比較であり、U14bのPerf同値ではない。
- enhancement上のHom関手を定義し、元のHom(E,−)がEnd比較に沿った制限と一致することを証明。
  Eの射影性はU13の対象の証拠から取得して導来随伴に接続した。
- `ChecksEnhancementComparison` と更新した `ChecksCompatibility` の対象ビルド成功。
  新規11主要宣言の公理は標準3公理のみ。U14公開入口へimport済み。

## U14a.21：評価成分のshift・cone比較図式（2026-10-17）

- `ShiftConeComparison.lean`：Hom(E,−)と再構成tensorの評価成分を複体値dg関手として定義。
  前者が既存の共変representableと、後者が既存のbalanced rightTensorDGと一致することを証明。
- 全Hom・各tensor成分のshift同型を構成。tensor側の同型は既存のbalanced tensorのshift同型と
  同一であることを、全次数写像と斉次shift単位による成分計算で証明した。
- 両関手の標準coneに対する複体同型を構成し、次数0および−1の両包含との可換図式を証明。
  これは評価後の図式であり、Perf比較の三角性・導来係数変更の完成とはしていない。
- `ChecksShiftConeComparison` と更新した `ChecksCompatibility` の対象ビルド成功。
  新規11主要宣言の公理は標準3公理のみ。U14公開入口へimport済み。

## U14b.1：指定対象を始域とする全Hom写像の同型（2026-10-17）

- `GeneratorHomIso.lean`：正則End加群とHom(E,E)との加群同型を成分の恒等写像として照合。
  任意の右D加群Mについて、Hom関手の全次数写像をその同型に沿って前合成すると、
  既存のdg Yoneda同型の逆になることを証明した。
- したがってHom(E,−)の `(E,M)` における全Hom写像はchain isoであり、特に擬同型。
  この基点の主張にはEのホモトピー射影性・compact性は不要。
  thick生成からの一般の始域への拡張と本質的全射は未証明である。
- `ChecksGeneratorHomIso` と更新した `ChecksCompatibility` の対象ビルド成功。
  新規6主要宣言の公理は標準3公理のみ。U14公開入口へimport済み。

## U14b.2：全Hom比較のホモトピーretract安定性（2026-10-17）

- `HomMapNaturality.lean`：任意のdg関手の全Hom写像について、閉零射による前合成・後合成との
  可換式を、豊穣合成の保存から証明。
- `HomComparisonRetracts.lean`：始域のK(D)内retractに沿って、再構成Hom写像の擬同型性が
  保たれることを証明。各次数のHomology写像のretractArrowを実際に構成した。
- 全終域に対する擬同型条件をK(D)上の対象の性質として定義し、生成対象Eを含むことと
  retract安定性を証明。shift・cone閉性とthick生成からの比較はなお別義務である。
- `lake build SerrePositivity.DifferentialGraded.Endomorphism.ChecksHomComparisonRetracts` 成功。
  新規7主要宣言の公理は標準3公理のみ。

## U14b.3：全Hom比較の反変shift図式とshift閉性（2026-10-17）

- `HomComparisonShift.lean`：dg関手の全Hom写像を、終域固定の反変representable間の
  全次数自然なchain map族として照合。反変複体値dg関手のshift同型に対する自然性を証明。
- その図式から、再構成Hom比較の擬同型性が始域の任意整数shiftに安定であることを証明。
  K(D)内の比較成立対象の性質に `IsStableUnderShift ℤ` を構成した。
- `ChecksHomComparisonShift` と更新した `ChecksCompatibility` の対象ビルド成功。
  新規6主要宣言の公理は標準3公理のみ。retract閉性も公開入口からimport済み。
  cone閉性、thick生成による全Hom比較、本質的全射は残る。

## U14b.4：dg関手による全次数分裂の保存（2026-10-17）

- `GradedSplitRelations.lean`：既存の全次数分裂を零次数Hom要素の4つの行列恒等式へ変換。
- `ZeroHomComponents.lean` と `GradedSplitOfElements.lean`：微分と可換とは限らない零次数Hom要素から
  全斉次作用と可換する次数付き成分を取り出し、行列恒等式から既存のModuleGradedSplitを復元。
- `GradedSplitImage.lean`：任意の主dg加群間のdg関手について、全Hom写像を用い分裂要素を送り、
  全次数分裂の保存を構成。chain mapでない分裂をchain mapと誤認していない。
  coneのHom短完全列の比較に使用する。
- `lake build SerrePositivity.DifferentialGraded.Endomorphism.ChecksGradedSplitImage` 成功。
  新規14主要宣言の公理は標準3公理のみ。

## U14b.5：短完全列の比較と全Hom比較の三角閉性（2026-10-17）

- `ShortExactComparison.lean`：複体の短完全列の間の射について、両端が擬同型なら中央も擬同型。
  前後のconnecting morphismを含む5項のHomology列を構成し、Mathlibの五項補題を適用した。
- `HomComparisonCone.lean`：全次数分裂のHom短完全列の間に、dg関手の全Hom写像を成分とする
  射を構成。分裂のdg像にも既存のHom短完全性を適用し、再構成比較のcone閉性を証明。
- K(D)の全distinguished triangleへ同型で運び、全Hom比較成立対象の性質が三角部分圏である
  ことを証明。retract閉性と合わせ、指定生成対象を含むthickな性質を得た。
- `ChecksHomComparisonCone` 対象ビルド成功。新規9主要宣言の公理は標準3公理のみ。

## U14b.6：thick生成仮定からenhancement上の全Hom擬同型（2026-10-17）

- `ThickHomComparison.lean`：指定加群EのK(D)内のthick閉包を、零対象・整数shift・
  distinguished triangle・retractによる有限操作として定義。その閉性と、Eを含む任意の
  thick部分圏への包含を証明した。
- U13の指定enhancementがEからこの閉包で生成される、という明示的なthick生成仮定を定義。
  この仮定の下で `perfectEndomorphismModuleHom_homQuasiIso` を証明した。
  全終域について成立するHom比較のthickな性質を適用しており、結論の擬同型を仮定に
  組み込んでいない。H⁰本質的全射・像のPerf保存はなお別義務である。
- `ChecksThickHomComparison` と更新した `ChecksCompatibility` の対象ビルド成功。
  新規4主要宣言の公理は標準3公理のみ。最新APIをU14公開入口へimport済み。

## U14b.7：全Hom擬同型とH⁰完全忠実性の照合（2026-10-17）

- `QuasiFullyFaithful.lean`：任意のdg関手の全Hom写像と、既存のH⁰射–Homology同値が
  自然に可換になることを証明。全Hom擬同型からH⁰の射集合写像の全単射を導いた。
- thick生成仮定の下でU13からの再構成Hom関手のH⁰完全忠実性を個別に構成。
  余域は現段階では全右End加群のK圏であり、Perfへの像の制限や本質的全射を
  既に証明したとはしていない。
- `ChecksQuasiFullyFaithful` と更新した `ChecksCompatibility` の対象ビルド成功。
  新規7主要宣言の公理は標準3公理のみ。U14公開入口へimport済み。

## U14b.8：加群値dg関手の実際のcone・shift同型（2026-10-17）

- `ModuleConeImage.lean`：全Hom写像で標準coneの次数−1包含を送り、既存の境界からの
  cone延長を使い加群射を構成。各評価が既存の複体値cone比較と一致することを証明し、
  評価による同型反映から実際の主加群同型を得た。次数0包含の図式も証明。
- `ModuleShiftImage.lean`：全次数Hom要素の自然性からshift比較の全斉次作用に対する
  自然性を導き、評価成分のshift同型を実際の主加群同型へ組み立てた。
- `ChecksModuleConeImage` と `ChecksModuleShiftImage` の対象ビルド成功。
  新規11主要宣言の公理は標準3公理のみ。

## U14b.9：Hom像のPerf保存と主導来HomのPerfへの制限（2026-10-17）

- `PerfectImage.lean`：加群値dg関手の主Kから主導来圏への像に対し、整数shift同型と
  cone同型を接続。像がperfectとなる始域の性質がshift・三角形・retractに閉じることを証明。
- 像がperfectである指定対象Eの有限thick閉包はperfectに送られることを導いた。
  これをHom(E,−)と正則End加群に適用し、明示したthick生成仮定からHom像のPerf保存を証明。
- 任意の主Perf対象をU13の射影解像度で表して導来Homに輸送し、主導来Hom関手の
  実際のPerf制限 `perfectEndomorphismHomToPerfect` を構成した。
  本質的全射や同値はまだ結論していない。
- `ChecksPerfectImage` と更新した `ChecksCompatibility` の対象ビルド成功。
  新規10主要宣言の公理は標準3公理のみ。U14公開入口へimport済み。

## U14b.10：Hom像のホモトピー射影性（2026-10-17）

- `HomotopyImage.lean`：加群値dg関手の主Kにおけるshift・cone同型を用い、指定対象の
  有限thick閉包の像が、像を含む任意のthick部分圏に含まれることを証明。
- `ProjectiveImage.lean`：主K内のホモトピー射影的対象の性質が、retract・整数shift・
  distinguished triangleに閉じることを証明した。
- 正則End加群の射影性とHom(E,E)との同型から、thick生成の下でHom像が実際に
  ホモトピー射影的であることを証明。perfectな導来像だけで代用していない。
- `ChecksProjectiveImage` 対象ビルド成功。新規9主要宣言の公理は標準3公理のみ。

## U14b.11：実際のperfect dg enhancement間の比較関手（2026-10-17）

- `PerfectDGComparison.lean`：Hom像のホモトピー射影性とperfect性の両証拠を保持し、
  U13の指定enhancementからEnd(E)上のperfect dg enhancementへの実際のdg関手を定義。
- 全Hom擬同型とH⁰の完全忠実性を、この関手について個別に証明。
  全加群への包含とのdgレベルの可換正方形も証明した。
- `ChecksPerfectDGComparison` と更新した `ChecksCompatibility` の対象ビルド成功。
  新規5主要宣言の公理は標準3公理のみ。U14公開入口へimport済み。
  H⁰の本質的全射はまだ証明していない。

## U14b.12：enhancement比較と主Perf制限の自然同型・完全忠実性（2026-10-17）

- `DerivedHomHomotopyComparison.lean`：主KのHom関手の局所化と主導来Hom関手を、
  商の自然同型の持上げを用い全K射で自然に比較した。
- U13のenhancement同値と再構成dg関手の包含正方形を接続し、主導来圏内および
  主Perf内の自然な比較正方形を構成。
- 主Perf間の導来Hom制限が、U13同値の逆・dg比較のH⁰・U13同値の合成と自然同型で
  一致することを証明。その同型から主Perf比較関手の完全忠実性を導いた。
- `ChecksDerivedHomHomotopyComparison` と更新した `ChecksCompatibility` の対象ビルド成功。
  新規7主要宣言の公理は標準3公理のみ。U14公開入口へimport済み。

## U14b.13：本質的像の正則生成対象・retract・整数shift（2026-10-17）

- `EssentialImageRetracts.lean`：冪等完備な始域を持つ完全忠実関手の本質的像の
  retract閉性を、始域で冪等射を分裂して同型を構成することで証明。
  これを主Perfの導来Hom比較に適用した。
- 指定対象Eの導来Hom像が正則End加群である計算を用い、正則生成対象が本質的像に
  入ることを証明。これは全対象に対する本質的全射とは分けている。
- `EssentialImageShift.lean`：生の加群表示・加群shift同型・局所化のshift比較を接続して、
  本質的像の任意整数shift閉性を証明した。
- `ChecksEssentialImageRetracts` と `ChecksEssentialImageShift` の対象ビルド成功。
  新規9主要宣言の公理は標準3公理のみ。

## U14b.14：本質的像のdistinguished triangle閉性（2026-10-17）

- `EssentialImageTriangles.lean`：本質的像の二つの対象の間の射を完全性で始域のPerfへ
  持ち上げ、射影解像度間の実際の閉零射で表示した。
- 導来Homの計算同型の自然性から最初の射の可換正方形を証明し、標準coneの
  dg像の同型と三角形の同型延長を使って第三対象が本質的像に入ることを証明した。
- `ChecksEssentialImageTriangles` 対象ビルド成功。新規3主要宣言の公理は標準3公理のみ。

## U14b.15：主Perf同値とenhancement準同値（2026-10-17）

- `PerfectEquivalence.lean`：本質的像の三角性・retract閉性と正則生成対象の包含から、
  U13のPerfの最小thick性を適用し、全perfect対象が本質的像に入ることを証明。
- 主導来HomのPerf制限の本質的全射性を構成し、完全忠実性と合わせて
  `perfectEndomorphismEquivalence` を構成した。順関手は実際の主導来Homの制限である。
- U13の同値との自然な正方形から、enhancement間のdg比較のH⁰本質的全射を別に証明し、
  既に証明した全Hom擬同型と組み合わせて `perfectEndomorphismDG_quasiEquivalence` を得た。
- `ChecksPerfectEquivalence` と更新した `ChecksCompatibility` の対象ビルド成功。
  新規7主要宣言の公理は標準3公理のみ。DG-GEN/DG-MORは採用していない。
- U14bの同値と準同値の数学的中心部分は証明済み。受入条件の整合的shift・三角性・
  導来係数変更の図式は引き続き照合が必要である。

## 残る受入条件

- U14a：underived加群圏の再構成随伴・単位・余単位は構成済み。
  導来Hom・導来tensor・主Kの随伴・導来射集合同値も構成済み。
  導来射集合同値の全導来射自然性と導来随伴も構成済み。
  U13のenhancementへの制限・受入図式の最終照合が残る。
- U14b：明示したthick生成仮定からenhancement上の全Hom擬同型は証明済み。
  Hom像のPerf保存と主導来HomのPerfへの制限は構成済み。
  H⁰の本質的全射、主Perf同値、enhancement準同値も構成済み。
  受入条件の整合的shift・三角性・導来係数変更の図式が残る。
- U14c：導来圏全体の比較にはcompact生成性が必要。
  無限生成集合の直和はcompactとは限らず、thick生成だけから全導来圏の比較は出さない。
  DG-GEN/DG-MORの採用が必要になったら採用せず停止・報告する。
- U12dとの全導来射自然なtensor評価比較、評価成分のshift・cone同型と包含図式は構成済み。
  Perf比較に対するshift・三角性・導来係数変更の図式が残る。
