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

## 残る受入条件

- U14a：underived加群圏の再構成随伴・単位・余単位は構成済み。
  U13のenhancementへの制限と導来化・受入図式の最終照合が残る。
- U14b：thick生成からPerf比較。全Homの擬同型とH⁰の本質的全射を別々に証明する。
- U14c：導来圏全体の比較にはcompact生成性が必要。
  無限生成集合の直和はcompactとは限らず、thick生成だけから全導来圏の比較は出さない。
  DG-GEN/DG-MORの採用が必要になったら採用せず停止・報告する。
- 既存導来tensorとの計算比較、shift・三角性・係数変更の図式。
