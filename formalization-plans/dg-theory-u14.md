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

## 残る受入条件

- U14a：enhancement／End(E)加群間の再構成随伴と、その単位・余単位。
- U14b：thick生成からPerf比較。全Homの擬同型とH⁰の本質的全射を別々に証明する。
- U14c：導来圏全体の比較にはcompact生成性が必要。
  無限生成集合の直和はcompactとは限らず、thick生成だけから全導来圏の比較は出さない。
  DG-GEN/DG-MORの採用が必要になったら採用せず停止・報告する。
- 既存導来tensorとの計算比較、shift・三角性・係数変更の図式。
