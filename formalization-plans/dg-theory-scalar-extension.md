# dg 理論の係数変更（U12f・U15d）

正本は `dg-theory.md` §15 冒頭・§15.2 U12f・§15.5 U15d。
任意可換環、非有界 cochain 複体、微分 +1、ホモトピー −1、Mathlib
`EnrichedCategory` を維持する。係数環・Hom 加群の宇宙は `u`、対象宇宙は独立な `v`。
直和を使う箇所だけ添字の `Small.{u}` を要求する。

## 編集境界

- `Derived/KFlatBimodule*`、既存の bimodule 合成系、既存 `Quotient/`、`Perfect/`、
  `DifferentialGraded/README.md`、`Stage*.lean` は編集しない。
- ルートの import は自分の行だけ追加・部分 stage する。
- `dg-theory.md` への参照追加は両単位の完了時のみ。
- 新規 sorry・axiom・引用は追加しない。

## 作業順と受入状況

1. U12f underived：複体上の restriction/extension 随伴、同じ添字の直和、
   coequalizer、tensor 比較を先行する。dg 圏・dg 加群・相対 tensor、単位・結合・自然性へ進む。
2. U12f derived：quasiIso 保存の条件を underived の余極限保存と区別する。
   非 flat な係数変更も扱い、underived との一致に必要な置換条件を記載する。
3. U15d：固定した path 添字の比較、最終微分、単位・合成との整合性。

現時点では U12f・U15d の全受入を完了扱いしない。

## 実装中の API

`Tensor/ScalarExtensionColimits.lean` の namespace は
`SerrePositivity.DifferentialGraded.ScalarExtension`。
`extension`・`restriction` は各次数への Mathlib の係数変更であり、
`adjunction` は加群の随伴の単位・余単位を複体へ持ち上げる。
`coproductIso`・`coequalizerIso` は余極限保存から得る同型で、平坦性を要求しない。
`tensorIso`・`tensorIso_naturality` は既存の非有界 total tensor 比較を再利用する。
`identityIso`・`compositionIso` は係数変更を一回または二回施す比較。

`Tensor/ScalarExtensionCoherence.lean` では sphere・単位複体の比較と
tensor 比較の単位・結合整合性を証明する。

## 2026-10-17：U12f の基礎部分

`Tensor/ScalarExtension.lean` で `extensionMonoidal` を構成し、
Mathlib の `TransportEnrichment` により `DGBaseChange` を定義した。
`homObject_eq`・`identity_eq`・`composition_eq` は実際の Hom・単位・合成の式である。
`dgFunctor` は Hom 上の係数拡大から得られる dg 関手で、単位と合成を保存する。

検証：`lake build SerrePositivity.DifferentialGraded.Tensor.ScalarExtension` 成功
（1969 jobs、警告なし）。
`lake build SerrePositivity.DifferentialGraded.Checks.ScalarExtension` 成功
（1970 jobs）。後者は `ℤ → ZMod 2` による強モノイダル構造と dg 圏の型検査を含む。
同ファイルの主要14宣言の `#print axioms` はすべて
`propext`・`Classical.choice`・`Quot.sound` の標準3公理のみ。
コミット：`3368f633`。

これは U12f の部分受入である。複体上の随伴を dg 加群上の随伴と同一視しない。
dg 加群の係数変更・その随伴、相対 tensor の比較、導来比較、U15d の最終微分と
単位・合成比較は未完であり、次の部分単位で実装する。

## 2026-10-17：全次数 Hom 比較と加群の対象

`Tensor/ScalarExtensionHom.lean`：

- `homComparison` は評価射の係数拡大を tensor–Hom 転置して作る。
  Hom の係数変更が同型であるとは主張しない。
- `homComparison_apply` は全整数次数で `1 ⊗ f` と `1 ⊗ x` の評価を与える。
- `homComparison_identity`・`homComparison_composition` から
  `complexDGFunctor` を作る。後者は Koszul 符号を保持する。

`Tensor/ScalarExtensionModule.lean`：

- `tensorIso_braiding`・`oppositeDGFunctor` により係数変更と opposite を交換する。
- `rightModule`・`leftModule` は実際の Mathlib 豊穣関手であり、
  各値が複体の係数拡大になる。
- `rightModule_action` は純粋生成元上の全次数作用の比較。

検証：`lake build SerrePositivity.DifferentialGraded.Tensor.ScalarExtensionModule` 成功
（1978 jobs、警告なし）。
`lake build SerrePositivity.DifferentialGraded.Checks.ScalarExtensionModule` 成功
（1979 jobs）。後者は `ℤ → ZMod 2` による左右加群の型検査と、主要12宣言の
`#print axioms` を含む。すべて標準3公理のみ。新規 sorry・axiom・引用は0件。
ルートには `Tensor.ScalarExtensionModule` の import 行のみ追加し、`git add -p` で
その hunk のみ stage した。

### 残る受入条件（完了宣言しない）

1. dg 加群の **射** の係数変更と関手、restriction と extension の加群圏上の随伴。
   現在の `adjunction` は複体圏上のもの。
2. 相対 balanced tensor の二つの関係射を上記 coequalizer 比較で運び、比較同型を作る。
3. 非 flat な係数変更の導来関手と、underived 比較に必要な K-flat 置換条件。
   `Derived/ScalarExtension.lean` は未作成。`Derived/KFlatBimodule*` は未編集。
4. U15d の固定 path 添字の同型、最終微分、単位・合成の比較。
   `Quotient/ScalarExtension.lean` は未作成。既存 `Quotient/` は未編集。

正本 `dg-theory.md` への完了参照はまだ追加しない。


## 2026-10-17：加群の射と係数拡大関手

`Tensor/ScalarExtensionNaturality.lean` で全次数 Hom 比較の前合成・後合成自然性を証明した。
`Tensor/ScalarExtensionModuleMaps.lean` の `moduleExtensionMap` は全次数自然な加群射の
各成分を係数拡大して加群圏の実際の射に戻す。恒等・合成保存を証明した `moduleExtension`
と、各対象での係数拡大との `moduleExtensionEvaluationIso` を公開した。
この段階では `Small.{u} D` を加群圏の Hom end の構成に要求する。

`lake build SerrePositivity.DifferentialGraded.Checks.ScalarExtensionModule` 成功
（1986 jobs、警告なし）。`ℤ → ZMod 2` の加群圏間の関手を型検査し、今回追加の
主要7宣言の公理監査はすべて標準3公理のみ。新規 sorry・axiom・引用は0件。
ルートの自分の import 行を `ScalarExtensionModuleMaps` へ進め、部分 stage する。

残る受入条件の第1項のうち、右加群の射と係数拡大関手までを実装済みとする。
係数制限、加群圏上の随伴、相対 tensor 比較、導来版、U15d は引き続き未完。


## 2026-10-17：係数制限関手

前節の加群圏上の係数拡大関手は `9025b9af` にコミット済み。

`Tensor/ScalarRestrictionHom.lean` は複体上の随伴から restriction の lax monoidal
構造を導き、既存 `Cochain.map` を用いて全次数 Hom 比較を構成する。
単位・合成保存、tensor の純粋生成元上の公式を証明した。
`ScalarRestrictionCategory.lean` の `unitDGFunctor` はモノイダル随伴の単位から
元の dg 圏と係数変更後の dg 圏を接続する。
`ScalarRestrictionModule.lean` の左右加群の係数制限を、
`ScalarRestrictionModuleMaps.lean` で右加群圏上の `moduleRestriction` にした。
その全次数自然性と評価自然同型も証明済み。

`lake build SerrePositivity.DifferentialGraded.Checks.ScalarRestriction` 成功
（1991 jobs、警告なし）。非 flat な `ℤ → ZMod 2` の関手を型検査。
主要17宣言の公理監査はすべて標準3公理のみ。新規 sorry・axiom・引用は0件。
ルートの自分の import 行のみ `ScalarRestrictionModuleMaps` へ進める。

係数拡大・係数制限の両関手まで実装済み。両者の加群圏上の随伴の証明を進める。
相対 tensor 比較、導来版、U15d は未完のまま維持する。
ユーザーの追加指示により amend・rebase・reset は禁止。通常の追加コミットのみを使う。


## 2026-10-17：加群圏上の随伴

係数制限関手は `0d6266d4` にコミット済み。
`Tensor/ScalarExtensionAdjunction.lean` の `moduleAdjunction` は
`moduleExtension φ D ⊣ moduleRestriction φ D` を構成する。
`moduleUnitApp`・`moduleCounitApp` は複体随伴の単位・余単位を各対象に置いた
実際の全次数自然な dg 加群射であり、`moduleUnit`・`moduleCounit` の自然性と
左右の三角恒等式を証明した。元の dg 圏の Hom に flatness を課さず、
係数環 A' の A-flatness も仮定しない。`Small.{u} D` は Hom end のために要求する。

`lake build SerrePositivity.DifferentialGraded.Checks.ScalarExtensionAdjunction` 成功
（1992 jobs、警告なし）。`ℤ → ZMod 2` の加群随伴を型検査し、主要9宣言の
公理監査はすべて標準3公理のみ。新規 sorry・axiom・引用は0件。
ルートの自分の import 行のみ `ScalarExtensionAdjunction` へ進める。

### 次の作業と全体の未完条件

1. 相対 balanced tensor の係数変更：直和の添字を同じ対象・対象対に固定し、
   二つの関係射を tensor 比較で運ぶ。coequalizer 比較の同型と包含成分の公式、
   両変数自然性、単位・結合比較を証明する。左右加群を opposite で交換する API も照合する。
2. `Derived/ScalarExtension.lean`：projective/semifree 置換による非 flat な導来版と、
   underived との一致に必要な K-flat 条件。`Derived/KFlatBimodule*` は読んで使い、編集しない。
3. `Quotient/ScalarExtension.lean`：固定 path 添字の比較、最終微分、単位・合成整合性。
4. 各部分のビルド・主要宣言監査・記録・追加コミットを続け、全受入の確認後にのみ
   正本 `dg-theory.md` へ一行の参照を足す。

U12f 全体・U15d 全体はまだ完了ではない。ゴールを縮小せず、この順序で継続する。


## 2026-10-17：相対 balanced tensor の係数変更

加群随伴は `6e33fa78` にコミット済み。
`Tensor/ScalarExtensionActions.lean` で左右作用の係数変更との可換性を全整数次数で証明した。
右作用の Koszul 符号を保持し、係数環の flatness は使わない。
`ScalarExtensionPresentation.lean` の `generatorIso`・`relationIso` は同じ対象添字 D と
同じ対象対添字 D×D の直和を使う。`relationLeft_square`・`relationRight_square` は
二つの関係射を比較し、後者では tensor の associator 整合性を使う。

`ScalarExtensionBalanced.lean` の `balancedIso` は直和同型を含む parallelPair 図式の同型と
先行実装の coequalizer 保存同型を合成した、相対 tensor の実際の chain 同型である。
`balancedIso_ι` と `balancedIso_inv_ι` は各対象の包含上の順方向・逆方向の成分式。
`ScalarExtensionBalancedNaturality.lean` の `balancedIso_naturality` は、両変数の作用に
可換な chain map 族に対する自然性を同時に述べる。既存 `mapOfFamilies` の射を使う。

`lake build SerrePositivity.DifferentialGraded.Checks.ScalarExtensionBalanced` 成功
（2017 jobs、警告なし）。非 flat な `ℤ → ZMod 2` を型検査し、主要16宣言の公理監査は
すべて標準3公理のみ。新規 sorry・axiom・引用は0件。
ルートの自分の import 行のみ `ScalarExtensionBalancedNaturality` へ進める。

残る underived 検証は、実際の左右加群圏の射に対する tensor 比較の明示的入口、
一対象環での通常 tensor 比較、相対 tensor の単位・結合比較との整合性。
これらを済ませてから、指示された順序で導来版、U15d に進む。
全体のゴールは active のままとし、正本への完了参照はまだ追加しない。


## 2026-10-17：左加群圏の関手と一対象の通常 tensor

相対 tensor の表示と同型は `0852681b` にコミット済み。
`Tensor/ScalarExtensionLeftMaps.lean` で左 dg 加群の全次数自然な射を係数拡大し、
`leftModuleExtension` を実際の左加群圏の関手にした。
`balancedIso_module_naturality` は既存 `BalancedTensor.map` と右・左の係数拡大関手を
使う、実際の閉零加群圏の両変数自然性である。

`ScalarExtensionRing.lean` の `ringBalancedIso` は係数変更後の一対象 tensor を
値の通常 tensor に送る。唯一の対象の包含を恒等写像に送る式 `ι_ringBalancedIso` と、
元の一対象 tensor 比較・非有界 `cochainTensorBaseChangeIso` の可換図式
`ringComplexBaseChange_comparison` を証明した。

`lake build SerrePositivity.DifferentialGraded.Checks.ScalarExtensionRing` 成功
（2034 jobs、警告なし）。`ℤ → ZMod 2` の左加群関手を型検査し、主要6宣言の監査は
標準3公理のみ。新規 sorry・axiom・引用は0件。
ルートの自分の import 行のみ `ScalarExtensionRing` へ進める。

次は scalar-changed representable の評価単位と、複体パラメータを相対 tensor の外へ
出す associator の生成項公式を比較し、残る underived 整合性を検証する。
導来版・U15d は引き続き未完。amend・rebase・reset は使わない。


## 2026-10-17：評価単位とパラメータ結合比較

左加群圏・一対象 tensor の比較は `680e1125` にコミット済み。
`Tensor/ScalarExtensionCoendCoherence.lean` は、係数変更した左右 representable を
相対 tensor に入れた評価同型 `yonedaBaseChangeIso`・`leftYonedaBaseChangeIso` を構成する。
各対象の包含との合成が、係数変更後の加群の左作用・右作用そのものになる公式と、
元の Yoneda 評価を係数変更した射との可換図式を証明した。
ここで使う representable は明示的に scalar-changed representable である。

同ファイルの `tensorModuleBaseChangeIso` は複体パラメータ K を相対 tensor の外へ
出す比較を係数変更し、生成項上で三つの tensor 因子の associator と一致する公式
`ι_tensorModuleBaseChangeIso` を証明する。
`tensorModuleBaseChange_comparison` が元の `BalancedTensor.tensorModuleIso` との可換図式。
元の三重 tensor の係数変更の associator 整合性を使い、符号規約は既存 API のまま保つ。

`lake build SerrePositivity.DifferentialGraded.Checks.ScalarExtensionCoendCoherence` 成功
（2044 jobs、警告なし）。`ℤ → ZMod 2` と次数 −1 の sphere のパラメータを型検査した。
主要9宣言の監査はすべて標準3公理のみ。新規 sorry・axiom・引用は0件。
ルートの自分の import 行のみ `ScalarExtensionCoendCoherence` へ進める。

underived 側の dg 圏・左右加群・随伴・直和/coequalizer・相対 tensor・両変数自然性・
一対象通常 tensor・評価単位・パラメータ結合比較が揃った。これは U12f 全体の完了ではない。
次に導来版を実装し、擬同型保存条件と underived との一致条件を明示する。
その後 U15d に進む。正本への完了参照は全担当の受入後のみとする。


## 2026-10-17：非 flat な導来係数拡大と exactness の区別

評価単位・パラメータ結合比較は `af9a2301` にコミット済み。
`Derived/ScalarExtensionHomotopy.lean` は標準加群 cylinder の射影が係数変更後も
objectwise 擬同型であることを、複体の明示的な収縮の保存から証明する。
その射影だけを導来圏で反転し、全 dg 自然な境界を同一視する
`moduleExtensionHomotopyToDerived` を構成した。任意の擬同型の underived 保存を
ここで仮定していない。

`Derived/ScalarExtension.lean` の `derivedExtension` は標準 semifree 射影解像度から
構成した実際の主導来加群圏間の関手であり、A′ の A-flatness と local Hom-flatness は不要。
任意の証明付き射影解像度による計算、解像度選択の自然同型と self/trans 整合性、
underived への比較射を公開した。比較が同型となる条件は、増大射の係数変更後の
objectwise 擬同型性として明示している。

`Derived/ScalarExtensionExact.lean` は restriction の擬同型保存を無条件で証明し、
`derivedRestriction` を構成する。extension についてはホモロジー保存を条件にした結果と、
環準同型の flatness による十分条件を別に証明した。flat な場合の underived 比較同型も得る。

検証：`lake build SerrePositivity.DifferentialGraded.Checks.DerivedScalarExtension` 成功
（2739 jobs、警告なし）。非 flat な `ℤ → ZMod 2` の主導来関手を型検査し、主要19宣言は
すべて標準3公理のみ。新規 sorry・axiom・引用は0件。ルートは自分の import hunk のみ部分 stage。

残り：非 flat な tensor の導来比較と K-flat 置換条件の具体化・自然性、U15d の固定 path
比較と最終微分・単位・合成整合性。U12f/U15d 全体は未完として維持する。
