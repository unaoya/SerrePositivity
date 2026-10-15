# 共有ホモトピー論の契約（H0）

固定環境：Lean `v4.35.0-rc4`、Mathlib
`e6bbacd0e1b7307ff6e17da09cd2455f60804fa6`。
設計は `formalization-plans/k-theory.md` §123・§124。

## 基底の型と宇宙

- 圏は `C : Type u`、`Category.{v} C`。異なる圏の対象・射の宇宙は独立に保つ。
- 射のクラスはMathlibの `CategoryWithCofibrations`、`CategoryWithFibrations`、
  `CategoryWithWeakEquivalences` と `MorphismProperty C`。
- モデル構造は `HomotopicalAlgebra.ModelCategory C`。代替型を作らない。
- 随伴は `CategoryTheory.Adjunction`。Quillen条件は通常の関手上のPropとして追加する。
- ホモトピー圏は指定したWのMathlib局所化。導来関手・導来随伴は既存の
  `Functor.IsLeftDerivedFunctor` / `IsRightDerivedFunctor`、`Adjunction.derived`へ接続する。
- 図式の対象・射の宇宙 `w_obj`, `w_hom` と局所化先の宇宙は使用箇所で明示する。
  `ModelCategory`だけから任意小極限・余極限・関手的置換を取り出さない。
- モデル構造を複数選ぶ場合は局所instanceか射クラス選択用の型別名を使う。
  対象の定義を複製しない。Underの構造は基底の三クラスを忘却で引き戻す標準構造。

## 担当と依存

この系列はG0〜G8の共有一般論を所有する。M5側は任意可換環AのCh(A)、
dg圏・加群・局所化導来圏・tensor・商・Moritaと具体的検証を所有する。
Ch(A)固有の型・符号・smallnessの証拠をこのディレクトリへ埋め込まない。
M5の射影モデル比較D4mへQuillen・転送・monoidal一般論を供給する。
M5の局所化経路は共有転送の完成を待たず進められる。

`Foundations.lean`はこの系列専用の入口。共有ルート`SerrePositivity.lean`には追加しない。
具体的SSet・スペクトル・Ch(A)・論文の圏を一般論からimportしない。
一般論はsorry・引用axiomなし。当てはめの引用は別の`Inputs/`と引用台帳に置く。
既存Spectraのnamespace・宣言名・`StageTwo`の入口を保持する。
既存可換環論・CLMST・M5担当ファイルは変更しない。

## H0〜H2の受入と検証

H1は通常の随伴についてcof/trivial cof保存とfib/trivial fib保存の同値、
恒等関手・合成を扱う。H2はUnderの三クラス、二つの分解・lifting、
有限極限・余極限とMathlib ModelCategoryへの接続を扱う。
各単位で対象ビルド、公開APIの利用例、主要宣言を含むモジュール全宣言の公理監査を行う。
最後に既存 `scripts/check_spectra_stage2.lean` とスペクトル公理監査も再実行する。

## 完了したAPI（2026-10-14）

専用入口は `SerrePositivity.HomotopicalAlgebra.Foundations`。
H0〜H2は実装・ビルド・公理監査・既存API互換検証まで完了した。

| 単位 | 公開API | M5側からの利用 |
| --- | --- | --- |
| H1 | `SerrePositivity.Quillen.IsLeftQuillen`, `IsRightQuillen` | cof/trivial cof、fib/trivial fibの保存を既存MorphismProperty上で供給。クラス自体は保存性のみを表し、随伴の存在は通常のAdjunctionで別に渡す |
| H1 | `preserves_left_iff_preserves_right` | 任意の二つの弱分解系について、随伴による左右保存の同値。モデル構造・関手的分解は不要 |
| H1 | `isLeftQuillen_iff_isRightQuillen`, `isRightQuillen_of_isLeftQuillen`, `isLeftQuillen_of_isRightQuillen` | モデル圏間の通常随伴に適用。逆向き推論は明示的なlemmaで行い、循環するinstanceを登録しない |
| H1 | `isLeftQuillen_id/comp`, `isRightQuillen_id/comp`、四つの`map_*` lemma | 恒等・合成はinstance、個別の射の保存は明示的lemma。すべての弱同値の保存は主張しない |
| H2 | `HomotopicalAlgebra.ModelCategory.under`、`cofibrations_under_iff`, `fibrations_under_iff`, `weakEquivalences_under_iff` | 任意SのUnderへ標準構造を継承。Sのcofibrancy/fibrancyは不要。三クラスは基礎射`f.right`で判定 |
| H2 | `CategoryTheory.MorphismProperty.MapFactorizationData.under`, `HasFactorization.under` | 指定した基礎射の分解・一般の二クラスの分解をUnderへ移す |
| H2 | `CategoryTheory.CommSq.HasLift.under`, `HasLiftingProperty.under` | 基礎のsquareのlift・lifting propertyをUnderへ移す |

Underの有限極限は既存StructuredArrowの構成を明示的に特殊化した。
有限余極限は既存MathlibのUnder instanceを使用する。
ModelCategoryの二つの分解・lifting・retract・two-out-of-threeをすべて接続済み。

検証コマンド：

```sh
lake build SerrePositivity.HomotopicalAlgebra.Foundations SerrePositivity.Spectra.StageTwo SerrePositivity.Spectra.Foundations
lake env lean scripts/check_homotopical_foundations.lean
lake env lean scripts/audit_homotopical_foundations.lean
lake env lean scripts/check_spectra_stage2.lean
lake env lean scripts/audit_spectra.lean
```

すべて成功。新規一般論は4モジュール76宣言（内部補助宣言も含む）、
既存スペクトル・共有基盤は261モジュール2612宣言が標準公理
`propext`, `Classical.choice`, `Quot.sound`のみ。
新規監査は必須の4モジュールすべてが監査対象に含まれたことも検証する。
利用例は独立した宇宙、Quillen左右保存、Underの三クラスとtrivialクラス、
両分解・両lifting、有限極限余極限、二重UnderとStageTwoの併用を確認する。

コミット：H0 `b46de69`、H1 `d554602`、H2 `e382feb`。
この時点の次段階はH3（生成条件・転送認識）とH4（既存導来随伴への接続）だった。
以下にその後のH3・H4の完了記録を示す。

## H3・H4の完了とM5への引継ぎ

H3とH4を実装・検証済み。専用入口は同じ`Foundations`で、共有ルートimportは変更しない。
すべての型は既存MathlibのModelCategory・MorphismProperty・Adjunction・導来関手を使用する。

| 単位 | 公開API（名前空間は`SerrePositivity.ModelGeneration`又は`SerrePositivity.Quillen`） | 契約 |
| --- | --- | --- |
| H3 | `CofibrantlyGenerated.{w} I J`, `generatedWfs`, `cofibrations_eq_generated`, `trivialCofibrations_eq_generated` | I,Jのsmall-object仮定と右クラスの生成等式。wはsmallnessとcell構成の補助宇宙。Mathlibのcardinal仮定を再定義しない |
| H3 | `hasFunctorialFactorization_cofibration_trivialFibration`, `hasFunctorialFactorization_trivialCofibration_fibration` | 生成性から両方の関手的分解が得られる。普通のModelCategoryだけでこれを主張しない |
| H3 | `modelCategoryOfRecognition`, `generatedLeft_le_of_cells_le` | 二つの小対象構成、2-out-of-3、生成クラスの同定、acyclicityからモデル圏を構成。cellから左クラスへの拡張ではWのretract閉性を使用 |
| H3 | `strictMap_rlp`, `rightTransfer I J adj hacyclic` | 通常随伴L⊣R、源の生成モデル構造、値域の有限極限余極限、L(I),L(J)のsmall-object仮定、L(J)-cellのRによるacyclicity。FibとWはRのinverse image |
| H3 | `rightTransfer_cofibrantlyGenerated`, `rightTransfer_isLeftQuillen`, `rightTransfer_isRightQuillen` | 像の生成射による生成性、通常随伴のQuillen性。構成したModelCategoryを局所instanceとして選んで使う |
| H4 | `map_weakEquivalence_of_cofibrant`, `map_weakEquivalence_of_fibrant` | Ken Brownの既存分解から良い対象間の弱同値保存。全対象の弱同値保存とは区別する |
| H4 | `cofibrant_derives`, `fibrant_derives`, pointwise derived existence instance | 既存のcof/fib derivability structureから導来関手の存在を証明。MathlibのtotalLeftDerived/totalRightDerivedを利用できる |
| H4 | `leftComparison_isIso`, `rightComparison_isIso`, `leftDerived_postcomp`, `rightDerived_postcomp` | 良い対象上で比較射が同型。任意の後合成が導来関手になることを証明し、absolute derivedの仮定を別入力にしない |
| H4 | `derivedAdjunction`, `derivedAdjunction_unit_fac`, `derivedAdjunction_counit_fac`, `derivedAdjunction_homEquiv` | 既存Adjunction.derivedへの接続。unit/counitの計算、元のmateとの一致、三角恒等式 |
| H4 | `leftChoiceIso`, `rightChoiceIso`, `derivedAdjunction_unit_choice`, `derivedAdjunction_counit_choice` | 導来関手の選択間のcanonical自然同型と、unit/counitを運ぶ自然変換の等式。特定の置換関手に依存しない |
| H4 | `derived_isEquivalence_iff` | 導来左関手が圏同値であることと、cofibrant上の導来unit・fibrant上の導来counitの可逆性の必要十分条件 |
| H4 | `derived_unit_isIso_of_weakEquivalence_mate`, `derived_counit_isIso_of_weakEquivalence_mate`, `derived_isEquivalence_of_mate_weakEquivalences` | 指定した置換の射とmateが弱同値なら比較は可逆。通常のcof→fibの弱同値mate判定から導来同値を得る十分条件。弱同値mate条件の必要性まで同じ定理と呼ばない |

M5はfree/forgetの随伴、生成射、像のsmallnessとcell acyclicityを供給すればH3を適用できる。
H4にはQuillen保存条件と局所化を渡せばよく、独自の導来随伴型は不要。
Ch(A)の具体的smallness・monoid axiom・dg加群の作用の検証はM5の担当のまま。
抽象monoidal model・monoid axiom・多対象転送への接続は次のH5/G5が担当する。
一般の右転送定理だけからdg加群転送の具体的仮定が満たされるとは主張しない。

最終検証では上記H0〜H2のコマンドに加えて、以下を実行した。

```sh
lake env lean scripts/check_homotopical_transfer.lean
lake env lean scripts/check_homotopical_derived.lean
```

すべて成功・新規ソース警告なし。集約ビルドは2244ジョブ。
共有ホモトピー論の監査は11モジュール153宣言、既存スペクトル監査は261モジュール2612宣言。
内部補助宣言を含む共有一般論は標準公理のみでsorry・引用axiom依存なし。
生成・転送の利用例は未装備の値域へモデル構造を作り、その同じ構造上で両分解とQuillen性を利用する。
導来側は実際のMathlib total derived functor、任意の選択、unit/counit、三角恒等式、
自然な選択変更、同値判定を確認する。H0〜H2・StageTwoの既存検証も再実行済み。

コミット：H3 `7d742b4`、H4前半 `8bdb3a8`、H4後半 `8825133`。
次はH5：Quillen bifunctor、pushout-product/pullback-hom、unit、豊穣tensor/cotensorの共有API。
M5の具体的な複体の証明を取り込まず、任意Vの一般論として進める。

## monoidal・豊穣の共有基盤H5の完了（2026-10-15）

### 受入条件と実装

H5（§123.6）の四つの受入条件を実装・検証した。入口は
`SerrePositivity.HomotopicalAlgebra.Foundations`。Mathlib固定版は変更していない。

| 受入条件 | 成果物・証拠 |
| --- | --- |
| pushout-product / pullback-hom の同値 | `Monoidal/QuillenBifunctor.lean`の`isQuillenBifunctor_iff_pullbackHom`。Mathlibの通常のparametrized adjunctionと任意のpushout/pullback square上で証明。両方のtrivial入力を扱い、flipとcofibrant対象固定によるQuillen性も証明 |
| unit公理を独立した条件にする | `Monoidal/ModelCategory.lean`の`UnitReplacementAxiom`, `HasUnitAxiom`, `MonoidalModelCategory`。指定したcofibrant単位置換と左右tensorの弱同値を記録。cofibrant unitならidentity置換で成立。閉圏でのpullback-hom判定にもunit条件を明示 |
| 任意Vのtensor/cotensor表現性と両立 | `CategoryTheory/Enriched/TensorCotensor.lean`。既存`EnrichedOrdinaryCategory`・`eHomFunctor`・二つのparametrized adjunctionを束ね、三つのHom同値、各三変数の自然性、相互の一致、評価・余評価・三角恒等式を証明 |
| 一般論にSSet/Chを埋め込まない | `HomotopicalAlgebra/Enriched/TensorCotensor.lean`の二つのmodel criterionと四つの固定対象Quillen補題。V,Cは独立した宇宙の任意モデル圏。具体的圏・M5・Spectraをimportしない |

普通のHom集合による表現性とV値のHom対象の表現性は別契約にした。
`CategoryTheory/Enriched/EnrichedRepresentability.lean`は閉なVにおける
二変数自然同型、Vパラメータの自然性、単位からの点での随伴との一致を入力とする。
`homObjectComparison_points`はこのHom対象の比較が選んだtensor/cotensor随伴と一致することを証明する。
普通のHom同値だけから、単位がgeneratorでない一般VでHom対象の同型を推論しない。

### M5への契約と残る範囲

M5はCh(A)の閉monoidal構造、具体的tensor/cotensorと既存enrichmentの表現性を供給する。
`IsQuillenBifunctor`の証拠を供給すれば、cotensorとmappingのpullback-hom条件と、
cofibrant対象を固定した左右Quillen性をこの共有層から得られる。
単位がcofibrantなら`unitAxiom_of_cofibrant_unit`を使える。
任意のdg圏にSSet豊穣構造を要求する条件は追加していない。

H5完了はG5/G6全体の完了を意味しない。monoid axiom、多対象加群転送、
基点付きsmashへのモデル構造の接続、具体的SSet/スペクトルのSM7は後続の証明対象。
次の独立した対象構成単位はH6（一般C,KのSym(K)加群と旧特殊化比較）。
G4局所化の二案は未選択で、M3の安定モデル構造も未完成のままである。

### 検証とコミット

共有入口、`Spectra.StageTwo`、`Spectra.Foundations`のビルドが成功。
以下の利用例・監査をすべて成功確認した。

- `scripts/check_homotopical_monoidal.lean`：任意squareでの双対判定、flip、canonical pushout-product/pullback-hom、別unit条件。
- `scripts/check_enriched_tensor_cotensor.lean`：Hom同値の一致・自然性・三角恒等式、Hom対象比較の点での一致、二つのmodel criterion、四つの固定対象Quillen性。
- 既存`check_homotopical_foundations`, `check_homotopical_transfer`, `check_homotopical_derived`, `check_spectra_stage2`を再実行。
- `audit_homotopical_foundations`：16モジュール276宣言。任意Vの新規2モジュールも全宣言を監査対象に含む。
- `audit_spectra`：261モジュール2612宣言。両監査とも標準公理のみでsorry・引用依存なし。

コミット：H5a `3706d4a`、H5b `00604a2`、H5c `547fcb6`。
共有ルートimport、M5、可換環論・CLMSTの担当ファイルは変更していない。

## G5の部分実装：monoid公理と内部加群転送

`Monoidal.MonoidAxiom`の`HasMonoidAxiom.{w}`は独立した追加条件。
`tensorRightImages`は任意対象のright tensorのMathlib mapの和（射の同型を許す）で、braidingによりleft tensorも含む。
`relativeCells.{w}`はcoproduct、pushout、transfinite compositionの順に閉じる。
retract acyclicityは既存の弱同値retract閉性から証明する。

`Transfer.CellMap`はcolimit保存関手でのcell移送を証明する。
`Monoidal.ModuleTransfer`の`moduleModelCategory M I J`は、braided closedなCの生成モデル構造、
monoid公理、wサイズ余極限、free(I)/free(J)のsmall-object仮定からMod C Mのモデル構造を作る。
Mのcofibrancyやcommutativityは不要。free-cell acyclicityは別入力にせずmonoid公理から証明。
W/Fibはforgetで検出され、free/forgetはQuillen。smallnessはmonoid公理から自動推論しない。

検証は`check_monoid_axiom`, `check_module_model_transfer`と既存の全共有利用例。
共有監査は19モジュール308宣言。標準公理のみ、sorry・引用依存なし。
コミットは`63ec369`, `7db1a9d`。多対象加群・具体的SM7・レベルモデル構造は後続。

## 多対象加群の共有転送（§141）

Transfer/EvaluationFamilyは任意Dと各対象iのL_i⊣R_iからobjectwise W/Fibを検出するモデル構造を構成する。
入力は全free像I/Jのsmall-object条件とJ-cell acyclicity。全free像のrlp、生成性、Quillen関手、
両関手的分解も提供する。Dを通常の関手圏に同一視する必要はない。

Monoidal/ManyObjectTransferはL_i⋙R_j≅tensorLeft(H_ij)、評価の余極限保存とmonoid axiomから
J-cell acyclicityを証明する。任意のH_ijを許し、cofibrancyを仮定しない。
modelCategoryOfTensorFormulaへ具体的small-object条件を渡すとモデルを構成できる。
M5は実際のdg加群・free/evaluation公式・保存性・Ch(A)のモデル入力を所有する。
専用検証check_many_object_transfer.leanは構成・三クラス・生成性・Quillen関手・分解と31宣言の監査を含む。
コミット0e2c2c5・d39af6c。具体的dgモデルの存在をこの一般転送から自動的に主張しない。

## 評価族のsmallnessとpresentabilityからの転送（§142）

Transfer/EvaluationSmallnessはSmall.{w}の添字族、LocallySmall.{w}のDと評価の余極限保存の下で、
source生成射始域の共通regular κ-presentabilityから全free像のSOAを構成する。
スペクトルLevelSmallnessも同じ一般補題を使い、旧APIを保持する。

Monoidal/ManyObjectPresentabilityのmodelCategoryOfPresentableGeneratorsは、κの証拠、
free/evaluationのtensor公式とmonoid axiomからモデルを構成し、image SOAやcell acyclicityを追加仮定にしない。
具体的dg加群の入力はM5が所有する。専用check_many_object_presentability.leanはそれらの追加仮定を
与えずに三クラス・生成性・Quillen性・分解を検証し、新規12宣言を監査する。
コミットac36b45・ea3ed40。

## 基点付きモデルとsmash単位（§143）

Pointed/Basicは既存Underモデル上のPointedObjectを使用する。
cofibrancyは基点射のcofibration性と同値で、forget/adjoinはQuillen随伴。
cofibrantな基礎圏単位の自由基点追加が、cofibrantな既存smash単位を与える。
その恒等置換からHasUnitAxiomを構成済み。pushout-product互換性は次の証明対象。
check_pointed_model.leanが一般Cの利用例・10宣言の公理監査を含む。コミット844a563。

## 既存smashのmodel互換性（§144）

Spectra/Pointed/SmashPushoutProductはsmash pushout-productが直積側のpushoutであることを普遍性から証明する。
Pointed/SmashModelは基礎圏Cのcartesian pushout-product条件を既存smashへ移す。
任意のPushoutObjObjの選択を扱い、cofibration/trivial cofibrationのpushout閉性を使う。
smash_hasQuillenPullbackHomは既存内部HomのSM7。
cofibrantな基礎圏単位を追加するとsmash_monoidalModelを構成する。
具体的SSetモデル入力やスペクトル側SM7はこの一般定理とは別の接続作業である。
check_pointed_modelは比較・保存条件・monoidalモデル・SM7と63宣言の監査を含む。
コミット0eaec83・6c48f0f。

## Smith認識に向けたR0：可換squareのsolution-set（2026-10-15）

`Smith/SolutionSet.lean`を共有入口から公開した。入力は`Arrow C`と候補射クラス`W`の
充満部分圏のaccessibility、および包含関手のaccessibility。
`C`にモデル構造、`W`にsmallness・2-out-of-3・retract閉性を仮定しない。
Mathlibの`SolutionSetCondition`から各源射の小さい代表族を選択する。

| API（namespace `SerrePositivity.Smith`） | 内容 |
| --- | --- |
| `arrowProperty`, `arrowInclusion`, `solutionSetCondition` | 既存射圏の充満部分圏と、その包含のMathlib solution-set条件 |
| `solutionIndex`, `solutionArrow`, `solutionSquare` | `Type w`で添字づけた候補射と、源射から候補への実際の可換square |
| `solutionSquare_factor`, `solutionSquare_factor_components` | 任意のsquareの射圏での分解と、左右成分の合成等式 |
| `solutionTargets`, `solutionTargets_isSmall`, `solutionTargets_le`, `solutionTargets_factor` | 任意の`w`-smallな射族に対する標的射の小さい合併、Wへの所属、分解の保持 |
| `solutionTargetsForClass`と対応するsmallness・所属・factor補題 | `I.IsSmall.{w}`から全Iに共通な小さい標的射クラスを得る入口 |

源射族の添字宇宙`t`と小対象の宇宙`w`は区別し、`Small.{w} ι`を明示する。
`solutionTargets`はまだ`cof(I) ∩ W`の生成射ではなく、W内のsolution targetsである。
R1で小さい族の共通cardinalとSOA、R2でこれらの標的を`cof(I) ∩ W`へ改良し、
R3でSmith認識を完成させる。今回R0だけからモデル構造・局所化存在は主張しない。

## Smith R1：共通基数と小対象論法（2026-10-15）

`Smith/Smallness.lean`は、小さい可呈示対象族に共通の正則可呈示基数を構成する。
`exists_common_arrow_presentability`は生成射の始域・終域を同じ基数で扱い、
`hasSmallObjectArgument`は局所可呈示な圏の小さい射クラスからMathlibの
`HasSmallObjectArgument`を証明する。モデル構造は仮定せず、R0の
`solutionTargetsForClass`にも適用できる。宇宙`w`の小ささと余極限をそろえ、
SOAから小ささを得る既存APIとの循環を避けるため、後者はinstance登録しない。
検証は`scripts/check_smith_smallness.lean`と共有入口の公理監査で行う。

## Smith R2：生成自明cofibration候補の構成（2026-10-15）

`Smith/GeneratingTrivialCofibrations.lean`の`refineSquare`は、生成射`i`から
弱同値`f`へのsquareをpushoutとI分解によって改良する。中間射は`I.rlp.llp ∩ W`
に属し、もとのsquareへの分解を保つ。R0の小さいsolution族すべてに適用して
`generatingTrivialCofibrations`を構成し、小ささ・共通部分への包含・全squareの
分解を証明した。入力は`I.rlp ≤ W`と2-out-of-3、IのSOA、pushout、R0の
accessibility条件であり、Jやモデル構造を入力に要求しない。
`scripts/check_smith_generators.lean`は局所可呈示性からIと構成済みJのSOAを
導く利用例と、全40宣言の標準公理監査を含む。R3の閉性・認識は別の受入項目。

## Smith R3の代数的な認識部分（途中）

`Smith/Recognition.lean`はsquareの分解から`I.rlp = J.rlp ∩ W`を証明する。
さらに`J.rlp.llp ≤ W`の下でretractを用いて`J.rlp.llp = I.rlp.llp ∩ W`を導き、
`modelCategoryOfSquareFactor`で呼出側のMathlib三クラス上にモデル構造を構成する。
生成性と両関手的分解への接続も利用例で検証する。

この段階では有限極限とacyclicityを明示した条件付きAPIであり、R3の完了ではない。
`generatedLeft_le_of_closure`はcoproduct・pushout・超限合成閉性からacyclicityを導くが、
最終Smith定理ではcoproduct閉性を追加仮定にせず導出する必要がある。
局所可呈示性から必要な有限極限を導く証明も残る。
検証は`scripts/check_smith_recognition.lean`。

## Smith R3の完備性ゲート（2026-10-15）

`Smith/Completeness.lean`で局所可呈示性から`HasLimitsOfSize.{w,w} C`を証明した。
小さい稠密部分圏の包含に対する制限Yonedaとその左Kan拡張の随伴を用い、
前層圏の反射部分圏として完備性を移す。`ShrinkHoms`と`SmallModel`を使うため、
対象・射・可呈示性の宇宙を同一視しない。有限極限を追加仮定にする必要はなくなった。
`scripts/check_smith_completeness.lean`で独立した宇宙の一般圏・有限極限を検証する。
認識の利用例も有限極限を局所可呈示性から導く。上記の残項目のうち完備性は解消し、
coproduct閉性の導出と最終Smith定理の統合・監査が残る。

## Smith R3のcoproduct閉性ゲート（2026-10-15）

`Smith/CoproductClosure.lean`は、coproductのある一般圏で、射クラスPのpushoutと
超限合成閉性から`P.IsStableUnderCoproducts.{w}`を導く。添字を整列し、summandを
一つずつ始域から終域へ置き換える。後続段階は一つの射のpushoutであり、
各成分のeventual constancyから極限段階の連続性を示す。空の添字も含む。
モデル構造・accessibility・retract閉性・coproduct閉性を入力に要求しない。
`scripts/check_smith_coproduct_closure.lean`は一般族、空族、Mathlib閉性クラス、
Smithのacyclicityへの接続を検証する。これでR3に残るのは最終定理の統合・監査。

## Smith R0〜R3：最終認識定理（2026-10-15）

最終入口は`Smith/Existence.lean`の`modelCategoryOfSmith`。
局所可呈示なC、小さいI、accessibleかつaccessibly embeddedな候補W、
Wの2-out-of-3・retract閉性、`I.rlp ≤ W`、`I.rlp.llp ∩ W`のpushout・超限合成閉性
から、指定した三クラス上にMathlibのModelCategoryを構成する。
cofibrationは`I.rlp.llp`、弱同値はW、fibrationは`(I.rlp.llp ∩ W).rlp`。
`Arrow C`のaccessibilityも局所可呈示性から既存Comma一般論で導く。

`smithGenerators`でJを構成し、小ささ、square分解、`J.rlp.llp = I.rlp.llp ∩ W`、
`I.rlp = J.rlp ∩ W`を証明する。`cofibrantlyGeneratedOfSmith`は構成したモデル上の
生成性を与え、既存Generated APIから両関手的分解を得る。
J・SOA・acyclicity・coproduct閉性・有限極限/余極限を追加仮定に要求しない。
`scripts/check_smith_existence.lean`は三クラスを選ぶところからモデル構造・生成性・
両分解・共通基数・square分解まで通す利用例と、全宣言の公理監査を含む。
R系列の終了範囲はSmith認識。局所化存在やスペクトルの安定化は後続系列で扱う。

## A0の入口：指定した分解データからの移送（途中、2026-10-15）

`Smith/AccessibleFactorization.lean`は、指定したFunctorialFactorizationDataのZが
κ-accessibleであるという明示的な仮定から、左右のArrow値の因子と始対象・終対象に
沿った制限のκ-accessibilityを導く。Arrow値の関手のaccessibilityは両端点で検出する。
`initialComparison`・`terminalComparison`は自然変換であり、対応するモデル分解データ
を使えば制限はcofibrant/fibrant置換になり、比較射は自明fibration/cofibrationとなる。
既存ModelReplacementの置換は、そこで選ばれたデータの制限と定義的に一致する。

これは条件付き移送の入口であり、A0の完成ではない。局所可呈示性と小さい生成族から
Z自体のaccessibilityを証明し、二つのモデル分解とQ/Rに共通の基数を得る作業が残る。
A1の元モデル弱同値のaccessibilityも未着手。関手的というだけではaccessibleと仮定しない。
検証は`scripts/check_accessible_factorization_transport.lean`（全41宣言・標準公理のみ）。

`Smith/AccessibleColimits.lean`は、同じκでaccessibleな関手の図式について、
pointwise colimitと通常の選択されたcolimitがκ-accessibleであることを証明する。
関手圏値の関手のaccessibilityをevaluationで検出し、colimが左随伴であることを使う。
`scripts/check_accessible_colimits.lean`で一般図式・pushout・超限添字を検証し、
添字と可到達性の基数の宇宙を同一視しない。全6宣言は標準公理のみ。
この補題だけでは、セル付加の各段階や超限帰納中の全関手のaccessibilityを
証明したことにはならない。A0の小対象論法への適用は引き続き必要である。

`Smith/AccessibleIteration.lean`はMathlibの`SuccStruct.ofNatTrans`による実際の
反復を扱う。後続関手Tがκ-accessibleなら、各段階と反復全体も同じκでaccessible。
最小段階・後続段階・極限段階を分けて証明し、極限段階では上のcolimit保存を使う。
`scripts/check_accessible_iteration.lean`で一般反復・恒等関手の反復・一般連続図式を
検証する。全6宣言は標準公理のみ。小対象論法のセル付加関手をTとして使うには、
そのaccessibilityを小さい生成射族の可呈示性から証明する必要が残る。

## A0：セルを添字づけるsquareとcoproduct（途中、2026-10-15）

`Smith/DependentCopower.lean`は、集合族Pに対し`⨿ (i,x∈Pᵢ), Aᵢ`を取る関手を
Hom集合族を取る関手の左随伴として構成する。したがって各正則κでaccessibleとなる。
`Smith/AccessibleSquares.lean`は、生成射aᵢの両端点のκ-可呈示性から、可換squareの
集合族を取る関手のκ-accessibilityを導く。squareの添字をMathlibの
`SmallObject.FunctorObjIndex`と同一視するequivalenceと、対応するcoproduct関手への
自然同型を構成し、実際のsquare添字によるcoproductのaccessibilityを証明する。

`scripts/check_accessible_squares.lean`は局所可呈示性から共通基数を選び、始域・終域の
両方のcoproduct関手がaccessibleになるところまで検証する。両モジュール全44宣言は
標準公理のみ。この核APIでは射の宇宙をwにそろえており、一般の宇宙への移送、
pushoutによるセル付加段階、小対象論法全体への接続、A1は残作業として区別する。

`check_smith_solution_set`はモデル構造のない抽象圏で、独立した宇宙、CommSqの左右成分、
小さい射族/射クラス全体の分解、空の射族、General/StageTwoとの併用を検証する。
同スクリプトはこのモジュールの全宣言を標準公理のみで監査する。
共有全体の`audit_homotopical_foundations`でもR0を必須モジュールとして監査する。

## A0：実際のセル付加関手（途中、2026-10-15）

`Smith/AccessibleCellAttachment.lean`は、square添字のcoproductとArrowの始域射影を
関手圏内でpushoutし、Mathlibの`SmallObject.functor`そのものがκ-accessibleで
あることを証明する。入力は生成射の両端点のκ-可呈示性であり、セル付加関手の
accessibilityは仮定しない。`scripts/check_accessible_cell_attachment.lean`は
局所可呈示性から共通κを得て適用し、全宣言の公理も監査する。
小さい生成射クラスへの宇宙の一般化と超限反復の統合、A1は引き続き残る。

セル添字の宇宙は生成射の宇宙と独立にでき、`Small.{w} ι`から必要な大きい添字の
coproductを導出する。生成射クラスの`toSet`が大きい型に入る場合にも対応する。
`check_accessible_squares`と`check_accessible_cell_attachment`はこの独立した宇宙で検証する。

## A0：実際の小対象因子分解（途中、2026-10-15）

`Smith/AccessibleSmallObject.lean`はMathlibのセル付加、超限反復、始域射影を
統合する。生成射の両端点がκ-可呈示なら、SOAに適した独立の基数μで構成した
`SmallObject.functorialFactorizationData I μ`のZと左右両因子がκ-accessibleになる。
局所可呈示性とIの小ささだけから、そのようなκと因子分解データの存在も導く。
`scripts/check_accessible_small_object.lean`は反復・accessibilityの基数を独立に検証し、
局所可呈示性からの利用例と全宣言の公理監査を含む。ここでは射の宇宙はwであり、
一般の局所w-小さい圏への移送、両生成クラスとQ/Rの同一基数での統合、A1は残る。

## A0：一般の宇宙と二つのモデル分解・Q/R（2026-10-15）

`Smith/AccessibleHomTransport.lean`は`ShrinkHoms`上の生成射と持ち上げクラスの
対応を証明し、構成した分解を元の圏と元の生成射クラスに戻す。
`Smith/AccessibleGeneratedPair.lean`は局所可呈示性と二つの小さい生成クラスから
共通の正則κと、両方のaccessibleな生成因子分解を構成する。対象・射・小対象論法の
三つの宇宙は独立である。

`Smith/AccessibleModelFactorizations.lean`の
`exists_accessible_model_factorizations`はMathlibのモデル圏、局所可呈示性、既存の
`CofibrantlyGenerated I J`だけを入力とする。指定した両モデル分解のZ、左右四因子、
それらから制限して得るQ/Rが同じκでaccessibleとなる。比較写像が実際に
trivial fibration/trivial cofibrationであることと、Q/Rの対象のcofibrancy/fibrancyを
公開する。`atLarger`で同じ分解を任意の大きい正則基数へ移せる。
任意に選んだ関手的分解へaccessibilityを推論するものではない。
`scripts/check_accessible_model_factorizations.lean`は最終入力だけからこれらを検証し、
三モジュールの全宣言を公理監査する。A1の弱同値部分圏のaccessibilityは別の残項目。

## A1：元の弱同値のfiltered colimitと包含（途中、2026-10-15）

`Smith/AccessibleLiftingClosure.lean`は、生成射の両端点のκ-可呈示性から、射圏に
おけるI.rlpのκ-filtered colimit閉性を証明する。任意のsquareを可呈示性で一段へ
持ち上げ、その段でのliftをcolimitへ合成する。
`Smith/WeakEquivalenceFilteredColimits.lean`は、第二モデル分解の右因子が
trivial fibrationであることと元の射が弱同値であることの同値を証明する。
これを用い、combinatorialモデルの元のWのfull subcategoryが十分大きいκで
κ-filtered colimitを持ち、実際の包含がそれを保存することを最終入力だけから導く。
`scripts/check_weak_equivalence_filtered_colimits.lean`で一般の宇宙・colimit cocone・
モデル分解・最終入力からの利用例と全10宣言の標準公理監査を検証した。
部分圏自体の小さい可呈示生成族はまだ構成していないため、A1全体の完成とはしない。

## A1：可呈示弱反射からの生成族（一般論、2026-10-15）

`Smith/PresentableFullInclusion.lean`はaccessibleなfully faithful関手が、像の対象の
κ-可呈示性を反映することを証明する。`Smith/PresentableWeakReflection.lean`は
κ-可呈示対象を保つ弱反射を入力とし、部分圏内のκ-可呈示対象と固定対象への射の
圏がκ-filteredであること、その表示がdenseであることを証明する。包含が
κ-accessibleで部分圏がκ-filtered colimitを持つ場合、この表示を使って部分圏自体の
κ-accessibilityを導く。任意のfull imageのaccessibilityは使わない。

`Smith/GeneratedWeakReflection.lean`は生成因子分解の実際の右因子に対するunitを
構成し、右持ち上げクラスへの任意のsquareがunitを越えて延長することを、実際の
liftによって証明する。`check_presentable_weak_reflection`で一般の宇宙、恒等弱反射、
モデル構造を仮定しない生成分解を検証し、三モジュール全44宣言を標準公理のみで
監査した。これを生成右クラスへ適用し、さらに元のWに必要な閉操作へ進む。

`Smith/AccessibleRightClass.lean`の`exists_accessible_right_lifting_class`は、局所可呈示性と
小さいIだけからI.rlpのfull subcategoryのaccessibilityと包含のaccessibilityを証明する。
A0の右因子にuniformizationを適用し、生成射の可呈示性と共通化した大きい正則基数で
上の生成族構成を適用する。`check_accessible_right_class`は一般の宇宙と、既存モデルの
trivial fibrationの部分圏への適用を検証する。元のWへの適用に必要な閉操作は残る。

`Smith/LocalPresentableCover.lean`は、固定対象Xが部分圏に属するとき、κ-可呈示なAから
Xへの射を、部分圏内のκ-可呈示なBを通して分解できる、という局所条件から生成族を
構成する。大域的な弱反射や、その選択の関手性は要求しない。基礎圏はκ-accessibleで
十分であり、局所可呈示性へ制限しない。
`Smith/WeakReflectionApproximation.lean`は、accessibleでκ-可呈示性を保つFと
可呈示弱反射rに対し、P(FX)のもとでA→Xを可呈示なB→Xへ拡大し、F(A→B)が
rのunitを通して分解することを証明する。`check_local_presentable_cover`は局所被覆・
恒等被覆・弱反射からの被覆・拡大段階を検証し、全宣言を公理監査する。
この拡大の超限反復と元のWへの接続はA1の残作業である。

## A0・A1完了：元の弱同値のaccessibility（2026-10-15）

`Smith/PresentableOverIteration.lean`は、固定対象への射を保ち、可呈示性を維持する
短い超限反復の余極限を構成する。`Smith/LiftingColimitRefinement.lean`は、各段階から
後の段階への写像がI.rlpの対象を経由すれば、十分filteredなcolimitがI.rlpに属する
ことを証明する。各段階自体がI.rlpに属するという仮定は要求しない。

`Smith/RightClassInverseImageCover.lean`は、短い正則基数μと大きい正則基数νを用い、
前記の近似段階をμ回反復する。結果はν-可呈示であり、その像はI.rlpに属する。
`Smith/AccessibleRightClassInverseImage.lean`は、uniformizationで必要な基数を選び、
局所可呈示な圏からのaccessibleなFによる小さい生成右クラスの逆像がaccessibleで、
包含もaccessibleであることを証明する。任意のaccessible関手のfull imageについての
仮定を置くものではない。

`Smith/WeakEquivalencesAccessible.lean`は、この一般定理を第二モデル分解の右因子へ
適用し、**元のモデル構造のW**のaccessibilityと包含のaccessibilityを導く。
`exists_accessible_model_and_weakEquivalences I J`は、Mathlibモデル圏、局所可呈示性、
既存の`CofibrantlyGenerated I J`だけから、両モデル分解・左右四因子・Q/R・Wの部分圏・
Wの包含に共通する正則基数を構成する。`weakEquivalences_solutionSetCondition`でR0の
solution-set入口にも接続する。これによりA0・A1の受入条件を満たした。

`check_weak_equivalences_accessible`は、独立した対象・射の宇宙、一般の逆像定理、
最終入力だけからのA0/A1一括利用とsolution-set接続を検証する。最終五モジュール
全21宣言は標準公理のみ。共有全体の監査は829宣言・60モジュールで成功した。
