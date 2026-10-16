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

## F0開始：Reedyの添字圏・対象・Δ（途中、2026-10-15）

`HomotopyFunctionComplex/Reedy/Index.lean`はMathlibの`ReedyStructure`を使い、
非恒等なdirect射が入るlatching圏と、非恒等なinverse射が出るmatching圏を構成する。
一意分解から、両三角形の介在射が対応するdirect/inverseクラスに属することを証明し、
次数が下がることと最小次数での空性を公開する。
`Reedy/Objects.lean`は実際のcolimit/limit、自然な比較射、相対pushout/pullback比較射と
その四つの可換公式を構成する。存在仮定は各添字圏に対して明示し、一般の源Cを
SSetへ特殊化しない。RMapの値域としてSSetを使うことと、源Cの特殊化は別である。
`Reedy/Simplex.lean`は既存の像分解からΔのepi/mono一意分解と次数公理を証明し、
MathlibのReedy構造を実際に構成する。Δopはそのop構造である。

`check_reedy_objects`は独立した宇宙、相対比較の可換性、Δ・Δopの次数0の空性、
実際の一意分解を検証し、三モジュール全57宣言を標準公理のみで監査する。
これだけでF0完了とはしない。有限添字の存在、次数帰納による拡張と関手的分解、
Reedyモデル公理・resolution、およびF1〜F4は引き続き実装する。

`Reedy/IndexOpposite.lean`は、op構造のlatching対象と元のmatching対象、およびその
双対の対象全単射を構成する。`Reedy/SimplexFinite.lean`は、次数の上界と有限なHom集合
への明示的な単射により、Δ・Δopのlatching/matchingの四つの添字圏が有限であることを
証明する。`FinCategory`も構成するので、任意のモデル圏の有限極限・有限余極限から
必要な比較射の存在が得られる。`check_reedy_simplex_finite`は追加の局所可呈示性を
仮定せず、任意モデル源で四種類の比較と相対比較を検証する。両モジュール全34宣言は
標準公理のみ。共有全体は920宣言・65モジュールで監査成功。F0の分解・モデル公理と
F1〜F4はまだ未完了である。

## F0：下位次数の境界と自然変換（途中、2026-10-15）

`Reedy/Degree.lean`は次数で切った充満部分圏を構成し、latching/matchingの図式が
現在の次数より下へ因数分解することを証明する。inverse/direct射での自然性から、
Mathlibの実際のReedy分解を用いてすべての射で自然な変換を構成する。
`Reedy/Boundary.lean`は下位次数だけに定義された図式Hから実際の境界射L→Mを
構成する。入るdirect射と出るinverse射の合成は下位図式で評価でき、その各成分の
公式を証明する。現在次数の対象を先に仮定しない。
`Reedy/LowerTransformation.lean`は、下位次数の自然変換からL_j F→G_jとF_j→M_j Gを
構成し、両方の比較射との可換性を、下位次数内の合成射での自然性から証明する。
`check_reedy_lower_boundary`で独立した宇宙、Δでの自然変換構成、Δopでの有限境界、
下位変換の境界比較を検証した。全38宣言は標準公理のみ。共有全体は958宣言・
68モジュールで監査成功。次数帰納での持ち上げ・分解、モデル公理とF1〜F4は残る。

`Reedy/LowerTransformationNaturality.lean`は、下位変換の二つの拡張について、全体で
定義された自然変換との前後合成・制限の六公式を証明する。`Reedy/LiftingStep.lean`は、
下位次数ですでに自然なliftから、相対latching射と相対matching射の間の実際の
可換正方形を構成する。その正方形のliftから新しい成分を構成し、元のsquareの
左右の分解と、入るdirect射・出るinverse射での自然性を証明する。モデル構造は
この補題の入力には要求せず、該当する相対射の持ち上げ性だけを用いる。
`check_reedy_lifting_step`で実際のsquare、成分の存在・分解・両方向の自然性を検証し、
二モジュール全31宣言を標準公理のみで監査した。共有全体は989宣言・70モジュール。
この一段の構成だけで、全次数のReedy持ち上げや分解が完成したとは判定しない。

## F0：全次数のReedy持ち上げ（途中、2026-10-15）

`Reedy/LowerNaturality.lean`は、次数制限内でのReedy分解と自然性の判定を証明する。
`Reedy/LiftBelow.lean`は下位次数での実際の自然なliftとその分解等式を保持する。
`Reedy/LiftSuccessor.lean`は既存成分を保持し、次の次数の各成分を前記の持ち上げ
正方形から追加する。direct/inverse射での自然性を証明し、同次数ではそれらの射が
恒等射となることを使う。一般の射での自然性は実際のReedy分解で回復する。

`Reedy/Lifting.lean`は、すべての有限次数制限のliftを整合的に反復し、全図式上の
一つの自然変換を構成する。主定理`Lifting.hasLiftingProperty r`は、自然数次数の
一般のReedy圏で、各相対latching/matching射の持ち上げ性から図式圏での
`HasLiftingProperty i p`を証明する。モデル構造を入力に要求しない。
`check_reedy_lifting`は一般の宇宙、全体の自然なlift・両分解等式・既存成分の保持、
Δ/Δopでの任意モデル源への二種類の相対trivial条件の適用を検証する。
新規四モジュール全63宣言は標準公理のみ。共有全体は1052宣言・74モジュール。
objectwise Wと相対trivial条件の同値、Reedy関手的因子分解・モデル公理・resolutionと
F1〜F4は引き続き残る。

`Reedy/FunctorData.lean`は、inverse/direct射での作用、各クラス内の合成、directの後に
inverseが続く場合の交換則から、全射上の実際の関手を構成する。一般射の合成則を
Reedy一意分解から証明し、inverse/directへの制限が入力の作用に一致することも示す。
既存関手から作ったデータの再構成がすべての射で元と一致することを検証した。
`check_reedy_functor_data`は一般の宇宙とΔ上の既存関手を使い、全37宣言を標準公理のみで
監査する。これは中間図式を構成するための入口であり、境界因子分解からこのデータを
実際に作ることと、関手的Reedy因子分解そのものはまだ残っている。


## F0：境界因子分解からの中間図式（途中、2026-10-15）

`Reedy/Subcategory`と`Reedy/Induced`は、inverse射で閉じた対象集合に実際のReedy構造を
構成する。`Reedy/Adjoin`は下位対象に一対象jを追加した添字圏である。次数関数の単射性は
要求しない。`Reedy/ExtensionData`と`Reedy/ExtensionFunctor`は境界L(H)→M(H)の因子分解
から実際の拡張図式を構成する。新対象を経由する合成則を含め、全射の関手の法則を証明し、
下位の全射がHと一致することと制限自然同型を与える。前節末尾の未実装項目のうち、
境界からの関手データの実際の構成はこれで実装済みとなった。

`Reedy/ExtensionTransformation`と`Reedy/ExtensionBoundary`は、追加図式間の自然変換と
latching/matching射の自然性を構成する。`Reedy/ExtensionOfFunctor`は既存図式と自然変換を
入力へ変換する。`Reedy/RelativeExtension`は下位図式での因子分解から、相対latchingの
押し出し→相対matchingの引き戻しの実際の射を作る。その因子分解から中間図式と左右の
自然変換を構成し、合成が元の変換になることを証明した。新対象での両相対射は選んだ
因子分解の左右の射に等しく、それぞれの射のクラスへの所属も保つ。

`Reedy/ExtensionDegree`は次数が対象を区別する場合、追加図式を通常の閉じた次数制限
`Upper`上へ戻し、下位図式を保つ自然同型を構成する。ΔとΔopの両方で利用例を検証した。
`check_reedy_extension`は一般の宇宙と任意の値圏Cを使い、中間図式を仮定せずに構成する
利用例、全下位射の保持、両相対射の所属、自然変換の合成、制限自然同型を検証する。
追加十モジュール全232宣言と共有基盤1320宣言・85モジュールは標準公理のみで監査成功。
共有入口のビルド1613 jobsと既存のaccessibility・共有基盤・スペクトルの回帰検証も成功。

全次数での整合的反復と関手的Reedy因子分解、objectwise Wと相対trivial条件の同値、
モデル公理とresolutionはF0の残項目であり、F1〜F4も引き続き未完了である。


## F0：全次数の中間図式と両射の整合的な反復（途中、2026-10-15）

`Reedy/DiagramTower`は有限次数の図式と隣接段の制限同型から、任意の二段の比較と
三段間の合成則を構成する。`Reedy/DiagramGluing`はこれらから全体の実際の関手を作り、
共通上位段の選択への非依存性と、各有限次数への制限自然同型を証明する。
`Reedy/TowerTransformation`は整合的な各段の変換を貼り合わせ、恒等変換と合成を保つ。
`Reedy/TowerOfFunctor`は元の関手の全射での回復を証明する。
`Reedy/FactorizationTower`は整合的な各段の因子分解から全体の中間図式と左右の自然変換を
構成し、分解等式と各段への左右の射の制限を証明する。

`Reedy/ExtensionComparison`は再構成した図式と元の図式を自然に比較する。
`Reedy/DegreeFactorizationStep`は元の自然変換の閉じた次数制限を因子分解する。
`Reedy/ExtensionRestriction`と一段構成の二つの制限公式により、左右の射まで前の段を保つ。
`Reedy/FactorizationSequence`は次数関数が対象と自然数の全単射になる場合、その一段構成を
実際に反復して整合的な列を作り、全体の因子分解へ貼り合わせる。列は入力に仮定しない。
通常の因子分解の選択だけで構成でき、`HasFactorization`と選んだ関手的データの両入口を持つ。
Δ・Δopでは任意モデル源Cの有限極限・有限余極限と通常の因子分解公理だけで利用例が通る。

現時点の全体の出力は`MapFactorizationData ⊤ ⊤ τ`である。実際の中間図式と両自然変換・
分解等式を構成済みだが、全体の両相対射のReedyクラスへの所属と、入力の可換正方形に
対する関手性は未証明である。F0のReedyモデル構造やresolutionの完成とは区別する。
通常の因子分解と関手的因子分解の区別によって、F1の任意モデル源の契約を狭めない。

`check_reedy_diagram_tower`の九モジュール全188宣言、共有基盤1507宣言・94モジュールは
標準公理のみで監査成功。共有入口のビルド1622 jobsと、従来の追加図式・accessibility・
共有基盤・スペクトルの回帰検証も成功した。F0の残りとF1〜F4は引き続き未完了である。


## F0：全体の相対Reedyクラスと弱因子分解系（途中、2026-10-15）

共有の`CategoryTheory/RelativeArrow`は、自然変換から作る相対押し出し・引き戻しの射を
射圏の関手にする。`Reedy/RelativeArrow`は既存の相対latching/matching写像にこれを適用し、
`reedyLeft`・`reedyRight`の同型・retract閉性を証明する。
`BoundaryDiagram`・`BoundaryDiagramIso`は下位図式と追加対象のgluingデータを圏にまとめ、
`BoundaryReconstruction`・`BoundaryDegree`は実際の追加図式・通常の次数制限を経由する
回復が恒等関手と自然同型になることを証明する。比較は射と可換正方形も含む。

`FactorizationArrowComparison`は一段構成を源の相対境界射の因子分解と射圏で比較し、
`FactorizationRestrictionArrow`は各段と全体の因子分解を射圏の同型で比較する。
`FactorizationClasses`はこれらを合成し、全体の実際の両射が相対Reedyクラスに属することを
証明する。新しい`FactorizationSequence.reedyFactorizationData`は前節の`⊤ ⊤`の出力を
`MapFactorizationData (reedyLeft r left) (reedyRight r right) τ`へ強めた入口である。

`WeakFactorizationSystem`は、次数関数が対象と自然数の全単射になる一般のReedy圏で、
源の弱因子分解系を相対Reedyクラスの弱因子分解系に移す。全次数の実際の因子分解、
retract閉性、全体の持ち上げ定理から、左右が相手の持ち上げクラスそのものであることを
証明した。Δ・Δopの任意モデル源Cで(cof,trivial fib)・(trivial cof,fib)の四つの利用例が通り、
源の通常のモデル公理以外に関手的分解やcombinatorial性は要求しない。

追加十モジュール173宣言、共有基盤1691宣言・104モジュールは標準公理のみで監査成功。
共有入口のビルド1632 jobs、既存の図式反復・追加図式・accessibility・共有基盤・
スペクトルの回帰検証も成功した。objectwise Wとrelative trivial条件の同値、入力の
正方形に対する関手的因子分解、モデル公理・resolutionとF1〜F4は引き続き残る。


## F0：実際のクラス付き関手的因子分解（途中、2026-10-15）

`FactorizationProblem`は境界図式の射と下位の因子分解を圏にまとめ、
`RelativeBoundaryFunctor`は相対押し出し→相対引き戻しの射を、元の可換正方形にも
作用する射圏の関手にする。`FunctorialExtension`はこれを選んだ源の関手的因子分解へ渡し、
新しい中間境界図式の関手と両自然変換を構成する。gluing則と両因子の分解等式も証明する。

`FunctorFactorizationFamily`は元の射圏上の関手的因子分解の族を扱い、
`FunctorialDegreeStep`・`FunctorialSuccessor`は通常の次数制限上での一段構成を与える。
下位へ戻す同型は入力の可換正方形に自然で、両因子と可換である。
`FunctorialSequence`は全次数でこの構成を反復し、各段の評価が同じ源の選択を用いた
通常の反復構成と等しいことも証明する。

`GlobalFunctorialFactorization`は全体の中間図式を`Arrow (J ⥤ C) ⥤ (J ⥤ C)`という実際の
関手にし、左右の自然変換と元の射への分解等式を構成する。
`DegreeClassTransfer`と`FunctorialFactorizationClasses`は、実際の全体の両因子に相対Reedy
クラスの所属を付ける。最終入口`FunctorFactorizationSequence.functorialFactorizationData`は
`FunctorialFactorizationData (reedyLeft r left) (reedyRight r right)`を出力する。

次数が対象と自然数の全単射になる一般のReedy圏で使える。Δ・Δopでは任意のモデル源Cの
有限極限・有限余極限と、選んだ源の関手的因子分解データから適用できる。
通常のモデル公理だけで与えられる分解と、選んだ関手的データの必要性は区別する。
追加十モジュール200宣言、共有基盤1891宣言・114モジュールは標準公理のみで監査成功。
共有入口のビルド1642 jobs、Δ・Δop両組の利用例、既存の相対射・図式反復・accessibility・
共有基盤・スペクトルの回帰検証も成功した。

objectwise Wとrelative trivial条件の同値、Reedyモデル公理・resolutionとF1〜F4は残る。
今回の関手的分解によって、F1の任意モデル源という契約を追加仮定付きへ狭めない。


## F0：Δ・ΔopのReedyモデル構造（resolutionは未完了、2026-10-15）

`Reedy/IndexReedy`はmatchingの添字圏をinverse型、latchingの添字圏をdirect型の
Reedy圏にする。`NestedMatching`・`NestedLatching`は入れ子の境界と元の対象の境界を
圏同値で比較し、`MatchingRestriction`・`LatchingRestriction`は実際の相対射のArrow同型を
与える。`EmptyBoundary`・`BoundaryLifting`・`BoundaryClasses`は全体のReedy持ち上げと
随伴を通じ、下位の相対クラスを実際の境界評価へ移す。

`ObjectwiseTrivial`はrelative trivial cofibration/fibrationを、Reedy cofibration/fibration
かつobjectwise Wと同値にする。`ModelCategory`は二つの構成済み弱因子分解系から
モデル公理を得る。`Reedy.simplexModelCategory`と`Reedy.simplexOpModelCategory`が任意のモデル源Cだけから
両図式圏の実際のモデル構造を返す。関手的な源の因子分解や無限の完備性は要求しない。
三クラスの一致も六つの式で証明した。

共有入口1656 jobs、境界の138宣言・10モジュール、モデル構造の34宣言・3モジュールを
検証。共有基盤2063宣言・127モジュールの監査は標準公理のみ。既存のReedy・共有基盤・
スペクトル・弱同値accessibilityの回帰検証も成功した。詳細は計画§173を参照。
F0には定数図式のresolutionが残る。F1〜F4も未完了で、全体の依頼範囲を維持する。


## F0のresolutionとF1の単体的Hom（2026-10-15）

`Reedy/Resolution`は定数図式のcofibrant/fibrant resolutionを通常のモデル公理から
構成する。比較射のobjectwise W、図式のhomotopical constancy、各成分の
cofibrancy/fibrancyも証明する。`Reedy/FunctorialResolution`は、源で選んだ関手的
因子分解から実際の`C ⥤ (J ⥤ C)`と自然な比較を構成する。両族は弱同値も保つ。
`Reedy/SimplexResolution`にΔ・Δopの通常の入口と関手的な入口を置いた。

`HomotopyFunctionComplex/ResolutionHom`は`Hom_C(Q(X)[n],R(Y))`を各次数に持つ
実際の両変数の単体的Hom関手を構成し、三方向の写像の式を証明する。
`ChosenResolutionHom`はこれを源の二つの関手的因子分解から構成した実際のresolutionと
fibrant置換へ適用する。源の追加データは明示的な入力である。

共有入口1664 jobs、resolutionの145宣言・4モジュール、Homの22宣言・2モジュールを
検証。共有全2230宣言・133モジュールは標準公理のみ。詳細は計画§174を参照。
F1のKan性・不変性・π₀比較と任意モデル源での関手性は未完了である。
条件付きHom関手の構成でF1の契約を置き換えず、F2〜F4も引き続き実装する。


## F1：有限tensorと境界の持ち上げ（Kan性は条件付き、2026-10-15）

`PresentationHom`・`PresentationLifting`は、標準単体のpresentationから単体的Homへの
写像を源のcocone・射へ移し、実際の正方形と持ち上げを移送する。
`NonsingularPresentation`・`SubcomplexTensor`は非退化単体の有限posetを用い、
実際のhorn・境界を含むsubcomplexのtensorと包含を構成する。値圏には有限余極限だけを
要求する。`TensorKanCriterion`はhorn tensorのtrivial cofibration性からKan性を導く。
このhorn条件自体はまだ未証明である。

`BoundaryIndex`・`BoundaryTensor`と`Reedy/CofibrantBoundary`は、境界の非退化単体posetと
latching添字圏の圏同値を構成し、境界tensor包含とlatching比較射のArrow同型を証明する。
Reedy cofibrancyから境界tensor包含のcofibration性を導き、通常のcosimplicial resolutionに
対して源のtrivial fibrationに対する全次数の境界持ち上げを得た。

共有入口1725 jobs、追加105宣言・8モジュール、共有全2335宣言・141モジュールを検証し、
公理は標準公理のみ。回帰検証も成功した。詳細と未完了項目は計画§175を参照。
F1の無条件のKan性・導来不変性・π₀比較・任意モデル源の関手性とF2〜F4は未完了である。


## F1：有限tensorの関手性と貼り合わせ（2026-10-15）

`TensorFunctor`・`TensorPushout`・`TensorRepresentable`はsubcomplexのtensorを関手にし、
交差・和のpushout、representableなfaceとA[k]の同型、空のtensorの初期性を証明する。
これらの入口は次の一般論へ接続している。

`FiniteTensor`は有限nonsingular単体集合の充満部分圏からCへの実際の関手で、任意の射を
扱う。単射や固定したambientは要求しない。`FiniteTensorPushout`は、四頂点がこの部分圏に
属する実際のSSetのpushoutをCのpushoutへ送る。`FiniteTensorRepresentable`は標準単体上で
元のcosimplicial図式Aに戻る自然同型を全Δの射に対して証明する。
`FiniteTensorBoundary`は一般の関手による境界生成射の像を実際の境界tensor包含と比較し、
Reedy cofibrancyからそのcofibration性を導く。値圏には有限余極限だけを要求する。

非退化単体のpresentationは、固定版Mathlibの`NonsingularColimit`の構成を自然同型で
接続して再利用する。共有入口1734 jobs、一般の有限tensor46宣言・4モジュール、
gluingの43宣言・3モジュール、従来の有限tensor持ち上げ107宣言・8モジュールを検証。
共有全2426宣言・148モジュールの監査は標準公理のみ。詳細は計画§176を参照。
この時点で残していた有限単射のcofibration性、horn tensorのtrivial cofibration性とKan性は、
次の実装で解消した。


`NonsingularCoproduct`・`FiniteTensorCoproduct`・`FiniteTensorSkeleton`は、有限余積と
固定Mathlibの実際の骨格pushoutを使い、有限nonsingular単体集合の任意の単射の像が
cofibrationになることを証明する。有限次元上界で帰納が尽きるため、無限余極限を追加しない。

`FiniteTensorWeakEquivalence`は、すべての有限交差が標準単体になる有限被覆の貼り合わせを
証明する。`HornTensor`は全hornの面被覆に適用し、Reedy cofibrantかつhomotopically constantな
cosimplicial対象のhorn tensorがtrivial cofibrationになることを証明する。
これにより任意のモデル圏の通常resolutionのHomは、fibrantな対象に対してKan複体となる。
既存のchosen二変数関手の各値のKan性にも接続している。通常resolutionの結果に
関手的分解は不要。chosen関手の結果は、その明示入力を引き続き要求する。

共有入口1740 jobs、新規42宣言・5モジュール、共有全2468宣言・153モジュールの
標準公理監査と回帰検証が成功。実装は`375b1c8`・`1116b19`、詳細は計画§177を参照。
F1の両変数の不変性・π₀比較と任意源での最終関手、F2〜F4は未完了である。


`Simplicial/WeakEquivalence`は、幾何学的実現による既存の弱同値の定義を共有層に置く。
スペクトル側の旧名は定義上等しいaliasである。`TargetInvariance`は境界の持ち上げと
fibrant Brown分解から標的変数の不変性を証明する。
`PresentationSourceLifting`・`RelativeBoundaryTensor`は実際の相対tensorとlatching mapを比較し、
`SourceInvariance`はReedyモデルのcofibrant Brown分解から源変数の不変性を証明する。
一般の源モデルCの通常resolutionにも適用でき、源を単体的モデル圏に限定しない。

共有証明では値域の単体集合モデルとcof=monoの一致を明示入力し、幾何学的Wへの結論には
そのWの一致を使う。上位の`Inputs/Homotopy/ResolutionHom`は既存HT-KQからこれらを供給する。
共有層から引用入力をimportしない。共有入口2309 jobs、共有2531宣言・159モジュールは
標準公理のみで監査成功。上位接続71宣言の直接引用は既存HT-KQ一件のみ。
コミットは`313028c`・`b70180c`・`29a00e7`、詳細は計画§178。
F1のπ₀比較・任意源での最終関手、F2〜F4は残る。依頼範囲はFを経てL0〜L5の完成までに拡張した。


`FiniteTensorBinaryCoproduct`と`BoundaryOne`は、実際の区間境界を頂点二つの余積として
Cへ移す。`ResolutionCylinder`は次数0・1からMathlibの実際のgood cylinderを構成する。
`PiZero`は、Homのedgeとこのcylinder上のホモトピーを比較し、0単体が定める写像
π₀ Hom(A,Y)→LeftHomotopyClass(A[0],Y)の全単射性を証明する。

任意のordinary localization L:C→Hについて、通常resolution q→Xとfibrant Yから
π₀ Hom(q,Y)≃Hom_H(LX,LY)を得る。既存chosen二変数関手についても、置換前のX,Yの射との
同値を構成し、源・標的の任意の射について自然性を証明する。
この比較には単体集合モデルやHT-KQ、通常resolutionの関手的分解は不要である。
Hの対象・射の宇宙は独立に扱う。

共有入口2321 jobs、新規85宣言・4モジュール、共有2616宣言・163モジュールの
標準公理監査と回帰検証が成功。実装は`c8f9445`、詳細は計画§179。
F1の任意源での最終の厳密な関手の入口、F2〜F4、L0〜L5は引き続き未完了である。


`Generated/CommonCofibrantReplacement`・`CommonFibrantReplacement`は、実際のfunctor categoryの
pullback/pushoutと指定した関手的分解から、一般のモデル圏の自然な共通置換を構成する。
`ResolutionHomNaturality`はfamilyと標的置換の自然変換を実際の二変数Hom関手へ移す。
`ResolutionComparison`は任意の二つのcosimplicial resolution familyを共通familyへ比較し、
`TargetComparison`は異なるfibrantTargetを共通のfibrant値関手へ比較する。

`ChosenComparison`は、異なるcof₁/fib₁とcof₂/fib₂から作った実際のHom関手に対して、
共通のKan値二変数関手への自然な弱同値のzigzagを構成する。補助分解も独立に指定できる。
共有証明では基準単体集合モデルとクラスの一致を明示し、上位`Inputs/Homotopy/ResolutionHom`は
既存HT-KQからその入力を供給する。新しい引用を導入しない。

共有入口2327 jobs、新規83宣言・6モジュール、共有2699宣言・169モジュールの
標準公理監査と回帰検証が成功。上位155宣言の直接引用は既存HT-KQ一件だけ。
コミットは`253cc8c`・`cda767b`、詳細は計画§180。
F2の実際の単体的Mapとの比較、F1の任意源での最終関手、F3・F4とL0〜L5は未完了である。


`SimplicialTensorHom`は、既存のSSet豊穣tensorとMapの随伴表示から、
n↦Δ[n]⊗XのHomと実際のMap(X,Y)の単体集合の同型を構成する。
単体の射・源・標的の任意の射との自然性を証明し、任意のQ/Rによる
二変数関手の自然同型と、実際のMap(QX,RY)への各値の同型を得る。
この同型自体はモデル構造・cofibrancy・fibrancyを要求しない。

`StandardCosimplicial`は任意の左随伴による有限tensorの保存と境界包含の対応を証明する。
left QuillenなFと値域のcof=monoからΔ[-]⋙FのReedy cofibrancyを得る。
`SimplicialTensorCofibrant`はSM7からcofibrantなXに対するn↦Δ[n]⊗Xへ適用し、
Reedy cofibrancyを別に仮定しない。

共有入口2330 jobs、新規26宣言・3モジュール、共有2725宣言・172モジュールの
標準公理監査と回帰検証が成功。コミットは`4e6ffc9`、詳細は計画§181。
標準tensor図式のaugmentation・homotopical constancyと一般のresolutionへの比較はまだ残る。
F2全体、F1の任意源での最終関手、F3・F4とL0〜L5の完了とは判定しない。


`Topological/BasedContraction`は、基点を固定する収縮から、任意宇宙の立方体ループの全境界に
相対的な収縮と実際のホモトピー群のsubsingleton性を証明する。
`Simplicial/StandardSimplexWeakEquivalence`は標準位相単体の線形収縮と実際の幾何学的実現を使い、
標準単体間の任意の射が幾何学的弱同値になることを証明する。この部分にモデル存在入力は不要。

一般の豊穣`TensorUnit`は、表示されたtensorの単位が恒等関手と自然に同型であることを証明する。
`SimplicialTensorAugmentation`は、実際のcollapse Δ[n]→Δ[0]とΔ[0]⊗-≅Idから
自然augmentationを構成する。`SimplicialTensorConstant`は幾何学的Wの一致、Brown補題、SM7から
cofibrantなXに対するhomotopical constancyとaugmentationのobjectwise弱同値性を導く。
Reedy trivial fibrationとは区別して扱い、その条件を未証明のまま強いresolutionの型へ変換しない。

共有入口2337 jobs、新規41宣言・5モジュール、共有2766宣言・177モジュールの標準公理監査と
回帰検証が成功。コミットは`1ebbbf8`、詳細は計画§182。一般のresolutionとの最終の自然比較は
まだ残る。F2全体、F1の任意源での最終関手、F3・F4とL0〜L5は未完了である。


`CosimplicialFrameFamily`はobjectwise弱同値のaugmentationを持つReedy cofibrant familyを扱う。
`FrameComparison`は強いresolutionとのpullbackと共通cofibrant replacementから自然比較を構成し、
弱いaugmentationにReedy trivial fibrationを要求しない。共通のHomはKanで、両比較は弱同値になる。

`SimplicialMapComparison`は標準tensor frameと二変数自然同型を合成し、任意の指定Q/Rについて
resolution Homと実際のMap(QX,RY)を自然な弱同値のcospanで比較する。
`ChosenMapComparison`はQ/Rも既存の二つの明示的源因子分解から構成し、追加のframe仮定を不要にする。
源は一般の単体的モデル圏で、共有層から引用入力をimportしない。

共有入口2341 jobs、新規70宣言・4モジュール、共有2836宣言・181モジュールの標準公理監査と
回帰検証が成功。コミットは`88f619b`、詳細は計画§183。指定分解からのF2比較は揃ったが、
F1の任意源での最終の厳密な関手、F3・F4、L0〜L5は残る。A0・A1は計画§166で完了済み。


`HomotopyFunctionComplex/Accessible`は、小さい固定cosimplicial対象族の全次数の共通可呈示基数を選び、
accessibleな標的置換との実際のresolution Homが同じ基数でaccessibleになることを証明する。
`MappingTests`は各局所化射に対する実際のprecompositionをArrow SSetへの関手として集め、
両端のRMap評価からそのaccessibilityを得る。

`AccessibleModelMapping`は元のcombinatorialモデルと小さい任意の射族だけから、A0の指定因子分解、
Q/R、A1の元のWと包含、全始域・終域のRMap評価、全検出射の関手を共通基数で扱う。
空の族と独立した宇宙にも対応し、源のcofibrancy・単体集合モデルを追加仮定にしない。
共有入口2343 jobs、新規19宣言・2モジュール、共有2855宣言・183モジュールの標準公理監査と
回帰検証が成功。コミットは`ffcab98`、詳細は計画§184。
F3のresolution全体のaccessibilityは別に残り、F1の任意源での最終関手、F4、L0〜L5も未完了である。


F3は計画§185で完了した。`Smith/AccessibleAdjunction`は稠密な可呈示対象族と随伴Hom同型から
右随伴のaccessibilityを証明し、`AccessibleLimits`は小さい形の実際のlimへ適用する。
`Reedy/AccessibleBoundary`・`AccessibleRelativeBoundary`はlatching/matchingと相対pushout/pullbackを
既存の関手へ接続する。`AccessibleFactorization`は実際の有限段階を帰納し、全次数のmiddle functorへ移す。
`AccessibleResolution`は従来のinitial/terminal constant arrowsへの制限を扱う。

`AccessibleResolutions/exists_accessible_resolutions_and_mapping_tests`は、元のcombinatorialモデルと
固定した小さい任意の射族だけから、A0の指定因子分解・Q/R、実際のΔ・Δopのresolution family、
A1の元のWと包含、全始域・終域のRMap評価・検出関手の共通基数を構成する。
source resolutionのaccessibilityを追加仮定にせず、全対象のRMap評価への一律の基数も要求しない。
共有入口2354 jobs、共有2941宣言・192モジュールの標準公理監査と回帰検証が成功。
コミットは`d71c2d1`・`19e4a10`。F1の任意源での最終関手、F4とL0〜L5は未完了である。


`Diagram/Projective`は元のcombinatorialモデルから実際の小さいfunctor categoryのprojectiveモデルを
構成する。free/evaluation随伴、生成族のSOA、評価でのtrivial cofibrationとセルのacyclicityを証明し、
弱同値・fibrationのobjectwise判定、生成性、関手的分解を得る。
`ProjectiveQuillen`はcolimのleft Quillen性と実際のpointwise left derived colimitの存在へ接続する。

`HomotopyColimit`は実際のprojective cofibrant replacementからhocolimと自然比較を構成する。
任意のobjectwise弱同値への不変性、cofibrant図式での通常のcolimitとの比較、任意のordinary derived
colimitとの自然同型を証明する。`ColimitWeakEquivalence`と`FilteredHomotopyColimit`はA1から、
図式の形に依存しない基数の上界を構成し、すべての十分filteredな図式のhocolim→colimを弱同値とする。

共有入口2360 jobs、共有3005宣言・197モジュールの標準公理監査と回帰検証が成功。
コミットは`c71600d`・`f7cc57a`、詳細は計画§186。
F4のRMapのhocolim→holim公式は残り、通常のlimitとの同型だけで代用しない。
F1の任意源での最終関手とL0〜L5も未完了である。


`PointwiseAdjunction`と`Diagram/ProjectiveBifunctor`は一般のtensor/cotensorのQuillen条件を
projective図式モデルへ持ち上げる。`FrameRightQuillen`は一般のモデル源のcosimplicial frameの
実際のHom関手を右Quillenとし、pointwise right derived functorの存在を証明する。
単体的集合の生成性・SM7・monoidal条件の既存証明は`Simplicial/Generators`と
`ModelCompatibility`へ共有化し、スペクトル側の既存名を互換aliasで維持する。

`Diagram/WeightedCones`は重み付きtensorの実際の右随伴を構成する。
`HomotopyCones`は定数単位のprojective cofibrant weightと入力の実際のfibrant replacementを使い、
fibrantな値と弱同値不変性、任意のright derived cone functorとの自然比較を証明する。
`WeightComparison`と`DerivedConstantAdjunction`はtensor weight→constの弱同値を導来し、
`HomotopyLimit`はcanonicalな局所化後の定数関手の右随伴としての普遍性を公開する。
ordinary localizationの出力宇宙は独立。図式と単体的集合の値は同じ宇宙wで扱う。

共有入口2392 jobs、新規holim側60宣言・5モジュール、共有3091宣言・207モジュールの
標準公理監査と回帰検証が成功。コミットは`a44d6e3`・`451422e`・`e72550c`、詳細は計画§187。
RMap(hocolim D,Y)とholim RMap(D_i,Y)の自然な弱同値は引き続き残り、今回のordinaryな
普遍性だけでF4完了とはしない。F1の任意源での最終関手とL0〜L5も未完了である。


`Reedy/LatchingPreservation`と`FramePreservation`は一般の左Quillen左随伴によるframeの保存を
実際のlatching射のArrow同型とBrown補題から証明する。`AdjunctionHom`は独立したHom宇宙を
共通の最大宇宙へULiftし、通常の随伴のHom同値を単体的・両変数自然同型にする。

`Diagram/ColimitFrame`は実際のprojective cofibrant replacementをresolveして各次数でcolimitを取り、
実際のhocolimへの弱augmentationを持つ自然なframeを構成する。
`FrameOverFunctor`と`ColimitMapComparison`は、RMap(hocolim D,Y)とこのframe Homから、
共通のKan値関手への両変数自然な弱同値を構成する。図式圏で定数RYへのresolution Homとの
自然同型、元のDのresolutionからの自然な弱同値も構成する。源Cに豊穣化は要求しない。

`Diagram/ProjectiveCofibrations`は自由生成射・relative cell・retractを評価し、projective cofibrationの
各点でのcofibration性を証明する。特に実際のQ_K(D)の各点はcofibrantである。
共有入口2399 jobs、共有3173宣言・214モジュールの標準公理監査と回帰検証が成功。
コミットは`ca5d064`・`8dbb4e4`、詳細は計画§188。
図式圏のHomを§187のweighted holimへ比較する部分と、必要なULiftの弱同値適合は残る。
F4全体、F1の任意源での最終関手、L0〜L5は未完了であり、一般局所化までの契約を維持する。


`Reedy/LatchingPreservation`は必要な個々のlatching余極限とcofibrationの保存だけへ一般化した。
`Diagram/EvaluatedFrame`はprojective cosimplicial resolutionをD・kに自然に評価し、
元のD(k)への弱augmentationを持つ実際のReedy cofibrant frameを構成する。
`PointwiseMappingComparison`は既存のk↦RMap(D(k),Y)図式と評価frameのHom図式から、
共通のKan値図式への自然な弱同値を構成する。比較はD・k・Yのすべてで自然である。

`Diagram/MappingLimit`は任意のcosimplicial diagramのHomを、各点のHomの通常のlimitとして
実際のコーンと普遍射から証明する。Hom宇宙と添字宇宙の最大へULiftし、モデル構造を仮定しない。
`FrameMappingLimit`は実際のdiagram-resolution Homを、上のRMap比較で使うframe図式の
通常のlimitへ同定する。limitの存在も構成し、chosen limitと比較する。

共有入口2403 jobs、共有3242宣言・218モジュールの標準公理監査と回帰検証が成功。
コミットは`9161b0c`・`6525eec`、詳細は計画§189。
通常のlimitがweighted holimを計算することと、必要なULift・添字宇宙変更の弱同値適合は残る。
点ごとのKan性や通常のlimitの普遍性だけでF4完了とはしない。F1の任意源の最終関手とL0〜L5も残る。


`HomotopyFunctionComplex/Realization`は標準単体に沿う実際の左Kan拡張とcosimplicialHomとの随伴、
標準単体上の同型、frameの場合のQuillen性を構成する。`SmallHomModel`と`SmallHomRealization`は
MathlibのShrinkHomsへ三クラスと局所可呈示性を移し、元のCへのSSet.{w} realizationを得る。
対象・Hom・局所可呈示性の宇宙は独立で、vサイズ余極限の追加仮定は不要である。
元のHomとの比較は共通宇宙へのULift後の実際の自然同型として公開する。

`Diagram/FrameWeightRealization`は任意の重み図式をpresheafの左Kan拡張でrealizeする。
`FrameWeightQuillen`と`SmallHomFrameWeights`は、点ごとのframe条件からprojective重みモデルに
対するQuillen随伴を得る。cofibrant重みと非cofibrantな定数重みを区別する。
`FrameWeightedLimit`は指定したcofibrant重みのweighted Homを、構成済みの実際のholimへ
自然に比較し、fibrantな標的での弱同値性を証明する。指定Rで前合成した全Yでも弱同値になる。

共有入口2411 jobs、共有3336宣言・225モジュールの標準公理監査と回帰検証が成功。
コミットは`94f8766`・`495b097`、詳細は計画§190。
重み付きrealizationの源とhocolimの比較、RMapへの最終同定、必要なULiftの弱同値適合は残る。
非cofibrantな定数重みへのBrown補題を先取りしない。F1の任意源の最終関手とL0〜L5も未完了である。


`Diagram/ConstantWeightHom`・`ConstantWeightRealization`・`SmallHomConstantWeight`は、
定数標準単体の重みrealizationを対応次数のcolimitへ同定する。モデル構造を要求しない同定を
独立したHom宇宙の元のCへ移送し、単位重みの場合も公開する。
`DegreeZeroHomotopyColimit`は指定したprojective resolutionの第0次数のcolimitから、
実際のhocolimへの自然な弱同値を構成する。D自体のcofibrancyは不要である。

`WeightedSourceComparison`は重み付き左随伴の単位での値からhocolimへの実際の源比較射を構成する。
全体の弱同値性は重みaugmentationのrealizationの弱同値性と同値であり、この最後の条件は未証明。
合成全体のDでの自然性、RMapへの最終接続、ULiftの弱同値適合も残る。
共有入口2416 jobs、共有3390宣言・230モジュールの標準公理監査と回帰検証が成功。
コミットは`c3a8584`、詳細は計画§191。F4全体・F1の任意源の最終関手・L0〜L5は未完了である。


`Localization/MappingTests`は実際のmapping bifunctorから局所対象と検出射クラスを定義し、
二対三性・retract閉性、単調性、局所対象を変えない射クラスの閉操作を証明する。
`Localization/Basic`は既存のchosenResolutionHomを使い、元の弱同値の包含、標的の弱同値不変性、
fibrant局所対象だけによる検査、弱squareや自然なQ→idによるSの代表変更の独立性を証明する。
`ChoiceIndependence`は既存の自然な弱同値cospanから、二組の実際のresolution/replacementで
局所対象・局所同値クラスが等しくなることを証明する。局所モデルの存在は仮定しない。

共有入口2419 jobs、共有3437宣言・233モジュールの標準公理監査と回帰検証が成功。
コミットは`4cbea1d`、詳細は計画§192。空集合で元の弱同値クラスを回復する逆向きの検出と、
条件付き局所化APIは未完了であり、L0全体の完了とはしない。F4の残項目とL1〜L5も維持する。


`Quillen/WhiteheadConverse`と`Saturation`はモデル公理と基本補題だけから、任意の通常の局所化で
射が可逆になることと元の弱同値性の同値を証明する。関手的分解やcombinatorial性は要求しない。
`Simplicial/PiZeroWeakEquivalence`は境界持ち上げ・section・Brown分解により実際のπ₀の全単射を証明する。
`Localization/Detection`は既存のRMapのπ₀比較の自然性を使い、すべての標的へのmapping testで
元の弱同値を検出する。S≤W_CならW_S=W_Cとなり、空集合の場合も含む。

`Localization/Conditional`は実際の候補モデルの証明書から、fibrationの式、trivial fibrationの一致、
恒等関手の左Quillen性を導く。空集合では元モデル自身の証明書を構成し、三クラスを回復する。
`Representatives`は任意のweak-square zigzagによるSの代表変更で局所対象・局所同値が変わらないことを証明する。
共有入口2425 jobs、共有3480宣言・239モジュールの標準公理監査と回帰検証が成功。
コミットは`e8ec17e`・`6f35f97`・`da42c88`。計画§193でL0の受入項目を照合して完了とした。
F4の最終比較・F1の任意源の最終関手・L1〜L5は引き続き未完了である。


`Transfer/FullyFaithfulLifting`は両射の像で持ち上げ条件を反映・保存する。
`Quillen/FullyFaithfulReflection`はcofibration・fibration・trivial fibrationを保存する
fully faithful関手による全弱同値の反映を証明する。どちらも随伴を要求しない。
`Simplicial/UniverseLift`・`UniverseLiftLifting`は実際の標準単体・境界・hornの同型、
生成射のArrow同型と、境界・horn右クラスの保存・反映を構成する。

`UniverseLiftModel`・`UniverseLiftWeakEquivalence`は、両宇宙の指定mono/Kanモデル間で
ULiftの左右Quillen条件と、任意の射の弱同値の保存・反映を証明する。Kan複体に制限しない。
共通宇宙へ持ち上げた後のArrow同型から、独立した二宇宙の弱同値テストも比較できる。
共有入口2431 jobs、共有3525宣言・245モジュールの標準公理監査と回帰検証が成功。
コミットは`c89ef64`・`5b4bc6e`、詳細は計画§194。F4・L1の宇宙変更の前提を一つ解消した。
small-Hom表示の局所性テストの接続とL1のaccessibility、F4の源比較と最終公式は未完了である。


`SmallHomComparison`はShrinkHomsを使う実際のHom bifunctorと、源・標的・単体次数に自然な
共通宇宙での同型を構成する。`Localization/SmallHomTests`は§194の結果を使い、
元のmapping test・局所対象・局所同値クラスとの一致を証明する。
`SmallHomAccessible`は固定した小さいSの評価とA0/A1へ共通のaccessibility基数を与える。
`Smith/AccessibleWeakEquivalenceInverseImage`は、accessibleなArrow値検査関手による
元モデル弱同値の逆像の部分圏と包含のaccessibilityを証明する。源にモデル構造は不要である。

`MappingTestDiagram`は検査族を実際の図式圏内の単一の射へまとめる。
`AccessibleSmallLocalObjects`・`AccessibleLocalObjects`は証明済みprojectiveモデルと逆像定理を
適用し、任意のsmallなSについて元のlocalObjectsの部分圏と実際の包含のaccessibilityを証明する。
任意の元の指定resolution/replacementへ選択独立性で戻すため、そのaccessibilityは仮定しない。
共有入口2438 jobs、共有3571宣言・252モジュールの標準公理監査と回帰検証が成功。
コミットは`7e11097`・`858793c`・`fe6bdc4`、詳細は計画§195。
L1の小さいhomotopy生成族の明示的な検出定理、F4の最終比較、L2〜L5は未完了である。


`YonedaWeights`・`YonedaHomotopyWeight`は実際のfree diagramのcolimitから、定数単位へ弱同値で
写るprojectively cofibrantな重みを構成する。`PostcompositionQuillen`・`PointwiseColimitComparison`・
`QuillenColimitComparison`は評価・postcompositionと実際のhocolim比較のQuillen性を証明する。
`YonedaWeightRealization`は重みの実現とframeの次数0の図式との自然同型を構成する。
`YonedaWeightQuillen`・`SmallHomYonedaWeight`と`Quillen/WeakAugmentation`は、標準の重みの
augmentationが実現後に弱同値になることを、源のHom/重み宇宙を独立にして証明する。
`WeightedSourceWeakEquivalence`はこれを実際のEvaluatedFrameへ適用し、§191のweighted source
comparisonが元のCの弱同値であることを証明する。定数図式のprojective cofibrancyは仮定しない。
共有入口2449 jobs、共有3659宣言・263モジュールの標準公理監査が成功。
コミット`4ce136b`・`a2bbdb9`、詳細は計画§196。F4の最終RMap–holim公式への接続は残る。


`QuillenStandardFrame`は実際の標準単体の左Quillen像のReedy cofibrancyと弱augmentation、
標準単体のcosimplicial Hom≅Idを証明する。`WeightedHomotopyColimitFrame`はこれを適用して
実際のhocolim(D)へ弱augmentationを持つframeを構成する。
`FrameOverObject`と`HocolimMappingComparison`は、Dを固定して標的に自然なzigzag
RMap(hocolim D,−)→middle←frame Hom≅weighted Hom→holimを構成する。
各射は共通宇宙への実際のULift後に弱同値であり、同じ指定fibrantTargetを使用する。
共有入口2453 jobs、共有3703宣言・267モジュールの標準公理監査と既存入口の回帰検証が成功。
コミット`a3d7d10`、詳細は計画§197。源図式Dへの自然性と右辺のpointwise RMapへの接続は残る。


`FrameWeightFunctoriality`は指定済み随伴のmateから実際のrealizationのframe関手性を証明する。
`ConstantWeightNaturality`・`SmallHomWeightFunctoriality`は定数重みとunitの実現同型の自然性を、
元のCの独立したHom/重み宇宙で証明する。`WeightedSourceNaturality`は実際のweighted source
comparisonとhocolim frameのaugmentationをDに自然な変換へまとめる。
`HocolimFrameComparison`は指定RMap(hocolim(−),−)とそのframe Homを、実際の二変数自然cospanで比較する。
共有入口2458 jobs、共有3752宣言・272モジュールの標準公理監査と関連回帰検証が成功。
コミット`2544f499`、詳細は計画§198。weighted Hom同型の源自然性、pointwise RMapへのholim比較は残る。


F4は計画§199で受入照合まで完了。`WeightedFrameHomNaturality`・`HocolimWeightedComparison`は
frame Hom≅weighted Homとholim比較を二変数に自然にする。
`SmallHomFrameInvariance`・`SmallPointwiseMappingComparison`・`PointwiseRMapHomotopyLimit`は
元の指定データを使うpointwise small-Hom RMapと実際のholimの比較を証明する。
`SmallHocolimFrameComparison`はULiftの充満忠実性で同型をSS_wへ戻す。
`HocolimRMapFormula`はRMap(hocolim D,Y)→middle₁←bridge→middle₂←holim RMap(D(k),Y)の
実際の二変数自然な弱同値zigzagと、任意の通常のSS_w局所化後の自然同型を証明する。
独立したu/v/wと任意の元の指定cof/fibを許し、源の豊穣性やSS_v/SS_maxのモデルは要求しない。
共有入口2466 jobs、3834宣言・280モジュールの標準公理監査と関連回帰検証が成功。
コミット`7c07d941`・`6c1ed2ca`。L1の小さいhomotopy生成族、L2〜L5、F1の任意源の最終関手は残る。


L1は計画§200で受入照合まで完了。`HocolimMappingTests`・`FilteredMappingGenerators`は
十分filteredな生成表示とF4を使い、小さい生成族での共変RMapテストを全対象へ拡張する。
`CovariantDetection`・`HomotopyGenerators`はType wの固定したcofibrant族Gを構成し、
任意の指定Q/RによるRMap(G_i,f)が元のW_Cを検出することを証明する。
`AccessibleHomotopyGenerators`は元の局所対象と包含、元のWと包含、指定分解d、GのRMap評価と
Sの全局所化射の実際のArrow値検査を同じ正則κでaccessibleにする。
共有入口2471 jobs、3848宣言・285モジュールの標準公理監査と関連回帰検証が成功。
コミット`f3021ca8`・`753fcd47`。L2〜L5とF1の任意モデル源の最終関手は引き続き未完了。


L2の実行記録は計画§201。`ArrowFrames`・`ArrowFrameTests`は任意の元の射を自然なReedy
cofibrationに置き換え、元のRMapの局所性テストと比較する。`LocalFibrantApproximation`は
小さい相対境界族と元のJから、accessibleなRと自然なcofibration η:Id→Rを実際に構成する。
`FiniteTensorLiftingClass`・`ArrowLiftingClass`・`ArrowTensor`は射圏のモデル構造なしで
相対tensorを扱い、`RelativeSubcomplexTensor`は相対horn tensorの自明cofibration性を証明する。
`ArrowFrameFibrations`・`PresentationSourceLiftingConverse`・`LocalBoundaryCharacterization`は
実際のtestMapのfibration性と、局所fibrant対象↔(J⊔境界生成族).rlpの厳密な判定を証明する。
`LocalReplacementDetection`・`AccessibleLocalEquivalences`は、accessibleなRの単位射が
W_Sに入るという明示仮定からW_S=R⁻¹(W_C)とそのaccessibilityを導く。
構成したηについてこの仮定を解消する証明は未完了。L2〜L5の完了とはしない。
共有入口2484 jobs、3959宣言・298モジュールの標準公理監査、関連利用例・回帰検証が成功。
コミット`fb6222b1`・`d8911e69`・`3de007a5`・`bb3599b6`。


目標はF→L→E→Sの全完了へ拡張（計画§202）。`HocolimLocalEquivalences`はF4の源自然性と
実際のholimの弱同値保存から、元のW_Sのhocolim保存を証明する。実際の弱比較がある場合と
projective cofibrantな図式の場合には、通常colimitの保存へ移す。
`FilteredLocalEquivalences`はS・図式によらない一つの正則κを構成し、すべての正則μ≥κで
μ-filtered colimitがW_Sを保存することを証明する。W_Sのaccessibilityは入力しない。
任意の超限合成・pushout閉性や生成したηのW_S所属を証明したものではなく、L2〜L5は残る。
共有入口2486 jobs、3968宣言・300モジュールの標準公理監査、9宣言・2モジュールの新規監査と
62宣言・9モジュールの局所境界判定の回帰検証が成功。コミット`fee6bdf8`・`d1bee094`。


L3の基礎として`Under/Quillen`は任意の基底射のrestriction/pushoutのQuillen性を証明する。
固定基底から出るcofibration間の弱同値は任意のpushoutで保存され、ここに左固有性は不要。
`Quillen/LeftProper`は元のWのcofに対する相対cobase-change安定性を左固有性の契約として使い、
対応する一方の脚がcofibrationである二つのspan間の弱同値のpushout gluingを証明する。
対象のcofibrancyは要求しない。これは元のWの補題であり、W_Sのpushout閉性への接続は残る。
共有入口2488 jobs、3974宣言・302モジュールの標準公理監査、6宣言・2モジュールの利用例・監査が成功。
コミット`aeb7fd57`、詳細は計画§203。F→L→E→S全体の目標は継続中。


L3のpushout条件は計画§204で完了（L3全体は超限合成閉性を残す）。
`ProjectiveReindexing`・`SpanCofibrations`・`ProjectiveSpan`は実際のprojective持ち上げから
任意のK≌WalkingSpanの両脚のcofibration性を抽出する。
`PushoutComparison`・`SpanHomotopyColimit`は左固有性から、一方の脚がcofibrationであるspanの
実際のhocolim→colimit比較の弱同値性を証明する。対象のcofibrancyは要求しない。
`SpanLocalEquivalences`・`LeftProperPushout`は元のW_Sのpushout保存と
(cof_C⊓W_S).IsStableUnderCobaseChangeを証明する。Sの小ささは不要、u/v/wは独立。
共有入口2495 jobs、3984宣言・309モジュールの標準公理監査、12宣言・7モジュールの利用例・監査と
hocolim保存の回帰検証が成功。コミット`5d8e8972`・`c45e13e4`。
局所化後のモデル構造を先取りしていない。L2・L3の残条件、L4〜S3、F1の任意源の残項目は継続中。


L3の超限合成への基盤（計画§205）：`ContinuousLiftSystem`・`ContinuousLiftSuccessor`・
`ContinuousLiftLimit`・`ContinuousLiftInduction`は任意のwell-ordered添字で実際の整合的な
持ち上げ自然変換を構成し、指定したbottom成分を保存する。モデル構造は不要。
`ContinuousProjectiveCofibrancy`は任意のQ.llpの連続列をprojectiveなLLPへ移し、
初期項cofibrantな連続cofibration列の実際のprojective cofibrancyを証明する。
`ContinuousRelativeCofibrancy`は初期項のcofibrancyなしでConst(D_0)→Dのprojective cofibration性を証明。
`ContinuousHomotopyColimit`の現時点の弱比較は初期項cofibrantの場合であり、
任意の初期項への拡張とW_Sの任意の超限合成閉性は残る。
共有入口2502 jobs、4084宣言・316モジュールの標準公理監査、100宣言・7モジュールの新規監査と
span/pushoutの回帰検証が成功。コミット`8d6e827e`・`34896ff3`。
F→L→E→S全体の目標は継続中。


L3は計画§207で受入検証まで完了（2026-10-16）。`BottomReplacement`・その比較/分解は
最小値を指定して図式を置換する一般構成で、`ProjectiveBottomCofibrancy`は任意のprojective
cofibrantな順序図式のConst(R_0)→Rのcofibration性を抽出する。連続性・well-orderは不要。
`ProjectiveLeftProper`・`ColimitFromBottom`・`RelativeHomotopyColimit`は元の左固有性とUnder圏の
Ken Brownから、初期項のcofibrancyなしで連続cofibration列の実際のhocolim比較を証明する。
`LimitPrefix`・`ContinuousLocalEquivalences`は全てのlimit段階を含む帰納でW_S所属を証明する。
`LeftProperTransfinite`は(cof_C⊓W_S)と(I.rlp.llp⊓W_S)のpushout・任意のw-smallな超限合成閉性を
Smith用の実際の安定性クラスとして出力する。Sの小ささ・limit cofinalityの制限は要求しない。
共有入口2512 jobs、4155宣言・326モジュールの標準公理監査、17宣言・3モジュールのL3監査、
58宣言・8モジュールのrelative hocolim監査と関連回帰検証が成功。
コミット`31393aa7`・`7e206fe4`・`d87a386d`・`d473d792`。
L2の生成射・単位射のW_S所属、L4/L5、E0、S0〜S3、F1の任意モデル源の最終関手は継続中。


L2は計画§208で最終仕様（左固有combinatorial源）に対する受入検証まで完了。
`Smith/ClosedGeneratedClass`とReedyの`ClosedBoundaryClass`・`ClosedObjectwise`は、
必要な小さい生成族だけにSOAを適用し、閉クラス全体のaccessibilityやモデル構造を仮定せずReedy帰納を行う。
`LocalBoundaryEquivalences`は実際の相対境界生成族B(S)、K=J⊔B(S)、生成左クラス、
自然な単位射の元のcof_C∩W_S所属を証明する。元のSの射の両端のcofibrancyは不要。
`AccessibleLocalReplacement`はaccessibleな実際のRと局所同値なη:Id→Rを出力し、
W_S=R⁻¹(W_C)を通して元のW_Sの射圏部分圏と包含のaccessibilityを証明する。
単位射のW_S所属を入力とする条件付き定理のままで止めていない。
共有入口2517 jobs、4168宣言・331モジュールの標準公理監査、13宣言・5モジュールの新規監査と
L3・逆像判定の回帰検証が成功。コミット`8c218e21`・`7f6ecf6a`。
次はL4の実際のモデル構成。L5・E0・S0〜S3とF1の任意モデル源の最終関手も残る。


L4は計画§209で受入検証まで完了（2026-10-16）。`ModelExistence`はL2・L3とSmith存在定理から
同じC上の実際の局所化モデルを構成し、元のcofibration、元のRMapのW_S、(cof_C∩W_S).rlpという
三クラスの等式、小さい実際の生成族、cofibrantly generated構造を出力する。
fibrant対象は元のfibrantかつS局所と同値であり、既存の`IsLocalizationModel`証明書を充足する。
`LocalLeftProper`は任意のW_Sの射の元のcofibration沿いのpushoutを扱い、新モデルの左固有性へ接続。
A0から局所モデルのaccessibleな実際の両モデル分解も出力する。共有入口2519 jobs、
4199宣言・333モジュールの標準公理監査、新規31宣言・2モジュールの監査とL2/L3/判定の回帰検証が成功。
実装コミット`129ab547`。次はL5。その後E0、S0〜S3。F1の任意モデル源の最終関手も未完了。


L5進捗は計画§210（2026-10-16）。`ReplacementData`・`Replacement`は実際のaccessibleなL_Sと
cofibrationかつ局所同値の単位を出力し、W_S=L_S⁻¹(W_C)、局所対象の単位による判定、
二つの冪等化写像の元の弱同値性を証明する。`ReplacementHomotopy`は通常のHo(C)での
単位による射の延長の全単射と二つの冪等化写像の一致を証明する。
`ReplacementComparison`は実際の合成による自然な弱同値cospanとHo(C)への関手の自然同型、
S⊆Tに対する両順序の合成置換の比較を与える。`ModelComparison`は恒等left Quillen関手、
生成表示による三クラスの独立性、元のRMapの選択変更を扱う。
`Fibrations`は新モデルでの実際のfibrant replacementへの接続と局所対象間のfibration判定を証明。
共有入口2525 jobs、4258宣言・339モジュール、新規60宣言・6モジュールの標準公理監査が成功。
コミット`983c00a9`・`c0d2d94a`。L5の任意のQuillen随伴に対する普遍性と、局所化モデルを
源とする再局所化の比較は未完了。L5の完了とはせず、続いてE0、S0〜S3、F1の残項目へ進む。


L5は計画§211で受入検証まで完了（2026-10-16）。`Quillen/FibrantTesting`・`FibrantCriterion`は
通常モデル圏のfibrant対象間のfibrationによる一般Quillen判定を証明する。`QuillenCriterion`・
`QuillenLocalObjects`・`UniversalProperty`は任意の元のQuillen随伴について、指定QでのF(Qs)の
弱同値性、右随伴によるfibrant対象の局所性、局所モデルからのQuillen性を対応させる。
`AdjunctionWeakEquivalence`はHom宇宙を共通宇宙へliftして実際のHom随伴を運び、
`Quillen/DerivedMapTest`が任意の実際のLFでのSの可逆性という最終定式化へ接続する。
`Quillen/ModelOrder`・`Minimality`・`Iteration`は最小性から実際の反復局所化とS⊔T局所化の
三クラスの一致を証明。`IteratedExistence`は最初のモデルの生成族・左固有性・分解を用いて
一般存在定理を再適用し、二つの小さいS,Tだけから反復局所化の実在と合併モデルの証明書を出力する。
共有入口2537 jobs、4284宣言・351モジュールの標準公理監査、普遍性10宣言・5モジュール、
反復8宣言・4モジュール、一般判定8宣言・3モジュールと置換/L4の回帰検証が成功。
実装コミット`a630c8ce`・`491b8be6`・`1eaac9fa`。L0〜L5は最終仕様で完了。
次はE0、その後S0〜S3。F1の任意モデル源の指定関手的分解なしの最終関手も未完了で、全体目標は継続中。


E0進捗は計画§212（2026-10-16）。`EndpointBifunctor`・`BifunctorChangeModel`は生成cofibrationの
endpoint functorのQuillen性からpushout-product条件を導く。`Localization/Endofunctor`・
`Bifunctor`・`Enriched`はL5の普遍性を使い、Vの生成始域のcofibrancyと導来tensorのS適合から
局所SM7・cotensor条件を出力する。Cの生成始域のcofibrancyは不要で、各宇宙は独立。
`UnitChangeModel`・`MonoidalUnit`は元のunit replacementを移送し、unitのcofibrancyを要求しない。
`BifunctorSymmetrize`・`Localization/Monoidal`はbraidingとclosed構造から両変数の局所tensorと
別の単位公理を接続する。こちらには元の生成cofibrationの始域のcofibrancyとtensor適合を明示する。
共有入口2547 jobs、4294宣言・360モジュールの標準公理監査、豊穣8宣言・7モジュールと
monoidal 2宣言・2モジュールの検証が成功。実装コミット`f45273b8`・`ffdd8e23`。
E0全体は未完了。ordinary RMapとV内部Homの局所性の比較、作用の単位の条件の照合が残る。
L0〜L5は完了済み。S0〜S3、F1の任意モデル源の最終関手も未完了として維持する。


E0は計画§213で受入検証まで完了（2026-10-16）。`PullbackHomSource`・`Enriched/DerivedMapping`は
実際のV値の導来Homとfibrancy・不変性を証明する。`Enriched/UnitAxiom`は作用の単位を独立に明示し、
非cofibrantなunitも扱う。`UnitFrame`は実際のunit replacementのresolutionから普通のsource frameを構成。
`EnrichedTensorFrameHom`・`FrameTests`・`EnrichedTestComparison`と局所SM7から、`EnrichedDetection`が
ordinary RMapとV値derived Homの局所対象・局所同値の等式とfibrant判定を証明する。
`EnrichedExistence`は元の一般入力と明示的tensor/unit条件から実際のモデル、SM7、unit、V値の弱同値クラスを
同時に出力する。Vの指定分解は生成表示から構成し、Cの生成始域のcofibrancyは不要。
`MonoidalExistence`はmonoidal用の追加条件から実際の局所monoidal modelを出力し、unitのcofibrancyは不要。
共有入口2559 jobs、4349宣言・372モジュールの標準公理監査、検出52宣言・9モジュール、
豊穣存在2宣言・2モジュール、monoidal 3宣言・3モジュールとV=SSetの利用例が成功。
実装コミット`b993cb83`・`56ec7652`。次は一般C,KのS0〜S3。F1の任意モデル源の最終関手も未完了。


## 一般の自由・忘却随伴と評価によるS0基盤（2026-10-16）

`Smith/ConservativeAdjunction`はfaithful・同型反映・accessibleな右随伴に沿って、小さい強生成族を
自由対象へ移す。源の局所可呈示性、標的の局所小性・余完備性から標的の局所可呈示性を証明する。
`Monoidal/ModulePresentability`は、既存の自由加群随伴・余極限創出・同型反映を使い、
実際の`Mod C M`へ適用する。モデル構造・monoid axiom・cofibrancyは不要。
`Transfer/EvaluationLeftProper`は評価した生成射のcofibration性を生成左クラス全体へ拡張し、
各段で検出する弱同値の左固有性を移送する。共有入口は具体的なSpectraをimportしない。
共有入口2834 jobs、4356宣言・375モジュールの標準公理監査が成功。
適用先の一般対称スペクトルとS0受入条件は計画§214。実装`2c53a5b0`・`91c43b23`。


## 二つのsource frameによる射の局所化テスト（2026-10-16）

`Localization/FrameArrowTests.mappingTest_iff`は、射を覆う二つのReedy cofibrant source frameと
各次数で弱いaugmentationから、元のRMapテストを計算する。parallel-pair図式上の
`FrameOverFunctor`の自然な弱いcospanを使用し、大域的なframe familyへの延長を要求しない。
`Monoidal/CofibrantTensor.tensorRight_isLeftQuillen`はcofibrantな係数の場合を実際のbraidingで移送する。
共有入口2563 jobs、4359宣言・376モジュールの標準公理監査が成功。共有層はSpectraをimportしない。
実装`3c9a992b`。適用先のS1の進捗と残るΩ_K検出の接続は計画§215。


## fibrant対象間のresolution Homテストと小さい検出族（2026-10-16）

`Localization/FrameTargetTests`は実際のreplacement単位の弱いsquareから、frame-Homのtarget置換を外す。
`ResolutionHomGenerators.exists_small_cofibrant_resolution_generators`は、小さいcofibrant検出族を元のHom宇宙へ
移し、fibrant対象間の元の弱同値を実際のsource resolutionからのHomで検出する。
族の存在はCの局所可呈示性と生成表示から証明し、全ての指定source分解で機能する。
共有入口を含む最終ビルド2819 jobs、4363宣言・378モジュールの標準公理監査が成功。
L1生成族・段階2の回帰確認も成功。共有層はSpectraをimportしない。
実装`c2aaa9ee`。この適用によるS1全体の完成と受入条件は計画§216。


## 閉Hom交換と右随伴による局所Quillen判定（2026-10-16）

共有`CategoryTheory/Monoidal/InternalHomExchange`は内部curryingとbraidingから
[X,[K,Z]]≅[K,[X,Z]]を構成し、二重uncurry後の評価の式を証明する。モデル仮定は不要。
`Localization/Endofunctor.endofunctor_isLeftQuillen_of_rightAdjoint_local`は、
実際の右随伴による局所対象保存から、両側を局所化した左Quillen条件を導く。
共有入口はSpectraをimportしない。4368宣言・379モジュールの標準公理監査に成功。
実装`2bd07abf`。一般スペクトルの局所tensor適合性への適用でS2を完了し、詳細は計画§218。


## 導来合成・弱逆の自然変換とtensor逆元（2026-10-16）

`Quillen/DerivedComposition`はcofibrant対象上の比較から、左Quillen関手の合成の
左導来を実際の導来関手の合成で計算する。
`DerivedWeakInverse`はcofibrant対象上で弱同値になる二つの合成→恒等の自然変換から、
両導来合成の自然同型と実際の圏同値を構成する。指定関手的分解は不要で宇宙も独立。
`Monoidal/DerivedTensorInverse`はcofibrantなX,Y,単位と弱同値X⊗Y→単位から、
導来tensorの同値とtensor Yによる逆関手を構成する。
共有入口はSpectraをimportしない。共有受入26宣言・3モジュールと、
4394宣言・382モジュールの標準公理監査が成功。新規sorry・引用axiomなし。
実装`92bb2333`。一般スペクトルへの適用は計画§220。


## 標準区間の左Quillen像とgood cylinder（2026-10-16）

`HomotopyFunctionComplex/QuillenCylinder`は、源・標的のHom宇宙が独立な
左Quillen左随伴SSet→Dについて、実際のΔ[1]・両coface・codegeneracyの像から
good cylinderを構成する。標準Reedy frameとBrown補題を使い、cylinderを仮定しない。
同型に沿った基点対象の変更とgood性の保存も証明する。共有層はSpectraをimportしない。
4403宣言・383モジュールの標準公理監査に成功。実装`8e7ba3ca`。
スペクトルの円tensorの商への適用と残るhomotopy pushout比較は計画§221。


## 通常のhomotopy pushout懸垂とcylinder商の比較（2026-10-16）

`Pointed/CylinderCone`は任意の基点付きモデル圏で、good cylinderの一端を潰したconeが
弱同値で零となり、残る端点がcofibrationであると証明する。propernessや生成条件は不要。
`Pointed/HomotopySuspension`は0←X→0の実際のprojective homotopy colimitを関手化し、
弱同値の保存と任意の通常の局所化への降下を証明する。
左固有combinatorial圏では、cone spanを使う二本の弱同値からcylinder商との対象ごとの同型を構成。
共有入口はSpectraをimportしない。4465宣言・385モジュールの標準公理監査が成功。
実装`fa1869ce`。自然性と関手全体の比較は未完了で、詳細は計画§222。


## 通常の懸垂比較の自然性と局所化への降下（2026-10-16）

`Pointed/CylinderConeMap`と`Pointed/SuspensionNaturality`はcone・商の射を構成し、
通常のhomotopy pushout懸垂とgood cylinder商の比較同型の自然性を証明する。
`Quillen/CofibrantComparison`はcofibrant対象上の比較自然同型をホモトピー圏全体へ降ろす。
共有入口はSpectraをimportしない。4493宣言・388モジュールの標準公理監査が成功。
実装`c5230ffd`。スペクトルへの適用を含む完了条件は計画§223。


## 指定分解なしのresolution圏とHo(SSet)値の関手（2026-10-16）

`HomotopyFunctionComplex/ResolutionCategory`は任意モデル源の全cosimplicial resolutionを束ね、
元の任意の射の持ち上げを通常のモデル公理だけで構成する。
`ResolutionCategoryHom`は実際のHomのKan性・不変性・自然なπ₀比較を与える。
`ResolutionLiftIndependence`は同じ元の射の任意の持ち上げがHo(SSet)で同じ射を誘導すると証明する。
`LocalizedResolutionHom`と`LocalizedMappingBifunctor`はこの結果と通常の局所化の普遍性から、
Ho(C)ᵒᵖ→(Ho(C)→Ho(SSet))を構成し、各値に実際のKanなresolution Homを代表として与える。
関手的分解・局所可呈示性・豊穣構造を源に仮定しない。
新規108宣言・5モジュールと共有4601宣言・393モジュールの標準公理監査が成功。
実装`fcbefc75`・`a29026e2`。SSet値の厳密化はF1の残項目であり、詳細は計画§224。


## 持ち上げ選択の高次整合性を扱う空間（2026-10-16）

`HomotopyFunctionComplex/LiftSpace`はaugmented frameの実際のHom fiberを構成する。
Reedy cofibrant frameとtrivial fibrationに対して、一点へのprojectionがtrivial fibrationとなり、
任意のmonomorphismに沿う延長と全次元の境界充填を与える。
`ResolutionLiftSpace`は任意モデル源の二つのresolutionと元の射にこれを適用し、
厳密なliftからの点・二点間の実際の区間・Kan性・一点への局所化同型を証明する。
`LiftSpaceFunctor`は固定した基底の上でfiberの厳密な標的関手性とprojectionの自然性を与える。
源の指定関手的分解は不要。新規63宣言・3モジュールと共有4664宣言・396モジュールの
標準公理監査が成功。実装`37ac8bdd`、詳細は計画§225。
最終RMapへの作用・合成と厳密化はF1の残項目である。


## 高次liftの対角Homへの実作用と行ごとの比較（2026-10-16）

`HomotopyFunctionComplex/DiagonalFrame`と`DiagonalHomComposition`は二重cosimplicial対象の
対角と、Hom(A,B)×Hom(B,Z)→Hom(diag A,Z)という実際の単体的合成を構成する。
`LiftSpaceAction`と`ResolutionLiftAction`は§225のlift空間をこの合成へ接続し、
厳密なlift点での元のHom射との一致・parameterと標的の自然性・境界作用の延長を証明する。
`DiagonalMappingRows`は任意モデル源の実際の二重resolution Homについて行ごとの弱同値を与える。
`DiagonalMappingComparison`はその対角と対角Homを自然同型で結び、比較射が実際のaugmentationの
前合成であることを証明する。対角全体の弱同値性は別の残項目として維持する。
新規65宣言・6モジュールと共有4729宣言・402モジュールの標準公理監査が成功。
実装`316d627d`、詳細とF1の厳密化の残項目は計画§226。


## 全bisimplicial集合のReedy cofibrancyと対角随伴（2026-10-16）

`Simplicial/LatchingDegeneracies`と`LatchingMonomorphisms`はEilenberg–Zilberの共通細分から、
実際のsimplex-op latching colimitの比較が単射となることを証明する。
`BisimplicialCofibrancy`は評価とcolimit保存の同型を介して、任意のbisimplicial集合が
cof=monoを持つ実際のReedyモデルでcofibrantとなることを証明する。
`DiagonalAdjunction`は対角制限の実際の右Kan拡張随伴を構成し、`DiagonalCofibrations`は
Reedy cofibrationの保存を証明する。対角の左Quillen適合性と弱同値保存は引き続き残る。
新規26宣言・5モジュールと共有4755宣言・407モジュールの標準公理監査が成功。
実装`27b29ced`、次のmatching射の計算とF1の残項目は計画§227。


## 対角右随伴の標準単体internal Homによる具体化（2026-10-16）

`Simplicial/DiagonalRepresentables`は対角に制限したuliftCoyonedaをΔ[n]⊗Δ[m]と比較し、
実際の右Kan拡張右随伴の各単体をHom(Δ[n]⊗Δ[m],Z)として計算する。
`DiagonalInternalHom`は閉随伴と既存の標準単体Yoneda比較から、元の右随伴と
標準単体internal Homの族との自然同型を構成する。内側・外側の単体操作とZについて自然。
具体的なinternal Homを右随伴とする通常の対角随伴も構成し、比較を追加仮定に戻さない。
この結果にはモデル構造の入力は不要。新規30宣言・2モジュールと共有4785宣言・409モジュールの
標準公理監査が成功。実装`5fbc9855`。matching射・Quillen条件とF1の残項目は計画§228。


## 対角Quillen定理と実際のresolution Hom比較（2026-10-16）

共有`Reedy/IndexOppositeEquivalence`と`BoundaryHom`は境界indexの圏同値と、
反対向きlimit保存関手によるlatching/matching比較を与える。
`Simplicial/DiagonalMatching`・`DiagonalRelativeMatching`はmatching射を境界pullback-Hom射と
実際のarrow同型で結ぶ。`DiagonalQuillen`は既存SM7から対角のQuillen適合性を証明し、
全bisimplicial対象のReedy cofibrancyから、任意の行ごとの弱同値が対角でも弱同値となることを示す。
`HomotopyFunctionComplex/DiagonalMappingWeakEquivalence`はこれを§226の元のHom比較へ適用する。
源は任意モデル圏のまま、指定関手的分解・豊穣構造・対角sourceのcofibrancy仮定は不要。
新規90宣言・6モジュールと共有4875宣言・415モジュールの標準公理監査が成功。
実装`a73ee69d`・`5f020cfc`、残るKan置換とF1の厳密化は計画§229。


## 値側Kan置換と任意源の高次作用の接続（2026-10-16）

`Simplicial/KanReplacement`は標準生成定理から値側の関手的Kan置換Rとη:Id→Rを構成する。
`HomotopyFunctionComplex/KanLiftAction`は実際の対角HomをKan化し、元のresolution Homからの
自然な弱同値比較、標的の厳密な関手性・弱同値不変性、普通のHo(C)の射とのπ₀比較を与える。
元の高次lift作用をηへ後合成するため、Rの積保存は不要。指定した境界作用の延長も保持する。
源Cの関手的因子分解は仮定しない。源の恒等射・合成を含む厳密化はまだ残る。
新規31宣言・2モジュールと共有4906宣言・417モジュールの標準公理監査が成功。
実装`ed6bec42`・`9f15f1ab`、詳細と残項目は計画§230。


## 選択した源liftの恒等射・合成の区間比較（2026-10-16）

`HomotopyFunctionComplex/KanLiftCoherence`は、独立に選んだliftと実際のresolution射を
実際のlift空間内の区間で結び、元のHom全体に作用させる。lift(id)と恒等作用、lift(f≫g)と
反変順の合成作用が両端で厳密に一致し、区間族全体が標的について自然である。
任意のmono上の既定の境界からの延長も、全ての標的とHomについて一度に構成する。
源の指定関手的分解やKan置換の積保存は不要。一般の高次合成の整合性と源の厳密化は残る。
実装`0f170666`。区間比較の37宣言・2モジュール、共有4922宣言・418モジュールの
標準公理監査が成功。A0・A1の最終受入検証も成功。詳細とF1の残項目は計画§231。


## 全lift有限列の同時比較と三重合成の3単体（2026-10-16）

`Simplicial/VertexTuples`は頂点の順序付き有限列からなる実際の単体的集合と、頂点からのmonoを
与える。`HomotopyFunctionComplex/CoherentLiftTuples`は、固定した基底射上の全ての厳密なliftを
頂点として保持し、その全有限列から実際のlift空間への一つの単体写像を構成する。
面・退化を全次元で保ち、標的について自然に元のHomへ作用する。同じ厳密なliftの繰り返しは
元の作用に厳密に一致する。三重合成の四つのlift式から実際の3単体と整合する面を構成した。
異なる基底射間の合成との適合性とF1の厳密化は残る。詳細は計画§232。
実装`eaa95550`。新規49宣言・2モジュールと共有4971宣言・420モジュールの標準公理監査が成功。


## 高次lift族の後合成と実際の作用の両立（2026-10-16）

`HomotopyFunctionComplex/ResolutionLiftPostcomposition`は厳密なresolution射gによって、
Lift(X,Y;f)をLift(X,W;f≫g.base)へ送る実際の単体写像を構成する。既定の境界を保持し、
厳密なlift点を実際の合成の点へ送る。全次元のlift族への作用は、元のHomのgによる前合成と
厳密に一致し、Kan化した作用でも同じ等式を満たす。源の関手的分解は入力しない。
源側の前合成・選択した比較族間の高次整合性・F1の厳密化は残る。詳細は計画§233。
実装`259e43be`。後合成の30宣言・2モジュールと共有4989宣言・421モジュールの監査が成功。


## 外側frameによる源写像とKan作用・局所化π₀（2026-10-16）

`HomotopyFunctionComplex/LiftSpacePrecomposition`は、モデル構造なしの増大付き図式の射から
実際のlift空間の前合成を構成する。`ResolutionLiftPrecomposition`は任意のモデル源で外側の
frame写像を実際に持ち上げ、その前合成と既存KanTarget族上の源写像を構成する。
元のHomの比較正方形、全parameterの作用、標的自然性、源の弱同値不変性を証明し、π₀では
独立宇宙の通常の局所化の前合成と一致する。実際のframe写像の恒等・合成則も保持する。
選択した外側liftの高次整合性とF1の厳密化は残る。詳細は計画§234。
実装`9b98c444`。前合成の55宣言・3モジュール、共有5031宣言・423モジュールの監査が成功。


## 固定境界付き比較空間と前後合成の相対ホモトピー（2026-10-16）

`Simplicial/RelativeChoiceSpace`は、mono V→Tと可縮fibrantなPへの固定境界bから、制限写像
[T,P]→[V,P]の実際のfiberを構成する。既存SM7からその点への射のtrivial fibration性・Kan性と
全次元の境界充填を証明し、評価した族T⊗K→PがV⊗K上でbを固定することを示す。
`HomotopyFunctionComplex/CoherentLiftRelative`は、選択済みinterpolationの前後合成と、
合成した厳密なliftの選択済みinterpolationとを、全てのstrict-lift頂点上で固定した相対
ホモトピーで結ぶ。比較空間には既定の高次境界の充填性もある。
全多重合成の境界の再帰的構成とF1の厳密化は残る。実装`dfe2314d`、詳細は計画§235。
関連107宣言・3モジュール、共有5120宣言・425モジュールの標準公理監査が成功。


## 指定した比較面の貼り合わせと相対充填（2026-10-16）

`Simplicial/BoundaryGluing`は実際のfacet上の比較と交わりの一致条件から境界を構成する。
一般の被覆の添字宇宙は独立で、モデル構造は不要。通常の単体的面恒等式から標準境界を
貼り合わせるAPIも提供する。`RelativeChoiceBoundary`は指定した全ての面を保つ充填と、
評価族の固定境界を保持する。`HomotopyFunctionComplex/CoherentLiftFaces`は前後合成の
相対比較空間へ適用する。三辺を指定した充填のKan作用での各辺の一致も検証済み。
全多重合成の面データの整合した構成とF1の厳密化は残る。詳細は計画§236。
実装`1ff62113`。新規39宣言・3モジュール、共有5159宣言・428モジュールの監査が成功。


## lift移送の厳密な法則と選択済み比較区間（2026-10-16）

`HomotopyFunctionComplex/ResolutionLiftFunctorLaws`は、添字の基底射の等式移送を明示し、
実際の前後合成の恒等・合成・交換則を証明する。`Simplicial/RelativeChoiceMaps`は、既定の
比較面を保ったまま相対選択空間を前後へ移し、評価した全parameter族が元の移送と厳密に
一致することを示す。この共有部分はモデル構造不要。
`CoherentLiftEdges`は前後合成の選択済み比較parameterを実際の相対選択空間内に保持し、
両端が指定の延長の点に一致する公式を与える。全多重合成の整合性とF1の厳密化は残る。
実装`0c8eb6c8`、詳細は計画§237。新規75宣言・3モジュール、共有5234宣言・431モジュールの
標準公理監査と回帰確認が成功。


## 選択済み後合成比較の具体的な三角形（2026-10-16）

`HomotopyFunctionComplex/CoherentLiftBaseChange`はlift有限列の基底移送と選択済みinterpolationの
可換性を与える。`CoherentLiftPostComposition`は連続する厳密なresolution射g,hについて、
選択済みpostEdge(g)、postEdge(h)の実際の移送と、選択済みの直接のpostEdge(g≫h)から
三角形の境界を構成する。端点から面恒等式を証明し、三辺を保持する実際の2単体を充填した。
全てのstrict-lift頂点は全体で固定され、Kan作用も各辺の以前の作用に厳密に制限される。
前合成・混合比較・単位・全次元の整合性とF1の厳密化は残る。詳細は計画§238。
実装`dbc9096b`。関連69宣言・3モジュール、共有5278宣言・433モジュールの監査が成功。


## 選択済み前合成比較の三角形（2026-10-16）

`HomotopyFunctionComplex/CoherentLiftPreComposition`は二つの実際のFrameMapについて、選択済み
preEdgeの移送と、実際の合成に対する直接のpreEdgeから三角形の境界を構成する。
基底射の結合則の移送を明示し、端点から面恒等式を証明して、選択済み三辺を保持する
実際の2単体を充填した。厳密なlift頂点は全体で固定され、Kan作用も各辺で元の作用に一致する。
混合比較・単位・全次元の整合性とF1の厳密化は残る。詳細は計画§239。
実装`a5839204`。関連67宣言・2モジュール、共有5318宣言・434モジュールの標準公理監査が成功。


## 選択済み四辺を保持する混合比較（2026-10-16）

`HomotopyFunctionComplex/CoherentLiftMixedFamilies`は前後合成の四つの族を共通の固定境界へ
そろえる。`CoherentLiftMixedComparison`は以前の二つのpreEdge・二つのpostEdgeを移し、
端点の一致を証明して、共通対角線を持つ二つの実際の2単体で両経路を結ぶ。
`Simplicial/SelectedTriangle`は指定された辺と端点からの相対充填を共有する。
四辺と対角線の制限、全体でのstrict-lift頂点の固定、各辺のKan作用を検証済み。
単位・全次元の整合性とF1の厳密化は残る。実装`270ce23f`、詳細は計画§240。
関連108宣言・3モジュール、共有5426宣言・437モジュールの標準公理監査と回帰確認が成功。


## 選択済み単位比較と標準退化の比較（2026-10-16）

`HomotopyFunctionComplex/CoherentLiftUnitFamilies`は実際の恒等射・恒等FrameMapによる
比較の両端を元のinterpolationへ同定する。`CoherentLiftUnitComparison`は、以前の
選択済み単位区間を一辺に保持し、残り二辺が頂点の実際の標準退化となる2単体を構成する。
共有`Simplicial/SelectedLoopContraction`はこの相対充填を提供する。
全体でのstrict-lift頂点の固定と各面のKan作用を検証済み。源の指定関手的分解は要求しない。
選択区間の厳密な退化への正規化、全次元の整合性、F1の最終的な厳密化は残る。
実装`a6a9a53c`、詳細は計画§241。関連43宣言・3モジュール、共有5469宣言・440モジュールの
標準公理監査と回帰確認が成功。


## 部分的な比較族を保持する全骨格の再帰延長（2026-10-16）

共有`CategoryTheory/Limits/SequentialExtension`は、各段で直前の射を延長し、全選択を保持する
余極限上の射を構成する。`Simplicial/RecursiveChoiceExtension`は実際の単射の骨格へ適用し、
固定境界付き相対選択空間への部分写像を、全次元で整合する一つの単体写像へ延長する。
各有限単体は対応する有限段階の実際の選択に一致し、評価した族とKan作用も元の部分族を保持する。
全多重合成から互換な部分写像を構成することと、F1の最終的な厳密化・比較は残る。
実装`fe7468c4`、詳細は計画§242。新規45宣言・2モジュール、共有5514宣言・442モジュールの
標準公理監査と単位比較の回帰確認が成功。


## 指定比較単体の骨格への組み立てと保持（2026-10-16）

`Simplicial/SkeletalCellGluing`は各非退化単体の境界一致から実際の骨格pushoutで写像を作り、
前段と指定した全単体を保持する。通常の各面の式で境界一致を証明でき、付加面の互換性は
前段の写像から導かれる。全骨格の再帰後も、初期部分に境界を持つ指定単体の保持を証明した。
`RelativeChoiceCells`は通常のモデル公理から全付加境界の充填系を構成し、固定頂点と
元の部分族へのKan作用の制限を保つ。全多重合成のパラメータ構成とF1の厳密化・比較は残る。
実装`0592c60b`、詳細は計画§243。関連85宣言・3モジュール、共有5564宣言・444モジュールの
標準公理監査と再帰延長・単位比較の回帰確認が成功。


## 有限合成列の全切断比較を保持するKanパラメータ（2026-10-16）

`HomotopyFunctionComplex/PostCompositionChain`は任意長の厳密なresolution射の合成列について、
各prefix/suffixの既存比較三角形を共通の相対選択空間へ移す。全三角形は同じ直接比較辺を共有する。
共有`Simplicial/TriangleBook`のpushoutで全切断比較を貼り合わせ、`PostChainKanParameter`で
その全体を値側の実際のKanパラメータへ延長する。各三角形・三辺・共有辺を厳密に保持し、
固定頂点と全標的へのKan作用を検証した。源の指定関手的分解は要求しない。
全括弧付け、列の再添字付け、前合成・混合比較の同時整合性とF1の最終厳密化・比較は残る。
実装`d612fe0b`、詳細は計画§244。関連87宣言・4モジュール、共有5641宣言・447モジュールの
標準公理監査と骨格構成・後合成三角形の回帰確認が成功。


## 切断ラベルの再添字付けと相対比較（2026-10-16）

`Simplicial/TriangleBookMaps`は共有辺付き三角形パラメータの再添字写像を厳密な恒等・合成則で構成する。
`KanTriangleFamily`は値側Kanパラメータの写像と、独立に選んだ延長間の実際のホモトピーを与える。
このホモトピーは元の三角形族全体を区間全体で固定する。`PostChainReindexing`は固定した有限列の
切断位置の選択・反復へ適用し、元の全切断比較を定義的に回復する。評価したstrict-lift頂点も固定する。
列そのものの面・退化、比較の高次整合性、前合成・混合比較とF1の厳密化・最終比較は残る。
実装`462a22b3`、詳細は計画§245。新規46宣言・3モジュール、共有5687宣言・450モジュールの
標準公理監査と全切断比較の回帰確認が成功。


## 合成列自体の面・退化と比較族の適合性（2026-10-16）

共有`CategoryTheory/AnchoredChain`は前後の射で外部端点と全体の射を固定した有限列を扱う。
任意の単調写像で内部の図式を変更し、列の厳密な恒等・合成則と各切断の実際の因子分解の一致を証明する。
`AnchoredChainSimplicial`は対象/Hom宇宙の最大内で列の実際の単体集合を構成する。
`HomotopyFunctionComplex/AnchoredPostComparison`は既存三角形と共有辺付き族の再添字付けを厳密に同定し、
独立に選んだKan延長間を、変更後の比較族全体を固定するホモトピーで結ぶ。通常の有限列の元の三角形も回復する。
比較ホモトピーの全高次整合性、全括弧付け、前合成・混合比較、F1の厳密化・最終比較は残る。
実装`05ef2e5d`、詳細は計画§246。新規93宣言・3モジュール、共有5780宣言・453モジュールの
標準公理監査と切断再添字付け・全切断比較の回帰確認が成功。


## 全合成列と因子分解圏のnerveの同定（2026-10-16）

共有`CategoryTheory/ArrowFactorizationCategory`は固定射の実際の因子分解圏を構成し、始対象・終対象と
それらの定値関手と恒等関手を結ぶ自然変換を与える。`AnchoredChainNerve`は図式との両逆と
全単体写像との自然性から、前後の脚を持つ全合成列の単体集合との実際の単体同型を構成する。
索引用の宇宙は対象/Hom宇宙の最大であり、源のモデル構造は一般層に要求しない。
`AnchoredPostComparison.fromDiagram_triangle`は既存の選択済み三角形をこの同定で保持する。
Kan比較の全高次整合性、前合成・混合比較、F1の厳密化・最終比較は残る。
実装`a146445e`、詳細は計画§247。関連120宣言・3モジュール、共有5869宣言・455モジュールの
標準公理監査と列の面・退化比較の回帰確認が成功。


## 全合成列パラメータの単体的収縮（2026-10-16）

共有`CategoryTheory/NerveHomotopy`は自然変換から実際のnerve間のSSet.Homotopyを構成し、
両端と全単体写像の自然性を証明する。`AnchoredChainContraction`は因子分解圏の始対象からの
自然変換へ適用し、前回のnerve同型を通して全合成列の索引単体集合の収縮を与える。
点への写像・基点・点上の厳密な逆の式と、逆側の合成から恒等写像への一つの単体的ホモトピーを持つ。
モデル構造や源の指定関手的分解は要求しない。選択済みKan比較の高次整合系への接続とF1の厳密化・比較は残る。
実装`cc1a202b`、詳細は計画§248。新規28宣言・2モジュール、共有5897宣言・457モジュールの
標準公理監査と因子分解nerveの回帰確認が成功。


## 全因子分解列に一度だけ構成する比較族（2026-10-16）

`Simplicial/UniverseLiftFillers`は既存の宇宙移送APIで小さい有限境界充填を持ち上げる。
`LargeParameterExtension`は大きい宇宙のモデル構造を仮定せず、任意の大きい単射に沿って骨格延長する。
共有`CategoryTheory/NerveVertices`の単射を使い、`AllFactorizationComparison`は固定f,gの全因子分解nerveで
一つの比較族を作る。既存の因子分解点を頂点に保持し、各有限列で元のHom宇宙内の単体写像を取り出す。
全ての面・退化、固定strict-lift頂点、全標的へのKan作用が同じ選択から厳密に整合する。
旧選択の辺・三角形との比較、外部の射を変える前後合成との同時適合性、F1の厳密化・最終比較は残る。
実装`bfdca7e4`、詳細は計画§249。新規57宣言・4モジュール、共有5954宣言・461モジュールの
標準公理監査と因子分解nerveの回帰確認が成功。


## 全列の外部移送と全体的な後合成比較（2026-10-16）

共有`CategoryTheory/ArrowFactorizationTransport`は実際の外部前後合成を構成し、中間対象・射を保つ。
`AnchoredChainTransport`は全列の単体写像へ移し、単位・合成・前後交換と中間図式の保持を厳密に証明する。
`Simplicial/LargeParameterHomotopy`は小さい有限境界充填だけから大きいパラメータ上のホモトピーを作る。
`AllFactorizationPost`は、新しい全体射の族を移送したものと、元の族を実際のliftの後合成で送ったものを、
一つのホモトピーで結ぶ。各有限値は元のHom宇宙内にあり、全strict-lift頂点を固定する。
値の前合成・混合比較、ホモトピーの高次整合性とF1の厳密化・最終比較は残る。
実装`f34b16b8`、詳細は計画§250。新規70宣言・4モジュール、共有6024宣言・465モジュールの
標準公理監査と全因子分解比較の回帰確認が成功。


## 全列上の源側前合成と全次元の写像空間充填（2026-10-16）

`AllFactorizationPre`は実際のFrameMapによる前合成を全因子分解列上の一つのホモトピーへ移す。
新しいbase射の族と元の族を既存のmixed相対選択空間で比較し、両端、全θでの自然性、
有限値が元のHom宇宙内にあることと全strict-lift頂点の固定を証明する。
`Simplicial/LargeParameterMapping`は小さいPの有限境界充填から、大きいKについて
内部Hom(K,ulift(P))の全次元境界充填を構成する。指定した全ての面をK全体上の写像として保持する。
大きい宇宙のモデル構造や源の関手的分解を追加しない。実際の前後合成ホモトピーを貼り合わせる
混合比較と全高次整合性、F1の厳密化・最終比較は残る。
実装`b2a1d411`、詳細は計画§251。新規18宣言・2モジュール、共有6042宣言・467モジュールの
標準公理監査、A0/A1の最終入口と外部移送の回帰確認が成功。


## 選択済みの四つの全体比較を保持する混合正方形（2026-10-16）

`AllFactorizationMixedTransport`は全体的な源側前合成の相対選択空間を標的側で移送し、
既存のmapAC/mapBDとfirstMapの正方形が実際の単体写像として可換であることを証明する。
共有`Simplicial/LargeParameterSquare`は小さい境界充填だけから、大きいパラメータK上の
指定済み四ホモトピーを保持する二つの三角形を作り、共通の対角辺を持たせる。
`AllFactorizationMixed`は全列パラメータへ適用し、既存の前合成・後合成ホモトピーそのものを
四辺に保持する。有限値の小さい宇宙、全θでの自然性、全strict-lift頂点の固定も証明する。
任意モデル源を維持する。単位・多重外部合成の全高次整合性、旧選択との比較、F1の厳密化・最終比較は残る。
実装`561db7ce`、詳細は計画§252。新規101宣言・3モジュール、共有6143宣言・470モジュールの
標準公理監査と前合成・外部移送の回帰確認が成功。


## 実際のFrameMapの圏と任意長の厳密な合成図式（2026-10-16）

`FramedResolutionCategory`は内側のresolution射と実際のFrameMapを記録する圏を構成する。
通常のモデル公理から全ての基底射を持ち上げ、forgetと基底射影のfullnessを証明する。
`FramedMappingBifunctor`はこの圏の反対圏からC→SSet[v]への厳密Kan二変数関手を構成し、
元のresolution Homとの自然比較、fibrant標的での両変数不変性、π₀の両変数自然性を証明する。
`FramedResolutionChains`は任意長の隣接FrameMapを保持して合成列を持ち上げ、元の図式との一致、
全次数のnerve全射性、実際の列の再添字付けと合成則を証明する。
`FramedMappingLocalization`は空間の局所化後の二変数自然同型と、同じ基底射の完全な作用の一致を示す。
任意モデル源を維持する。独立な列のliftの全高次整合性、任意標的へのSSet値拡張、
最終C上の厳密化と最終比較は残る。実装`00bdacac`、詳細は計画§253。
新規118宣言・4モジュール、共有6261宣言・474モジュールの標準公理監査と混合比較の回帰確認が成功。


## 全比較系の相対選択空間と動く頂点の持ち上げ（2026-10-16）

`Simplicial/LargeParameterRelativeChoice`は小さいPの有限境界充填から、任意の大きい単射に
相対的な選択空間の全次元延長を証明する。大きい宇宙のモデル構造は要求しない。
固定した部分データを保つホモトピー、全パラメータ族の比較、動く境界と既指定全体族を
ともに保持するfamily_liftingを供給する。
`AllFactorizationChoices`は全因子分解nerve上のcoherentな比較系の空間と普遍評価を構成する。
既存の選択を点として保持し、その空間全体の一つの収縮と、元の因子分解点を固定する評価を証明する。
別の全体族との比較、元のHom宇宙内の有限値・全θの自然性、動く頂点の延長も供給する。
外部合成列の全整合性、旧独立選択との接続、任意標的へのSSet値拡張と最終厳密化・比較は残る。
実装`515511d5`・`2951a1d3`、詳細は計画§254。新規55宣言・2モジュール、既存変更を含む
対象78宣言・3モジュール、共有6316宣言・476モジュールの標準公理監査と関連回帰確認が成功。


## 因子分解点を固定する後合成比較と全後合成文脈の関手（2026-10-16）

`AllFactorizationPostPoints`は元の因子分解点が既存firstMapで厳密に後合成されることを証明する。
`AllFactorizationPostRelative`は全因子分解点を固定する全列上のホモトピーを構成する。
共有`Simplicial/HomotopyEndpointComparison`で旧比較と新比較を実際の両面に保持し、
その両端の全体族を固定する。大きい宇宙のモデル構造は要求しない。
`PostChoiceFunctor`は全後合成文脈Under(Y)上の小さいSSet値の厳密関手を構成し、
元のfirstMap・等式移送との一致、単位・任意合成、自然なpostLeftPointとprojectionを証明する。
projectionは成分ごとに自明fibration、pointは弱同値である。
源側前合成まで含む全整合系、全列比較族の文脈図式への接続、最終RMapの厳密化・比較は残る。
実装`25a7578e`、詳細は計画§255。新規56宣言・4モジュール、共有6372宣言・480モジュールの
標準公理監査と混合比較・相対選択空間の回帰確認が成功。


## 相対選択の一般図式化とFrameMap付き前合成文脈（2026-10-16）

共有`Simplicial/RelativeChoiceFunctor`は任意のD→SSetと自然な固定境界から相対選択空間の
厳密関手を構成する。自然な全体延長からpointとprojectionを作り、point≫projection=idを示す。
モデル構造や境界の単射性はこの通常の圏論層には不要である。
`FramedPreChoiceFunctor`は実際のFrameMap付き対象YへのOver圏の反対圏に適用する。
元のlift空間の全射での厳密合成と既存前合成＋baseChangeとの一致を証明し、
既存preChoiceSpaceとpreLeftPointを値・自然な点とする小さいSSet値の厳密図式を構成する。
projectionは成分ごとに自明fibration、pointは弱同値である。任意モデル源を維持する。
混合文脈の図式、既選択比較族の全整合性、最終C上のRMapの厳密化・比較は残る。
実装`f975a211`、詳細は計画§256。新規47宣言・2モジュール、共有6419宣言・482モジュールの
標準公理監査と後合成文脈・framed二変数関手の回帰確認が成功。


## 前後合成の混合文脈と実際のfiber図式（2026-10-16）

共有`Simplicial/FiberFunctor`は任意の自然変換と自然な点から実際のpullback fiberの厳密関手を
構成し、指定点上の自然な族をfiberへ持ち上げる。モデル構造は不要である。
`MixedChoiceFunctor`は実際のFrameMap付きOver圏の反対圏とresolutionのUnder圏の積へ適用する。
各fiberを元のResolutionLiftSpaceとprojectionを保つ実際の同型で結び、前後移送の厳密交換則を示す。
根の全lift族・固定頂点を運ぶ自然変換と相対選択空間の厳密関手を構成した。
自然なpoint・projectionとpoint≫projection=idがあり、成分の自明fibration性・弱同値性も証明する。
任意モデル源と小さいSSet値を維持する。旧独立比較族の全整合性、基底Cへの降下、最終RMapは残る。
実装`7c8e969c`、詳細は計画§257。新規63宣言・2モジュール、共有6482宣言・484モジュールの
標準公理監査と前後合成の各文脈関手の回帰確認が成功。
