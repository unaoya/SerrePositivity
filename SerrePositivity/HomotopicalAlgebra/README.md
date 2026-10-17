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


## 旧混合比較と全列族の厳密文脈図式への接続（2026-10-16）

共有`Simplicial/RelativeChoiceIso`は境界を保つ標的同型から実際の選択空間同型を作り、
全パラメータ族の評価と指定延長を保つ。モデル構造は不要。
`MixedChoiceCompatibility`は根のlift族が元の後合成→前合成そのものと示し、元の混合space・
familyA・固定境界へ接続する。元のspaceを値とする厳密関手、自然同型、自然な既存pointAを得る。
旧三角形を全ての面・共有対角線ごと保持する。
`AllFactorizationMixedContext`は全因子分解列の既選択の混合正方形を族全体のまま接続し、
元の四つの全体的ホモトピー・共有対角線・全面退化を保持する。有限単体の値は元の小さいSSet。
全外部合成列の相対高次整合性、基底Cへの降下、最終RMapと最終比較は残る。
実装`1972260f`、詳細は計画§258。新規56宣言・3モジュール、共有6538宣言・487モジュールの
標準公理監査と混合文脈図式・全列混合比較の回帰確認が成功。


## 全合成列の動く終点評価と要素圏の一般Reedy構造（2026-10-16）

共有`Reedy/Elements`は任意のReedy圏とType値関手から実際の要素圏のReedy構造を構成する。
中間要素を左射の像で定義し、射影の充満性・対象上単射性を仮定せず分解の一意性を証明する。
`CategoryTheory/NerveSimplexEndpoint`は実際のnerve単体圏から元の圏への終点評価関手を構成する。
終点を削る面は列の実際の末尾の射を用い、全作用素の合成則がある。
`Simplicial/NerveCoherentFamily`は単体圏のReedy構造と、退化が終点で同型になることを示す。
小さい単体パラメータから終点の値への自然変換として全面・退化の整合系を定義し、
既存の自然なpointAから全外部文脈列の基準系を得る。源・値の宇宙は独立。
既選択の独立比較を保つ相対Reedy延長、基底Cへの降下、最終RMapと最終比較は残る。
次は各境界索引の有限性とlatching境界包含の同定を証明する。
実装`1de52e9a`、詳細は計画§259。新規63宣言・3モジュール、共有6601宣言・490モジュールの
標準公理監査、混合比較とReedyモデル圏の回帰確認が成功。


## 大きい単体圏の有限Reedy境界と小さい値域（2026-10-16）

`Reedy/ElementsFinite`は要素圏のmatching索引を底圏へ単射で符号化し、
direct射の像の単射性の下ではlatching索引も同様に扱う。有限性とHomの有限性を移す。
`Simplicial/SimplexIndexFinite`は任意サイズの単体集合Xに適用し、X.Elementsᵒᵖの
各latching/matching索引とHomの有限性を証明する。全射な単体作用素の分裂性を使う。
対象・射の異なる宇宙を保ち、ULiftHomによる有限圏の提示と圏同値を経由して、
独立した値域の有限極限・有限余極限だけから元の境界索引での存在を供給する。
大きいnerveでも小さいSSet値域内で境界を構成でき、一般Reedy持ち上げ定理に接続できる。
次はlatching写像の境界包含との同定、値のmatchingの計算と相対延長。
基底Cへの降下、最終RMapと最終比較は引き続き残る。
実装`c5b8792f`、詳細は計画§260。新規36宣言・2モジュール、共有6637宣言・492モジュールの
標準公理監査とnerve整合系・Reedyモデル圏の回帰確認が成功。


## 実際のlatching境界包含と全列パラメータのReedy cofibrancy（2026-10-16）

`Reedy/ElementsMatchingEquivalence`は要素圏のmatching索引と底圏のmatching索引を圏同値で結び、
反対圏のlatching索引についても実際の三角形とsource図式を保つ圏同値を構成する。
`Simplicial/SimplexLatchingBoundary`は任意サイズのXの単体圏上で、標準単体パラメータの
latching余極限を標準境界と同型にし、比較写像を境界包含そのものと同定する。
独立したSSet値の宇宙を保つ。Arrow同型・単射性・明示したSSetモデルでのReedy cofibrancyを得る。
nerveの場合は既存のNerveCoherentFamily.simplicesそのものであり、自然な持ち上げの左条件を
仮定として残さず証明した。次は値図式のmatching条件と相対延長。
既選択系の全外部合成列への組立て、基底Cへの降下、最終RMapと最終比較は残る。
実装`95d8d9bb`、詳細は計画§261。新規90宣言・2モジュール、共有6727宣言・494モジュールの
標準公理監査と有限境界・nerve整合系の回帰確認が成功。


## 逆境界の終対象・値のmatching条件・全合成列の相対延長（2026-10-16）

`Simplicial/SimplexMatchingTerminal`は任意のXの非空matching索引に、非退化核による実際の終対象を
構成する。全逆商からの射の存在・一意性を証明し、逆射を同型に送る値図式のmatching比較を同型にする。
`SimplexInverseMatching`は空境界と非空境界を計算し、各値の点射の自明fibration性から、
自然な点射のReedy右条件を導出する。対象の小ささや大きい積・モデルは要求しない。
`NerveCoherentExtension`は自然な点の選択を入力せず、全合成列の一つの整合系を構成する。
Reedy cofibrationで指定された部分自然系は、自然変換・各成分の等式として保持して延長できる。
既存の独立比較を部分系へ組み立てることと、その包含のcofibrancyは次の課題。
基底Cへの降下、最終の厳密RMapと最終比較は引き続き残る。
実装`4dca7af7`、詳細は計画§262。新規73宣言・3モジュール、共有6800宣言・497モジュールの
標準公理監査とlatching境界・混合比較の回帰確認が成功。


## 指定した低次数系と独立な比較点を保持する全整合系（2026-10-16）

`Reedy/RelativeLifting`は任意次数までの既存の自然な持ち上げから再帰を開始し、
全体の制限が元の系と厳密に一致することを証明する。
`Simplicial/NerveLowerExtension`はこれを低次数の全合成列・全面・退化の系に適用する。
与えたLowerSystemを、追加の部分包含cofibrancy仮定なしに全次数へ延長できる。
任意に指定した対象ごとの点も次数0の自然系へ組み立て、全て固定して延長する。
元の混合spaceの既存pointBを各文脈でそのまま保持する受入例も検証した。
既存の独立な辺・三角形は、単位・退化を含む低次数自然性を確認してから接続する。
基底Cへの降下、最終の厳密RMapと最終比較は引き続き残る。
実装`9dc93b11`、詳細は計画§263。新規45宣言・2モジュール、共有6845宣言・499モジュールの
標準公理監査と相対整合延長・混合比較の回帰確認が成功。


## 局所的な面・退化条件から指定単体を全整合系へ組み立てる入口（2026-10-16）

`Reedy/PrescribedLowerStep`は新次数の指定射と、旧系に対する入射direct・出射inverseの可換式から、
新次数同士の射も含む全自然性を導く。旧部分系と全指定成分は厳密に保持する。
モデル構造・極限・次数の単射性・索引の小ささは不要である。
`Simplicial/NervePrescribedCells`は指定辺・三角形・高次単体を同じ入口で組み立て、全次数へ延長する。
独立に指定した点→局所条件付きの辺→局所条件付きの三角形を組み立て、全体延長が三層を
同時に保持する受入例が成功した。単位・退化条件もデータに含む。
具体的な旧比較の局所条件との接続、基底Cへの降下、最終RMapと最終比較は残る。
実装`c9d850e6`、詳細は計画§264。新規38宣言・2モジュール、共有6883宣言・501モジュールの
標準公理監査と低次数保持・相対整合延長の回帰確認が成功。


## 比較パラメータ全体と整合した境界を保持する相対延長（2026-10-16）

`SimplexNaturalMatching`はinverse射を同型へ送る二つの図式の間の成分ごとの自明fibrationから、
相対matching射の自明fibration性を導く。終点が点であるという制限を外した。
`NerveRelativeValueExtension`は全次数で指定した値側の系と適合する低次数持ち上げを厳密に保持する。
`NerveParameterExtension`はmono A→Kのcotensor制限へ適用し、整合したA境界を全次数で固定する。
対象ごとに独立指定したK→F(d)も全写像の等式として保持する。
実際の旧edgeABを保持する例は、互換な整合した∂Δ1境界系を入力として検証した。
この境界系の構成と旧端点式からの適合性、基底Cへの降下、最終RMapと最終比較は残る。
実装`3d6feb1b`、詳細は計画§265。新規42宣言・3モジュール、共有6925宣言・504モジュールの
標準公理監査と指定単体組立て・相対整合延長の回帰確認が成功。


## 端点整合系からの境界構成と旧混合4辺の同時保持（2026-10-16）

`BoundaryOneCotensor`は実際の∂Δ1の余積表示をtensorで移送し、cotensor写像の貼り合わせと一意性を示す。
`NerveIntervalBoundary`は二つの全端点整合系から境界系を構成し、旧区間の端点式から低次数適合性を導く。
全外部次数で両端点系を固定し、各対象で元の区間写像全体を回収する。
`betweenChosen`は指定点から端点系を先に選び、互換境界を追加仮定せず延長する。
`MixedChoiceCoherentIntervals`は実際の旧pointA・B・C・Dから共有端点系を選び、
旧edgeAB・BD・AC・CDを全て保持する。共有頂点では全端点整合系そのものが同じである。
旧三角形と共有対角線の全境界接続、基底Cへの降下、最終RMapと最終比較は残る。
実装`78b8b659`、詳細は計画§266。新規110宣言・3モジュール、共有7035宣言・507モジュールの
標準公理監査とパラメータ相対延長・指定単体組立ての回帰確認が成功。


## 一般の全境界貼り合わせと旧混合三角形・共有対角線の保持（2026-10-16）

`BoundaryCotensor`はパラメータの交換と実際の標準境界貼り合わせにより、任意次元の
cotensorへの全facet写像を貼り合わせ、制限式と一意性を示す。
`NerveBoundaryExtension`はcodimension 2で互換な全facet整合系から全境界系を構成し、
旧高次写像全体と全facet系を同時に保持する。
`MixedChoiceCoherentIntervals`に旧対角線ADを追加し、同じA・D端点系を使用する。
`MixedChoiceCoherentTriangles`は実際の旧三角形二つを全外部次数へ延長し、
4辺と共有対角線の全整合系を固定する。各文脈で元の三角形写像全体を厳密に回収する。
全因子分解パラメータへの接続、基底Cへの降下、最終RMapと最終比較は残る。
実装`79fe1764`、詳細は計画§267。新規・更新146宣言・5モジュール、共有7085宣言・510モジュールの
標準公理監査と区間境界・パラメータ相対延長の回帰確認が成功。


## 全因子分解の大きいパラメータ全体を保持する外部整合系（2026-10-16）

`SimplexMonomorphismLifting`・`NerveMonomorphismLifting`は、全monoに対する右持ち上げ性から、
値側モデル構造なしに相対外部Reedy持ち上げを構成する。
`BoundaryFillerLifting`・`NerveFillerExtension`は有限境界充填をこの一般層へ接続する。
`NerveLargeParameter`は元の小さい値の境界充填のみから、大きいKの写像全体を保持する整合系を構成する。
整合した大きい部分パラメータ境界と低次数系を固定する相対入口もある。
`AllFactorizationCoherentSquare`は旧大域三角形二つを全対角線に沿って先に貼り合わせ、その全体を保持する。
旧三角形・大域前後合成ホモトピー4辺・Hom宇宙の有限単体を回収し、全次数で共有対角線が一致する。
大きい補助写像空間のモデル構造は仮定しない。元の値図式は小さいままである。
固定中心射を変える共通索引への接続、基底Cへの降下、最終RMapと最終比較は残る。
実装`03f095fa`、詳細は計画§268。新規81宣言・6モジュール、共有7166宣言・516モジュールの
標準公理監査と高次境界・パラメータ相対延長の回帰確認が成功。


## 全中心射の索引と小さい実lift図式・固定中心への制限（2026-10-16）

`CategoryTheory/ArrowContext`はHom二変数関手の要素圏上で、中心射を変える全因子分解圏と
全鎖パラメータを一つの厳密図式にする。
`ResolutionArrowDiagram`は全framed源・標的resolution・基底中心射に対する自然なbasepointから、
実際の小さいlift空間の厳密図式を構成する。任意指定した全点を保持する全中心整合系もある。
`FiberFunctorReindex`と`NerveCoherentReindex`は、fiber図式と全整合系の実際の再添字付けを扱う。
旧固定中心fiber図式は全中心図式の制限と自然同型であり、その上の系も一つの全中心系の制限として得る。
動く比較パラメータと旧全固定境界の接続、基底Cへの降下、最終RMapと最終比較は残る。
実装`673dd59a`、詳細は計画§269。新規73宣言・4モジュール、共有7239宣言・520モジュールの
標準公理監査と全因子分解の大きいパラメータ・高次境界の回帰確認が成功。


## 動く始点パラメータと終点値の整合系・動く全境界の保持（2026-10-16）

`NerveSimplexStart`・`NerveBiparameter`は[K(start), F(end)]の実際の二端点図式を構成し、
全単体作用素のprefix前合成・tail後合成の式と、inverse射の同型性を証明する。
`NerveDiagramExtension`は任意の鎖依存値に対するモデル不要の相対Reedy持ち上げを扱う。
`NerveMovingParameter`は小さい値の境界充填から、動くK(d)の指定写像全体を保持する一つの系を構成する。
`NerveMovingParameterRelative`は成分ごとのmonoで動く全境界系を固定し、元の全写像も同時に保持する。
`ResolutionArrowParameters`は全中心の実際の基底因子分解パラメータと小さいlift図式へ適用する。
旧比較の具体的な動くtuple/vertex境界との接続、基底Cへの降下、最終RMapと最終比較は残る。
実装`ff1ca062`、詳細は計画§270。新規91宣言・6モジュール、共有7330宣言・526モジュールの
標準公理監査と全中心lift図式・大きいパラメータの回帰確認が成功。


## 旧tuple interpolationとstrict vertex境界の全中心接続（2026-10-16）

`VertexTuplesFunctor`・`ResolutionArrowTuples`は実際のstrict liftの前後合成から旧tuple・vertex図式を作り、
旧点の移送式によりvertexDataを自然変換にする。
`NerveNaturalBoundary`・`NerveRelativeNaturalBoundary`は自然な境界から全境界系を作り、
元の各対象での境界式から低次数適合性を導く。全境界・元の全写像を同時に保持する。
`ResolutionArrowTupleCoherence`は全中心の旧interpolationを全写像として保持し、
旧tuple単体・定数tuple退化も回収する。全strict vertex境界を全外部次数で固定する。
既選択pre/post区間と混合三角形の全境界接続、基底Cへの降下、最終RMapと最終比較は残る。
実装`fb287c15`、詳細は計画§271。新規53宣言・5モジュール、共有7383宣言・531モジュールの
標準公理監査と動くパラメータ・全中心図式の回帰確認が成功。


## 動く区間の全両端系・全vertex境界のpushoutと相対延長（2026-10-16）

`NerveBiparameterMaps`は始点制限・終点値移送・任意関手による二端点系の再添字付けを扱う。
`PushoutCotensor`・`NervePushoutBoundary`は実pushoutで二つの全整合系を貼り合わせ、両側を回収する。
`NerveCylinderBoundary`はQ=(K×A)⨿_(V×A)(V×T)を実際の図式圏pushoutとして作り、
Q→K×Tの各成分がmonoであることをモデル構造不要のpushout-product定理から証明する。
`NerveCylinderExtension`は小さい値の境界充填から延長し、全両端系・全vertex cylinder系・
指定済み全低次数系を同時に保持する。外部次数0では元の区間写像全体を回収する。
大きい補助パラメータのモデル構造は不要。共通部分の等式と低次数境界適合性は一般層の入力であり、
旧pre/post比較への具体的接続で証明する部分が残る。混合三角形の全境界接続・基底Cへの降下・
最終RMapと最終比較も残る。実装`9d61c8af`、詳細は計画§272。
新規61宣言・5モジュール、共有7444宣言・536モジュールの標準公理監査が成功し、
旧tuple系とA0・A1最終入口の回帰確認も成功した。


## 比較の両端系の全中心射圏接続と旧pre/post端点の回収（2026-10-16）

`NerveBiparameterMapLaws`は自然な全境界を保持する制限・値移送・再添字付けの式を扱う。
`NerveBiparameterEvaluation`はこれらの全系の対象評価を実際の前後合成へ戻す。
`NerveArrowComparison`は同じ一つの全系をsource・targetへ再添字付けして二つの比較端点を作り、
両端の全vertex境界が同じ自然な全境界系と等しいことを証明する。
`ResolutionArrowComparisonEndpoints`は旧全中心tuple系へ適用し、その評価を小さい元の写像として回収する。
`ResolutionArrowElementary`は前後合成を実際の全中心索引の射として構成し、そのfiber・tuple移送を
旧移送と比較する。旧postLeft・postRight・preLeft・preRightの四端点が全小写像として回収される。
任意の実frame mapを使い、源の関手的因子分解や選択frame liftの合成則は追加仮定にしない。
旧比較区間全体を同時保持するための両端系のΔ1境界への貼り合わせ、vertex cylinderとの適合性、
混合三角形の全境界接続、基底Cへの降下、最終RMap・最終比較は引き続き残る。
実装`2e786e3d`、詳細は計画§273。新規49宣言・5モジュール、共有7493宣言・541モジュールの
標準公理監査と区間境界相対延長・旧全tuple系の回帰確認が成功。


## 全中心区間の実両端系・全vertex cylinder境界の貼り合わせ（2026-10-16）

`BinaryCotensor`・`NerveBinaryBoundary`は実二項余積上で二つの全写像・全整合系を貼り合わせる。
`NerveProductParameter`は実射影で追加パラメータに定数な全系を構成し、二方向の制限との交換を証明する。
`NerveMovingIntervalBoundary`は実際のK×∂Δ1上へ両端全系を貼り合わせる。両端の既存vertex式から、
V×T上の自然な全境界系との共通部分の一致を導く。全次数の適合性を追加仮定にしない。
`ResolutionArrowCylinderBoundary`は旧全中心left・rightへ適用して実図式圏pushout
Q=(K×∂Δ1)⨿_(V×∂Δ1)(V×Δ1)上の一つの全境界系を作り、両端・全vertex系を回収する。
Q→K×Δ1は実vertex包含から成分ごとのmonoとなる。小さい元のlift値の境界充填から、
この全境界と指定済み全低次数系を保持する相対延長を具体化する。
旧比較区間に対する低次数境界適合性、旧混合三角形の全境界接続、基底Cへの降下、
最終RMapと最終比較は残る。大きい宇宙のモデル構造は仮定しない。
実装`da59b695`、詳細は計画§274。新規59宣言・5モジュール、共有7552宣言・546モジュールの
標準公理監査と全中心端点・一般区間境界延長の回帰確認が成功。


## 実際の三境界式から導く低次数適合性と全区間写像保持（2026-10-16）

`NerveMovingFamilyFit`は任意の全境界系の0次数制限を実際の対象評価から回収し、
対象ごとの境界式から0次数適合性を導く。指定全写像の自然性や別の整合性入力を要求せず、
小さい値の境界充填と成分ごとのmonoから全写像・全境界を同時に保持する。
`NerveEvaluationLaws`は全系の制限式・自然な境界・追加定数パラメータを実際の対象写像へ戻す。
`ResolutionArrowCylinderFamilyFit`は全中心の実Q系に適用し、二端点と区間全体のvertex制限の三式から
Q全体への適合性を導く。Dataに指定した各中心の全区間写像と既存Q全境界系を同時保持する。
低次数整合性は追加入力に残さない。大きい宇宙のモデル構造は不要。
旧pre/postの具体的区間をUniverseLift・テンソルの実比較でこの入力へ載せる部分、
旧混合三角形の全境界接続、基底Cへの降下、最終RMapと最終比較は残る。
実装`1259086c`、詳細は計画§275。新規38宣言・3モジュール、共有7590宣言・549モジュールの
標準公理監査と実全中心区間境界・旧比較端点の回帰確認が成功。


## 既選択pre/post全区間のpresentation整合系と元の全小写像の回収（2026-10-16）

`UniverseLiftTensor`は実テンソル・標準単体の全写像を上げ下げする操作の逆関係を証明する。
`UniverseLiftFixedHomotopy`は指定済みedgeから新たな選択なしで元のfamilyを使い、
両端・区間全体のvertex境界と全小写像の回収を保つ。
`ResolutionArrowCylinderFaces`は実際の全中心Qの二つの端点と標準δ1・δ0を比較する。
`ResolutionArrowSelectedIntervals`は既存のpostEdge・preEdgeへ適用し、Q全境界への実適合性を証明する。
`SelectedIntervalDiagram`は全pre/postの具体的presentationを索引にまとめ、その基礎射の実可換正方形で
移送する。元の全区間写像と再添字付けした同じQ全境界系を一つの整合系で同時に保持し、
元の小さいselected edge familyを全写像として回収する。同じ射を与える異なるpresentationも保持する。
源の一般モデル圏、元のHom宇宙の小さい値、任意の実frame mapを維持する。
大きいモデル構造や源の関手的因子分解、元のresolution射影の充満忠実性は仮定しない。
旧混合三角形の全境界・共有対角線の接続、基底Cへの降下、最終RMapと最終比較は残る。
実装`6a4960a9`、詳細は計画§276。新規106宣言・5モジュール、共有7696宣言・554モジュールの
標準公理監査と全区間境界適合性・既存混合三角形の回帰確認が成功。


## 全中心の混合正方形・旧全三角形の実入力と同じ四辺全系への接続（2026-10-16）

`ResolutionMixedDiagram`は実framed射・中心射・標的射から全中心索引の実可換正方形を作る。
その実可換立方体を射とする索引上で四隅・四辺・対角移送と自然な共通vertex境界を構成する。
`ResolutionMixedTriangles`は旧二つの全三角形・全facet・共有対角線を実座標へ移し、全小写像を回収する。
`ResolutionMixedReassociation`はBD側の左結合中心と右結合中心を自然同型で結び、その小さい値の移送が
旧castMapそのものであることを証明する。実BDのfiber移送も旧postTailに等しい。
`ResolutionMixedIntervalRestrictions`は前回の同じ全区間系を四辺へ再添字付けし、実tuple・値移送でそろえる。
`ResolutionMixedEdgeRecovery`はその四辺の対象評価が旧三角形の四facetの全写像に等しいことを証明する。
UniverseLiftTensorの標準単体付き全写像に、値の後合成との実交換式も追加した。
共有対角線を含む全facet系の適合性と、その全境界を固定する三角形全系の延長は残る。
旧三角形の対象ごとの回収を、全外部次数で同じ四辺全系を固定する延長の代わりにはしない。
基底Cへの小さいSSet値降下、最終RMapと最終比較も残る。源の仮定・宇宙契約は維持する。
実装`17aa144d`、詳細は計画§277。今回の監査対象163宣言・6モジュール、共有7840宣言・559モジュールの
標準公理監査と同じ旧全区間系・既存混合三角形の回帰確認が成功。


## 同じ四辺全系の八端点と四共有隅の全次数での一致（2026-10-16）

`NerveBiparameterComposition`・`NerveArrowComparisonComposition`は全系の移送・合成と中間交換、
等しい索引関手の移送による厳密同定を証明する。`NerveProductEndpointTransport`は全端点式を実移送する。
`SelectedIntervalEndpoints`は元の全区間系の固定Q境界から、両端と任意の再添字付け後の全端点式を回収する。
`ResolutionMixedReassociationEquality`はBD最終中心の関手がcornerDそのものと等しく、
既存toFinalがその等号からのeqToIsoと等しいことを証明する。一般の自然同型への厳密自然性は仮定しない。
`ResolutionMixedRawEndpoints`・`ResolutionMixedEndpointCompatibility`は同じ四辺全系の八端点を
元の同じ全tuple系から得る四つのcorner系へ同定し、共有端点の一致を全外部次数の等式で得る。
共有対角線と二つの∂Δ2全境界の構成・三角形全系の延長、基底Cへの降下、最終RMap・最終比較は残る。
実装`7583f39c`、詳細は計画§278。新規79宣言・7モジュール、共有7919宣言・566モジュールの
標準公理監査と同じ混合四辺・既存全区間系の回帰確認が成功。


## 旧全対角線・同じQ境界の同時保持と五辺全系の適合性（2026-10-16）

`ResolutionMixedDiagonalData`は実対角射のfiber・tuple移送を旧post/pre合成へ同定し、
元の全対角線が同じQ境界へ適合することを実二端点・全vertex制限から証明する。
`ResolutionMixedCoherentDiagonal`はその全写像と同じQ全境界を同時に保持して延長する。
旧小写像回収、同じcorner0・corner3への全端点式、区間全体の共通vertex制限も証明した。
`ResolutionMixedFaceSystems`は同じ四辺と一つの共有対角線を二つの三角形のfacetへ並べ、
すべての面交差での適合性を全系の等式で証明する。元の二つの全三角形の実facet評価と
全小写像の回収も保持する。源の一般モデル圏と独立宇宙、小さい値の契約は維持する。
実∂Δ2系への貼り合わせ・三角形全体の延長、基底Cへの降下、最終RMap・最終比較は残る。
実装`e376cab5`、詳細は計画§279。新規50宣言・3モジュール、共有7969宣言・569モジュールの
標準公理監査と同じ混合四辺・全端点の回帰確認、A0・A1の最終利用例が成功。


## 実∂Δ2境界と全vertex境界を同時に固定する旧全三角形の延長（2026-10-16）

`ProductBoundaryCotensor`は閉随伴で境界パラメータを移し、動く追加パラメータを保持して実境界を
貼り合わせる。`NerveMovingBoundary`は全facetを保持する整合系と一意性、共通全vertex制限を構成する。
`ResolutionMixedBoundary`は同じ五辺から二つの実∂Δ2全境界を作り、旧全三角形の実適合性を証明する。
実装`da71d1d9`、詳細は計画§280。

`SelectedIntervalVertices`・`NerveNaturalBoundaryTransport`は元の区間全系の固定全vertex境界を
実再添字付け・実可換正方形で運ぶ。`ResolutionMixedVertexRestrictions`は同じ四辺と共有対角線の
全vertex制限を、同じ自然な共通境界へ同定する。
`ResolutionMixedTriangleBoundary`はQ2の実pushout境界・monoを構成し、旧全三角形の適合性を導く。
`ResolutionMixedCoherentTriangles`は旧二つの全三角形を保ち、同じ四辺・対角線・三角形全体の
vertex境界をすべての外部次数で固定する。元の小さい全三角形を回収し、共有AD制限も全系で等しい。
源の一般性・独立宇宙・小さいlift値を維持する。大きいモデル構造や源の関手的因子分解は不要。
presentation系と全因子分解の接続、基底Cへの小さいSSet値降下、最終RMap・最終比較は残る。
実装`1c295db1`、詳細は計画§281。今回57宣言・6モジュール、共有8054宣言・577モジュールの
標準公理監査、共有入口2772 jobs、元の全境界・共有対角線の回帰確認が成功。


## 全混合比較族の小さい回収と元のKan写像対象への実作用（2026-10-16）

`NerveSmallFamilies`は大きい索引上の動くパラメータ全系から、元の小さいK(c0)×Δn→F(cn)を
全写像として回収する。任意のθでの実prefix・tail移送を保持し、パラメータ前合成とも交換する。
`UniverseLiftProductParameter`は単体付きパラメータの実自然同型と全単体写像の可換性を構成する。
`ResolutionMixedSmallFamilies`は同じ全三角形と五辺を元のSSet[v]の全有限列族へ戻し、
旧全三角形・実facet制限・共有ADを回収する。
`ResolutionMixedSmallAction`はその小さい全族を元のKanLiftActionへ渡し、
作用の実facet式・共有AD・標的Zの自然性と旧全三角形による作用の回収を証明する。
大きいモデル構造や源の関手的因子分解は要求しない。
任意中心射での作用の両端移送との統合、全因子分解系の接続、基底Cへの厳密降下、
任意標的の導来不変性、最終RMap・最終比較は残る。
実装`c543585a`、詳細は計画§282。新規41宣言・4モジュール、共有8095宣言・581モジュールの
標準公理監査、共有入口2776 jobs、旧全三角形の回帰確認が成功。


## 実中心射での作用の両端移送と全外部単体写像への接続（2026-10-16）

`ResolutionArrowActionTransport`は任意の実中心射によるlift値移送の作用を、
入力Homの実target resolution前合成と出力Kan Homの実source frame前合成へ分解する。
`ResolutionArrowActionFunctors`はその両端を既存の厳密なHom関手のmapへ同定する。
`NerveSmallAction`は元の小さい全有限列族の全θ公式とこの両端移送を接続し、
任意入力族の作用公式・入力再添字付け時の全作用制限と実両端移送の合成則を証明する。
`ResolutionMixedActionOperators`は同じ混合三角形・全五辺の小さい作用へ適用し、
内部facet制限と外部θ・prefix移送の交換も保持する。
源の一般性・独立宇宙・小さい値域は維持する。生の作用移送はSSetモデルも不要。
全因子分解系への接続、基底Cへの小さいSSet値での厳密化、任意標的への導来不変な拡張、
最終RMapと最終比較は残る。
実装`58401618`、詳細は計画§283。新規43宣言・4モジュール、共有8138宣言・585モジュールの
標準公理監査、共有入口2780 jobs、同じ旧小作用の回帰確認が成功。


## 全因子分解比較の小さい全族と実作用（2026-10-16）

`NerveLargeSampling`は大きい定数パラメータの同じ整合系を、小さい全試験族へ戻す。
`AnchoredChainFiniteTest`は全因子分解列の各単体について補助単体全体を保持し、
両方向の単体写像との可換性を証明する。
`AllFactorizationSmallFamilies`は同じ旧全因子分解三角形・全facet・共有対角線を
元のSSet[v]の全有限列族として回収し、元のchoice座標での全三角形の一致を証明する。
`AllFactorizationSmallAction`はその相対選択空間を実lift値図式へ評価し、
元の小さいKan Hom上の作用へ接続する。全外部単体写像での実両端移送、
内部因子分解列・facet制限、全頂点境界、共有対角線と両立する。
源の仮定や値域宇宙は強めない。基底Cへの厳密降下、任意標的への導来不変な拡張、
最終RMapと最終比較は残る。詳細は計画§284、実装`6bfedb29`。
新規64宣言・4モジュール、共有8202宣言・589モジュールの標準公理監査、
共有入口2784 jobs、既存作用43宣言・旧全因子分解比較101宣言の回帰確認が成功。


## 任意標的の実replacementと両変数同時の通常降下（2026-10-16）

`Replacement/FibrantCategory`は、任意基底Xの実trivial cofibration X→RXとfibrantなRX、
可換比較射を持つ圏を構成する。通常の分解と持ち上げで全対象・基底射を扱い、
実比較の弱同値性を基底弱同値性と同定する。関手的分解は不要。
`Replacement/FibrantLocalization`は、fibrant対象上で弱同値を同型へ送る任意関手について、
同じ基底射上の実比較射の像の等式を証明する。
`ReplacementMappingBifunctor`は源の実frameと標的の実replacementの上で、
元のSSet[v]値の厳密なKan双関手を構成する。両基底弱同値を保ち、
元の非fibrant基底標的に対するπ0比較と両変数の自然性を持つ。
`ReplacementMappingLocalization`と`ReplacementMappingDescent`は、両比較射の選択独立性を
全局所化写像空間で証明し、選んだ小さいKan値を用いる基底上の同時降下と、
任意presentationへの実弱同値に基づく自然同型を構成する。
基底上の関手則はHo(SSet)での主張であり、最終SSet値RMapの厳密化と最終比較は残る。
実装`41280dff`、詳細は計画§285。新規128宣言・5モジュール、共有8330宣言・594モジュールの
標準公理監査、共有入口2789 jobs、既存framed関手・全因子分解小作用の回帰確認が成功。


## 固定値での厳密降下の反例と値変更による自然弱同値（2026-10-16）

`StrictValueObstruction`はΔ1→Δ0のcofibration・trivial fibration分解から、
点と弱同値だが同型ではない小さいKan複体を構成する。
`StrictValueDescentCounterexample`は、同型な二つの基底対象にこれらの値を指定すると、
対象ごとの同型の範囲でもその値を持つSSet値関手は存在しないことを証明する。
`StrictValuePresentationCounterexample`は、fullな実presentation射影、小さいKan値、
全実射の弱同値性、局所化後の平行射の独立性を全て満たす反例を構成する。
同時に、値を定数の点へ変更した厳密関手への自然弱同値を構成し、局所化後の自然同型を得る。
これは固定値での同型降下の不可能性であり、値変更と自然弱同値zigzagを許す
最終RMapの不可能性は主張しない。次の厳密化はこの値変更を含めて構成する。
実装`21a2851d`、詳細は計画§286。新規45宣言・3モジュール、共有8375宣言・597モジュールの
標準公理監査、共有入口2793 jobs、前回の両変数降下128宣言の回帰確認が成功。


## モデル不要のbarと基底上の厳密な補助候補（2026-10-16）

`BarConstruction`は次数ごとの実要素圏のnerveとdiagonalから厳密なbar関手を作る。
`BarAugmentation`は任意の実coconeへの写像を定義する。
`RelativeBarConstruction`は実射影p:D→Bと小さい値図式Fから、costructured arrowを使い、
B上の厳密な相対bar関手を構成する。`RelativeBarAugmentation`はF→p⋙Gから
全単体写像・全基底射で自然なaugmentationを構成する。一般部分にモデル構造は不要。
`ReplacementBarCandidate.auxiliaryBar`はこれを実replacement双関手へ適用し、
(Cᵒᵖ×C)→SSet[max(u,v)]を構成する。大きいSSetのモデル構造は要求しない。
値域は最終契約のvではなく、元の双関手との自然弱同値比較・小さい厳密関手への移行は残る。
`BarSize`は点だけの図式でも索引対象がbarの0単体へ単射し、具体的に非smallとなる例を証明する。
入力の小ささから生のbarの小ささを推論せず、別の小さい値と自然弱同値を構成する必要がある。
実装`4ff11f4e`、詳細は計画§287。新規31宣言・6モジュール、共有8406宣言・603モジュールの
標準公理監査、共有入口2799 jobs、両変数降下・固定値反例の回帰確認が成功。


## 元の実replacement図式と補助barの自然比較span（2026-10-16）

`RelativeBarUnit`は恒等射影のbarから、pで全comma射を移した相対barの制限への自然変換を作る。
`RelativeBarIdentity`は固定対象でのaugmentation sectionと実合成が恒等になる式、
degreeごとの実collapse、全列の回収、各degreeの全nerve homotopyを構成する。
section自体を全基底射で自然だとは扱わず、degreeごとのホモトピーを対角全体のものとは扱わない。
`UniverseLiftIteration`は二重liftを一重liftへ明示的・自然に比較する。
`RelativeBarSpan`と`ReplacementBarComparisonSpan`は、元の小さい写像空間の明示的liftから
補助barの制限へ至る自然なspanを、恒等射影のbarを中間に置いて構成する。
一般部分はモデル不要で、適用でも大きいSSetのモデル構造や源の関手的分解は要求しない。
両脚の弱同値性、対角全体の収縮、最終の小さい厳密関手と最終比較は残る。
実装`8f58d0eb`、詳細は計画§288。新規36宣言・5モジュール、共有8442宣言・608モジュールの
標準公理監査、共有入口2804 jobs、既存bar・両変数降下の回帰確認が成功。


## 恒等射影barの対角収縮と同じ実左脚のホモトピー逆（2026-10-16）

`RelativeBarContractionOperators`は区間関手全体が全単体写像と両立することを証明する。
`RelativeBarDiagonalContraction`はその両立で、恒等写像からaugmentation・sectionの合成への
一つの実SSet.Homotopyを対角全体に構成する。
`UniverseLiftHomotopy`と`RelativeBarSpanContraction`は同じ全ホモトピーを実liftで移し、
二重liftの自然同型を打ち消して、同じ比較spanの左脚と同じsectionへ接続する。
`ReplacementBarLeftContraction.auxiliaryLeft_has_homotopyInverse`は実replacement図式で、
一方の合成の厳密な恒等式と他方の合成の全simplicial homotopyを同時に出力する。
一般部分はモデル不要で、適用でも大きいSSetモデルや源の関手的分解を要求しない。
弱同値の公開定理への接続、span右脚の弱同値性、最終の小さい厳密関手と最終比較は残る。
実装`1a068872`、詳細は計画§289。新規21宣言・5モジュール、共有8463宣言・613モジュールの
標準公理監査、共有入口2809 jobs、既存span・barの回帰確認が成功。


## Anodyne反転による実左脚の比較と元の小さいモデル弱同値（2026-10-16）

`AnodyneIntervalEndpoints`は任意Xの両区間端点がanodyneであることをモデル不要で証明する。
`AnodyneHomotopyLocalization`はanodyne反転関手で全simplicial homotopyの像の等式を得て、
実retractionと同じ全ホモトピーから実際の同型を構成する。
`AnodyneModelDetection`は元のSSet[v]の固定モデル条件の下で、
anodyne反転が元の全弱同値を反転することと、元のモデル弱同値が
canonicalなanodyneQでの同型によって正確に判定できることを証明する。
`RelativeBarAnodyneComparison`と`ReplacementBarAnodyneComparison`は、
実span左脚の全図式がanodyne反転後に自然同型となることを証明する。
任意モデル源で大きいSSetモデルを要求しない。小索引では実モデル弱同値まで検証する。
宇宙liftとの判定の保存・反映、span右脚、最終の小さい厳密関手と最終比較は残る。
実装`42d73f52`、詳細は計画§290。新規31宣言・5モジュール、共有8494宣言・618モジュールの
標準公理監査、共有入口2814 jobs、既存収縮・spanの回帰確認が成功。


### 宇宙liftのモデル不要のanodyne保存（§291）

`Generated/FunctorClosure.generatedLeft_map`は、小さいcolimitとpushoutを保存する
関手が、生成射の保存から生成左類全体の保存を導く一般入口である。
値域は四つのcell操作に閉じた射のクラスだけを持てばよい。
`Simplicial/UniverseLiftAnodyne`はこれを実hornへ適用し、宇宙liftのanodyne保存と、
anodyne局所化での可逆性の保存を証明する。
元の小さいモデルの全弱同値のliftにも適用するが、大きい宇宙のモデル構造は要求しない。
判定の反映、bar右脚の比較、最終の小さい厳密RMapは引き続き未完了。
検証：`scripts/check_universe_lift_anodyne.lean`、計画書§291。


### 宇宙liftの反映と元の弱同値の検出（§292）

`Simplicial/HomotopyClasses`と`KanHomotopyExtension`・`KanHomotopyClasses`は、
実ホモトピー類を使ったモデル不要のKan対象への検出を提供する。
`UniverseLiftHomotopyClasses`は実ホモトピーを小さい宇宙へ戻す。
`UniverseLiftAnodyneReflection.anodyneQ_map_isIso_iff`は任意の射について、
元とlift後のanodyne局所化での可逆性の同値を証明する。両宇宙ともモデル構造は不要。
元の小さいモデルを指定した場合の実弱同値判定と、全自然変換についての同値も公開する。
bar右脚と最終の小さい厳密RMapは未完了。
検証：`scripts/check_universe_lift_anodyne_reflection.lean`、計画書§292。


### 終域resolutionと実自然弱同値span（§293）

`HomotopyFunctionComplex/DualResolutionTargets`は反対モデル圏の既存resolutionを用い、
全終域次数を既存fibrant replacement圏の実対象・実比較として扱う。
`RightResolutionMapping`は終域も動かした小さい対角図式と、その小さいKan置換を構成する。
0次値からの自然弱同値、両変数の弱同値不変性、元のbase間Homとのπ0同値を持つ。
`RightResolutionRefinement`は全旧presentationを含む補助索引で、旧図式と新図式を結ぶ
実自然弱同値spanを構成する。対象被覆だけでcofinalityやbar右脚の弱同値は主張しない。
検証：`scripts/check_right_resolution_mapping.lean`、計画書§293。


### 実二重Homの両側比較と右lift作用（§294）

`BiresolutionRawMapping`と`BiresolutionRightMapping`は、実二重Homのop/unop自然同型と
左右のframed対角への自然弱同値を構成する。
`BalancedResolutionComparison`は共通の小さいKan中間から両側への自然弱同値span、
右端の元のbase間Homへのπ0比較、局所化後の全図式の自然同型を提供する。
`BiresolutionRightAction`は反対モデル圏の既存全中心lift選択を実右mapping行へ接続し、
同じ選択点の保持・全パラメータ・全源単体作用素・実中心移送との整合式を公開する。
両側の混合整合性、実bar右脚の弱同値、基底上の最終小さい厳密RMapは引き続き未完了。
検証：`scripts/check_balanced_resolution_comparison.lean`、計画書§294。


### 同じraw二重Hom上の混合作用と全境界保持（§295）

`CosimplicialMapFamily.ofDoubleHom`は実familyから全単体互換性を導く。
`MixedDiagonalHom`は両側の作用順序の実等式とparameter制限との交換を証明する。
`MixedResolutionLiftAction`は元の両側lift空間へ適用し、任意の単射境界上の両familyと
作用写像全体を同時に保持する延長を構成する。小さいKan出力にも適用する。
`MixedBiresolutionComparison`は既存raw図式との実自然同型を提供し、
`MixedDiagonalHomRecovery`は元の両側の片側作用を同じ全写像として回収する。
全中心・全因子分解の大域的整合性、bar右脚、最終の基底上の小さい厳密RMapは未完了。
検証：`scripts/check_mixed_resolution_lift_action.lean`、計画書§295。


### 両側中心と全chain作用素の混合整合性（§296）

`MixedResolutionCenters`は両側の実frame・target resolutionを動かす入力・出力図式を作り、
元のinclusionから混合作用の全中心移送式を導く。
`NerveMixedAction`は同じ両側systemを使い、全chain・全単体作用素について
parameter・入力・出力の実移送を含む整合式を証明する。
`NerveMixedChoices`は両側systemを構成し、指定済み全familyと任意の低次数全systemを保持する。
モデル構造は元の小さいSSetだけで使う。
具体的な全因子分解systemへの接続、混合出力の弱同値比較、bar右脚、最終RMapは未完了。
検証：`scripts/check_mixed_center_chain_action.lean`、計画書§296。


### 混合出力の自然弱同値と両側Kan比較（§297）

`MixedDiagonalRows`は左右の行表示と行ごとの弱同値による判定を提供する。
`MixedResolutionComparison`は両側の実augmentationによる混合Hom比較を
全presentation上の自然弱同値として証明する。対角Reedy cofibrancyは要求しない。
`MixedResolutionKanComparison`は同じ実strict lift作用を回収し、既存の共通Kan中間から
混合Kan出力への自然弱同値、両変数の弱同値不変性、元のbase間Homへのπ0同値を構成する。
`MixedCenterComparison`はこれを既存の全chain作用の同じ全中心KanOutputへ接続する。
具体的な全因子分解systemへの接続、bar右脚、基底上の最終小さい厳密RMapは未完了。
検証：`scripts/check_mixed_resolution_comparison.lean`、計画書§297。


### 任意の全lift familyの混合作用の弱同値（§298）

`Quillen/ContractibleParameters`は一般モデル圏で、収縮可能な二つのparameterを
加えたgraphの弱同値を実pullbackと二対三性から導く。
`MixedResolutionInvariance`は同じ実raw Hom写像とstrict lift作用の弱同値を証明する。
`MixedLiftActionWeakEquivalence`は元の全lift空間の普遍作用と、任意の全familyの作用に適用する。
両基底射と入力写像が弱同値なら、元の作用と小さいKan出力への作用が弱同値となる。
`MixedCenterActionWeakEquivalence`は同じ全中心・全chain作用へ接続する。
実bar入力への適用条件の証明、bar右脚、基底上の最終小さい厳密RMapは未完了。
検証：`scripts/check_mixed_lift_action_weak_equivalence.lean`、計画書§298。


### 実resolution barの先頭側評価（§299）

`Simplicial/NerveFirstChoice`は反変図式の先頭側全chain整合系を構成し、
元の点・任意の低次数全system・定数chainでの頂点を保持する。
`ResolutionBarCenters`は実comma圏から両側の反変lift中心を作る。
`ResolutionBarFirstAction`は実prefix Hom写像を含む全単体作用素の式を証明する。
`ResolutionBarEvaluation`は同じraw混合Homの実relative bar全体を小さいreference出力へ評価する。
`ResolutionBarReference`はreferenceからの写像との合成を元の小さい作用として回収し、
大きいモデルを使わず、その実合成のanodyne局所化での可逆性を証明する。
評価自体・bar右脚の弱同値、元のreplacement barとの比較、最終小さい厳密RMapは未完了。
検証：`scripts/check_resolution_bar_evaluation.lean`、計画書§299。


### 実row resolutionと既存bar内の行presentation（§300）

`ResolutionFrameRows`は二つの自明Reedy fibrationを合成し、同じ基底上の実row resolutionと
全行作用素を構成する。`ResolutionFrameRowFunctor`は全実framed比較への自然性を証明する。
`MixedHomBifunctor`と`ResolutionRowMixedMapping`は同じ混合出力の実行表示を作り、
全行比較・全行作用素の弱同値と、対角の全図式の自然同型を提供する。
`ResolutionBarRowPresentations`は行augmentationを既存barの実comma射・要素comma射へ接続し、
誘導されるraw写像として同じ行比較を回収する。
新しいouter-frame liftの関手性は主張しない。barの逆向きホモトピー比較・右脚、
元のreplacement barとの比較、基底上の最終小さい厳密RMapは未完了。
検証：`scripts/check_resolution_frame_rows.lean`、計画書§300。


### 実barホモトピーと右脚の行sectionへの帰着（§301）

`RelativeBarSections`・`RelativeBarSectionHomotopy`は、任意の実comma射から
relative barへの全写像の間のsimplicialホモトピーを構成する。モデル構造は不要。
`RelativeBarSectionUnit`は同じ自然spanの右脚をsource sectionで検出する。
`UniverseLiftPadding`は元のreferenceのULift wrapperを明示的な自然同型で回収する。
`ResolutionBarRowHomotopy`は同じrow augmentationへの実ホモトピーを作り、
paired raw bar右脚全体の局所化後の可逆性を全referenceの0次行sectionの可逆性へ帰着する。
0次行sectionが可逆であること自体は未証明。右脚の無条件の弱同値、
元のreplacement barとの比較、基底上の最終小さい厳密RMapは未完了。
検証：`scripts/check_resolution_bar_row_homotopy.lean`、計画書§301。


### 全bar単体の評価を持つ実row presentationへの射（§302）

`ResolutionLiftRows`は高次liftの各単体から、全自然変換を持つ実row resolution射を取り出す。
`ResolutionCenterRowLifts`は同じ全fiber familyを使い、両端中心の実移送式を証明する。
`ResolutionBarSimplexCone`は各bar単体の最初の頂点から実row presentationへの射を構成し、
元のHomラベルの像が同じ既存評価値に正確に一致することを証明する。
両基底成分が弱同値なら、そのraw Hom写像全体も弱同値になる。
次数ごとの行対象とouter-frame liftの整合性は残り、bar全体の収縮とはまだなっていない。
0次行section・右脚の可逆性、元のreplacement barとの比較、最終小さい厳密RMapは未完了。
検証：`scripts/check_resolution_bar_simplex_cone.lean`、計画書§302。


### 全bar単体圏上の厳密なordinary-resolution比較図式（§303）

`ResolutionCenterRowLaws`は全row liftのparameter制限・単体制限の式を証明する。
`ResolutionBarRowDiagram`は元の両側全systemから、全nerve単体圏上の厳密な自然変換を構成する。
`ResolutionBarRowOperators`は全chain・全単体作用素の可換式をその自然性から回収する。
`ResolutionBarConeDiagram`は実barのラベルを忘れるsimplicial mapを通して引き戻し、
同じ単体比較射を全bar単体圏上の自然変換の成分として保持する。
構成はordinary resolution圏内であり、outer-frame liftの関手性は主張しない。
frame側の比較、bar収縮・右脚・0次行sectionの可逆性、最終小さい厳密RMapは未完了。
検証：`scripts/check_resolution_bar_cone_diagram.lean`、計画書§303。


### 元のframe合成の小さいderived比較（§304）

`FrameLiftSpace`は元のdiagram圏のReedyモデルを使い、固定inner射のframe比較空間を
元のHom宇宙に構成する。元のframe写像を点に入れ、任意の指定済み全境界を保持して延長する。
`FrameSquareComparison`はinnerが可換な正方形の元の両frame合成を二端点として保持する。
`ResolutionBarFrameSquares`は同じ全bar単体圏の実正方形へ適用し、両側の比較を構成する。
大きいSSetモデル構造も、選んだframe liftの関手性も要求しない。
固定正方形間の高次整合性・bar全体の収縮、0次行section・右脚の可逆性、
元のreplacement barとの接続、最終小さい厳密RMapは未完了。
検証：`scripts/check_resolution_bar_frame_squares.lean`、計画書§304。


### 同じraw値の通常resolution barへの厳密な移送（§305）

`OrdinaryResolutionPairs`は元のraw Hom・projectionを通常のresolution pair上へ厳密に因子分解する。
`OrdinaryResolutionRows`では元の全row pair・augmentationが同じcomma圏内の厳密な図式になる。
`RelativeBarReindex`と`OrdinaryResolutionBar`は元のframed barからの実自然変換を作り、
元の全Homラベルを保持する。元のspanのsource・middle・左脚と、その局所化後自然同型も保持する。
forgetFramesのcofinality・strict section・新しい右脚の弱同値性は仮定しない。
今後の右脚の証明は通常索引で進める。値はまだ補助の大きい宇宙にあり、
元のmapping図式への自然弱同値比較と最終小さい厳密RMap・F2は未完了。
検証：`scripts/check_ordinary_resolution_bar.lean`、計画書§305。


### 通常resolution右脚への同値な帰着（§306）

`RelativeBarMiddleReindex`は任意の索引関手による実middle比較と左右の可換性を構成する。
anodyne射を反転する任意の関手の下で、このmiddle比較は全自然同型になる。
`OrdinaryResolutionBarReduction`は実forgetFramesへ適用し、元の右脚の像が全自然同型になる条件を、
通常resolution上の右脚の像が全自然同型になる条件と同値にする。
対象ごとのframeだけを使い、忘却のfunctorial section・faithfulness・cofinalityを要求しない。
通常右脚の可逆性、自然な小値化、最終小さいRMap・F2は未完了。
検証：`scripts/check_ordinary_resolution_bar_reduction.lean`、計画書§306。


### 通常barの実評価とcomma圏内の全自然cone（§307）

`OrdinaryBarCenters`・`OrdinaryBarFirstAction`・`OrdinaryBarEvaluation`は通常barの全実chainと
ラベルを使い、同じ小さい参照混合Homの持ち上げへの実単体的評価を構成する。
`OrdinaryBarReference`は恒等参照sectionとの合成を元の小さい弱同値として回収する。
`OrdinaryBarSimplexCone`は同じ実要素comma圏内の単体比較を構成し、ラベルが評価値と等しいと証明する。
`OrdinaryBarRowDiagram`・`OrdinaryBarCommaCone`は全比較を同じcomma圏内の自然変換としてまとめる。
`OrdinaryBarRightEvaluation`は元の右脚と評価のanodyne局所化後可逆性の同値を証明する。
評価自身の可逆性・bar全体の収縮、元のreplacement図式との自然比較、最終小さいRMap・F2は未完了。
検証：`scripts/check_ordinary_bar_evaluation.lean`、計画書§307。


### 次数・ラベル付き総要素coneと実nerveホモトピー（§308）

`OrdinaryBarTotalCone`は実comma対象・次数・Homラベルを記録する同じ総要素圏で、
全bar単体から全rowへの実自然変換を構成する。
`OrdinaryBarTotalEvaluation`はrow側が元の小さい評価先の単体圏を経由することを全関手で証明する。
`OrdinaryBarTotalHomotopy`は元のbar単体圏のnerveから総要素圏のnerveへの実ホモトピーを構成する。
独立宇宙の`NerveHomotopyUniverse`と、元の要素を保持する`ElementsNaturalPrecomp`を使用する。
`UniverseLiftElements`は既知の持ち上げの単体圏同値だけを構成し、任意のbarを縮小しない。
補助nerveと元のbarとの比較、評価の可逆性、自然な最終小値化・F2は未完了。
検証：`scripts/check_ordinary_bar_total_cone.lean`、計画書§308。


### 実nerve augmentationと元のbar値ホモトピー（§309）

`SimplexChainParameter`・`SimplexNerveAugmentation`は任意Xについてnerve(X.Elements)→Xを構成し、
全単体作用素・任意のX→Yでの自然性を証明する。
`LabelledChain`・`TotalNerveBarAugmentation`は総要素圏の実chainと同じラベルを既存の対角barへ送る。
`RelativeBarCommaPresentation`は同じrelative barとの明示的同型を作り、全元射・ラベルを保持する。
`OrdinaryBarNerveBridge`は同じ総要素nerveから元の通常barへの実bridgeを構成し、
前のnerveホモトピーを元bar値のホモトピーへ移す。
標準単体圏augmentationとの端点の同定、augmentation・評価の可逆性、最終小値化・F2は未完了。
検証：`scripts/check_ordinary_bar_nerve_bridge.lean`、計画書§309。


### 元の端点の全写像の同定とaugmentation正方形（§310）

`LabelledChain.reconstruct`は全実chainを基底chainと最初のラベルから正確に再構成する。
`NerveSimplexFirstFunctor`は一般のnerveの最初の頂点関手を標準augmentationと同定する。
`OrdinaryBarFirstEndpoint`は元のfirstCompositeを標準simplexAugmentationと全写像で同定する。
`OrdinaryBarEvaluatedEndpoint`は元のもう一端を小さい評価先の単体圏経由の実合成に因子分解し、
元の評価とのaugmentation正方形の可換性を証明する。
元のbar値ホモトピーは、標準augmentationからこの実小さい因子分解へ向かうものになる。
augmentation・評価の可逆性、自然な最終小値化・F2は未完了。
検証：`scripts/check_ordinary_bar_endpoints.lean`、計画書§310。


### 単体圏nerveの構造と標準単体augmentationの可逆性（§311）

`SimplexNerveFunctor`は元の実chainを作用素chainと最初のラベルの直和として自然に分解し、
任意の小さいcolimit coconeの保存を証明する。
`SimplexNerveMonos`は元の単射成分から全次数の単射とモノ射保存を導く。
`NerveInitialImage`は実始対象によるnerveの収縮を任意のanodyne反転関手での同型にする。
`SimplexNerveStandard`は補助宇宙を含む任意の値宇宙で、標準単体上の元のaugmentationの可逆性を証明する。
補助SSetモデル構造は不要。一般Xへの貼り合わせ、元の評価の可逆性、最終小値化・F2は未完了。
検証：`scripts/check_simplex_nerve_standard.lean`、計画書§311。


### モデル不要のKan値判定と局所化後の直積保存（§312）

`AnodyneKanReplacement`は元のhorn小対象論法だけで実Kan置換関手と自然なanodyne unitを構成する。
`KanTestDetection`は、元のanodyne局所化後可逆性と、全Kan値の元のホモトピー類テストの全単射性の
同値を証明する。同じテストから任意のanodyne反転関手でも実射が可逆になる。
`AnodyneLocalizedTensor`はQで可逆な全射について、任意の左右直積後の可逆性を証明する。
値宇宙は任意で、補助SSetモデル構造・源の関手的分解は要求しない。
モノ射に沿う相対貼り合わせ・一般augmentationの可逆性、元の評価・最終小値化・F2は未完了。
検証：`scripts/check_kan_test_detection.lean`、計画書§312。


### 元の端点・区間を保つ延長とpushout後の全射性（§313）

`KanMonoEndpointExtension`は任意のモノ射に沿い、元の始点または終点を固定して実ホモトピーを延長する。
区間写像の制限も元のHと正確に等しい。
`KanMonoStrictExtension`は厳密延長の存在を元の全ホモトピー類へ降ろし、全射テストから
元の指定写像に厳密に等しい制限を持つ延長を得る。
`KanMonoPushoutExtension`は元のQで可逆なモノ射の任意の実pushout後に厳密延長とKanテストの全射性を証明する。
補助宇宙のモデル構造は不要。pushout後の単射性・完全な相対持ち上げ・骨格の逐次貼り合わせ、
一般augmentation・評価の可逆性、最終小値化・F2は未完了。
検証：`scripts/check_kan_mono_extension.lean`、計画書§313。


### Kan fibrationの実収縮から全モノ射への持ち上げ（§314）

`KanTwoHornLift`は元の二辺と基底2単体を保つ外側hornの充填を構成する。
`CurriedHomotopy`は内部Homの辺を実ホモトピーへ戻す。
`KanFibrationEndpointExtension`は元の終点・制限区間・基底区間を厳密に保つ延長を供給する。
`KanFiberwiseContraction`は実sectionと実収縮から基底上で定数な収縮を構成する。
`KanRetractionRightLifting`はこれらから全モノ射に対する右持ち上げとI.rlpを導く。
値宇宙は任意で補助モデル構造は不要。局所化の可逆性から実収縮への接続、
pushout後の単射性、一般augmentation・評価・最終小値化・F2は未完了。
検証：`scripts/check_kan_retraction_lifting.lean`、計画書§314。


### 両端点指定の相対延長と実pushout後の可逆性（§315）

`KanActualHomotopy`はKan値の商の等式を単一の実ホモトピーへ戻す。
`KanFibrationLocalizedLifting`はKan基底上の局所化で可逆なKan fibrationに全モノ射持ち上げを供給する。
`HomotopyClassesClosed`は元の閉随伴を区間ホモトピーとその商へ降ろす。
`KanRestrictionLifting`は局所化で可逆なモノ射の実内部Hom制限写像に全モノ射持ち上げを構成する。
`KanMonoRelativeHomotopy`は両端点と元の全制限区間を保つ延長を供給する。
`KanMonoPushoutEquivalence`は任意の実pushout後のテストの単射性・全単射性と可逆性を証明する。
補助宇宙のモデル構造は不要。逐次・超限貼り合わせ、一般augmentation・評価、最終小値化・F2は未完了。
検証：`scripts/check_kan_pushout_equivalence.lean`、計画書§315。


### 固定持ち上げ族と逐次・超限合成の閉性（§316）

`KanRelativeLifting`は実境界pushout-productへの持ち上げから全相対ホモトピーを構成する。
`KanTestLiftingClass`は局所化後可逆なモノ射を、モノ射と固定Kan右テスト族のllpとの共通部分に同定する。
`KanLocalizedTransfinite`は任意の小さい整列添字でこのクラスの超限合成閉性を証明する。
実連続図式と指定colimitから元の先頭射の可逆性を得る。ℕ列の専用入口もある。
補助モデル構造・Qのcolimit保存は不要。二つの骨格図式間の比較、一般augmentation・評価、
最終小値化・F2は未完了。
検証：`scripts/check_kan_transfinite_equivalence.lean`、計画書§316。


### 境界分解と固定境界上のpushout比較（§317）

`MonoRightLiftingContraction`は全モノ射右持ち上げから厳密sectionと基底上で定数な実収縮を構成する。
`MonoLocalizedFactorization`は値宇宙内の実関手的境界分解を供給し、右因子の局所化後可逆性を証明する。
`UnderMonoBrown`はモノ射の構造射を持つUnder対象間でBrownの議論をモデル不要で行う。
`KanPushoutComparison`は固定境界Aからの両構造射がモノ射なら、任意の基底変更後の一般比較が
局所化で可逆であると証明する。二つの実pushout間の指定比較にも適用できる。
比較射自身・基底変更射のモノ射性、補助モデル構造は不要。
境界も動く骨格比較、一般augmentation・評価、最終小値化・F2は未完了。
検証：`scripts/check_kan_pushout_comparison.lean`、計画書§317。


### 強変形レトラクトの実Kan引き戻し（§318）

`KanFibrationEndpointExtension.exists_from_zero`は元の始点・全制限区間・基底区間を保つ延長を供給する。
`KanPullbackDeformation`は強変形レトラクトを任意のKan fibrationに沿う元の実pullbackへ移す。
同じ部分対象を全区間で固定し、元の基底区間を保持する実retractionと収縮を構成する。
基底・全空間のKan性や補助モデル構造は不要。元の引き戻し射はQと任意のanodyne反転関手で可逆になる。
内部Homの前合成への移送、一般骨格比較、一般augmentation・評価、最終小値化・F2は未完了。
検証：`scripts/check_kan_pullback_deformation.lean`、計画書§318。


### 内部Homの実収縮とモデル不要の一般左固有性（§319）

`PrecompositionHomotopy`は元の区間を内部Homの前合成へ移し、後合成・定数区間との整合性を証明する。
`MappingPrecompositionRetraction`は垂直な収縮から前合成の像を全区間で固定する強変形収縮を構成する。
`PushoutInternalHomPullback`は元のpushoutの内部Homが実pullbackであることを証明する。
`HomotopyRetractionTests`は単位対象での後合成テストを元の前合成テストへ戻す。
`MonoRightPushoutEquivalence`は境界右クラスのモノ射に沿う実pushoutの可逆性を証明する。
`KanLocalizedLeftProper`は任意の局所化同値の、任意のモノ射に沿う実pushoutの可逆性を証明する。
比較射のモノ射性・元の対象のKan性・補助モデル構造は不要。
境界も動くcubeと骨格の比較、一般augmentation・評価、最終小値化・F2は未完了。
検証：`scripts/check_kan_localized_left_proper.lean`、計画書§319。


### 動く境界のpushout cubeと小さいcoproduct（§320）

`KanPushoutCube`は片側のattaching mapだけがモノ射である二つの実pushoutを比較する。
境界と二脚の元の比較が局所化同値なら、指定されたpushout間の比較も局所化同値になる。
他方のattaching map・比較射のモノ射性は不要。
`KanLocalizedCoproducts`は任意の局所化同値の小さい族のcoproductを扱い、
任意の実coproduct cocone間の指定比較にも結論する。
補助モデル構造は不要。逐次colimit比較、一般augmentation・評価、最終小値化・F2は未完了。
検証：`scripts/check_kan_cube_coproduct.lean`、計画書§320。


### 実逐次図式の相対分解とcolimit比較（§321）

`BoundaryRightColimit`は両端点の有限可呈示性から境界右クラスの実逐次colimit保存を証明する。
`SequentialBoundaryFactorization`は既に作った前段を保って相対pushoutを分解し、元のαをF→Z→Gへ分解する。
`SequentialFactorLiftingClasses`は各実相対後続因子を固定右テスト族のllpへ入れる。
`SequentialFactorLift`は前段の実liftを保持して全図式の自然なliftを構成する。
`KanSequentialColimitComparison`は源の接続射だけのモノ射性と各成分の局所化同値から、
元の逐次colimit比較、および指定された二つの実cocone間の元の比較の可逆性を証明する。
補助モデル構造・Qのcolimit保存は不要。
一般augmentation・評価の可逆性、最終小値化・F2は未完了。
検証：`scripts/check_kan_sequential_comparison.lean`、計画書§321。


### 一般augmentationの可逆性と両bar augmentation（§322）

`SkeletalDimension`は次元内の元の相対骨格と全体の実同型を供給する。
`CellularNaturalComparison`は小さいcolimit・モノ射を保存する二関手間の自然比較を標準単体で判定する。
境界・実cell pushout・全骨格の逐次colimitを使い、Qのcolimit保存は仮定しない。
`SimplexNerveEquivalence`は任意の元のXの単体圏nerve augmentationの可逆性と、
任意のanodyne反転関手への元のaugmentationをhomとする自然同型を構成する。
`OrdinaryBarAugmentationEquivalences`は元のbar評価squareの大きい・小さい両augmentationを可逆にする。
補助モデル構造は不要。row比較・評価の可逆性、自然な小値化・最終小さい厳密RMap・F2は未完了。
検証：`scripts/check_simplex_nerve_equivalence.lean`、計画書§322。


### 元のrow比較・bar評価・右脚全体の可逆性（§323）

`OrdinaryBarReferenceRows`は小さいraw単体圏上のreferenceとrowを、全ラベル・作用素を保つ自然変換で結ぶ。
`OrdinaryBarReferenceRowHomotopy`はこれを元のbar上の実ホモトピーへ移し、両端点の実因数分解を証明する。
`SimplexNerveEquivalence.map_localized_isIso`は元の単体圏nerve関手の可逆射保存を供給する。
`OrdinaryBarEvaluationEquivalence`は任意のcoherent systemに対する元のbar評価をQで可逆にする。
既存の還元を通し、rightとordinaryRightの自然変換全体もQで可逆になる。
源は任意のModelCategory、値側モデルは元の小さいSSetだけで足りる。
基底上の自然な小値化、最終小さい厳密RMap・F2は未完了。
検証：`scripts/check_ordinary_bar_evaluation_equivalence.lean`、計画書§323。


### 元のreplacement図式への自然比較と基底不変性（§324）

`OrdinaryBarMappingComparison`はmixed raw・right resolution・degree-zero replacementの
各小さい図式のliftとordinary barを、任意のanodyne反転関手の後で自然同型により結ぶ。
`OrdinaryBarBaseInvariance`は元の厳密barが両基底変数の弱同値を反転することを証明する。
`OrdinaryBarReplacementComparison`は既存のrefinement圏全体で元のreplacement図式と自然に比較し、
任意の元のpresentationの値・基底との比較も供給する。
源の関手的分解、projectionのfaithfulness・cofinality・厳密section、大きいSSetのモデル構造は不要。
自然な小値化・最終小さい厳密RMap・F2は未完了。
検証：`scripts/check_ordinary_bar_mapping_comparison.lean`、計画書§324。


### 小さいKan参照への実比較と基底射の小さい代表（§325）

`KanLocalizedRepresentatives`はモデル不要で、Kan対象へのanodyne局所化射を実単体写像で表し、
射の等しさを実区間ホモトピーで分類する。
`UniverseLiftLocalizedHom`はlift間の局所化Homのv-small性と元の小さい実写像による代表を供給する。
`OrdinaryBarSmallReference`は元のbar値から小さいKan参照値のliftへの実写像を構成し、
その像が元の比較同型の逆であることと、bar値間の局所化Homの小ささを証明する。
`OrdinaryBarSmallAction`は全基底射を小さい実写像で表し、単位・合成・元の比較squareを実ホモトピーで結ぶ。
両基底成分の弱同値は元の小さいモデルの弱同値へ移る。
単位・合成のホモトピーから厳密関手や全高次整合性が得られたとは主張しない。
自然な小値化・最終小さい厳密RMap・F2は未完了。
検証：`scripts/check_kan_localized_representatives.lean`、
`scripts/check_ordinary_bar_small_reference.lean`、計画書§325。


### 全パラメータ閉包と小さい実部分複体（§326）

`SmallParameterClosure`は小部分複体を全パラメータ作用に閉じ、その可算閉包の次数ごとのsmall性を証明する。
`SmallDominatedSubcomplex`は実ホモトピーによる小さい支配から、指定済み小部分複体を含む
小部分複体と、元の全ホモトピーの制限・包含の両側ホモトピー逆を構成する。
`SmallSimplicialValue`は次数ごとのsmall性を証明済みの値・任意の大きい基底上の図式を、
全作用を保って元の小さい宇宙へ縮小する。
`OrdinaryBarSmallSubcomplex`は元の比較をhorn unitへ厳密に延長し、Kan barの中の小部分複体と、
実際のSSet.{v}値からのQ可逆な実写像を構成する。
個別の閉包の全基底射に対する自然性、自然小値化・最終小さい厳密RMap・F2は未完了。
検証：`scripts/check_small_dominated_subcomplex.lean`、計画書§326。


### 全基底上の小部分図式の障害と小さい自然商（§327）

`AnodyneNonempty`はモデル不要でQ可逆射による頂点の非空性の検出を供給する。
`CodiscreteNerveExtension`はcodiscrete nerveへの写像を頂点関数で分類し、任意のmonoに沿う延長とKan性を証明する。
`SmallSubdiagramObstruction`は大きいがlocally smallな星形基底上に、全値がKanで
すべての基底射がQ可逆となる図式を構成する。
元の小さい宇宙の任意の図式からこの固定図式へ向かう自然同値は存在しないが、
逆向きには小さい定数点図式への実自然な商があり、その像はQで可逆となる。
したがって値ごとの小さい閉包から全基底に閉じる小部分図式を自動に推論しない。
最終の自然弱同値zigzag、小さい厳密RMap・F2は未完了。
検証：`scripts/check_small_subdiagram_obstruction.lean`、計画書§327。


### 安定な合同関係による小さい厳密商図式（§328）

`DiagramQuotient`は全基底射・全単体作用素に安定な次数ごとのSetoidから、実商図式と自然射影を構成する。
`SmallDiagramQuotient`は実商型のv-small性と元の商射の有限境界持ち上げ性から、
元のSSet.{v}値の厳密関手と、任意のanodyne反転関手で可逆となる全図式の自然比較を供給する。
元の値がKanなら小さい商値もKanであり、基底射のQ可逆性は元の小さいモデルの弱同値へ移る。
`StarDiagramSmallQuotient`は前回の星形例で全条件を証明し、同じ一般構成による実小値化を得る。
大きい値宇宙のモデル構造・小さい基底は不要。
bar用の合同関係と三条件、最終小さい厳密RMap・F2は未完了。
検証：`scripts/check_small_diagram_quotient.lean`、計画書§328。


### 全barの自然な通常の射ラベルと小さい粗商（§329）

`LocalizedHomDiagram`は一般モデル圏の通常の局所化のlocally small性から、
小さい通常の射集合とその定数単体集合の厳密図式を構成する。
`OrdinaryMappingClassLabel`は両増大射を反転した分数式を全raw単体に付け、全作用での自然性を証明する。
`OrdinaryBarMappingClasses`は全barの自然なラベル写像、raw包含での一致、π₀への自然な降下を供給する。
そのkernelは全作用で安定で、各実商型がv-smallとなり、小さい厳密な粗商図式を与える。
`DiagramQuotient`の一般kernel・単射比較・small性・降下APIも追加した。
SSetのモデル構造は不要。π₀写像の全単射性、粗商の高次情報の保存は主張しない。
高次を保つ自然な小値化・最終小さい厳密RMap・F2は未完了。
検証：`scripts/check_ordinary_bar_mapping_classes.lean`、計画書§329。


### 通常の射の全次数の代表と粗商の同定（§330）

`OrdinaryBarLabelSurjectivity`は任意のresolution pair・任意の次数でrawラベルの全射性を証明する。
全barのラベル・augmentationの次数ごとの全射性と、π₀ラベルの全射性も得る。
`DiagramQuotient`の全射kernel比較の一般同型判定により、粗商の明示的uliftは
通常の射の定数単体集合図式のuliftと自然同型であり、元の射影とラベルの因子分解も一致する。
源の通常のモデル公理だけでよい。π₀ラベルの単射性・高次を保つ自然な小値化・F2は未完了。
検証：`scripts/check_ordinary_bar_label_surjectivity.lean`、計画書§330。


### 元のbarの実際のπ₀と通常の局所化の射（§331）

`PiZeroConstant`は離散単体集合への写像をπ₀上の関数で分類し、離散値のKan性とホモトピーの剛性を証明する。
`PiZeroLocalization`はKanテストから、anodyne局所化で可逆な実写像の実際のπ₀全単射を得る。
どちらにもSSetのモデル構造は不要である。
`OrdinaryRawLabelHomotopy`は同じHo(C)ラベルを持つraw頂点を、sourceの良い円筒とtargetの退化から実辺で結ぶ。
`OrdinaryBarPiZero`はentryの局所化後の可逆性とπ₀全単射を証明し、
元のbarのπ₀とHom_H(QX,QY)の自然な全単射、そのraw包含上の分数式、π₀のv-small性を得る。
源は任意のモデル圏、モデル構造を使うSSetは元の小さい宇宙だけでよい。
barのπ₀単射性の残項目は解消。高次を保つ自然な小値化・最終小さい厳密RMap・F2は未完了。
検証：`scripts/check_ordinary_bar_pi_zero.lean`、計画書§331。


### ラベル保存商の実際のπ₀と縮小への移送（§332）

`UniverseLiftPiZero`はモデル不要でπ₀(ulift X) ≃ π₀(X)と全実写像での自然性を証明する。
`OrdinaryQuotientPiZero`はHo(C)ラベルを保存する任意の安定なbar商について、
商射影と降下したラベルの実際のπ₀全単射を証明する。
各商型のv-small性があれば、元のSSet.{v}内の小さい厳密商図式のπ₀からHo(C)の射への
実同値、両変数の自然性、元のbar比較との因子分解の一致が得られる。
π₀については有限境界持ち上げ性や高次保存を仮定しない。
高次を保つ合同関係の存在・自然小値化・最終小さい厳密RMap・F2は未完了。
検証：`scripts/check_ordinary_quotient_pi_zero.lean`、計画書§332。


### 実Kan barへの一意な自然ラベルの延長（§333）

`DiscreteKanExtension`はanodyne拡張に沿う離散値写像の一意な実延長を構成し、
任意の大きい基底上で全自然変換を値ごとの実Kan置換へ一意に延長する。モデル構造は不要である。
`OrdinaryKanBarMappingClasses`は厳密な大きいKan bar、元のbarからの自然単位、
全Ho(C)ラベルの自然で一意な延長、kernelの各実商型のv-small性を供給する。
元の小さいSSetモデルだけでπ₀同値・全基底自然性・元のbar比較との一致と両変数の弱同値不変性も得る。
高次を保つ合同関係の存在・自然小値化・最終小さい厳密RMap・F2は未完了。
検証：`scripts/check_ordinary_kan_bar_mapping_classes.lean`、計画書§333。


### Kan barの有限境界商からの全出力（§334）

`DiscreteLocalizedExtension`は局所化後可逆な全自然比較に沿って、離散値比較を一意に降下する。
`OrdinaryKanBarQuotient.QuotientData`は実Kan bar上の安定な合同関係・実商型のv-small性・有限境界持ち上げ性を記録する。
この未構成の入力を供給した場合、小さい厳密なcurry、Kan性、元のbarとの全自然比較、
任意のanodyne反転関手での全図式同型、異なる入力間の比較が得られる。
ラベル保存は入力から導く。元の小さいSSetモデルだけで弱同値不変性・実π₀同値・全基底自然性・
元のbar比較との一致も得る。大きいSSetモデルは不要。
QuotientDataの一般の存在・無条件の最終RMap・F2全体は未完了であり、条件付きの出力とは区別する。
検証：`scripts/check_ordinary_kan_bar_quotient.lean`、計画書§334。


### 全presentation圏上の実small kernelと境界証明（§335）

`SmallTargetKernelQuotient`は自然な小さいKan参照への局所化後可逆な比較を値側で因子分解し、
anodyne拡張上の実kernel、実商型のv-small性、有限境界持ち上げ性を構成する。
`PresentationKernelQuotient`は既存の全presentation上の実span左射に適用し、
合同関係と三条件を実際に供給して、小さいKan値の厳密図式と自然な弱同値比較を得る。
ここまではSSetのモデル構造が不要。元の小さいモデルだけで基底barへの自然比較と弱同値不変性も得る。
基底は全resolution presentation圏であり、Cᵒᵖ × Cへの降下・最終小さい厳密RMap・F2は未完了。
射影のsectionやcofinalityを仮定せず、固定Kan bar上のQuotientDataの存在とも区別する。
検証：`scripts/check_presentation_kernel_quotient.lean`、計画書§335。


### 小さいKan値の通常圏的な基底降下（§336）

`SmallKanHomotopy`は小さいKan値とHom宇宙vの区間ホモトピー類を持つ通常の圏を構成し、
任意の大きいanodyne局所化への完全忠実な実現を供給する。SSetモデルは不要である。
`OrdinaryBarHomotopyDescent`は元のCᵒᵖ × C上のこの通常圏への厳密関手、元のbarとの実現後の全自然同型、
両変数の弱同値反転、§335のpresentation商との通常圏内の全自然同型を得る。
同じ基底射のpresentation比較の像は同じホモトピー類となり、射影のsection等は仮定しない。
元の小さいSSetモデルだけを使う。実写像を射とするSSet値の厳密化・高次整合性・最終RMap・F2は未完了。
検証：`scripts/check_ordinary_bar_homotopy_descent.lean`、計画書§336。


### 全パラメータ写像空間の宇宙比較（§337）

`SimplexParameterHom`はn単体K ⊗ Δ[n] → Pを持つ実写像空間、native内部Homとの単体同型、
両変数の厳密なbifunctor、同じパラメータでの合成・単位・結合、Kan対象への写像空間のKan性を供給する。
`UniverseLiftParameterHom`はこの全空間の明示的ulift比較、全bifunctorの自然同型、
族の合成squareと単位の保存、およびnative内部Homのulift比較を証明する。SSetモデルは不要。
受入例で実際の小さいbar参照値間にも適用した。
元の基底作用の全高次整合性・SSet値の厳密な降下・最終RMap・F2は未完了。
検証：`scripts/check_universe_lift_parameter_hom.lean`、計画書§337。


### 厳密な参照retractと全パラメータの相対射選択（§338）

`LocalizedRelativeChoice`は局所化後可逆なmonoに沿うKan対象への実延長と、
その選択空間の全monoに対するパラメータ延長・有限境界充填をモデル不要で供給する。
`OrdinaryBarRetractSystem`は各Kan bar値をmono等価拡張し、小さい参照への厳密なretractと垂直収縮を得る。
各基底射の実延長空間、単位・ambient合成の点、任意の大きい族の小さい写像空間への移送と指定族の保持、
単位の正規化および中間retractの収縮による実合成ホモトピーも構成した。
対象ごとのenlargementを基底上の関手とは仮定しない。全高次の組立て・厳密なSSet値降下・最終RMap・F2は未完了。
検証：`scripts/check_ordinary_bar_retract_system.lean`、計画書§338。


### section上で固定した収縮と両単位の定数合成比較（§339）

`MonoRightLiftingRelativeHomotopy`は、両端点・部分対象上の区間・射影後の区間全体を保持する
相対持ち上げをモデル不要で構成する。厳密なsectionを持つ全mono右持ち上げ射は、
sectionの像上でも一定な垂直収縮を持つ。実際のbarの収縮もこの条件を満たすよう強化した。
`OrdinaryBarRetractTransfer`は任意のambient実射の移送・実単位と合成比較を構成し、
左右どちらかが恒等射なら比較区間全体が定数になることを、元の小さい宇宙でも証明する。
選んだ基底作用の全高次整合性・厳密なSSet値降下・最終RMap・F2は引き続き未完了。
検証：`scripts/check_strong_retract_transfer.lean`、計画書§339。


### 任意長のambient鎖のcube族と途中の面（§340）

`ParameterComposition`と`RetractChainFamily`は、任意の共通パラメータを保つ合成、
任意長の実ambient鎖の収縮付き評価・移送、全パラメータ置換をモデル不要で構成する。
任意のprefix/suffix内で、0面は隣接実射の合成、1面は前後の移送の合成になる実等式を証明した。
`ParameterCube`は実有限区間積と任意位置の面・座標公式を供給する。
`OrdinaryBarChainFamily`は全次数の実cube族と面の置換公式を元の小さい宇宙で構成し、
低次数が既存の移送射・選択済みの全二射比較区間と一致することも証明する。
基底作用の高次選択・恒等射の内部退化・厳密なSSet値降下・最終RMap・F2は未完了。
検証：`scripts/check_finite_chain_cube.lean`、計画書§340。


### 相対延長空間全体の合成と選択済み合成射の比較（§341）

`RelativeChoiceFamilies`は、選択空間への任意パラメータ射と、全境界を保つ実族との同値を供給する。
`OrdinaryBarChoiceComposition`は元の基底作用に沿うchoicesの全族を合成し、実SSet合成、
全パラメータ自然性、基底等式の明示的relabel後の単位・結合則を証明する。
選択済みの二点の合成は既存のcompositePointと等しく、action(f ≫ g)と実合成action(f) ≫ action(g)の
間には元のbar境界を全区間で固定するcompositeComparisonを構成した。大きいSSetモデルは不要。
全高次の選択・内部の恒等射の退化・厳密なSSet値降下・最終RMap・F2は引き続き未完了。
検証：`scripts/check_relative_choice_composition.lean`、計画書§341。


### パラメータ付き選択圏と厳密な単体的図式（§342）

`ParameterCategory`は共通パラメータTを持つ実族の圏と厳密なパラメータ置換を供給する。
`OrdinaryBarChoiceCategory`は基底射と全相対延長族を保持する実際の圏、基底への射影、
ambient値への厳密な評価、全パラメータ置換と両関手の可換squareを構成する。
任意monoの制限は充満で、指定済みの射の族全体が元の基底射の上で延長できる。
基底射影も充満だが、faithful・cofinal・厳密なsection付きとは主張しない。
`OrdinaryBarChoiceSimplicialCategory`は標準単体をパラメータとする実Cat値関手を構成する。
元の基底上の小さい厳密なSSet値降下・移送後の内部単位条件・最終RMap・F2は未完了。
検証：`scripts/check_parameter_choice_category.lean`、計画書§342。


### 動く選択圏の射列と小さい鎖移送の接続（§343）

`RetractChainFamily`は各射が全パラメータで動くfamilySnocへ一般化し、固定射のsnocも保持する。
任意位置の0面は動く族の合成、1面は前後の移送の合成になる実等式を一般化した。
`OrdinaryBarChoiceChainTransfer`は実際の選択圏の任意長のpathをこの鎖へ入力し、
0面で選択圏の実合成が現れることと、全射・全収縮座標の同時置換との交換を証明する。
全pathを元の小さい宇宙の実族へ戻し、空path・一射・0面/1面・全パラメータ自然性も検証した。
元の基底上への厳密な降下・内部の恒等射の退化・最終RMap・F2は引き続き未完了。
検証：`scripts/check_moving_choice_chain_transfer.lean`、計画書§343。


### 基底射の離散空間への全mono右持ち上げ性を持つ選択射空間（§344）

`DiscreteFiber`・`DiscreteFamily`・`DiscreteFamilyLifting`は離散ラベル上の実ファイバー、
実total空間とそのファイバー同型、全パラメータの分解・再構成をモデル不要で供給する。
各ファイバーの全mono延長性から、射影全体の全mono右持ち上げ性と局所化後可逆性を証明した。
`OrdinaryBarChoiceMappingSpace`は全次数の実選択圏の射からSSet射空間を構成し、
基底射の離散空間への射影・全mono右持ち上げ性・Kan性・局所化後可逆性、
厳密な合成・単位と射影による保存を証明する。最終RMapそのものではない。
射影の厳密なsectionやcofinalityは主張しない。小さいSSet値降下・移送後の内部単位・最終RMap・F2は未完了。
検証：`scripts/check_choice_mapping_space.lean`、計画書§344。


### 自由図式全体の相対パラメータ延長（§345）

`OrdinaryBarFreeDiagramExtension`は任意quiver上の自由図式をmono U → Tに沿って延長し、
制限後に元の関手全体へ戻る実等式と、基底への射影の一致を証明する。
基底の自由図式だけから選択圏への実関手を構成し、元の全基底グラフにもfreeCoverを適用した。
`OrdinaryBarRelativeFreeDiagramExtension`はT上で指定済みの生成射と、
それらからなる任意長のpathを固定したまま自由図式を延長する。
元の源モデルの自由性、関係付き図式の自動的な持ち上げ、基底上の厳密なsectionは要求・主張しない。
高次の組立て・小さいSSet値降下・移送後の内部単位・最終RMap・F2は未完了。
検証：`scripts/check_relative_free_diagram_extension.lean`、計画書§345。


### 自由path余モナドとfreeCoverの最初の二面・退化（§346）

`FreePathResolution`は通常の関手の自由pathへの移送、path合成の余単位、生成射の二重化、
それらの自然性・両余単位則・余結合則をモデル不要で証明し、実Mathlib Comonadを構成する。
`OrdinaryBarFreeResolutionFaces`は元の基底の二重自由圏からfreeCoverへの二つの面を構成し、
基底への射影の一致と、退化を前合成したとき両方が元のfreeCoverへ戻る実等式を証明した。
二面そのものの相対比較、全次数の単体的分解、小さいSSet値降下、最終RMap・F2は未完了。
検証：`scripts/check_free_path_comonad.lean`、計画書§346。


### 全次数の余モナド分解（§347）

`ComonadResolutionOperators`は任意の余モナドの面・退化の六関係式とaugmentationの
可換性を全次数で証明する。`ComonadResolutionPresentation`は実際に関係式の商へ降下し、
`SimplexCategoryGenRelᵒᵖ`上の実関手と定値対象への実自然変換を構成する。
`FreePathResolutionPresentation`は自由path余モナドへ適用し、独立した対象・Hom宇宙の
任意の圏への実射影と、その全添字射に対する可換性を与える。モデル構造は不要。
通常の`SimplexCategory`との比較は未完了であり、この段階では通常の単体的分解の完成や、
元の基底上の厳密な小さい`RMap`の完成を主張しない。
受入検証は`check_comonad_resolution_presentation`（54宣言・3モジュール）。


### 単体圏の表示の同値と通常の単体的分解（§348）

`CategoryTheory/Simplex/PresentationDegeneracies`と`PresentationFaces`は、退化と面の
標準形を実単調写像から復元する。`PresentationEquivalence`は標準関手のFull・Faithful・
EssSurj・IsEquivalenceを証明し、次数を保つ実逆関手と両合成の恒等を与える。
これにより、§347で残った通常の単体圏との比較は解消した。
`ComonadSimplicialResolution`は任意の余モナドの実SimplicialObjectとaugmentationを構成し、
`FreePathSimplicialResolution`は独立した対象・Hom宇宙の任意の圏へ適用する。
モデル構造は不要。選択圏への全次数の整合的な持ち上げと、元の基底上の小さい厳密なRMapは残る。
受入検証は`check_simplex_presentation_equivalence`（92宣言・5モジュール）。


### 自由分解の最初の相対比較（§349）

`OrdinaryBarFreeDiagramHomotopy`は任意のP上の二つの自由図式を、指定生成射を
区間全体で固定して比較する。`OrdinaryBarFreeResolutionComparison`は元の基底の
実freeCoverの二面へ適用し、両端の一致、退化像全体の一定性、基底射影の可換性を
関手の実等式で証明する。任意のPを保持し、源への追加仮定や大きいSSetモデルは不要。
異なるPごとの選択の自然性、全次数の高次整合性、最終的な小さい厳密なRMapは残る。
受入検証は`check_relative_free_resolution_comparison`（69宣言・2モジュール）。


### 実三辺の頂点・退化の重なり（§350）

`FreePathResolutionDegreeTwo`は元の圏に直接作用する次数2の三面・二退化と全関係式を与える。
`OrdinaryBarFreeTriangleBoundary`は既存の比較を三面へ前合成し、任意Pでの実三辺について、
六端点、三頂点の重なり、六つの退化制限、二重退化の共通像での一定性を関手の実等式で証明する。
P × ∂Δ²上の実境界関手、退化の生成射像の交差全体の特徴付け、相対充填は残る。
受入検証は`check_free_triangle_boundary`（49宣言・2モジュール）。


### 三辺を実際の境界図式へ貼り合わせる（§351）

`BoundaryTensorGluing`は任意のパラメータを持つ全次数の境界族の貼り合わせと外延性を与える。
`OrdinaryBarChoiceTriangleGluing`は端点等式から基底射の付け替えも導き、元の三選択射へ戻る
実境界族を作る。`OrdinaryBarFreeTriangleGluing`は§350の実三辺へ適用し、
Paths³(Cᵒᵖ × C) → Choice(P × ∂Δ²)という実境界関手と、全三面への制限の実等式を構成する。
退化を保持するΔ²相対充填、全次数の整合性、小さい厳密なRMapは残る。
受入検証は`check_free_triangle_gluing`（50宣言・3モジュール）。


### 両退化を固定する実三角形充填（§352）

`OrdinaryBarChoiceBoundaryExt`は全次数の境界制限の同時忠実性を与える。
`FreePathDegeneracyImage`は二つの退化生成射像の交差全体を特徴付ける。
`TriangleDegeneracyParameters`と`OrdinaryBarFreeTriangleDegeneracy`は指定する退化三角形の
境界一致・交差上の値の一致を証明する。`OrdinaryBarFreeTriangleFiller`は実Prescribedを作り、
境界全体・三面・両退化像全体を厳密に保つP × Δ²上の充填関手を構成する。
次数2の相対充填は完了。全次数の帰納構成と、最終的な小さい厳密なRMapは残る。
受入検証は`check_relative_free_triangle_filler`（63宣言・5モジュール）。


### 全次数の退化生成射像の交差（§353）

`CategoryTheory.Quiver.PathIntersections`は、
辺の共通原像から任意長pathの共通原像を作る一般定理を与える。
`FreeGeneratorDegeneracies`は全次数の退化の単射性・関係式・交差の一意な共通原像を証明する。
`FreeGeneratorCategories`は生成射表示を実自由path余モナドの反復へ接続し、
全退化関手との比較等式と実生成射像の交差定理を与える。三モジュールともモデル構造を仮定しない。
全次数の相対充填の帰納構成と、最終的な小さい厳密なRMapは残る。
受入検証は`check_all_degree_free_generators`（58宣言・3モジュール）。


### 全次数の境界貼り合わせと全退化を保持する相対延長（§354）

`FreeGeneratorLatchingValues`は二重退化の整合式から全退化像上の値を一意に貼り合わせる。
`OrdinaryBarChoiceBoundaryGluing`は各面の重なりから基底射の一致も導き、元の各面へ戻る実境界射を作る。
`OrdinaryBarFreeBoundaryGluing`は任意quiver上で全次数の実境界関手と全面制限の等式を構成する。
`OrdinaryBarFreeDegeneracyExtension`は実Prescribedと相対延長を作り、境界・射影・全退化関手を保持する。
元の自由分解からの全次数の帰納入力の構成と、小さい厳密なRMapは残る。
受入検証は`check_free_latching_extension`（50宣言・4モジュール）。


### 実自由分解からの全次数の境界・退化指定値（§355）

`FreeGeneratorFaces`は実余モナドの面との比較、固定対象の逆順面、全面の重なりを証明する。
`OrdinaryBarFreeResolutionBoundary`は低次数の面等式から重なりを導き、次の実境界関手と全面制限を作る。
`OrdinaryBarFreeResolutionDegeneracyValues`は低次数Fをσで引き戻し、低次数の退化等式から
交差全体の整合性を導く。全退化像上の指定値を作り、実引き戻し図式との一致も証明する。
指定退化値の境界制限の一致と、全次数の帰納構成、小さい厳密なRMapは残る。
受入検証は`check_free_resolution_boundary_data`（48宣言・3モジュール）。


### 全次数の境界退化一致と整合的反復（§356）

`FreeGeneratorMixedOperators`と`ReversedSimplexParameters`は源・パラメータの全混合式を証明する。
`OrdinaryBarFreeResolutionMixedFaces`と`OrdinaryBarFreeResolutionDegenerateBoundary`は、
低次数の面・退化等式から指定退化図式の全面と境界全体の一致を導く。
`OrdinaryBarFreeResolutionStep`は実相対充填で次の関手と全面・全退化等式を作る。
`OrdinaryBarFreeResolutionTower`は整合的な初期二次数Seedから全次数の関手と厳密な等式を反復構成する。
既存のfreeCover・comparisonから実Seedへの接続、Δの図式への束ね、小さい厳密なRMapは残る。
受入検証は`check_free_resolution_step`（87宣言・6モジュール）。


### 元の源モデルからの全次数の整合的選択（§357）

`OrdinaryBarFreeResolutionSeed`はHomだけのULiftをdown・自由pathの反復で既存freeCover・comparisonへ
接続し、実Seedと面・退化等式を構成する。
`OrdinaryBarFreeResolutionChoices`はこのSeedから全次数の選択関手を作り、
全ての面・退化等式と、元の基底への射影が実augmentationへ等しいことを証明する。
利用者にSeedや高次整合性の仮定は要求しない。任意の既存Pと独立宇宙の一般源モデルに適用できる。
通常のΔの図式への束ね、自然比較と元の基底への降下、小さい厳密なRMapは残る。
受入検証は`check_actual_free_resolution_choices`（38宣言・2モジュール）。


### 通常のΔ上の実自然変換とaugmentation（§358）

`CategoryTheory.Simplex.Naturality`は全面・全退化の交換から任意の単体写像での自然性を導く。
`OrdinaryBarParameterChoiceCategory`はP × Δⁿの選択圏と元の基底への射影を実simplicial図式にする。
`OrdinaryBarFreeResolutionNaturalChoice`は既存自由分解の反転から選択図式への実自然変換choicesを構成する。
基底射影との合成は、既存自由分解のaugmentationそのものに自然変換全体で厳密に等しい。
実ambient族への適用、移送と自然比較、元の基底への降下、小さい厳密なRMapは残る。
受入検証は`check_free_resolution_natural_choices`（32宣言・3モジュール）。


### 全次数の実ambient作用と小さい内部Homへの移送（§359）

`OrdinaryBarFreeResolutionAction`は実choicesをevaluationへ合成し、任意の単体写像との交換と
合成・恒等の保持、既存augmentationへの基底射影を証明する。
`OrdinaryBarFreeAmbientFamilies`は元の対象をliteralな端点にした実ambient族を作り、
厳密な合成・恒等・全面・全退化等式を与える。
`OrdinaryBarFreeTransferredFamilies`は小さい対象モデルへ移送し、恒等族と全面・全退化を保持する。
移送族は小さい内部Homの宇宙持ち上げに値を取る。移送後の厳密な合成保持は主張しない。
有限射列の収縮族への接続、自然比較、元の基底への降下、小さい厳密なRMapは残る。
受入検証は`check_free_resolution_action`（53宣言・3モジュール）。


### 全次数の有限射列の収縮族と小さい移送族（§360）

`OrdinaryBarFreeChainTransfer`は実source射列と独立な収縮パラメータを実chainへ写し、
任意の全パラメータ代入・全面・全退化と交換する。
任意のprefix・suffixを含む零面での実source合成、一面での移送合成、空列・単一射、
全零での任意長の実合成への一致を証明する。
`OrdinaryBarSmallFreeChainTransfer`は小さいパラメータへ引き戻し、これらの族と境界式を
nativeなSSet.{v}の実写像へ降ろす。
内部恒等の消去と高次整合性、自然比較、元の基底への降下、小さい厳密なRMapは残る。
受入検証は`check_free_chain_transfer`（55宣言・2モジュール）。


### 強い収縮による恒等消去と吸収則（§361）

`RetractChainUnits`はモデル構造不要の一般強収縮について、任意パラメータの先頭・末尾恒等消去と
一の左右吸収則、内部恒等の二つの零境界での消去を証明する。
`OrdinaryBarFreeChainUnits`は全次数の実自由分解の恒等射へ適用し、nativeな小さい族の両端消去も与える。
元の収縮に半群則は仮定しない。任意の二収縮の間での内部恒等消去は残る。
次は有限語の収縮パラメータと簡約を検証し、内部恒等を隣接語の連結として扱う構成を調べる。
自然比較、元の基底への降下、小さい厳密なRMapは未完了。
受入検証は`check_free_chain_units`（20宣言・2モジュール）。


### 有限語の収縮パラメータ対象と区間比較（§362）

`SegmentWords`は端点を単位・吸収元へ簡約した有限語と一般の評価・写像を構成する。
`WordSegment`は同じ宇宙の実SSet、結合積・単位・吸収元、Δ¹からの実写像と明示的収縮を与える。
`WordSegmentComparison`は終射とΔ¹からの写像が、任意のanodyne反転関手と実anodyneQで同型になることを証明する。
三モジュールともモデル構造は不要。区間の0はモノイド単位1、区間の1は吸収元0へ写る。
既存の強い収縮への語の作用と内部恒等消去への接続、元の基底への降下、小さい厳密なRMapは残る。
受入検証は`check_word_segment`（59宣言・3モジュール）。


### 強い収縮の実語作用と厳密な連結則（§363）

`RetractEndomorphisms`は切断を固定し射影上にある自己写像の零付きモノイドと語の交換則を与える。
`WordRetractionAction`は任意の強い収縮を実際のSSet語作用へ延長し、全単体写像との交換、
文字への制限、積・単位・吸収元・射影・切断との整合性を証明する。モデル構造は不要。
`OrdinaryBarWordContraction`は既存の実bar縮約系へ適用し、任意パラメータ族の合成を語の連結と同定する。
小さいSSetのモデル構造だけを用いる。内部恒等消去への全射列での接続、自然比較、
元の基底への降下、小さい厳密なRMapは残る。
受入検証は`check_word_retraction_action`（71宣言・3モジュール）。


### 任意語パラメータによる全有限列の内部恒等消去（§364）

`WordRetractChainFamily`はモデル構造不要の語パラメータ列と評価・移送を構成し、
任意の前後列の間の内部恒等を、任意の隣接二語の連結で消去する。
`OrdinaryBarWordChainFamily`、`OrdinaryBarFreeWordChainTransfer`、
`OrdinaryBarSmallFreeWordChainTransfer`は全次数の実自由分解とnativeな小さい族へ適用し、
全面・全退化・代入・両境界・内部恒等消去を保持する。文字への制限は元の区間族に一致する。
語列の生成関係によるsimplicialな射対象と合成・単体作用、元の基底への降下、
小さい厳密なRMapと自然比較は残る。
受入検証は`check_word_chain_transfer`（155宣言・4モジュール）。


### 生成関係による実simplicial語圏と小さい次数別評価（§365）

`CategoryTheory/Presentation/RetractWords`はambient/small頂点と元の射・語・切断・射影から
八種類の明示的関係で商の圏、small full subcategory、元の圏へのaugmentationを構成する。
`RetractWordRealization`と`RetractWordMap`は任意の圏への評価、source・語パラメータの変更と
strictな恒等・合成則を与える。評価kernelで割るものではない。
`WordPresentationDiagram`は実Cat値simplicial図式、実SSetのHomと合成・結合・単位則を与える。
`WordPresentationRealization`は既存の強い収縮で全生成関係を検証し、次数ごとの実評価を構成する。
`OrdinaryBarWordPresentation`は全自由分解次数に適用し、元の小さいType v値の実関手と
既存の実移送族への一致を与える。
全商射での評価の単体自然性、自由分解方向の交換、augmentationの比較・弱同値、
元の基底への小ささを保つ降下と小さい厳密なRMapは残る。
受入検証は`check_retract_word_presentation`（190宣言・6モジュール）。


### 全商射の単体自然性とnativeな小さい値への作用（§366）

`CategoryTheory/Quiver/PathNatTrans`は生成辺の自然性から道の圏の実自然変換を構成する。
`WordPresentationNaturality`は実source族・語作用・切断・射影の自然性を道と商へ延長し、
任意の商射の評価が任意の単体写像と交換することを証明する。
`WordPresentationAction`はモデル構造不要で実SSetの評価写像を組み立て、
共有パラメータによる作用族の恒等・合成・代入則を与える。
`OrdinaryBarWordAction`は全自由分解次数へ適用し、任意の商射族をnativeな小さい
SSet.{v}の実写像へ写し、恒等・合成・代入を保持する。
自由分解方向の全面・全退化との接続、augmentationの比較・弱同値、
元の基底への小ささを保つ降下と小さい厳密なRMapは残る。
受入検証は`check_word_presentation_action`（22宣言・4モジュール）。


### source関手性と全自由分解作用素での実評価交換（§367）

`PathFunctorExt`と`RetractWordExt`は道と商の実関手の生成辺による外延性を与える。
`RetractWordPullback`は任意のsource functor・零付きモノイド準同型による実評価の引き戻しと
実商関手による評価の一致を証明する。
`WordPresentationSourceMap`は語Homの実SSet写像と単体自然性、恒等・合成・単位の保持を与える。
`OrdinaryBarWordEvaluationOperators`は全自由分解次数・全面・全退化・全パラメータの
実評価関手の交換を全商射について証明する。
`OrdinaryBarWordActionOperators`はnativeな小さいSSetの任意商射族で同じ交換則を与える。
両単体方向を持つ実図式とaugmentationの組立て、比較の弱同値、元の基底への小ささを保つ降下、
小さい厳密なRMapは残る。
受入検証は`check_word_source_operators`（24宣言・6モジュール）。


### 実Cat関手・両単体図式・対角augmentation（§368）

`WordPresentationCat`は語圏をCat上の実関手にまとめ、語パラメータ変更を自然変換として与える。
`RetractWordAugmentation`はaugmentationとambient source functorの変更則を証明する。
`WordPresentationAugmentation`は語方向とsource方向に自然なaugmentation、実二重図式と
対角図式からのaugmentationを構成する。
`WordPresentationSection`はambient埋め込みの実切断と対角augmentationの分裂を証明する。
`OrdinaryBarWordResolution`は既存の通常のΔᵒᵖ上の自由道分解へ適用し、全混合単体写像の交換、
元の基底への実augmentationと射影の自然性を与える。全五モジュールともモデル構造は不要。
既存実評価の通常の図式・対角への移送、比較の弱同値、元の基底への小さいstrictification、
小さい厳密なRMapは残る。ambient分裂からsmall切断や弱同値は主張しない。
受入検証は`check_word_resolution_diagram`（56宣言・5モジュール）。


### 対象を固定した通常の自由分解と小さい対角評価（§369）

`OrdinaryBarFixedSource`は既存の次数比較とaugmentationから、任意の単体作用素の対象写像が
元のCᵒᵖ×Cの恒等となる実simplicial図式を構成する。
`OrdinaryBarFixedChoices`と`OrdinaryBarFixedWordEvaluation`は既存choiceとambient評価を移し、
全単体写像での語評価交換を全商射について証明する。
`OrdinaryBarFixedWordResolution`は既存対角図式と自然同型なliteral表示、実Hom SSetと
合成・恒等・結合・単位則を与える。
`OrdinaryBarDiagonalEvaluation`は標準恒等単体を代入し、任意の対角語射族をnativeな小さい
SSet.{v}の実写像へ移す。恒等・合成・代入を保持し、二方向の実自然性を使う。
内部Homへの対角作用、augmentationの比較・弱同値、元の基底への小さいstrictification、
小さい厳密なRMapは残る。
受入検証は`check_diagonal_word_evaluation`（62宣言・5モジュール）。


### 全対角作用と小さい内部Homへの写像（§370）

`OrdinaryBarDiagonalEvaluation.evaluation_naturality`は任意の対角語射とPの単体で全自然性を与える。
`OrdinaryBarDiagonalAction`は全パラメータP⊗Hom_diagの実SSet作用と任意の大きい作用族を構成し、
恒等・合成・代入、既存の小さい評価へのlowerの一致を証明する。
`ClosedParameterComposition`はcurryが共有パラメータの合成とMathlib標準内部Hom合成を対応させると証明する。
`OrdinaryBarDiagonalClosedAction`は小さい内部HomのULiftに値を取る全mappingと、その実作用への復元を与える。
nativeな小さい内部Hom族の標準単位・合成・代入則も証明した。
closedIsoと小さいcurryの接続、全mappingの持ち上げた標準合成との整合性、
augmentationの弱同値、元の基底への小さいstrictificationと小さい厳密なRMapは残る。
受入検証は`check_diagonal_closed_action`（18宣言・3モジュール）。


### 実closedIsoと全対角mappingの標準合成・単位（§371）

`UniverseLiftClosedCurry`は既存closedIsoと小さいcurry・lowerTensor・標準評価の交換を証明する。
`UniverseLiftClosedComposition`は標準内部Hom合成・単位の実持ち上げとの交換を与える。
ともにモデル構造不要のSSet一般論である。
`OrdinaryBarDiagonalClosedCompatibility`は全mappingを小さいパラメータに制限すると
nativeFamilyの持ち上げそのものになることと、任意の大きいパラメータで標準合成・単位を保つことを証明する。
augmentationのHom比較と弱同値、元の基底への小さいstrictification、小さい厳密なRMapは残る。
受入検証は`check_diagonal_closed_compatibility`（35宣言・6モジュール）。


### 全対角Homの実ホモトピー比較とaugmentation（§372）

`RetractWordIdentities`と`OrdinaryBarDiagonalAmbientHom`は全単体作用に自然なsection・projection・
word、ambient Hom、small頂点間Homへのtransferと逆向きinclusionを構成し、small側の実分裂を証明する。
`OrdinaryBarDiagonalHomRetraction`は両端に動くwordを挿入する全次数ホモトピーから、任意のanodyneを
可逆にする関手でのHom比較同型を与える。補助宇宙のモデル構造は不要である。
`OrdinaryBarFixedAugmentation`と`OrdinaryBarDiagonalHomAugmentation`は元の基底の定数Homへの
実augmentation、両比較との可換性、small augmentationの合成・単位保存を構成する。
small augmentationの局所化後の可逆性はambient側の可逆性に帰着できる。
augmentation自体の可逆性、元の基底への小さいstrictification、小さい厳密なRMapは残る。
ここでsmall Homはsmall頂点間の補助宇宙のHomであり、SSet.{v}への縮小を主張しない。
受入検証は`check_diagonal_hom_augmentation`（54宣言・5モジュール）。


### 分裂頂点のない表示とambient Homの実同型（§373）

`AmbientWords`は元の射と各対象でのword作用だけで生成する商圏とその評価を構成する。
`AmbientWordKaroubi`と`AmbientWordComparison`はsmall頂点をword(0)の冪等元として復元し、
既存RetractWordsのambient Homと新表示のHomの実同値・両逆則を証明する。
`AmbientWordMap`は元の関手・word準同型との交換を全商射について与える。
`OrdinaryBarAmbientWordComparison`は実対角SSet同型、全単体作用の実関手での計算、
元の基底へのaugmentationを構成し、small augmentationの可逆性を新表示へ帰着する。
すべてモデル構造不要。augmentationの弱同値と小さい厳密なRMapは残る。
受入検証は`check_ambient_word_comparison`（137宣言・5モジュール）。


### 自由道圏上の実正規形と固定次数のaugmentation（§374）

`WeightedPaths`と`WeightedPathMaps`は各頂点に重みを置く道の圏、任意の重み置換、forget・fillを与える。
`WeightedPathRealization`はAmbientWords(Paths G,M)の実商射と重み付き道の実同値・両逆則を証明する。
`AmbientWordAugmentation`と`WeightedPathParameterMap`は実augmentationがforgetに一致することと、
word準同型が重み置換に一致することを証明する。
`WeightedWordHom`は全重みを動かす実ホモトピーを構成し、projectionのanodyne局所化後の可逆性を得る。
`FreeWordHom`は実商圏HomとのSSet同型を通じて、実augmentationの局所化後の可逆性を証明する。
`OrdinaryBarFixedRowWordHom`は既存の任意の固定外側次数へ適用する。すべてモデル構造不要である。
行ごとの比較から対角への接続、外側のaugmentation、小さい厳密なRMapは残る。
受入検証は`check_free_word_hom`（165宣言・8モジュール）。


### 実word行図式と対角anodyne保存（§375）

`AmbientWordFunctoriality`は元の関手・word準同型の恒等・合成則とaugmentationの自然性を証明する。
`OrdinaryBarWordRowMaps`は外側の全単体写像による実行間写像と二重単体図式を構成する。
`OrdinaryBarSourceHom`と`OrdinaryBarWordRows`は元のsource Hom、実augmentationの外側自然性、
実対角とターゲットの対角同型を与える。
`OrdinaryBarWordRowsDiagonal`は既存のword Homとの実対角同型と、元のaugmentationの実分解を証明する。
`DiagonalAnodyne`は右随伴の相対matchingのhorn右持ち上げ性から、モデル構造不要で
Reedy anodyne写像の実対角がanodyneとなることを証明する。
行ごとの局所化同値から対角への保存、外側のaugmentation、小さい厳密なRMapは残る。
受入検証は`check_word_rows_diagonal`（36宣言・6モジュール）。


### モデル構造不要の行ごとの局所化同値の対角保存（§376）

`KanLocalizedMonoLifting`は局所化同値な単射のKan基底を持つKan fibrationに対する厳密liftを構成する。
`DiagonalKanTests`と`LocalizedMonoReedy`はKanテストと閉クラスのReedy判定から、
Reedy単射で各行が局所化同値となる写像の対角保存を証明する。
`BoundaryReedyFactorization`の実WFSと分裂を使い、`DiagonalLocalizedEquivalence`は
任意の行ごとの局所化同値の実対角が局所化同値となることを証明する。値域のModelCategoryは不要である。
`OrdinaryBarWordDiagonalEquivalence`は実toSourceの可逆性と、元の全対角small augmentationの
source augmentationへの帰着を与える。
source augmentationの可逆性、小さいstrictificationと小さい厳密なRMapは残る。
受入検証は`check_diagonal_localized_equivalence`（39宣言・6モジュール）。


### 追加退化と実source・全対角augmentationの収縮（§377）

`Simplex/Prefix`と`PrefixInterval`は始点を加える関手と標準区間のcut写像を構成する。
`ExtraDegeneracyInterval`と`ExtraDegeneracyContraction`は任意のMathlib追加退化から
実区間ホモトピーを構成し、augmentationとsectionが任意のanodyne反転関手のもとで互いに逆と証明する。
`OppositeHomotopy`は単体方向の逆転による実ホモトピーの端点交換を与える。
`PathObjectTransport`、`OrdinaryBarSourceOperators`、`OrdinaryBarSourceExtraOperators`は
元のsourceの全作用を自由道作用へ同定し、singletonとの全交換法則を証明する。
`OrdinaryBarSourceExtraDegeneracy`は元の増大Homに実追加退化を構成する。
`OrdinaryBarSourceContraction`は元のsource・word・全対角small頂点augmentationの
anodyne局所化後の可逆性を証明する。任意の圏Cで使え、モデル構造は不要である。
Hom値は補助宇宙max(u,v)にあり、小さいstrictificationと小さい厳密なRMapは残る。
受入検証は`check_source_contraction`（85宣言・10モジュール）。


### Hom sectionと全パラメータ作用の元のHomへの降下（§378）

`OrdinaryBarSourceSection`は追加退化から元のHom augmentationの単体的sectionを与える。
`OrdinaryBarSourceWordEmbedding`は全作用に自然な実source→ambient・small word Hom比較と
augmentationの交換・局所化可逆性を証明する。
`OrdinaryBarHomSections`は実ambient・small Hom augmentationのSplitEpiと全次数の全射性を与える。
これらはHomのsectionであり、合成を保つ圏のsectionではない。
`SplitLocalizedDescent`はsplitな局所化同値に沿って、全P族のKan対象への実写像を降下させ、
元の写像および同じ基底族の持ち上げを比較する実区間ホモトピーを得る。
`OrdinaryBarClosedHomDescent`と`OrdinaryBarClosedHomDescentLaws`は既存の実作用へ適用し、
元の基底Homを引数とする小さい内部Homへのnativeな族、厳密なパラメータ置換則、
小さい宇宙の実単位・合成比較ホモトピーを与える。
高次の整合性と小さい厳密な基底関手は未完了である。
受入検証は`check_hom_parameter_descent`（37宣言・6モジュール）。


### 相対境界を保つ降下選択とnativeな比較区間（§379）

`KanPostDetection`と`KanRestrictionEquivalence`は単射性を仮定せず、Kan対象への内部Hom制限が
局所化同値となることを証明する。
`KanLocalizedComparisonResolution`はboundary分解からdecodeと一つの大域的な比較区間を与える。
そのunit上の比較は厳密に定数である。
`RestrictionDescentChoices`は実pullbackの選択空間と、既存の族・比較区間全体を同時に保持する
任意の単射パラメータからの延長を構成する。
`OrdinaryBarRelativeHomDescent`は元の実word作用へ適用し、nativeな小さい内部Homへの族を得る。
`RestrictionDescentEvaluation`と`OrdinaryBarRelativeNativeComparison`は元の実作用との比較を
元の小さい宇宙の実区間へ戻し、区間写像自体の置換則と、nativeな族・比較区間の同時相対延長を証明する。
補助宇宙のモデル構造も選択空間の低い宇宙でのsmallnessも仮定しない。
異なるHomをまたぐ単位・合成の高次整合性と、小さい厳密な基底関手は残る。
受入検証は`check_relative_hom_descent`（84宣言・7モジュール）。


### 指定native比較の合成正方形と三角形（§380）

`HomotopyBinarySquare`は二つの指定区間から、四辺を保持する実正方形とその対角の実比較を構成する。
`ClosedHomotopyComposition`は標準内部Hom合成へ適用し、同時合成の区間写像の厳密な結合則を証明する。
`OrdinaryBarRelativeComposition`は元の二つのnative比較へ適用し、四辺の式と対角の全パラメータ置換則を得る。
`KanComparisonTriangle`は共通終点を持つ二つの指定比較をouter two-hornで埋め、両全辺を保持する。
`OrdinaryBarRelativeCompositionTriangle`はXY・YZ・XZの実降下選択を受け取り、
合成射の指定比較と二つの入力比較の同時合成を保持する実三角形を元の小さい内部Homに構成する。
三辺目が降下合成を比較する実ホモトピーであり、標準内部恒等へのnativeな比較も与える。
三角形の全fillerの相対延長、全高次の整合性、小さい厳密な基底関手は残る。
受入検証は`check_relative_composition`（91宣言・5モジュール）。


### 指定二辺を固定する全合成三角形の小さい選択空間（§381）

`ComparisonTriangleHorn`は元の指定二辺の実hornへの貼り合わせと、任意の三角形の制限式を証明する。
`ComparisonTriangleChoices`は全fillerの実空間、boundary右持ち上げ性・Kan性、
元の三角形の実頂点、全辺の固定式、任意の小さい単射境界を保持する三角形族の延長を与える。
同じ指定二辺を持つ任意の二つのfillerを、horn全体を固定する実ホモトピーで比較する。
`OrdinaryBarCompositionChoices`は元の実合成比較へ適用し、SSet.{v}値の全合成三角形の空間を構成する。
§380の選んだ三角形を実頂点として含み、評価で元の三角形がそのまま戻ることを証明する。
実族T⊗(Δ[2]⊗L)の指定二辺の一致と、既存の三角形族全体を保持する小さい相対延長も証明する。
元のTの変更に伴う移送、全高次の整合性、小さい厳密な基底関手は残る。
受入検証は`check_composition_choices`（41宣言・3モジュール）。


### 元のパラメータ変更に沿う全三角形選択空間の移送（§382）

`ComparisonTriangleTransport`は指定二辺を保つ写像に沿って全fillerを移送し、
実データの頂点・全族の評価との交換および恒等・合成則を証明する。
`OrdinaryBarCompositionReindex`は元の小さいパラメータi:U→Tによる実native比較の制限へ適用する。
全合成三角形選択空間の実SSet射と、全追加パラメータL上での実評価の厳密な制限式を得る。
`OrdinaryBarCompositionReindexLaws`は恒等・合成則、既存の実三角形の頂点と評価の交換を証明し、
移送した前回の三角形と新たに選んだ三角形を、指定horn全体を保つ実ホモトピーで比較する。
元の基底上の小さいRMapの関手性と全高次の整合性は残る。
受入検証は`check_composition_reindex`（24宣言・3モジュール）。


### 全制限先の小さい図式と自然な三角形族（§383）

`ParameterChoiceDiagram`は実制限に沿う全境界延長の図式と、元の選択空間からの自然変換を構成する。
`ComparisonTriangleParameterDiagram`は指定二辺を保つ全三角形へ適用し、
元の三角形の自然な点、族の相対延長、二つの元の選択を結ぶ自然な区間と端点式を与える。
`OrdinaryBarCompositionParameterDiagram`は元のnative合成比較へ適用し、
SSet.{v}値の実図式、制限した既存の合成選択空間との対象ごとの同型、実評価の制限式を証明する。
元のCᵒᵖ×C上のRMapと異なるHomをまたぐ全高次整合性は残る。
受入検証は`check_composition_parameter_diagram`（54宣言・3モジュール）。


### 指定面を保持する四面体とnative三重合成の比較円板（§384）

`KanComparisonTetrahedron`は同じ終点への区間が支える三つの指定三角形を面に保ち、
第四面の全三辺が元の比較辺に一致する実四面体を構成する。
`KanComparisonSquare`は一つの対角三角形を共有する二つの四面体から四辺を保持する円板データを作る。
`ComparisonTriangleBinary`は三角形と区間を左右から合成し、比較辺で第三の射を始点に固定する。
`OrdinaryBarTripleComparison`は元の六つのHom降下選択を使う四つの比較と円錐面を用意する。
`OrdinaryBarAssociativityCoherence`は元の小さい内部Homへ適用し、
以前の二つの外側合成比較と、内側比較に第三の降下射を合成した全四辺、共通対角線を保持する。
出力は二つの実三角形による円板であり、単位・全高次の整合性と小さい厳密なRMapは残る。
受入検証は`check_comparison_tetrahedra`（106宣言・3モジュール）と
`check_native_associativity_coherence`（98宣言・2モジュール）。


### 整合性の実四面体全体を保つパラメータ移送（§385）

`ComparisonCoherenceTransport`は指定全辺を保つ写像に沿って四面体と比較円板を移送し、
四つの元の円錐三角形・共通対角三角形・両方の四面体全体を保持する。
`ComparisonCoherenceRestriction`は実パラメータ制限へ適用し、円板・対角・四面体全体の実評価の
制限式と、左右の四面体写像全体の厳密な恒等・合成則を証明する。モデル構造は不要である。
元のnative三重合成円板と四面体を、独立したu・vのまま制限する利用例も検証した。
受入検証は`check_comparison_coherence_restriction`（65宣言・2モジュール）。


### 元の合成比較・単位比較・定数区間を保つ左右単位の整合性（§386）

`BinaryIntervalTriangles`は二つの指定区間の三角形を明示的に構成し全三辺を保持する。
`ClosedParameterUnits`は任意の共有パラメータ・全区間での内部Homの厳密な単位則を証明する。
`ComparisonTriangleDegeneracy`は退化円錐三角形と往復比較の四面体を構成し、定数辺を保持する。
`OrdinaryBarUnitTriangles`は元の単位・合成比較をそのまま左右の往路・復路三角形に接続する。
`OrdinaryBarUnitCoherence`は以前の合成三角形を面に保つ四面体を作り、残る面の全三辺を証明する。
降下作用の単位則を厳密化したとの主張はせず、全次数の構成と小さいRMapへの接続は残る。
受入検証は`check_comparison_unit_triangles`（47宣言・3モジュール）と
`check_native_unit_coherence`（69宣言・2モジュール）。


### 任意次元の全指定面と、変化するhorn族の相対延長（§387）

`ParameterizedHornChoices`は任意次元の互換な指定された全ての面から小さい全filler空間を作る。
全指定面の保持、単射に沿う以前の全族の延長、filler間の相対比較、全制限先の自然な族を証明する。
`KanHornFamilyLifting`は変化するhorn族を一様に埋め、任意のパラメータ写像での厳密な自然性を持つ。
指定された単射境界上の以前の全fillerと、全horn族を同時に保持する相対延長も構成する。
元のnative単位四面体で、保持・復元・可変horn族への延長を検証した。一般論にモデル構造は不要である。
互換な境界自体の全次数の構成・退化面の保持・小さい厳密なRMapへの接続は残る。
受入検証は`check_parameterized_horn_choices`（19宣言）と`check_horn_family_lifting`（22宣言）。


### 指定入力族と退化を保持する一様filling操作（§388–389）

`RelativeHornFillingOperation`は指定入力部分単体集合上の全fillerを保持する一つの切断を構成する。
`DegenerateHornInput`は任意次元の各退化について、hornに残るsection面で入力を復元し、
退化入力のsplit monoと、その全族を保持する操作を構成する。
`CompatibleInputUnion`は大きい添字の入力像の和を小さい値宇宙に保ち、互換な出力族を降下させる。
`CompatibleHornFillingOperation`はその和を使い、すべての互換な指定全族を一つの操作に保持する。
受入検証は`check_relative_horn_operation`（31宣言）と`check_compatible_horn_operation`（31宣言）。


### 両退化の同時保持と、元のTに厳密に自然なnative合成比較（§390）

`DegenerateTriangleOverlap`は三角形の両退化の重なりで、全fillerが等しいことを証明する。
`NormalizedTriangleHorn`は両退化を同時に保持する一つの切断を構成する。
`NaturalHornFilling`は任意次元で元のKに切断を固定し、Tの変更に厳密に自然な実fillerを与える。
`NormalizedComparisonTriangle`は指定二辺を保持する三角形を構成し、退化一致・厳密な定数辺を証明する。
`OrdinaryBarNormalizedCompositionTriangle`は実native入力の再評価に対する厳密な全三角形・全区間の式と、
以前の独立した三角形との相対比較を与える。Kの変更や元の基底上のRMapの関手性は残る。
受入検証は`check_normalized_native_triangles`（64宣言・5モジュール）。


### 任意次元の全退化を同時保持する正規化horn操作（§391）

`CosimplicialDegenerateHorn`は任意の圏の余単体対象で、同じhornを与える退化写像の一致を証明する。
`DegenerateHornOverlap`は任意の外部パラメータへ適用し、退化した全filler族の重なりを証明する。
`NormalizedHornFilling`は任意次元・任意の欠ける面で、全退化を同時に保持する一つの切断を構成する。
元のKに操作を固定したT自然性・全評価・以前のfillerとの相対比較を持ち、三角形では以前の操作に一致する。
受入検証は`check_normalized_horn_filling`（25宣言・3モジュール）。


### Tに厳密に自然な四面体と比較円板の選択（§392）

`NormalizedComparisonTetrahedron`は指定三角形を全三面に保持し、退化入力をそのまま返す。
入力全体を制限してから選んだ全四面体・残る面の全評価が、以前の選択の実制限に厳密に一致する。
`NormalizedComparisonSquare`は自然な共通対角線と二つの自然な四面体を選び、
元の四辺を保持する円板を作る。左右の全四面体と全評価の厳密なT自然性を証明する。
Kの変更に関する操作間の比較、全次数の互換な境界構成、小さい厳密なRMapへの接続は残る。
受入検証は`check_normalized_comparison_coherence`（73宣言・2モジュール）。


### 標的写像に沿う正規化操作の比較と全退化の区間固定（§393）

`MonoRightLiftingRelativeHomotopy`は、同じ基底への射を指定mono上で固定して比較する。
`CompatibleInputUnion.hom_ext`は大きい添字でも、和からの射を入力族で判定する。
`NormalizedHornTargetComparison`は任意のKan標的写像K→Lに沿う二つの正規化充填操作を比較する。
一つの全入力空間上の比較により、horn全体と全退化入力族を区間全体で固定する。
任意のTへの制限と実評価はパラメータ変更に厳密に自然である。モデル構造は要求しない。
標的写像の恒等・合成との高次整合性と、小さい厳密なRMapへの接続は残る。
受入検証は`check_normalized_horn_target_comparison`（43宣言・3モジュール）。


### 任意形状の相対持ち上げと全面を保持する充填（§394）

`RelativeProductLifting`は二つのmonoのpushout-productから以前の族・指定族・基底族を保持する。
`RelativeBoundaryFilling`は任意次元の互換な全面を持つ実fillerを、基底と指定部分上で一定にする。
`RelativeComparisonTriangle`は以前の三つの全区間をそのまま三辺に保持する。
Kan性やモデル構造は不要である。受入検証は`check_relative_boundary_filling`（25宣言・3モジュール）。


### 元の標的比較を保持する恒等・合成三角形（§395）

`CompatibleInputMap`と`NormalizedHornInputMap`は全退化入力の和を標的写像に厳密に沿って移す。
`NormalizedHornTargetComposition`は元のq・r・q≫rの比較を面に持つ実三角形を構成する。
全hornと全退化入力を固定し、全三角形・実評価はTの制限に厳密に自然である。
`NormalizedHornTargetIdentity`は以前の恒等比較と二つの厳密な定数辺を面に持つ三角形を構成する。
受入検証は`check_normalized_horn_target_coherence`（66宣言・4モジュール）。
三重合成以降の整合性の実構成と、小さい厳密なRMapへの接続は残る。
