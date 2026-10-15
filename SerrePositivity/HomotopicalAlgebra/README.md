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
