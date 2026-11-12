# §10 almost 数学と almost purity：リファクタの提案と、形式化の計画の提案（2026-11-12）

作成：ノートのチャット（形式化の調整役ではない）。§2〜§6 と同じ形。**扱いは調整役が判断する。** 事実に推奨を添える。

- 基準：main 22150d511（途中で 56decc02b のノートと地図の更新が入ったが Lean のコードに差分はない）。読み取りだけのエージェントがノートの加筆 2 本、コードの見直し 1 本（件数を含む）。件数のスクリプトはノートのチャットの作業用の場所にある。規模の見立ては推測で、それ以外は断らない限り grep・import グラフ・原典の照合で確かめた。
- 原典（pp.78–84）の項目は Def 10.1〜Rem 10.13 の 13 個。
- 二種類の提案：**A. リファクタ（R10-1〜R10-8）**、**B. 形式化の計画（§3 の表と §3.1 の計画上の点）**。

## 0. 規模と中身の分かれ方（確認済み）

- 対象は 61 本・11,508 行で、本体に sorry は 0。
  - BS/Almost：9 本・2,879 行
  - BS/PerfectoidIdeal：7 本・1,155 行
  - Perfectoidization/Derived の §10 の群：6 本・2,008 行
  - CA/Almost：3 本・812 行
  - CA/UniversalHomeomorphism：6 本・1,069 行
  - CA/EtaleStratification：30 本・3,585 行
- 中身は三つの系統に分かれる。
  - **(i) 単項の系統**：J=(g) の `perfectoidIdeal`。PerfectoidIdeal/*、Lemma103、PerfectoidAlmost、SupportedQuotient がこれ。Mathlib の `DerivedCategory`（有界上の模型）の上にあり、CLMST が使う。
  - **(ii) 一般の J の系統**：BS-W13 で入った `perfectoidKernel`。AlmostConnectivity・AlmostTensor・AlmostTensorForward・AlmostGenerators・CompletedModuleTensor がこれで、∞ の導来圏の頂点 `DVertex` の上にある。
  - **(iii) Thm 10.9・10.11 の古典的な入力と Lemma 10.12**：FiniteEtaleComparison、Derived/Integral*、PerfectoidFilteredColimit、FiniteEtalePerfectoid、UniversalHomeomorphism、EtaleStratification。
- 主定理の閉包（`SerrePositivity.Paper.Statement` から import を辿ったもの）に入るのは 13/61 本。
  - 入る 13 本：Lemma103、PerfectoidAlmost、SupportedQuotient、PerfectoidIdeal の 6 本（TorCriteria 以外）、IntegralExistence、CA/Almost の 3 本。いずれも (i) と E3 の利用側。
  - (ii) と (iii) は閉包に入らない。A9 が Inputs を置き換えた時点で入る。

## 1. A. リファクタの提案（今あるコードを直す）

### R10-1 単項の `perfectoidIdeal` と一般の J の `perfectoidKernel` が二系統ある【推奨：保守（優先）。台帳に新しく足す】

二つの核は J=span{g} で定義上同じになる（推測、rfl で通る見込み）。
- `perfectoidIdeal`：PerfectoidIdeal/Basic:37 の `ker((toQuotientPerfectoidization R (span{g})).comp mk)`。
- `perfectoidKernel`：AlmostConnectivity:38 の `ker(quotientPerfdMap)`。

両者を結ぶ補題は一つもない（grep で確認）。その結果、同じ内容の対が並んでいる。

| 内容 | 単項の側 | 一般の J の側 |
| --- | --- | --- |
| (g) ⊆ 核 | `span_le_perfectoidIdeal`（Basic:54） | `le_perfectoidKernel`（:41） |
| 単調性 | `perfectoidIdeal_mono`（Basic:76） | `perfectoidKernel_mono`（:61） |
| 普遍性 | `perfectoidIdeal_le_ker_of_eq_zero`（Cover:194） | `perfectoidKernel_le`（:47） |
| 商写像の全射性 | `perfectoidIdeal_quotientMap_surjective`（CompletedQuotient:47） | `quotientPerfdMap_surjective`（:100） |
| 商が perfectoid | `perfectoidIdeal_quotient_isIntegralPerfectoid`（Lemma103:361） | `perfectoidKernel_quotient_isIntegralPerfectoid`（:108） |
| almost 零 ⇒ テンソル零 | `perfectoidIdeal_completedTensor_isZero_of_isAlmostZero`（PerfectoidAlmost:422） | `perfectoidKernel_completedTensor_isZero_of_isAlmostZero`（:115）。証明は同じ |
| 逆向き | `perfectoidIdeal_isAlmostZero_of_completedTensor_isZero`（PerfectoidAlmost:447、加群、D(R)） | `isAlmostZero_of_completedTensor_isZero`（AlmostTensor:191、DVertex の複体） |
| 根基 | `perfectoidIdeal_isRadical`・`radical_span_le_perfectoidIdeal`（Powers:128・147） | `perfectoidIdeal_radical`（AlmostConnectivity:67。名前と違い perfectoidKernel についての定理） |
| Lemma 10.3 の三主張 | `perfectoidIdeal_lemma103`（Lemma103:401） | 名前つきの宣言なし。第三主張だけ AlmostConnectivity:126 で直接使う |

**台帳にない事実：一般形は既にある。** `Perfectoidization/CompletedTensor` に、商 R/K が perfectoid な任意の K についての版が置かれている。
- `:286 integralPerfectoid_completedQuotientMul_isIso`（Lemma 10.3 の芯）
- `:294 integralPerfectoid_completeIdealExtensionClosed`（Prop 10.2 の拡大閉性）
- `:301 integralPerfectoid_ideal_mod_power_idempotent`（Rem 10.7 の mod pⁿ の冪等性）

これに対して単項の系統は次のように重ねて持っている。
- **冪等性**：PerfectoidAlmost:111–351 の約 240 行で、conormal を経由する別の証明（`perfectoidIdealMod_idempotent`:343）を持つ。一般形の :301 は外から未使用。
- **拡大閉性が三つ**：CompletedTensor:294、`perfectoidIdeal_completeIdealExtensionClosed`（CompletedQuotient:63、未使用）、`perfectoidIdeal_isAlmostZero_extension`（PerfectoidAlmost:470、CLMST が使う）。

推奨：
- `perfectoidKernel p R hR (span{g}) = perfectoidIdeal R p hR g` を一本置く。
- 一般の J の Lemma 10.3・Prop 10.2（拡大）・Rem 10.7（冪等）を一般形の系として述べる。
- 単項版は、CLMST の署名を保ったままその特殊化にする。
- conormal 経由の証明は削れる候補（推測）。
- 導来圏の模型も二つある（Mathlib の D(R) と DVertex を CompletedModuleTensor が橋渡し）。これは系統の差に由来するので、記録だけにする。

### R10-2 BR24「almost の言葉で述べ直す」は範囲が広がった【推奨：保守のまま。範囲を書き直す】

- 「∀ s ∈ perfectoidIdeal …, … → s • x = 0」の手書きは 85 か所・12 ファイルある。
  - BS：53 か所・10 ファイル。内訳は SupportedQuotient 9、Cover 7、Tor 6、TorCriteria 6、CompletedQuotient 5、Andre/TorDescent 6、Perfectoidization/ExcisionTor 8、FiniteComparisonExcision 3、ExcisionComparison 2、Excision 1。
  - CLMST：32 か所（KoszulAnnihilation 18、AllModuleTorVanishing 14）。
- 共通側の述語は `IsAlmostZero`（`I ≤ annihilator`、CA/Almost/Basic:38）と `IsAlmostInjective`・`IsAlmostSurjective`・`IsAlmostIso`（:129・132・137）。
- BR24 の原文（box-texts.md:225）の参照先は古い。
  - `CommutativeAlgebra/Almost/Zero:25`・`Morphism:34` は、今は Basic:38・137。
  - `PerfectoidizationSupportedQuotientKernel` などの 3 ファイルは SupportedQuotient に統合済み。
  - 「`PerfectoidAlmost`（17 行）は集約だけ」は、今は 534 行の本体。

### R10-3 名前の紛らわしさ（BR43）【推奨：B3 の改名表へ】

- 状態は変わらない：`perfectoidIdeal_radical`（AlmostConnectivity:67）は perfectoidKernel についての定理。`IsJAlmostZero`（:86、複体）と `IsAlmostZero`（加群）、`IsAlmostConnective`（:91）。
- 案：`perfectoidKernel_radical`、`IsJAlmostZero` → `IsAlmostZeroComplex` など。

### R10-4 drafts/A8 と本体の重なり【推奨：5∞-0（R4-1・R5-1 と同じ扱い）】

- drafts/A8 は 4 本・899 行・宣言 77。そのうち sorry を含む宣言が 42。
- **本体と同じ名前が 40**。そのうち 18 は drafts では sorry のままで、本体では証明済み（W13 の報告では「draft と同じ型」）。例：
  - `isAlmostZero_iff_completedTensor_isZero`（AlmostTensorForward:394）
  - `connective_iff_almost`:480
  - `isAlmostZero_iff_forall_gen`（AlmostGenerators:155）
  - `trivialCoverComparison_*`（FiniteEtaleComparison）
  - `integralClosure*`・`arcOutside_*`（IntegralClosureCompletion）
  - `integral_isFilteredColimit_finitePresentation`
  - `isIntegralPerfectoid_completedFilteredColimit`
  - `exists_finitePresentation_approximation_fixedLocalization`
- 名前空間も同じ（`BhattScholze.Almost`・`Perfectoidization.Derived`）。drafts を本体へ移すと完全修飾名が衝突する。
- 不要になった見込みの宣言：`restrictScalars_perfectoidQuotient_fullyFaithful`（drafts:95）と `completeModuleRestriction`（:84）。本体の Prop 10.4 は忘却関手 U を使わず、切り捨てと Koszul で証明している（推測）。`integralClosure_not_complete_counterexample`（IntegralDiscreteness:224）は設計の反例で、E3 には要らない。
- 古いコメント：
  - 「基準コミット 972bb7f53」（全本）。
  - AlmostConnectivity:12 の W9-III-08（解消済み。Lemma103 の閉包は Inputs に届かないことを確認した）。
  - 規約の `CommutativeAlgebra/Almost/Zero`。
  - IntegralDiscreteness:9 が削除済みの A8/Stratification を import すると書いている。

### R10-5 層の向き・置き場所・名前空間【推奨：B3】

- **(a) SupportedQuotient が E3 の引用に依存する。**
  - `Almost/SupportedQuotient` → `Derived/IntegralExistence` → `Inputs`（E3）。§10 の 61 本で Inputs に届くのはこれだけ（確認）。
  - 原典の項目ではなく（docstring:21）、使うのは §8 の `Perfectoidization/ExcisionTor`（:56・81・169）だけ。
  - Almost/ に置いたままだと、A8 のファイルが誤って import したときに A9 で循環する危険がある（W9-III-08 の条件）。ExcisionTor の隣へ移す。
- **(b) §10 から §7 への余分な import。** FiniteEtaleComparison:5 と IntegralClosureCompletion:4 は `Andre.Transfinite.Limit` を import しているが、使うのは被約環の一行補題 `mul_eq_zero_of_pow_mul_eq_zero_of_reduced`（Limit:84）だけ（FiniteEtaleComparison:243、IntegralClosureCompletion:223）。補題を CommutativeAlgebra へ移す。PerfectoidFilteredColimit は `isIntegralPerfectoid_adicCompletion_ringDirectLimit` を本当に使っているので、そのままでよい。
- **(c) 一般論が BS のファイルにある。**
  - `InfinityCategories.Derived.IsConnectiveAt`（AlmostTensor:67。本体でこの名前空間を使うのはこのファイルだけ）は drafts/DerivedGeneral/Truncation:53 と完全修飾名が同じ。
  - `Perfectoidization.Derived.isPCompleteVertex`（AlmostConnectivity:138）は drafts/A7/AnimatedDomain:71 と同じ名前。
  - CompletedModuleTensor（DVertex と有界上の模型の比較）は HomologicalAlgebra と InfinityCategories しか import しない。
  - 移し先は `InfinityCategories/Project/DerivedCategories/`（または HomologicalAlgebra）。drafts と衝突する前に移す。
- **(d) §10 の芯が §8 の名前のファイルにある。** `Perfectoidization/CompletedTensor:186–305`（Lemma 10.3 の証明中の主張と、R10-1 の三つの一般形）。B3 で Almost/ へ切り出すか、docstring に明記する。
- **(e) Lemma 10.12 の 36 本が root から届かない（確認済み）。**
  - UniversalHomeomorphism 6 本と EtaleStratification 30 本は、`SerrePositivity.lean` の import 閉包に入らない。import するのは `scripts/audit/shared.lean` だけ。
  - lakefile の既定のターゲット（`SerrePositivity`）では一度もビルドされない。
  - A9 で E3 を置き換えると主定理の閉包に入るので、それより前に root へ足す。B3 の静的検査に含める。
- **(f) 名前空間がそろっていない。**
  - Almost/ の中で、W13 の 6 本は `BhattScholze.Almost`、Lemma103・PerfectoidAlmost・SupportedQuotient は `BhattScholze`。
  - PerfectoidIdeal/ の Basic・Cover・Powers は root の `SerrePositivity`（BhattScholze が付かない）。
  - IntegralExistence は三つの名前空間にまたがり、その一つが `BhattScholze.Inputs`（BR39）。
  - CA/Almost は `SerrePositivity.Almost`、UniversalHomeomorphism・EtaleStratification は `SerrePositivity.CommutativeAlgebra`。
- **(g) B3 の配置案**（refactor/kerodon-layout の report-bulk-w1.md:164・186）への意見。案は「Almost・PerfectoidIdeal を保持し、新設の `IntegralPerfectoidization/` に 6 本」。
  - FiniteEtaleComparison（Thm 10.9 の入力）だけが Almost に残り、同じ役割の IntegralClosureCompletion が移る。そろえる。
  - IntegralExistence は E3 の利用側（Thm 1.17(1)、閉包の中）で、§10 の証明ではない。A9 で BR39 と一緒に整理するまで、Perfectoidization の界面の側に置く。
  - IntegralApproximation は中身が純粋な可換環論。W13 の報告自身が `CommutativeAlgebra/IntegralApproximation/` を提案していた。
  - 移動案に (a)(c)(e) が入っていない。

### R10-6 閉包・葉・未使用の宣言【推奨：消さない】

- 葉（集約以外に importer がない）は 8 本：AlmostGenerators、AlmostTensorForward、FiniteEtaleComparison、FiniteEtalePerfectoid、IntegralClosureApproximation、PerfectoidFilteredColimit、TorCriteria、EtaleStratification/Stratification。最後の二つは root にも入っていない。W13 の成果はすべて葉で、利用者は drafts/A8 だけ。
- 公開の宣言（instance・private を除く）427 件のうち：
  - 自分のファイルの外で本体・drafts・scripts のどこにも出ないもの：169 件。名前の最後の部分で照合しているので、この数は下限。
  - 自分のファイルでも使われないもの：51 件。
  - BS の側の例：CompletedModuleTensor の比較 5 件、PerfectoidAlmost の `perfectoidIdealMod_*_iff` 3 件、Cover:105・165・265・308、IntegralExistence の内部補題 6 件、`exists_perfectoidization_of_completed_integral`:499。
- 原典の項目にあたる宣言は残す。TorCriteria は 11-02 の決定で残している。

### R10-7 docstring【推奨：B3 の docstring の回（BR25・BR34）】

- 工程ラベルは 32 行・10 ファイル：B3・B4・B5・G2・KL-T・B-I・Π2-5／6・G-A8-n・A8-4・W9-III-07。
- 「（旧 …）」は 24 行・11 ファイル。§5・§6 では 0 件だったが、ここには残っている。
- 古い記述・方針違反：
  - PerfectoidAlmost:22「Prop 10.4 の全体は A8」（BR34）。同値は AlmostTensorForward:394 にあり、圏同値は D66 で形式化しない。
  - PerfectoidAlmost:510「文献入力の冪等性」。今は :343 で証明済み。
  - Lemma103:20「ノート D13」は、ノートへの参照を置かない方針に反する。
  - SupportedQuotient:216「citation B-I」。
  - IntegralExistence:413「Π2-6 … 旧 Inputs の置換は別工程」。
  - EtaleStratification/Stratification:54「（A8-4）」。
- 英語の docstring・見出し：SupportedQuotient（見出し 3、宣言の docstring）、Cover:41・87、Powers:126・145 など。

### R10-8 設計書・地図の古い記述【推奨：調整役が直す】

- **a8-design**
  - :13「§10.1（Def 10.1、Prop 10.2、Lemma 10.3、Rem 10.7）は形式化済み（B5）」は単項の場合だけ。
  - :14・:47 は J_perfd を `perfectoidIdeal` と書くが、本体は `perfectoidKernel`。
  - :33「複体は truncation の帰納」は、今は済み。
  - §4（:187–197）の「既存」の欄が、G-A8-3′・3″・4・5・6・8・9・10・11 で「なし／要確認」のまま。すべて本体にある。
  - :187 のパス `{FinitePresentationComplete,ModuleClosure}.lean` は、今は `ModuleComplete/{Presentation,Closure}`。
  - §8 の 6「Codex 未」は済み。
  - W13 に一度も触れていない。
- **design-status**
  - :160 の A8-1「非有界での Prop 10.4 の接続は Codex 未」は証明済み。
  - :161・:163 の A8-2・A8-4 は、W13 で本体に入った部品に触れていない。design-status 全体に W13 の記録がない。
  - :293 の G-A8-6 は W11 で済み。
- **drafts/README**：:28 の A8 の行（「それまで drafts/A8/ のまま」）、:62 の順序（A8/Stratification）。
- **items.csv**
  - 10.2：一般形 CompletedTensor:294 があり、一般の J も一行で出る。
  - 10.3：「A8-1 の非有界 Prop 10.4 で一般 J 版が必要」は古い。
  - 10.7：一般形 :301 が宣言の列にない。
  - 10.12：root に入っていないことを注記する。
- **stage-ii-second-half :60**：5∞-8 の依存が足りない（§3.1 の 1）。

## 2. 台帳の項目の今の状態（§10 に関わるもの）

- **BR24（保守）**：一部実施。SupportedQuotient は手書きのまま。範囲は R10-2 の 85 か所に広がっていて、台帳の原文の参照先は古い。
- **BR43**：変化なし。**BR34** の PerfectoidAlmost の件：変化なし（:22）。
- **BR39**：変化なし（IntegralExistence:422・:467、:491 と Inputs の同名）。
- **BR8**：TorCriteria は root の外のまま。**BR25**：R10-7 の 32 行。
- **台帳にない新しい事実**：
  - R10-1：一般形が CompletedTensor にあり、単項の系統は重ねて証明している。
  - R10-4：drafts/A8 と本体の同名 40。
  - R10-5 (a)(b)(c)(e)：特に (e) の Lemma 10.12 が root の外にあること。
  - R10-8：設計書・地図の古い記述。

## 3. B. 形式化の計画の提案（新しく形式化する項目）

| 項目 | 今あるもの・要るもの | 規模（推測） | 依存 | 推奨 |
| --- | --- | --- | --- | --- |
| Def 10.1 | 済み（`IsAlmostZero`＋`perfectoidKernel`）。付随の「J=(p) なら J_perfd=√(pR)」は ⊇ だけ（Powers:147） | 小 | — | 補完：等号を足す |
| Prop 10.2（核・余核・拡大での閉性、⊗ イデアル） | 拡大は一般形 CompletedTensor:294 を perfectoidKernel に当てるだけ。核・余核は `IsAlmostZero.submodule/quotient`（Basic:87・91）と完備加群の閉性。⊗ イデアルは完備テンソルの H⁰ の定義が要る | 小（拡大は数行） | — | 補完：5∞-0 か、A8 の古典の段（§3.1 の 2） |
| Prop 10.2（(R/J)_perfd 加群の圏との同値） | 加群の段階なので離散。`quotientModule`（CA/Almost/Quotient:115）、全射環準同型での係数制限、完備性の移送（HA Restriction.Completion） | 小〜中（200〜400 行） | — | 後回し。D14・D66 の決定を加群の段階でも保つか、調整役が確認する |
| Lemma 10.3（一般の J） | 一般の K の三主張（Lemma103:87・190・256、CompletedTensor:286）と `perfectoidKernel_quotient_isIntegralPerfectoid`（AlmostConnectivity:108）からの系 | 極小 | — | 入れる（5∞-0。R10-1 と一緒に） |
| Prop 10.4（同値） | 済み（AlmostTensorForward:394、AlmostTensor:191） | — | — | — |
| Prop 10.4（D_p-comp((R/J)_perfd) との同値、厚いテンソルイデアル） | 同値には完備加群の ∞ 圏と忘却関手の完全忠実性が要る（drafts:95、sorry）。厚いイデアルの部分は同値と完全性から出る | 同値は中〜大、厚いイデアルは小 | 同値は ∞ の完備圏 | 同値は入れない（D66）。厚いイデアルは補完（任意） |
| Lemma 10.5 | 済み（:480） | — | — | — |
| Def 10.6、Prop 10.8 | なし | Def は中（G コホモロジーの複体）、Prop は [And18b] の引用 | — | 入れない（D63） |
| Rem 10.7 | 冪等性：単項は済み、一般の J は CompletedTensor:301 の系。Galois の mod pⁿ 版は Def 10.6 待ち。J=(g) の J_perfd,n ⊗ J_perfd,n の平坦性（脚注 17 の余極限の式）はない。「∀ g ∈ J で (g)-almost」は生成元版（AlmostGenerators:155）の系 | 冪等は極小、平坦性は小〜中 | — | 冪等と ∀ g の系は補完（5∞-0）。平坦性は後回し、Galois は入れない |
| Thm 10.9 (a) J-almost 連結性（A8-2） | 入力は本体（FiniteEtaleComparison、IntegralClosureCompletion、Thm 7.14、aic の分裂 `finiteEtaleAway_exists_finite_cover`（CA/AbsolutelyIntegrallyClosed/Etale:327））。残る sorry は drafts の 6 宣言 | 中 | A6 の Cor 8.12、A7 の Prop 8.13、C1′ | 入れる（5∞-8b） |
| Thm 10.9 (b) S_perfd は離散で perfectoid | 原典の証明どおり Thm 10.11 の系（S は有限なので整） | 小 | 10.11 | 入れる（10.11 の直後の補完） |
| Thm 10.9 (c) V(J) の外で S → S_perfd が同型 | なし | 中 | A6 | 後回し |
| Thm 10.9 (d)(e) mod pⁿ の almost 有限射影・不分岐、G-Galois | almost setting（GR03）、Σ_r の Galois 閉包（[And18b] Lemma 1.9.2）、Prop 10.8 | 大＋引用 | — | 入れない（D63） |
| Thm 10.11 の組み立て・E3 の欄 `integral` | 入力は本体（IntegralApproximation:275・436、IntegralClosureApproximation:41、PerfectoidFilteredColimit:98、FiniteEtalePerfectoid:434、Lemma 10.12）。drafts/IntegralDiscreteness に残る sorry は 12（反例 1 件を除く） | 中（数百〜千行） | A4・A5・A6・A7、A8-2 | 入れる（5∞-8b。5∞-9 の前提） |
| Lemma 10.12 | 済み（Stratification:374） | — | — | root への登録だけ（R10-5 (e)） |
| Rem 10.10 | 主張なし（adic 空間を使わないという注意） | — | — | 入れない |
| Rem 10.13（[HM17] Thm 1.3 の再証明） | Thm 10.9 (d)、Rem 3.11、完備正則局所環 | 大 | 10.9 (d) | 入れない |

### 3.1 計画の上で気づいた点

1. **5∞-8 の依存が足りない（確認済み）。**
   - 段の表は「5∞-8 A7・A8｜5∞-4」となっている（second-half:60）。
   - しかし drafts/A8 は次のものを import している：A6 の Excision（Cor 8.12）、A7 の AnimatedPerfectoidization・UniversalProperty（AlmostPurityConnectivity:12）、A5・A4（IntegralDiscreteness:9–10）。
   - 推奨：5∞-8a（A7、依存は 5∞-4）と 5∞-8b（A8 の組み立て、依存は 5∞-5・5∞-6・5∞-7・5∞-8a）に分ける。
   - 5∞-7 は 6-4 に依存するので、⑥ は A8 の経路に乗る。5∞-9 の依存は既に 5∞-7 を含むので、最終の経路は変わらない。
2. **A8 の古典の段を ∞ を待たずに開ける見込み（推測）。** 5∞-3a と同じ考え方で、B3・5∞-0 の後に始められるもの：
   - 一般の J の Lemma 10.3・Prop 10.2（拡大）・Rem 10.7（冪等）の系
   - C1′ の残り：`completeBaseChangeUnitIso`・`perfectoidIdeal_baseChange`・`isAlmostZero_baseChange_iff`（drafts:189・197・209）
   - `span_singleton_isModuleComplete`（APC:84）
   - `exists_principal_splitting_cover`（APC:107）
   - Lemma 10.12 の root への登録
   - `isAlmostConnective_completedFilteredColimit`（drafts:132）は ∞ の filtered 余極限が要るので、③-b を待つ可能性がある。
3. **W13 の型検査済みの比較候補はリポジトリにない。** `/tmp/bsw13-basechange-coefficients.lean`・`-probe.lean` などにしか残っていない（確認：`completeBaseChangeUnitIso` を grep しても本体にない）。消える前に drafts へ写すか、報告に要点を残すとよい。
4. **5∞-0 に足すもの（§10 の分）。** R10-4（drafts/A8 を本体の宣言を指す形にし、重なる 40 の名前を外す）、R10-1 の結ぶ補題と一般の J の系、R10-5 (c)（IsConnectiveAt・isPCompleteVertex を移す）、R10-8。どれも数学の主張は増えない。

## 4. 件数（スクリプトで数えた）

- **対象**：61 本・11,508 行、本体の sorry 0。宣言 532（公開 427）。
- **閉包**：主定理の閉包に 13/61 本。root から届かないものが 37 本（Lemma 10.12 の 36 本と TorCriteria）。葉は 8 本。
- **未使用の公開宣言**：自分のファイルの外で未使用 169/427 件（群ごと：BS/Almost 21/86、PerfectoidIdeal 26/54、Derived 29/52、CA/Almost 25/70、UniversalHomeomorphism 15/37、EtaleStratification 53/128）。自分のファイルでも未使用 51 件。
- **drafts/A8**：4 本・899 行・宣言 77、sorry を含む宣言 42。本体と同名 40（うち drafts で sorry 18）、本体にない sorry 24。
- **手書きの零化条件**：85 か所・12 ファイル（BS 53・10 ファイル、CLMST 32・2 ファイル）。
- **docstring**：工程ラベル 32 行・10 ファイル、「旧」24 行・11 ファイル、ノートの参照 1（Lemma103:20）。
- **二系統の対**：表の 9 行。一般形がありながら単項の側で重ねている証明・包みは、冪等性 1（約 240 行）と拡大閉性 2。
## 5. ノートの側（参考）

1. ノート：§10 の全 13 項目を見出しと主張・Lean・証明の囲みにした（10 章、番号 10.1.n・10.2.n）。章末の項目の表と D 表は外し、D13 を Lemma 10.3、D14 を Prop 10.2（Prop 10.4 からも参照）、D63 を Thm 10.9 の下に移した。D66 は a8-design の番号で、ノートにはリンクなしで引いた。
2. 原典の誤植と判断した所（確証なし）：Rem 10.7 と脚注 17 の推移写像の指数 \(g^{1/p^i-1/p^{i-1}}\)（負になる）。証明の囲みでは脚注の最後の行に合わせて \(g^{1/p^i-1/p^{i+1}}\) と読み、そう読んだと書いた。
3. 旧ノートの「almost 零性の反映には \(K'\simeq K\hat\otimes R'\) だけを使う」は Lean で確かめられなかったので外した。Fayolle の反例（Prop 2.9）は旧ノートから引き継ぎ、文献には当たっていない。
4. 地図 items.csv：10.2（一般形 CompletedTensor:294）、10.3（三主張の残りの向きと一般の J への組み合わせ、title_ja を「J_perfd に沿った完備テンソル」に）、10.7（一般形 :301）、10.9（Thm 10.11 の部品 `integralClosureCompletion_isModuleComplete` を 10.11 の行へ移した）を 56decc02b で直した。R10-8 の items.csv の 4 点のうち 10.2・10.3・10.7 はこれで済み、10.12 の root の外の注記はこのコミットで足した。
