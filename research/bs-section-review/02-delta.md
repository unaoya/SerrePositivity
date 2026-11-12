# §2 δ 環：リファクタの提案と、形式化の計画の提案（2026-11-12）

作成：ノートのチャット（形式化の調整役ではない）。ユーザーの方針（11-12）で、原典の §2 から順にノートを加筆し、節ごとにリファクタと計画の提案を書く。**扱い（実施・計画への取り込み・不要）は調整役が判断する。** ここでは事実に推奨を添える。

- 基準：main cfa0e8324 前後。読み取りだけのエージェント 7 本（小節ごとのノートの加筆 6 本、コードの見直し 1 本）が調べた。宣言の位置は grep で確かめたもの。規模の見立ては推測。
- この文書には性質の違う二種類の提案がある。
  - **A. リファクタの提案（R2-1〜R2-10）**：今ある本体のコードを直す。数学の主張は増えない（置き場所、重複、層の向き、docstring）。
  - **B. 形式化の計画の提案（§2 の表）**：原典にあって本体にない、または特別な場合しかない項目を、新しく形式化するかどうか。リファクタではない。
- 「主定理の閉包」は `SerrePositivity.Paper.Statement` の import の推移閉包。
- 台帳 `formalization-plans/refactor-ledger.md` の番号（BR4・BR5・BR6・BR32・BR34・BR37・BR38・BR41、T2-0・T2-3）にすでにあるものは、今の状態の確認と新しい事実だけを書く。

## 0. 規模と配置（事実）

- `BhattScholze/Delta/` は 56 ファイル・26,580 行。うち DividedPower が 23 ファイル・9,540 行。
- 主定理の閉包に入るのは 30 本、入らないのは 26 本。入らない 26 本は BS-W15 の系列（RegularSequencePD*・FreeDP*・FrobeniusDivision*・FrobeniusPushout・Universal・PrimeLocal*・Tensor・HomExt・Division/BaseChange・FreeDeltaFrobeniusFlat）。

## 1. A. リファクタの提案（今あるコードを直す）

推奨の順（効果と手間の比）で並べる。

### R2-1 Delta の層の向きを直す（BR41 の中身の特定）【推奨：先に】

Delta が上の層（Prismatic・Andre）を import しているのは三か所で、使っている宣言は少ない。

| importer | import 先 | 使う宣言 | 移し先の案 |
| --- | --- | --- | --- |
| `Delta/DividedPower/FrobeniusDivisionPD` | `Prismatic.CrystallineTensorRegularity` | `CrystallineFrobeniusTarget`、`crystallineCompletelyFlat_frobenius`、`crystallinePrimeRegular_of_isPushout`、`frobeniusLift_isDeltaHom_of_regular` | ファイルごと Delta へ（このファイル自身は CommutativeAlgebra・Delta・Mathlib しか import しない） |
| 同上 | `Andre.Envelope.PDivision` | `deltaPDivisionToAway_injective_of_p_mul_injective`（:516） | `Delta/DividedPower/PDivision` へ（依存は同ファイルの :181・:251 だけ） |
| `Delta/DividedPower/FrobeniusDivisionRegularSequence` | `Andre.PowerRootEnvelope.Completion` | `pdCompletionCoordinateEquiv`（:367）・`_unit`（:400） | 環の部分を HomologicalAlgebra か `Delta/Extension/DeltaPDCompletion` へ、δ の部分を DeltaPDCompletion へ |

- 推移的には FrobeniusDivisionPD が非 Delta の BS を 18 本、FrobeniusDivisionRegularSequence・FrobeniusPushout が 25 本取り込んでいる。RegularSequencePDKoszul・PrimeRegular・Tor・TruncatedFlat の 4 本は、`CommutativeAlgebra/KoszulRegular/Powers` → `Andre.OrdinaryRoots.MonicRelation`（台帳の BR26′）を経て 12 本取り込む。
- `RegularSequencePDUniversalTor` は `KST.DerivedBlowup.ScalarTensorView` を直接 import し、使うのは `scalarExtensionTensorView` だけ（design-status:41 に記録があり、台帳にはない）。
- 理由：R2-3（r=1 の旧版を一般版に替える）をすると、一般版の系列が主定理の閉包に入る。その前に層を直しておかないと、閉包に Andre・Prismatic・KST の一部が余計に入る。

### R2-2 Lemma 2.32 の節を Basic へ移し、Frobenius が δ 射であることを一本にする（BR5）【推奨】

- 版は二つではなく三つある：p 正則版 `isDeltaHom_frobeniusLift`（`Delta/Perfect/PerfectDelta:288`、利用者は同ファイルの 1 か所と監査）、一般版 `isDeltaHom_frobeniusLift_general`（`Delta/Free/FreeDeltaRing:276`、利用者 2）、Prismatic の p 正則版 `frobeniusLift_isDeltaHom_of_regular`（`Prismatic/CrystallineTensorRegularity:60`、利用者 4）。
- p 正則版が残る原因は import の循環：`Free/RelativeFreeDelta` が `PerfectDelta` を import して使うのは `p_mul_delta_dvd_delta_pow`（Lemma 2.32、PerfectDelta:159）だけ。FreeDeltaRing → RelativeFreeDelta → PerfectDelta の向きなので、PerfectDelta から一般版を使えない。
- 案：PerfectDelta の Lemma 2.32 の節（およそ :150〜230、DeltaRing だけに依存）を `Delta/Basic` へ移して循環を切り、二つの p 正則版を一般版の系にする。直す利用者は 5〜6 ファイル。

### R2-3 Lemma 2.38 の r=1 の旧版を一般版に替える（BR6・BR38）【推奨：R2-1 の後】

- 旧版 `Delta/DividedPower/PrincipalDP`（1,547 行）は主定理の閉包に入り、一般版（RegularSequencePD*）は閉包の外。旧版の利用者は Andre の 3 ファイル（Envelope/PDivision、PowerRootEnvelope/DividedPowerPrime、PowerRootEnvelope/PrincipalDP、計 5,192 行、使う宣言は 10・5・14）。
- 階乗部分環 `pDivisionFactorialSubring`（PDivision:476）への同型が六つある：`principalDPFactorialEquiv`、`dpFamilyFactorialEquiv`、`freeDPFactorialEquiv`、`frobeniusDivisionFactorialEquiv`、`pDivisionFactorialBaseEquivOfDividedPowers`、`deltaPDivisionRawFactorialEquiv`（Andre/Envelope/PDivision:642、監査だけ。台帳にない）。どれも「A[1/p] への単射と像の等式から `ofBijective`・`subringCongr`」の形なので、一般形を一つ置けそう（推測）。直す利用者は約 4 ファイル。
- 一変数の分冪代数 `RankOneDP`（1,919 行・144 宣言、δ を使わない）は多変数の FreeDP*・TruncatedPolynomialBasis と並行している（台帳にない）。利用者は PrincipalDP（18）、Andre/PowerRootEnvelope/DividedPowerPrime（20）、FreeDPModPBlocks（3）。σ=Unit の特殊化で出せる可能性がある（推測）。

### R2-4 自由 δ 環の Frobenius の平坦性を一本にする（BR37）【推奨】

- 四か所で示されている：ℤ 版（`Delta/Free/FreeDeltaFrobeniusFlat`、本命の `freeDeltaModPFrobenius_moduleFaithfullyFlat` :231・`freeDeltaFrobenius_isCompletelyFaithfullyFlat` :339 は外の利用者 0）、一般形 `crystallineCompletelyFlat_frobenius`（`Prismatic/CrystallineTensorRegularity:206`）、`Delta/Division/FrobeniusPushout:155〜244` の private な ℤ_(p) 版（`primeLocalFreeDelta_frobenius_isCompletelyFlat`、台帳にない。一般形はすでに推移的に import されている）。
- FreeDeltaFrobeniusFlat の 49 宣言のうち外で使われるのは 6 つ。Frobenius を代数構造とみるための ULift の別名が三つ（`FreeDeltaFrobeniusTarget` :258、`FreeDeltaModPFrobeniusTarget` :163、`CrystallineFrobeniusTarget`）。
- 案：R2-1 で CrystallineTensorRegularity を Delta へ下ろしたうえで、一般形を正本にし、ℤ 版と FrobeniusPushout の private 版をその系にする。

### R2-5 自由 δ 環の ℤ 版を相対版で表す（BR4）

- 一本化の障害（台帳にない）：ℤ の標準 δ 構造が `private def integerDelta`（`Delta/Distinguished/PrimeLocalIntegers:43`）で、外から使えない。ℤ 上の δ 構造の存在と一意性（`integerFrobenius_exists` :32）も非公開。
- ℤ 版 `FreeDeltaRing` を名前で使う利用者は 4 ファイル（Distinguished/Universal 19 か所、Free/FreeDeltaFrobeniusFlat 50、Prism/Basic/UniversalOrientedFrobenius 4、drafts A1 3）。比較 `relativeFreeDeltaStructure_int_eq`（:238）は監査だけが使う。
- 案：ℤ の δ 構造と、ℤ が δ 環の始対象であること（Ex 2.6 の Lean の形）を公開の宣言にし（§2 のノートの例 2.1.17 がこれを必要とする）、`FreeDeltaRing` を相対版の abbrev にする。

### R2-6 δ 環のテンソル積を一本にする（台帳 T2-0 は閉じられる）

- 一般の δ テンソル `tensorDeltaStructure`・`existsUnique_tensorDeltaHom`（`Delta/Basic/Tensor:101・156`）は 11-10 からある。台帳の T2-0 の「確かめる」は済み。
- `perfectDeltaTensorStructure`（`Delta/Perfect/PerfectDeltaTensor:200`）は p ねじれなしと Frobenius から別に作られた二重の構成で、どこからも参照されない宣言が 6 つある。PerfectDeltaTensor は主定理の閉包に入り、Basic/Tensor は外（利用者は Prism/Bounded/CompletedTensor だけ）。
- 案：完全 δ 環のテンソルを一般形の系にする。

### R2-7 置き場所（BR32 の今の状態）

- DividedPower の 23 本は分割されていない。δ を使わないファイル：FreeDP・FreeDPBaseChange・FreeDPBasis・FreeDPDerivation・FreeDPIntegral・FreeDPModPBlocks・TruncatedPolynomialBasis・RankOneDP・RegularSequencePD（と Koszul・PrimeRegular・Reduction・TruncatedFlat・UniversalTor）。
- FreeDP*・TruncatedPolynomialBasis・RankOneDP は分冪代数の一般論で、Mathlib の `DividedPowerAlgebra/Init`（dp・lift・map だけ）の欠けを埋める。CommutativeAlgebra に分冪のディレクトリはまだない。案：`CommutativeAlgebra/DividedPowers/` を作って出す（Mathlib へ出す候補にもなる）。RegularSequencePD* は δ を使わないが Lemma 2.38 そのものなので Delta に残す。
- Def 2.42 の `IsCompletelyRegularRel` は `Prismatic/RelativeCompleteRegularity:149` にあり、§2 の項目が Delta の外にある。本体の利用者はなく（集約だけ）、drafts の A0・A1 が使う。docstring の「使われ方」は実態と合わない。
- Ex 2.6 の `existsUnique_primeLocalIntDeltaHom` は `Delta/Distinguished/` にあり、docstring の規約は「Lemma 2.15」になっている（主張は Ex 2.6 の始性）。

### R2-8 使われていない宣言・ファイル

- 集約と stage2 監査からしか届かない：`Delta/Division/FrobeniusPushout`（Rem 2.37、446 行）、`Delta/DividedPower/RegularSequencePDUniversalTor`（165 行、Lemma 2.38 の原典の形の版 `dpFamilyUniversalTor_subsingleton` :114 を含む）、`Delta/Distinguished/PrimeLocalFlat`（61 行）。
- 監査だけが参照する葉の宣言が Delta 全体で 219 個（多い順に RankOneDP 24、PDivision 18、Division/Source 18、Relations 17、RelativeFreeFiniteDelta 16、Residue 14、RelativeFreeDelta 13）。どこからも参照されない宣言が 9 個（FrobeniusPushout の公開定理 3、PerfectDeltaTensor の 6）。`deltaPDivisionToAway_range_eq_of_deltaStructure`（PDivision:758、Warning 2.41 の前半）もどこからも参照されない。
- BS-W15 K1 の主要な定理（`frobeniusDivisionDPEnvelopeEquiv`・`frobeniusDivisionPDCompletionEquiv`・`dpFamilyDelta` など）は drafts の AuditK1 以外ではファイルの中でしか使われない。外で使われるのは `frobeniusDivisionDPFamilyEquiv`・`frobeniusDivision_primeRegular`（利用者 Prism/Basic/CrystallineCoverRegularity）。
- 案：消すかどうかは E3 の経路（A0〜A2 が Lemma 2.36〜2.39 を使う予定）を見て決める。今は「利用者のない原典の項目」として残す判断もありうる。

### R2-9 docstring（BR34・BR25 と同じ回で）

- 台帳 BR34 の 2 件はまだ残る：`Delta/Extension/DeltaLocalization:19`（「今は主定理の経路にない」、実際は閉包に入り 6 ファイルが使う）、`Delta/Free/FreeDeltaFrobeniusFlat:29`（「監査だけが読む」）。
- 台帳にないもの：
  - `Delta/Perfect/PerfectDeltaTensor:23`「一般の δ 環のテンソル積はまだない」（11-10 からある）。
  - `Delta/DividedPower/PrincipalDP:22`・`Andre/Envelope/PDivision:30`「ノート §2.5 の課題 T2-1・T2-2」（済み、ノートに T 番号はもうない）。`Andre/Envelope/JetKoszul` の「ノート §2.6 の課題 T2-3」も同じ。
  - `Delta/DividedPower/PDivision` の方針「生の pushout の p ねじれなしは r=1 で Andre にある」（一般版がある）。
  - `Delta/Division/FrobeniusPushout` の概要「有限個の自由 δ 座標」（実際は任意の `σ`）。
  - `RankOneDP:36`・`PDivisionCompletion:17` の「ノート BR32」（今の正本は台帳）。RankOneDP の「使われ方」に FreeDPModPBlocks が抜けている。
  - `Delta/Perfect/DeltaPerfection` の規約「lim_φ はない（A3 で要る）」（計画の書き込み）。
  - `Delta/Distinguished/Distinguished:215`「BSBS 著者版」、`Prism/Basic/OrientedPrism:57–58`「判定BS 著者版」（空白の抜け）。
  - 「宣言名・名前空間・型は統合前のまま」が 11 ファイル、節の見出しの「（旧 Delta/…）」が 30 ファイル・228 か所。
- **ノートの番号を docstring が引いている**：Delta の 7 ファイル（DeltaRing・DeltaQuotient・DeltaColimit・DeltaWitt・RelativeFreeDelta・FreeDeltaRing・FreeDeltaFrobeniusFlat）が「命題 2.1.5 (4)」のようにノートの番号を直接引く。今回の加筆では §2.1 の既存の番号を保った。docstring は原典の番号（BS 著者版 Lemma 2.n）で引く形にそろえるのがよい（推奨）。そうすればノートの番号を振り直せる。

### R2-10 小さな一般化（見立て）

- `isDistinguished_iff_of_span_eq` は \(d\) と \(e\) の両方が根基にあると仮定するが、\((d)=(e)\) なら片方から従う。
- `isDistinguished_of_p_mem_span` が使うのは「\(\delta(d)\) を含む極大イデアルは \(p,d\) を含む」ことだけで、根基の仮定より弱くできる。
- `DeltaPDCompletion` の普遍性（`existsUnique_pdCompletionRingHom`・`existsUnique_deltaPDCompletionHom`）は試験環を同じ宇宙 u に置く。`complete_add`・`complete_of_power` は private。
- 「完全 p 完備 δ 環からの環準同型は δ 射」の強い形 `Andre.perfectSource_ringHom_isDeltaHom`（`Prism/PerfectPrismHomLift:343`、Andre 名前空間）と、Delta/Perfect の W(k) を源とする弱い版（:434）が並ぶ。Delta/Perfect へ下ろして一本にできる。

## 2. B. 形式化の計画の提案（新しく形式化する項目）

計画外の項目（地図で goal が not_required、または status が none・design_only・proved_special）ごとの見通し。「推奨」の欄は、入れる（今の計画に足す価値がある）・後回し（使う場所が出たら）・入れない、の三つ。

Mathlib（rev e6bbacd0e）にあるもの：Witt ベクトル（Frobenius は一般の R、FV=p は一般、VF=p は CharP、Teichmüller・IsPoly・truncated。単元の判定は体の上だけ）、DividedPowers の基本と分冪代数の Init（包はない）、エタール・FormallyEtale・HenselianRing、fpqc の site。ないもの：δ 環・λ 環、単体的可換環・animated 環、Elkik・van der Kallen、ファイバーごとの平坦性判定。

規模：小＝数百行、中＝千〜数千行、大＝それ以上か外部の理論が要る（推測）。

| 項目 | 何があればよいか | 規模 | 推奨 |
| --- | --- | --- | --- |
| Ex 2.6 の残り（δ が p 進付値を 1 下げる、δⁿ(pⁿ) は単元）と、ℤ の始性の公開 | 計算だけ。R2-5 と一緒に | 小 | **入れる**（R2-5 の前提） |
| Rem 2.27 の右随伴 lim_φ | 逆極限の部分環に成分ごとの δ、完全性、普遍性 | 小（300〜600 行） | **入れる**（原典の基本の構成。drafts の A3 も触れていた） |
| Rem 2.29 の二つの例 | Rem 2.2 の一意性と分離性（Mathlib） | 小 | 入れてよい。ただし原典の文言の読み方を先に確かめる（§3 の 2） |
| Lemma 2.33 の一般形（一般の完全 p 完備 A） | `perfectDeltaWittRecoveryEquiv` で W(k) の版を移す | 小 | **入れる** |
| Rem 2.40 の前半（\(D_I(A)\) は φ の引き戻し） | Division/BaseChange の押し出し、一般版の δ 射、Cor 2.39 | 小（100〜300 行） | 入れる |
| Rem 2.40 の後半、Warning 2.41 の反例 | 1/p ∉ 階乗部分環の判定と計算。後半は A{f/p} の p ねじれなしが一般に分からず読み方に注意 | 小〜中 | 後回し |
| Ex 2.20 (2)〜(4)（q-de Rham、\(A_{\inf}\) の ξ、Breuil–Kisin） | 冪級数環の δ 構造は Rem 2.2 から、ξ は Lemma 2.33 の一般形から | 各 小〜中 | (3) の ξ は Lemma 2.33 の一般形の後に入れる。(2)(4) は §16・§9 などで要るときに |
| Lemma 2.11 の残り（本当の忠実平坦性、\(\mathbb Q\{x\}\)） | 重み deg x_j = p^j の次数つきの議論か、ファイバーごとの判定 | 中 | 後回し（E3 は p 完全忠実平坦で足りる） |
| Cor 2.12（Frobenius は fpqc 局所全射） | Lemma 2.11 の本当の忠実平坦性、Basic/Tensor、忠実平坦性の底変換 | 中 | Lemma 2.11 の残りと一緒に |
| Rem 2.13 の一般形（ghost 写像の単射性なしの w） | 普遍の ℤ{x}・ℤ{x,y} から関手性で移す | 中 | Rem 2.7 の右随伴と一緒に検討 |
| Rem 2.7（一般の極限・余極限、W が右随伴） | 極限は小。右随伴は一般の R での W(R) の δ 構造と一般の w | 中〜大 | 後回し |
| Cor 2.31 の圏同値 | 対象ごとは済み。δ 環の圏が本体にない | 中 | δ 環の圏を置くときに |
| Lemma 2.18 のエタール部分 | 原典どおりは Elkik・van der Kallen が要る。「エタール代数の完備化」に限れば FormallyEtale の持ち上げで中。一般の有限生成 I の完備化も別に中 | 大（特別な場合は中） | 後回し（使う Lemma 4.21 は目標の外） |
| Lemma 2.43・Cor 2.44 の離散版 | RankOneDP・FreeDPModPBlocks の自由性、`IsCompletelyRegularRel`、CompletelyFlat の判定、φ の p 完全忠実平坦性、Cor 2.39。多変数の「R/(f^p) が A 平坦なら DPFamilyPresentation も平坦」は `dpTruncatedCoefficientMap_faithfullyFlat` からすぐ出るが宣言がない | 中（1〜3 千行） | Prop 3.13 の一般形（§3）を形式化するときに一緒に。変数の場合は Prop 3.13 の存在定理で足りている（台帳 T2-3） |
| Rem 2.22（A → W(A/d)） | 一般の Joyal の w と W の δ 構造、W(A/d) の単元判定 | 大 | 後回し（用途は Construction 6.1 が肩代わり） |
| Rem 2.3（Wilkerson：λ 環） | λ 環の定義と定理、Borger | 大 | 入れない（rank 1 の言葉だけなら小） |
| Rem 2.5・2.30・2.37 と Def 2.42〜Cor 2.44 の単体的な版 | 単体的可換環（drafts の A2 の ∞ 基盤） | 大 | A2 が入ってから |
| Lemma 2.38 の無限列 | 原典の外（原典も有限列）。必要なら有向余極限経由 | 中 | 入れない |

## 3. ユーザーに確かめたい点（ノートの側）

1. **§2.1 の番号**：docstring 7 ファイルがノートの番号を引いているため、既存の 2.1.1〜2.1.14 を保ち、新しい三項目（Rem 2.3・Rem 2.5・Ex 2.6）を 2.1.15〜2.1.17 として原典の順の位置に置いた。ページ上で番号が順に並ばない。R2-9 の docstring の直しの後に振り直すか、このままにするか。
2. **Rem 2.29 の読み方**：原典の「ただ一つの δ 構造」は、「この φ を持つ δ 構造がただ一つ」と読まないと成り立たない（\(\mathbb Z_p[x]/(x^2)\) では \(x\mapsto pcx\) も Frobenius の持ち上げ、\(p=2\) の \(\mathbb Z_p[x]/(x^p-1)\) では \(x\mapsto -1\) も）。ノートの証明の中に注として書いた。
3. **補った証明の筋**：原典が「容易」「同様」とだけ書く所を補った箇所がある（Ex 2.20 (3)(4)、Rem 2.22 の Witt 座標、Def 2.42 の後の二つの段落、Cor 2.44 の手順 4、Warning 2.41 の \(1/p\notin R_i\)、Lemma 2.18 の細部、Rem 2.5 の単体的な延長）。ノートでは補ったことを明記してある。
4. **原典の誤植と判断した所**：Def 2.42 の後の「\((f_1,\dots,f_r)\pi_0(B)\)」は \((f_1,\dots,f_n)\)、Cor 2.39 の証明の「Remark 2.36」は Rem 2.37、Rem 2.37 末尾の \(D_{(x)}(\mathbb Z_{(p)})\) は \(D_{(x)}(\mathbb Z_{(p)}\{x\})\)。

## 4. 地図・ノートの側で今回直したこと（参考）

- ノート 02 章：§2.1〜§2.6 の 44 項目すべてを囲み（主張・証明の筋・Lean・原典との差）にした（囲み 50 個）。宣言の file:line 208 か所を照合。
- 地図 items.csv：2.6・2.7・2.15・2.18・2.20・2.27・2.31・2.33（proved → proved_special、W(k) の場合だけ）・2.39・2.41（none → proved_special、前半は本体）・2.42・2.43 を直した。
