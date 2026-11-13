# §3 prism：リファクタの提案と、形式化の計画の提案（2026-11-12）

作成：ノートのチャット（形式化の調整役ではない）。§2（`02-delta.md`）と同じ形。**扱いは調整役が判断する。** 事実に推奨を添える。

- 基準：main fb8269303 前後。読み取りだけのエージェント 3 本（ノートの加筆 2 本、コードの見直し 1 本）が調べた。宣言の利用者は全 .lean（本体・drafts・scripts）のトークン索引で数えた（短い名前の一致なので、同名があると多めに出る）。規模の見立ては推測。
- 「主定理の閉包」は `SerrePositivity.Paper.Statement` の import の推移閉包。
- 二種類の提案：
  - **A. リファクタの提案（R3-1〜R3-7）**：今ある本体のコードを直す。数学の主張は増えない。
  - **B. 形式化の計画の提案（§3 の表）**：本体にない、または特別な場合しかない項目を新しく形式化するか。
- 台帳 `refactor-ledger.md` の番号（BR13・BR15・BR18・BR19・BR27〜BR29・BR33・BR44、T3-1・T3-4・T3-5）は、今の状態の確認だけを §2 に書く。

## 0. 規模と配置（事実）

- `BhattScholze/Prism/` は 39 本・11,916 行。主定理の閉包に入るのは 14 本（OrientedPrism、Rigidity、Completeness、Tilt、PerfectPrismHomLift、Perfection/PCompletedPerfection・PrismPerfection、Perfectoid/ の 3 本、Residue/ の 2 本、Tensor/IteratedTensor・PerfectPrismTensor）。
- 閉包の外：Lemma 3.7 (2)(3) と Cor 3.12 の `Prism/Bounded/*`（BS-W15 K4）、`ClassicalPrismPerfection`（W17）、§3 の `Prismatic/`（site・envelope の 22 本）、`Semiperfectoid/` の Thm 3.10 の 5 本。

## 1. A. リファクタの提案（今あるコードを直す）

### R3-1 `IsBoundedPrism`（Def 3.2 (2)）を Prism/ へ下ろし、Prism → Prismatic の逆向きの import を消す【推奨：先に、B3】

- `IsBoundedPrism` は `Prismatic/PrismOver.lean:41`（Def 4.1 の site のファイル）にある。`Prism/Basic/CrystallineCover`・`Basic/UniversalOriented`・`Bounded/CompleteFlatReduction`・`Bounded/PDCompletionPrism`・`Perfection/ClassicalPrismPerfection` の 5 本が `Prismatic.PrismOver` を import し、使うのは `IsBoundedPrism` だけ（確認済み）。本体の利用者は 78 ファイル。
- 述語を使わず `∃ N, ∀ n x, p^n x = 0 → p^N x = 0` と手で書いた箇所が 22（PerfectPrismHomLift 6、例 `existsUnique_perfectPrismHomLift_to_bounded` の `hB` :749／Completeness 2／Tilt 2／Andre/PowerRootEnvelope 13）。
- Lemma 3.8 (2)「完全 prism は有界」に名前の付いた補題がなく、`⟨1, …quotient_p_pow_torsion_killed_by_p⟩` を毎回組む（ClassicalPrismPerfection:46、Cor73PrismComparison 2 回、InitialPrismPerfection、PerfectPrismDivision）。OrientedPrism.lean に置けないのは import の向きのため。
- B3 の配置案（`report-bulk-w1.md:155`）は PrismOver を Prismatic/Site へ移すだけで、逆向きは残る。
- 案：B3 で `IsBoundedPrism` を `Prism/Basic/OrientedPrism`（または新しい `Prism/Basic/Bounded`）へ移し、`OrientedPrism.isBoundedPrism_of_perfect` を足す。手書きの 22 か所は保守で述語に置き換える。

### R3-2 §3 の本体が §7 の Andre/・Semiperfectoid/ の一般の補題に依存している【推奨：B3（BR41 と同じ扱い、台帳にない）】

| importer | import 先 | 使う宣言 | 移し先の案 |
| --- | --- | --- | --- |
| `Prism/Basic/UniversalOriented` | `Andre.PowerRootEnvelope.PrincipalPair` | `principalPair_pairCompletion_{second,first,mod_second_first}_regular`（:295・:501・:521） | `HomologicalAlgebra/DerivedCompletion/Pair/` |
| `Prism/Basic/Construction61Frobenius` | `Andre.PowerRootEnvelope.VarpiPD` | `perfectPrism_generator_modPrime_regular`（:88、4 行） | `Prism/Basic` |
| `Prism/Bounded/PDCompletionPrism` | `Andre.Transfinite.Colimit`、`Semiperfectoid.LciEnvelopeRegular` | `completedUnit_pure_bounded_torsion`（:289）、`pdCompletion_generator_regular_of_completed_scalarCone_homology_isZero`（:67） | ファイルごと §7 へ（R3-3） |
| `Prismatic/FlatCover` | `Andre.Transfinite.Tower` | `isCompletelyFaithfullyFlat_self`（:959）、`Andre.Transfinite.isCompletelyFaithfullyFlat_comp`（Colimit:678） | `CommutativeAlgebra/CompletelyFlat/Basic` |
| `Prismatic/CompletedFreeDeltaFlat` | `Andre.Transfinite.Colimit`、`Andre.PowerRootEnvelope.Completion` | `principalCompletionH0_isCompletelyFaithfullyFlat`（:474）、`isCompletelyFlat_comp`（:629）、`completelyFlat_pair_algebra_of_regular_reduction`（:188） | 同上 |

- 完全平坦性の自明な閉包性質（同型・合成）が `Andre/Transfinite` にあり、`CommutativeAlgebra/CompletelyFlat/`（6 本）にない。利用者は Prismatic・Semiperfectoid・Perfectoidization にまたがる（`isCompletelyFaithfullyFlat_comp` は Semiperfectoid だけで 6 ファイル）。

### R3-3 置き場所【推奨：B3】

Prism/ にある §3 でないもの：
- Construction 6.1 の 8 本（`Prism/Basic/Construction61Frobenius`・`CrystallineCover*`）：B3 の案で HodgeTate/Comparison へ移る（`report-bulk-w1:183`）。状態の確認だけ。
- `Prism/Bounded/PDCompletionPrism`（177 行、docstring は Prop 7.10）：§7 の内容で Semiperfectoid・Andre を import。利用者は `Prismatic/FiniteEnvelopeCompletion` だけで、そちらは B3 で `Semiperfectoid/FiniteEnvelopes/` へ移る。一緒に移す（B3 の案にない）。
- `Prism/Residue/PrismaticResidue`（BR19、762 行）：`OrientedPrism`・`DeltaStructure` を使わず、import は HomologicalAlgebra・CommutativeAlgebra だけ（確認済み）。利用者は Andre の 7 ファイルと `Semiperfectoid/RootEnvelope` の 2 ファイル。**行き先は HomologicalAlgebra**。docstring の :15「Prop 3.13 の底変換の計算に使う」は事実と合わない（Prismatic/ に利用者がない）。
- `Prism/Residue/PerfectDeltaResidue`（219 行、台帳にない）：利用者は `Andre/Perfection/DeltaAlgebra` だけ。docstring の :15「Lemma 3.9 の完全化に使う」は誤り。行き先は `Andre/Perfection/`。
- `Prism/Tensor/` の 3 本（2,312 行）：中身は §8（完全 prism の完備テンソル、Prop 8.13 環版）。`PerfectPrismTensor` の本体の利用者は `Perfectoidization/CompletedTensor` だけ。`IteratedTensor` は名前空間 `SerrePositivity.DerivedCompletion` の一般論。英語の docstring が 71。行き先は Perfectoidization/（ResidueTensor の削除は BR18）。

Prism/ の外にある §3：
- Thm 3.10 の芯が `Semiperfectoid/` に 4 本・421 行（閉包の外）：`PerfectoidPrismPresentation`（`exists_boundedPerfectPrismPresentation`:47）、`PerfectoidWittEquiv`（`exists_fontaineCompatibleWittEquiv`:72）、`FontainePrism`（:29）、`AinfClassical`（`exists_ainfClassicalPrism`:105）。案：`Prism/Perfectoid/` へ。理由：Andre/Variants/Auxiliary・RootedExtension・Transfinite/Tower、Semiperfectoid/RootEnvelope/PerfectPrism・Perfectoidization の 5 本が `exists_perfectoidTrialPrism` を直接使い、表示を手で組み直している（BR13 (b)）。移せば層の向きを気にせず置き換えられる。

### R3-4 名前空間をそろえる【推奨：保守、KL-W1 の改名表で】

- `Prism/Bounded/Completeness`（Lemma 3.7 (1)）・`Tilt`・`PerfectPrismHomLift`（Lemma 4.8）の名前空間が `SerrePositivity.BhattScholze.Andre`（旧 Andre/Remark715 の名残、節の見出しに「André A1-a」が 6 か所）。Lemma 3.7 (2)(3) の `Prism/Bounded/*` は `…Prismatic`、`Prism/Basic` は `…BhattScholze`・`OrientedPrism`。`Andre.` の接頭辞で呼ぶ行が 20 行・14 ファイル（drafts 4 本を含む）。

### R3-5 二重の構成

- (a) Lemma 4.8 の二版：`existsUnique_perfectPrismHomLift`（PerfectPrismHomLift:522、完全 → 完全、両方の商に `Fact (¬IsUnit p)`）と `…_to_bounded`（:749、完全 → 有界、その仮定なし）。前者は後者の特別な場合（完全 prism は有界）。前者の利用者は `Semiperfectoid/Perfectoidization` と監査 2 本。案：前者を後者の系に（保守、R3-1 の後、BR29 の入口と一緒に）。
- (b) 零環の prism が二つ：`PerfectoidPrismPresentation:30`（private `zeroPrism`）と `AinfClassical:116`（その場で組む）。案：公開の `OrientedPrism.ofSubsingleton` を `Prism/Basic` に（小、保守、BR13）。
- (c) Lemma 3.5 後半の向き付き版を毎回手で組む：`ofDistinguished D (f d) (hf.map_isDistinguished P.isDistinguished_generator) hreg hp hd` の形が VariableEnvelope:87、VariableEnvelopeBaseChange:210、AffineCechPrismBaseChange:97、CompletelyFlatPrism:112、DiscretePrism:41（drafts の A0/FlatDescent:109 も同じ形を予定）。案：構成子 `OrientedPrism.ofDeltaHom` にまとめる（B の Lemma 3.5 後半と同じもの）。台帳 T3-5 の「各項で要る形」の実例。
- (d) \(A_{\inf}(R)\) の模型が二つ（推測を含む）：`exists_perfectoidTrialPrism`（PerfectPrismPerfectoid:383）は \(W(R^\flat)\) の d 完備性を仮定しないため `PDCompletionH0 (W(R♭)) p d` の上に作り、`FontainePrism`・`AinfClassical` は Witt の復元を経由して \(W(R^\flat)\) 自身の上に作る。\(W(R^\flat)\) の古典的な \((p,\xi)\) 完備性を直接示せば一本にできる（推測、優先は低い）。
- (e) drafts と本体の重なり（BR40 の材料）：`drafts/A0/FlatDescent` の `isFaithfullyFlat_of_isIso`:135・`IsFaithfullyFlat.comp`:142・`exists_isPushout_isFaithfullyFlat`:152・`exists_boundedPrism_of_completelyFlat`:113 が、本体の `FlatCover:45・61`・`FlatTopologyPushout:43`・`CompletelyFlatPrism:70` と名前・内容で重なる。`A0/PrismaticSite` の `IsFaithfullyFlat`:65・`flatTopology`:106 は本体の `FlatCover:40`・`FlatSiteSheaf:50` と、`A0/PrismaticEnvelope` の `IsCompletelyRegularRel`:59・`prismaticEnvelope_baseChange_of_variables`:89 は本体の `RelativeCompleteRegularity:149`・`VariableEnvelopeBaseChange:132` と重なる（drafts の一部は ∞ の D(A) の模型なので文字どおりの重複ではない）。

### R3-6 docstring【推奨：B3 の docstring の回】

- ノートを引く（`lean-docstrings-citing-notes.md` の 22 か所のうち §3 の 5 か所）：`OrientedPrism:22`（D5）→「Def 3.2 (2) の orientable で向きを選んだもの」、`Rigidity:22`（T3-5）→「Lemma 3.5 の第二文」、`PrismPerfection:22`（BR28）、`PerfectPrismPerfectoid:25`（D8・BR29）、`PrismOver:48`（D16）。
- 古い記述：`PrismPerfection:22`「原典の形の一つの定理にはまとめていない」（今は `ClassicalPrismPerfection:75`）、`Completeness:22`「Lemma 3.7 の (2)〜(4) は未」（(2)(3) は Prism/Bounded）、`PrismaticResidue:15`・`PerfectDeltaResidue:15`（R3-3）、`PCompletedPerfection:23` の「使われ方」（prism の層は監査だけ）、§3 の外で `Semiperfectoid/CharacteristicP:19`「どこからも使われていない」（`Perfectoidization/Derived/ArcValuationExtension` が import）。
- 工程ラベル：§3 関係の 64 ファイルのうち 25 ファイル・67 行（D77、K1・K2、F3〜F7、G9・G10、B4-5、W9-I-11、a0-design §2.7、「drafts と同じ」など）。「旧 …」のパスの注記が 13 ファイル・76 行（BR25）。

### R3-7 使われていない宣言【推奨：保守。原典の項目そのものは残す】

- 監査も含めて参照 0：`classicalPrismPerfection_isBounded`（:46）・`classicalPrismPerfectionMap_generator`（:68）。
- 監査だけ：`completelyFlatCochain_isDiscrete_of_boundedPrism`（CompleteFlatCochain:180、地図の 3.7 (2)）、`isDistinguished_iff_p_mem_span_pow`（OrientedPrism:59、3.1）、`exists_crystalline_iff`（:329、3.3）、Rigidity の 7 宣言（BR44）、`UniversalOrientedFrobenius` の 12 宣言のうち 9。
- 原典の項目にあたる宣言は、利用者がなくても残すことを推奨する。

## 2. 台帳の項目の今の状態

- **BR15（表現を直す必要あり）**：`PCompletedPerfection.lean:394–606` の prism の層（約 25 宣言）を使うのは `scripts/audit_bhatt_scholze.lean` だけ（確認済み）。δ 環の層（`PCompletedDeltaPerfection`、`existsUnique_pCompletedDeltaPerfectionHom` など）は PrismPerfection・`Semiperfectoid/PerfectPrismDivision`・`Andre/Variants/RootedExtension`・`Andre/Envelope/MonicCandidate` が使い、閉包に入る。除算の枝のうち **`PerfectPrismDivision`（517 行）は閉包に入る**（Cor 7.3 の Perfectoidization、RootEnvelope/Source、MonicCandidate）。監査だけなのは `PerfectPrismDivisionComparison`（579 行）。案：(i) prism の層と Comparison を消す（保守、安全）、(ii) Cor 7.3 の経路を W17 の `ClassicalPrismPerfection` に一本化（主経路の書き換えなので E3 の sorry 0 の後）。名前の注意：ここの「PD 版」の PD は \((p,d)\) 完備化（`PDCompletionH0` は `PairCompletionH0 R p d`）で、分冪（Crystalline の PD*）とは別。
- **BR18**：変化なし（ResidueTensor の 11 宣言とも外から参照なし）。
- **BR19**：行き先が具体的になった（HomologicalAlgebra）。PerfectDeltaResidue（→ Andre/Perfection）を足す。
- **BR27・BR33**：閉のまま。
- **BR28**：`ClassicalPrismPerfection` がある（閉包の外、利用者は `InitialPrismPerfection` と stage2 監査）。原典の付随の主張はまだ一つの定理になっていない（B の Lemma 3.9 の行）。PrismPerfection:22 の docstring は古い。
- **BR29**：変化なし（入口はない、drafts の `perfectSiteEquivPerfectoidUnder`（A5/PerfectSite:267–271）は sorry）。R3-5 (a) を足す。
- **BR13 (b)**：`exists_boundedPerfectPrismPresentation` はある。`exists_perfectoidTrialPrism` を直接使う 5 本は R3-3。
- **BR44**：確認済み（`idealTensorEquiv`・`idealBaseChangeEquiv` は scripts だけが使う）。
- **T3-1・T3-4**：閉でよい。**T3-5**：R3-5 (c) の 5 か所が実例。

## 3. B. 形式化の計画の提案（新しく形式化する項目）

「推奨」は、入れる／後回し（使う場所が出たら）／入れない。

| 項目 | 今あるもの・要るもの | 規模 | 依存 | 推奨 |
| --- | --- | --- | --- | --- |
| Def 3.2「prism の圏」 | `Hom`・`id`・`comp` はあるが `Category` の instance がない（Prism/ に Category の定義 0）。site の `PrismOver` には圏がある | 小（〜100） | — | **入れる**（Thm 3.10 の圏同値の前提） |
| Def 3.2 (3) 平坦な prism の射 | `PrismOver.IsFaithfullyFlat`（FlatCover:40）だけ。`OrientedPrism.Hom.IsFlat`・`IsFaithfullyFlat` がない | 小 | R3-1 | **入れる**（site の定義をその略記に） |
| Def 3.2 一般の Cartier 因子 I（D5 の見直し） | Mathlib に `Module.Invertible`（RingTheory/PicardGroup）。導来 \((p,I)\) 完備性は本体に元ごとの `IsModuleComplete` だけ（有限生成元で書く）。向き付き ≌ 向き付け可能の同値は Andre の `BoundedPrismInputUnoriented.equivalence`（InputCategory:395、固定基底）が手本 | 中（1〜2 千） | — | **入れない（当面）**。入れるなら `OrientedPrism`（216 ファイル・1,053 か所）は変えず、上に `Prism` と `OrientedPrism.toPrism` を重ねる |
| （参考）一般の prism の影響 | 固定基底が向き付きなら site の対象は剛性で向き付き（D19）なので、\((X/A)_\Delta\) と E3 は影響を受けない。完全 prism も Lemma 3.8 (1) で向き付けられるので Thm 3.10 も影響を受けない。影響が出るのは Lemma 3.1 (3)・3.5（降下）・3.6・3.7 (4)・3.8 (1) の一般形、全 prism の site、Rem 4.7・Lemma 4.8 の一般の標的、Prop 3.13 の向き付きへの帰着 | — | — | — |
| Lemma 3.1 (3) | ind-Zariski 局所化、\(V(p,I)\) に沿う局所化。Rem 2.16 はある（`DeltaLocalization:148`） | 中 | 一般の prism | 後回し |
| Lemma 3.5 後半（逆） | 向き付き版は R3-5 (c) の構成子と「\((B,(fd))\) が prism ⇔ \(fd\) が非零因子（完備性を仮定）」。⇒ にあたる `Hom.map_generator_mul_injective`（Rigidity:53）はある | 小（50〜150） | — | **入れる**（向き付き）。一般形は一般の prism 次第 |
| Lemma 3.6 | 向き付きでは \(\varphi(I)A=(\varphi(d))\) は自明。distinguished 性は `isDeltaHom_frobeniusLift_general`（FreeDeltaRing:276）と `map_isDistinguished`（DeltaRing:180）、別の生成元は `isDistinguished_factor`（Distinguished:142）。一般形は Lemma 3.1 (3)・2.23・2.24・Pic の議論 | 向き付き 小（〜50）／一般 中 | 一般形は一般の prism | 向き付き版は入れる（優先は低い）、一般形は入れない |
| Lemma 3.7 (3) を圏の同一視として | 今は対象の対応だけ（`exists_boundedPrism_of_completelyFlat_deltaAlgebra`:70）。関手の充満忠実・同値に | 小（〜200） | Def 3.2 の圏・(3) | 後回し |
| Lemma 3.7 (4) | 向き付きでは中身がない | 大 | 一般の prism、3.1 (3)、3.5 の一般形 | 入れない |
| Lemma 3.7 の後の注意（完備平坦な複体の層） | ∞ の降下 | 大 | — | 入れない |
| Lemma 3.8 (1)「任意の生成元が distinguished」と (2) の名前付き補題 | Lemma 2.24 と R3-1 | 小 | R3-1 | **入れる** |
| Lemma 3.9 の付随の主張（BR28 の残り） | \(A_{\mathrm{perf}}\) で \(d\)・\(p\) が非零因子（`DistinguishedRegular` の完全 δ 環の一般形）、\(A_{\mathrm{perf}}/d[p^\infty]=[p]\)（`distinguished_quotient_p_pow_torsion_killed_by_p`）、導来完備化＝古典的完備化（`principalCompletionAdicAlgEquiv`、HA/DerivedCompletion/PrincipalClassicalComparison:108 を二度）、\(IA_{\mathrm{perf}}=(d)\) は向き付きで自明。**注意**：原典の証明は未完備の \(A_{\mathrm{perf}}\) に Lemma 2.34 を当てるが、Lemma 2.34 は p 進分離性を仮定する（ノートの加筆で気づいた、§4 の 2） | 小（200〜500） | — | **入れる**（原典の証明の一か所を形式化で確かめることにもなる） |
| **Thm 3.10 の圏同値（絶対版）** | 部品はそろう：`quotient_isIntegralPerfectoid`:340、`exists_ainfClassicalPrism`・`exists_boundedPerfectPrismPresentation`、`existsUnique_perfectPrismHomLift_to_bounded`:749、`ainfClassicalMap`（AinfClassicalMaps:60）。要るのは完全な向き付き prism の圏と `IsIntegralPerfectoid` の充満部分圏。Mathlib の `Functor.FullyFaithful`・`EssSurj` で足りる。射は向きを保たないので、向き付き完全 prism の圏＝完全 prism の圏（Lemma 3.8 (1)） | 小〜中（300〜800） | Def 3.2 の圏、R3-1、R3-3 | **入れる**。drafts の相対版 `perfectSiteEquivPerfectoidUnder`（A5/PerfectSite:267）は絶対版の under 圏への制限と濃度条件で出せそう（推測）なので、⑤∞ の前に置くと G-A5-4 が軽くなる |
| Thm 3.10 の perfectoid の定義の差 | 原典は BMS18 §3、本体の `IsIntegralPerfectoid` は CLMST Def 2.4.1（`CommutativeAlgebra/Perfectoid/Defs:39`）。同値の証明はない | 小〜中 | — | 後回し（任意） |
| Rem 3.11 | Cohen 環は完全剰余体の場合だけ（`CommutativeAlgebra/Witt/CohenRing`）。\(W[[x]]/(f)\) の表示、Kunz の易しい半分、完全化の忠実平坦性、[Bha18a, Prop 5.1]（外部）。perfectoid 被覆は André の経路にある（BR36） | 中〜大 | Lemma 3.9・Thm 3.10 | 入れない |
| Cor 3.12 全有界 prism の site | 本体は固定基底 \((A,(d))\)・\(R\) 上・濃度 κ の site（`FlatSiteSheaf:50`、実質 Def 4.1）。絶対版でも完備テンソル（`PrismCompletedTensor`）は任意の基底で作れ、層条件は \((*/A)_\Delta\) への制限で出せそう（推測）。「高次コホモロジーの消滅」は全次数の Čech 完全性（FlatCechDescent）まで | 中（向き付き絶対版 1〜2 千）／大（一般） | Def 3.2 の圏・(3) | 後回し（向き付き）、入れない（一般） |
| **Prop 3.13 の一般形** | 鎖：(1) 向き付き・\(J=(d,x)\) 大域・\(x\) が \((p,d)\) 完全正則（相対）← (2) Cor 2.44 の離散版 ← (3) Lemma 2.43 の離散版（台帳 §8 で「中」）← (4) Lemma 2.38・Cor 2.39（済）、Ex 3.4 の Frobenius の完全平坦性（`UniversalOrientedFrobenius:309`）、Def 2.42（`RelativeCompleteRegularity:149`、本体の利用者なし）。離散版の Tor 消滅の帰納法は `Andre/Envelope/JetKoszul`（1,174 行）に一部ある | (1) まで 大（3〜8 千）。底変換 (2) と平坦局所化 (3) は各 中。Zariski 局所の仮定と非向き付きは 大 | §2 の 2.43・2.44 | **後回し**（E3 不要、D21）。やるなら向き付き・大域の形を §2 の 2.43・2.44 と同じ束で。見返り（推測）：今ある三つの特別な場合（Prismatic の変数の場合 1,377 行、`Semiperfectoid/LciEnvelope*` 19 本 2,371 行（Ex 7.9）、Andre/Envelope の根の関係 4 本 3,726 行）をまとめられる |
| Ex 3.14 の一般形 | p 完全に滑らかな代数（Mathlib は `Algebra.Smooth` だけ）、局所正則列、Zariski 局所性 | 大 | Prop 3.13 の完全な形 | 入れない |
| Ex 3.3「結晶 prism は有界」 | 名前付きの補題がない（自明） | 小 | R3-1 | 任意 |

## 4. ノートの側（参考）

1. ノート 03 章：§3 の全 14 項目と Lemma 3.7 の後の段落を、見出しと主張・Lean・証明の囲みにした（15 見出し、番号は小節ごとの 3.k.n）。宣言の file:line 117 か所を照合。補った筋のある証明は 10（ラベル「補った筋あり」）。
2. **原典の証明で気になった所**：Lemma 3.9 の証明は未完備の \(A_{\mathrm{perf}}\) に Lemma 2.34 を当てて \(d\) の正則性を出すが、Lemma 2.34 は p 進分離性を仮定する。\(A_{\mathrm{perf}}\) が p 進分離かどうかは確かめていない。ノートは「完備化の後なら仮定は満たされる」と書いた。B の Lemma 3.9 の行で形式化すれば確かめられる。
3. 地図 items.csv：3.1・3.5・3.6（\(\varphi(d)=p\cdot u\) は一般の向き付き prism では成り立たない、例 \(\mathbb Z_p[[q-1]]\) と \(d=[p]_q\)）・3.8・3.9・3.10・3.11・3.12 を直した。
4. 生成器：見出しが「原典 Lemma 3.7 の後の段落」のような項目は、その番号の状態でなく Lean の囲みで確認のラベルを決めるようにした（§2 の注意 2.6.2・2.6.3・2.6.5 も直った）。
