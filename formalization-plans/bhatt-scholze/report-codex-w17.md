# BS-W17 作業報告

§1–4 は段0（2026-11-11）の調査、§6 は段1・停止点1の報告。

基準は `math/bs-classical`、main `3520dfa62`（W15 の取り込み `acbf9fc5e` を含む）。指示書 W17、a0-design §2.8–2.9、a1-design §2.4–2.5・§3・D30、D74・D76、草稿 A1/HodgeTateComparison・A0/CechAlexander・A0/BaseChange を照合した。著者版 PDF は main 作業木の `paper/refs/BS-prisms-author.pdf` を読み、Construction 6.1 の式 (6)、Prop 6.2・Thm 6.3（著者版 pp.51–53）、Construction 4.17–4.18・Rem 4.19（pp.41–43）を確認した。段0は紙の検討で、Lean の編集・ビルドは行っていない。

## 1. 最初の確認 — D74

**結論。K2 の d 完全平坦性で Construction 6.1 の古典的な証明に足りる。草稿の `universal61` の型への接続には調整が要る。**

記号を `R := A/p`、`x := d mod p`、`F := modPMap p P.deltaStructure.frobeniusLift` とする。必要な平坦性は式 (6) の中間射

`F₀ : R/(x) → R/(x^p),  [a] ↦ [a^p]`

の忠実平坦性である。

1. K2 の `universalOrientedPrism_frobenius_isCompletelyFlat` は、F による制限スカラー加群に `IsCompletelyFlat (Ideal.span {x})` を与える。`flat_algebraQuotient_of_completelyFlat`（CompletelyFlat/PowerTorsion）で `R/(x) → R/(F x)` の通常の平坦性を得る。`F x = x^p` と二重商の同型で F₀ に移す。
2. `Spec(R/(x^p)) → Spec(R/(x))` は全射。素イデアルに対する Frobenius の逆像は同じ素イデアルで、`(x)` と `(x^p)` の根基は一致する。`Module.FaithfullyFlat.of_comap_surjective` で忠実性を付ける。この Frobenius 剰余に特化した公開補題が新たに要る。
3. 最初の射 `R → R/(x)` は x の正則性から Tor 次元 ≤1。`Andre.perfectPrism_generator_modPrime_regular` は、名前に perfect とあるが、実際の引数は向き付き prism と A/d の p 正則性だけである。
4. 最後の射 `R/(x^p) → B/p` は一元の分冪表示の切断基底で自由・忠実平坦。K1 の `frobeniusDivisionDPFamilyEquiv`・`frobeniusDivision_primeRegular`・`frobeniusDivisionPDCompletionEquiv` と `freeDPTruncated_moduleFree` を再利用し、完備化の mod p 比較と標準基底脚を合わせる。

原典 Ex 3.4 の明記は d 完全平坦である。一方、Construction 6.1 冒頭と草稿 `Construction61Hypotheses.frobenius_flat` は A/p 全体の通常の平坦性を仮定している。草稿 `universalOrientedPrism_frobenius_flat`・`universal61` はこの強い型で書かれている。K2 の公開定理からその型を埋める推論は用意できていない。d 完全平坦から通常の平坦への一般的な移行は使わない。

**提案する接続。** 原典の強い仮定を表す `Construction61Hypotheses` を保ち、本体の一般化された補題は `hF : IsCompletelyFlat (Ideal.span {x}) (baseChangeScalarModule F)` と A/d の p 正則性を明示的な引数に取る。結晶被覆の環・prism の構成そのものは、A/d の p 正則性から K1 で作る。普遍 prism に対しては K2 の完全平坦性と `universalOrientedPrism_mod_generator_p_regular` をそのまま入力する。草稿 `universal61` と、その仮定に添字づけされた被覆・保存性の利用箇所をこの入力へつなぐ型の調整は、停止点0で承認をお願いする。段0では草稿を変更していない。

## 2. H1〜H4 の洗い出しと実装案

### H1 — Construction 6.1 の環・prism と Tor

| 草稿の宣言・群 | 判定と既存部品 | 新しく要るもの・置き場所 |
| --- | --- | --- |
| `freeOrientationRing`〜`universalOrientedPrism_hom`、通常の mod p Frobenius | 古典的。K2 の `UniversalDistinguishedRing`・`universalOrientedPrism`・有界性・正則性・`existsUnique_universalOrientedPrismHom` が本体にある。F の比較は `modPMap` と p 乗の一致を使う | 普遍環を再構成する必要はない。必要な別名・評価の照合と §1 の入力定理を `Prism/Basic/Construction61Frobenius.lean` に置く案 |
| `Construction61Hypotheses`・`universal61` | 古典的な仮定。§1 の通常平坦性と完全平坦性の差がある | 普遍例の入力は K2 の二定理から得る。仮定をまとめる新構造は増やさず、補題の引数に明示する |
| `coverDivision`・`coverDivisionMap`・`crystallineCoverRing`・`coverBase`・`crystallineCover`・生成元・`crystallineCoverMap` | すべて古典的。K1 の r=1 の Frobenius 除算と分冪表示、δ の p 冪ねじれ商、`pdCompletionH0_self_complete_p`、p 正則性の完備化保存を使う | 生の除算と p 冪ねじれ商の同型、完備化の比較、p 正則性、δ 射の合成、α(d)∈(p) を接続する。`Prism/Basic/CrystallineCover.lean` と `Prism/Basic/CrystallineCoverReduction.lean`。prism 射を得た後の α(d)=p·u は既存の `map_generator_unit_mul` で得る |
| `alphaModP`・`torAmplitude_modP_le_one` | 環射と数値的な Tor 評価は古典的。草稿の定理の K は `derivedInfinityCategory` の頂点 | まず `∀ M : ModuleCat (A/p), ∀ i>1, Subsingleton (TorAlg ᾱ i M)` を式 (6) から示す。さらに通常の鎖複体の模型に対する `H^j(K)=0 (j<m) ⇒ H^j(K⊗^L B/p)=0 (j<m-1)`。`HomologicalAlgebra/RegularQuotientFlatTorAmplitude.lean`、BS 固有の分解は `Prism/Basic/CrystallineCoverTor.lean` |
| `crystallineCoverMap_torAmplitude`・有限性の系 | 数値の評価は古典的、現行 `HasFiniteCompleteTorAmplitude` の型は ∞ 側 | D4-04 の上界 3 を保持する。A→A/p と ᾱ で 2、`Kos_B(p,α(d)) ≃ Kos_B(p,0)` の零座標で 1。通常の複体版を `Prism/Basic/CrystallineCoverCompleteTor.lean` に置く。mod p の通常の上界 1 と区別する |

`koszulResidue`・`koszulResidueModule`・`relBaseSequence`・`relSequence`・`relResidueMap`・`relHomologyBaseChange`・`FlatKoszulComparison` は古典的な D20 の補助群である。現状、この草稿内の定義以外に利用が見つからなかった。K3 と Koszul の座標作用の零ホモトピー・底変換を先に再利用し、H1 の証明に実際に使う照合だけを加える。A0 の完全正則性をもう一つ定義し直す案は取らない。

### H2 — Prop 6.2・Thm 6.3 の古典的な入力

- **主張の型案。** `K : CochainComplex (ModuleCat A) ℤ` の実際の導来テンソルを計算する模型について、p 完備性・d 完備性の下で「α に沿う二座標完備底変換が acyclic ⇒ K が acyclic」を示す。射については写像錐に適用し、`QuasiIso` の反映まで出す。通常の `DerivedCategory (ModuleCat A)` で表せる箇所は同型の反映としても述べる。
- **既存部品。** `derived_homology_isZero_of_complete_of_scalarCone_isZero` と `isZero_of_complete_of_smul_surjective`（DerivedCompletion/DerivedPurity）、`flatDerivedBaseChange`・`flatDerivedBaseChangeHomologyNatIso`・`faithfullyFlatDerivedHomology_map_eq_zero_iff`、`derivedRestrictScalars_reflectsIsomorphisms`、`derivedRestrictScalars_isComplete`・`derivedCompletionRestrictionIso` を再利用する。H1 の二つの忠実平坦な射と d 完備 Nakayama、その前後の p 完備 Nakayamaを接続する。
- **D30 の入力。** A₀→A の制限スカラーは完備性と同型の反映を持つ。W15 の `boundedAboveDerivedBaseChangeCompositionIso`・`boundedAboveDerivedBaseChangeSquareIso` は対象ごとの上に有界な比較として使える。任意の射との自然性、完備化との交換、H4 の係数脚との整合性は別に示す。候補は `HomologicalAlgebra/CompleteBaseChangeConservative.lean`、`Prismatic/Construction61Detection.lean`・`Prismatic/AffineCompletedChangeComparison.lean`。
- **有界性の注意。** 草稿の Tor 振幅は `D^{≥m}` についての主張である。既存の `DerivedCategory.Minus` のみへ対象を絞るとこの型を満たさない。任意の加群の Tor 消滅から、実際の鎖複体の模型の次数評価へ進み、その模型が導来テンソルを計算することも含めて示す必要がある。これが H2 の主な追加部品で、上に有界な既存 API だけで済んだとは扱わない。
- **草稿の型の現状。** `CompleteModules`・`moduleInclusion`・`moduleReflection`・`alphaStar`・`ReflectsEquivalences`・`baseChangeB/C`・それらの保存性・`affineModuleDiagram`・`affineCompleteDiagram/Tot`・`baseChange_preserves_affineTot`・`baseChange_cechAlexanderAffine_eq` と `crystallineCoverMap_prismaticCohomology` は ∞ 側の型を含む。`HasFiniteCompleteTorAmplitude`・Tot 交換・A0 の Δ/Δ̄ の底変換も同様である。
- **指示書の説明と現在の型との差。** `HodgeTateIsoStatement` は現在の本体 `HodgeTateCompletedMap.lean:461` では、通常の複体からの写像の全次数の全単射性である。そのため `hodgeTate_iso_crystalline`・`hodgeTate_iso_of_construction61`・`hodgeTate_iso` の結論、および `affineLine_moduleComparison` の結論自体は古典的である。ただし W17 が明示的に HT 比較の組み立てを範囲外にしたことに従い、今回はその入力までを計画する。`bockstein_sq_zero'` の多項式の場合は本体の `HodgeTateBocksteinSquare.bockstein_sq_zero` を再利用する。

### H3 — Construction 4.17–4.18

| 対象 | 既存と残り |
| --- | --- |
| 一般の `cechIndex/Map`・`cechFreeDelta/Map`・`cechEval`・`cechKernel` | 環・添字の定義は古典的。自由 δ 環の一意延長と `IsPrismaticEnvelope.of_closure` が本体にある。J は原典どおり `ker(B→H⁰(LΛ_p(B/J₀B)))` とする。⑤b の `bigCechIdeal` は閉包前の評価核の拡大なので、この閉包との比較を通す |
| `HasEnvelopes`・多項式の場合の存在 | 古典的。一般 R の定義は指定された包絡族と有界性・濃度を入力する形。D21 に沿い、存在を供給する定理は多項式の場合。main の `affineBigCechTerm`・有界性・W15 の変数包絡を使う |
| `cechAlexanderObj`・余単体的対象・弱始性・余積 | 多項式の場合、既存 BigCech の各変数を `D→D/d` の全射で持ち上げ、`BigCechTerm.existsUnique_liftVariables` から射を作る。この補題は `R = polyCompletion P Q.n` 用なので、一般の HasEnvelopes 族には自由 δ 環の普遍性から持ち上げの補題を一般化する。余積は n+1 個の C⁰ から来る変数像を束ね、同じ一意性で `Cofan.IsColimit` を示す。一般の押し出しの存在を仮定する必要はない |
| `smallCechNerveOfCoproducts`・`cechNerveData`・`cechSmall_weaklyTerminal` | 古典的。草稿の `CechNerveData` は `SimplicialObject`、射影、`Fan.IsLimit` と構造射の等式だけを持つ。これを大きさの異なる圏にも使える `CategoryTheory/CechNerveData.lean` に置く案。opposite と同値で site のデータへ移す |
| `cechAlexanderComplex/ReducedComplex` | 古典的。既存の余単体的環と mod d の加群へ `alternatingCofaceMapComplex` を適用する |
| `cechAlexander_isLimitCone_iff`・Δ と Tot の比較・cutoff 不変性・`cechAlexanderAffine_computes` | 現行の型は SSet の錐・∞ 層・Δ の頂点を含む。W17 の対象は、その入力となる弱始性・標準余積・普通の複体の比較 |

置き場所案は `Prismatic/CechAlexanderWeaklyInitial.lean`、`Prismatic/CechAlexanderCoproduct.lean`、必要な一般の定義・閉包の接続を `Prismatic/CechAlexanderEnvelopeData.lean`。小さい模型は既存の `cechAlexanderAffine`・`cechAlexanderOfAffineTerms` を使う。HasEnvelopes からの一般の組み立てと、D21 の存在の適用を分けて主張する。

### H4 — Remark 4.19

型の案は、任意の有界向き付き prism の射 `f : P→P′` と各 n について、`PrismCompletedTensor (A := A) (C := X.B) P′ ≃+* Y.B`（X・Y は両基底の affine 項）、二つの係数脚・δ 構造・元の各 copy の座標との両立、全ての `θ : [m]→[n]` との可換性である。草稿 `cechAlexanderAffine_baseChange` の環の側に一致する。

main には W15 の `exists_completedFreeDelta_baseChange_equiv`・`prismaticEnvelope_completedBaseChange_of_variables` がある。さらに⑤bの枝に、この型を直接覆う部品が既にある（次節）。それらを main への取り込み後に使い、余単体的な比較と通常の交代余面複体への誘導をまとめる。`f(d)=u d′` の単元補正を保ち、生成元を厳密に保つ射だけに限定しない。新規の置き場所は `Prismatic/AffineCechBaseChange.lean`・必要なら `Prismatic/AffineCechBaseChangeComplex.lean`。

## 3. ⑤b との重なりと再利用

読み取り時の枝 `math/bs-d68` は `6a2194c7d`。main に未取り込みのコミットを `git show` で確認した。作業木の未コミット変更は結晶 pd 評価の自然性・切断に集中していた。

| 状態 | 再利用する宣言 | W17 への対応 |
| --- | --- | --- |
| main | `BigCechIndex`・`bigCechEval/Initial/Ideal`・`BigCechTerm`・`BigCechTerm.map/map_id/map_comp`・`bigCechAlexanderOfTerms`・`bigCechAlexander` | H3 の大きい模型、関手性。有界な実在する包絡は `affineBigCechTerm`・`affineBigCechTerm_bounded` |
| main | `BigCechTerm.residueSection`・`residueSection_comp`・`residueSection_variable`・`existsUnique_liftVariables` | R からの剰余脚と弱始性・余積。構造射の両立を含めて再利用する |
| main | `liftFromPolyCompletion`・`polyCompletionCoefficientQuotient_surjective`・`cechAlexanderFrame`・`affineCechAlexanderFrame`・`bigCechToAffineFrame` | 完備多項式からの延長、小さい枠と大きい枠の比較 |
| ⑤b 枝 | `AffineEnvelopeTerm.existsUnique_liftVariables`（AffineCechFrameLift）、`affineCechVertexFrame`、`BigCechVertexFrame.model/vertexFrame/toBig/toFinite/toBig_quasiIso` | H3 の標準模型を site の余単体的対象として使える。既存の混合頂点によるホモトピー・擬同型を再利用する |
| ⑤b 枝 | `exists_affineEnvelopeBaseChange_equiv`（AffineEnvelopeBaseChange）、`affineEnvelopeCoefficientMap/spec/unique/natural`（AffineEnvelopeCoefficients）、`exists_affineEnvelopeCoefficientBaseChange_equiv` | H4 の項ごとの同型と全単体射に関する自然性に直接一致する。新しく同じ比較を作る必要はない |
| main | `crystallineCechSource`・`crystallineCechSourceMap_spec`・`crystallineCechResidueIso`、`pdModelBaseChange` | 結晶側の自由源・mod p 比較と係数変更。H1 の一元の被覆の式 (6) 自体の比較は追加で要る |
| ⑤b 枝 | `CompletedBaseChangeEquivalence/Model`、`ScalarCokernelTensor` と pd 列の完備底変換 | H2/H4 の完備複体の比較の候補。対象ごとの同型と射の自然性を型で確認して利用する |

H3・H4 の実装前に、上記⑤bの既存宣言を含む main を取り込む順序が適切。同じ比較・持ち上げ・ホモトピーの追加は避ける。

## 4. 規模と承認事項

| 段 | 新規分の見込み | 最初に確認する点 |
| --- | --- | --- |
| 1・H1 | 5〜8 本、1,000〜1,800 行 | D74 の剰余 Frobenius の忠実平坦性、被覆の p 正則性、式 (6) の標準脚 |
| 2・H2 | 5〜9 本、1,800〜3,200 行 | 上に有界な API と任意の鎖複体の入力との差、射と完備化に関する自然性 |
| 3・H3 | 3〜5 本、700〜1,400 行 | BigCech の site への読み替え、指定された包絡族と D21 の存在の区別、濃度 |
| 3・H4 | 1〜2 本、200〜600 行 | ⑤b の既存の比較・自然性の再利用と係数脚の照合 |

合計 14〜24 本、約 3,700〜7,000 行。⑤b の取り込み状況と H2 の鎖複体の模型の既存 API により動く。

停止点0で確認してほしい事項は、(1) D74 の明示的な完全平坦性入力と草稿 `universal61` の型の接続、(2) HT 比較の結論の型は現在は古典的だが、W17 は指示どおりその入力までとする整理、(3) H3/H4 の前に⑤bの上記部品を再利用する取り込み順序。承認までは段1を開始しない。

## 5. 段1・中間（2026-11-11、停止点1は未到達）

D77 を含む main を取り込み（枝の merge は `f5e8bc39d`）、H1 の実装を進めた。新規16モジュールで、(a) 通常平坦性から完全平坦性、主元剰余 Frobenius の忠実平坦性と K2 の普遍入力、(b) 結晶被覆の環・prism・標準射・有界性、生の除算包との同型、(c) mod p の分冪表示と標準係数脚、式(6)の分解と通常の Tor 上界一、(d) 任意の複体の半自由分解・K-flat 性、Koszul の実際の比較射と非有界な下界の共通部品、を置いた。K1 の正則列分冪表示と切断基底を再利用し、KST の直接 import は加えていない。

対象ビルド成功。公開77宣言の `#check`・`#print axioms`・`#print sorries` が通り、sorry なし、依存公理は `propext`・`Classical.choice`・`Quot.sound` のみ。既存の数学の宣言と入口・監査登録は変更していない。

残りは、共通の非有界模型を被覆へ適用する下界一・二、完全 Koszul の上界三、drafts の D77 の接続。これらを閉じて停止点1を報告する。

## 6. 段1・停止点1（2026-11-11）

**H1 完了。** 中間コミット `ebf28afd6` と今回の差分で、新規22モジュール・公開の名前付き95宣言を置いた。入口・監査登録と既存の本体の宣言は変更していない。

- D77：`Construction61.completelyFlat_of_flat` が原典の通常平坦性を d 完全平坦性へ送る。普遍例は K2 の二定理を直接使う。
- 被覆の環・prism・標準射・有界性、生の除算包との同型、mod p の分冪表示と係数脚を接続した。K1 の `RegularSequencePD*` と切断分冪基底を再利用した。式(6)の分解と、その後半の忠実平坦性を実際の環射で示した。
- `modPBaseChange_homology_isZero_below` は下界を一、`coverMapToModP_homology_isZero_below` は二だけ下げる。いずれも任意の複体と実際の K-flat 分解射を入力する。
- `crystallineCoverMap_torAmplitude` は `HasCochainCompleteTorAmplitude … ![p,d] 3`。全ての非有界な半自由分解上で、標的の p の錐を通常剰余へ比較し、残りの錐の長完全列から上界三を得た。一般の計算は `HomologicalAlgebra/TwoCoordinateCompleteTor.lean` に置いた。
- 模型の存在は既存の半自由分解から供給し、Koszul 増大との比較が擬同型になることも示した。上に有界な対象へ制限していない。H2 にも使う共通部品を H1 で先行実装したため、段0の本数の見込みより増えた。KST の直接 import はない。

**D77 の drafts 変更。** A1/HodgeTateComparison の `Construction61Hypotheses` の二つのフィールド（通常の平坦性・商の p ねじれなし）は保った。普遍 prism と被覆は本体の模型を参照し、利用箇所を明示的な完全平坦性・p 正則性へ付け替えた。`universalOrientedPrism_frobenius_flat`・`universal61` の強い主張を経由しない。∞ 関手への接続と HT 比較の組み立ては drafts に残し、G10 の後とする。drafts は指示どおり非ビルド領域として扱った。

**検証。** 対象ビルド16本＋6本が成功。名前付き公開宣言77＋18本の `#check`・`#print axioms`・`#print sorries` が通り、sorry なし、依存公理は標準三公理のみ。対象ファイルの sorry・axiom と KST の直接 import も確認した。

段2（H2）へ進む。H3・H4 は⑤bの次の停止点の main への取り込み通知を待つ。
