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

## 7. 段2・停止点2（2026-11-11）

**H2 完了。** 新規8モジュール・728行で、通常の非有界な複体上の完備底変換の零性と擬同型の反映を置いた。入口・監査登録、既存の本体の宣言、drafts の HT 比較の組み立ては変更していない。

- `CochainFlatDetection`：任意の複体の忠実平坦な底変換によるホモロジーの零性の反映と、実際の K-flat 模型の正則列商と Koszul 模型の零性の同値。
- `CochainCompleteDetection`：任意の複体の主元完備 Nakayama、全座標に完備な複体の有限 Koszul 簡約による検出、標準の完備化単位を使った一回・二回の完備化からの検出。
- `CompleteBaseChangeConservative`：標的主元の剰余が正則列商を忠実平坦に覆う、という実際の環射の分解から二座標完備底変換の零性の反映を得る一般の環の定理。
- `Prismatic/Construction61Detection`：標的の (p,p) の反復完備化による `completedCoverModelFunctor` を明示し、式 (6) の (p,d) の商からの忠実平坦射と標的の p 正則性を接続した。任意の非有界な複体の実在する半自由分解に適用でき、模型の存在も証明した。普遍例は K2 の完全平坦性と p 正則性を直接入力する。
- `CompleteCochainCone`・`Prismatic/Construction61Reflection`：具体的な完備化と実導来完備化の自然同型と三角関手性から、実際の完備底変換した射が擬同型なら元の射も擬同型になることを示す。さらに `completedCover_semifree_map_quasiIso_iff` が完備な半自由模型間の射の前後の擬同型性の同値を与える。
- `SemifreeBaseChangeModel`：半自由複体の K-projective 性から、模型間の擬同型が任意の係数拡大で保たれることを示す。H1 の任意の半自由分解の存在・前後の K-flat 性、既存の `restrictedBaseChangeComplexIso`、実際の Koszul 増大の比較射と合わせて、通常の導来テンソルを計算する模型であることを確かめる。Tor の下界一・二、完全振幅三は H1 の非有界な定理を再利用し、D⁻ だけの入力には縮めていない。
- D30：既存の任意の導来対象に対する `derivedRestrictScalars_isComplete`・`derivedRestrictScalars_reflectsIsomorphisms` を再利用し、`DerivedCompletion/PairRestriction` に二座標の `pairCompletionRestrictionIso` と全ての導来射に関する自然性を置いた。普遍基底への制限で用いる比較で、係数射の平坦性や対象の有界性は不要。

**検証。** 対象8モジュールのビルドが成功（依存分を含む4,235ジョブ）。公開24宣言の `#check`・`#print axioms`・`#print sorries` が通り、sorry なし、依存公理は `propext`・`Classical.choice`・`Quot.sound` のみ。新規ファイルに KST の直接 import はない。

H3・H4 は、指示書 §3 の⑤bの四モジュールの main への取り込み通知を待つ。⑤bの枝の直接 merge はしていない。HT 比較の写像の組み立てと Tot の比較は G10 の後に残す。

## 8. 段3・H3 先行分（2026-11-11 夕、停止点3は未到達）

指示書 §4 に従い main を `2af7f8377` まで取り込み、main にある部品だけで H3 の先行分を実装した。新規15モジュール・1,230行。既存の数学の宣言・drafts・入口・監査登録は変更していない。

- `CategoryTheory/CechNerveData`：対象と射の宇宙を分けた通常の圏の Čech データ、標準頂点の余積から反対圏の積への構成、必要な有限冪を保つ関手による移送、弱始性から弱終性への反転。
- `CechAlexanderPresentation/RingPresentation/Coproduct/Choice`：変数像の一意な δ 環射を site の射へ移し、余単体的対象・弱始性・標準頂点を脚とする余積・Čech データを構成した。二つの包絡の選択の比較は全単体射に自然な同型。一般の包絡と BigCech の site の可換条件は共通の `ofRingLift` で共有した。
- `CechAlexanderEnvelopeData/Lift/Assembly/FreeDelta/EnvelopeMaps`：`HasEnvelopes` は drafts と同じ存在命題にした。J は原典どおり導来 p 完備化の H⁰ への核で、通常の閉包へ置き換えていない。`IsPrismaticEnvelope.of_closure` により生の評価核の普遍性を取り出す。任意の HasEnvelopes から実際の site の対象・余単体的構造・弱始性・標準余積を構成し、構造射が包絡の単位を介して完備自由 δ 環の構造射を延長することまで示した。
- `BigCechSitePresentation/Alexander/Affine`・`CechAlexanderBounds`：main の `BigCechTerm`・`existsUnique_liftVariables`・`residueSection` と既存の有界な `affineBigCechTerm` を再利用した。各元を各頂点の変数にする場合の濃度を cutoff で抑え、有限完備多項式の `HasEnvelopes` を供給した。site の構造射の台環射は既存の `BigCechTerm.map` と一致するので、既存 `bigCechAlexander` の構造射を作り直していない。
- `CechAlexanderComplex`：通常の A 加群の交代余面複体と、各 prism の mod d を取った交代余面複体を定義した。後者は A/d 上の代数を取って A に係数を制限する。導来極限・Tot・RΓ との比較は含めていない。

**検証。** 全15モジュールの対象ビルドが成功。公開72宣言の `#check`・`#print axioms`・`#print sorries` が通り、sorry なし、依存公理は `propext`・`Classical.choice`・`Quot.sound` のみ。KST の直接 import、sorry、公理の新設はない。新しい鍵で整理券は常に一枚とし、鍵は対象ビルドと Lean の宣言監査の間だけ使用した。

**残り。** 停止点3にはまだ達していない。⑤b の `AffineCechFrameLift`・`BigCechVertexFrame`・`AffineEnvelope*` を要する部分と H4 は、main への取り込み通知の後に進める。⑤b の枝の直接 merge はしていない。一般の包絡の存在を今回追加したという意味ではなく、一般は HasEnvelopes の下の構成、実在する族の供給は main の有限完備多項式の場合である。

## 9. 段3・H3 の小さい site と既存模型の比較（2026-11-11、停止点3は未到達）

main `7a3a0f965` を取り込み（merge `f47a76b45`）、H3 の先行分を続けた。新規3モジュール。既存の宣言・drafts・入口・監査登録は変更していない。

- `CategoryTheory/CechNerveTransport`：標準余積を保つ関手による Čech データの移送、小さい同値模型への移送、同値による弱始性と反対圏での弱終性を示した。圏の対象・射・小さい模型の宇宙を独立に取る。
- `CechAlexanderSmall`：drafts の古典的な `smallCechNerveOfCoproducts`・`cechNerveData`・`cechSmall_weaklyTerminal` を本体に置いた。`EssentiallySmall` は drafts と同じ明示的な仮定で、一般の site の本質的小ささをここで新しく証明したという意味ではない。値は通常の圏の `CategoryTheory.CechNerveData` で、SSet・∞ 層・Tot は用いない。
- `CechAlexanderBigComparison`：HasEnvelopes で選んだ族と main の任意の BigCechTerm の族を、site 上の全単体射に自然な同型 `cechAlexanderBigSiteIso` で比較した。その自然同型から、通常と mod d の交代余面複体の実際の同型を得た。有限枠との擬同型や prism の底変換の比較ではなく、同じ変数の普遍性を持つ二つの大きい模型の比較である。

**検証。** 対象3モジュールのビルド成功。公開12宣言の `#check`・`#print axioms`・`#print sorries` が通り、sorry なし、依存公理は標準三公理のみ。鍵は対象ビルドと宣言監査の間だけ使用し、待ちは一枚ずつとした。

停止点3はまだ未到達。指定された⑤bの4モジュールが main にないことを再確認した。`AffineCechFrameLift`・`BigCechVertexFrame`・`AffineEnvelope*` を要する H3 の残りと H4 は、取り込み後に続ける。

## 10. 段3・H3/H4 完了（停止点3）

⑤b の途中の登録 `724b03fa2` を含む main を取り込んだ（merge `a4fedc98c`）。⑤b の枝の直接 merge はしていない。今回の追加は新規6モジュール、公開21宣言。§8・§9 と合わせて段3は新規24モジュール、公開105宣言。既存の数学・drafts・入口・監査登録は変更していない。

- `Prismatic/PrismaticFrameCoproduct`：既存の `PrismOverVertexFrame.lift/hom_ext` から、任意の変数添字の枠の標準余積、各次数の弱始性、反対圏の Čech データを構成した。
- `Prismatic/AffineCechSiteNerve`：`affineCechVertexFrame` を直接再利用し、drafts の `cechAlexanderAffine_isCoproduct`、有限 affine 模型の弱始性、小さい site の Čech データと弱終性を本体に置いた。`EssentiallySmall` は drafts と同じ明示的仮定。
- `Prismatic/AffineCechChosenComparison`：既存の `BigCechVertexFrame.model` と先行分の `bigCechSiteAlexander` を site 上で比較した。HasEnvelopes から選んだ包絡の複体との実際の同型を作り、⑤b の `toBig_quasiIso` をその同型で移して有限 affine 枠からの擬同型 `affineToChosenCech_quasiIso` を得た。持ち上げ・混合頂点のホモトピー・大小の比較の証明は再実装していない。
- `Prism/Bounded/CompletedTensorRingMaps`：完備化 H⁰ の既存の環としての一意延長から、完備テンソル積の環射の両脚による判定を得た。両脚が δ 射なら全体も δ 射であることを、既存の δ 射の延長と接続した。標的の p と左生成元の像の導来完備性を明示する一般の補題。
- `Prismatic/AffineCechPrismBaseChange`：既存の `exists_affineEnvelopeCoefficientBaseChange_equiv`・`affineEnvelopeCoefficientMap_spec` を再利用した。項ごとの実完備テンソル積に標準の δ 構造と左生成元による prism を与え、`cechAlexanderAffine_baseChange` として drafts の古典的な存在の型（両脚・δ 同型・イデアルの像・基底・各頂点の座標）を本体に置いた。生成元の厳密な保存は要求せず、一般の prism 射を許す。
- `Prismatic/AffineCechCoefficientComplex`：`affineEnvelopeCoefficientMap_natural` の全単体射に関する自然性を、基底の下の余単体的代数の自然変換と実際の交代余面複体の射にまとめた。項ごとの底変換の右脚はこの指定された係数変更であり、比較・持ち上げをもう一つ作っていない。

項ごとの完備導来底変換を single 対象で計算する部分は、main の `affineEnvelopeTermCompletedBaseChangeIso`・`affineEnvelopeTermCompletedBaseChangeToTargetIso` を再利用する。新設した係数変更の余鎖写像は通常の複体の射であり、複体全体の Tot・導来極限・Δ の底変換の同型を証明したという意味ではない。その部分は指示書どおり G10 の後に残す。

**検証。** 段3の全24対象モジュールのビルドが成功。公開105宣言の `#check`・`#print axioms`・`#print sorries` が通り、sorry なし、依存公理は `propext`・`Classical.choice`・`Quot.sound` のみ。新規ファイルに KST の直接 import・sorry・新しい公理はない。鍵は `--wait 3600`、整理券は一枚ずつ、対象ビルド・Lean の監査の間だけ使用した。検証ログは `/tmp/serre-w17/h34/build-all.log`・`audit.log`。

**停止点3に到達。** 登録対象は §8 の15本、§9 の3本、今回の6本（計24本）。入口・監査の登録と取り込みは調整役へ渡す。続いて指示書 §5 の H5 は段0の洗い出しだけを報告し、実装の前で止める。

## 11. H5 段0：Prop 7.10 の古典的な部分（停止点0）

指示書 §5 に従い、H3・H4 の停止点3（`22bd55917`）の後に行う紙の洗い出し。対象は drafts `A3/LciAndQuasiregular.lean` の qrsp 節（261–486行）、a3-design §1・W9-I-32〜45、原典 Notation 7.1・Lemma 4.8・Lemma 7.7–7.8・Example 7.9・Proposition 7.10。H5 の Lean の編集・ビルドはまだ行っていない。

### 宣言ごとの切り分け

「古典」は実際の環・prism・通常の導来圏で作るもの、「境界」は結論の一部が古典でも現在の型が Δ に依存するものを指す。境界の宣言を弱い型へ置き換えて完了とはしない。

| drafts の宣言 | 分類と今回の切り出し |
| --- | --- |
| `PadicBase`・`padicBaseAlgebra` | 古典。実主元完備化と ℤ_p の比較による作用 |
| `CotangentPCompletelyFlat`・`IsQuasiregularSemiperfectoid` | 現行は ∞ 側。cotangentWedgeAtAlgebra・loop・VertexIso を含む。弱い古典的な定義には置換しない |
| `ainfCoefficients`・`ainfPrismRing`・`ainfTheta`・`ainfDelta` | 古典。Witt 環と零環の分岐 |
| `AinfData`・`ainfData`・`ainfPrism`・`ainfResidueAlgebra`（local instance を含む） | 古典。θ・核の生成元・剰余同型を、固定した Witt 環上で照合 |
| `InitialDelta` | 境界。指定 Δ の台環と Frobenius を参照する。模型の始性はその台環と同定する前に直接証明する |
| `QrspDiscrete`・`qrsp_isDiscretePrismatic` | ∞ 側。指定された Δ の離散性。今回は実包絡模型 B の正則性・完備性まで |
| `qrspHTMap` | 境界。模型では明示した単位 `η : S → B/(d)` を作る。Δ の HT 単位との同定は残す |
| `qrsp_completelyFaithfullyFlat` | 境界。模型の η による **S 上**の p 完全忠実平坦性は古典。一般 qrsp の HT filtration と指定 Δ への移送は残す |
| `rootPolynomials`・`rootBase`・`rootX`（R 作用を含む） | 古典。根付きモノイド環と実 p 完備化の模型 |
| `rootBase_perfectoid`・`rootBasePrismMap` | 古典。根付きモノイド環の perfectoid 性、完全基底からの一意な持ち上げ |
| `rootRelations`・`rootQuotient`・`rootQuotientMap`（R 作用を含む）・`regularSemiperfectoid` | 古典。有限 T と任意添字の S′ の具体環。実 H⁰ 完備化との比較が必要 |
| `regularSemiperfectoid_prismatic` | 混合。Xi−fi の正則性、有界な包絡 B_T、全有界試験 prism への始性を切り出す。perfectBaseComparison の同型と Δ の離散性・InitialDelta は ∞ 側 |
| `qrsp_initial` | ∞ 側かつ一般形は別単位 W9-I-43。T・S′ の始性から一般 qrsp の始性を主張しない |
| `perfectedCoefficients`・`perfectedPrism`・`perfectedPrism_isPerfect`・`toPerfectedPrism` | 古典。δ 完全化の後の (p,d) 完備化と標準射 |
| `IsCor73Comparison` | 古典。S′ 上の単位を保つ唯一の prism 同型 |
| `rootQuotient_initial` | 境界。模型 B_S′ の全有界試験 prism への始性は古典。QrspDiscrete・InitialDelta との同定は残す |
| `rootQuotient_prismatic_perfection_eq` | 混合。模型の完全化、perfectoidization、Cor 7.3 候補との S′ 上の唯一の同型を切り出す。指定 Δ からの同定は G10 後 |

lci 節の前提では `exists_lciEnvelope` の古典的な存在は W15 の `exists_bounded_lciRelationEnvelope` で供給済み。`lciTensorDelta` とその射の判定は古典的な再利用候補。一方 `lciDerivedEnvelope_isEnvelope_of_discrete`・`universalModDComparison`・`lci_envelope_surjective_invert_p_universal`・`prismaticCohomology_lci_eq_envelope` は指定された導来包・Δ との比較を含み、今回の実包絡の構成とは分ける。`lciCompletionH0Comparison` は実完備化の比較の入力を再利用するが、drafts の ∞ 側との接続は残す。

### 証明の筋・再利用と不足

1. **根付き基底と A_inf。** `PowerRootPolynomial` の多項式上の自由性・分数指数基底、既存の Witt δ 環・`exists_distinguished_fontaine_kernel_generator` と perfect prism の構成を使う。多変数モノイド表示の比較、p 完備化の perfectoid 性、固定 θ の核の照合が不足。`rootBasePrismMap` は `existsUnique_perfectPrismHomLift_to_bounded` を直接使う。非零の Fact を全体に追加せず、零環の枝を残す。
2. **有限 T。** Xi−fi の monic な正則列と quotient の一様な p 冪ねじれの有界性を証明し、任意の持ち上げ wi に移す。`exists_bounded_lciRelationEnvelope`、`IsFiniteLciRelationEnvelope`、`IsPrismaticEnvelope.exists_initial_of_base_quotient` を使って実際の有界な B_T と単位を返す。D76 の有界性は `completedBaseChange_bounded_torsion_pure` へ渡す。Lemma 4.8 の既存の有界標的への一意な基底持ち上げにより、基底 A′ を忘れても全有界試験 prism に対する始性を得る。
3. **忠実平坦性。** K5 の `LciEnvelopeReduction`・`LciEnvelopeResidue`・`LciEnvelopeCompletedResidue`・`LciEnvelopeDiscrete` は正則性・完全平坦性を供給する。忠実性はまだ別途必要で、`exists_deltaDivision_freeVariable_residue_faithfullyFlat` の実際の mod(p,d) の忠実平坦性を、特殊化・完備化へ移す。主張の底は T（または S′）で、単位 η による `IsCompletelyFaithfullyFlat (Ideal.span {p}) (B/(d))` とする。
4. **任意添字 S′。** 有限部分集合の B_T 間の δ 射を包絡の一意性から構成し、固定した基底 A 上で生成元と単位を揃える。`deltaAdjoinDivisionFiniteColimitEquiv` とその δ 保存を再利用する。その生の余極限を実 (p,d) 完備化へ移し、正則性・一様なねじれの指数・忠実平坦性・S′ 単位・始性を証明する部分が主な不足。生の余極限と完備余極限は同一視しない。
5. **完全化と Cor 7.3。** 非完全な源からの延長には `existsUnique_deltaPerfectionPDCompletionHom` を使い、既存の完全化比較と generator・quotient・unit の式を接続する。`exists_perfectoidization_of_perfectPrism_quotient` へ r の全射性と r(d′)=0 を渡し、両普遍性で S′ 上の唯一の δ-prism 同型を得る。零環の枝は別に閉じる。既存の `CompatibleRootPerfectoid` の比較は候補に使えるが、全ての根を殺すイデアルと、Xi(0) のみを殺す S′ のイデアルを混同しない。

本体の型案は、入力を perfectoid R と有限 r・fi（または任意 J の零関係）だけとし、実環 B、有界 prism Q、単位 `η : T →+* B ⧸ Q.ideal`（S′ でも同様）を存在として返す。結論に **任意の有界 prism Y と任意の `z : T →+* Y/Y.ideal` に対する `∃! g : OrientedPrism.Hom Q Y, g.quotientMap.comp η = z`** を置く。有限の場合は任意に持ち上げた wi に関する `IsFiniteLciRelationEnvelope` と、η による p 完全忠実平坦性も返す。S′ の完全化比較は、同じ S′ 単位を保つ唯一の δ-prism 同型として述べる。包絡や持ち上げの存在を新しい仮定束へ移す型にはしない。

Lemma 7.7 は `DiscreteDelta`・`DiscretePrism`、Lemma 7.8 は `CategoryTheory.initial_of_retraction_idempotent`・`PrismRetract.exists_split_idempotent` を再利用する。T・S′ は包絡の直接の普遍性を優先する。K2 の Frobenius は D77 の **d 完全平坦性**の入力、K4 は `exists_boundedPrism_of_completelyFlat_deltaAlgebra` を使う。普通の Frobenius 平坦性を追加要求しない。D36 の Frobenius による δ 射の判定は標的の p 正則性が要るので、全有界標的への包絡の普遍性をその判定だけで置き換えない。

### 型と原典の強弱の確認

- `IsQuasiregularSemiperfectoid` は有界ねじれを既に含み、原典 Notation 7.1 と整合する。D76 の `exists_lciEnvelope` の hR も残っている。T・S′ では有界性の仮定を新設する前に、monic な具体表示と perfectoid R の p ねじれ（既存の `p_mul_eq_zero_of_pow_mul_eq_zero`）から供給する。任意の perfectoid 商の有界性は主張しない。
- `rootBase`・`rootQuotient` の `completionRing` は **PrincipalCompletionH0（実 H⁰ LΛ_p）**であり、古典的 AdicCompletion と定義的には違う。原典の p 完備環、および有限 T の未完備商との一致は証明すべき比較である。新本体は一般の実完備化 API を直接使い、E3 の ∞ interface を import しない。drafts の定義を勝手に古典的完備化へ変更しない。
- `qrsp_completelyFaithfullyFlat` の型の底 S と HT 単位は正しい。一方、証明コメントの一般 qrsp の「分裂 filtration」は平坦性だけからは出ない。一般形では mod p の平坦な余核による Fil₀ の純粋な包含を用いる必要がある。有限 lci の自由な場合と分ける。一般形のこの証明と Δ 比較は G10 後に残す。
- `regularSemiperfectoid_prismatic` の最初の同型は **G-A2-10 の完全基底比較**で、単なる A2(4) の底変換だけとは扱わない。
- 原典 Lemma 4.8 は任意の prism を対象とするが、再利用する本体は有界標的版。今回の公開始性の範囲は drafts・E3 が用いる **全有界試験 prism**とする（完全標的は有界）。相対 A′ 上の包絡そのものの普遍性は任意の prism 上のまま。p 正則な標的だけには狭めない。
- 現時点で D76 のように「本体化のため直ちに修正すべき偽の強い型」は確定していない。上の未証明の完備化比較と filtration のコメントは区別して記録する。Δ の離散性を模型の離散性に読み替えて既存宣言を完了とはしない。

### 置き場所・規模・順序

新数学はすべて新規ファイル。`BhattScholze/Semiperfectoid/` に `RootFamilyBase`・`RootFamilyPerfectoid`・`RootRelationRegular`・`RootRelationEnvelope`・`RootRelationFaithful`・`RootRelationColimit`・`RootRelationCompletion`・`RootRelationInitial`・`RootRelationPerfection` の族を置く案。一般の有限部分族の完備化補題は `CommutativeAlgebra/` または `HomologicalAlgebra/DerivedCompletion/` に切り出す。

| 束 | 不足する新規モジュールと行数の見込み |
| --- | --- |
| 根付き基底・A_inf と θ | 2〜3本、500〜1,000行 |
| 有限正則列・有界ねじれ・実完備化比較 | 2〜4本、700〜1,400行 |
| B_T・単位上の忠実平坦性・始性 | 2〜3本、600〜1,200行 |
| 完備有限部分族の余極限と B_S′ | 2〜4本、1,000〜1,800行 |
| 完全化と Cor 7.3 候補の一意同型 | 1〜2本、300〜600行 |

合計 **9〜16本、約3,100〜6,000行**。一般 qrsp の Δ・HT 比較はこの工数に含めない。まず有限 T の実包絡と全有界標的への始性、その後 S′ の完備余極限、最後に完全化の比較の順とする。**H5 は停止点0。実装は検収を待つ。**

## 12. H5 有限 T の途中：正則性・実完備化比較・実包絡

main は `0ec3d99b0` まで取り込み済み（停止点3の登録 `f3ff89155` を含む）。**停止点4には未到達**。有限 T の忠実平坦性、drafts の固定 A_inf と ULift 添字までの照合が残る。

- `RootFamilyBase`・`RootFamilyPerfectoid`：任意添字の根付きモノイド環の実 H⁰ p 完備化、古典的完備化との単位を保つ比較、perfectoid 性。既存 `Perfectoidization/Derived/RootAdjunction` の古典的な私有補題 `monomialAdicCompletionPerfectoid` を `import all` で再利用した（同じ証明を作らない）。この import の推移閉包には E3 interface があるが、新規宣言の型に ∞ 側の対象はない。監査も標準三公理のみ。
- `RootFamilyFractionBasis`・`RootRelationPolynomial`・`RootRelationRawBasis`・`RootRelationRawRegular`：有限関係商の小数指数自由基底、忠実平坦性、生の Xi−fi の Koszul 正則性、係数と同じ p ねじれの指数。
- `PointwiseProjectiveCompletion`・`PointwiseKoszulCompletion`・`KoszulCompletionRegular`：係数環上で代数と関係商が自由な場合、Koszul 分解を実各項完備化で移す。係数の p 正則性は不要。係数制限後の K-projective 模型とホモトピー同値を使い、実際の完備環上の Koszul 複体へ比較した。
- `FiniteQuotientComplete`・`PrincipalQuotientComparison`・`RootRelationCompletion`・`RootRelationBounded`：有限関係の通常商の導来完備性、生の関係商の実完備化との単位を保つ環同型、有界ねじれ、古典的 p 完備性、通常商の再完備化との同型。drafts の定義は変更していない。
- `PerfectoidPrismPresentation`・`PerfectEnvelopeInitial`・`KoszulRingEquiv`・`PrismRelationQuotient`・`PerfectoidRelationEnvelope`・`PrismInitialTransport`・`RootRelationCoordinates`・`RootRelationEnvelope`：完全 prism の剰余表示（零環を含む）、任意の有界標的への一意な基底持ち上げ、K5 の有界な有限 lci 包絡。公開した `exists_rootRelationEnvelope` は具体的な持ち上げ・実包絡・剰余単位・その係数射との対応式と、全有界試験 prism への始性を返す。始性を p 正則な標的へ狭めていない。
- `RootFamilyReindex`：小さい添字とその宇宙持ち上げの基底比較（各段の根と単位を保存）。有限関係イデアル・商までの照合は続ける。
- 承認済みの `qrsp_completelyFaithfullyFlat` の証明コメントだけを修正。一般形の Fil₀ の包含は「mod p の平坦な余核による純粋な包含」とし、drafts の型は維持した。

検証：22 新規モジュール、1,803行、87個の名前付き公開宣言。有限 T の包絡まで `lake build ...RootRelationEnvelope`（4,705 jobs）と添字変更の個別ビルドが成功。全22本を import した `#check`・`#print axioms`・`#print sorries` は87件すべて成功、sorryなし・標準三公理のみ。ログ：`/tmp/serre-w17/h5/finite/build-28.log`、`audit-1.log`。入口・全体監査への登録は行っていない。

次は、普遍除算の実 mod (p,d) の忠実平坦性を、関係商への底変換と実完備化へ移す。途中の一般完備テンソル H⁰ 比較は `HomologicalAlgebra/DerivedCompletion/` の新規ファイルに置く。現在の合計規模は上限内で、S′ の生の余極限と完備余極限の比較はまだ実装していない。

## 13. H5 有限 T の途中：指定した単位の完全忠実平坦性

§12 の途中コミットは `bf03c92b1`。**まだ停止点4ではない**。

- `exists_bounded_lciRelationEnvelope_faithful` は K5 の存在を強め、同じ関係イデアルの有界な実包絡と、その標準剰余単位による **関係商上の p 完全忠実平坦性**を返す。関係商の有界性は D76 の形のまま使う。
- `exists_perfectoidRelationEnvelope_faithful`・`exists_rootRelationEnvelope_faithful` により、有限 T の標準単位の忠実平坦性と、全有界試験 prism への始性を同時に得た。元の係数射を保つ単位の式を結論に含めた。
- 忠実性は `exists_deltaDivision_freeVariable_residue_faithfullyFlat` の実 mod (p,d) を再利用し、自由変数包絡の p 完備化、関係商への完備底変換へ移した。一般 qrsp の Fil₀ の分裂は仮定していない。
- `CompletedBaseChangePrincipalH0`・`PrincipalFiniteResidue`・`CompletedTensorFlat`・`CompletedTensorFaithful` は通常テンソル環の実 H⁰ 完備化を扱う。完全平坦性は既存の導来完全平坦性と G9 の離散性、有界な係数のねじれを使用。忠実性は元の代表元を保つ mod p の環同型から得る。
- `TensorProduct/QuotientFactor`・`CompletedTensorRelationResidue`・`CompletedTensorRelationFaithful` は、そこで消える関係を基底・係数から除いたテンソルと包絡の生成元剰余との比較で、標準単位を保つ。既存の完備化の定義を変更していない。

追加14モジュール・1,289行・17個の名前付き公開宣言。ビルド `...RootRelationEnvelopeFaithful`（4,719 jobs）成功。追加14本の `#check`・`#print axioms`・`#print sorries` は17件すべて成功、sorryなし・標準三公理のみ。ログ：`/tmp/serre-w17/h5/finite/build-45.log`、`audit-faithful.log`。§12 と合わせて36新規モジュール・3,092行・104宣言。入口と全体監査への登録は未実施。

残りの有限 T：ULift 添字・その全初期関係の商・実 H⁰ 完備化までの具体比較と、固定した A_inf の θ・δ・剰余表示の照合。前者を編集中。S′ の実装はまだ始めていない。6,000行の上限は引き続き確認する。

## 14. H5 停止点4：固定 A_inf 上の有限 T

**停止点4に到達。有限 T の公開出力を閉じ、ここで止める。** §12・§13 の途中報告で残していた固定 A_inf と ULift の具体比較は、この節で解消した。

### 実装した型と対応

- `RootRelationLift`・`RootRelationLiftInitial`：Fin r と ULift の各段の根・係数・初期関係イデアル・通常商を比較し、通常の有限 T と ULift 関係商の **実 H⁰ p 完備化**との単位を保つ同型を証明した。外側の環圏の完備化表示まで含む `exists_rootRelationLiftCompletionEquiv` と、そこへの忠実平坦な単位・全有界標的への始性がある。殺すのは Xi(0)−fi で、全ての根を殺すイデアルではない。
- `PerfectoidWittEquiv`・`FontainePrism`：既存の完全 prism の Witt 復元、完備 Witt 商の Fontaine 比較の全単射性、θ の自然性を再利用し、剰余が R の完全 prism を **固定した W(R♭)** へ δ・θ を保って戻す。Witt 環をその完備化に置き換えるだけでは済ませていない。
- `AinfClassical`・`AinfClassicalMaps`：drafts の `ainfCoefficients`・`ainfTheta`・`ainfDelta` と同じ二分岐の定義式で、実際の有界な完全 prism と θ を保つ剰余同型を供給した。p が単元の枝では perfectoid R が零環であることから直接構成し、非零性を仮定として足していない。選択した prism・剰余作用と、根付き基底への `rootFamilyAinfMap` もある。
- 最終出力 **`exists_rootRelationAinfEnvelope`**（`RootRelationAinfEnvelope`）：perfectoid R と任意の r・fi を入力し、ULift 根付き基底の固定 A_inf 上で、θ(wi)=Xi(0)−fi を満たす wi、有界な実 prism Q、イデアル (d)⊔(wi) の実 `IsFiniteLciRelationEnvelope`、実完備な有限 T から Q/(d) への単位 v を返す。v は元の θ と係数射を保ち、**T 上** p 完全忠実平坦。さらに任意の有界 prism Y と任意の T→Y/(d) に対し、v を保つ Q→Y が一意に存在する。標的を p 正則なものに狭めていない。

K5 の `exists_lciRelation_regular_completedTensor` と包絡の分類・存在、普遍自由変数除算の実 mod (p,d) の忠実平坦性、Lemma 4.8 を再利用した。D76 の T の有界性は具体表示から供給し、入力に新しい有界性仮定を足していない。D77 の普通の Frobenius 平坦性への逆戻りもない。新しい数学は新規ファイルだけで、既存の本体の宣言・入口・全体監査の登録は変更していない。A3 drafts は承認済みの filtration の証明コメントだけを修正した。

Δ との同定、`QrspDiscrete`・`InitialDelta` への移送、一般 qrsp の HT filtration は完了と扱わず、G10 側に残す。S′ の生の余極限・完備余極限・完全化と Cor 7.3 は、次の停止点5の対象であり、まだ実装していない。

### 検証と規模

今回の最後の追加は **7モジュール・42個の名前付き公開宣言**。H5 の合計は **43新規モジュール・3,860行・146個の名前付き公開宣言**（docstring の補充を含む）。

- 最終ビルド：`RootRelationAinfEnvelope` と従来の `RootRelationEnvelope` の二つの葉から全43本を含め、**4,729 jobs 成功**。共有鍵は `--wait 3600`、待ちは常に一枚、鍵はビルド・Lean 検証の間だけ使用した。
- 公理監査：87＋17＋42件の `#check`・`#print axioms`・`#print sorries` がすべて成功。**146件とも sorry なし、標準三公理のみ**。直接の KST import もない。
- 最終ログ：`/tmp/serre-w17/h5/finite/build-stop4.log`。監査：同ディレクトリの `audit-1.log`・`audit-faithful.log`・`audit-stop4.log`。登録用43本の一覧：`stop4-modules.txt`。
- 基点は main `0ec3d99b0`（停止点3登録 `f3ff89155` を含む）。最後に main `cba436208` の関連差分（PointwiseExtension・PointwiseTensor など）も閲覧した。今回の導来 H⁰・Koszul 完備化の比較と同じ宣言の追加はなく、既存の D30・G9 の API を再利用している。⑤b の枝は直接取り込んでいない。

本体合計6,000行の上限まで **2,140行**。停止点5では、有限部分族の遷移を単位を保つ一意な δ 射で作ること、一様なねじれ指数を取り出すこと、生の余極限と実完備化の比較が不足する。S′ の完備余極限と完全化をこの残量で閉じられるかを開始時に再見積もりし、合計6,000行または S′ 部分2,500行を超えそうなら指示どおり止める。

入口と全体監査への43本の登録、および取り込みの検収は調整役に委ねる。**停止点4で停止。**

## 15. 停止点4後：S′ 開始時の再見積もりと規模による停止

main `ac33a3640`（指示書 §7）を fast-forward で取り込んだ。開始時の再調査では、残りは **約2,300〜3,200行**、既存3,860行と合わせて **約6,160〜7,060行**を見込む。数学的な最小行数ではなく、現在の API から単位・比較まで公開する実装量の見積もりである。残量2,140行を超えそうなので、**指示書 §6・§7 に従い、新規実装に入る前に停止する。停止点5には未到達。**

| 残る束 | 新規行数の見込み |
| --- | ---: |
| 任意添字の根付き基底と有限関係部分族の比較、実 H⁰ と S′ の比較 | 450〜650 |
| 有限包絡の遷移、基底・生成元・単位の整合性 | 300〜400 |
| 一様ねじれ評価、生の余極限の還元と実完備化、有界 prism と完全忠実平坦性 | 750〜1,000 |
| 完備余極限上の S′ 単位、全有界標的への一意延長 | 400〜550 |
| 完全化の標準射・商、Cor 7.3 の単位を保つ唯一の同型と零環の枝 | 400〜600 |
| 合計 | **2,300〜3,200** |

S′ だけでも **1,900〜2,600行**であり、部分上限2,500行を超える可能性もある。当初 §11 の S′ 1,000〜1,800行から増えた理由は、次の比較を独立に作る必要があるため。

- `exists_rootRelationAinfEnvelope` は変数全体が有限の定理。任意 J の固定した根付き基底上で有限個の関係を殺す定理とは型が異なる。`RootFamilyFractionBasis` の指数分解は `[Finite J]` と `Finsupp.equivFunOnFinite` を使う。`rootFamilyBaseReindex` は添字の全単射であり、有限部分集合の包含・補変数への分離・反復完備化との比較は供給しない。既存の宣言を変更せず、この比較を新規に置く必要がある。
- 有限 T ごとの `IsBoundedPrism` や `rootRelationRawCompleted_bounded` の「ある指数が存在する」だけでは、図式全体に一様な指数は得られない。生の関係商は `rootRelationRaw_torsion_bound` と perfectoid のねじれ評価から指数1を持つ。`DerivedPurity` の `moduleTowerLimit_power_torsion_bound_of_relations` を再利用して、指定した指数を実完備化へ渡し、それを余極限に渡す補題が要る。存在指数から一様性を仮定することはしない。
- `deltaAdjoinDivisionFiniteColimitEquiv` は、固定した δ 基底上の **生の**除算環の有限部分族余極限を全族へ比較する。δ 保存・各段の公式・`deltaAdjoinDivisionFiniteColimit_p_mul_injective` は再利用するが、有限 T の選んだ完備包絡の図式、剰余の完全忠実平坦性、S′ の実 H⁰ 完備化との比較までは含まない。生の余極限を完備余極限と同一視して行数を削れない。
- `RootEnvelope/Source` の bounded-support の Tor 交換と実還元も確認した。これは Thm 7.4 の根添加・除算源の図式であり、今回の Xi(0) のみを殺す商との比較が別途必要。既存の Tor 交換自体は作り直さず利用するが、全ての根を殺す商への置換はしない。

再開時は、上表の順に `RootFamilyFiniteSubfamily`・`RootRelationUniformBound`・`RootRelationColimit`・`RootRelationCompletedColimit`・`RootRelationInitial`・`RootRelationPerfection` の新規ファイル族に分ける案。一般の指数保存・完備余極限の補題は `HomologicalAlgebra/DerivedCompletion/` に置く。完全化側では非完全な源からの `existsUnique_deltaPerfectionPDCompletionHom`、`exists_perfectoidization_of_perfectPrism_quotient`、既存の完全 prism の比較を再利用し、S′ 上の単位を保つ同型まで示す。全有界試験 prism の範囲・零環の枝・drafts の定義は維持する。

今回は調査と本報告のみ。新しい数学・drafts の変更・ビルド・鍵の取得は行っていない。有限 T の43モジュール・3,860行の検証結果は §14 のまま。**規模上限による停止であり、S′ と完全化は未実装。**

## 16. H5 停止点5a：S′ の完備包絡と始性／残る平坦性の規模で停止

main `06672de8f`（停止点4の登録 `e4c3276a8` と指示書 §8）を取り込んだ。**§8 の「S′ の完備余極限と全有界標的への一意な延長」には到達した。停止点5・W17全体の完了ではない。**

### 本体に入れたもの

- `RootRelationCompletedInitial.exists_rootRelationCompletedInitial`：任意添字 J、perfectoid R から、固定 A_inf 上の全初期関係の**有界な実包絡**、S′ の実 H⁰ 完備化からの剰余単位、その θ・係数射との対応式、**任意の有界試験 prism Y と任意の S′→Y/I に対する唯一の prism 射**を返す。標的の p 正則性は課さない。
- `RootRelationFiniteEnvelopeDiagram`：全変数の持ち上げを一度選び、同じ基底上で全有限段を構成。各段の単位の p 完全忠実平坦性から、剰余のねじれを**全段で共通の指数1**で評価する。
- `FiniteEnvelopeDiagram`・`FiniteEnvelopeRawColimit`・`FiniteEnvelopeCompletion`：包含の一意な遷移、合成則、生の δ 環余極限、その分母の正則性と剰余の共通指数、実 (p,d) 完備化、全関係の包絡の普遍性。生の余極限を完備環とは同一視しない。
- `RootRelationCompletedSurjective`：通常の全初期関係商も指数1を持つ。前完備性により、根付き基底から **S′ の実 H⁰ への標準射は全射**。`exists_rootRelationCompletedAdicEquiv` は実 H⁰ と古典的 p 完備化を単位を保って比較する。通常商を分離的とは仮定しない。
- 任意添字の有限台小数指数基底、通常の変数部分族商、有限初期関係の Koszul 正則性と実完備化、指定指数を保存する G9 の補題を追加した。根の第零段 Xi(0) だけを消し、全ての根を消す商とは区別した。零環の枝も維持した。

K5 の存在・剰余単位の忠実平坦性、Lemma 4.8、既存の δ 余極限・実完備化の普遍性を再利用した。一般の指数補題は `HomologicalAlgebra/DerivedCompletion/`、一般の通常商・余極限は `CommutativeAlgebra/` に置いた。既存の BS にある一般補題 `completedUnitReductionIso`・`discrete_completelyFlat`・`natCast_complete_restrict` は import all で再利用し、同じ補題を作り直していない。

### §15 の見込みと実測

未登録の補題をテーマごとの14ファイルへまとめ、固定基底の最終構成で使わない添字射・二段完備化の一般化は外した。以下は共有ファイルの各節を対応する束に配分し、共通見出しを先頭の束に計上した行数。

| §15 の束 | 見込み | 実測 | 差・残り |
| --- | ---: | ---: | --- |
| 任意添字・有限部分族・S′ の実 H⁰ の比較 | 450〜650 | 715 | 上端より65行増 |
| 遷移と固定基底・生成元・単位の整合性 | 300〜400 | 403 | 上端より3行増 |
| 共通指数・生の剰余・有界な実完備化・忠実平坦性 | 750〜1,000 | 913 | **有限段の忠実平坦性まで。S′ 単位の忠実平坦性は下記の残り** |
| S′ 単位・全有界標的への一意延長 | 400〜550 | 333 | 下端より67行減 |
| 完全化・Cor 7.3 | 400〜600 | 0 | 未着手。全射性の入力は上に実装済み |

追加 **14モジュール・2,364行・106個の名前付き公開宣言**。H5 合計は **57新規モジュール・6,224行**。ビルド **4,738 jobs 成功**、106件の `#check`・`#print axioms`・`#print sorries` も全件成功し、**sorry なし・標準三公理のみ**。ログ：`/tmp/serre-w17/h5/sprime/verify-consolidated.log`。登録用14本の一覧：同ディレクトリの `modules.txt`。直接の KST import、既存の本体宣言・drafts・入口・全体監査の変更はない。

### 残る S′ 単位の完全忠実平坦性と停止理由

**§11・§15 で予定した、S′ 単位そのものの p 完全忠実平坦性は未実装。** 今回の公開した始性の結論には追加していない。この不足は G10 側の Δ との同定とは別の、古典的な証明の残り。

各有限段で底環 T_F が変わる。既存の `directLimit_flat`・`faithfullyFlat_algebraDirectLimit`・`isCompletelyFaithfullyFlat_algebraRingDirectLimit` は固定した底環上の API なので、T_F 上の完全忠実平坦性をそのまま S′ 上の主張へ移せない。追加で要るのは、(1) 共通の剰余底環へ導来基底変更した図式と、その余極限の比較、(2) 実完備包絡の生成元剰余との単位を保つ比較、(3) 実際の Tor 消滅と忠実性の移送。mod p の通常の平坦性だけで Tor 消滅を済ませない。

この残りを **約700〜1,000行**と再見積もりする。S′ 部分の残量は636行なので、予定どおり含めると **S′ 合計3,064〜3,364行**となる。さらに完全化・Cor 7.3 の400〜600行を含む H5 合計は **7,324〜7,824行**の見込み。

指示書 §8 の停止条件「合計が7,500行、または S′ の部分が3,000行を超えそうなとき」に該当するため、**ここで規模による停止。完全化にはまだ入っていない。** 一般 qrsp の Δ・HT 比較も従来どおり drafts に残る。入口と監査への14本の登録は調整役に委ねる。

## 17. H5 停止点5：完全化と Corollary 7.3（W17 の区切り）

11-12 朝の範囲変更に従い、**S′ 単位の p 完全忠実平坦性は後回し**とした。§16 の不足 (1) 共通剰余底環への導来底変換と余極限の比較、(2) 実完備包絡の生成元剰余・単位との比較、(3) Tor 消滅と忠実性の移送は未実装のまま記録する。E3 の S′ の経路ではこれを使わず、既存の始性と今回の完全化比較を使う。

### 追加した出力

- `Prism/Perfection/ClassicalPrismPerfection`：任意の prism Q の δ 完全化を実 (p,d) 完備化して、標準の完全 prism、有界性、標準 δ-prism 射、生成元の像、完全標的への一意延長を構成した。**源 Q の完全性は仮定しない**。既存の `existsUnique_deltaPerfectionPDCompletionHom` と生成元の像に沿う完備性を再利用した。
- `Semiperfectoid/InitialPrismPerfection`：全有界標的への初期剰余単位 v から、完全化後の完全標的への始性と、標準剰余単位の `IsPerfectoidization` を得る。perfectoid 標的の完全 prism 表示と Lemma 4.8 を使い、標的を p 正則な場合に狭めていない。
- `Semiperfectoid/Cor73PrismComparison`：同じ perfectoid 化を与える完全 prism の間に、単位を保つ唯一の δ-prism 射と両逆を構成した。これを、固定完全 prism の全射商から作る Cor 7.3 の**実 δ 除算・完全化・実完備化の標準候補**へ適用する。零環の商の枝も独立の補題で同じ唯一の同型まで示した。
- `Semiperfectoid/RootRelationPerfection.exists_rootRelationPrismaticPerfection`：任意添字 J と perfectoid R に対する固定 A_inf 上の S′ の有界初期包絡を返し、その完全化の商が S′ の perfectoid 化であること、Cor 7.3 の候補との **S′ 単位を保つ唯一の δ-prism 同型**を示した。根付き基底が零環の枝では S′・完全化係数環・その剰余も零環であり、この枝でも同型を出す。根付き基底が非零でも S′ が零環になる場合を排除していない。

S′ は停止点5aの実 H⁰ 完備化のまま。未完備な通常商との全射と、古典的 p 完備化との単位を保つ比較は `RootRelationCompletedSurjective` を再利用した。drafts の定義や型は変更せず、Δ との同定・一般 qrsp の filtration・G10 への移送は drafts に残す。

### 検証・規模・取り込み

追加は **4モジュール・443行・20個の名前付き公開宣言**。§15 の完全化の見込み400〜600行に対し実測443行。H5 合計は **61新規モジュール・6,667行**（S′ 部分は2,364行のまま）で、上限7,500行・3,000行の内側に収まった。

- 最終の葉 `RootRelationPerfection` から4本を含むビルドは **4,744 jobs 成功**。20件の `#check`・`#print axioms`・`#print sorries` が全件成功し、**sorry なし・標準三公理のみ**。
- ログ：`/tmp/serre-w17/h5/perfection/build-stop5.log`・`audit-stop5.log`。登録用4本の一覧は同ディレクトリの `modules.txt`、公開宣言の一覧は `declarations.txt`。
- 数学は新規4ファイルだけ。既存の本体宣言・drafts・入口・全体監査の登録は変更していない。直接の KST import なし。共有鍵は `--wait 3600`、待ちは一枚、ビルドと Lean 監査の間だけ使用した。
- 基点は停止点5a `218f8939f` のまま。KL-W1 の改名表は未受領なので、独自の改名や KL 枝の直接取り込みは行っていない。停止点5aの14本と今回の4本の main 取り込み・登録は、KL-W1 の取り込み後に調整役の改名表へ追従してから行う。

**今回の絞った範囲で停止点5に到達し、W17 の区切りとして停止する。** S′ 単位の完全忠実平坦性の三つの不足は後回しであり、一般 qrsp の離散性・Δ との同定まで完了したとは扱わない。

## 18. KL-W1 改名追従：参照採取器の失敗により保留（11-12）

開始 HEAD は `ce4bba8f6`、作業木はクリーンで、進行中の検証・未検証の下書きはなかった。配布された `bs-classical-files.json` の18本は枝固有の Lean 全18本と一致し、10:21以後に追加すべきファイルはない。写した一覧は `klw1-follow-bs-classical-files.json`。直接の importer は12本で、すべて対象18本に含まれる。

**main の取り込み前の collect が8本成功後、9本目で失敗したため、指示どおりソースを書き換えずに報告する。** 失敗するのは `Semiperfectoid/RootFamilySparseBasis.lean` の `rootFamilySparseFractionCoordinates_smul`。142行の `rw [add_smul, map_add, ...]`、147行の `simp`、160行の `rw [smul_add, map_add, ...]` が採取器による再解釈で失敗する。最初のエラーは `map_add` の書き換え対象が見つからないもの。停止点5のビルド済みソースをそのまま入力しており、採取前後で変更していない。

再現したコマンド（専用 worktree で `source ~/.zshenv` 後）：

```sh
klw1=/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout
zsh scripts/refactor/with_build_lock.sh --wait 3600 -- gtimeout --foreground 1700s \
  python3 "$klw1/scripts/refactor/klw1_namespace.py" collect --root "$PWD" \
  --files /tmp/serre-w17/klw1-follow/bs-classical-files.json \
  --output /tmp/serre-w17/klw1-follow/before_index
```

- `collect` 終了コード2。ログ：`/tmp/serre-w17/klw1-follow/collect.log`。部分採取8本は同ディレクトリの `before_index/`。このディレクトリは未完で `files.json` がなく、rewrite の入力に使っていない。再採取時には新しい出力先を指定する。
- **書き換え0ファイル・0行。プレビューと `review.json` は未作成**であり、保留0件と扱わない。main `19f081dcb` 以降の取り込みと移行後の対象ビルドも未実施。改名表・採取器・既存の証明はいずれも変更していない。
- 採取器が独自のオプションで同期再解釈すること、通常の `lakefile.toml` に `maxSynthPendingDepth = 3` があることは確認したが、失敗との因果は未確認。通常 Lean 実行との比較診断は鍵の待ちに並べた後、ツール修正待ちで止めるため取り下げた。**新しい待ち・ビルド・監査は残っていない。**

KL-W1 側で採取器の扱いを確認・修正してもらってから、同じ18本を main 取り込み前に採取し直し、rewrite・差分確認・main 取り込み・対象と直接の importer のビルドを再開する。W17 の数学の検証結果は §17 のまま。
