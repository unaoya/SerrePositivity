# Cohen–Gabber：微分を軸にした形式化計画

更新：2026-10-14。状態：**整域版のCohen–Gabber正規化は証明済み**。
Gabberの微分による経路で係数切断・微分パラメータ・同じ有限評価の分離性を構成し、
`Inputs.cohen_gabber_normalization` を既存の公開型のまま証明へ置換した。
任意剰余体を許し、次元0・極大イデアルが零の体の分岐も含む。
公開入口と `Section2.lemma_2_2` の公理は `propext`・`Classical.choice`・`Quot.sound` のみ。
最終実装・検証は§9.12を参照。主定理に残る外部引用は5件、保留K理論は2件。
一般の被約環版は今回の整域版の範囲に含めない。
一般p-basisの逆方向の特徴付けなど、今回の証明に不要な拡張は将来の課題として残る。

以下の§1〜8と§9.1〜9.11は設計・実装の履歴であり、各記録時点の「未完了」はその時点の状態。
現在の完成判定はLeanソースと最終公理監査を正本とする。

この文書を引用2の証明経路・依存関係・受入条件の正本とする。
[次の実装単位とコード確認に基づく詳細計画](#9-コード確認後の詳細実装計画2026-10-14)を末尾に追加した。
[1〜3の計画](local-algebra-1-3.md)は共通基盤と過去の実施記録、
[完備化の統合計画](adic-completion-integration.md)は共通完備化APIの所有・分担を保持する。

## 1. 固定する最終目標と原典

最終入口は [Inputs/CohenNormalization.lean](../SerrePositivity/Inputs/CohenNormalization.lean)
の `Inputs.cohen_gabber_normalization`。公開型は変更しない。
標数p>0の完備Noether局所整域D、dim D=h、任意の剰余体kについて、
係数写像κ:k→Dとパラメータyを実構成し、A=k[[X₁,…,X_h]]からの評価Fを作る。
同じFについて単射性・有限性・指定剰余写像への全射性を供給し、
Fが誘導する分数体拡大の分離性と `IsScalarTower` まで接続する。
kの完全性・有限p-rankは最終定理に追加しない。

原典の正本はOrgogozoによる **訂正を含むExposé IV §2.1**：
[Travaux de Gabber, GTG.pdf](https://www.cmls.polytechnique.fr/perso/orgogozo/travaux_de_Gabber/GTG/GTG.pdf)。
比較・補題番号の旧版対応にはGabber–Orgogozoの
[2008年版 §7](https://www.cmls.polytechnique.fr/perso/orgogozo/articles/Sur%20la%20p-dimension%20des%20corps.pdf)
を使う。arXiv:0706.0671v1やGTG-v2を訂正版と同一視しない。
特にGTG.pdf §2.1.11は旧版の係数体変更箇所を訂正している。
§1.2.5の連続微分の普遍性にも、対象加群の位相に関する注意がある。
EGA 0_IV §20・§21とBourbaki AC IXの使用箇所はG0で個別に照合する。
これらの補題も証明課題とし、新しい引用としてコードに移さない。

原証明の流れは、有限個のp-basis方向を扱う中間係数体を作り、
その上の完備微分の生成的次元を計算し、係数体の持ち上げを変更して次元をhにするもの。
微分が基底となるf_i∈m_Dを選び、既存のパラメータτ_iを
`y_i = τ_i^p * (1 + f_i)`へ変えて分離的な有限正規化を得る。
現行の整域版では、複数の極小素イデアルに同時に対応する帰納法は初期対象に含めない。

Kurano–Shimomotoの超曲面・Weierstrass・座標変更による経路は比較資料に残す。
同じCohen–Gabber定理の二つの証明を並行実装しない。
既存のWeierstrass APIは再利用可能だが、採用経路の必須工程には置かない。

## 2. 微分の対象と仮定を先に固定する

通常の `KaehlerDifferential` と連続／完備微分を区別する。
通常のΩ_{S/R}が有限生成であることを、Sが冪級数環という理由だけで推論しない。

最初の位相的範囲は、有限変数冪級数環・完備Noether局所環と、
指定イデアル進の分離完備加群。一般の任意の位相加群へ最初から拡張しない。
`S ⊕ M`の平方零拡大の位相とスカラー作用の連続性が普遍性に必要かも確認する。
位相の選択・係数制限・次数のずれを各証明へ散在させず、共通入口で供給する。

候補モデルは `AdicCompletion I Ω[S/R]`。
これは定義を置いただけでは連続微分を表さない。
δ(I^(n+1))⊆I^n M、普遍写像の延長、連続導分との対応を証明してから採用する。
原典の分離完備化の位相と一致しない場合は、冪商の逆極限・連続導分の普遍対象へ修正する。
モデル変更の根拠はこの節に記録し、証明経路の切替は自動で行わない。

数学的な導分・p-basis・同型を表す構造は許容する。
「生成的階数=h」「分離的正規化が存在する」などを未証明のフィールドとして
一括で受け取る構造体・型クラスは作らない。
条件付き定理は対象・写像・仮定を明示し、最終適用で実際に供給する。

## 3. 確認済みAPIと、確認していない接続

対象は `lake-manifest.json` の固定Mathlibと現在のコード。宣言の所在を確認した台帳であり、
下記すべての組合せを型照合・ビルド済みという意味ではない。

| 材料 | 確認した入口 | この経路での扱い |
| --- | --- | --- |
| 通常の微分 | Mathlib `Kaehler/Basic`：`KaehlerDifferential.D`、`span_range_derivation`、導分の普遍性 | 定義・普遍性を再実装しない |
| 通常の右完全列 | 同：`mapBaseChange`、`exact_mapBaseChange_map`、`map_surjective` | 完備微分の完全列へそのまま読み替えない |
| 多項式の微分 | Mathlib `Kaehler/Polynomial`：`mvPolynomialBasis`、`polynomialEquiv` | 冪級数の連続微分の基底への出発点 |
| 微分の有限性 | `KaehlerDifferential.finite`、仮定 `Algebra.EssFiniteType` | 有限代数S/Rで供給する。冪級数環S/kに無条件で使わない |
| 分離性 | Mathlib `Unramified/Field`：`FormallyUnramified.iff_isSeparable`、仮定 `EssFiniteType` | 分数体拡大の有限性と作用の両立を供給して使う |
| 完備化の完全性 | Mathlib `AdicCompletion.map_exact`と既存`AdicCompletionExact` | 有限加群等の仮定を確認して適用。無限生成な通常のΩへ自動適用しない |
| 有限加群の完備性 | `AdicCompleteness`・`AdicCompletenessSup`・`AdicCompletenessClosedQuotient` | 完備微分と通常の相対微分の同一視、像の閉性に再利用 |
| 完備化とテンソル | 既存`AdicCompletionTensor`・`AdicCompletionScalarRestriction` | 係数作用と対象イデアルが一致する場合だけ利用。一般比較を重複実装しない |
| 正規化の共通部分 | `AdicPowerSeries`、`PowerSeriesRegular`、`PowerSeriesLocalStructure`、`FiniteNormalizationTools` | 評価・基底・有限閉ファイバー・単射性を再利用 |
| 既存の下流 | `GenericEtale.exists_finite_etale_away_of_generic`等 | 分離的基底の選択を証明した後の適用先。存在の代用品ではない |
| p-basisと完備微分の専用API | 今回の探索範囲では最終構成を供給する宣言を未確認 | G0で検索・型照合を続ける。「Mathlibに存在しない」とは断定しない |

## 4. 共通定理として作るステートメント

以下は数学的な型案。Lの実装名は末尾の進捗記録に示す。それ以外の仮称を
実装済みの宣言名として説明資料へ引用しない。

### L：一般線形代数と導分の生成

L1：有限次元Lベクトル空間V、span_L(W)=V、b:Fin n→V、n≤finrank_L Vなら、
各w_i∈W∪{0}で `LinearIndependent L (fun i => b i + w i)` となるものがある。
Lの無限性は要求しない。原典の線形代数補題に対応し、係数体変更に使う。

L2：整域Sの分数体L上のベクトル空間Vへの導分δについて、δ(S)がVを生成するなら、
任意の非零イデアルH⊆Sのδ(H)もVを生成する。
Leibniz則とHの非零元のLでの可逆性から証明する。
位相・Noether性をこの補題に入れない。完備微分のδ(S)による生成は別に証明する。

### P：p-basisと指定持ち上げ

P1：体kのp乗部分体k^p上で、指数0,…,p−1・有限台のp単項式が基底となる族を扱う。
存在、部分族の独立性、有限部分の中間体、微分による特徴付けを整備する。
無限添字を `Finite`・`Fintype` で制限しない。

P2：標数pの完備Noether局所環D、指定剰余体同型Res(D)≃k、p-basis b_iと
その任意の持ち上げβ_i∈Dから、κ:k→Dを実構成する。
剰余体上の両立、κ(b_i)=β_i、一意性を証明する。
整域性は必要な補題でだけ使い、係数体の存在全体へ自動で追加しない。
既存の `PerfectNilpotentLifting` は完全体の場合の先行成果として使えるが、
任意のkが完全だと仮定してP2を済ませない。
P2の係数体の構成は `PBasisCoefficientField.lean` の
`existsUnique_coefficientRingHom_of_residueEquiv` で実装済み。
この部分のNoether性・整域性は不要で、同標数と極大イデアルについての完備性で証明した。

### M：連続微分・冪級数・有限代数

M1：S=R[[X₁,…,X_n]]、連続R導分S→Mが、各X_iの像で一意に定まる。
適切な分離完備S加群Mに対して普遍性を証明し、完備微分をS^nへ同定する。
一般係数Rで証明できる部分を体・Dのパラメータに固定しない。
積位相でのM1は `ContinuousPowerSeriesDerivation.lean` と
`PowerSeriesContinuousDifferential.lean` で実装済み。
有限変数・離散係数での変数イデアル進位相との一致は `PowerSeriesAdicTopology.lean`、
実際のイデアル進加群への接続は `AdicPowerSeriesDerivation.lean` で実装済み。
終域加群の `IsHausdorff` からT2性を供給し、通常の導分の連続性も冪の評価から証明済み。
通常Ωの分離商と完備化の同型は `PowerSeriesSeparatedDifferential.lean` と
`PowerSeriesCompletedDifferential.lean` で実装済み。後者は完備化したdX_iを基底として供給する。
この同定は一般の可換係数環と有限変数で成立し、Noether性・体・標数は不要。
実際のGabberの有限代数側の加群についての分離性・有限性はM2の適用時に確認する。

M2：k→R→Sが両立し、R・Sが指定位相で完備、必要な微分加群が有限な場合、
連続微分の右完全列を構成する。S/Rが有限なら、通常のΩ_{S/R}の有限性と完備性を確認して
完備微分と同定する。像の閉性、完備化後の余核、係数制限を個別に証明する。
通常の相対微分の完備化との同型と係数制限の全射性は
`CompletedRelativeDifferential.lean` で実装済み。有限S/Rより広いessentially finite type S/R、
Noether局所環S、極大イデアル以下の完備イデアルIで扱う。
通常の推移列の像の閉性にはSの完備性は不要。
完備化後の像の閉包と核の一致は `AdicCompletionKernelClosure.lean` の一般定理から
`CompletedDifferentialTransitivity.lean` に接続済み。
完備化した中項が有限なら像自身と核の一致も得られる。
`CompletedKaehlerFinite.lean` は有限生成イデアルI、前完備なS、有限型の閉ファイバーS/Iから
完備Ω_{S/k}の有限生成性を証明する。通常Ωの有限生成性・Noether性・体・標数は不要。
`PrimaryCompletedDifferential.lean` は共通剰余体と準素性から閉ファイバーの有限性を供給し、
通常の有限正規化の同じ係数写像・パラメータへ実際に適用した。
有限型の閉ファイバーの条件を満たす推移列では、像と核の一致も条件付き入口へ接続済み。
A=k[[X]]、変数イデアルJ、その像I=JS、I進完備なSについては、
`PowerSeriesBaseChangeDifferential.lean` がS⊗_A 完備Ω_{A/k}と
AdicCompletion I (S⊗_A Ω_{A/k})を同定する。元の微分のテンソルとの両立も証明済み。
`PowerSeriesDifferentialTransitivity.lean` が完備基底微分からの写像を推移列へ接続し、
その像と係数制限の核を変数の像の微分が生成する部分加群へ同定する。
`PBasisCofiniteField.lean` と `CofiniteCoefficientDifferential.lean` が中間係数体κ_eの有限性と
閉ファイバー・完備微分の有限性を供給する。
`CofiniteCoefficientNormalization.lean` はκ_e[[X]]からX_i↦τ_i^pとする有限単射を供給する。
`PowerSeriesPowersCompletedDifferential.lean` はp乗への評価で係数制限の核が零となることを供給する。
既存の核の生成元の計算と、導分が標数の冪を消す定理を適用する。
その係数制限の全射性から、係数環上の完備微分と通常の相対微分を同定する。
`PowerSeriesPowersFractionDifferential.lean` は同じ写像の分数体の通常微分へ局所化し、元の普遍微分との両立も確認する。
`CofiniteCompletedDifferentialComparison.lean` はκ_eと準素パラメータについて、閉ファイバーの有限性とイデアル進完備性を供給して適用する。
極大イデアル進の完備微分も、両方の完備微分の有限性と交差する完備性を確認して同じ通常微分へ同定する。
通常の相対微分の生成点との比較と、同じ有限正規化での階数安定への接続は供給済み。
通常有限正規化に沿う階数安定と微分基底の計算を合成した次元h+|f|への接続も実装済み。
通常の絶対微分の有限生成性を仮定して有限加群の完備化の完全性を使うだけでは、
Gabberの適用範囲を覆わない。
平坦性を必要以上に最終仮定へ追加しない。

M3：Ω_{L/K}=0と有限体拡大L/Kの分離性を接続し、有限整域拡大の分数体局所化へ移す。
通常のΩの局所化と完備微分の生成的評価の比較を区別する。
単に `rank=0` と書かず、有限次元性の供給と `Subsingleton`／零加群への移送まで証明する。
`FractionDifferential.lean` はMathlibの形式的不分岐性の判定を再利用し、
有限体拡大で通常Ωの消滅と分離性、さらに有限性を伴う次元0との同値を供給する。
同じ分数体作用に対するL⊗_D Ω_{D/A}≃Ω_{L/K}と、普遍微分との両立も実装済み。
`isSeparable_fractionRingMap_iff_finrank_tensorDifferential_eq_zero` は、
有限単射Fに由来する環・分数体の係数作用を明示して判定を適用する。
`CompletedFractionDifferential.lean` はDがNoether局所環、I⊆m_D、I進完備で
D/Aがessentially finite typeなら、通常の相対Ωの完備性を使って
L⊗_D 完備Ω_{D/A}≃Ω_{L/K}を供給する。有限整域拡大には次元0による分離性判定も適用する。
これは有限な相対微分の比較である。κ_e上の完備微分から同じp乗評価の通常相対微分へは、
上記の核の消滅と二つの完備化の比較を経由して接続済み。


## 5. Gabber固有の接続

### F：有限p-basis方向と体の微分の階数

係数写像κ、p-basisの有限部分eについてκ_e=κ^p(β_i : i∉e)を構成する。
[κ:κ_e]の有限性、逆向きの有向性、全eの交わりがκ^pになることは
`PBasisCofiniteField.lean` で実装済み。p-basisの全体の添字集合は有限と仮定しない。
有限性は整な有限族による添加から証明した。
κ_e上の相対単項式基底と正確な次数p^|e|は `PBasisCofiniteBasis.lean` で実装済み。
係数基底の展開と元のp-basisの独立性から、相対独立性を実際に確認する。
τがパラメータならR_κ=κ[[τ]]、R_{κ,e}=κ_e[[τ^p]]を、実際の評価の像として扱う。
後者の有限単射は `IsPBasis.exists_injective_finite_cofinite_powerSeries_map` で実装済み。
係数の像とX_i↦τ_i^pを保持し、変数イデアルの像は
`map_powerSeries_variables_eq_span` で(τ_i^p)へ同定できる。
κ_eから剰余体への全射性は要求しない。
形式的な冪級数環の間では、`CofinitePowerSeriesExpansion.lean` が
κ_e[[X]]→κ[[T]]、X_i↦T_i^pの有限単射と、β^a T^rによる生成性を供給する。
`PowerSeriesCoefficientBasis.lean` の一意な係数基底分解と、既存の指数剰余分解を組み合わせた。
`PowerSeriesExpansionBasis.lean` は両方を組み合わせた単項式族の独立性と基底を供給する。
`IsPBasis.finrank_cofinitePowerSeries` はこの係数作用について自由加群の階数p^(h+|e|)を計算する。
`CofiniteFractionField.lean` は同じ冪級数写像を分数体へ延長し、同じ単項式の像から基底と拡大次数を供給する。
`CofiniteNormalizationFraction.lean` は指定した有限正規化FをFrac(D)へ延長し、
同じ合成評価F∘(X_i↦T_i^p)の分数体像として部分体族を構成する。
反単調性・有向性・各部分体上のFrac(D)の有限性を確認し、
その交わりはFで移したK₀^pの像へ同定する。Frac(D)^pとの一致は主張しない。
`exists_equalCharacteristic_finite_fraction_normalization` は通常有限正規化の
係数体・パラメータ・剰余体への全射性を保ち、その同じFの有限な分数体延長を供給する。
共通分数体K₀=Frac(κ[[T]])内では、`CofiniteFractionSubfield.lean` が各延長写像の像F_eを
実際の部分体として構成し、反単調性・下向きの有向性・有限性と次数p^(h+|e|)を確認する。
K₀^p⊆F_eも証明済み。有限変数では `CofiniteFractionIntersection.lean` が⋂_e F_e=K₀^pを供給する。
逆包含は分母をp乗へ変え、基底の飽和性で分子を冪級数の像へ戻してから係数の交わりを使う。

体の階数安定補題：K/K_αが有限な、下向き有向な部分体族で交わりがK^pなら、
有限拡大L/Kに対して十分小さい共有限K′⊆K_αで
`finrank_L Ω_{L/K′} = finrank_K Ω_{K/K′}`。
各微分空間の有限性を先に供給する。
`SeparableDifferentialRank.lean` は分離的な拡大での自然な係数拡大同型、
微分空間の有限性の移送、次元の保存を供給する。ここでは拡大L/Kの有限性は要求しない。
`MonogenicDifferentialRank.lean` は、最小多項式の微分が零の単生成拡大について、
生成元の微分からなる実際の一元基底と、相対微分の次元1を供給する。
p乗根関係x^p=bの微分は推移列の核に入り、db≠0なら係数拡大後も非零である。
有限なK/Rについて、通常微分の有限性を確認して推移列の次元式を適用し、
finrank_L Ω_{L/R}≤finrank_K Ω_{K/R}を証明済み。
`PrimeRootDerivationExtension.lean` はdbを消す加群値導分を、添加元xを0に送る形で実際に延長する。
`PrimeRootDifferentialKernel.lean` はこれを関係式の微分で割った加群へ適用し、
ker(mapBaseChange)=L(1⊗db)を証明する。Rは一般の可換環でよく、有限性は不要。
共有限な体Rとdb≠0についてはfinrank_L Ω_{L/R}=finrank_K Ω_{K/R}も証明済み。
`PBasisDifferentialConstants.lean` はD_{K/K^p}(b)=0↔b∈K^pを、
bを含むp-basisとその偏導分から証明する。b∉K^pを検出する共有限な中間体も実際に選べる。
ただし、この新しく選ぶ体が指定済みの部分体族に属すとは限らない。
`IsPBasis.exists_not_mem_cofiniteFractionSubfield` は実際の分数体族の交わりから、
b∉K₀^pならb∉F_eとなる指標eを供給する。ここでは相対微分の非零性までは主張しない。
`KaehlerBaseRestriction.lean` は、一度確認した微分の非零性を小さい底環へ移す。
`finrank_kaehlerDifferential_primeRoot_tower_eq_of_baseRestriction` が、
その非零性から、より小さい共有限な底体についても次数pの次元等号を供給する。
`FiniteExponentOneConstants.lean` は、有限な指数1の拡大についてD_{K/F}(b)=0↔b∈Fの像を証明する。
指定元を避ける中間体のうち[K:E]が最小のものを選び、K=E(b)と次数pを実際に確認して導分を作る。
`CofiniteFractionDifferential.lean` は各F_eの有限性とK₀^p⊆F_eを供給して相対零判定を適用し、
交わりから選んだ指標での微分の非零性と、後続指標への保存を確認する。
`SubfieldFamilyPrimeRootRank.lean` が、共有限な部分体族の有限性・p乗部分体の包含・交わりの条件から次数pの段階を供給する。
この一段の定理に有向性は要求しない。
`CofiniteFractionPrimeRootRank.lean` はその三条件を実際の族で確認し、次数pの拡大L/K₀に対して、あるeを選び、
F_e以下の任意の共有限な部分体Rでfinrank_L Ω_{L/R}=finrank_{K₀} Ω_{K₀/R}を供給する。
終域へのAlgebra・Module・SMulは、指定済みのK₀→Lと部分体の包含の合成から取る。
`SubfieldSpanIntersection.lean` は、下向き有向な部分体族と、その一つの体上で独立な共通の有限族について、
全ての線形包への所属と、部分体族の交わり上の線形包への所属を同値にする。
`SubfieldPrimeRootIntersection.lean` はこれを冪基底へ適用し、⋂_i E_i(a)=K^p(a)を証明する。
aが個々のE_iに既に属する場合も、p未満の冪による線形包の所属判定は同じAPIで扱う。
`PrimeRootPowerSubfield.lean` はL=K[x]、x^p=aからL^pをK^p(a)の像へ同定し、
⋂_i (E_iの像⊔L^p)=L^pへ接続する。非自明な添加ではa∉K^pをxの非所属から証明する。
`CofiniteExtendedFractionSubfield.lean` はG_e=F_eの像⊔L^pを定義する。
任意の有限拡大で共有限性と下向き有向性を確認し、次数pの添加後には交わりをL^pへ同定する。
その三条件を供給して `IsPBasis.exists_extendedFractionSubfield_primeRoot_rank_stable` が
次の次数pの拡大への共通定理の再適用を行う。
`SeparablePowerSubfieldIntersection.lean` は有限基底Bのp乗を使い、L^pをK^pの像上の線形包へ同定する。
生成性の計算には分離性は不要。分離性によるK上での独立性はMathlibの
`LinearIndependent.map_pow_expChar_pow_of_isSeparable` を使う。
`SubfieldScalarSpan.lean` は各E_iの像とL^pの合成を共通の生成族の線形包へ直し、
前回の交わりの補題へ接続する。各E_iの共有限性は、L/(E_iの像)の有限性と
添加対象の代数性を供給するために使う。
実際の分離的有限拡大後の族の交わりと、次の次数pの階数安定への再適用も供給済み。
`PowerSubfieldMap.lean` はp乗部分体の写像による包含と、族の構成の塔に沿う合成を供給する。
`pBasisExtendedFractionSubfield_tower` は、二段階で構成した実際の族を合成した拡大での族へ同定する。
`PurelyInseparablePrimeStep.lean` は、底体の外の元について底体へ入る最小のFrobenius冪を選び、
非自明なp乗根と、添加後の残りの有限拡大の厳密な次数減少を供給する。
`SubfieldFamilyTower.lean` は共有限性・有向性と、次の分離的／次数pの段階での交わりを合成した拡大へ接続する。
`FiniteExtensionPowerSubfieldIntersection.lean` は純非分離な場合に拡大次数の強い帰納を使い、
一般の場合にはMathlibの分離閉包とその上の純非分離性を使って交わりをL^pへ同定する。
始域・終域の宇宙の一致は仮定せず、始域を終域内の底中間体へ移して帰納する。
`IsPBasis.iInf_extendedFractionSubfield_of_finite` が実際の族へ適用し、
`IsPBasis.exists_extendedFractionSubfield_primeRoot_rank_stable_of_finite` が任意の有限拡大の後の次数pの段階へ再適用する。
`FiniteExtensionDifferentialRank.lean` は通常微分の階数安定化の一般有限拡大の帰納も供給する。
底体RとR→K・R→Lの作用を固定し、R→Kの像が選んだE_iへ入る条件で各中間体の等号を合成する。
`exists_subfieldFamily_primeRoot_rank_stable_of_range` は、底体を部分体そのものとして表すことを要求しない次数pのAPI。
既存の部分体版はこのAPIへの適用へ整理した。
各中間体への作用は同じ代数写像の合成で取り、Module・SMul・二つのスカラー塔を明示する。
R上の各体の有限性から通常微分の有限性を供給するため、無限次元のfinrankが0になる規約には依存しない。
`CofiniteFractionDifferentialRank.lean` は実際の族の四条件を確認して一般定理を適用する。
`IsPBasis.exists_cofiniteFractionSubfield_rank_stable` は選んだF_e以下の任意の共有限な部分体での等号、
`IsPBasis.exists_cofiniteFractionSubfield_rank_stable_of_superset` はe⊆fとなる全てのF_fでの等号を供給する。
通常の体の階数安定化と、κ_e上の完備微分から同じp乗評価の分数体の通常微分への比較は完了した。
`IsPBasis.exists_cofiniteFractionField_rank_stable` はQ_f=Frac(κ_f[[X]])の像が実際のF_fであることを確認して適用する。
`CofiniteNormalizationDifferentialRank.lean` は同じ有限単射Fを延長したK₀→Lと、Q_f→K₀→Lの合成で作用を揃える。
`IsPBasis.exists_cofiniteNormalization_completed_rank_stable` が、十分大きいfで
L⊗_D 完備Ω_{D/κ_f}とΩ_{K₀/Q_f}の次元等号を供給する。
`CofiniteFractionDifferentialBasis.lean` は既存の相対単項式基底をσ⊕f上のp指数で添字付け直す。
`RelativePBasisDifferentials.lean` の一般定理で、T_iと残したb_jの微分を基底にし、
`IsPBasis.finrank_cofiniteFractionDifferential` が次元h+|f|を計算する。
`CofiniteNormalizationDifferentialDimension.lean` が完備微分へ次元式を移す。
`IsPBasis.exists_completed_finrank_of_parameters` は係数写像とh個の準素パラメータから
通常有限正規化を構成して適用するため、有限単射Fを別途入力する必要はない。

階数安定化の証明は分離閉包までの分離的段階と、その上の純非分離な拡大次数の強い帰納へ分ける。
最終定理へ有限p-rankの仮定を持ち込まない。

R_{κ,e}の有限p単項式による分解と分数体の部分体族の性質、Mの比較を使い、
V_f=L⊗_D 完備Ω_{D/κ_f}の有限性と、十分大きいfでの次元 `h+|f|` を証明済み。
有限性は既存の `IsPBasis.moduleFinite_completedKaehler_cofiniteField` とテンソルの有限性を使う。
普通の有限正規化（分離性なし）は既存の共通評価・有限性・単射性から別に供給する。
ここでCohen–Gabberの結論を先に使わない。

### K：係数体の変更と訂正版の接続

L1・L2をV_eとH=m_Dへ適用し、β′_i=β_i+m_i（i∈e）の微分を独立にする。
e以外の持ち上げを保ち、P2から **新しい** 係数写像κ′を構成する。
κ′_e=κ′^p(β_i : i∉e)も新たに定義する。

旧κ_eと新κ′_eを同じ部分体・同じ `Algebra` インスタンスとして扱わない。
訂正版§2.1.11に従い、絶対微分をe以外のdβ_iが生成する部分加群で割る表示を使って、
それぞれの相対微分、続いて完備微分を自然に同定する。
κ′の残るe個の方向を消す写像の像を独立なdβ′_iで計算して、
V′=L⊗_D 完備Ω_{D/κ′}の次元hを導く。
新しい係数体の存在・この比較・次元減少を別の証明に分ける。

実装状況：`PBasisCoefficientPerturbation.lean` は核内の有限摂動μを指定して、
補集合のp-basis元の像を保つ新しい切断を構成する。独立性を結論と同じ形で入力へ要求しない。
`KaehlerRestrictionKernel.lean` はMathlibの推移列から通常の係数制限の核を定数の微分の線形包へ同定する。
`CofiniteCoefficientRestriction.lean` は核をfの外のdβ_iの線形包へ直し、
補集合で係数写像が一致する場合に共通商を経由した通常・完備微分の自然な比較を供給する。
この比較はSのNoether性・局所性・通常微分の有限性を要求しない。
`cofiniteCoefficientDifferential` は選んだ係数写像によるκ_f作用を型へ保持し、
S上の加群作用も同じ写像から供給する。旧・新のκ_fの像の一致は主張しない。
同じS上の係数拡大後の有限性・次元の移送も供給する。
`IsPBasis.exists_completed_finrank_of_parameters_coefficientChange` は、
前節の次元式をfの外の像を保つ新しい係数写像へ移し、次元h+|f|を供給する。
次はL1による独立な摂動μの実際の選択と、κ′の残したf方向を消す次元減少。

### Y：微分基底をパラメータにする

L2と有限次元性から、df_iがV′の基底となるf:Fin h→m_Dを選ぶ。
既存パラメータτから `y_i=τ_i^p*(1+f_i)` を作る。
1+f_iの単元性から生成イデアルの根基を保存し、パラメータ条件を確認する。
導分の計算で `dy_i=τ_i^p*df_i` を証明する。
整域とパラメータ条件からτ_i≠0を確認し、分数体上の可逆性によりdy_iも基底となる。
座標τ_iが非零であることを暗黙にしない。

### N：同じ評価の有限性と分離性

A=k[[X₁,…,X_h]]を選び、κ′とyでF:A→Dを構成する。
既存の有限閉ファイバー・adic有限生成判定・次元一致による単射性を適用する。
M2で相対微分の生成的消滅を、M3で分数体拡大の分離性を得る。
`FractionRing.liftAlgebra`等で、Fに由来する作用・`IsScalarTower`を供給する。
分離性だけ別の分数体作用に対して証明しない。
全性質が揃ってから既存のInputs入口を置換し、§2・主定理の公理監査で引用2の解消を判定する。

## 6. 実装順・受入条件・再利用先

```text
G0 原典訂正・通常/連続微分の契約・Mathlib型照合
 ├─ G1 L1/L2 ──────────────────────┐
 ├─ G2 P1/P2 + 通常有限正規化 ── F ─┼─ K ─ Y ─ N ─ Inputs
 └─ G3 M1/M2/M3 ──────────────── F ─┘
```

| 段階 | 最初に完了させる成果物 | 受入条件 | 再利用先 |
| --- | --- | --- | --- |
| G0 | 原典の補題台帳、モデルの位相・普遍性・作用の型を固定 | 訂正版と旧版を区別。候補宣言を最小importで型照合。未確認接続を列挙 | 全ての後続 |
| G1 | L1とL2の独立した一般定理 | 有限体でもL1が成立。L2にNoether性・位相を追加しない | 生成的微分基底の選択、係数体変更 |
| G2a | p単項式の基底と有限部分の中間体 | 無限p-basis、e=∅、完全体の場合を扱う | 正標数体・不分離拡大 |
| G2b | 指定持ち上げの係数体と通常有限正規化 | 係数体を仮定する版と存在版を区別。剰余体の両立を証明 | 任意剰余体のCohen構造、将来の局所代数 |
| G3a | 完備微分の普遍性・冪級数の微分基底 | 通常のΩを無根拠に有限としない。n=0、1を確認 | 連続導分、形式的滑らかさ |
| G3b | 有限代数の相対微分比較と完全列、分数体への接続 | 有限性・閉性・完備化と作用の同定を供給 | 分岐、エタール性、既存GenericEtale |
| G4 | Fの階数安定とh+|e| | 微分の有限次元性、部分体族の交わりを実際に証明 | p-rank・有限拡大の微分 |
| G5 | Kの新係数体と階数h | 旧κ_e≠新κ′_eを許す自然比較。独立性から次元を計算 | 係数体変更と連続微分 |
| G6 | YとN、既存入口の置換 | 同じFで全性質。最終仮定を強めない。引用2がsorriesから外れる | 本体の等標数構成 |

実装の最初の単位は **G0の契約・型照合を確定し、G1の二つの一般補題を証明すること**。
続いてG2a、G3a、G2b/G3b、G4、G5、G6へ進む。
これは依存上の区分であり、別チャットやサブエージェントを新たに起動する指示ではない。
期間・行数による見積りはG0/G3aの検証後に更新する。現段階では完了日を置かない。

## 7. 所有・配置・検証

可換環論側（この作業）がp-basis、係数体、連続微分、階数計算、引用2の接続を担当する。
一般線形代数はリングや論文に依存しない場所へ配置する。
新設候補は `FieldTheory/PBasis`、`CommutativeAlgebra/CoefficientField`、
`CommutativeAlgebra/ContinuousDifferentials`、`CommutativeAlgebra/CohenGabber`。
ファイルを作る前に既存配置とMathlibとの重複を確認する。
共通微分層は `Paper`・`Inputs`・`CLMST`・具体的な根の塔をimportしない。

CLMST側が所有する一般のテンソル比較・完備化平坦性を利用する。
変更が必要なら統合計画へ要求する型・仮定を記録し、同じ一般証明を別ファイルに作らない。
今回、CLMST・K理論・他の引用の作業範囲は変更しない。
root import・監査・計画一覧は共有ファイルなので追加箇所だけ編集・コミットする。

各共通補題は対象ビルドと `assert_no_sorry`、適用は実際の型・写像・作用で監査する。
境界はh=0（Dが体、空変数）、h=1、完全剰余体（e=∅）、無限p-basis、有限体、
純非分離な通常正規化を確認する。
`k[[t^p]]⊂k[[t]]`のような有限単射を、分離的正規化と取り違えない。
新しいsorry・axiom・native_decideや、未証明結論をまとめた入力束を追加しない。
引用2の型を保持した置換後に `lake build`・主定理の `#print sorries`・文書検査を行う。

計画改訂時点では新しいLean実装は行っていなかった。G1の実装を開始した現在も、
引用2の証明状態・全体の引用件数は変わらない。

検証記録：現在の作業ツリーの全体ビルド4019ジョブ、可換環論278宣言の公理監査、
主定理の引用依存監査が成功。文書検査は14個のMarkdownと295個の解説参照で失敗0。
原典の訂正と対象加群の位相条件は確認済みだが、新しい微分APIの型照合・証明はG0以降の作業。

### G1の実装（2026-10-13）

`LinearAlgebra/IndependentPerturbation.lean`に
`exists_perturbation_notMem_submodule`と `exists_linearIndependent_perturbation`を実装。
生成集合と零による摂動を真部分空間の外に選び、列の長さに関する帰納法でL1を証明した。
体の無限性を使わず、`Fin 0`も同じ型で扱う。

`CommutativeAlgebra/DerivationIdealSpan.lean`に
`span_derivation_ideal_eq_span_range`、`span_derivation_ideal_eq_top`を実装。
L2を強め、任意の非零イデアルの微分が全微分と同じ分数体上の部分空間を生成すると証明した。
導分の係数作用と分数体作用の `IsScalarTower`を明示し、局所性・Noether性・位相は要求しない。
組合せの `exists_linearIndependent_derivation_perturbation`は、イデアル内の元そのものを選択し、
指定ベクトルにその微分を加えた列の独立性を供給する。

G1は完了。次の段階はG2aのp単項式基底とG3aの連続微分の契約・普遍性。
完備微分の生成性・有限次元性は未証明であり、上記の適用時には別途供給する。

検証：対象ビルド1706ジョブと全体ビルド4026ジョブが成功。
可換環論監査283宣言（今回追加5宣言）が成功し、追加分の公理は
`propext`・`Classical.choice`・`Quot.sound`のみ。新しい未証明入力はない。

### G2aの基礎API（2026-10-13）

`FieldTheory/PMonomial.lean`に有限台・各指数p未満の `PExponent` と `pMonomial`を実装。
無限添字を許し、埋め込みに沿う零延長と単項式の一致から任意の部分族の独立性を証明した。
有限添字の場合のみ関数 `ι → Fin p`との同値を用い、指数の個数と独立な単項式が張る
**部分空間**の次元を `p ^ Fintype.card ι`と計算する。
この部分空間を、未証明のまま中間体や部分代数と同一視しない。

`FieldTheory/PBasis.lean`でFrobenius像の部分体 `pPowerSubfield`と `IsPBasis`を定義。
条件は単項式の独立性と生成性であり、p-basisの数学的な定義を表す。
そこから実際の `Module.Basis`と、係数のp乗根を持つ一意な有限台展開 `expansionEquiv`を構成し、
復元式 `expansionEquiv_symm_apply`・`sum_expansionEquiv`を証明した。
p-basisが代数としても生成することと、導分がp-basis上の値で決まることも証明。
空のp-basisはp乗部分体が全体であることと同値で、完全体の場合へ接続した。

この基礎APIの実装時点では、p-basisの存在・独立族の拡張、単項式空間の積と逆元による閉性、
中間体との同定、微分による基底の特徴付けが残っていた。閉性と中間体の同定は次の記録で解消した。
G2bの指定持ち上げの係数体とG3aの連続微分はまだ未実装。
引用2の型・証明状態と、外部引用9件・保留K理論2件の境界は変わらない。

検証：対象ビルド2003ジョブ、全体ビルド4028ジョブ、公理監査313宣言が成功。
今回追加30宣言の公理は高々 `propext`・`Classical.choice`・`Quot.sound`。
`assert_no_sorry`で未証明入力を経由しないことを確認した。

### G2aの単項式空間と中間体（2026-10-13）

`FieldTheory/PMonomialSpan.lean`に指数の除法による単項式の分解を実装。
積の繰り上がりをp乗部分体の係数へ移して、`pMonomialSpan`の積による閉性を証明した。
逆元の閉性は `x⁻¹ = (x^p)⁻¹ * x^(p-1)`から直接証明する。
これにより有限次元性・独立性・添字の有限性を仮定せず、実際の部分代数と
`pMonomialIntermediateField`を構成した。

`pMonomialIntermediateField_eq_adjoin`で、単項式空間が族を添加した中間体と一致すると証明。
`IsPBasis.finrank_adjoin_comp`はp-basisの任意の有限部分の中間体の次数を `p ^ |I|`と計算する。
`finite_pMonomialIntermediateField`は有限族が生成する有限拡大を、独立性なしで供給する。

G2aの残りはp-basisの存在・独立族の拡張と、微分による基底の特徴付け。
G2bの係数体の指定持ち上げ、G3aの連続微分と引用2の最終接続は未実装。

検証：対象ビルド2029ジョブ、全体ビルド4037ジョブ、公理監査327宣言が成功。
今回追加14宣言は `assert_no_sorry`を通過し、公理は高々
`propext`・`Classical.choice`・`Quot.sound`のみ。

### G2aの一段の添加（2026-10-13）

`FieldTheory/PAdjoin.lean`に、体拡大で `x^p`が基礎体に属し `x`自体が属さない場合の
最小多項式 `X^p - C a`、冪の独立性、単純添加の次数pを実装。
Mathlibの `X_pow_sub_C_irreducible_of_prime`・`linearIndependent_pow`・
`IntermediateField.adjoin.powerBasis`を再利用した。
整性だけの補題 `isIntegral_of_prime_pow_eq`には標数の仮定を要求しない。

`linearIndependent_pMonomial_optionElim`は、単項式が独立な族 `b`と、
その生成中間体の外の元xから、添加した族 `Option.elim' x b`の単項式の独立性を供給する。
元の族は無限でもよい。`PExponent.splitOption`で指数を分け、
Mathlibの `linearIndependent_smul`で既存の単項式と新しい冪を組み合わせた。
結論の独立性を追加仮定として渡していない。

独立族の一段の拡張は実装済み。p-basisの存在・任意の独立族の拡張には、
集合上の鎖の合併の独立性とZornの補題、最大独立族の生成性をまだ証明する必要がある。
微分の基底の特徴付け・指定持ち上げの係数体・連続微分・引用2の最終接続も残る。

検証：対象ビルド2030ジョブ、全体ビルド4038ジョブ、公理監査339宣言が成功。
今回追加12宣言は `assert_no_sorry`を通過し、公理は高々
`propext`・`Classical.choice`・`Quot.sound`のみ。引用2の証明状態は変わらない。

### G2aのp-basis存在・独立集合の拡張（2026-10-13）

`FieldTheory/PIndependentSet.lean`で、元の体を共通添字とし、台が集合sに含まれる
p指数上の独立性 `IsPIndependentSet s`を定義した。
`isPIndependentSet_iff_linearIndependent`で従来の集合sを添字とする単項式族の独立性と
同値であることを、指数の制限・零延長を通して証明した。

有限個の単項式の台の合併が有限であることから、
`isPIndependentSet_iff_finite`で独立性が有限部分集合で検査できると証明。
Mathlibの `Order.IsOfFiniteCharacter.exists_maximal`を適用した。
この定理の実証明が、鎖内の有限集合を一つの段階に含めて鎖の合併を処理し、Zornの補題を使う。
同じ鎖・選択原理を独自に再実装していない。

最大独立集合の生成性は、生成中間体の外の元を添加する
`IsPIndependentSet.insert`と最大性の矛盾から証明した。
`exists_pBasis_superset`は任意のp独立集合を包含する実際のp-basisを供給し、
`exists_pBasis`は空集合から開始する。添字の有限性・有限p-rank・完全体性は要求しない。

G2aの残りは微分による基底の特徴付け。G2bの指定持ち上げの係数体と
G3aの連続微分は未実装で、引用2の証明状態・引用件数は変わらない。

検証：対象ビルド2032ジョブ、全体ビルド4043ジョブ、公理監査352宣言が成功。
今回追加13宣言は `assert_no_sorry`を通過し、公理は高々
`propext`・`Classical.choice`・`Quot.sound`のみ。

### G2aの通常微分の生成性（2026-10-14）

`CommutativeAlgebra/DerivationSpan.lean`に、代数の生成集合sが全体を生成するなら、
導分δの全ての値が張る部分加群がδ(s)の張る部分加群と一致する一般定理を実装。
生成集合の有限性・環の局所性・Noether性は要求しない。
Kähler微分の普遍導分にも適用し、Mathlibの全微分の生成性へ接続した。
標数pの代数への導分がp乗を消す補題も、一般の加群を対象として証明した。

`FieldTheory/PBasisDifferentials.lean`ではp-basisの実際の代数生成性を適用し、
通常の `KaehlerDifferential (pPowerSubfield K p) K`がp-basisの微分で生成されると証明。
`IsPBasis.finite_kaehlerDifferential`は **有限p-basisの場合だけ** 有限生成性を供給する。
無限p-basisや冪級数環の通常微分を無条件に有限と扱わない。

`derivationOverPowers`は、任意の基礎環R上の導分がp乗部分体を消すことから、
同じ写像をp乗部分体上の導分として構成する。p乗部分体の作用は、
Kの作用を制限した標準作用に固定し、異なる作用を定義的に同じと扱わない。
これにより任意のR上の通常微分 `KaehlerDifferential R K`にも生成性を適用できる。

残りは偏導分の実構成・微分の独立性・基底の特徴付け。
基礎環Rが任意の場合は生成性だけであり、独立性を主張しない。
G2bの係数体の指定持ち上げ・G3aの連続微分・引用2の最終接続も未実装。

検証：対象ビルド2042ジョブ、公理監査363宣言が成功。追加11宣言は
`assert_no_sorry`を通過し、公理は高々 `propext`・`Classical.choice`・`Quot.sound`のみ。
全体ビルドは初回、並行更新中のCLMSTの `PerfectoidFrobeniusComparison`で失敗したが、
同ファイルをこちらで変更せず再実行し、4050ジョブで成功した。

### G2aの一段の添加の導分（2026-10-14）

偏導分の構成は、一つのp-basis方向を残し、それ以外の方向の中間体上で
一段のp乗根添加として扱う経路で進める。多項式の微分・冪基底を再利用する。

`CommutativeAlgebra/DerivationDescent.lean`は、全射な代数写像の核を消す導分を
終域へ降ろし、元の導分との両立を証明する。対象は終域自身で、
始域の作用は代数写像による標準作用。Mathlibの `LinearMap.liftOfSurjective`を再利用した。
核を消す条件は最終適用で実際に確認する。

`FieldTheory/PowerBasisDerivation.lean`は、最小多項式の微分が零の場合、
評価の核に属する多項式の微分も評価後に零になることを最小多項式の倍数表示から証明。
冪基底が与える評価の全射性と合わせて `Polynomial.mkDerivation`を降下し、
`PowerBasis.generatorDerivation`を構成した。生成元の値1と評価・微分の両立を証明。
普遍微分の線形写像で値1を検出し、生成元のKähler微分が非零であることも証明した。

`FieldTheory/PAdjoinDerivation.lean`は前回の最小多項式 `X^p-C a`を使用する。
基礎体の標数pを代数写像の単射性から供給し、最小多項式の微分が零であることを証明。
`IntermediateField.adjoin.powerBasis`で実際の添加体上の冪基底を作り、
`exists_derivation_adjoin_primeRoot`で添加元を1に送る導分を供給した。
この一段の添加では、最小多項式の微分が零という条件を未証明入力として残していない。

残りはp-basisの一方向を除いた族の中間体、元の体が残した元の単純添加であること、
その元が既存中間体に属さないことの証明。これらを供給して各方向の偏導分を作り、
微分の独立性・基底を証明する。G2a全体・引用2はまだ未完了。

検証：対象ビルド2068ジョブ、全体ビルド4054ジョブ、公理監査373宣言が成功。
今回追加10宣言は `assert_no_sorry`を通過し、公理は高々
`propext`・`Classical.choice`・`Quot.sound`のみ。

### G2aの補中間体・偏導分・通常微分の基底（2026-10-14）

`FieldTheory/PBasisComplement.lean`で、一つの添字iを除いた族の生成中間体
`pBasisComplementField b i`を構成した。単項式基底の指数iの座標を用い、
残したb_iには1、補中間体の単項式には0という値を検出して、b_iが補中間体に属さないと証明。
残りのb_jを補中間体の係数に移し、b_iの添加が元の体全体を生成することも証明した。

`exists_derivation_primeRoot_of_adjoin_eq_top`はMathlibの `PowerBasis.ofAdjoinEqTop`を使い、
単純添加が全体である場合に導分を終域自身へ供給する。
`IsPBasis.exists_complementDerivation`はp乗の係数、補中間体の外にあること、生成性を全て供給し、
b_iを1、他のb_jを0に送る補中間体上の導分を構成した。

`FieldTheory/PBasisPartialDerivation.lean`ではMathlibの `Derivation.restrictScalars`で
p乗部分体上の `partialDerivation`を構成した。各方向の値を実証明し、
普遍微分の線形写像で有限線形関係の係数を検出して、微分の独立性を証明。
前回の生成性と合わせて `IsPBasis.kaehlerBasis`という実際の `Module.Basis`を構成した。
添字が無限でもよく、有限の場合の `finrank_kaehlerDifferential`は次元を添字数と計算する。
空添字も同じ型に含まれる。

G2aの存在・独立集合の拡張・有限部分の中間体・p-basisから微分基底を作る順方向は完了。
任意の族について微分基底からp-basisへ戻す逆方向の特徴付けは未実装。
次の指定持ち上げの係数体・連続微分では、構成済みのp-basisとその微分基底を使う。
通常微分の結果を完備微分へ読み替えない。引用2の証明状態は変わらない。

検証：対象ビルド2073ジョブ、公理監査386宣言が成功。今回追加13宣言は
`assert_no_sorry`を通過し、公理は高々 `propext`・`Classical.choice`・`Quot.sound`のみ。
全体ビルドは初回、CLMSTの `PerfectoidIdealRoots.olean`欠如で停止した。
再実行では、並行更新中の `CLMST/PerfectoidIdealRoots.lean:141`の
`compatibleRoots_pow`未定義と関連する未解決ゴールで停止。
同ファイルはこの作業で変更していない。全体入口に依存する文書参照検査も未完了。
対象の微分APIの検証成功と、作業ツリー全体の検証未完了を区別する。

### G2bの指定持ち上げの一意性（2026-10-14）

`FieldTheory/PBasisRingHomExt.lean`で、p-basisの像と全てのp乗で一致する環写像が
一致することを有限台展開から証明。さらに、同じp-basisの像と一つのFrobenius冪の像での
一致から写像全体の一致を、冪指数に関する帰納法で証明した。
終域の完全性・標数・局所性はこの環写像の一致定理に要求しない。

`CommutativeAlgebra/PBasisNilpotentLifting.lean`では、同じ剰余写像を持つ二つの写像の差を
核へ入れ、Frobenius冪で消して一意性を供給した。
`ringHom_lift_unique_of_nilpotent_kernel`は指定p-basisの像による冪零核上の一意性。
`ringHom_lift_unique_of_hausdorff_kernel`は核イデアルについて分離な終域での一意性。
後者に完備性・全射性・Noether性・局所性を要求しない。
冪商自身の標数は仮定せず、元の環で差のFrobenius冪を評価して商へ移すため、零商も扱える。

`CommutativeAlgebra/NilpotentFrobenius.lean`に、冪零イデアルの全ての元を
一つのpの冪指数で消す評価を集約。評価自体には標数を要求しない。
既存 `PerfectNilpotentLifting.lean`の `exists_unique_ringHom_lift_of_nilpotent_kernel`の
証明もこの評価へ整理し、完全体版と任意p-basis版の重複を除いた。

G2bの存在は未証明。一意性だけから持ち上げの存在を推論しない。
次は高いFrobenius冪の係数に関するp-basis展開と、指定像を持つ冪商への環写像の実構成。
その後、一意性で冪商の写像を両立させて完備環への逆極限を取る。
引用2の証明状態は変わらない。

検証：対象ビルド2031ジョブ、全体ビルド4062ジョブ、公理監査392宣言が成功。
追加6宣言と既存の完全体版の整理後の証明は `assert_no_sorry`を通過し、
公理は高々 `propext`・`Classical.choice`・`Quot.sound`のみ。
先のCLMSTによる全体ビルド未完了は、現在の作業ツリーでは解消した。

### G2bの高いFrobenius係数部分体（2026-10-14）

`FieldTheory/FrobeniusPowerSubfield.lean`にp^n乗の像部分体と体全体からその像への
同型を定義し、n=0の全体・n=1の既存p乗部分体との一致を証明した。
完全体性・有限p-rank・添字の有限性は要求しない。

`CommutativeAlgebra/FrobeniusKernelLift.lean`で、核を一つのFrobenius冪が消す全射に沿って、
そのFrobenius冪を終域から元の環への環写像として降下した。
`PerfectNilpotentLifting.lean`の完全体版も、この共通APIへ整理した。
共通の降下モジュールはp-basis・係数部分体をimportせず、
`FrobeniusCoefficientLift.lean`が降下と部分体の同型を組み合わせる。

`exists_frobeniusCoefficientLift_of_nilpotent_kernel`は、冪零核の場合に実際の指数nと
係数写像 `k^{p^n} → A`を構成し、剰余写像との両立を証明。
任意の持ち上げβについて、βのp^n乗が係数写像の値と一致することも供給する。
これは **高い冪の係数部分体上の写像** であり、k全体の切断を証明したものではない。

`FieldTheory/PBasisFrobeniusGeneration.lean`では、p-basisの有限台展開をFrobenius冪で移して
係数を次の部分体へ送る帰納法で、任意のnについて `k^{p^n}`とp-basisの元が
代数としてk全体を生成することを証明した。
この生成性から、高い冪の単項式の独立性・一意な展開を推論しない。

この段階の残りは高い冪の単項式の基底、指定βの冪関係を使った乗法の確認、k全体の写像の実構成。
基底と一意な展開の進展は次の記録を参照。
次いで冪商間の両立と逆極限を取る。G2bの係数体全体の存在・引用2は未証明。

検証：対象ビルド2033ジョブ、全体ビルド4068ジョブ、公理監査406宣言が成功。
追加14宣言と完全体版の整理後の証明は `assert_no_sorry`を通過し、
公理は高々 `propext`・`Classical.choice`・`Quot.sound`のみ。

### G2bの高いFrobenius冪上の基底と一意な展開（2026-10-14）

`LinearAlgebra/BasisRingEquiv.lean`で、係数体と拡大体の両立する同型に沿う基底の
移送をMathlibの `Basis.map` と `Basis.mapCoeffs` から証明した。
`FieldTheory/PBasisTransport.lean`はp乗部分体の同型も明示し、p-basisの独立性・生成性を
体同型に沿って移す。標数・Frobeniusに固有の処理は、一般の基底移送から分離した。

`FieldTheory/FrobeniusLayerBasis.lean`では、隣接する部分体の包含、包含による係数作用、
`IsScalarTower`を構成する。Frobeniusの係数同型との可換性を確認し、元のp-basisから
`k^{p^n}/k^{p^(n+1)}`の実際の単項式基底を移送した。

`FieldTheory/FrobeniusTowerBasis.lean`では、各段階の基底を `Basis.smulTower` で帰納的に
合成し、`k/k^{p^n}`の基底を構成した。添字 `FrobeniusDigits p ι n` はn個の有限台p指数を
高い桁から並べたもの。単項式の値は高い桁のp単項式のp^n乗と、残りの桁の積である。
独立性・全体の生成性・任意の元の一意な有限台展開を証明済み。
添字集合の有限性・完全体性は不要で、n=0も空積1の基底として扱う。
有限p-basisの場合のみ、`finrank_frobeniusPowerSubfield` が拡大次数p^(n・card ι)を計算する。
生成性だけから独立性を仮定したものではない。

この段階の残りは、p進の桁と各指数がp^n未満の有限台指数との同一視、指定βの冪関係を使った
繰り上がりと乗法の確認、この展開を送るk全体の環写像の実構成。
その後に冪商間の両立と逆極限を取る。係数体全体の指定持ち上げ・引用2は未証明。

検証：対象ビルド2008ジョブ、全体ビルド4072ジョブ、公理監査429宣言が成功。
追加23宣言はすべて `assert_no_sorry` を通過し、公理は高々
`propext`・`Classical.choice`・`Quot.sound`のみ。

### G2bの有限台指数・乗法性と冪零核上の指定持ち上げ（2026-10-14）

`FieldTheory/PExponentRadix.lean`は商・余りによる有限台指数の同値を実装した。
`pMonomial_radixJoin`が単項式の値との両立を証明する。体・標数・添字の有限性は不要。
`FrobeniusMonomialBasis.lean`が桁の基底をこの同値で付け替え、各指数がp^n未満の
有限台指数を添字とする実際の基底 `frobeniusMonomialBasis` を構成した。n=0も扱う。

`CommutativeAlgebra/FrobeniusMonomialCarry.lean`では、係数写像cと指定βについて
β_i^(p^n)=c(b_i^(p^n))から、すべての有限台単項式の冪関係を導いた。
指数の和の商と余りを使い、積の繰り上がりをcの値に移す実際の公式を証明。
βの環への持ち上げや乗法性を結論の形で仮定していない。
この共通公式の持ち上げ先はCommRingだけで、標数の仮定も不要。

`PBasisFrobeniusLift.lean`の `exists_ringHom_of_frobeniusRelations` は、基底の展開を
βの単項式へ送る線形写像を作り、繰り上がり公式と双線形写像の基底上の外延性から
乗法性を証明した。係数写像の延長であることも確認。
`exists_ringHom_prescribed_of_frobeniusRelations` が指定βの像を供給する。
n=0では係数との一致を使い、n>0では指数1の単項式を使うので、Fin 1に1を入れない。

`PBasisNilpotentLiftExistence.lean`の `exists_ringHom_lift_of_nilpotent_kernel` は、
既存の高いFrobenius係数写像からβの冪関係を実際に導き、k全体の環切断を構成。
剰余写像との両立はp-basisと高い冪での環写像の外延性で証明した。
`existsUnique_ringHom_lift_of_nilpotent_kernel` は既存の一意性APIを再利用する。
仮定は同標数pの環A・体k、全射A→k、核の冪零性、p-basis、各β_iの剰余像の一致。
完全体性・有限p-rank・Noether性・局所性は不要。

この段階の残りは完備環の冪商へこの結果を適用する際の仮定確認、商間の両立、逆極限での
環写像の構成。冪零核上の存在を、完備環の係数体存在と同一視しない。
G3aの連続微分と引用2の最終接続も引き続き未証明。

検証：対象ビルド2048ジョブ、全体ビルド4080ジョブ、公理監査445宣言が成功。
追加16宣言はすべて `assert_no_sorry` を通過し、公理は高々
`propext`・`Classical.choice`・`Quot.sound`のみ。

### G2bの完備環への指定持ち上げと係数体（2026-10-14）

`CommutativeAlgebra/KernelPowerQuotient.lean`は、全射fの核Iの正の冪商から終域への写像を
構成し、全射性・核のイデアルとしての冪零性・隣接商間の両立を証明した。
源と終域が同じ標数pなら、正の冪商にも同じ標数が入る。
一般の商の標数を無条件で仮定せず、終域の標数から自然数の像が消える条件を確認する。
この共通モジュールはp-basis・係数体・完備性をimportしない。

`PBasisCompleteLifting.lean`の `existsUnique_ringHom_lift_of_complete_kernel` は、
各正の冪商に前段の冪零核上の切断を適用する。指定βの商での像を保ち、一意性で切断を
両立させる。Mathlibの `StrictMono.liftRingHom` で逆極限を取り、剰余写像との両立と
p-basisの像を証明した。全体の一意性は既存のHausdorff核上の一意性APIを使用。
零回目の冪商は零環になるため使わず、n+1の正の冪を使う。
仮定は同標数pの環A・体k、全射f:A→k、核についての `IsAdicComplete`、p-basisと指定β。
局所性・Noether性・整域性・核の有限生成性・有限p-rank・完全体性は不要。

`PBasisCoefficientField.lean`で完備局所環の剰余写像へ適用した。
`existsUnique_coefficientRingHom_of_residueEquiv` は指定剰余体同型Res(A)≃kと指定βを保つ。
`existsUnique_coefficientRingHom` は実際の剰余体を終域とする入口。
`exists_ringHom_section_of_complete_kernel` は構成済みのp-basis存在と全射からβを選択して
係数sectionを供給する。`exists_coefficientField_ringHom` は任意剰余体に対して係数写像の
存在・単射性・局所性をまとめる。剰余体の標数はMathlibの素数標数の判定から確認済み。
指定βを省いた係数写像には一意性を主張しない。

この段階でG2bの指定係数体部分P2は実装済み。残りは通常有限正規化への接続、G3aの連続微分、
階数計算と訂正版の係数体変更・分離的パラメータの選択。
係数体の存在だけで分数体拡大の分離性は得られず、引用2は引き続き未解消。

検証：対象ビルド2079ジョブ、全体ビルド4083ジョブ、公理監査456宣言が成功。
追加11宣言はすべて `assert_no_sorry` を通過し、公理は高々
`propext`・`Classical.choice`・`Quot.sound`のみ。
公開型を別途出力し、係数体存在にNoether性・整域性・完全体性・有限p-rankが
隠れて要求されていないことも確認した。

### G2bの通常有限正規化への接続（2026-10-14）

`CommutativeAlgebra/EqualCharacteristicNormalization.lean`で、係数体・パラメータ・冪級数評価を
接続した。`exists_finite_powerSeries_map_of_parameters` は指定した係数写像と極大イデアルを
根基とする有限列から、同じ係数・変数を送る実際の評価Fを構成する。
有限性は既存の `finite_quotient_of_common_residue_primary` と
`adicPowerSeriesEval_finite_of_span` を適用。係数写像を与えたこの段階では標数を仮定しない。

`exists_injective_finite_powerSeries_map_of_parameters` はdim D=hとh個のパラメータから、
既存の `ringHom_injective_of_finite_of_equal_dimension` によって同じFの単射性を証明。
終域Dの整域性は不要。h=0も空列・空変数の同じ構成で扱う。

`exists_equalCharacteristic_finite_normalization` は前段で証明した任意剰余体の係数写像を
実構成し、既存の準素イデアル内のパラメータ系存在を適用する。
自然数化した次元とhとの一致をhdimから確認し、実際のφ・z・Fを供給。
Fの単射性・有限性・剰余体への全射性に加え、F(C a)=φ(a)、F(X_i)=z_iを保持する。

`exists_cohen_normalization_equalCharacteristic` は同じFに対して標準基底
A=Res(D)[[X₁,…,X_h]]の整域性・正則局所性・完備性・極大イデアルの変数による生成を
供給する。冪級数環の構造には既存の一般APIを使用した。
仮定は同標数pの完備Noether局所環Dとdim D=h。終域の整域性・完全剰余体は要求しない。

この段階でG2bの係数体と通常有限正規化は実装済み。残りはG3aの連続微分、階数計算、
訂正版の係数体変更と分離的パラメータの選択。
**通常の有限正規化とCohen–Gabberの生成的分離性は区別する。**
引用2の公開型と証明は変更せず、未証明の分離性をこの結果から推論しない。

検証：対象ビルド2714ジョブ、全体ビルド4084ジョブ、公理監査460宣言が成功。
追加4宣言はすべて `assert_no_sorry` を通過し、公理は高々
`propext`・`Classical.choice`・`Quot.sound`のみ。

### G3a/M1の積位相での連続導分と有限自由な表現（2026-10-14）

`CommutativeAlgebra/ContinuousPowerSeriesDerivation.lean`は
`MvPowerSeries.WithPiTopology`を明示して、Mathlibの形式偏微分の連続性を係数公式から証明。
この部分は変数の有限性・標数の仮定を要求しない。
`continuous_powerSeries_derivation_ext` は多項式の稠密性を使い、T2な加群への連続導分を
変数の像で決定する。こちらも有限変数・完備性・連続なスカラー作用の仮定は不要。

有限変数の場合、`powerSeriesDerivation` が任意の指定像a_iから偏微分の有限和を構成する。
加群の連続な加法・スカラー作用からこの導分の連続性を確認し、
`existsUnique_continuous_powerSeriesDerivation` が指定像を持つ連続導分の存在と一意性を供給。
源は一般の位相的可換環R、終域はT2な位相的加群。完備性・Noether性・局所性・標数は不要。
`continuousPowerSeriesDerivations` は連続導分の部分加群であり、未証明の入力をまとめたものではない。
`continuousPowerSeriesDerivationEquiv` はその加群と変数の像σ→Mの実際の線形同型。

`PowerSeriesContinuousDifferential.lean`で、有限自由加群σ→S（S=R[[X]]）への偏微分の組を
導分として構成した。`powerSeriesContinuousDifferentialLiftEquiv` が連続導分を
Hom_S(S^σ,M)と線形同型にし、`_comp` が対応する線形写像で導分を復元することを確認。
その線形写像自体の連続性も有限和と連続なスカラー作用から証明した。
空変数の場合も同じ有限和・稠密性の証明が適用される。

この結果は **係数の積位相での連続導分の表現**。一般の係数位相を変数イデアル進位相と
同一視しない。この段階の次は有限変数・離散係数で両位相の一致を証明し、Gabberの実際のイデアル進
加群に対して連続な作用とT2性を確認する。
通常のKähler微分の完備化との同定、有限代数の右完全列と像の閉性は未実装。
これらを仮定せずに通常Ωを有限自由と主張しない。引用2は引き続き未解消。

検証：全体ビルド4096ジョブ、公理監査478宣言が成功。
追加18宣言はすべて `assert_no_sorry` を通過し、公理は高々
`propext`・`Classical.choice`・`Quot.sound`のみ。
文書検証は14 Markdown資料・295 exposition参照に対して不整合0件。

### G3a/M1の変数イデアル進位相と実際の加群への接続（2026-10-14）

`CommutativeAlgebra/PowerSeriesAdicTopology.lean`で有限変数・離散係数について、係数の積位相が
変数イデアルJのイデアル進位相であることを証明した。
`mem_powerSeries_variables_pow_iff` はJ^nへの所属と次数n未満の全係数の消滅を同定する。
Mathlibの多項式の完備化との同型、有限生成イデアルの完備化での評価の核、
多項式の変数イデアルの冪の係数判定を使う。ここは位相・Noether性・体・標数の仮定が不要。
既存 `PowerSeriesLocalStructure.lean` の `powerSeries_ker_constantCoeff` も、n=1の特殊化へ
整理した。完備化への変数イデアルの像と評価の核の計算を個別に重ねない。

`powerSeries_piTopology_isAdic_variables` は各冪の開性と零近傍への共終性を確認する。
次数n未満の有限個の係数が零となる条件は開。逆に積位相の有限個の係数条件は、
その有限集合の最大次数より高い冪で満たされる。
有限変数性は低次数の指数集合の有限性に、離散係数性は係数の零条件の開性に使用する。
空変数、冪指数0、零係数環にも追加の非零性の仮定を置かない。
`powerSeries_continuous_iff_variables_adic` はこの位相等式を連続性の同値として供給。

`AdicPowerSeriesDerivation.lean`で前段の積位相の一般定理へこの同値を実際に適用した。
`variables_adic_powerSeries_derivation_ext` が変数イデアル進位相での導分の一意性、
`existsUnique_variables_adic_powerSeriesDerivation` が指定像を持つ導分の存在と一意性を供給。
`existsUnique_adicModule_powerSeriesDerivation` は終域にもJ進加群位相を入れ、
連続な加法とスカラー作用をMathlibの `WithIdeal.topologicalSpaceModule` から確認した。
一般定理の連続な作用を結論の形で仮定しただけの適用ではない。
終域のT2性は明示した仮定であり、実際の分離加群への適用時に供給する。
Noether性・局所性・体・標数・加群の有限生成性はこれらの入口には不要。

この段階の残りは終域のT2性と代数的な `IsHausdorff` の接続、通常のKähler微分の完備化との同定、
有限代数の右完全列と像の閉性。引用2の分離的選択は引き続き未証明。

検証：対象ビルド2151ジョブ、整理後の局所構造ビルド2366ジョブ、全体ビルド4101ジョブが成功。
公理監査484宣言が成功。追加6宣言と整理した定数係数の核の定理は `assert_no_sorry` を通過し、
公理は高々 `propext`・`Classical.choice`・`Quot.sound`のみ。

### G3a/M1の分離加群と通常の導分・Kähler微分への接続（2026-10-14）

`CommutativeAlgebra/AdicModuleSeparation.lean`で、任意のイデアルI・加群Mについて
`IsHausdorff I M` と実際のI進加群位相のT2性との同値を証明した。
Mathlibの加群フィルター基底で、零近傍をI^n Mの族として確認する。
`hasBasis_nhds_zero_adicModule` がこの基底、`t2Space_adicModule_of_isHausdorff` がT2性を供給する。
環自身・有限加群・Noether環・完備加群には制限しない。

`DerivationIdealPowers.lean`はLeibniz則とイデアル積の帰納法から
`derivation_mem_pow_smul`：δ(I^(n+1))⊆I^n Mを証明。
位相・有限生成性・Noether性・局所性・標数は不要で、環R上の一般のSと導分S→Mを扱う。
`AdicDerivationContinuity.lean`がこの次数降下を上記の零近傍の基底へ移し、
任意の通常の導分のI進連続性を証明する。ここにも分離性・完備性は不要。

`AdicPowerSeriesDerivation.lean`に
`powerSeries_derivation_ext_of_isHausdorff` と `existsUnique_powerSeriesDerivation_of_isHausdorff` を追加。
変数イデアルJについて分離なMへの通常の導分が、指定した変数の像で一意に存在する。
連続性を外部から仮定せず、上の一般評価から実際に供給する。
係数環には証明内で離散位相を入れるので、公開型に係数の位相・終域の位相・T2性を追加しない。
有限変数、一般の可換係数環、両立する加群構造、J進分離性だけを要求する。
終域の完備性・有限生成性は不要。

`SeparatedPowerSeriesKaehler.lean`でMathlibの通常のKähler微分の普遍性へ接続した。
`powerSeries_kaehler_linearMap_ext_of_isHausdorff` がΩから分離加群への線形写像をdX_iの像で決定し、
`existsUnique_powerSeries_kaehler_linearMap_of_isHausdorff` が任意の指定像の線形写像を構成する。
通常Ωからの写像を、連続導分の新しい入力構造体に包んで仮定するものではない。
これは **分離した終域への写像の分類** であり、通常Ω自身の有限性は主張しない。

この段階の残りは通常Ωの分離商・完備化と有限自由加群の実際の同型、有限代数の右完全列と像の閉性。
Gabberの実際の微分加群での分離性・有限性の供給も、この一般入口への適用時に確認する。
引用2の分離的選択は引き続き未証明。

検証：対象ビルド2165ジョブ、全体ビルド4108ジョブ、公理監査493宣言が成功。
追加9宣言はすべて `assert_no_sorry` を通過し、公理は高々
`propext`・`Classical.choice`・`Quot.sound`のみ。

### G3a/M1の通常Ωの分離商・完備化と微分基底（2026-10-14）

`CommutativeAlgebra/PowerSeriesSeparatedDifferential.lean` の
`powerSeriesHausdorffificationEquiv` は、S=R[[X]]、変数イデアルJについて
Hausdorffification J Ω_{S/R} ≃ₗ[S] S^σを実構成する。
通常Ωから偏微分の組への写像 `powerSeriesKaehlerToFree` との両立も証明した。
逆写像は標準基底を分離商のdX_iへ送り、分離加群への微分写像の外延性で逆関係を確認する。

`PowerSeriesCompletedDifferential.lean` の `powerSeriesCompletedDifferentialEquiv` は
AdicCompletion J Ω_{S/R} ≃ₗ[S] S^σを構成し、元のΩの像で同じ偏微分写像と一致する。
`powerSeriesCompletedDifferentialBasis` のi番目は実際に完備化したdX_iである。
`moduleFree_powerSeriesCompletedDifferential` と `moduleFinite_powerSeriesCompletedDifferential`
が有限変数の場合の自由性・有限生成性を供給する。通常Ω自身の有限生成性は主張しない。
空変数・零係数環にも同じ証明が適用される。

共通API `AdicModuleProducts.lean` は完備加群の有限直積の完備性を、
Mathlibの完備化と有限直積の同型から供給する。Noether性・イデアルの有限生成性は不要。
`AdicCompletionExt.lean` の `adicCompletion_linearMap_ext_of_of` は、有限生成イデアルIの
完備化からI進分離加群への線形写像の一致を、元の加群の像での一致から証明する。
冪商の代表元で各I^nを法として近似し、終域の分離性を使う。
元の加群・終域の有限生成性やNoether性・終域の完備性は不要。
冪級数への適用では有限変数からJ.FGを実際に確認する。

この段階でG3a/M1の冪級数の完備微分基底は実装済み。
次は有限代数の相対微分の有限性、係数制限、右完全列、像の閉性と完備化後の余核（M2）。
続いて分数体での通常微分との比較（M3）、階数安定化と訂正版の係数体変更を接続する。
引用2は引き続き未解消で、外部引用9件・保留K理論2件の境界は変更していない。

検証：対象ビルド2169ジョブ、全体ビルド4112ジョブ、公理監査508宣言が成功。
追加15宣言はすべて `assert_no_sorry` を通過し、公理は高々
`propext`・`Classical.choice`・`Quot.sound`のみ。
文書検証は14 Markdown資料・295 exposition参照に対して不整合0件。

### G3b/M2の通常の相対微分との比較と像の閉性（2026-10-14）

`CommutativeAlgebra/AdicModuleMaps.lean` は、一般の加群の線形写像のイデアル進連続性、
分離した終域への写像の核の閉性、商の分離性からの部分加群の閉性を証明する。
Noether性・局所性・有限生成性・完備性はこの共通層には不要。
冪との積が線形写像で保存されることを、既存の零近傍の基底へ移す。

`CompletedRelativeDifferential.lean` は、essentially finite type S/Rについて
Mathlibの `KaehlerDifferential.finite` を使い、通常のΩ_{S/R}の有限性を供給する。
Noether局所環S、I≤m_S、I進完備なSでは、既存の有限加群の完備性の定理から
`isAdicComplete_relativeDifferential` と `relativeDifferentialCompletionEquiv` を構成する。
体・標数・整域・RのNoether性・局所性・完備性は不要。有限代数はこの範囲に含まれる。
同型は元の微分を完備化の標準写像で送り、逆写像との両立も確認した。

k→R→Sの両立する係数作用について `completedDifferentialRestriction` は
完備Ω_{S/k}→Ω_{S/R}を構成し、通常の係数制限との両立、d(s)の像、全射性を証明する。
絶対微分Ω_{S/k}の有限性は仮定しない。相対微分の完備性とMathlibの完備化による
全射保存を使う。完備化後の係数制限の核も、相対微分の分離性から閉である。

`isClosed_range_kaehlerMapBaseChange_adic` は通常の推移列
S⊗_R Ω_{R/k}→Ω_{S/k}→Ω_{S/R}→0の最初の写像の像の閉性を証明する。
Mathlibの `range_mapBaseChange` で像を核へ同定し、有限相対微分の分離性を使う。
この閉性にはSのI進完備性も不要。Noether局所環とI≤m_Sを、Krullの共通部分定理で使用する。

この段階の残りは **完備化後の核を最初の写像の像へ同定する証明**、係数制限・テンソルと完備化の比較、
有限代数側の完備微分の有限生成性、M3の分数体比較。
閉性を確認しただけで、完備化の完全性を得たとは扱わない。
Mathlibの `AdicCompletion.map_exact` は中項の有限生成性と最初の写像の単射性を要求するため、
一般の絶対微分にそのまま適用しない。引用2と引用境界は変更していない。

検証：対象ビルド2186ジョブ、全体ビルド4118ジョブ、公理監査521宣言が成功。
追加13宣言はすべて `assert_no_sorry` を通過し、公理は高々
`propext`・`Classical.choice`・`Quot.sound`のみ。
有限代数・極大イデアルでの適用例3件も別途コンパイルし、
通常の像の閉性が環の完備性を要求しないことを確認した。
文書検証は14 Markdown資料・295 exposition参照に対して不整合0件。

### G3b/M2の完備化した推移列の核と像の閉包（2026-10-14）

`CommutativeAlgebra/AdicCompletionKernelClosure.lean` で、有限生成イデアルIと
一般の全射g:M→Nについて `exists_ker_approximation_adicCompletion` を証明した。
完備化した写像の核の元xは、任意のnで元の核の元aによりI^nを法として近似できる。
冪商の代表元bを選び、g(b)∈I^n Nを確認する。全射性からI^n Mの元zにg(b)を持ち上げ、
a=b−zとすれば、同じ近似精度を保ったままg(a)=0となる。
この誤差の修正には加群の有限生成性・Noether性・環の完備性は不要。
Iの有限生成性は完備化の冪と冪商への評価の核の一致に使用する。

`closure_ker_image_eq_ker_adicCompletion_map` は元の核の像の閉包を、完備化した写像の核へ同定。
`closure_range_adicCompletion_map_eq_ker` は右完全列P→M→N→0に対して
完備化した最初の写像の像の閉包と、次の写像の核の一致を証明する。
最初の写像の単射性も不要。ここでは像自身の閉性を結論に含めない。

`adicCompletion_map_exact_of_finite_completion` はNoether環R、I≤Jac(R)、
**完備化した中項**のR上の有限生成性から、閉包を除いた完全性を証明する。
像で割った商が有限なのでKrullの共通部分定理から分離であり、像は閉となる。
通常の中項Mの有限生成性を仮定する既存の `AdicCompletion.map_exact` の適用とは異なる。

`CompletedDifferentialTransitivity.lean` は通常の微分の推移列へこれらを適用する。
`completedDifferentialBaseChange` の源はAdicCompletion I (S⊗_R Ω_{R/k})。
`closure_range_completedDifferentialBaseChange_eq_ker` が、この写像の像の閉包と
既存の `completedDifferentialRestriction` の核の一致を確認する。
`range_completedDifferentialBaseChange_eq_ker` は完備Ω_{S/k}が有限な場合に像自身との一致を供給する。
通常Ω_{S/k}の有限生成性を仮定せず、相対微分の完備化との比較同型を通して核を移す。

この段階の次の課題は、冪級数環上の有限正規化に対する **完備Ω_{S/k}の有限生成性の実証明** と、
最初の項をS⊗_R 完備Ω_{R/k}へ移すテンソル・完備化の比較。
有限生成性をこの一般定理へ渡すだけでGabberへの適用が完了したとは扱わない。
M3の分数体比較、階数安定化と訂正版の係数体変更も残る。引用2は未解消。

検証：対象ビルド2291ジョブ、全体ビルド4120ジョブ、公理監査530宣言が成功。
追加9宣言はすべて `assert_no_sorry` を通過し、公理は高々
`propext`・`Classical.choice`・`Quot.sound`のみ。
一般加群の閉包版と、通常の有限中項から完備中項の有限性を供給する適用例2件も
別途コンパイルして確認した。
文書検証は14 Markdown資料・295 exposition参照に対して不整合0件。

### G3b/M2の有限型閉ファイバーによる完備微分の有限生成性（2026-10-14）

`CommutativeAlgebra/AdicCompletionFinite.lean` の `adicCompletionQuotientEquiv` は
有限生成イデアルIについて、完備化のI^n商と元の加群のI^n商を実際に同定する。
`adicCompletionQuotientEquiv_mk` はこの同型が冪商への評価であることを確認する。
`moduleFinite_adicCompletion_of_finite_quotient` は、前完備な基底環Rと
有限生成なM/IMからAdicCompletion I Mの有限生成性を証明する。
元のMの有限性・分離性・完備性、Noether性・局所性は不要。
完備化の分離性と商の有限性を、既存の有限自由加群からの全射の構成へ供給する。

`CompletedKaehlerFinite.lean` の `moduleFinite_kaehler_quotient_of_finiteType_fiber` は
I.FGとessentially finite typeの閉ファイバーS/Iを仮定し、通常Ω_{S/k}/IΩ_{S/k}の有限性を証明。
Mathlibの余接の右完全列 I/I²→(S/I)⊗_S Ω_{S/k}→Ω_{(S/I)/k}→0を使う。
左項はIの有限生成性と商への全射、右項は閉ファイバーの有限型性から有限。
中項の有限性を得て、テンソル積とイデアル商の既存同型で移す。
`moduleFinite_completedKaehler_of_finiteType_fiber` はSのI進前完備性を追加し、
上の一般判定により完備Ω_{S/k}の有限生成性を得る。
体・標数・Noether性・局所性、通常Ω_{S/k}の有限生成性は不要。
有限性を新しい入力構造体に包んだのではなく、余接列の両端から実際に証明した。

`PrimaryCompletedDifferential.lean` の `moduleFinite_completedKaehler_of_primary_common_residue` は
完備Noether局所環S、共通の剰余体への全射な係数写像、m_S準素なIに適用する。
既存の `finite_quotient_of_common_residue_primary` と小さいイデアルへの完備性の移行から、
閉ファイバーの有限性・I.FG・I進前完備性を実際に供給する。
`exists_equalCharacteristic_normalization_with_finite_differential` は、通常の有限正規化が構成する
同じ係数写像φ、同じパラメータz、同じ有限単射Fに対して、
変数の像のイデアルに沿う完備微分の有限生成性を添える。整域性も不要。
通常の有限正規化の既存入口と公開型は変更していない。

`range_completedDifferentialBaseChange_eq_ker_of_finiteType_fiber` は閉ファイバーの有限型性から
完備絶対微分の有限生成性を供給し、完備化した推移列の像と核の一致へ適用する。
完備中項の有限生成性を外部から仮定するだけの適用ではない。

この段階の次は最初の項AdicCompletion I (S⊗_R Ω_{R/k})をS⊗_R 完備Ω_{R/k}へ比較し、
冪級数の有限自由な微分基底と接続する。
通常Ω_{R/k}は有限とは限らないため、有限加群に対するテンソル・完備化の交換をそのまま使わない。
Gabberの中間係数体κ_eについては、[κ:κ_e]の有限性を証明して閉ファイバーの有限型性へ移す適用が残る。
M3の分数体比較・階数安定化・訂正版の係数体変更も残り、引用2は未解消。

検証：対象ビルド2725ジョブ、全体ビルド4127ジョブ、公理監査538宣言が成功。
追加8宣言はすべて `assert_no_sorry` を通過し、公理は高々
`propext`・`Classical.choice`・`Quot.sound`のみ。
Noether性を要求しない有限型代数への適用、零イデアル、冪指数0の商同型の適用例3件も
別途コンパイルして確認した。
文書検証は14 Markdown資料・295 exposition参照に対して不整合0件。

### G3b/M2の冪級数基底に沿うテンソル・完備化の比較（2026-10-14）

`CommutativeAlgebra/PowerSeriesBaseChangeDifferential.lean` はA=k[[X]]、有限変数σ、
変数イデアルJ、そのSへの像I=JS、I進完備なSについて、
AdicCompletion I (S⊗_A Ω_{A/k}) ≃ₗ[S] S^σを構成する。
`powerSeries_baseChange_kaehler_linearMap_ext_of_isHausdorff` は、I進分離加群への写像を
1⊗dX_iの像で決定する。係数制限によりJ進分離性を供給し、既存の微分写像の外延性へ戻す。
逆写像は標準基底を完備化した1⊗dX_iへ送る。
`powerSeriesBaseChangeCompletedDifferentialBasis` が実際にこの族を基底として与え、
自由性・有限生成性も確認する。

`powerSeriesCompletedDifferentialTensorEquiv` は、既存の完備微分の基底と合わせて
S⊗_A AdicCompletion J Ω_{A/k} ≃ₗ[S] AdicCompletion I (S⊗_A Ω_{A/k})を構成する。
`_tmul_of` は、s⊗of(ω)をof(s⊗ω)へ送る標準写像との両立を証明する。
通常Ω_{A/k}の有限生成性を仮定したテンソル・完備化の交換ではない。
Noether性・局所性・体・標数・係数拡大の有限性や平坦性は、この比較には不要。
SのI進完備性と、実際の係数作用の両立を要求する。
Iの有限生成性はJ.FGの像として確認し、各証明でNoether性から供給し直さない。
任意のイデアルや任意の係数位相での交換を証明したとは扱わない。

`PowerSeriesDifferentialTransitivity.lean` の `powerSeriesCompletedDifferentialMap` は
S⊗_A 完備Ω_{A/k}→完備Ω_{S/k}を構成する。
`_tmul_of` は通常の基底微分から来るテンソルを、Sでの微分の像へ送ることを確認する。
`range_powerSeriesCompletedDifferentialMap_eq_span` は、その像を
of(d(algebraMap A S X_i))が生成するS部分加群として計算する。
この像の計算にはSのNoether性・局所性・代数の有限型性は不要。

SがNoether局所環、I≤m_S、S/Aと閉ファイバーS/Iが対応する係数上でessentially finite typeなら、
前段の完備絶対微分の有限生成性の実証明を使い、
`exact_powerSeriesCompletedDifferentialMap_restriction` が推移列の完全性を供給する。
`ker_powerSeriesCompletedDifferentialRestriction_eq_span` は係数制限の核を上の微分の生成する部分加群へ同定。
最初の写像の単射性は主張しない。

この段階の次はGabberの中間係数体κ_eの有限性と閉ファイバーの有限型性を供給し、
この推移列を各eの実際の係数作用・冪級数評価に適用する。
分数体での通常微分との比較（M3）、階数安定化、訂正版の係数体変更も残る。
通常の有限正規化と分離的有限正規化を同一視せず、引用2は未解消のまま。

検証：対象ビルド2740ジョブ、全体ビルド4130ジョブ、公理監査556宣言が成功。
追加18宣言はすべて `assert_no_sorry` を通過し、公理は高々
`propext`・`Classical.choice`・`Quot.sound`のみ。
有限代数・共通剰余体・準素性から閉ファイバーの有限性を供給する適用例と、
空変数の場合の零加群の確認も別途コンパイルした。
最初の全体ビルドでは別途変更中の `PerfectoidRootTorsion.lean` の型クラス解決が失敗したが、
そのファイルを本作業では編集せず、更新後の再実行で全体ビルド成功を確認した。
文書検証は14 Markdown資料・295 exposition参照に対して不整合0件。

### G4/Fの有限方向の中間係数体と完備微分への適用（2026-10-14）

`FieldTheory/PBasisCofiniteField.lean` の `pBasisCofiniteField b e` は
κ_e=κ^p(β_i : i∉e)を、κ^p上の実際の中間体として構成する。
有限集合eを残し、それ以外の族は無限でもよい。
`IsPBasis.adjoin_cofiniteField_eq_top` は残した有限個のβ_iでκ全体が生成されること、
`IsPBasis.finite_cofiniteField` はκ/κ_eの有限性を証明する。
各元のp乗がκ_eに属すことから整性を供給し、Mathlibの整な有限族の添加の有限生成定理を使う。
生成性だけから単項式の独立性や正確な次数を推論しない。

`pBasisCofiniteField_antitone` と `pBasisCofiniteField_directed` は、残す有限集合を増やすと
係数体が小さくなり、有限集合の和で共通の下界を得ることを確認する。
`IsPBasis.cofiniteField_empty` は空集合の場合に元の体全体となることを証明する。
`IsPBasis.iInf_cofiniteField_eq_bot` は全有限集合に対する交わりを計算する。
ここでのbotはκ^p上の中間体の最小元、すなわちκ^pそのもの。
各非零指数の一方向を残した中間体では、その指数の単項式座標が零になる。
全座標が零指数以外で消えるので、元はκ^p上の定数の単項式である。
有限p-rank・p-basis全体の有限性は使用しない。

座標の共通処理は `PBasisComplement.lean` の
`IsPBasis.coord_eq_zero_of_mem_subfamilyField` に切り出した。
任意の埋め込みで指定した部分族が使わない方向の単項式座標は、その生成体上で零。
既存の一方向を除く `IsPBasis.notMem_complementField` と新しい有限方向の座標消滅の双方が
この補題を適用するように整理し、指数の埋め込みと座標の計算を重ねない。

`CommutativeAlgebra/CofiniteCoefficientDifferential.lean` の
`IsPBasis.moduleFinite_primaryQuotient_cofiniteField` は、共通剰余体を持つ準素商S/Iのκ上の有限性を
上の有限拡大κ/κ_eへ移し、κ_e上の有限性・有限型性を供給する。
`IsPBasis.moduleFinite_completedKaehler_cofiniteField` は完備Noether局所環Sに適用し、
完備Ω_{S/κ_e}のS上の有限生成性を証明する。
係数制限・スカラー塔にはMathlibの中間体の標準インスタンスを使う。
合成した環写像から別の代数構造を重ねて加群作用の同一視を散在させない。
体の完全性・有限p-rank・Sの整域性は不要。

この段階の残りはκ_e上の相対単項式基底・正確な次数、κ_e[[τ^p]]からの実際の有限評価、
その分数体の部分体族の性質と微分の階数安定化、M3の通常微分との比較。
係数体κの族の交わりを、そのまま冪級数の分数体の族の交わりへ移したとは扱わない。
完備Ωの有限性から次元h+|e|を推論せず、その計算は別に証明する。
訂正版の係数体変更・分離的選択も残り、引用2は未解消。

検証：対象ビルド2733ジョブ、全体ビルド4134ジョブ、公理監査568宣言が成功。
追加12宣言と整理した既存の一方向の補中間体の証明は `assert_no_sorry` を通過し、
公理は高々 `propext`・`Classical.choice`・`Quot.sound`のみ。
空集合、一方向を除く既存中間体との一致、有限添字全体、閉ファイバーの有限型性、
中間体からの係数写像の一致の適用例5件も別途コンパイルして確認した。
文書検証は14 Markdown資料・295 exposition参照に対して不整合0件。

### G4/Fの相対単項式基底・次数・一意な展開（2026-10-14）

`FieldTheory/PBasisCofiniteBasis.lean` で、残す有限集合eの単項式を
κ_e上のκの実際の基底 `IsPBasis.cofiniteMonomialBasis` として構成した。
添字はPExponent p eであり、基底の各元は残したβ_iのp未満の冪の積に一致する。
`IsPBasis.finrank_cofiniteField` はこの基底から[κ:κ_e]=p^|e|を計算する。
`IsPBasis.existsUnique_cofiniteExpansion` はκ_e係数の有限台単項式展開の存在と一意性を供給する。
p-basis全体の有限性・有限p-rank・体の完全性は仮定しない。

独立性は補集合の単項式をκ_e自身のκ^p上の基底
`IsPBasis.cofiniteCoefficientBasis` として構成し、各係数をこの基底に展開して証明する。
`PMonomialPartition.lean` は二つの互いに素な方向の有限台指数を合成し、
その合成の単射性と、合成した単項式が二つの単項式の積に一致することを確認する。
元のp-basisの独立性をこの指数の合成へ制限して、積の族の独立性を供給する。
`LinearAlgebra/BasisScalarIndependence.lean` の `linearIndependent_of_basis_smul` は
係数基底との積の族の小さい係数環上の独立性から、大きい係数環上の独立性を戻す。
半環と一般の加群の範囲で証明し、係数基底や族の有限性は不要。
Mathlibの `linearCombination_smul` と基底による係数展開の全射性を使い、
p-basisや体に固定した係数展開の証明を増やさない。

生成性は、既存の添加による生成性をMathlibの `Algebra.adjoin_eq_span` へ移す。
乗法的閉包の元を有限台の任意指数の単項式に表示し、既存の
`finsuppMonomial_eq_pow_mul_remainder` でp未満の指数へ還元する。
p乗の係数がκ_eに属すことを実際に確認して相対線形包へ戻す。
前段の有限性だけから正確な次数を推論せず、独立性と生成性の両方で基底を作る。

この段階の次はκ_e[[τ^p]]からの実際の有限評価と単射性を、上の係数制限と準素商の有限性へ接続する。
冪級数の有限単項式分解、分数体の部分体族の性質、M3の微分の比較、階数安定化は残る。
κの有限拡大の次数の計算は、完備Ωの次元h+|e|の計算とは別の成果である。
訂正版の係数体変更・分離的選択も残り、引用2は未解消。

検証：対象ビルド2075ジョブ、全体ビルド4138ジョブ、公理監査583宣言が成功。
追加15宣言はすべて `assert_no_sorry` を通過し、公理は高々
`propext`・`Classical.choice`・`Quot.sound`のみ。
空集合の次数1、一方向の次数p、零指数の基底元1、有限添字全体の次数の適用例4件も
別途コンパイルして確認した。
文書検証は15 Markdown資料・295 exposition参照に対して不整合0件。

### G4/Fの中間係数体・パラメータのp乗からの有限単射（2026-10-14）

`CommutativeAlgebra/FinitePowerSeriesNormalization.lean` に、有限な閉ファイバーを使う
`exists_finite_powerSeries_map_of_finite_quotient` を追加した。
係数環kは一般の可換環、変数は有限族、評価先Dは変数の像の生成イデアルJについて完備とする。
D/Jのk上の有限性から、係数と変数の像を保持する同じ評価Fの有限性を証明する。
係数から剰余体への全射性、DのNoether性・局所性・整域性はこの一般定理には不要。
kが体でdim Dが変数の個数に等しければ、同じ評価の単射性も供給する。
通常の有限正規化の `exists_finite_powerSeries_map_of_parameters` はこの入口へ移行し、
公開定理の型を保持したまま評価・有限性の証明を共通化した。

`radical_span_powers` は任意の添字族と各生成元の正の指数について、生成イデアルの根基の一致を証明する。
有限性・Noether性・標数は不要。指数0は主張の範囲から除く。
`map_powerSeries_variables_eq_span` は任意の環写像について変数イデアルの像を確認する。

`CommutativeAlgebra/CofiniteCoefficientNormalization.lean` の
`IsPBasis.exists_finite_cofinite_powerSeries_map` はκ_e係数・X_i↦τ_i^pの評価を構成する。
p>0から(τ_i^p)の準素性を実際に証明し、そのイデアル進完備性を供給する。
κ/κ_eの有限性と元のκから剰余体への全射性を使い、D/(τ_i^p)のκ_e上の有限性を供給する。
κ_e自体から剰余体への全射性は仮定も結論もしていない。
`IsPBasis.exists_injective_finite_cofinite_powerSeries_map` はdim D個のパラメータについて
同じ評価の単射性を確認する。準素性から極大イデアルへの包含が従うため、
各τ_iの極大イデアルへの所属は別の仮定として重複させない。

この段階の残りは冪級数の有限単項式分解、分数体の部分体族、同じ評価への微分推移列の適用、
M3の通常微分・局所化との比較と階数安定化。その後に訂正版の係数体変更と分離的選択へ進む。
分数体拡大の分離性は今回の有限単射からは主張しない。引用2は未解消。

検証：全体ビルド4146ジョブ、公理監査589宣言が成功。
追加6宣言はすべて `assert_no_sorry` を通過し、公理は高々
`propext`・`Classical.choice`・`Quot.sound`のみ。
空の生成元族、各生成元で異なる正の指数、次元0での中間係数体からの有限単射、
指定変数イデアルの像の適用例4件を別途コンパイルした。
主定理の `#print sorries` も確認し、外部引用9件・保留K理論2件の境界は維持されている。
文書検証は15 Markdown資料・295 exposition参照に対して不整合0件。

### G4/Fの冪級数の有限単項式による生成性と有限拡大（2026-10-14）

`CommutativeAlgebra/PowerSeriesCoefficientBasis.lean` は、一般の可換環E→Kと
KのE上の有限基底Bから、各係数のB座標を冪級数にまとめる
`powerSeriesCoefficientComponent` を構成する。
`powerSeries_existsUnique_coefficient_decomposition` は
f=Σ_a C(B_a)·map(E→K)(g_a)の存在と一意性を証明する。
変数の有限性、係数環の体性・標数・完全性は不要。座標の定義自体は無限基底にも適用できるが、
任意の冪級数についてこの有限和の定理を使うには有限基底を要求する。

`CommutativeAlgebra/PowerSeriesFiniteExpansion.lean` は
E[[X]]→K[[T]]、X_i↦T_i^qを `powerSeriesExpandMap` として定義する。
係数・変数の像を確認し、E→Kが単射なら同じ写像が単射であることを係数から証明する。
有限係数基底と有限変数では、既存の `powerSeries_residue_decomposition` と
上の係数基底分解を組み合わせ、B_a T^r（各r_i<q）による生成性を証明する。
その有限な生成族の線形包が全体であることを確認し、同じ写像の有限性を証明した。
qは任意の正の整数でよく、標数や完全体性には依存しない。
変数の有限性は生成族を有限にする箇所で使い、単射性には要求しない。

`CommutativeAlgebra/CofinitePowerSeriesExpansion.lean` は相対単項式基底を指定し、
κ_e[[X]]→κ[[T]]、X_i↦T_i^pの有限性・単射性とβ^a T^rによる実際の有限和を供給する。
係数の相対基底の独立性と、冪級数上の単項式族の独立性は区別する。
この段階の成果は生成性と有限性であり、冪級数上の基底や次数p^(h+|e|)はまだ主張していなかった。

この段階の次は指数剰余ごとの座標抽出を有限単項式族の独立性へ接続し、冪級数上の基底を構成することだった。
一般定理の候補は、`powerSeriesExpandMap q hq` の `toAlgebra` を係数作用として
`Module.Basis ((σ → Fin q) × α) (MvPowerSeries σ E) (MvPowerSeries σ K)` を構成し、
その基底元をT^r B_aへ同定するもの。
座標の候補は各q·d+r次の係数のB座標を集めた冪級数であり、
剰余単項式を合成してから座標を抽出すると元の座標へ戻ることを確認する。
既存の係数基底の一意性だけから、異なる指数剰余の独立性まで済んだとは扱わない。
その後、実際の評価の像・分数体の部分体族、同じ評価への微分推移列、M3の比較と階数安定化へ進む。
引用2の分離的選択は未解消。

検証：対象ビルド2460ジョブ、全体ビルド4157ジョブ、公理監査601宣言が成功。
追加12宣言はすべて `assert_no_sorry` を通過し、公理は高々
`propext`・`Classical.choice`・`Quot.sound`のみ。
無限変数での係数基底分解、零冪級数の座標、指数1での変数の像、空の変数族での有限性の
適用例4件も別途コンパイルして確認した。
文書検証は15 Markdown資料・295 exposition参照に対して不整合0件。
主定理の公理監査も成功し、外部引用9件・保留K理論2件の依存が残ることを確認した。

### G4/Fの冪級数上の独立性・基底と正確な自由加群の階数（2026-10-14）

`PowerSeriesResidueDecomposition.lean` の
`coeff_powerSeriesResidueExpansion` は入力を任意の冪級数として、
T^r·expand_q(g)の係数を指数の剰余・商から計算する。
既存の `coeff_powerSeriesResidueTerm` はこの一般定理の適用へ移行し、係数計算の重複を避けた。
`powerSeriesResidueIndex_scale_add` と `powerSeriesQuotientExponent_scale_add` は
q·d+rから元の剰余rと商dが戻ることを確認する。

`CommutativeAlgebra/PowerSeriesExpansionBasis.lean` は
`powerSeriesExpansionCoordinate` でq·d+r次の係数の基底B座標を集める。
`powerSeriesExpansionCoordinate_sum` は有限単項式展開から指定した係数冪級数を戻す。
これを零の線形関係に適用し、各係数冪級数の零を証明して独立性を得る。
作用は `powerSeriesExpandMap q hq` の `toAlgebra` と
`powerSeriesExpansionModule q hq` で明示し、Mathlib標準の係数写像による作用と混同しない。
特にE=Kでは、`Algebra` だけを局所指定しても既定の環自身の `Module` が選ばれ得る。
公開定理・基底の型でも `Module` を局所指定し、X↦X^2の自己写像による作用を恒等作用と区別する。
`powerSeriesExpansion_smul` は、その加群から取り出した実際の `SMul` について
f•g=expandMap(f)·gを確認する。自己写像で `•` を使う適用時には、その `SMul` も明示する。

`powerSeriesExpansionBasis` はB_a T^rを実際の
`Module.Basis ((σ → Fin q) × α) (MvPowerSeries σ E) (MvPowerSeries σ K)` として構成する。
係数環は一般の可換環のままで、体性・Noether性・標数・完全性は不要。
非零なEについては `powerSeriesExpansion_finrank` がq^|σ|·|α|を計算する。
基底自体にはEの非零性を要求しない。
生成性は `PowerSeriesFiniteExpansion.lean` の `powerSeriesExpansion_span` へ切り出し、
既存の有限性の証明と基底構成の両方から同じ定理を使う。

`IsPBasis.cofinitePowerSeriesBasis` は相対p単項式基底を指定し、
`IsPBasis.finrank_cofinitePowerSeries` は冪級数環の間の自由加群の階数p^(h+|e|)を計算する。
これは分数体の拡大次数や、完備Ωの次元h+|e|の計算とは区別する。
この段階の次は同じ冪級数写像を分数体へ移し、その像の部分体族と微分の比較へ接続することだった。
係数体変更・階数安定化・分離的選択も残り、引用2は未解消。

検証：対象ビルド2461ジョブ、全体ビルド4157ジョブ、公理監査617宣言が成功。
追加16宣言はすべて `assert_no_sorry` を通過し、公理は高々
`propext`・`Classical.choice`・`Quot.sound`のみ。
同じ冪級数環へのX↦X^2のスカラー作用と階数2、変数が空の場合の係数階数、
選択したp-basis方向が空の場合の階数p^hの適用例4件も別途コンパイルした。
文書検証は16 Markdown資料・295 exposition参照に対して不整合0件。
主定理の公理監査も成功し、外部引用9件・保留K理論2件の依存が残ることを確認した。

### G4/Fの同じ冪級数写像に沿う分数体の基底・拡大次数（2026-10-14）

`CommutativeAlgebra/FractionRingBasis.lean` は、指定した単射の分数体への延長
`fractionRingMap` と、元の環写像との両立を供給する。
`fractionRingMapModule` は延長した同じ写像による加群作用を明示する。
`fractionRingBasisOfAlgebraic` は代数的な整域拡大A→Dの指定基底を、
Frac(A)上のFrac(D)の指定基底へ移す。基底の添字の有限性はこの構成自体には要求しない。
独立性はMathlibの `LinearIndependent.localization`、生成性は
`IsFractionRing.ideal_span_singleton_map_subset` を使い、代数的な分母を底環側へ移す。
Noether性・局所性・分離性は要求しない。
有限基底については `finrank_fractionRing_eq_natCard_basis` がその大きさを拡大次数へ移す。

既存の `span_range_fractionRing_eq_top` は `SeparableBaseChange.lean` からこの共通層へ移した。
名前と既存の利用先は保持し、環と体の宇宙を独立に一般化した。
以前の証明オプションは不要で、線形包の集合としての包含を明示して同じ証明を通した。
`PowerSeriesDomain.lean` は既存の `isDomain_mvPowerSeries` を
`PowerSeriesRegular.lean` から移した小さな入口。整域性の名前・型・インスタンスを保持し、
分数体の一般論から正則局所性・Witt係数や分離性の理論への依存を避けた。

`PowerSeriesFractionField.lean` は `powerSeriesFractionMap` で
E[[X]]→K[[T]]、X_i↦T_i^qをそのまま分数体へ延長する。
元の環の像での両立と二つの `IsScalarTower` を実際に確認する。
局所化の既定の `SMul` とは混同せず、塔の証明では指定した代数の作用を明示する。
`powerSeriesFractionBasis` はB_a T^rの像を分数体の基底へ移す。
`finrank_powerSeriesFractionField` はq^h·|α|を計算する。
係数環E・Kはここでは体とし、元の有限基底から代数性を供給する。分離性は使わない。

`IsPBasis.cofiniteFractionBasis` と `IsPBasis.finrank_cofiniteFractionField` は
κ_e[[X]]→κ[[T]]、X_i↦T_i^pに沿う分数体拡大の基底と正確な次数p^(h+|e|)を供給する。
これで形式的な冪級数環の間の階数から分数体の次数への接続は実装済み。
正規化先Dの分数体での像、部分体族の交わり、完備Ωの次元h+|e|はまだ主張しない。

この段階の次はK₀=Frac(κ[[T]])内で各延長写像の像を実際の部分体として構成することだった。
e⊆fに対するκ_f→κ_eの係数写像と、同じ変数のp乗による冪級数写像の合成を確認し、
分数体の写像の一意性から像の逆向きの包含と有向性へ移す。
交わりがK₀^pになることは係数体の交わりだけから自動的には推論せず、別に証明する。
その後、通常の正規化の有限単射をFrac(D)へ延長し、同じ部分体族をその像へ移す。
M3の微分との比較・階数安定化、訂正版の係数体変更・分離的選択も残る。引用2は未解消。

検証：対象ビルド2471ジョブ、全体ビルド4165ジョブ、公理監査633宣言が成功。
追加15宣言と移動した共通補題はすべて `assert_no_sorry` を通過し、公理は高々
`propext`・`Classical.choice`・`Quot.sound`のみ。
元の変数の像、同じ分数体へのX↦X^2による拡大次数2、空の変数族での係数次数、
空のp-basis方向での次数p^hの適用例4件を別途コンパイルした。
文書検証は16 Markdown資料・295 exposition参照に対して不整合0件。
主定理の公理監査も成功し、外部引用9件・保留K理論2件の依存が残ることを確認した。

### G4/Fの共通分数体内の部分体族とp乗部分体の包含（2026-10-14）

`PowerSeriesFractionSubfield.lean` の `powerSeriesCoefficientFractionMap` は
係数写像φ:E→Fだけを作用させ、変数を保つ分数体の写像を構成する。
`powerSeriesFractionMap_comp_coefficientMap` は、係数写像の合成がκへの写像と両立すれば、
その写像とX_i↦T_i^qの分数体写像の合成が一致することを証明する。
元の冪級数の係数写像の合成を確認し、Mathlibの分数体の写像の一意性を使う。
環写像が係数・変数の像で一致するというだけでは済ませていない。
`powerSeriesFractionSubfield` は共通のFrac(κ[[T]])内の実際の像を `Subfield` として取る。
`powerSeriesFractionSubfield_le_of_coefficientMap` は上の因子分解から像の包含を供給する。
これらの写像と包含には変数の有限性を要求しない。

`CofiniteFractionSubfield.lean` の `pBasisCofiniteFractionSubfield` は
κ_e[[X]]→κ[[T]]、X_i↦T_i^pの延長写像の像F_eを実際の部分体として構成する。
e⊆fに対しκ_f→κ_eの包含を指定し、κへの係数写像との両立を実際に確認する。
これによりF_f⊆F_eを証明し、e∪fを使って下向きの有向性を供給する。
`FractionRingBasis.lean` の `finrank_fieldRange` は、体の写像による係数作用と
その実際の像の部分体による係数作用の拡大次数を、Mathlibの体同型による次数比較へ接続する。
`IsPBasis.finrank_cofiniteFractionSubfield` はK₀/F_eの次数p^(h+|e|)を供給する。
その正の次数から `IsPBasis.finite_cofiniteFractionSubfield` が有限次元性を供給する。
係数体のp-basis全体の有限性を仮定しない。

`cofiniteFrobeniusCoefficientMap` はκの各元のp乗をκ_eの元として取る実際の環写像。
これを係数へ作用させた分数体写像と、X_i↦T_i^pの写像の合成が
共通分数体K₀のFrobeniusになることを証明した。
Mathlibの冪級数のFrobenius・指数展開の公式と、分数体の写像の一意性を使う。
`pPowerSubfield_le_cofiniteFractionSubfield` はK₀^p⊆F_eを、
`pPowerSubfield_le_iInf_cofiniteFractionSubfield` はK₀^p⊆⋂_e F_eを供給する。
`PowerSeriesCharacteristic.lean` は定数の埋め込みの単射性から冪級数環の標数を確認し、
分数体の標数はMathlibの既存インスタンスで移す。変数の有限性・整域性・素数性は
冪級数環の標数を移す一般定理には不要で、係数は一般の可換半環でよい。

この段階の次は⋂_e F_e⊆K₀^pを証明することだった。係数体の交わりの結果だけから、
分数体の像の交わりまで同定したとは扱わない。
その後、通常の正規化の同じ有限単射をFrac(D)へ延長し、上の部分体族を実際の像へ移す。
M3の微分の比較・階数安定化、訂正版の係数体変更・分離的選択も残る。引用2は未解消。

検証：対象ビルド2474ジョブ、全体ビルド4168ジョブ、公理監査649宣言が成功。
追加16宣言はすべて `assert_no_sorry` を通過し、公理は高々
`propext`・`Classical.choice`・`Quot.sound`のみ。
選択方向が空・変数が一個での次数p、無限変数でのp乗部分体の包含、分数体への標数の移送、
恒等係数写像を挟んでも変数のq乗を二重に適用しない合成の適用例4件を別途コンパイルした。
文書検証は16 Markdown資料・295 exposition参照に対して不整合0件。
主定理の公理監査も成功し、外部引用9件・保留K理論2件の依存が残ることを確認した。

### G4/Fの共通分母・基底の飽和性による交わりの逆包含（2026-10-14）

訂正版GTG.pdfのExposé IV §2.1.6で、この分数体族が階数安定補題の仮定を満たす箇所を確認した。
係数体の交わりをそのまま分数体へ移さず、以下の分母の処理を実装した。

`LinearAlgebra/BasisSaturation.lean` の `basis_mem_span_singleton_of_smul_mem` は、
非零スカラーaについてa·xが一つの基底元の線形包に属せば、xも同じ線形包に属すと証明する。
係数は零因子なしの可換半環、対象は一般の加群とし、基底の有限性や体性は不要。
`FractionRingBasis.lean` の `mem_range_algebraMap_of_smul_mem_of_basis_one` は、
基底に1が含まれる環拡大の底環の像へこの飽和性を適用する。
`algebraMap_mem_fractionRingMap_fieldRange_iff_of_basis_one` は分数を底環側の分子・分母で表し、
その分母を払って、分数体の像と元の環の交わりが底環の像になることを証明する。
基底に1が含まれることを仮定・適用時に実際に確認し、Noether性・整閉性・代数性は要求しない。

`PowerSeriesFractionSubfield.lean` の
`algebraMap_mem_powerSeriesFractionSubfield_iff_of_basis_one` は、
係数基底元1と零の指数剰余から冪級数基底元1を確認して、この交わりの定理へ接続する。
`CofiniteFractionIntersection.lean` の
`IsPBasis.exists_powerSeries_pow_of_mem_all_cofinite_ranges` は、全ての環の像に属す冪級数の
p倍の指数の係数を各κ_eへ戻し、係数体の交わりκ^pとFrobenius同型でp乗根を構成する。
変数のp乗の像にあることも元の冪級数から確認する。この環側の補題には変数の有限性は不要。

分数体の元x=f/gについては、x=n/g^p、n=f·g^(p−1)と表す。
g^pは全F_eに属すので、xが全F_eに属せばnも全F_eに属す。
上の飽和性と、相対単項式基底の零指数の基底元が1であることを確認して、
nを各κ_e[[T^p]]の実際の環の像へ戻す。
環側のp乗根n=u^pを構成するとx=(u/g)^pを得る。
これが `IsPBasis.mem_pPowerSubfield_of_mem_all_cofiniteFractionSubfields` の証明であり、
`IsPBasis.iInf_cofiniteFractionSubfield_eq_pPower` が⋂_e F_e=K₀^pを供給する。
有限変数は冪級数の加群基底を使う箇所で要求し、κの有限p-rankは要求しない。

これでK₀内の部分体族について、各拡大の有限性、下向きの有向性、交わりK₀^pを全て確認した。
次は通常の正規化の同じ有限単射をFrac(D)へ延長し、この族を実際の像へ移す。
その後、M3の微分の比較・階数安定化へ接続する。訂正版の係数体変更・分離的選択も残り、引用2は未解消。

検証：対象ビルド2476ジョブ、全体ビルド4173ジョブ、公理監査656宣言が成功。
追加7宣言はすべて `assert_no_sorry` を通過し、公理は高々
`propext`・`Classical.choice`・`Quot.sound`のみ。
変数が空での交わり、無限変数の零冪級数のp乗根、分母Xを持つ分数のp乗、
零分数への逆包含の適用例4件も別途コンパイルした。
文書検証は16 Markdown資料・295 exposition参照に対して不整合0件。
主定理の公理監査も成功し、外部引用9件・保留K理論2件の依存が残ることを確認した。
全体ビルド時には、並行する根APIの共通化で旧利用先の書き換え2件が失敗したため、
`CLMST/PerfectoidFrobeniusComparison.lean` の該当箇所だけを
`CLMST.completedTowerRoot_zero` の明示的な等式の合成へ変更した。共通の根の定義は保持した。

### 2026-10-14：同じ通常有限正規化をFrac(D)へ延長

`FractionRingBasis.lean` に `fractionRingMap_comp` と
`fractionRingMap_finite`、`fractionRingMap_fieldRange_finite` を追加した。
`finiteDimensional_fractionRing_of_finite` は `SeparableBaseChange.lean` から
この共通層へ移し、環・分数体の宇宙を独立にした。既存名と利用先は保持する。
有限加群の係数拡大から分数体への全射を作る既存の証明を再利用し、
指定した写像に沿う加群作用を明示する。分離性・Noether性・局所性は要求しない。

`CofiniteNormalizationFraction.lean` の
`pBasisNormalizationFractionSubfield` は、同じFの延長でF_eをFrac(D)へ移す。
`pBasisNormalizationFractionSubfield_eq_fieldRange` が、これを実際の合成した
冪級数評価の分数体写像の像と同定する。反単調性と下向き有向性を移し、
`IsPBasis.finite_normalizationFractionSubfield` が各像上のFrac(D)の有限性を確認する。
有限変数での交わりは `IsPBasis.iInf_normalizationFractionSubfield_eq_map_pPower` により
埋め込んだK₀^pの像と等しい。Mathlibの `Subfield.map_iInf` を使用する。
全p-basisの有限性は要求せず、Frac(D)^pとの一致は主張しない。

`EqualCharacteristicFractionNormalization.lean` の
`exists_equalCharacteristic_finite_fraction_normalization` は、整域の場合に
既存の通常有限正規化の同じ係数体・パラメータ・F・剰余体への全射性を保持し、
Fの分数体延長の有限性を追加する。IsDomain Dはこの延長に必要な箇所に置き、
元の通常有限正規化の定理には加えていない。
この具体的な存在定理のimportは、部分体族の一般論から分けた。

次はM3の微分の比較と階数安定化へ進む。係数変更と最終的な分離性は未証明であり、
引用2はまだ置換していない。主定理の外部引用9件・保留K理論2件の境界を維持する。

検証：対象ビルド2824ジョブと、最終の全体ビルド4176ジョブが成功。
共通可換環論監査666宣言の `assert_no_sorry` が成功し、追加10宣言の
`#print axioms` はpropext・Classical.choice・Quot.soundのみ。
空変数、空の方向集合、合成評価の係数・パラメータの像、恒等自己写像、
X↦X²の非自明な自己写像の5例も成功。文書検証は16 Markdown資料・
295 exposition参照に対して不整合0件。主定理の公理監査で9件＋2件を再確認した。
初回の全体ビルドは、並行作業によるルートimportの追加がビルド中に入り
新しい生成物が未生成だったため停止した。依存関係を取り直した再実行は成功した。

### 2026-10-14：相対微分の局所化・分離性判定と分離的段階の階数保存

`FractionDifferential.lean` の
`relativeDifferentialEquivOfFormallyUnramified` は、底環拡大のΩが零なら
係数制限の微分写像が同型であることを、通常の推移列の完全性から証明する。
`fractionDifferentialEquiv` はMathlibの局所化の形式的エタール性と
`tensorKaehlerEquivOfFormallyEtale` を組み合わせ、L⊗_D Ω_{D/A}≃Ω_{L/K}を構成する。
`fractionDifferentialEquiv_tmul_D` が自然な普遍微分との両立を確認する。
この同型は有限性・Noether性・局所性を要求せず、異なる宇宙の環・体で使える。

有限体拡大での `isSeparable_iff_subsingleton_kaehlerDifferential` と
`isSeparable_iff_finrank_kaehlerDifferential_eq_zero` は、Mathlibの
`FormallyUnramified.iff_isSeparable` を再利用する。有限型性から通常Ωの有限性を供給し、
`Module.finrank_zero_iff` を使って次元0から零加群へ移す。
`isSeparable_fractionRing_iff_finrank_tensorDifferential_eq_zero` は
有限整域拡大から分数体拡大の有限性を実際に確認して適用する。
指定写像版 `isSeparable_fractionRingMap_iff_finrank_tensorDifferential_eq_zero` では、
環と分数体の両方のAlgebra・Moduleを同じFから取り、自己作用との混同を防ぐ。
自己写像でも数値評価が体自身の標準作用を使うよう、分数体拡大のAlgebraは
分離性の引数に直接渡す。DからFrac(D)への標準Module・SMulも明示し、
局所化の既定作用が元の自己写像に沿う作用を拾うことを防ぐ。
利用先では公開定理の結果型をそのまま保持する。A=Dの具体例で局所インスタンスを
再宣言してΩとテンソルの型を書き直すと、底環作用と対象環の自己作用が競合し得る。
確認例のX↦X²への適用は、公開定理の結果型を保持して検証した。

`CompletedFractionDifferential.lean` の `completedFractionDifferentialEquiv` は、
完備性を先に確認した通常の相対Ωを完備化から戻し、その同型を局所化へつなぐ。
D/Aはessentially finite typeで十分であり、AのNoether性・局所性は不要。
分離性判定 `isSeparable_fractionRing_iff_finrank_completedRelativeDifferential_eq_zero` には
有限整域拡大を用い、同じ分数体作用について完備相対微分の生成点での次元0を判定する。
通常の相対Ωの有限性を、κ_e上の絶対Ωの有限性へ読み替えていない。

`FieldTheory/SeparableDifferentialRank.lean` は、分離的な拡大で
通常微分が自然な係数拡大となること、その有限性を移せること、次元が変わらないことを供給する。
L/K自体の有限性や、底体の有限p-rankは要求しない。

残る課題はκ_e上の完備微分の生成点での通常微分との比較、
階数安定化の純非分離の次数pの段階と有限拡大への帰納、訂正版の係数変更と分離的選択。
引用2は未解消であり、主定理の外部引用9件・保留K理論2件は保持する。

検証：通常微分・分離的階数の対象ビルド2453ジョブ、完備相対微分の対象ビルド2530ジョブ、
最終の全体ビルド4181ジョブが成功。共通可換環論監査681宣言の `assert_no_sorry` が成功。
追加15宣言の公理はpropext・Classical.choice・Quot.soundのみ。
恒等体拡大、有限性を仮定しない分離的拡大、X↦X²による同じ環の非自明な自己作用、
零イデアルの完備化、零元の普遍微分の5例が成功。
文書検証は16 Markdown資料・295 exposition参照、不整合0件。
主定理の公理監査で外部引用9件・保留K理論2件を再確認した。

### 2026-10-14：非分離な単生成拡大の微分基底とp乗根添加の次元上界

訂正版GTG.pdf、Exposé IV Proposition 1.2.4の純非分離段階を確認した。
原典はx^p=bの関係を用いて、元の微分からdbの一方向を落とすことと、
新しいdxの一方向を加えることを組み合わせる。
この段階の成果は後者の実際の基底と、前者による次元の上界であり、等号全体ではない。

`FieldTheory/MonogenicDifferentialRank.lean` に
`PowerBasis.span_kaehlerDifferential_gen` と `PowerBasis.kaehlerDifferentialBasis` を追加した。
生成性は既存の代数の生成元からの導分の生成性を再利用し、独立性は
`PowerBasis.generatorDerivation` により生成元の微分が非零であることから得る。
`PowerBasis.finrank_kaehlerDifferential` はその一元基底から次元1を計算する。
この一般層にはp・標数・局所性・Noether性を要求しない。
`finrank_kaehlerDifferential_primeRoot_of_adjoin_eq_top` は既存のp乗根添加の最小多項式を使い、
非自明なp乗根が終域全体を生成する場合へ適用する。

`PowerBasis.finrank_kaehlerDifferential_tower` は有限なK/Rについて
finrank_L Ω_{L/R}=finrank_L range(mapBaseChange R K L)+1を供給する。
Bの冪基底からL/Kの有限性を得て、有限体拡大の推移性と有限型の微分の一般論から
Ω_{L/R}の有限性を確認し、通常の推移列とMathlibの階数・零化次元定理を使う。

`primeRoot_differential_mem_ker_mapBaseChange` は、x^p=bの関係式から
1⊗dbが最初の写像の核に入ることを証明する。Rは一般の可換環でよく、有限性も要求しない。
`PowerBasis.finrank_kaehlerDifferential_tower_le_of_primeRoot` はdb≠0から
体拡大の忠実平坦性により1⊗db≠0を確認する。核の次元が正であることと
二つの次元式を組み合わせてfinrank_L Ω_{L/R}≤finrank_K Ω_{K/R}を証明する。
`finrank_kaehlerDifferential_primeRoot_tower_le_of_adjoin_eq_top` が実際のp乗根生成元へ接続する。
関係式の微分が非零である条件を暗黙にせず、全p-basisの有限性も要求しない。

次は核がL(1⊗db)だけであることの同定、交わり条件からdb≠0となる部分体の選択、
有限拡大への帰納へ進む。κ_e上の完備微分との比較と訂正版の係数変更も残る。
引用2は未解消であり、主定理の外部引用9件・保留K理論2件は維持する。

検証：対象ビルド2085ジョブ、全体ビルド4183ジョブが成功。
共通可換環論監査690宣言の `assert_no_sorry` が成功し、追加9宣言の公理は
propext・Classical.choice・Quot.soundのみ。基底からの微分空間の有限性、
無限p-basisの補中間体上の次元1、零の関係式、共有限な底体上の次元上界の4例も成功。
文書検証は16 Markdown資料・295 exposition参照、不整合0件。
主定理の公理監査でも外部引用9件・保留K理論2件を再確認した。

### 2026-10-14：p乗根添加の導分の延長、核の同定、条件付きの次元等号

`CommutativeAlgebra/ModuleDerivationDescent.lean` に `descendModuleDerivation` を追加。
全射S→Tの核を消すR導分S→Vを、Tの加群Vへ降下する。
既存 `DerivationDescent.lean` の環自身を値域とする入口は、この一般版を使うwrapperへ移した。
公開型と元の導分との両立は保持し、旧利用先もこの共通証明を経由する。

`CoefficientEvalDerivation.lean` はMathlibの `Derivation.mapCoeffs` と
`PolynomialModule.map`・`PolynomialModule.eval` を組み合わせ、
係数導分を多項式へ適用して指定したxで評価するR線形写像を構成する。
定数の導分を保持し、変数を0に送り、aeval xによる作用についてLeibniz則を満たす。
係数環・評価先は一般の可換環、値域は一般の加群でよい。
必要な係数制限の両立は実際の `IsScalarTower` から供給する。

`FieldTheory/PrimeRootDerivationExtension.lean` の
`exists_derivation_primeRoot_extension` は、非自明なx、x^p=b、K[x]=Lについて
δ(b)=0であるR導分δ:K→Vを、xを0に送るR導分L→Vへ延長する。
最小多項式X^p-C bの係数導分が零であることを確認し、その倍数も消すことを証明する。
評価の全射性は実際の冪基底から供給し、核の確認後に共通の加群値降下を適用する。
導分の延長や微分の核の結論を、仮定や構造体のフィールドとして渡していない。

`PrimeRootDifferentialKernel.lean` の
`ker_mapBaseChange_primeRoot_of_adjoin_eq_top` は、推移列の核をL(1⊗db)へ同定する。
逆包含は、M=L⊗_K Ω_{K/R}をこの一方向で割った加群Qへ向かう導分を作り、
その導分をLへ実際に延長して普遍性を適用する。
Rは一般の可換環でよく、微分空間の有限性・有限p-rankは要求しない。
商加群のR・K作用をL作用から明示し、Module・MulAction・SMulと塔の法則を両立させる。

`finrank_kaehlerDifferential_primeRoot_tower_eq_of_adjoin_eq_top` は、
K/Rが有限な体拡大でdb≠0ならfinrank_L Ω_{L/R}=finrank_K Ω_{K/R}を供給する。
有限性を実際の冪基底と有限拡大の推移性から確認し、
一方向の核と新しいdxの一方向の次元を計算する。db=0の境界では核は零になる。

次は、部分体族の交わりの条件からdbが非零となる十分小さい部分体を選ぶ議論。
通常微分の零元とp乗の部分体の関係、有限拡大への帰納を接続する必要がある。
κ_e上の完備微分との比較、訂正版の係数変更と最終的な分離的選択も残る。
引用2は未解消であり、主定理の外部引用9件・保留K理論2件は維持する。

検証：対象ビルド2091ジョブ、全体ビルド4194ジョブが成功。
共通可換環論監査699宣言の `assert_no_sorry` が成功し、追加9宣言の公理は
propext・Classical.choice・Quot.soundのみ。零の評価点、一般の加群への延長、
db=0で核が零になる境界、共有限な底体上の次元等号の4例も成功。
文書検証は16 Markdown資料・295 exposition参照、不整合0件。
主定理の公理監査でも外部引用9件・保留K理論2件を再確認した。

### 2026-10-14：絶対微分の零判定と検出体、底環制限での非零性の保存

`FieldTheory/PIndependentSet.lean` の空集合のp独立性を
`isPIndependentSet_empty` へ切り出し、既存のp-basis存在証明と指定元の添加で共有する。
`PBasisDifferentialConstants.lean` の
`exists_pBasis_containing_of_not_mem_pPowerSubfield` は、b∉K^pなら
空集合へbを添加し、既存の最大p独立集合の構成からbを含む実際のp-basisを得る。
`exists_derivation_detecting_not_mem_pPowerSubfield` は、その偏導分でbを1に送る。
`kaehlerDifferential_over_pPowers_eq_zero_iff` がD_{K/K^p}(b)=0↔b∈K^pを証明する。
微分空間・p-basis・体拡大の有限性は要求しない。
この零判定は絶対的なp乗部分体上のもので、一般の底体R上の判定とは区別する。

`exists_finite_intermediateField_detecting_not_mem_pPowerSubfield` は、
bを含むp-basisの一方向の補中間体Eを選び、K/Eの有限性とD_{K/E}(b)≠0を確認する。
有限性はbのp乗根添加の実際の冪基底から供給する。
指定した部分体族の一員であること、またはその族の一員がEに含まれることは主張しない。

`CommutativeAlgebra/KaehlerBaseRestriction.lean` の
`kaehlerDifferential_ne_zero_of_baseRestriction` は、R→S→Tの実際の塔について
D_{T/S}(b)≠0ならD_{T/R}(b)≠0を供給する。環は一般の可換環でよく、標数・有限性は不要。
`PrimeRootDifferentialKernel.lean` の
`finrank_kaehlerDifferential_primeRoot_tower_eq_of_baseRestriction` は、
一つの底環S上で確認した関係式の微分の非零性を、より小さい共有限な底体Rでの
次数pの次元等号へ適用する。Rの共有限性は仮定し、次元式に必要な有限性へ使う。

`CofiniteFractionIntersection.lean` の
`IsPBasis.exists_not_mem_cofiniteFractionSubfield` は、実際の部分体族の交わりがK₀^pであることから
b∉K₀^pならb∉F_eとなる指標eを得る。
これは非所属の選択であり、D_{K₀/F_e}(b)≠0を得る相対判定はまだ必要。
原典Corollaire 1.1.8の一般相対版とLemma 1.2.2・1.2.3の接続を残作業として区別する。
有限拡大への帰納、κ_e上の完備微分との比較、訂正版の係数変更・最終的な分離的選択も残る。
引用2は未解消であり、主定理の外部引用9件・保留K理論2件は維持する。

検証：対象ビルド2502ジョブ、全体ビルド4198ジョブが成功。
共通可換環論監査707宣言の `assert_no_sorry` が成功し、追加8宣言の公理は
propext・Classical.choice・Quot.soundのみ。零元、p乗の元、無限p-basisの一方向の共有限検出体、
同じ底環への係数制限、空変数の分数体族からの非所属指標選択の5例も成功。
文書検証は16 Markdown資料・295 exposition参照、不整合0件。
主定理の公理監査でも外部引用9件・保留K理論2件を再確認した。

### 2026-10-14：有限指数1の相対零判定と、実際の族に対する次数pの階数安定

`FieldTheory/FiniteExponentOneConstants.lean` の
`exists_maximal_intermediateField_not_mem` は、有限体拡大K/Fで指定元bを避ける最大中間体Eを
[K:E]の最小化から選ぶ。全ての中間体についてK/Eが有限なので、次数比較は有限次元の比較になる。
`exists_derivation_detecting_finite_exponentOne` は、全てのp乗がFの像に属する場合、
Eの外の任意の元yの添加が次数pになることを確認する。
最大性からb∈E(y)、同じ次数pと包含からE(b)=E(y)を得て、K=E(b)を証明する。
生成元bを1に送るE導分を構成し、Fへ係数制限する。
`kaehlerDifferential_finite_exponentOne_eq_zero_iff` がD_{K/F}(b)=0↔b∈range(algebraMap F K)を供給する。
`kaehlerDifferential_finite_subfield_eq_zero_iff` がp乗部分体を含む共有限な部分体へ適用する。
底体自身・終域自身の有限p-rankは要求しない。

`CommutativeAlgebra/CofiniteFractionDifferential.lean` の
`IsPBasis.kaehlerDifferential_cofiniteFractionSubfield_eq_zero_iff` は、
実際のF_eについて、既存の有限性とp乗部分体の包含を確認して判定を適用する。
`IsPBasis.exists_kaehlerDifferential_cofiniteFractionSubfield_ne_zero` は、
実際の交わりの定理から得る非所属の指標を、微分が非零になる指標へ移す。
`IsPBasis.kaehlerDifferential_cofiniteFractionSubfield_ne_zero_of_subset` は後続指標でも非零性を保つ。
ここでは、新しく構成した別の検出体が指定族に属すると仮定していない。

`PAdjoin.lean` の `primeRoot_coefficient_not_pow` は、元の体の外のp乗根の係数は
元の体の中でp乗でないことをFrobeniusの単射性から証明する。
既存の最小多項式の既約性の証明も、この同じ補題を再利用する。
`KaehlerBaseRestriction.lean` の `kaehlerDifferential_subfield_ne_zero_of_le` は
部分体の包含に由来する実際の係数の塔を確認して、非零性を小さい部分体へ移す。

`FieldTheory/SubfieldFamilyPrimeRootRank.lean` の
`exists_subfieldFamily_primeRoot_rank_stable` は、一般の体Kの共有限な部分体族について
各体の有限性・K^pの包含・交わりがK^pであることを用い、次数pの段階を供給する。
この一段では有向性は不要で、有限p-rankも要求しない。
有限拡大後の別の部分体族にも適用できるよう、冪級数の実現から証明を切り離した。
`CofiniteFractionPrimeRootRank.lean` の
`IsPBasis.exists_cofiniteFractionSubfield_primeRoot_rank_stable` は、
この共通定理の三つの仮定を既存の実際の族の定理で確認して適用する。

非自明なp乗根x、x^p=b、K₀[x]=Lに対し、あるeを選んで、F_e以下の任意の共有限な部分体Rで
finrank_L Ω_{L/R}=finrank_{K₀} Ω_{K₀/R}を供給する。
b∉K₀^pはp乗根の非所属から証明し、D_{K₀/F_e}(b)≠0も実際の族で確認するため、
関係式の微分の非零性を追加の仮定として渡していない。
R→Lの作用は指定済みのK₀→LとR→K₀の合成で与え、Module・SMulも同じAlgebraから明示する。
RがK₀^pを含むことは要求せず、F_eで得た非零性をRへ係数制限して使う。

次は有限拡大M/K₀の後の部分体族F_e(M^p)の交わりをM^pへ同定する接続と、
一般の有限拡大への帰納。分離的な段階と次数pの段階の単独の次元比較は供給済みだが、
階数安定化全体の証明はまだ完了していない。
κ_e上の完備微分との比較、訂正版の係数変更と最終的な分離的選択も残る。
引用2は未解消。今回のCohen–Gabber作業は主定理の引用境界を変更していない。
最終監査時には、並行するCLMST作業で `Inputs.completedTower_isIntegralPerfectoid` が
`propext`・`Classical.choice`・`Quot.sound` のみの証明へ置換されていたため、
主定理の未証明入力は外部引用8件・保留K理論2件となった。過去の9件という検証記録は当時の状態を表す。

検証：対象ビルド2501 jobs、全体 `lake build` 4207 jobsが成功。
局所代数監査の718宣言について `assert_no_sorry` が成功し、今回追加した11宣言の公理は
`propext`・`Classical.choice`・`Quot.sound` のみ。
自明な拡大、零元、空の変数集合、有限p-rankを要求しない非零性の持続と、
実際の次数pの階数安定定理の直接適用を合わせた5件の境界・API確認も成功。
文書検証は16 Markdownファイルと295 exposition参照で不整合0件、`git diff --check` も成功した。

### 2026-10-14：次数pの拡大後の部分体族の交わりと再適用

前回残したF_e(L^p)の交わりについて、非自明な次数pの添加の一段を実装した。
共通の有限族vがあるE_j上で独立で、E_iの族が下向き有向なら、
元zが全てのE_i線形包に属することと、⋂_i E_i上の線形包に属することは同値。
`sum_mul_mem_subfield_span_iff` は固定した独立展開の係数の所属を検出し、
`mem_all_subfield_spans_iff` はE_i・E_jより小さいE_kを選んで展開の一意性を使う。
体の標数・有限拡大性・有限p-rankは、この線形代数の共通部分には要求しない。

`mem_subfield_adjoin_primeRoot_iff` はa^p∈EならE(a)をp未満の冪の線形包として扱う。
a∈Eの退化した場合を別途証明し、a∉Eの場合には既存の最小多項式とMathlibの冪基底を使う。
⋂_i E_i=K^pとa∉K^pから、a∉E_jとなる指標を選んでその体上の独立性を確認し、
`iInf_subfield_adjoin_primeRoot` が⋂_i E_i(a)=K^p(a)を供給する。
族全体の有限性はこの交わりの定理には不要。

`pPowerSubfield_primeRoot_eq_map_adjoin` はL=K[x]、x^p=aからL^pをK^p(a)の像へ同定する。
通常の部分代数の生成条件に沿った帰納で、全てのp乗がその像に入り、逆包含も実際のp乗根から確認する。
この同定は自明な添加にも適用できる。
非自明な添加について、拡大後の族G_i=E_iの像⊔L^pの交わりをL^pへ同定する。
像と交わりの交換にはMathlibの `Subfield.map_iInf` を使用する。
その添字の非空性はa∉K^pから導き、空の添字の交わりで埋め込みの像とL全体を同一視しない。

`finite_subfield_of_map_le` はE⊆K、Eの像⊆G⊆Lについて、K/EとL/Kの有限性からL/Gの有限性を供給する。
E→LとE→G→Lの作用が同じであることを明示的なスカラー塔で確認する。
`CofiniteExtendedFractionSubfield.lean` は実際の分数体族をG_e=F_eの像⊔L^pへ拡張し、
共有限性・反単調性・下向き有向性を証明する。共有限性と有向性は任意の有限拡大で使える。
次数pの添加後の交わりは、元の実際の族の交わり・包含・有向性を確認して共通定理へ適用する。
一段目の生成条件からL/K₀の有限性も供給し、得た三条件を使って次の次数pの添加での階数安定定理を再適用した。

これは一般有限拡大での階数安定化全体の完了ではない。
次は分離的な段階での拡大後の族の交わり、一般有限拡大の分解と帰納、
各段階の次元等号を同じ共有限底体へ揃える接続を進める。
κ_e上の完備微分との比較、訂正版の係数変更・最終的な分離的選択も残る。
引用2は未解消であり、新しい未証明入力は追加しない。

検証：対象ビルド2504 jobs、全体 `lake build` 4214 jobsが成功。
局所代数監査735宣言の `assert_no_sorry` が成功し、今回追加した17宣言に
`propext`・`Classical.choice`・`Quot.sound` 以外の公理依存はない。
空の有限基底、底体内の添加元、空の変数集合で拡大しない族、自明な添加のp乗部分体の4境界例と、
交わり・再適用の2公開API確認も成功。今回の新規モジュールと境界例に警告はない。
文書検証は16 Markdownファイル・295 exposition参照で不整合0件、`git diff --check` も成功。
主定理監査では外部引用8件・保留K理論2件を再確認した。引用2はその8件に含まれる。

### 2026-10-14：分離的有限拡大後の交わりと、族の塔に沿う合成

L/Kの任意の有限基底Bについて、L^pはK^pの像上でB_i^pを張った空間となる。
`pPowerSubfield_eq_span_pow_basis` は基底展開へFrobeniusを適用してこの生成性を証明する。
分離性はこの計算には要求しない。分離的拡大では、Mathlibの
`LinearIndependent.map_pow_expChar_pow_of_isSeparable` によりB_i^pはK上でも独立である。
この独立性を体の埋め込みの像と、その小さい部分体へ移す処理は
`linearIndependent_fieldRange`・`linearIndependent_subfield_of_le` として公開し、
Mathlibのスカラー変換の一般定理を適用する。

`mem_subfield_sup_iff_mem_span` はF⊆EとSのF上の生成族について、EとSの合成をE線形包へ直す。
E上のLの有限性は、`IntermediateField.adjoin_toSubalgebra` に必要な代数性へ使う。
ここで生成族の積や逆元の閉性を独自に再実装せず、Mathlibの中間体・部分代数・部分単群の添加と線形包のAPIを使った。
`iInf_subfield_sup_pPower_of_isSeparable` は、E_iの像についての有限性と独立性を確認し、
前回の `mem_all_subfield_spans_iff` を使って⋂_i (E_iの像⊔L^p)=L^pを証明する。
この共通定理は非空な添字・共有限な下向き有向族・交わりK^p・分離的有限拡大を仮定する。
有限p-rankは要求しない。実際の族の添字Finset ιは、ιが空でも空集合を持つため非空である。

`IsPBasis.iInf_extendedFractionSubfield_of_isSeparable` は実際の族で全ての仮定を確認して適用する。
`IsPBasis.exists_extendedFractionSubfield_primeRoot_rank_stable_of_isSeparable` は、
この交わり・共有限性・p乗部分体の包含から次の次数pの段階へ共通定理を再適用する。
微分の非零性や拡大後の交わりを追加の未証明入力として渡していない。

`map_pPowerSubfield_le` は任意の体準同型がp乗部分体をp乗部分体へ送ることを確認する。
`map_subfield_sup_pPower_tower` はこの包含とMathlibの像の合成・上限の保存を使い、
(Eの像⊔L^p)をさらにMへ写してM^pを添加した体が、EのMへの像⊔M^pになることを証明する。
実際の族では `pBasisExtendedFractionSubfield_tower` として公開した。
作用の合成は指定された `IsScalarTower` の代数写像の等式で確認する。

次は一般有限拡大の分離的・純非分離的な分解と帰納、各段階の次元等号を同じ共有限底体へ揃える接続。
分離的有限拡大と次数pの添加の二つの段階で族の交わりを保存できることと、
一般有限拡大での階数安定化全体の完成は区別する。
κ_e上の完備微分との比較、係数変更・分離的選択も残り、引用2は未解消。

検証：対象ビルド2549 jobs、全体 `lake build` 4218 jobsが成功。
局所代数監査745宣言の `assert_no_sorry` が成功し、今回追加した10宣言の公理は
`propext`・`Classical.choice`・`Quot.sound` のみ。
恒等拡大でのp乗部分体の生成性、空の変数集合での実際の族の交わり、恒等な二段の塔、
全射性を要求しない任意の体準同型でのp乗部分体の包含の4境界例と、再適用・塔の2公開API確認も成功。
今回の新規・変更モジュールと境界例に新しい警告はない。
文書検証は16 Markdownファイル・295 exposition参照で不整合0件、`git diff --check` も成功。
主定理監査では外部引用8件・保留K理論2件を再確認し、引用2の未証明状態を維持した。

### 2026-10-14：一般有限拡大後の族の交わり

`PurelyInseparablePrimeStep.lean` は、純非分離拡大の底体の外の元xについて、
x^(p^n)が底体へ入る最小のnを選ぶ。n>0を確認し、y=x^(p^(n−1))を非自明なp乗根として得る。
この抽出は拡大の有限性を使わず、底体の標数は終域から単射な代数写像で供給する。
有限拡大では既存の最小多項式の計算から[K(y):K]=pを確認し、次数の乗法性とp>1から
[L:K(y)]<[L:K]を証明する。帰納の停止を未証明の構造体のフィールドとして渡さない。

`SubfieldFamilyTower.lean` は、共有限性・下向き有向性を拡大後の族へ移し、
既に交わりを確認した段階の後の次数p／分離的有限拡大での交わりを、合成した拡大での族へ同定する。
ここで先の交わりは帰納仮定であり、次の段階の交わりは既存の定理で証明する。
`PowerSubfieldMap.lean` に全射な体準同型でのp乗部分体の像の等号を追加し、
自明な拡大での交わりの計算を帰納の基底として供給する。

`FiniteExtensionPowerSubfieldIntersection.lean` の純非分離な場合の帰納は、残りの拡大次数に関する強い帰納。
非自明なp乗根yについてT=K(y)を実際に構成し、Mathlibの冪基底で添加元がTを生成する条件を供給する。
元の族E_iをG_i=E_iのTへの像⊔T^pへ移し、次数pの一段で交わりT^pを証明する。
G_iの共有限性と有向性を確認した上で、より小さい[L:T]に帰納仮定を適用する。
二段で構成した族と合成した拡大での族の一致を使い、⋂_i(E_iのLへの像⊔L^p)=L^pを得る。

帰納の内部では底体と終域を同じ宇宙で扱うが、公開定理にはその制約を出さない。
任意の始域Kを終域L内の底中間体へ移し、Kからそこへの全射で族・p乗部分体・有限性・交わりを移して適用する。
一般の有限拡大ではT=separableClosure K Lを使い、Mathlibが供給するT/Kの分離性とL/Tの純非分離性を適用する。
分離的段階と純非分離的段階を接続して `iInf_subfield_sup_pPower_of_finite` を証明した。
有限p-rank・局所性・Noether性は要求しない。族の添字は非空で、各E_iはK内の共有限部分体であり、族は下向きに有向である。

実際の族への適用は `IsPBasis.iInf_extendedFractionSubfield_of_finite`。
元のp-basisから共有限性・有向性・p乗部分体の包含・交わりを供給し、L/K₀の有限性だけを追加して適用する。
その結果と既存の共有限性から、任意の有限拡大の後の次の次数pの階数安定へも再適用できる。

一般有限拡大後の族の交わりの保存は完了したが、階数安定化全体の数値等号は未完了。
次は各段階の次元比較を、元のK内の同じ共有限底体へ係数作用を保って移し、合成する帰納へ進む。
κ_e上の完備微分との比較、係数変更・最終的な分離的選択も残る。引用2は未解消。

検証：対象ビルド2552 jobs、全体 `lake build` 4226 jobsが成功。
局所代数監査758宣言の `assert_no_sorry` が成功し、今回追加した13公開宣言の公理は
`propext`・`Classical.choice`・`Quot.sound` のみ。内部の強い帰納の補題への依存も含めて監査した。
拡大次数pで抽出後の残りの次数が1になること、恒等写像でのp乗部分体の像、
Unitを添字にした自明な拡大の帰納の基底、空の変数集合での実際の族への適用の4境界例と、
宇宙を制限しない一般定理・次の次数pの段階への再適用の2公開API確認も成功。
今回の新規・変更モジュールと境界例に新しい警告はない。
文書検証は18 Markdownファイル・295 exposition参照で不整合0件、`git diff --check` も成功。
主定理監査では外部引用8件・保留K理論2件を再確認した。引用2は引き続きその8件に含まれる。

### 2026-10-14：一般有限拡大での通常微分の階数安定

前回完成した族の交わりの保存から、通常微分の次元等号の帰納も完成した。
`exists_subfieldFamily_kaehlerDifferential_ne_zero` はp乗でない指定元を検出する指標を、
族の交わりと有限指数1の相対零判定から供給する。
`exists_subfieldFamily_primeRoot_rank_stable_of_range` はR→Kの像がその部分体へ入るなら、
Rからその部分体への実際の代数写像を構成し、係数制限で微分の非零性を移して次数pの等号を得る。
旧 `exists_subfieldFamily_primeRoot_rank_stable` はこの共通定理の部分体への適用へ整理し、公開型を保った。

`FiniteExtensionDifferentialRank.lean` は、通常微分を同じ底体R上で比較する。
純非分離な場合には次数pの添加K→Tと残りT→Lを取り、二つの指標i・jより小さいE_kを有向性から選ぶ。
R→Kの像がE_kへ入るなら、一段目の次数pの等号と、二段目の帰納の等号の両方を確認できる。
R→TをR→K→Tの合成で取り、R→K→T・R→T→Lのスカラー塔とR上のTの有限性を確認する。
Rを別の部分体の型へ取り替えず、finrank_L Ω_{L/R}=finrank_T Ω_{T/R}=finrank_K Ω_{K/R}を合成する。
帰納の停止とT^pを交わりとする族の条件には、前回完成した次数減少・交わり・共有限性の定理を使う。

始域と終域が異なる宇宙の場合は、終域内の底中間体へ移して同じ帰納を適用する。
その底中間体と元のKの間の等号は、全射な代数写像の分離性から既存の分離的な微分比較で確認する。
一般有限拡大では分離閉包までの分離的段階と、その上の純非分離的な帰納を同じRで接続する。
公開定理 `exists_subfieldFamily_rank_stable_of_finite` は任意の指定された底体の作用を対象とする。
`exists_subfieldFamily_rank_stable` は部分体版を供給する。
有限p-rank・Noether性・局所性は要求せず、族の共有限性・有向性・p乗部分体の包含・交わりとL/Kの有限性を使う。
各R上のK・T・Lの有限性から通常微分の有限性を供給し、無限次元を0とするfinrankの規約に依存しない。

`CofiniteFractionDifferentialRank.lean` は、p-basisから構成した実際のF_eの四条件を確認して適用する。
あるeを選び、F_e以下の任意の共有限なR、特にe⊆fとなる全てのF_fについて、有限拡大前後の次元等号を供給する。
fでの共有限性は既存の基底の定理から、包含は反単調性から確認する。
係数制限のAlgebra・Module・SMulは同じ指定済みのK₀→Lの合成から明示する。

`primeRoot_adjoin_gen_properties` は、非自明なp乗根を添加した中間体の標準生成元について、
同じ関係式・非所属・生成条件を一つの証明で供給する。
族の交わりの帰納と今回の微分の帰納で共通化し、Mathlibの冪基底をそのまま使う。
この補題自体は標数の仮定を必要としない。

通常の体の階数安定化の一般定理と実際の族への適用は完了した。
G4全体の次元h+|e|、κ_e上の完備微分との比較、係数変更と最終的な分離的選択は未完了。
次は完備微分から分数体上の通常微分への比較と、具体的な基底の次元計算へ接続する。
引用2はまだ置換していない。

検証：対象ビルド2624 jobs、全体 `lake build` 4237 jobsが成功。
局所代数監査766宣言の `assert_no_sorry` が成功し、今回追加した8公開宣言の公理は
`propext`・`Classical.choice`・`Quot.sound` のみ。内部の強い帰納も依存関係を含めて監査した。
有限性を確認して零の次元から実際の分離性へ戻す確認、標数を要求しない添加元の生成条件、
零元を非零微分で検出できない境界の3例と、空の変数集合での二つの実際の適用・
純非分離な一般APIの3確認が成功。今回の新規・変更モジュールと境界例に新しい警告はない。
文書検証は18 Markdownファイル・298 exposition参照で不整合0件、`git diff --check` も成功。
最終の主定理監査では、並行作業の初等的パラメータKoszul評価により一般Roberts引用への依存が外れており、
外部引用7件・保留K理論2件となった。一般Roberts定理自体の `sorry` は残る。
今回のCohen–Gabber作業は引用境界を変更せず、引用2の未証明状態を維持した。

### 2026-10-14：κ_e上の完備微分と同じp乗評価の分数体微分の比較

`PowerSeriesPowersCompletedDifferential.lean` はA=k[[X]]→S、X_i↦z_i^p、
Iが変数イデアルの像である場合に、完備した係数制限の核が零であることを証明する。
既存の `ker_powerSeriesCompletedDifferentialRestriction_eq_span` で核を変数の像の微分が張る部分加群へ直し、
`derivation_pow_char_eq_zero` で各生成元を消す。
既存の係数制限の全射性と合わせて、AdicCompletion I Ω_{S/k}≃Ω_{S/A}を構成した。
通常のΩ_{S/k}の有限性や、単射でない完備化の像を同一視する仮定は置かない。
この一般層は係数環kを体に限定せず、pの素数性も要求しない。
有限変数、SのNoether性・局所性・I進完備性、S/Aのessentially finite type、閉ファイバーのessentially finite typeを使う。

`PowerSeriesPowersFractionDifferential.lean` はその同型をLへ係数拡大し、
既存の `fractionDifferentialEquiv` と合成してL⊗_S AdicCompletion I Ω_{S/k}≃Ω_{L/Q}を供給する。
Q・LはA・Sの指定された分数体で、同じ評価の二つのスカラー塔を要求する。
l⊗完備化(ds)はl·d(algebraMap S L s)へ移ることを証明し、数値の等号だけで同じ写像と扱わない。

`CofiniteCompletedDifferentialComparison.lean` はκ_eと同じ有限評価κ_e[[X]]→Dへ適用する。
I=(z_i^p)の根基を元のパラメータイデアルの根基から極大イデアルへ同定し、DのI進完備性を供給する。
κの共通剰余体とp-basisからD/Iのκ_e上の有限性を確認し、閉ファイバーの条件を供給する。
κ_eの剰余体への全射性・通常の絶対微分の有限性・有限p-rankは要求しない。
Dの標数は元の係数体から単射な代数写像で移すため、実現層に追加の標数入力を置かない。
同じ評価のFrac(κ_e[[X]])→Frac(D)について、通常微分との自然な線形同型と、両側の有限性・次元等号を供給する。

極大イデアル進の完備微分へも接続した。
`AdicCompletionChangeIdeal.lean` は二つの完備化が相手のイデアルについても完備なら、
元の加群の像を保つ自然な同型を構成する共通APIである。
写像の延長はMathlibの完備化の関手性と `ofLinearEquiv`、互いに逆であることは既存の完備化の外延性を使う。
この共通APIは元の加群の有限性、Noether性、二つのイデアルの根基の一致は要求しない。
実現層ではI進・極大イデアル進の完備微分をそれぞれ有限D加群と確認し、
Dの両方の完備性から交差する完備性を供給する。
この確認を経て、極大イデアル進のκ_e上の完備微分も同じΩ_{L/Q}へ同定し、普遍微分との両立と次元等号を証明する。

次はQのK₀への像を実際のF_eと揃え、前回の階数安定を同じ代数作用に適用する接続。
Ω_{K₀/F_e}の具体的な基底・次元h+|e|の計算、係数変更・最終的な分離的選択も残る。
G4全体と引用2の一般形はまだ未完了。

検証：対象ビルド2824 jobs、全体 `lake build` 4249 jobsが成功。
局所代数監査789宣言の `assert_no_sorry` が成功し、今回追加した23公開宣言の公理は
`propext`・`Classical.choice`・`Quot.sound` のみ。
同じイデアルへの比較が完備化全体で恒等写像となること、空の変数集合でp=0・標数0でも一般比較を使えること、
異なるイデアルの比較で零元の像が零となることの3境界例と、極大イデアル進の比較・通常微分の有限性・次元等号の
3公開API確認も成功。元の加群の有限性や、一般比較のpの素数性を境界例に追加していない。
今回の新規モジュールと境界例に警告はない。
文書検証は19 Markdownファイル・304 exposition参照で不整合0件、`git diff --check` も成功。
主定理監査では外部引用7件・保留K理論2件を再確認した。引用2は未解消のままである。

### 2026-10-14：同じ有限正規化で完備微分と階数安定を接続

`IsPBasis.exists_cofiniteFractionField_rank_stable` は、Q_f=Frac(κ_f[[X]])を底体とし、
X_i↦T_i^pに沿うQ_f→K₀の像が実際のF_fとなることを確認して、一般階数安定定理を適用する。
Q_f上のK₀の有限性は既存の相対単項式基底から供給する。
部分体の型への置換による微分の同一視は使わず、同じQ_f上で通常微分を比較する。

`CofiniteNormalizationDifferentialRank.lean` の
`IsPBasis.exists_cofiniteNormalization_completed_rank_stable` は通常有限単射F:κ[[T]]→Dを固定し、
Q_f→K₀→Lの合成を底体作用として、前回の極大イデアル進の完備微分の比較へ接続する。
十分大きいfに対し、L⊗_D 完備Ω_{D/κ_f}とΩ_{K₀/Q_f}の次元が等しい。
有限性はFと冪級数展開の有限性を合成して供給し、係数写像の保存からκ_f→κ_f[[X]]→Dの塔を確認する。
変数の像F(T_i)=z_iからX_i↦z_i^pを導出し、二つの局所化の塔は分数体写像の環上での一致から確認する。
DとLの標数も係数体・分数体への単射から導出する。
結論の次元等号を仮定へ追加せず、κ_fの剰余体への全射性や有限p-rankも要求しない。

次は既存のQ_f上の単項式基底からΩ_{K₀/Q_f}の微分基底を構成し、次元h+|f|を計算する。
拡大次数p^(h+|f|)だけから微分の次元を推論しない。
この計算後に係数変更・分離的パラメータの選択へ進む。G4全体と引用2は未完了。

検証：対象ビルド2873 jobs、全体 `lake build` 4252 jobsが成功。
局所代数監査791宣言の `assert_no_sorry` が成功し、新規2定理の公理は
`propext`・`Classical.choice`・`Quot.sound` のみ。新規定理のビルド警告はない。
文書検証は19 Markdownファイル・304 exposition参照で不整合0件、`git diff --check` も成功。
主定理の `#print sorries` で外部引用7件・保留K理論2件を再確認した。引用2は未解消。

### 2026-10-14：相対微分基底と完備微分の次元h+|f|

`RelativePMonomialSpan.lean` は指定された底体Fについて、各生成元b_iのp乗がFの像にあるとき、
p未満の相対単項式の線形包と生成部分代数・生成中間体の一致を証明する。
添字の有限性や、絶対p乗部分体への固定は要求しない。
部分代数との一致は標数pも不要で、指数の繰り上がりを底体の係数へ移す。
中間体との一致は各生成元の整性とMathlibの代数的な添加の比較を使う。

`RelativePBasisDifferentials.lean` は、相対単項式がF上の基底であることと各b_i^pがFの像にあることから、
b_iだけを1に送る偏導分を構成する。
一方向を除いた生成中間体上で、除いた単項式の座標が零であることを確認してb_iの非所属を示す。
一段のp乗根添加の導分を構成し、Fへ係数制限する。
その偏導分で微分の独立性を検出し、単項式基底からの代数生成性で張ることを証明する。
これにより、添字が無限でも生成元の微分の基底を得る。
微分の独立性・有限性・次元を入力へ追加した構造体は置かない。
既存の `IsPBasis.exists_partialDerivation` と `IsPBasis.linearIndependent_kaehlerDifferential` も
この一般定理への適用へ整理し、公開型を保持する。

`PExponent.sumEquiv` は直和上の有限台指数を二つへ分ける同値。MathlibのFinsuppの同値を使う。
`CofiniteFractionDifferentialBasis.lean` はQ_f=Frac(κ_f[[X]])→K₀、X_i↦T_i^pの作用を固定し、
既存の分数体基底をσ⊕fの相対p単項式で添字付け直す。
T_iと係数b_jのp乗がQ_fの像に属することは、既存のK₀^p⊆F_fから供給する。
一般定理でT_iと残したb_jの微分を基底にし、通常微分の有限性と次元h+|f|を得る。
拡大次数p^(h+|f|)だけから微分の次元を推論しない。

`IsPBasis.exists_cofiniteNormalization_completed_finrank` はこの次元式と前回の階数安定を同じ作用で合成する。
`IsPBasis.exists_completed_finrank_of_parameters` は係数写像・次元h・h個の準素パラメータから
既存の通常有限正規化を構成し、十分大きいfでV_fの次元h+|f|を供給する。
κ_fの剰余体への全射性・有限p-rank・分離的正規化の存在は要求しない。

G4/Fの階数・次元計算の主要部分は完了した。
次はKの係数体変更：β_i+m_iの独立性から新しい係数写像κ′を構成し、訂正版§2.1.11の商表示で
旧κ_fと新κ′_fの完備微分を比較する。同一の部分体・作用として扱わない。
その後、残した係数方向を消す次元減少と、Yの分離的パラメータの選択へ進む。
引用2の一般形は引き続き未解消。

検証：対象ビルド2877 jobs、全体 `lake build` 4258 jobsが成功。
局所代数監査814宣言の `assert_no_sorry` が成功し、今回追加した23宣言の公理は
`propext`・`Classical.choice`・`Quot.sound` のみ。新規・変更した基底モジュールに警告はない。
空の変数と空の係数方向で次元0、一変数で係数方向が空なら次元1、
変数が空で任意の有限係数方向fなら次元|f|となる3境界例も成功した。
一変数の例はT↦T^pの作用を恒等作用と混同しないことを確認する。
文書検証は19 Markdownファイル・304 exposition参照で不整合0件、`git diff --check` も成功。
主定理の `#print sorries` は外部引用7件・保留K理論2件のまま。引用2は未解消。

### 2026-10-14：有限係数摂動と訂正版の共通商による比較

`KaehlerRestrictionKernel.lean` は通常の推移列のMathlibの完全性から、
Ω_{S/R}→Ω_{S/A}の核をd(algebraMap A S a)のS線形包へ同定する。
独自の微分の構成や完全性の再証明はせず、基底・有限性・標数も要求しない。

`CofiniteCoefficientRestriction.lean` は係数写像φ:κ→Sを明示し、
Ω_{S/κ_f}をΩ_{S/ℤ}の共通商として表示する。
κ_fの既存の係数単項式基底から代数生成性を確認し、
p乗部分体上への導分の制限と、生成元上の値が全ての値を張る一般定理を使って、
核をfの外のdφ(β_i)の線形包へ同定する。Sの標数pを追加で仮定する必要もない。

φとψがfの外のp-basis元で一致すれば、二つの係数制限の核は一致する。
同じ絶対微分の商を経由する線形同型を構成し、全ての絶対普遍微分の像との両立を証明した。
κ_fの元の像全体やp乗部分体の像全体の一致は仮定しない。
`cofiniteCoefficientDifferential` はφによる作用を型に保持する表記であり、未証明入力を束ねる構造体ではない。
別のκ作用が文脈にある場合にも、S上の加群作用を指定したφで供給する。

完備化はMathlibの `AdicCompletion.congr`、同じS上の係数拡大はテンソル積の同型を使う。
元の通常微分や絶対微分の有限性、完備化と商の交換は仮定しない。
生成点での有限性も同型に沿って移すため、finrankの等号だけで数学的な有限性を代用しない。
`IsPBasis.exists_completed_finrank_of_parameters_coefficientChange` は前回の次元h+|f|をψ側へ移す。
既存のAlgebraと環準同型から作り直したAlgebraの等号に沿って、次元を明示的に移送する。

`PBasisCoefficientPerturbation.lean` は核について完備な全射f:S→κの切断φと
有限集合e上のμ:e→ker(f)から、新しい切断ψを構成する。
指定p-basisの完全な持ち上げの存在定理へ、有限集合内ではφ(β_i)+μ_i、外ではφ(β_i)を指定して適用する。
剰余体の場合は既存の完備性・剰余写像で適用できる。Noether性・有限p-rankは要求しない。

K/G5全体は未完了。次はL1でV_f内の微分が独立になるμを選び、
この切断構成へ渡す。さらに新しい係数体の残したf方向を消す核・次元減少を計算し、
V′の次元hへ進む。引用2の一般形とY/Nの分離的正規化は未完了。

検証：対象ビルド2880 jobs、全体 `lake build` 4263 jobsが成功。
局所代数監査833宣言の `assert_no_sorry` が成功し、今回追加した19宣言の公理は
標準の `propext`・`Classical.choice`・`Quot.sound` の範囲内。新規・変更モジュールに警告はない。
自己比較が通常微分の全体で恒等、完備化全体でも恒等、空の有限摂動集合でも切断を構成できる
3境界例が成功。通常微分の有限性やNoether性は境界例にも要求していない。
文書検証は19 Markdownファイル・304 exposition参照で不整合0件、`git diff --check` も成功。
主定理の `#print sorries` は外部引用7件・保留K理論2件のまま。引用2は未解消。

## 8. arxiv_formalizationの再利用調査（2026-10-13）

対象は同じホストの `arxiv_formalization`、HEAD `761bc6b`の作業ツリー。
`AlgebraicGeometry/VecBundle/TangentCotangentBundle`は通常の相対微分から
余接層・接束を構成する。以下の環レベルの部分を切り出して確認した。

| 候補 | 型・実証明で確認した内容 | 今回の適用先と制限 |
| --- | --- | --- |
| `Basic.lean:65,83`の `module_eq_zero_of_isLocalized_span`・`_range` | 単位イデアルを生成する族の全局所化で零なら、元も零。有限性・Noether性は不要 | 局所性の共通補題。分数体で零という条件だけから大域的な零を推論するものではない |
| `Basic.lean:170,249`の局所化を越える導分の零化 | 係数から来る元の逆数・局所化像を相対導分が消す。写像の両立を明示 | Mの係数作用・局所化の確認。現在はCommRingCat/ModuleCatの型なので、必要なら一般Derivationの共通入口へ移す |
| `PresheafLocality.lean:58`のbasic-open局所化 | 実証明はMathlibの `KaehlerDifferential.isLocalizedModule_map`を適用 | M3はMathlib `Etale/Kaehler`を直接利用する。スキーム層のimportを共通微分層へ持ち込まない |
| Mathlib `tensorKaehlerEquivOfFormallyEtale`・`span_range_map_derivation_of_isLocalization` | テンソルによる局所化同型と、局所化後も元の微分の像が生成すること | M3とL2の生成性の接続に利用。通常のΩの結果を完備微分へ無根拠に読み替えない |
| `LocallyFree.lean:49`の `kaehlerFreeIsoOfStandardSmooth` | standard smoothと相対次元nから、Ωを有限自由加群へ明示的に同定 | rank・基底・ModuleCat同型の構成例。Cohen–Gabberの分離性を得る前に滑らかさを仮定して使わない |

検証：上記Basicの4宣言と有限自由同型の1宣言を、数学的仮定・証明を変えずに
現在のSerrePositivityのMathlib環境へ抽出し、コンパイルと `assert_no_sorry` を確認した。
5宣言とMathlibの上記3宣言は `propext`・`Classical.choice`・`Quot.sound` のみ。
局所化の `IsLocalizedModule.Away` と、非零因子全体による分数体への局所化の型を
それぞれ `#synth` で確認した。

原repoはLean4.32、こちらは4.35.0-rc4。元repoの `.lake` の参照先が欠けており、
targeted buildは依存パッケージを開けず失敗した。元repo全体の現在の依存監査を成功扱いしない。
Basic全体の無変更移植も前層部分のAPI差で失敗したため、検証範囲は上記の環レベルの抽出部分。
元repoのソースは編集していない。連続微分・完備微分・p-basisの核心を供給する宣言は
今回の探索範囲では未確認であり、G0/G2/G3aの証明課題を解消したとは扱わない。

採用：M3の局所化と生成性は既存Mathlibを直接利用し、上記小補題は必要な型だけ共通化する。
余接層・準連接性・接束の大きなフレームワークは将来の幾何的利用先として参照する。
今回の調査ではLeanソースへの新規移植・証明の追加は行わず、台帳のみ更新した。

## 9. コード確認後の詳細実装計画（2026-10-14）

以下は2026-10-14の現行コードを確認した実装計画である。新しい宣言名は候補であり、
この節の追加によってLean定理が証明されたことにはしない。
基盤の保存コミットは `1a7a717`。引用2の公開入口は引き続き `sorry` のままである。

### 9.1 確認範囲と、実装済みAPIの使い分け

確認の中心は、独立摂動、非零イデアルの微分生成、有限係数摂動、共通商比較、
完備微分の次元式、完備化の核、冪級数の推移列、分数体の分離性判定。
全新規証明の数学的な逐行レビューではなく、残工程へ接続する公開型・証明経路と依存の確認である。

| 実装済みAPI | 次工程で使う内容 | 追加で供給する内容 |
| --- | --- | --- |
| `exists_linearIndependent_derivation_perturbation` | 非零イデアル内の元そのものを選ぶ | 対象導分、像の生成性、有限次元性、イデアルの非零性 |
| `IsPBasis.moduleFinite_completedKaehler_cofiniteField` | κ_f上の完備微分の有限性 | I=m_D、同じ係数作用、分数体へのテンソルの有限性 |
| `IsPBasis.exists_completed_finrank_of_parameters` | 十分大きいfで次元h+|f| | 選んだfを以降の全構成で固定 |
| `IsPBasis.exists_section_of_finitePerturbation` | 有限摂動から新しい切断ψを構成 | μを微分独立性から実際に選ぶ |
| `IsPBasis.cofiniteCoefficientBaseChangeCompletedDifferentialEquiv_tmul_of` | 比較が普遍微分の像を保つ | 独立な微分の族の移送 |
| `adicCompletion_map_exact_of_finite_completion` | 通常中項が非有限でも完備化後の完全性 | 係数拡大の通常推移列と完備中項の有限性 |
| `ker_powerSeriesCompletedDifferentialRestriction_eq_span` | 冪級数の相対微分の核 | 新評価のパラメータイデアル、閉ファイバー、完備性 |
| `isSeparable_fractionRing_iff_finrank_completedRelativeDifferential_eq_zero` | 生成点での完備相対微分の消滅から分離性 | 同じFからの代数作用と二つの分数体の塔 |

`DerivationIdealSpan.lean` は既に環の元の選択を結論としているため、一般線形代数の再実装は不要。
一方、`CompletedDifferentialTransitivity.lean` の入口は `Algebra.EssFiniteType R S` を要求する。
κ_f→κ→DにR=κ、S=Dとして直接適用するのは不可：Dは一般にκ上のessentially finite typeではない。
この適用条件を、未証明のインスタンスや新しい最終仮定で埋めない。

今回の確認では、全体 `lake build` 4277 jobs、
`lake env lean scripts/audit_local_algebra.lean`（833件の `assert_no_sorry`）が成功した。
全体ビルドは同時進行中の他領域を含む作業ツリーについての結果。
Cohen–Gabberの新規基盤には `sorry`・`axiom`・`native_decide` の追加を検出していない。
既存の公開引用を含む全体の証明完成を意味しない。

### 9.2 A：完備普遍微分の生成性（最初の実装単位）

配置候補：`CompletedDifferentialGeneration.lean`。
I=m_D、E=κ_f、C=AdicCompletion I Ω_{D/E}、L=Frac(D)、V=L⊗_D Cを固定する。
通常の普遍導分からC、続いてVへのD線形写像との合成でδ:D→Vを構成する。
`Derivation` の底環Eと、VのD・L作用のスカラー塔を明示する。

目標は、Cが有限D加群なら通常微分の像がCをD上で生成し、
従ってδの像がVをL上で生成する、という一般定理。
通常Ω自体の有限性や `AdicCompletion.of` の全射性は仮定しない。
証明案は、通常微分がΩを張ることと完備化の冪商での代表元から、
その像の線形包がCで稠密であることを示す。
Cの有限性とI⊆Jac(D)から商のHausdorff性・線形包の閉性を得て閉包を除く。
既存の `AdicModuleSeparation.lean` とMathlibの冪商・完備化APIを使う。
テンソル積の生成元の表示から、Vでの生成性を移す。

受入条件：有限性は `Module.Finite` として供給し、finrankの数値だけで代用しない。
零加群・空の係数方向も扱い、一般定理へ整域性や体の無限性を加えない。

### 9.3 B：独立な係数摂動の選択と新しい切断

配置候補：`PBasisIndependentCoefficientPerturbation.lean`。
通常有限正規化のτと係数切断φを固定し、既存の次元定理から有限集合eを選ぶ。
f=e（必要なら以後の用途に応じて拡大）として固定し、AからV_fの生成性と有限性を得る。

δ(φ(β_i))、i∈fを `Fin f.card` へ添字付け直し、
`f.card ≤ h + f.card` と `exists_linearIndependent_derivation_perturbation` により
μ_i∈m_Dを選ぶ。μを `f → RingHom.ker (residue D)` へ移し、
`exists_section_of_finitePerturbation` を適用する。
結論は切断ψ、補集合でのφとの一致、ψ(β_i)=φ(β_i)+μ_iとその微分の独立性。
共通商比較の `tmul_of` 補題で、独立性をψ側のV_fへ移す。

非零イデアルの条件は明示する。m_D=⊥の場合はDが体となる分岐を先に扱い、
剰余写像の切断が同型であることから空変数の正規化を構成する。
h=0の処理を、m_D≠⊥を要求する一般補題への無理な適用にしない。

受入条件：独立性を結論と同じ形で入力へ要求しない。
有限体・無限p-basisを許し、μの選択に体の無限性を使わない。

### 9.4 C：有限係数方向を消す核と次元減少（G5の主要残工程）

配置候補：`FiniteCoefficientCompletedDifferential.lean` と
`CohenGabberCoefficientField.lean`。一般層とGabberへの適用を分ける。
ψ作用でE=κ_f→κ→Dを固定し、通常の係数制限Ω_{D/E}→Ω_{D/κ}を完備化する。
目標は、この写像の全射性と、核がf内のdψ(β_i)のD線形包であること。

通常推移列の左項はD⊗_κ Ω_{κ/E}。
既存の相対単項式基底と `kaehlerBasisOfPMonomialBasis` から、
Ω_{κ/E}の基底をf内のdβ_iとし、左項を有限自由D加群へ同定する。
Dのm_D進完備性から左項自身の完備性を供給する。
`adicCompletion_map_exact_of_finite_completion` を通常推移列へ直接適用し、
左項の基底の像から核を計算する。完備化した係数制限の全射性もMathlibの
全射の完備化APIで別途供給し、完全性だけから暗黙に結論しない。
`CompletedDifferentialTransitivity` のEssFiniteType仮定をこの係数体の場面へ持ち込まない。

局所化LはD上平坦なので、テンソル後も完全性を保ち、核を同じf個の微分のL線形包へ移す。
Bの独立性から核の次元が|f|、全射の次元式からV_ψの次元がhとなる。
V_ψの有限性は、有限中項からの全射または共通剰余体の有限性定理で供給する。

受入条件：通常絶対微分の有限性、完備化と任意商の交換を仮定しない。
f=∅では核0と次元hを得る。比較同型の生成元上の値も監査する。

### 9.5 D：微分基底を持つパラメータ系（G6前半）

配置候補：`DifferentialParameterSelection.lean`。
Aの生成性を新係数体上のV_ψへ適用する。
`span_derivation_ideal_eq_top` によりm_D内の微分が張ることを得て、
有限次元空間の基底選択からf_i∈m_D、i:Fin hを選ぶ。
選んだ元の微分が基底であることを、添字同値と実際の値を含めて証明する。

τは既存の通常有限単射F₀から選ぶ。
F₀(X_i)=τ_iとX_i≠0、F₀の単射性を用いればτ_i≠0を供給できるため、
一般のパラメータ系の各成分の非零性を新規に大きな次元論で証明する必要はない。
y_i=τ_i^p(1+f_i)と置き、局所環で1+f_iが単元であることを示す。
単元倍と正の冪による生成イデアルの根基保存からyがパラメータ系であることを証明する。
Leibniz則と `derivation_pow_char_eq_zero` からδ(y_i)=τ_i^p·δ(f_i)を得る。
L内のτ_i^pの非零性から、各基底ベクトルの可逆スカラー倍による基底の移送を行う。

受入条件：根基保存と微分基底の２つを独立に検証する。
h=0は空族、h=1は一元族として扱い、τ_iの非零性を暗黙にしない。

### 9.6 E：同じ評価の相対微分消滅と分離性（G6後半）

配置候補：`CohenGabberNormalization.lean`。
ψとyから `exists_injective_finite_powerSeries_map_of_parameters` で
F:κ[[X]]→Dを構成し、係数・変数の値、有限性、単射性、剰余体への全射性を固定する。
J=(y_i)とm_D進の２つの完備微分の比較は既存の
`AdicCompletionChangeIdeal` と有限性・相互の完備性の確認を使う。
微分基底が元の普遍微分の像であることを、この比較でも保存する。

J進の `ker_powerSeriesCompletedDifferentialRestriction_eq_span` を同じFへ適用する。
相対微分への全射と核の計算をLへテンソルし、Dで得たdy_iの基底によって
L⊗_D 完備Ω_{D/κ[[X]]}が零であることを示す。
分離性判定は同じFから構成したFrac(κ[[X]])→Frac(D)へ適用する。
`fractionRingMap` と既存の分数体接続で、環上の作用・分数体上の作用・スカラー塔の両立を確認する。

最後にA=κ[[X]]、t=X、標準環同型を選び、既存の正則性・完備性・極大イデアル生成を付ける。
共通層の定理を証明した後で `Inputs.cohen_gabber_normalization` の型を保持して置換する。
一般の被約環版や混標数の一般Cohen環の構成は、この整域版の工程へ追加しない。

### 9.7 実装と検証の順序

```text
A 完備微分の生成性 ─ B 独立摂動・切断 ─ C 係数制限の核・次元h
                                         └─ D 微分パラメータ ─ E 分離性・Inputs
```

最初の変更はAの一般定理とそのκ_fへの適用だけに絞る。
B、C、D、Eを各々レビュー可能なコミットにし、各段階で対象ビルドと
新規公開宣言の `assert_no_sorry`、元・普遍微分上の写像の両立を確認する。
一般p-basisの逆方向の特徴付けは、この経路が要求しない限り先行実装しない。

境界例はh=0、h=1、f=∅、有限体、無限p-basis。
特にT↦T^pによる通常有限正規化について、分離性が未供給の段階では
分離的正規化の存在を結論しないことを型・依存監査で確認する。
最終受入は全体 `lake build`、局所代数監査、主定理の `#print sorries` と
`#print axioms`、文書検査、`git diff --check`。
引用2が依存から消えたことを宣言名で確認し、他の作業による引用件数の増減と区別する。

この計画はコードの接続条件に基づくもので、追加のLean型照合は各単位の着手時に行う。
特にAの生成性、Cのテンソル後の核、Eのイデアル比較は実証明が必要な接続であり、
既存API名があることだけで完成扱いしない。完了日は設定しない。

### 9.8 Aの実装：完備微分の生成性（2026-10-14）

`CompletedDifferentialGeneration.lean` は、有限な完備化が元の加群の像で張られることを証明した。
像の線形包による商はNoether環上の有限加群なので、I⊆Jac(D)から分離性を得る。
商写像と零写像を元の加群上で比較し、既存の完備化の外延性から商写像が零と結論する。
位相の閉包を新たに構成せず、同じ近似・分離性を実装済みAPIへ集約した。
普遍導分の完備化・係数拡大を定義し、双方でその像の生成性を証明した。
`CofiniteCompletedDifferentialGeneration.lean` は共通剰余体からκ_f上の完備微分の有限性を供給し、
Frac(D)への係数拡大の有限性と生成性を得る。通常Ωの有限性・有限p-rankは不要。
適用層の2定理は整域性を要求しない一般性まで保ち、後続でFrac(D)を体として使う際に整域性を供給する。
対象ビルド2739 jobsと局所代数監査842宣言が成功。新規9宣言は標準公理のみ。
次はBでこの導分へ既存の独立摂動選択を適用する。引用2は未解消。

### 9.9 Bの実装：独立な係数方向を持つ切断（2026-10-14）

`exists_linearIndependent_derivation_perturbation_fintype` は既存のFin添字の選択を任意有限添字へ移す。
`PBasisIndependentCoefficientPerturbation.lean` は極大イデアルが非零の整域について、
次元h+|e|とAの生成性から、e内の係数の微分を独立にするμ_i∈m_Dを実際に選ぶ。
`IsPBasis.exists_independent_coefficient_section` はこれを剰余写像の指定持ち上げへ渡し、
新しい切断ψを構成する。共通商比較は絶対導分の像を保存することを別補題で確認し、
ψ側での独立性と、同じeでの生成点の次元h+|e|まで結論する。
微分独立性を入力へ要求しない。m_D=⊥の場合は最終入口の体の分岐へ残す。
対象ビルド2886 jobsと局所代数監査848宣言が成功。新規6宣言は標準公理のみ。
次はCで完備係数制限の核を計算し、この独立性から次元hを導く。引用2は未解消。

### 9.10 Cの実装：係数方向の核と次元h（2026-10-14）

`FiniteCoefficientCompletedDifferential.lean` は全射の完備化の全射性と、
通常の核の生成族を完備化した核へ移す一般定理を実装した。
完備中項の有限性から商の分離性・像の閉性を得て、既存の核の閉包定理から閉包を除く。
この証明は生成族自体の有限性や終域のessentially finite typeを要求しない。
κ_e→κ→Dの通常の核は、κがe内のp-basis元でκ_e上生成されることから計算した。
平坦な係数拡大で同じ生成族の像へ核を移す一般定理も実装した。

`CohenGabberCoefficientField.lean` はFrac(D)で核の次元を独立なe個の微分から|e|と計算し、
全射の次元式でh+|e|からhへ減らす。
`IsPBasis.exists_coefficient_section_completed_finrank` はBの実際の切断へ適用し、
環の次元hと等しい完備微分の生成点の次元を持つ係数切断を構成する。
対象ビルド2889 jobsと局所代数監査855宣言が成功。新規7宣言は標準公理のみ。
次はDの微分パラメータの選択。極大イデアルが零の体の分岐と引用2の最終置換は残る。

### 9.11 Dの実装：微分基底を持つパラメータ（2026-10-14）

`DifferentialParameterSelection.lean` は非零極大イデアル内から微分基底を選び、
y_i=τ_i^p(1+f_i)について単元倍・正の冪による根基保存を証明した。
導分のp乗消滅とLeibniz則を使い、dy_i=τ_i^p df_iを計算する。
Frac(D)内でτ_i^pが可逆なので、実際の基底の可逆スカラー倍としてdy_iの基底を構成した。

`CohenGabberDifferentialParameters.lean` は通常有限単射の変数の像τ_iが非零であることを確認し、
Cの係数切断変更へ接続した。非零極大イデアルの完備局所整域について、
係数切断ψ、準素パラメータy、極大イデアル進の完備微分の生成点の実際の基底を同時に供給する。
対象ビルド2891 jobsと局所代数監査861宣言が成功。新規6宣言は標準公理のみ。
次は同じ評価Fの分離性と公開入口への接続。引用2は未解消。

### 9.12 Eの実装と最終監査（2026-10-14）

`CohenGabberNormalization.lean` の
`isSeparable_powerSeries_fractionMap_of_completed_differential_span` は、同じ有限評価Fに沿う
極大イデアル進の係数制限をFrac(D)へ拡大する。
パラメータの微分はその写像で零となり、元の完備微分を張るので写像全体が零。
係数制限の全射性から通常相対微分の局所化が零となり、同じFの分数体写像について分離性を得る。
既存の `completedDifferentialRestriction` が極大イデアル進で直接使えるため、
§9.6で予定したパラメータイデアル進への比較は最終工程では不要となった。
相対微分の有限性・完備性はFの有限性から供給し、通常絶対微分の有限性は要求しない。

`exists_coefficient_section_differential_span` は極大イデアルが零の分岐を含む。
この場合は剰余写像が単射なので係数切断が全射となり、係数体上の通常微分が零。
冪商による完備化も零となることを確認して、次元0の正規化へ接続した。
非零極大イデアルの場合はDの実際の微分基底を用いる。
`exists_cohen_gabber_powerSeries_map` は単射性・有限性・剰余体への全射性・分離性を同じFに供給する。
`exists_cohen_gabber_normalization` は標準冪級数基底の正則性・完備性・座標を付ける。
`Inputs.cohen_gabber_normalization` は既存の公開型を変更せず、その証明への適用へ置換した。

検証：対象ビルド3374 jobsと全体 `lake build` 4285 jobsが成功。
共有作業の更新後に全体ビルド4291 jobsも再確認した。
局所代数監査866宣言の `assert_no_sorry` が成功。
新規4定理・公開入口・`Section2.lemma_2_2` は `propext`・`Classical.choice`・`Quot.sound` のみ。
`audit_cohen_gabber.lean` の4境界例も標準公理のみ：有限体F₂でh=0、F₂[[T]]でh=1、
有限性を仮定しない添字のp-basisでe=∅の核0、正の微分次元でp乗の微分だけでは張らないこと。
公開定理の元の型との照合は一致。文書検査は20 Markdown・306解説参照で不整合0件。
差分検査も成功し、解説PDFの変更箇所を再生成・描画確認した。

主定理の `#print sorries` からCohen–Gabberが消えたことを確認した。
残るのは外部引用5件（交点消滅、BS存在・全射、CLMST almost消滅・isogeny）と保留K理論2件。
主定理全体の `sorryAx` はこれらに由来し、Cohen–Gabberを未証明入力として再導入していない。
この整域版の計画G5・G6と§9のA〜Eは完了。一般被約環版やp-basisの一般逆方向は別の拡張。
