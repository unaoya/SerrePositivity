# BS-D69 段 0 報告（停止点 0）

2026-11-10。⑤b、`math/bs-d68`。指示書を含む main `c1f41aeb3` を fast-forward し、報告時点の main `fc86737de` も取り込んだ。本体、A1 の草稿、a1-design §10.4–§11、⑤c の K1 の枝を静的に照合した。以下は紙上の実装案。行数は証明・補助宣言・docstring を含む概算。

## P1 — 基底の分冪と両立する包と枠

| 対象 | 再利用できる宣言 | 新規に証明すること |
| --- | --- | --- |
| `IsCompletedPDEnvelope`・`exists_completedPDEnvelope` | Mathlib の `DividedPowers.IsDPMorphism`、`DividedPowerAlgebra.lift`・`algHom_ext`、`SubDPIdeal` の商。D68 の `FreeDPBasis`・`FreeDPBaseChange`、`principalCompletionRingFunctor` と主完備化の環射の普遍性。`IsPrismaticEnvelope` は普遍性の書き方の先例 | 任意の `J.map (algebraMap k B) ≤ K` の未完備包を作る。まず多項式表示上で基底の分冪を延長し、自由分冪変数を足し、表示関係のうち pd イデアル内にあるものの分冪も課す。表示からの商には `SubDPIdeal` を使う。その後、p 冪商の逆極限で p 完備化し、閉じた pd イデアル、商 `D/K' ≃ B/K`、標準脚を含む普遍性を示す。 |
| `pdFrame`・`pdFrameEval`・`pdCechNerve`・`pdCechAugmentation` | `MvPolynomial.aeval`・`rename`、`pdRawModel` と `pdModel` の copy 添字の処理 | 包の台環・pd イデアル・分冪・標準脚・商の評価を一つのデータとして選ぶ。copy の改名と評価の可換性から lift し、恒等と合成は一意性で示す。任意の枠に対する増大は `R̄` の零 pd イデアルへの lift。 |
| `pdCechNerveMap`・`pdCechNerveMap_quasiIso` | `cechEndHomotopy`・`cechSplitCochainEquiv`（`SplitCechConerve`）、`crystallineAddSplitCech_equiv`。いずれも既存の split Čech の鎖ホモトピーの手本 | `φ : S → D_{S′}^0` を各頂点に送り、同じ評価を持つことから lift。擬同型には、二つの lift の像を一つの頂点を境に切り替える余単体ホモトピーを作る。各変数の評価は切り替えの前後で一致し、余面・余退化との恒等式は包の普遍性で確認できる。枠が両方とも全射なら逆方向の lift を選べる。合成と恒等の間にも同じホモトピーを適用する。 |
| `pdModel_iso_pdCechNerve` | `pdRawModel`、`pdRawBasis`、`pdModel`、`CrystallineRawPDSplit` の第 0 頂点と差座標の分離 | `ker(k[X^{(0..n)}] → (k/J)[X])` を基底イデアルと頂点差で表し、`k[X^{(0)}] ⊗ Γ_k(差)` に基底の分冪を入れる。完備包の普遍性を示し、copy の標準脚で自然同型を得る。大きい枠では、小さい枠の各余分な変数を、その評価の第 0 頂点での持ち上げの各 copy だけ平行移動する。残る自由 pd 変数との分離は、P2 で大きい枠の p 正則性にも使う。 |

表示独立性の上の証明は **今回の古典範囲での案**。a1-design §11.6(5) の site 経由の証明は (a)＋(d)、すなわち `crystallineCechIso` とその自然性がそろった後の照合として残す。古典版では各混合頂点写像を完備包の間の厳密な射として作れるため、鎖ホモトピー自体に逆極限の交換は要らない。§10.5.1 の積の枠と extra degeneracy の方法も使える。分冪変数を足した包の分離は、どちらの方法でも独立に証明する。分冪包の構成と変数追加は Berthelot I.2.3.1 の経路に沿う。[Stacks 60.2](https://stacks.math.columbia.edu/tag/07H7)

一般の `p ∈ J` については、完備化に使う pd 商の指数を確認した。包の分冪を `δ` とすると、`m ≥ 2, e ≥ 2` で `δ_m(p^e x) = p^((e−1)m) x^m δ_m(p)` は `p^eD` に入り、`m = 1` も保たれる。したがって一般の分冪では `e ≥ 2` の共終部分で完備化できる。`p^1D` も使う塔には `pD` の pd 安定性を別に示す。標準の p の分冪なら `v_p(p^(em)/m!) ≥ e` が使え、`p = 2` も含む。濃度は未完備包を生成元で評価し、完備包全体は可算積による上界を使う。有限段を直接作る場合はその段の未完備商の上界も使える。

**配置と規模**。一般の環論を `BhattScholze/Delta/DividedPower/{RelativePDPolynomial,RelativePDEnvelope,CompletedPDEnvelope}.lean` 付近、枠と表示独立性を `BhattScholze/Prismatic/{PDFrame,PDFrameNerve,PDFrameComparison}.lean` 付近の新規ファイルに置く。未完備包 → 完備化 → 枠の射 → 表示独立性・小さい模型の順。約 6–11 本、2,000–3,600 行。

## P2 — Poly(C) 上の厳密な zigzag

| 段 | 再利用できる宣言 | 新規に証明すること |
| --- | --- | --- |
| 0 と係数 | `deltaWittGhostRingHom` と Witt の係数・Frobenius の補題、`DeltaStructure.existsUnique_of_frobeniusLift`、`OrientedPrism.crystalline` | `psiRing`・`wZero_psi`・`psiPrism`。W の p 正則性は C の p 正則性から ghost 写像で、p 完備性は非完全な C 用に別途示す。完全体向けの Witt 完備化をそのまま適用しない。普遍向き付き prism と C の入力は K2 と接続する。 |
| 1 | `prismPolynomialCompletion`・`polyCompletion`・`polyCutoff`、`IsPrismaticEnvelope.lift`、`affineEnvelopeTerm`・`cechAlexanderAffine`・`polyCosimplicialAlgebra`・`prismSiteAlgebras` | 小さい affine 模型は有限変数。これを入力に、大きい `cechAlexander` の存在を全元を添字とする枠で組む。draft A0 の `hasEnvelopes_of_polynomial` に相当する古典的存在も必要。各 `f : Q → Q′` の完備化で `x_(q,i) ↦ x_(f̂(q),i)` とし、`bigCechAlexander` の厳密な関手則、`cechAlexanderFrame` とその古典的な比較を示す。 |
| 2 | `crystallineBridge`、`crystallineBridgeModP_isCohomologyIso`、`pdDelta_modP_frobeniusPushout`、`frobeniusTwist_cech_quasiIso_infinite` | P1 の包から `bigResidue`・`wittBigPdModel` を作る。`wittPdIdeal` の分冪と `wittBigCrystalline` の p 正則性・δ 構造を示し、`wittBigBridge` を厳密な lift として作る。有限模型の `wittSmallFrame`・`wittSmallBridge` と `wittBridge_frame_comm` を示す。比較の核は、`ψ` 底変換後の小さい橋について mod p の押し出し、無限変数の Lemma 5.4、高次 δ 座標の収縮、導来 Nakayama をつなぐこと。一般の J での押し出しは未証明。 |
| 3 | `pdRawCoefficients`・`pdRawChange`、`pdFormsCoefficientMap`・`pdTotalCoefficientMap_d`、P1 の基底を替える lift | `residuePdStructure`・`wZero_isDPMorphism`、小さい `pdPolynomialFunctor`、`wittToSmall`、`pdModelBaseChange`、`wittToSmall_frame`。W と C の小さい模型について有限変数の de Rham の span を係数変換と照合し、完備底変換した比較を擬同型にする。 |
| 4 | `pdRow`・`pdDeRhamDifferential`・`pdDeRhamDoubleComplex`・`pdWedge`、二射影、`pdDeRhamRowZeroProjection_quasiIso`、D68 の積の照合 | 多項式代入の連鎖律を `pdDeRhamCDGA`・`pdDeRhamProjection`・`pdDeRhamZeroIso` として厳密に関手化し、`formsCDGAFunctor` に接続する。D68 の `pdDeRhamColumnCollapseHomotopyEquiv` と `pdDeRhamColumnZeroIso` は `(p : k) = 0` の版。未完備の積分・内部積を完備係数へ移して一般の列の収縮と第 0 列への射影を閉じる。 |

紙上では、`W = W(C)` の `J = V W + pW` の二成分に分ける。p を反転した環で `γ_m(z) = z^m/m!` を計算し、`γ_m(Vx) = (p^(m−1)/m!) V(x^m)`（係数は p 局所整数）と `γ_m(pa) = (p^m/m!) a^m` から J に戻す。W の p 正則性により重なりで一致し、`w_0` は V 成分を零にし、p 成分で標準の分冪を保つ。大きい枠の橋では `q ↦ x_q^p mod p` の加法・乗法・係数の関係式の誤差が pd イデアルにあり、その p 乗が p で割れることを使う。δ 拡張は、入力の核に対する `φ(z) ∈ pD` と分冪の標準脚で確かめ、δ 射として envelope の普遍性を適用する。Thm 5.2 の原典はまず `I = (p)` を扱い、Thm 6.4 は `ψ` に沿う完備底変換の後で比較している。[Bhatt–Scholze 著者版、Theorems 5.2・6.4](https://people.mpim-bonn.mpg.de/scholze/prisms.pdf)

擬同型は二種類を区別する。枠の比較と P2 の段 4 は同一係数での交代余面複体または総複体の `QuasiIso`。段 2・3 は、厳密な半線形射を保ったまま、`ψ : A₀ → W` と `w₀ : W → C` で**導来 p 完備底変換した比較**を対象とする。係数制限だけの写像に `QuasiIso` を要求すると、変数なしでも例えば W → C の非自明な核が問題になる。古典的な型は通常の導来圏での同型、またはその完備複体模型の擬同型とする。各項の完全平坦性や mod p^e の比較を証明してから、項ごとの完備底変換模型を使う。段 3 の有限自由性は完備多項式環上で使うので、これを係数環 W 上の有限自由性と取り違えない。

**配置と規模**。`Prismatic/{PolynomialCategory,BigCechAlexander,WittPDBase,WittBigPDModel,WittCrystallineBridge,WittToSmall,PDPolynomialFunctor,PDDeRhamCDGA,PDDeRhamCompletedComparison}.lean` を中心とする新規分割。厳密な `Poly` と係数制限 → 項の構成と四角形 → 小さい模型の擬同型 → 大きい模型への移送。約 13–25 本、4,100–7,300 行。大きい affine 包の存在、非完全な Witt の完備性、一般 J の橋の mod p 押し出しが幅の主因。

## P3 — affine big 結晶サイトの古典部分

| 対象 | 再利用できる宣言 | 新規に証明すること |
| --- | --- | --- |
| `IsCrystallineCutoff`・`CrysOver`・`Hom`・`essentiallySmall`・`CrysOverSmall`・`CrystallineSite` | `PrismOver.lean` の `cutoff`、`PrismOver` の代数射と濃度の処理、Mathlib の `SmallModel` | 環の側では p 冪零の pd 厚化と `R̄ → B/J_B`、サイト側はその opposite。固定した台集合への移送で本質的小ささを得る。 |
| `IsZariskiFamily`・`zariskiTopology`・`crysAlgebras`・`crystallineStructureRing`・`crystallineStructure_isSheaf` | Mathlib の `IsLocalization.Away`・有限族の被覆と `Coverage.isSheaf_iff_isLimit_coverage`、本体 `FiniteZariskiCover`・`FiniteZariskiBaseChange` の有限局所化の計算 | 分冪の局所化と剰余への移行を示し、有限主開被覆の引き戻し・合成で生成位相を扱う。構造環の等化子は通常の有限 Zariski の貼り合わせ。必要なら増大つき Čech 複体の完全性も古典的に述べる。 |
| `crysPullback`・`crysPullbackSite`・`crysBaseRestriction` | `CrysOver.Hom` の台の写像、`SmallModel` の同値 | `R̄ → R̄′` では `sec` を前合成し、基底変更ではスカラーを制限する。環と局所化は同じなので被覆保存と構造環の制限を照合する。厳密な関手則は環の側で述べ、小さい模型へ移した比較には標準同型を使う。 |
| `crysResidueAlgebra`・`crysResidue_kernel`・`pdCechNerveIdeal`・`pdCechNerveDP`・`pdCechNerve_isDPMorphism`・`pdCechTower`・`pdCechTower_proWeaklyTerminal` | P1 の同じ包データと標準脚、Mathlib の pd 商、既存の Čech 余脈体の圏論 | p 冪商に pd を降ろし、`R̄ ≃ D_S^n/K'` を使って各段を厚化にする。枠が全射なら各段の copy の余積を lift の普遍性で示す。環側の商の遷移は反変、opposite の塔は `ℕ ⥤ CrystallineSite`。任意の厚化へは枠を持ち上げ、対象の p 冪零指数まで下げて包の射を得る。site 側でこれが弱終性。 |
| 多項式の Poincaré、Thm 5.2 の模型 | P1 の `pdModel_iso_pdCechNerve`、P2 の両射影。D68 の `crystallinePDRawComparison`・`pdInclusion`・`pdInclusionModP_isCohomologyIso` と余分な高次 δ 座標の収縮 | `O` の場合の古典的な span を取り出す。`crysPolynomial`・`polyPdCech`・`deltaCechVariable`・`pdDeltaCechNerve`・`etaBridge`・`pdDeltaRetraction` と擬同型、`frobeniusPdBridge`、`crystallineBridge_eq_eta` の厳密な比較を P2 と共用する。高次 δ 座標の収縮は `δ^a X ↦ 0`（`a ≥ 1`）の余脈体因子の収縮で、η は `b ↦ φ(b)`。 |

`IsProWeaklyTerminal`・`ProCechNerveData`・`proCechIndexFunctor`（および `_obj`）の通常の圏論部分を切り出す。`CechNerveData` が参照する各段の積は、通常の圏の積錐として持たせる。§11 の `07JJ` は affine での高次消滅の参照で、今回の層性はその証明で使われる Zariski の貼り合わせの部分。`07LG` は RΓ を計算する定理なので、今回は二射影による複体の比較までを担う。[Stacks 07HM](https://stacks.math.columbia.edu/tag/07HM)、[07HN](https://stacks.math.columbia.edu/tag/07HN)、[07HP](https://stacks.math.columbia.edu/tag/07HP)、[07JJ](https://stacks.math.columbia.edu/tag/07JJ)、[07LG](https://stacks.math.columbia.edu/tag/07LG)

**配置と規模**。`Prismatic/{CrystallineSiteBasic,CrystallineSiteZariski,CrystallineSitePullback,CrystallineCechTower,CrystallinePolynomialComparison}.lean` 付近の新規ファイル。サイトの対象と射 → Zariski と構造環 → 塔と弱終性 → 模型との照合。塔の一般部品は `CategoryTheory/` に分けるのは再利用先がある場合のみ。約 7–14 本、2,000–3,600 行（P2 と共用する η の代数計算は二重計上しない）。P1–P3 合計は約 26–50 本、8,100–14,500 行。

## ⑤c の K1 との分担

- `math/bs-classical` の `4f729b6d7` を確認した。枝には `FrobeniusDivisionPD`・`RegularSequencePD`・`FreeDPModPBlocks` などの 7 モジュールがあり、W15 の報告では一般列の同定・高次 Tor・完備化との照合が停止点 1 の残件。P1 の存在は任意の基底分冪 `γ` と任意の `K` に対する普遍性。K1 の出力は正則列の具体的表示、p 正則性、δ 構造と Frobenius 除算との同定で、P2/P3 から使う。
- 共通の自由分冪の基底、階乗、正則列・Koszul の冪、Frobenius 除算の p 正則性や底変換は既存の `Delta/DividedPower/`・`CommutativeAlgebra/KoszulRegular/` と⑤cの新規補題に寄せる。⑤b には基底の pd 構造の延長・任意イデアルの相対包・その枠とサイトへの適用を置く。K1 からは未完備包の比較と標準脚、完備化・mod p での整合性を受け取る。W の非単項な J 全体を正則列と仮定する経路は採らない。
- P1 は先行できる。P2 の普遍基底の具体化は K2、一般の η の同定は K1 の取り込みに合わせる。`math/bs-impl` と `math/bs-classical` の枝差分に候補パスの重複はない。K1 の作業木の未追跡 3 ファイルも⑤cの既存候補名で、今回の候補とは重ならない。A0・A3 は参照のみ。A1 の `CrystallineInput.lean`・`HodgeTateMap.lean` の CAlg_R に触れる行は⑤aに委ねる。

## 停止点 0 の確認事項

1. **表示独立性の証明順**。P1 では `pdCechNerveMap_quasiIso` の主張を保ち、混合頂点による古典的鎖ホモトピーで先に証明する。a1-design §11.6(5) の site 経由の照合は `RΓ_crys` と模型の接続の段に残す。
2. **古典的な型の切り出し**。`Poly` と通常の代数の係数制限・台加群関手は、今は草稿 A2 や `InfinityCategories/Derived/DiscreteEmbedding` にある。厳密な定義だけを古典モジュールに置き、草稿の使用箇所をつなぐ。`pdDeRhamCDGA` の値域は通常の `CommMon (Complex k)` の余単体的対象とする。複体の `QuasiIso` と通常の導来圏の結果を新規に置き、`*_isInvertible`・`polyUnderlying_iso_bigCech`・`bigZigzagIso`・`deRham_iso_polynomial_universal`・`RΓ_crys` の型は草稿側で保つ。通常の層性は `CategoryTheory.Presheaf.IsSheaf` で別に置き、草稿の E∞ 値の層性とは後で照合する。
3. **塔の指数と cutoff**。`pdCechTower` は一般の pd 基底で `p^{e+2}` の塔を使い、標準の p の分冪と両立する場合に `p^{e+1}` の塔を得る案。包の分冪と標準脚を同じ選択から取り出す。`crysPullbackSite` では `R̄` と `R̄′` を同じ十分大きな cutoff に置く。比較のための cutoff 不変性は使わない。

段 0 はこの報告まで。Lean ファイルの編集・ビルド・監査は実施していない。承認後に P1 に進む。

## 段 1（P1）途中

- 任意の `J.map (algebraMap k B) ≤ K` について、未完備の相対分冪包、p 完備化への分冪の延長、`exists_completedPDEnvelope` を実装した。段 0 の多項式表示による構成の代わりに、環の式と分冪イデアル内の式を分け、標的での評価が一致する式を同一視した。この構成は入力と同じ宇宙に入り、射の一意性は式の帰納法で従う。
- `p^{e+2}` による商に分冪が降りることを示し、余終な塔の座標ごとに分冪の公理と延長射の両立を確認した。完備包を分冪イデアルで割った剰余環は入力の剰余環に戻る。
- `pdFrame`・`pdFrameEval`・`pdCechNerve`・`pdCechAugmentation`・`pdCechNerveMap` を構成し、`pdCechNerveMap_quasiIso` を証明した。表示の比較では二つの写像の変数像を頂点ごとに切り替える余単体ホモトピーを、完備包の各項に直接作った。交代余面複体への移送には既存の `CosimplicialHomotopy.toCochainHomotopy` を使った。台加群を取る関手は Mathlib の可換代数と基底の下の圏の同値から定めた。
- 鍵付きの対象ビルドと一時監査を次の 5 モジュールで実施した。501 宣言に標準三公理のみ。既存の Lean 宣言の変更なし。以下は停止点 1 での登録候補。
  - `SerrePositivity.BhattScholze.Prismatic.RelativePDEnvelope`
  - `SerrePositivity.BhattScholze.Prismatic.PDAdicCompletion`
  - `SerrePositivity.BhattScholze.Prismatic.CompletedPDEnvelope`
  - `SerrePositivity.BhattScholze.Prismatic.PDCechNerve`
  - `SerrePositivity.BhattScholze.Prismatic.PDCechFrameHomotopy`
- 残りは `pdModel_iso_pdCechNerve`。任意の宇宙の係数環に対して小さい枠の添字を合わせるため、`Fin r` を `ULift (Fin r)` として各変数を同じ添字の元に送る。自由分冪代数と階乗表示には D68 の既存部品を使う。⑤c の正則列の包絡と Frobenius 除算のファイルとは重複なし。

## 停止点 1（P1 完了）

- `pdModel_iso_pdCechNerve` を証明した。D68 の `pdRaw` に係数イデアル J と正次数の頂点差の分冪が生成するイデアルを取る。有理係数多項式への単射を使って分冪を制限し、標準脚の普遍性と頂点写像との両立を未完備の環で示した。p 正則性で D68 の主完備化と古典的な p 進完備化を比較し、完備化の単位に沿う射の一意性で余単体自然性を得た。
- 小さい枠の添字は `ULift (Fin r)` とした。これは枠の変数と係数環の宇宙を合わせるためで、各変数は `j.down` 番目の変数に評価する。⑤c の K1 を取り込んだ `bb385d21a` を枝にマージした。P1 は D68 の自由分冪基底・係数拡大・階乗評価を再利用し、K1 で扱う正則列の包と Frobenius 除算との照合は重複させていない。
- 追加の登録候補は以下の 4 本。段 1 途中の 5 本と合わせて、全 9 本を `BhattScholze.lean` と段階 II の監査に登録する対象とする。
  - `SerrePositivity.BhattScholze.Prismatic.PDFromGenerators`
  - `SerrePositivity.BhattScholze.Prismatic.PDRelativeFree`
  - `SerrePositivity.BhattScholze.Prismatic.PDSmallRawEnvelope`
  - `SerrePositivity.BhattScholze.Prismatic.PDSmallModelComparison`
- 全 9 本の `--wait 1800` 付き対象ビルドと一時監査が通過。非公開宣言を含む 661 宣言の依存公理は標準三公理のみ。追加の公理と `sorry` は 0。既存の Lean 宣言の変更と A1 の CAlg_R 部分への編集はない。
- 段 2 は多項式代数の圏と係数変更を古典的に切り出し、既存の affine 模型を大きい枠へ延ばすところから進める。

## 段 2（P2）途中 — 多項式関手と Witt 基底

- `Poly` と係数変更 `changePoly` を古典的なモジュールに切り出した。D68 の `polyCompletion` に対する `polyCompletionMap` は未完備多項式の単位と可換で、恒等と合成を保つ。草稿 A2 の `Poly` を本体のものへ差し替える際は、草稿の同名定義を新モジュールの import に置き換える。
- 剰余環の代数射と枠の変数の改名から分冪 Čech 脈体の写像を作った。これを `Q̂ → Q̂′` と `Q̂/p → Q̂′/p` に適用し、`bigPDModel` とその Witt 係数版 `wittBigPdModel` を厳密な関手として構成した。
- `wittPdStructure` は `J = (w₀)⁻¹(pC)` を Verschiebung の像と p で生成して構成した。p を反転した環での階乗表示を生成元ごとに降ろし、`wZero_isDPMorphism` は階乗を掛けて両辺を比較した。Witt 環の p 正則性は ghost 射で、p 進完備性は列の差分方程式を第 0 成分で解いて Verschiebung で残りを持ち上げることで示した。
- `psiRing`・`wZero_psi`・`psiPrism` は任意の向き付き prism を引数にし、必要な p 正則性と剰余環の p 進完備性を明示した。Witt Frobenius の mod p の性質には既存の相対自由 δ 環の Witt 座標を用いた。この段階の実装には K2 の普遍 prism の具体化は不要。具体化が入ったときに `psiPrism` へ適用する。
- 鍵付きの対象ビルドと一時監査は以下の 7 モジュールで通過。非公開宣言を含む 163 宣言は標準三公理のみで、追加公理と `sorry` は 0。既存の Lean 宣言と A0・A1・A3 の草稿は編集していない。以下は停止点 2 での登録候補。
  - `SerrePositivity.BhattScholze.Prismatic.PolynomialCategory`
  - `SerrePositivity.BhattScholze.Prismatic.PolynomialCompletionFunctor`
  - `SerrePositivity.BhattScholze.Prismatic.PDCechNerveNaturality`
  - `SerrePositivity.BhattScholze.Prismatic.BigPDModel`
  - `SerrePositivity.BhattScholze.Prismatic.WittPDBase`
  - `SerrePositivity.BhattScholze.Prismatic.WittAdicCompleteness`
  - `SerrePositivity.BhattScholze.Prismatic.WittCrystallinePrism`
- 残りは大きい prismatic Čech–Alexander 模型、有限枠と大きい枠の比較、`wittBigBridge` と `wittToSmall` の厳密な射および導来 p 完備底変換での擬同型、完備 pd de Rham の多項式代入と二射影。停止点 2 の検収はこれらを閉じた後に行う。
