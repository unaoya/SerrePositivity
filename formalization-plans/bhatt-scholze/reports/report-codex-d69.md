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

## 段 2（P2）途中 — 有限枠との比較

- `polynomialResidueEquiv` で、p 正則な剰余係数環上の完備多項式を p で割ると通常の多項式になることを、D68 の主完備化単位の mod p 同型から示した。
- `wittSmallFrame` は小さい D68 の分冪模型から `wittBigPdModel` の各値への写像。`W/J ≃ C/p` と `polynomialResidueEquiv` で同じ剰余環上の二つの枠に直し、P1 の表示独立性から `wittSmallFrame_quasiIso` を得た。
- `bigCechAlexanderOfTerms` は、評価核の prismatic envelope を項ごとに受け取り、`Poly(C)` と単体の積圏上で厳密に関手化する。導来 p 完備化で閉じる前のイデアルを使う。閉包を取る版には既存の `IsPrismaticEnvelope.of_closure` を適用できる。
- 次の3モジュールの鍵付き対象ビルドが通過。段 2 のここまでの10モジュールを一時監査し、非公開宣言を含む321宣言が標準三公理のみであることを確認した。
  - `SerrePositivity.BhattScholze.Prismatic.PolynomialCompletionResidue`
  - `SerrePositivity.BhattScholze.Prismatic.WittSmallFrame`
  - `SerrePositivity.BhattScholze.Prismatic.BigCechAlexander`
- ⑤c の K2・K3 を含む main `14f8925ae` を取り込んだ。K2 の普遍 prism の p 正則性と剰余の p 正則性を `psiPrism` の入力に使える。⑤a・⑤c と編集ファイルの重複はない。

## 段 2（P2）途中 — affine 包と結晶 prism 構造

- `bigCechAlexander` を有界 prism 上で構成した。第 0 頂点の多項式変数は固定し、それ以外の枠の変数から評価値の持ち上げを引く。持ち上げには完備多項式環の係数商の全射性を使う。変数の部分集合に沿う既存の包の普遍性をこの座標変換で移し、各項の有界性も示した。
- `affineCechAlexanderFrame` は D68 の有限 affine 模型から大きい模型への余単体的代数の射。指定した各頂点の変数像で作り、包の普遍性で単体の写像との可換性を示した。この比較の擬同型性は残っている。
- K2 の普遍 prism と剰余環の p 正則性を使い、`universalOrientedResidue_complete`・`universalWittPrismMap`・`universalWittBigPDModel` を構成した。
- p 正則な完備分冪包について `exists_deltaStructure_of_pdPolynomial` と `wittPDEnvelopeCrystalline` を示した。標的の (p) の標準分冪へ包の Frobenius を延長する。mod p では分冪イデアルの元の p 乗が零なので、通常の Frobenius と一致する。大きい Witt 模型の各項が p 正則であることは別途証明が必要。
- 以下の6モジュールを追加した。ここまでの段 2 の16モジュールは鍵付き対象ビルドと一時監査を通過。非公開を含む536宣言は標準三公理のみで、追加公理と `sorry` は0。
  - `SerrePositivity.BhattScholze.Prismatic.BigCechCompletionLift`
  - `SerrePositivity.BhattScholze.Prismatic.BigCechAffineEnvelope`
  - `SerrePositivity.BhattScholze.Prismatic.BigCechFrameComparison`
  - `SerrePositivity.BhattScholze.Prismatic.UniversalWittComparison`
  - `SerrePositivity.BhattScholze.Prismatic.PDFrobeniusLift`
  - `SerrePositivity.BhattScholze.Prismatic.WittPDEnvelopeCrystalline`

## 段 2（P2）途中 — 完備 de Rham の二射影

- D68 の第 0 行への射影に加え、第 0 列への射影の擬同型を任意の係数環で示した。分冪座標ごとの積分と定数項の写像を p 完備化へ延ばし、鎖ホモトピーの等式を保ったまま全座標を収縮した。
- 第 0 列を通常の完備 de Rham 複体と同定し、総複体からの合成 `pdDeRhamTotalToCompletedForms` の擬同型性を示した。ここでの比較は複体の写像であり、多項式代入との厳密な自然性と積の照合は残っている。
- 以下の3モジュールの鍵付き対象ビルドが通過。段 2 のここまでの19モジュールを一時監査し、非公開を含む628宣言は標準三公理のみ。追加公理と `sorry` は0。既存の Lean 宣言の変更はない。
  - `SerrePositivity.BhattScholze.Prismatic.PDCompletedColumnContraction`
  - `SerrePositivity.BhattScholze.Prismatic.PDDeRhamCompletedProjection`
  - `SerrePositivity.BhattScholze.Prismatic.PDDeRhamCompletedColumnZero`

## 段 2（P2）途中 — 小さい分冪模型の関手性

- `PDPolynomialFunctor.nerve` では各頂点で多項式を代入し、剰余への評価と両立することから分冪包へ延長した。恒等、合成、単体の射との可換性は、枠の変数上で照合した。
- `pdPolynomialFunctor` は P1 の有限枠との同型を介して代入を D68 の小さい模型へ移した厳密な関手。有限枠との同型も多項式代入に関して自然。
- `SerrePositivity.BhattScholze.Prismatic.PDPolynomialFunctor` の鍵付き対象ビルドが通過。段 2 のここまでの20モジュールを一時監査し、非公開を含む668宣言は標準三公理のみ。追加公理と `sorry` は0。

## 段 2（P2）途中 — Witt 係数から小さい模型への射

- `wittToSmall` は、第 0 Witt 成分に沿って係数を制限した小さい分冪模型への厳密な自然変換。大きい枠の変数 `(q, i)` を、頂点 `i` における完備多項式 `q` の評価へ送る。剰余での評価が一致することを確かめ、完備分冪包の普遍性を使った。
- 単体の射と多項式代入との可換性は、完備化前の多項式と枠の変数で検査した。導来 p 完備な係数変更後の擬同型性は残っている。
- `SerrePositivity.BhattScholze.Prismatic.WittToSmall` の鍵付き対象ビルドが通過。段 2 のここまでの21モジュールを一時監査し、非公開を含む774宣言は標準三公理のみ。追加公理と `sorry` は0。

## 段 2（P2）途中 — 大きい Witt 枠の正則性

- 第 0 頂点の通常の多項式変数を残し、余分な変数から剰余評価の多項式の持ち上げを引いた。座標変換後の完備分冪包は、残した座標の多項式環と余分な座標の自由分冪代数とのテンソル積の p 完備化で計算できる。
- この模型の p 正則性を元の分冪包へ移して `wittBigCrystalline` を構成した。零環の剰余は別に扱い、座標の選択は正則性の証明だけに使った。
- 変数を改名する Witt 係数の分冪射が結晶 δ 構造を保つことを示した。Frobenius との二つの合成は、標的の (p) 上の標準分冪への分冪射として係数と変数で一致する。
- 以下の4モジュールは鍵付き対象ビルドを通過。段 2 の累計25モジュールの一時監査で、非公開を含む895宣言が標準三公理のみであることを確認した。追加公理と `sorry` は0。
  - `SerrePositivity.BhattScholze.Prismatic.PDPolynomialSplitEnvelope`
  - `SerrePositivity.BhattScholze.Prismatic.PDPolynomialGraph`
  - `SerrePositivity.BhattScholze.Prismatic.WittBigCrystalline`
  - `SerrePositivity.BhattScholze.Prismatic.WittPDPrismMaps`

## 段 2（P2）途中 — 小さい模型の係数変更

- `pdModelBaseChange` は小さい完備分冪 Čech 模型の係数変更。未完備の多項式・自由分冪の係数変更を各項で完備化し、余単体構造との可換性を移した。`pdModelBaseChange_unit` で未完備模型との可換性を示した。
- `SerrePositivity.BhattScholze.Prismatic.PDModelBaseChange` の鍵付き対象ビルドが通過。段 2 の累計26モジュールの一時監査で、非公開を含む904宣言は標準三公理のみ。追加公理と `sorry` は0。

## 段 2（P2）途中 — 厳密な結晶の橋

- `wittBigBridge` を大きい affine Čech–Alexander 模型から Witt 分冪模型への厳密な自然変換として構成した。係数の射は `psiPrism` で、各頂点の枠の変数は p 乗へ送る。
- Frobenius 前の多項式評価は、prismatic 側の評価核を分冪イデアルへ送る。Frobenius 後はその像が (p) に入るため、完備自由 δ 環と prismatic envelope の普遍性を使った。単体の写像と多項式代入の両方との可換性は、係数と枠の変数で照合した。
- `SerrePositivity.BhattScholze.Prismatic.WittBigBridge` の鍵付き対象ビルドが通過。段 2 の累計27モジュールを一時監査し、非公開を含む1,003宣言は標準三公理のみ。追加公理と `sorry` は0。
- 停止点 2 までに、有限枠から大きい prismatic 枠への射の擬同型性、`wittBigBridge` と `wittToSmall` の導来 p 完備底変換後の擬同型性、完備 pd de Rham の cdga の代入と二射影の厳密な自然性を示す。段 3 の結晶サイトはこの検収の後に進める。

## 段 2（P2）途中 — 逆向きの枠の射と分冪係数変更

- `BigCechTerm.existsUnique_liftVariables` は、剰余の構造射と両立する枠の変数像を完備自由 δ 環から包へ延長する。有限枠の第 0 項で選んだ持ち上げを各頂点へ送り、`bigCechToAffineFrame` として大きい枠から有限枠への余単体的代数の射を得た。
- `affineToBig_residueSection` で、有限枠から大きい枠への射が完備多項式の剰余構造射を保つことを示した。この照合により、二つの合成と恒等射の変数像を剰余で比較できる。混合頂点による余鎖ホモトピーは残っている。
- 未完備の小さい模型で、基底の分冪を保つ係数変更は分冪射になることを示した。これを使う `wittToSmall_frame` の完備化後の照合は進行中。
- 以下の4モジュールは鍵付き対象ビルドを通過。段 2 の累計31モジュールの一時監査で、非公開を含む1,047宣言は標準三公理のみ。追加公理と `sorry` は0。段 2 の途中のため、停止点 2 の検収は保留。
  - `SerrePositivity.BhattScholze.Prismatic.BigCechFrameLift`
  - `SerrePositivity.BhattScholze.Prismatic.BigCechFrameRetraction`
  - `SerrePositivity.BhattScholze.Prismatic.BigCechFrameResidue`
  - `SerrePositivity.BhattScholze.Prismatic.PDRawCoefficientPD`

## 段 2（P2）途中 — Witt 比較の有限枠での照合

- `wittToSmall_frame` を示した。有限 Witt 枠から大きい枠へ入れて `wittToSmall` を適用した射は、小さい模型に対する `pdModelBaseChange` と一致する。未完備の分冪包で各頂点の変数像を照合し、完備化の普遍性で等式を移した。
- `SerrePositivity.BhattScholze.Prismatic.WittToSmallFrame` の鍵付き対象ビルドが通過。段 2 の累計32モジュールの一時監査で、非公開を含む1,145宣言は標準三公理のみ。追加公理と `sorry` は0。
- 導来 p 完備底変換での擬同型性には、有界な完備 de Rham 複体を使う。まず未完備項の単項式基底でテンソル底変換を照合し、p の有限冪で割った各項を比較する。導来底変換を計算する箇所では有界な模型と平坦性を明示する。

## 段 2（P2）途中 — 11 月 10 日の夜前の区切り

- `pdRawCoefficients_isBaseChange` で、未完備の各項のテンソル底変換を単項式基底で計算した。これを p の有限冪での商と有界な完備 de Rham 模型の比較へつなぐ。
- `SerrePositivity.BhattScholze.Prismatic.PDRawBaseChangeLinear` の鍵付き対象ビルドが通過。段 2 の累計33モジュールの一時監査は1,146宣言で標準三公理のみ。追加公理と `sorry` は0。
- 次は有限枠と大きい prismatic 枠の二つの合成を、混合頂点で恒等射に結ぶ。Witt の二比較の導来 p 完備底変換後の擬同型性と、完備 pd de Rham の代入に関する二射影の厳密な自然性も残る。

## P3 の紙上整理（11 月 10 日夜）

古典的なサイトの入口は `SerrePositivity.BhattScholze.Prismatic` に置く。以下の型は設計案。記号は `γ : DividedPowers J`、`hp : (p : k) ∈ J`、`R : Type u` とし、`R` は `k ⧸ J` 代数とする。

| ファイル案 | 宣言の型の案と担当 |
| --- | --- |
| `CrystallineSiteBasic` | `IsCrystallineCutoff k R κ : Prop := cutoff k R ≤ κ`。 `CrysOver p γ R κ` は `B : Type u`、可換環と `k` 代数の構造、`I : Ideal B`、`δ : DividedPowers I`、係数の分冪射、`IsNilpotent (p : B)`、係数と両立する `sec : R →+* B ⧸ I`、`Cardinal.mk B ≤ κ`。 `CrysOver.Hom X Y` は `X.B →ₐ[k] Y.B` と分冪・剰余の可換性。 `CrysOver.essentiallySmall : EssentiallySmall.{u} (CrysOver p γ R κ)` を得て、`CrystallineSite := (SmallModel (CrysOver p γ R κ))ᵒᵖ` とする。小さい模型を使う手順は `PrismOver` と同じ。 |
| `CrystallineSiteLocalization` | `crysAway (X : CrysOver p γ R κ) (f : X.B) : CrysOver p γ R κ` と `X ⟶ crysAway X f`。台環は `Localization.Away f`、イデアルは像、剰余構造射は商写像との合成。分冪の局所化と、局所化済みの標的への分冪射の一意性をここで示す。濃度評価は局所化の分子・分母の表示から従う。 |
| `CrystallineSiteZariski` | `IsZariskiFamily (f : ι → X.B) (h : ∀ i, X ⟶ Y i) : Prop`（有限型 `ι`）は各脚が `Away (f i)` で `Ideal.span (Set.range f) = ⊤`。opposite で引き戻しと合成を示して `zariskiTopology : GrothendieckTopology (CrystallineSite p γ R κ)` を定める。 `crysAlgebras : CrysOver p γ R κ ⥤ Under (CommRingCat.of k)` を小さい模型に制限し、`crystallineStructure_isSheaf : Presheaf.IsSheaf zariskiTopology crystallineStructureRing` を有限主開の貼り合わせから示す。 |
| `CrystallineSitePullback` | `crysPullback (f : R →ₐ[k ⧸ J] R') : CrysOver p γ R' κ ⥤ CrysOver p γ R κ` は `sec` の前合成。 `crysPullbackSite` は小さい模型を経た opposite の関手で、主開被覆を保つ。 `crysBaseRestriction` は分冪基底射と剰余代数の写像を引数にとる同様の関手。同じ `κ` を取り、係数制限された構造環との比較を通常の自然同型で記述する。 |
| `CrystallineCechQuotient` | `crysResidueAlgebra` と `crysResidue_kernel` の後、`pdCechQuotient (s : S → R) (hs : Function.Surjective (pdFrameEval … s 0)) (e n : ℕ) : CrysOver p γ R κ`。台環は `D_s^n ⧸ (p^(e+2))`、分冪イデアルは包のイデアルの像。全射性から得る `D_s^n / I ≃ₐ[k] R` の逆向きで剰余構造射を定める。まず有限段の環側で定義し、cutoff に入ることを分けて示す。 |
| `CrystallineCechTower` | `pdCechTower … : ℕᵒᵖ × SimplexCategory ⥤ CrysOver p γ R κ` を商の遷移と P1 の頂点射で作る。固定 `e` では次数 `n` の頂点射が `Fin (n+1)` 個の第 0 項の余積を表すことを `IsColimit` で示す。opposite で得た第 0 項の塔 `U : ℕ ⥤ CrystallineSite …` に対し `pdCechTower_proWeaklyTerminal : ∀ X, ∃ e, Nonempty (X ⟶ U.obj e)`。同じ cutoff の中で標的の p 冪零指数より大きい段を選ぶ。 |
| `CrystallinePolynomialComparison` | `R := MvPolynomial (Fin r) (k ⧸ J)` に対し、P1 の有限枠の交代余面複体と連続 de Rham 複体を結ぶ span。中央は `pdDeRhamTotal p k r`、左脚は第 0 行、右脚は `pdDeRhamTotalToCompletedForms`。両脚の `QuasiIso` と、必要な場合に `pdCechTower` の有限段からの構造射との照合を別定理にする。 |

**既存部品の接続。**

- P1 の `PDCechNerve.term` から包・イデアル・分冪・標準脚を一緒に取る。 `PDAdicCompletion` の有限冪商と `IsCompletedPDEnvelope.quotientEquiv` が塔の入力。有限段の普遍性には、標的の p 冪零性から得る p 完備性と、`p^(e+2)` を消す条件の両方を使う。一般の基底では `p` 自体による商に分冪が降りるとは仮定しない。
- P2 の `pdModel_iso_pdCechNerve` と二射影を多項式 Poincaré の複体比較に使う。係数と枠の自然性には `wittToSmall_frame` と P2 の射影の自然性を参照する。大きい枠の `WittBigCrystalline` の p 正則性は結晶の橋の入力で、一般の厚化の対象条件には入れない。
- ⑤c の K1 は main にある `RegularSequencePD`、`FrobeniusDivisionPD`、`FreeDPModPBlocks`。正則列から作る η の具体的模型、mod p での座標、Frobenius 除算の同定に使う。任意のイデアルに対する塔の存在・弱終性は P1 の普遍性だけで示せる。
- ⑤c の K4 は `math/bs-classical` の `74f5032f5` までを参照した。 `exists_isPushout_isFaithfullyFlat` の圏の向きと cutoff の扱いは Zariski の引き戻しの先例。主開の環計算は本体の `FiniteZariskiCover`・`FiniteZariskiBaseChange` を直接使う。 `idealPowerCompletedCech_acyclic` と逆塔の完全性は有限段から完備な構造環を比較する箇所で使える。 `prismaticEnvelope_completedBaseChange_of_variables` と `completelyFlatCochain_isDiscrete_of_boundedPrism` は P2 の ψ 側の底変換で候補になる。K4 の枝の宣言を import する作業は main への取り込み後に行う。
- `RΓ_crys` と site の極限による計算は草稿に置く。ここでの層性は通常の環値前層、Poincaré は交代余面複体の定理。P3 の Lean 本体は P2 の停止点を経て着手する。

## P2 の夜間作業（11 月 11 日朝の検査待ち）

- 枠の比較は、有限 affine 枠の変数の持ち上げを `AffineCechFrameLift` に置いた。`CechVertexHomotopy` に混合頂点の余単体恒等式、`PrismaticFrameHomotopy` に包の普遍性から交代余面複体へ移す部分を置いた。`AffineCechVertexFrame` と `BigCechVertexFrame` で両方の枠に適用し、既存の比較射の二つの合成を恒等射に結ぶ余鎖ホモトピーの定義と証明を書いた。大きい枠の各項の有界性と共通の濃度上限を仮定に取り、標準の大きい枠への特殊化と擬同型の宣言は朝の検査後に続ける。
- Witt の二比較では、`PDModelCompletionQuotient` に小さい分冪模型の完備項の有限冪商とその平坦性を書いた。`WittBigBridgeAffineFrame` で ψ 側の橋を有限枠に制限し、係数が ψ、各頂点の変数像が p 乗であることを照合した。残りは ψ に沿った有限冪商での押し出し、`wittToSmall_frame` の係数変更の有限冪商への移送、各項の完備テンソルが有界な模型で導来底変換を計算すること、および二つの擬同型への組み立て。
- pd de Rham では `PDRawPolynomialSubstitution` に未完備分冪包への代入を書いた。`PDDeRhamSubstitutionJacobian` で多項式の微分と差座標の Jacobian を定め、`BicomplexProjectionNaturality` で双複体の射に対する二射影の可換性を書いた。残りは分冪偏微分の連鎖律、外積への延長と完備化、縦横の微分と可換な双複体の射、第 0 行・第 0 列の比較同型との照合。
- 上の Lean 10 本は夜間ビルド前の作業木に置いた。P2 の停止点は、残りの証明と以下の検収の後。

## 朝の対象ビルドの順番

日本時間 8 時から。夜の終了の目印が先に現れたときはその時点から。⑤b の作業木で一組ずつ実行する。

1. 枠の普遍性とホモトピーの共通部分。

   ```sh
   scripts/refactor/with_build_lock.sh --wait 1800 -- lake build \
     SerrePositivity.BhattScholze.Prismatic.AffineCechFrameLift \
     SerrePositivity.BhattScholze.Prismatic.CechVertexHomotopy
   ```

2. 二つの合成のホモトピー。順に `PrismaticFrameHomotopy`、`AffineCechVertexFrame`、`BigCechVertexFrame`。

   ```sh
   scripts/refactor/with_build_lock.sh --wait 1800 -- lake build \
     SerrePositivity.BhattScholze.Prismatic.BigCechVertexFrame
   ```

3. 完備係数の有限冪商と Witt の比較の有限枠への制限。

   ```sh
   scripts/refactor/with_build_lock.sh --wait 1800 -- lake build \
     SerrePositivity.BhattScholze.Prismatic.PDModelCompletionQuotient \
     SerrePositivity.BhattScholze.Prismatic.WittBigBridgeAffineFrame
   ```

4. 分冪多項式代入、Jacobian と総複体の射影。代入を先に単独で確認する。

   ```sh
   scripts/refactor/with_build_lock.sh --wait 1800 -- lake build \
     SerrePositivity.BhattScholze.Prismatic.PDRawPolynomialSubstitution
   scripts/refactor/with_build_lock.sh --wait 1800 -- lake build \
     SerrePositivity.BhattScholze.Prismatic.PDDeRhamSubstitutionJacobian \
     SerrePositivity.HomologicalAlgebra.BicomplexProjectionNaturality
   ```

5. 対象ビルドの後、`/private/tmp/AuditD69P2Night.lean` を `lake env lean` で一時監査する。夜前の33本と上の10本を対象に、非公開宣言も含めて標準三公理のみであることを確認する。続けて追加する証明はこの監査の対象に足す。

## 段 2（P2）途中（11 月 11 日朝）

- `main` の取り込みと登録を含む `6e6a3f9a7` へ早送りした。夜間の枠の持ち上げ、混合頂点、prism 上の余鎖ホモトピー、有限 affine 枠への適用の対象ビルドが通った。大小の枠の比較の二つの合成と、標準比較への移送は引き続き検査中。
- Witt の結晶の橋を有限枠に制限した座標計算、未完備分冪模型の代入、Jacobian と分冪偏微分の連鎖律、双複体の第 0 行・第 0 列への射影の自然性が対象ビルドを通った。連鎖律は自由分冪の生成元に階乗を掛けて通常の冪に直し、標的の p 正則性と p 完備性で階乗を消去して示した。
- 今回ビルドと監査が通った追加は `AffineCechFrameLift`、`CechVertexHomotopy`、`PrismaticFrameHomotopy`、`AffineCechVertexFrame`、`WittBigBridgeAffineFrame`、`PDRawPolynomialSubstitution`、`PDDeRhamSubstitutionJacobian`、`PDDeRhamSubstitutionChainRule`、`SerrePositivity.HomologicalAlgebra.BicomplexProjectionNaturality` の9本。一時監査は夜前の33本を合わせた42本、1,352宣言で標準三公理のみ。

- `BigCechVertexFrame` と `BigCechAffineFrameQuasiIso` が通った。共通の濃度上限に大小の標準枠を置けることを示し、二つの合成の余鎖ホモトピーを `affineCechAlexanderFrame_quasiIso` に移した。
- `PDModelCompletionQuotient`、`PDRawBaseChangeQuotient` が通った。前者は有限冪商の平坦性と完備化単位との照合、後者は未完備項での底変換を係数のイデアルの商まで移した環同型。
- `PDDeRhamCompletedSubstitution`、`PDCompletedSubstitutionNaturality`、`PDDeRhamSubstitutionForms` が通った。完備係数に連鎖律を移し、各余面・余退化と可換な代入の関手、および Jacobian の各外冪への延長を作った。外積と微分を保つことと、総複体の二射影との照合は検査を続けている。
- 上の追加7本を含む49本の一時監査は1,516宣言で標準三公理のみ。Witt の二比較の導来 p 完備底変換後の擬同型と、完備 pd de Rham の厳密な自然性が残る。

- `PDTermQuotientModel` と `WittFiniteBridge` が通った。前者では完備分冪模型の実際の各項の p 冪商を未完備項の商と比較した。後者では有限 prismatic 枠から小さい Witt 模型への橋を、基底を ψ、各頂点の変数像を p 乗と指定して構成した。大小の Witt 枠を結ぶ四角形は検査中。
- 上の2本を含む51本の一時監査は1,574宣言で標準三公理のみ。

- `PDDeRhamSubstitutionWedge` と `PDDeRhamSubstitutionGenerators` で、完備形式の代入が外積を保ち、1 形式では完備 Jacobian になることを示した。`PDDeRhamBicomplexCoefficients` では完備形式の係数変更を双複体の射にし、係数制限で読んだ二つの射影と可換であることを示した。
- `PDDeRhamColumnBounded` で第 0 列の有界性と各列の導来 p 完備性、`SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletedBaseChangeEquivalence` で完備化同値が導来底変換後にも完備化同値になることを示した。これら5本の対象ビルドが通り、56本の一時監査は1,653宣言で標準三公理のみ。

- `main` の `c77013db6` を `74b2af07f` で取り込んだ。K4 の `VariableEnvelopeBaseChange` が参照できるようになり、共有鍵を整理券方式に切り替えた。
- `WittFiniteBridgeNaturality` で有限枠の各次数の結晶の橋を余単体射にし、`WittFiniteBridgeSquare` で大きい Witt 枠への二つの合成を各次数で照合した。`PDDeRhamSubstitutionDegreeZero` は次数 0 の代入と微分の可換性を証明した。
- 共通の `SerrePositivity.CommutativeAlgebra.DeRham.PolynomialDeRhamCompletionUnit` で未完備多項式 de Rham 複体の有界性と完備化単位、`SerrePositivity.HomologicalAlgebra.DerivedCompletion.PowerCokernelEquivalence` で正則なスカラーの冪商から完備化同値を判定する補題を示した。これら5本は鍵付きの対象ビルドを通った。61本の一時監査は1,781宣言で標準三公理のみ。

- `PDDeRhamSubstitutionDifferential` で、多項式代入と完備分冪微分の可換性を全次数で示した。頂点変数の微分が 1 形式を生成し、外積の保存と Leibniz 則で高次数へ延ばす。`PDDeRhamRowFormsExt` で係数と微分を保つ形式の写像を次数 0 で比較し、`PDDeRhamSubstitutionCofaces` と `PDDeRhamSubstitutionFunctor` で余面・余退化、恒等射、合成の厳密な両立を示した。二つの射影も厳密に自然になった。
- `PDDeRhamCoefficientProjection` で、D68 の既存の総複体の係数変更と実際の二射影の成分を照合した。`PDRawColumnCompletion` で標数を仮定しない未完備の分冪列と完備列への標準写像、`PDRawFormsBaseChange` で各項の自由模型の通常の底変換を作った。`SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletedBaseChangeModel` で完備化同値と射影模型から完備導来底変換を計算する同型と可換図式を示した。
- この追加8本は鍵付きの対象ビルドを通った。69本の一時監査は1,977宣言で標準三公理のみ。残りの Witt の二比較では、有限冪商から列の完備底変換を計算する部分と、K4 の比較を余単体構造に移して一般の結晶の橋を適用する部分を続ける。

- `WittAffineBaseChange` で、標準の有限 affine 項を ψ に沿って完備テンソルした環を、Witt 係数の完備自由 δ 環に同定した。⑤c の `exists_completedFreeDelta_baseChange_equiv` をそのまま使い、左の係数脚と自由座標上の等式を残した。余単体射と橋への移送は続けて検査する。対象ビルドは成功し、70本の一時監査は1,996宣言で標準三公理のみ。


## 段 2（P2）途中（11 月 11 日昼）

- `main` の `7a689544b` を `5b9030cd3` で取り込んだ。共有鍵の待ちは以後 `--wait 3600` とし、この作業木から並べる整理券は一つにまとめる。昼の bulk を繰り上げない版のスクリプトを使っている。
- `PDTermReductionLinear` と `PDTermCompletionEquivalence` で、実際の完備化単位が有限冪商で誘導する線形同型を示した。共通の `ScalarCokernelTensor` でスカラー作用の余核の同型を任意の加群とのテンソルに移す。`PDColumnCompletionEquivalence` でこれを列の各項に適用し、自由な未完備列の単位が導来 p 完備化後で擬同型になることを示した。
- `PDRawColumnBaseChange` と `PDRawColumnBoundedModel` で、第 0 列の有界自由模型と通常の底変換同型を作った。`PDColumnCompletedBaseChange` で、両基底が p 正則であれば、完備第 0 列の導来 p 完備底変換を標的の完備第 0 列で計算できる。係数の環射の平坦性を追加する必要はない。自由模型からの実際の射は `pdColumnZeroBaseChangeFreeMap` で指定し、完備化単位との照合には共通の `completedBaseChangeModelIso_hom_comm` を使う。
- `PDColumnCoefficientUnit` で、実際の半線形な係数変更と自由模型の完備化単位の可換性を示した。`PDDeRhamDerivedSpan` と `PDDeRhamCompletedBaseChange` で、総複体から出る二射影を使って第 0 列の底変換同型を総複体と第 0 行へ移した。Witt の指定された比較射への適用は続けて検査する。
- `CompletedFreeDeltaScale`、`AffineEnvelopeBaseChange`、`AffineEnvelopeCoefficients`、`AffineEnvelopeBaseChangeCoefficients` で、K4 の項ごとの自由 δ 環の同型を affine 包の頂点座標を保つ形に直した。prism の生成元の像の単元倍を、差の分母座標の逆単元倍で補正する。右脚との合成は δ 射になり、包の一意性で指定された係数変更に一致する。この係数変更は余単体射と厳密に可換。

### 検収と残り

今回の追加15本は `with_build_lock.sh --wait 3600` を通した対象ビルドが成功した。追加を含む85本の一時監査は2,302宣言で標準三公理のみ。新規ソース中の `sorry` と独自公理は0で、既存宣言の変更もない。検査ログは `/private/tmp/d69-ticket-build-14.log` と `/private/tmp/d69-morning-audit-fiftytwo.log`、一時監査は `/private/tmp/AuditD69P2MorningFiftyTwo.lean`。Witt の二比較の擬同型の最終宣言は引き続き残る。第 0 列の計算と二射影の自然性を第 0 Witt 成分による係数変更へ適用し、もう一方では affine 底変換の比較と一般の結晶の橋を合わせる。

今回の登録候補は次のとおり。共通の一本を除き `SerrePositivity.BhattScholze.Prismatic` の下に置いた。

- `PDTermReductionLinear`
- `PDTermCompletionEquivalence`
- `PDColumnCompletionEquivalence`
- `PDRawColumnBaseChange`
- `PDRawColumnBoundedModel`
- `PDColumnCompletedBaseChange`
- `PDColumnCoefficientUnit`
- `PDDeRhamDerivedSpan`
- `PDDeRhamCompletedBaseChange`
- `CompletedFreeDeltaScale`
- `AffineEnvelopeBaseChange`
- `AffineEnvelopeCoefficients`
- `AffineEnvelopeBaseChangeCoefficients`
- `SerrePositivity.HomologicalAlgebra.DerivedCompletion.ScalarCokernelTensor`
- `PDEnvelopeCrystalline`

- `PDEnvelopeCrystalline` は既存の `exists_deltaStructure_of_pdPolynomial` を一般の結晶基底に適用する。Frobenius が基底の分冪イデアルを (p) に送ることを仮定し、包の生成元、基底の δ 両立、各枠変数の δ が零であることを残した。Witt に限らない小さい結晶模型への適用を続ける。


- 続く追加6本の対象ビルドが通った。`PDEnvelopeCrystallineMaps` で基底を固定する変数の改名が一般の小さい分冪包の δ 構造を保つこと、`PDDeltaFrobeniusEvaluation` で Frobenius 差の δ 除算模型から小さい分冪包へ送る評価とその基底脚・変数像、`CrystallinePDRetraction` で既存の ℤ_p の結晶模型への適用を示した。
- `PDRawRingHomExt` と `PDTermRingHomExt` で、p 正則・p 局所な標的への代数射を頂点の変数で比較できることを示した。未完備の模型では階乗を消去し、完備項では主完備化の一意延長を使う。`SerrePositivity.BhattScholze.Delta.Division.HomExt` で、p 正則な完備標的への δ 射を標準脚で比較する共通補題を追加した。
- 上の6本を含む91本の一時監査は2,405宣言で標準三公理のみ。新規ソースの `sorry`・独自公理は0で、既存宣言の変更もない。対象ビルドは `/private/tmp/d69-ticket-build-18.log`、一時監査は `/private/tmp/AuditD69P2MorningFiftyEight.lean` と `/private/tmp/d69-morning-audit-fiftyeight.log`。
- この6本も登録候補に加える。自然性と分冪包含の切断を記す `CrystallinePDRetractionNaturality` と `CrystallinePDRetractionSplit` は作業木で検査中。次は切断を使って既存の mod p の包含と結晶の橋のコホモロジー同型を、小さい分冪模型への橋へ移す。

- `CrystallinePDRetractionNaturality` で、結晶の δ 除算模型から小さい分冪模型への評価を厳密な余単体射にまとめた。`CrystallinePDRetractionSplit` で、既存の分冪包含にこの評価を続けると整係数で恒等射になることを示した。各次数の包の改名は既存の `CrystallinePDRetraction` 内に私的な補題として足した。以前の宣言の型と証明は変更していない。
- `CrystallineSmallBridgeModP` で、この切断を mod p に降ろした。既存の包含のコホモロジー同型を消去すると評価もコホモロジー同型になり、既存の結晶の橋との合成も同様になる。型照合では、次数を自然数で固定してから余単体の対象に組み立て、完備模型の内部での `m` と `⦋m.len⦌` の照合を避けた。
- この追加3本の鍵付き対象ビルドは `/private/tmp/d69-ticket-build-20.log` と `/private/tmp/d69-ticket-build-21.log` で成功した。94本の一時監査は2,496宣言で標準三公理のみ。一時監査とログは `/private/tmp/AuditD69P2MorningSixtyOne.lean` と `/private/tmp/d69-morning-audit-sixtyone.log`。新規ソース中の `sorry`・独自公理は0。
- 登録候補に `CrystallinePDRetractionNaturality`、`CrystallinePDRetractionSplit`、`CrystallineSmallBridgeModP` を加える。P2 は継続中で、整係数の橋との還元の照合と、完備化後の Witt の指定された二比較への適用を続ける。

- `CrystallineSmallBridge` で整係数の小さい結晶の橋を固定し、prism の生成元を p に送ることと、前項の mod p の射がこの厳密な射の還元であることを示した。鍵付き対象ビルドは `/private/tmp/d69-ticket-build-22.log` で成功した。95本の一時監査は2,499宣言、標準三公理のみ。監査は `/private/tmp/AuditD69P2MorningSixtyTwo.lean` と `/private/tmp/d69-morning-audit-sixtytwo.log`。
- 登録候補に `CrystallineSmallBridge` を加える。完備化後の擬同型へ進むため、共通の `CompleteCochainReduction` を作業木で検査している。これは二つの導来完備な複体の間の射を通常のスカラー商で判定する補題で、各項の正則性を仮定する。短完全列と写像錐の比較、既存の `DerivedPurity` の完備ホモロジーの零性判定を使う。

- 共通の `SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompleteCochainReduction` の対象ビルドが `/private/tmp/d69-ticket-build-23.log` で成功した。項ごとにスカラーが正則な二つの導来完備複体の射について、通常のスカラー商の擬同型から元の射の擬同型を導く。通常商を元の環の加群のまま束ね、短完全列、写像錐の関手との比較、既存の `cochain_quasiIso_iff_cone_acyclic` と `DerivedPurity` を使った。環上の平坦性は仮定しない。
- この共通モジュールも登録候補に加える。96本の一時監査は2,520宣言で標準三公理のみ。一時監査とログは `/private/tmp/AuditD69P2MorningSixtyThree.lean` と `/private/tmp/d69-morning-audit-sixtythree.log`。
- 作業木では `CrystallineSmallBridgeCoordinates`（各頂点変数の p 乗の式）と `CrystallineBridgeAlgebra`（既存の橋の ℤ_p 上の線形性）が個別検査を通った。`CrystallineWittCoefficients` は、既存の `arcPadicIntMap` とその一意性を使って Witt 基底への係数射を作る。これら3本は一つの整理券で対象ビルドを待っている。
- 次の適用では、既存の `toModules` と `cohomologyEquivModuleHomology` で環のコホモロジーと基底線形な複体を合わせ、小さい橋の通常商の擬同型に完備複体の判定を適用する。その後、affine 包の完備底変換の比較と分冪側の係数変更を使い、Witt の有限枠の指定された橋との可換図式を閉じる。Witt 側から C 側の比較には既存の第 0 列の自由模型と二射影の係数変更の可換性を使う。P2 の停止点には引き続き未到達。

- `CrystallineSmallBridgeCoordinates` の各頂点変数の p 乗の式と、`CrystallineBridgeAlgebra` の ℤ_p 上の厳密な線形性が鍵付きの対象ビルドを通った（`/private/tmp/d69-ticket-build-24.log`）。同じビルドの `CrystallineWittCoefficients` は証明だけに使う section 変数の明記で失敗したため、修正して個別検査を通した。基底の係数射は既存の `arcPadicIntMap` を使い、その一意性から Witt Frobenius と δ の両立を得る。Witt 係数射の再対象ビルドは次の束で行う。
- ビルド済みの追加2本を含む98本の一時監査は2,554宣言、標準三公理のみ。監査とログは `/private/tmp/AuditD69P2MorningSixtyFive.lean` と `/private/tmp/d69-morning-audit-sixtyfive.log`。登録候補に `CrystallineSmallBridgeCoordinates` と `CrystallineBridgeAlgebra` を加える。
- 次の7本の対象ビルドを、一つの整理券、`--wait 3600`、鍵の使用1700秒以内で流している（`/private/tmp/d69-ticket-build-25.log`）。上の2本、`CrystallineWittCoefficients`、`CrystallineSmallBridgeComplex`、共通の `SerrePositivity.HomologicalAlgebra.Cosimplicial.ModuleMap`・`ScalarQuotient`、`SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompleteScalarQuotient`。いずれも個別検査済み。
- `ModuleMap` は既存の `toModules` を射に移し、環のコホモロジー同型から線形な交代余面複体の擬同型を得る。`ScalarQuotient` は実際の環の商射に対応する線形複体の短完全列。`CompleteScalarQuotient` は、商複体を短完全列で指定した形の完備複体の判定と、整数添字への零延長の両立を示す。`CrystallineSmallBridgeComplex` で小さい橋の始域・終域・線形な余鎖射を固定し、両複体の零延長の導来 p 完備性を示した。

- 上記7本の対象ビルドは `/private/tmp/d69-ticket-build-25.log` で成功した。追加5本を含む103本の一時監査は2,619宣言で標準三公理のみ。監査とログは `/private/tmp/AuditD69P2MorningSeventy.lean` と `/private/tmp/d69-morning-audit-seventy.log`。新規ソース中の `sorry`・独自公理は0で、以前の宣言の型や証明の変更はない。
- 登録候補に `CrystallineWittCoefficients`、`CrystallineSmallBridgeComplex`、共通の `SerrePositivity.HomologicalAlgebra.Cosimplicial.ModuleMap`・`ScalarQuotient`、`SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompleteScalarQuotient` を加える。
- `CrystallineWittCoefficients` は、係数射の δ 両立と prism 射に加え、(p) の分冪構造から Witt 基底の分冪構造への両立も示した。ここでは既存の `PDFrobeniusLift` の階乗消去の補題を直接使った。
- `CompleteScalarQuotient` には自然数添字の入口も加えた。実際の通常商を短完全列で指定すれば、整数添字への零延長が導来完備な二つの複体の間の射について、商の射の擬同型から元の射の擬同型が従う。これを適用する `CrystallineSmallBridgeQuasiIso`（整係数の小さい結晶の橋の擬同型）は新規部品と合わせた個別検査を通り、通常の import で再検査中。
- 作業木の `PDEnvelopeCrystallineCoefficientMaps` は、係数環が異なる場合に分冪包の標準 δ 構造を保つことを示し、個別検査を通った。既存の基底固定の宣言はそのまま使える。次は、実際の小さい分冪模型の係数変更にこの補題を適用する。Witt 環の p 正則性から、標準 ℤ_p 作用の平坦性を示す `CrystallineWittFlat` も検査している。

- `CrystallineSmallBridgeQuasiIso`、`PDEnvelopeCrystallineCoefficientMaps`、`CrystallineWittFlat` の対象ビルドが `/private/tmp/d69-ticket-build-26.log` で成功した。小さい結晶の橋の実際の ℤ_p 線形余鎖射は擬同型となった。証明は通常商での既存の擬同型、両辺の導来 p 完備性、項ごとの p 正則性を使う。Witt 係数射の平坦性は、既存の p 進整数の単元と p の冪への分解と Witt 環の p 正則性から示した。
- 追加3本を含む106本の一時監査は2,645宣言で標準三公理のみ。監査とログは `/private/tmp/AuditD69P2MorningSeventyThree.lean` と `/private/tmp/d69-morning-audit-seventythree.log`。登録候補に上記3本を加える。既存宣言は変更していない。Witt の指定された比較射との係数変更の照合は引き続き残り、停止点2には未到達。

- `PDSmallCoefficientComparison` の対象ビルドが `/private/tmp/d69-ticket-build-27.log` で成功した。実際の小さい完備分冪模型の係数変更を一般の分冪基底上の完備分冪枠に移し、基底脚・頂点変数・分冪・標準 δ 構造との両立を示した。係数作用は η⁰ に対応する実際の環射に沿う作用として固定した。登録候補にこの一本を加える。
- 追加を含む107本の一時監査は2,690宣言で標準三公理のみ。監査とログは `/private/tmp/AuditD69P2MorningSeventyFour.lean` と `/private/tmp/d69-morning-audit-seventyfour.log`。新規ソースの `sorry`・独自公理は0、既存宣言の変更はない。
- 作業木では、`PDEnvelopeAffineBridge`（有限分冪枠への橋と係数変更の厳密な自然性）、`CrystallineSmallBridgeFrame`（既存の整係数の橋の有限枠での仕様）、`CrystallineWittSmallFrame`（Witt 結晶基底上の小さい橋）、`CrystallineWittSmallCoefficients`（整係数から Witt 係数への厳密な可換図式）、`WittFiniteBridgeCrystallineFactor`（既存の `finiteBridgeAt` の ψ に沿う係数変更を通る分解）が一時ファイルによる個別検査を通った。これらと、既存の `CompletedFlatRegularModule` を使う `CrystallineWittCompletedModules` を次の一件の整理券で対象ビルド中。対象ビルド前の新規ファイルはコミットしていない。
- 係数変更の順序は、まず整係数から Witt 結晶基底への標準 prism 射で小さい橋を移し、その後、一般の基底 P から ψ に沿って Witt 結晶基底へ移す。一般の P に対して結晶基底の生成元 p が P のイデアルに入るとは限らないため、整係数の affine 枠から P の affine 枠へ直接 prism 射を作る手順は使わない。Witt Frobenius 全体と、係数を固定して頂点を p 乗へ送る射も区別している。

- 上記の厳密な比較の5本（`PDEnvelopeAffineBridge`、`CrystallineSmallBridgeFrame`、`CrystallineWittSmallFrame`、`CrystallineWittSmallCoefficients`、`WittFiniteBridgeCrystallineFactor`）は `/private/tmp/d69-ticket-build-28.log` で対象ビルドを通った。112本の一時監査は2,850宣言で標準三公理のみ。監査とログは `/private/tmp/AuditD69P2MorningSeventyNine.lean` と `/private/tmp/d69-morning-audit-seventynine.log`。登録候補にこれら5本を加える。
- `crystallineWittSmallBridgeAt_coefficients` は整係数の実際の小さい橋と Witt 結晶基底上の橋の厳密な可換図式。`wittFiniteBridgeAt_eq_crystalline_comp` は既存の指定された有限 Witt 比較を、ψ による affine 係数変更と Witt 結晶基底の小さい橋の合成に同定する。両方とも有限 affine 包の一意性による等式で、元の比較射の定義は変更していない。
- 同じ束の `CrystallineWittCompletedModules` は p の像の型合わせで失敗したため、係数射による p の像の等式を直接書き換えて個別検査を通した。次の対象ビルドで再確認する。ほかに、`PDTermCompletelyFlat`、`CrystallineWittFlatCochain`、共通の `PointwiseBaseChange`・`PointwiseRegular` は個別検査済み。`AffineEnvelopeDerivedBaseChange` では、既存の完備自由 δ 環の完全平坦性と有界 prism 上の離散性から、実際の完備テンソルの single 対象が各 affine 項の完備導来底変換を計算する型を準備した。これら6本を `/private/tmp/d69-ticket-build-29.log` の一件の整理券で対象ビルドしている。
- P2 の残りは、これらの項の比較を余単体構造と合わせ、Witt の指定された二比較について、係数変更後の交代余面複体の擬同型を閉じること。各項への完備係数拡大と、複体全体への導来完備化は別に指定し、両者を同定する証明を省略しない。停止点2には引き続き未到達。

- `CrystallineWittCompletedModules` の修正と、`PDTermCompletelyFlat`、`CrystallineWittFlatCochain`、共通の `SerrePositivity.HomologicalAlgebra.DerivedCompletion.PointwiseBaseChange` は `/private/tmp/d69-ticket-build-29.log` で対象ビルドを通った。追加を含む116本の一時監査は2,887宣言で標準三公理のみ。監査とログは `/private/tmp/AuditD69P2MorningEightyThree.lean` と `/private/tmp/d69-morning-audit-eightythree.log`。登録候補にこの4本を加える。
- `pdTerm_completelyFlat` は基底の p 正則性を仮定し、未完備模型の自由な基底と既存の主完備化の完全忠実平坦性から (p) 完全平坦性を示す。`crystallineWittCompletedBridge_isIso` は、実際の整係数の小さい橋を通常の Witt 係数拡大と複体全体の導来完備化に移した射の可逆性。この段では各項の完備化との同定は使っていない。
- 共通の `PointwiseBaseChange` は、single・導来完備化・実際の H⁰ を合成した加法的な加群関手と、その通常の係数拡大との合成を固定する。元の鎖ホモトピーは既存の `Functor.mapHomotopy` で移る。
- 同じ対象ビルドで `AffineEnvelopeDerivedBaseChange` と共通の `PointwiseRegular` に残った、存在から同型を選ぶ書き方と import の問題は修正している。`PointwiseRegular` は通常の import での個別検査を通った。さらに `PointwiseExact`（両端が正則な短完全列を H⁰ 完備化が保つ）は一時ファイルによる個別検査を通った。これらは対象ビルドが通るまでコミットしない。

- `AffineEnvelopeDerivedBaseChange`、共通の `PointwiseRegular`・`PointwiseExact` の対象ビルドは `/private/tmp/d69-ticket-build-30.log` で成功した。追加を含む119本の一時監査は2,920宣言で標準三公理のみ。監査とログは `/private/tmp/AuditD69P2MorningEightySix.lean` と `/private/tmp/d69-morning-audit-eightysix.log`。登録候補にこの3本を加える。
- `affineEnvelopeTermCompletedBaseChangeIso` は、両基底が有界 prism という仮定の下で、有限 affine 項の実際の完備テンソル積の single 対象が二座標完備導来底変換を計算する。係数射そのものの通常の平坦性は仮定せず、既存の完備自由 δ 環の完全平坦性、有界 prism 上の離散性、H⁰ の係数線形な比較を使う。`affineEnvelopeTermCompletedBaseChangeToTargetIso` は既存の係数脚を保つ完備テンソルの同型を通して、標準の係数変更先の項へ移す。
- `PointwiseRegular` は加群上だけのスカラーの正則性から、主導来完備化の純性と H⁰ の正則性を示す。`PointwiseExact` は、両端でスカラーが正則な短完全列が H⁰ 完備化後も短完全であることを、標準導来三角形と長完全列で示す。
- 作業木の `PointwiseCochain` では、非輪状な正則複体のサイクルの短完全列を使い、各項の H⁰ 完備化が正則な複体の擬同型を保つことを個別検査で確認した。さらに平坦な通常の係数拡大と合成し、整数・自然数の両添字に対する入口を用意した。実際の整係数の小さい橋に適用する `CrystallineWittPointwiseBridge` も検査中。対象ビルド前なので、この2本はまだコミットしない。

- 共通の `PointwiseCochain`・`PointwiseAlgebra` と BS の `CrystallineWittPointwiseBridge` の対象ビルドは `/private/tmp/d69-ticket-build-31.log` で成功した。追加を含む122本の一時監査は2,948宣言で標準三公理のみ。監査とログは `/private/tmp/AuditD69P2MorningEightyNine.lean` と `/private/tmp/d69-morning-audit-eightynine.log`。登録候補にこの3本を加える。
- `PointwiseCochain` は、指定スカラーが各項で正則な非輪状複体をサイクルの短完全列に分け、各項の H⁰ 完備化後も非輪状であることを示す。写像錐の比較から擬同型の保存を得て、平坦な通常の係数拡大と合成した整数・自然数両添字の宣言を閉じた。`crystallineWittPointwiseBridge_quasiIso` は、実際の整係数の小さい橋にこの自然数添字の宣言を適用する。
- `PointwiseAlgebra` は各項の H⁰ 完備化を既存の主完備環の係数加群に同定する。標準の完備化単位を保ち、任意の係数線形写像について厳密に自然である。自然性の証明には既存の `principalCompletionLinearMap_ext` を使う。
- 次はこの同定と通常テンソルの係数を保つ比較を合わせ、各項の完備係数拡大を実際の有限 Witt 模型と照合する。作業木の `PointwiseTensor` でこの比較と単位の式を準備している。P2 の最終の二比較は引き続き残り、停止点2には未到達。

## P2 途中の取り込み点（2026-11-11 夕）

調整役の途中取り込みの依頼に対する記録。**停止点2の検収とは別の取り込み点**。

- **本体の取り込み点：`e79fa8e7c589288e5f523b5341723f36ca1e205d`（`e79fa8e7c`）**。
- 登録一覧の差分の基準は、この記録時点の main `7a3a0f965544bde84ff8e9d62359536d6d836430`（`7a3a0f965`）。追加は **89モジュール（BS 74本、共通15本）**。全89本が取り込み点にコミット済みで、対象ビルド済み。
- ⑤c の H3・H4 が待つ `AffineEnvelopeBaseChange`・`AffineEnvelopeCoefficients`・`AffineCechFrameLift`・`BigCechVertexFrame` は、4本ともこの取り込み点に含む。
- 本体の変更は新規ファイルのみ。枝と main の共通祖先 `7a689544b` から取り込み点まで、既存の本体ファイルの差分は0。入口・共通監査スクリプトへの登録は、この枝では変更していない。
- **未コミットの `SerrePositivity.HomologicalAlgebra.DerivedCompletion.PointwiseTensor` は対象外**。下の登録一覧にも監査対象にも含めない。

### ビルドと監査

- 対象ビルドは既記録の小さな束で検査済み。最新の束は `/private/tmp/d69-ticket-build-31.log` で成功。鍵はビルドの間だけ取り、`--wait 3600`、同じ worktree の整理券は常に一つにしている。
- **今回登録する追加89本だけの一時監査：1,802宣言、標準三公理 `propext`・`Classical.choice`・`Quot.sound` のみ**。一時監査 `/private/tmp/AuditD69P2IntermediateE79.lean`、ログ `/private/tmp/d69-intermediate-e79-audit.log`。
- 既取り込みの依存33本も含めた累計の一時監査は122モジュール・2,948宣言で、同じ標準三公理のみ。一時監査 `/private/tmp/AuditD69P2MorningEightyNine.lean`、ログ `/private/tmp/d69-morning-audit-eightynine.log`。
- 追加89本のソースを再走査し、`sorry`・独自の `axiom` 宣言は0。監査でも `sorryAx` と独自公理は検出されていない。

### BhattScholze.lean への登録（74本）

```text
SerrePositivity.BhattScholze.Delta.Division.HomExt
SerrePositivity.BhattScholze.Prismatic.AffineCechFrameLift
SerrePositivity.BhattScholze.Prismatic.AffineCechVertexFrame
SerrePositivity.BhattScholze.Prismatic.AffineEnvelopeBaseChange
SerrePositivity.BhattScholze.Prismatic.AffineEnvelopeBaseChangeCoefficients
SerrePositivity.BhattScholze.Prismatic.AffineEnvelopeCoefficients
SerrePositivity.BhattScholze.Prismatic.AffineEnvelopeDerivedBaseChange
SerrePositivity.BhattScholze.Prismatic.BigCechAffineFrameQuasiIso
SerrePositivity.BhattScholze.Prismatic.BigCechVertexFrame
SerrePositivity.BhattScholze.Prismatic.CechVertexHomotopy
SerrePositivity.BhattScholze.Prismatic.CompletedFreeDeltaScale
SerrePositivity.BhattScholze.Prismatic.CrystallineBridgeAlgebra
SerrePositivity.BhattScholze.Prismatic.CrystallinePDRetraction
SerrePositivity.BhattScholze.Prismatic.CrystallinePDRetractionNaturality
SerrePositivity.BhattScholze.Prismatic.CrystallinePDRetractionSplit
SerrePositivity.BhattScholze.Prismatic.CrystallineSmallBridge
SerrePositivity.BhattScholze.Prismatic.CrystallineSmallBridgeComplex
SerrePositivity.BhattScholze.Prismatic.CrystallineSmallBridgeCoordinates
SerrePositivity.BhattScholze.Prismatic.CrystallineSmallBridgeFrame
SerrePositivity.BhattScholze.Prismatic.CrystallineSmallBridgeModP
SerrePositivity.BhattScholze.Prismatic.CrystallineSmallBridgeQuasiIso
SerrePositivity.BhattScholze.Prismatic.CrystallineWittCoefficients
SerrePositivity.BhattScholze.Prismatic.CrystallineWittCompletedModules
SerrePositivity.BhattScholze.Prismatic.CrystallineWittFlat
SerrePositivity.BhattScholze.Prismatic.CrystallineWittFlatCochain
SerrePositivity.BhattScholze.Prismatic.CrystallineWittPointwiseBridge
SerrePositivity.BhattScholze.Prismatic.CrystallineWittSmallCoefficients
SerrePositivity.BhattScholze.Prismatic.CrystallineWittSmallFrame
SerrePositivity.BhattScholze.Prismatic.PDColumnCoefficientUnit
SerrePositivity.BhattScholze.Prismatic.PDColumnCompletedBaseChange
SerrePositivity.BhattScholze.Prismatic.PDColumnCompletionEquivalence
SerrePositivity.BhattScholze.Prismatic.PDCompletedSubstitutionNaturality
SerrePositivity.BhattScholze.Prismatic.PDDeRhamBicomplexCoefficients
SerrePositivity.BhattScholze.Prismatic.PDDeRhamCoefficientProjection
SerrePositivity.BhattScholze.Prismatic.PDDeRhamColumnBounded
SerrePositivity.BhattScholze.Prismatic.PDDeRhamCompletedBaseChange
SerrePositivity.BhattScholze.Prismatic.PDDeRhamCompletedSubstitution
SerrePositivity.BhattScholze.Prismatic.PDDeRhamDerivedSpan
SerrePositivity.BhattScholze.Prismatic.PDDeRhamRowFormsExt
SerrePositivity.BhattScholze.Prismatic.PDDeRhamSubstitutionChainRule
SerrePositivity.BhattScholze.Prismatic.PDDeRhamSubstitutionCofaces
SerrePositivity.BhattScholze.Prismatic.PDDeRhamSubstitutionDegreeZero
SerrePositivity.BhattScholze.Prismatic.PDDeRhamSubstitutionDifferential
SerrePositivity.BhattScholze.Prismatic.PDDeRhamSubstitutionForms
SerrePositivity.BhattScholze.Prismatic.PDDeRhamSubstitutionFunctor
SerrePositivity.BhattScholze.Prismatic.PDDeRhamSubstitutionGenerators
SerrePositivity.BhattScholze.Prismatic.PDDeRhamSubstitutionJacobian
SerrePositivity.BhattScholze.Prismatic.PDDeRhamSubstitutionWedge
SerrePositivity.BhattScholze.Prismatic.PDDeltaFrobeniusEvaluation
SerrePositivity.BhattScholze.Prismatic.PDEnvelopeAffineBridge
SerrePositivity.BhattScholze.Prismatic.PDEnvelopeCrystalline
SerrePositivity.BhattScholze.Prismatic.PDEnvelopeCrystallineCoefficientMaps
SerrePositivity.BhattScholze.Prismatic.PDEnvelopeCrystallineMaps
SerrePositivity.BhattScholze.Prismatic.PDModelCompletionQuotient
SerrePositivity.BhattScholze.Prismatic.PDRawBaseChangeQuotient
SerrePositivity.BhattScholze.Prismatic.PDRawColumnBaseChange
SerrePositivity.BhattScholze.Prismatic.PDRawColumnBoundedModel
SerrePositivity.BhattScholze.Prismatic.PDRawColumnCompletion
SerrePositivity.BhattScholze.Prismatic.PDRawFormsBaseChange
SerrePositivity.BhattScholze.Prismatic.PDRawPolynomialSubstitution
SerrePositivity.BhattScholze.Prismatic.PDRawRingHomExt
SerrePositivity.BhattScholze.Prismatic.PDSmallCoefficientComparison
SerrePositivity.BhattScholze.Prismatic.PDTermCompletelyFlat
SerrePositivity.BhattScholze.Prismatic.PDTermCompletionEquivalence
SerrePositivity.BhattScholze.Prismatic.PDTermQuotientModel
SerrePositivity.BhattScholze.Prismatic.PDTermReductionLinear
SerrePositivity.BhattScholze.Prismatic.PDTermRingHomExt
SerrePositivity.BhattScholze.Prismatic.PrismaticFrameHomotopy
SerrePositivity.BhattScholze.Prismatic.WittAffineBaseChange
SerrePositivity.BhattScholze.Prismatic.WittBigBridgeAffineFrame
SerrePositivity.BhattScholze.Prismatic.WittFiniteBridge
SerrePositivity.BhattScholze.Prismatic.WittFiniteBridgeCrystallineFactor
SerrePositivity.BhattScholze.Prismatic.WittFiniteBridgeNaturality
SerrePositivity.BhattScholze.Prismatic.WittFiniteBridgeSquare
```

### root への登録（共通15本）

```text
SerrePositivity.CommutativeAlgebra.DeRham.PolynomialDeRhamCompletionUnit
SerrePositivity.HomologicalAlgebra.BicomplexProjectionNaturality
SerrePositivity.HomologicalAlgebra.Cosimplicial.ModuleMap
SerrePositivity.HomologicalAlgebra.Cosimplicial.ScalarQuotient
SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompleteCochainReduction
SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompleteScalarQuotient
SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletedBaseChangeEquivalence
SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletedBaseChangeModel
SerrePositivity.HomologicalAlgebra.DerivedCompletion.PointwiseAlgebra
SerrePositivity.HomologicalAlgebra.DerivedCompletion.PointwiseBaseChange
SerrePositivity.HomologicalAlgebra.DerivedCompletion.PointwiseCochain
SerrePositivity.HomologicalAlgebra.DerivedCompletion.PointwiseExact
SerrePositivity.HomologicalAlgebra.DerivedCompletion.PointwiseRegular
SerrePositivity.HomologicalAlgebra.DerivedCompletion.PowerCokernelEquivalence
SerrePositivity.HomologicalAlgebra.DerivedCompletion.ScalarCokernelTensor
```

### P2 の残り

最後の二つの比較の検収は引き続き残る。各項の完備係数拡大と実際の有限 Witt 模型の同定を余単体構造に合わせ、指定された二比較の係数変更後の交代余面複体の擬同型を閉じる。この途中取り込みの後も作業を続け、P2 全体が対象ビルド・監査を通ったところで停止点2を報告する。

## P2 続行（2026-11-11 夜、途中取り込み後）

- 調整役の登録 `724b03fa2` を含む main `53ff00aa1` を fast-forward で取り込んだ。既存89本の入口・監査登録は main のものをそのまま使う。
- 共通の新規 `SerrePositivity.HomologicalAlgebra.DerivedCompletion.PointwiseTensor` と `SerrePositivity.HomologicalAlgebra.DerivedCompletion.TensorCompletionUnit` が対象ビルドを通った（`/private/tmp/d69-ticket-build-32.log`・`/private/tmp/d69-ticket-build-33.log`）。鍵は `--wait 3600`、各ビルドの間だけ保持した。
- `PointwiseTensor` は各項の H⁰ 完備係数拡大を通常テンソル環の主完備化と線形に同定し、単位と代数射についての自然性を示す。`TensorCompletionUnit` はテンソルの一方の主完備化単位が、全体の主完備化後に左係数上の代数同型になることと厳密な自然性を示す。この環の同型には平坦性を仮定しない。各項が導来底変換を計算するための正則性・完全平坦性とは分けて使う。
- 一時監査は124モジュール・3,005宣言、標準三公理のみ。`/private/tmp/AuditD69P2MorningNinetyOne.lean`、ログ `/private/tmp/d69-morning-audit-ninetyone.log`。今回の登録候補追加は上記の共通2本。入口・共通監査の登録は変更していない。
- Nakayama の整理候補：⑤c の `HomologicalAlgebra.CochainCompleteDetection.cochain_homology_isZero_of_complete_of_scalarCone_isZero` に、⑤b の `CompleteCochainReduction` が持つ正則な通常商とスカラー錐の比較を組み合わせれば、通常商版の証明を同じ入口へ寄せられる見込み。現段階では両ファイルを変更せず、停止点2で再確認する。
- 最後の二比較は引き続き未完了。実際の小さい分冪項の完備テンソル同型と、有限・大きい Witt の射を余面構造まで合わせる。

- 続いて `PDTermCompletedTensor`・`PDTermPointwiseCoefficients` と共通の `SerrePositivity.HomologicalAlgebra.DerivedCompletion.RepeatedPrincipalRing` が対象ビルドを通った（`/private/tmp/d69-ticket-build-34.log`・`/private/tmp/d69-ticket-build-35.log`、鍵は待ち3600秒、ビルド中のみ）。登録候補に BS 2本・共通1本を追加する。
- `pdTermCompletedTensorAlgEquiv` は、任意の係数代数について、小さい完備分冪項の通常テンソルの主完備化を係数変更後の項に同定する。`pdTermCompletedTensorAlgEquiv_coefficient` は右脚が既存の `pdModelBaseChange` そのものであることを示す。公開型で関手の内部の定義展開を要求しないよう、新規の型付き入口 `pdTermCoefficientRingHom` を使った。
- `pdTermPointwiseCoefficientIso` とその単位の式は、加群の各項の完備係数拡大関手から実際の分冪項への線形同型と右脚を固定する。`repeatedPrincipalAlgEquiv` は二座標 (p,p) の H⁰ を主完備環に、元の環上で単位を保って同定する。いずれの環の同型にも正則性や平坦性を追加していない。
- 追加を含む一時監査は127モジュール・3,040宣言、標準三公理のみ。`/private/tmp/AuditD69P2MorningNinetyFour.lean`、ログ `/private/tmp/d69-morning-audit-ninetyfour.log`。ここまでの新規5本に `sorry`・独自の公理はなく、既存宣言の変更もない。停止点2の二比較の検収は引き続き残る。

- `CrystallineCompletedTensor`・`AffineEnvelopePointwiseCoefficients` の対象ビルドも成功した（`/private/tmp/d69-ticket-build-36.log`・`/private/tmp/d69-ticket-build-37.log`）。登録候補に BS のこの2本を追加する。
- 前者は生成元が p である終域で二座標完備テンソルを通常テンソルの p 完備化に、左右の脚を保って同定する。後者は両基底を有界 prism と仮定し、既存の affine 包の係数底変換同型を通して、実際の有限 affine 項を各項の完備係数拡大と同定する。右脚が指定済みの `affineEnvelopeCoefficientMap` となる式も含む。
- 一時監査は129モジュール・3,067宣言、標準三公理のみ。`/private/tmp/AuditD69P2MorningNinetySix.lean`、ログ `/private/tmp/d69-morning-audit-ninetysix.log`。入口・監査登録と既存宣言は変更していない。

- `PDTermPointwiseNaturality`・`PDCompletedCoefficientComplex` と、共通の `SerrePositivity.HomologicalAlgebra.DerivedCompletion.PointwiseTensorExt`・`SerrePositivity.HomologicalAlgebra.Cosimplicial.MapComplex` の対象ビルドが成功した（`/private/tmp/d69-ticket-build-38.log`・`/private/tmp/d69-ticket-build-39.log`）。登録候補に BS 2本・共通2本を追加する。
- `pdTermPointwiseCoefficientIso_naturality` はすべての単体の構造射について厳密な自然性を示す。`pdCechPointwiseCoefficientIso` は実際の `pdCechRings` の台加群の余単体的同型、`pdCompletedCoefficientComplexIso` は小さい分冪交代余面複体へ各項の H⁰ 完備係数拡大を適用した標準の比較同型。複体全体の完備導来テンソルとの同定を暗黙に使っていない。
- 共通の `PointwiseTensorExt` は完備な標的への線形射を純テンソルの単位上で判定し、係数拡大した任意の加群射について単位の自然性を示す。`MapComplex` は加法的関手を各項に適用する操作と交代余面複体との交換同型を固定する。
- 一時監査は133モジュール・3,098宣言、標準三公理のみ。`/private/tmp/AuditD69P2MorningHundred.lean`、ログ `/private/tmp/d69-morning-audit-hundred.log`。対象ビルド済みの追加11本に sorry・独自公理はなく、既存宣言の変更も0。Witt の指定された二比較の最終的な検収は残っており、この記録を停止点2の報告とはしない。

- `AffineCechPointwiseCoefficients`・`CrystallineWittTransportedBridge` の対象ビルドが成功した（`/private/tmp/d69-ticket-build-40.log`・`/private/tmp/d69-ticket-build-41.log`）。登録候補に BS のこの2本を追加する。
- 前者は、各項の比較を実際の `htRings` の台加群の余単体的同型へ組む。後者は、この affine 側の同型と分冪側の同型を通して、既存の整係数の橋を実際の Witt affine・分冪交代余面複体の間へ移し、その射が擬同型であることを示す。指定された `crystallineWittSmallBridgeAt` との各次数の照合は、次の新規ファイルで続けている。
- 一時監査は135モジュール・3,135宣言、標準三公理のみ。`/private/tmp/AuditD69P2MorningHundredTwo.lean`、ログ `/private/tmp/d69-morning-audit-hundredtwo.log`。対象ビルド済みの追加13本はすべて新規ファイルで、入口・監査登録・既存宣言の変更はない。停止点2にはまだ達していない。

- `CrystallineWittBridgeAgreement`・`WittFiniteCompletedBridge` と共通の `SerrePositivity.HomologicalAlgebra.DerivedCompletion.PointwiseExtension` が対象ビルドを通った（`/private/tmp/d69-ticket-build-42.log`〜`/private/tmp/d69-ticket-build-44.log`。整形後も44の束で確認済み）。登録候補に BS 2本・共通1本を追加する。
- `crystallineWittTransportedBridge_f` は移した橋の各次数の射が、指定された `crystallineWittSmallBridgeAt` を線形に読んだ射そのものであることを示す。係数変更の既存の正方形と、完備係数拡大からの射の一意性で証明した。
- `wittFiniteCompletedBridge_quasiIso` は一般の有界 prism から ψ で係数を変えた有限橋の擬同型。`wittFiniteCompletedBridge_unit` は純テンソルの単位上で既存の `WittFiniteBridge.finiteBridgeAt` を延長することを固定する。各項の完備テンソルが導来底変換を計算する入力は既存の `affineEnvelopeTermCompletedBaseChangeToTargetIso` を使う。単位の式一つに限り定義照合の再帰深さを1500にしており、heartbeat の全体的な変更はしていない。
- `PointwiseExtension` は完備な標的への半線形代数射の標準線形延長・純テンソルの単位の式・可換な正方形に対する厳密な自然性を与える。大きい枠の二比較を同じ延長で扱うための共通部品。
- 一時監査は138モジュール・3,209宣言、標準三公理のみ。`/private/tmp/AuditD69P2MorningHundredFive.lean`、ログ `/private/tmp/d69-morning-audit-hundredfive.log`。今回の追加まで本体16本（BS 10本、共通6本）は新規ファイルのみで、sorry・独自公理0。既存宣言・入口・監査登録は変更していない。
- 残り：大きい affine／分冪枠の鎖ホモトピー同値を延長後の二比較に合わせ、β と `wittToSmall` の大きい模型での検収を閉じる。有限橋の検査が通ったことだけでは停止点2とはしない。

- 共通の `SerrePositivity.HomologicalAlgebra.Cosimplicial.CompletedCoefficientMap` が対象ビルドを通った（`/private/tmp/d69-ticket-build-45.log`）。登録候補の共通部品にこの1本を追加する。
- `completedCoefficientMap` は、係数の構造射を保つ半線形な余単体環射を、各項の完備係数拡大後の線形余単体射へ延長する。標的の各項の p 完備性を型に置く。`completedCoefficientMap_unit` は純テンソルの単位上で元の半線形射を与え、`completedCoefficientCochainMap` は実際の交代余面複体の射を固定する。
- 一時監査は139モジュール・3,223宣言、標準三公理のみ。`/private/tmp/AuditD69P2MorningHundredSix.lean`、ログ `/private/tmp/d69-morning-audit-hundredsix.log`。追加17本（BS 10本・共通7本）まで対象ビルド・監査済み、既存宣言は変更していない。


## 停止点2：P2 完了（2026-11-11、途中取り込み後の最終検収）

### 取り込み点と検収

- 本体の取り込み点：`07e636bad`（`math/bs-d68`）。前回の途中取り込み `e79fa8e7c` と報告 `d19a6e362`、main の登録 `724b03fa2` は、今回開始時の main `53ff00aa1` の取り込みで反映済み。
- 今回の追加は26モジュール（BS 19本・共通7本）、すべて新規ファイル。既存の宣言・入口・公式監査スクリプトの変更は0。drafts の他レーンの持ち分にも変更はない。
- 新規26本を一つの対象ビルドで検査し成功：`/private/tmp/d69-ticket-build-54.log`（4,853 jobs）。`scripts/refactor/with_build_lock.sh --wait 3600 -- /opt/homebrew/bin/gtimeout --kill-after=5s 1700s lake build …` を使い、鍵はビルドの間だけ保持した。最後の模型の単独ビルドは53のログにもある。ルートビルドは行っていない。
- ビルド後の一時監査：今回の新規26本・479宣言、標準三公理 `propext`・`Classical.choice`・`Quot.sound` のみ（`/private/tmp/AuditD69P2New26.lean`、`/private/tmp/d69-new26-audit.log`）。
- P2 の検査範囲を含む一時監査：148モジュール・3,427宣言、同じ標準三公理のみ（`/private/tmp/AuditD69P2Final.lean`、`/private/tmp/d69-final-audit.log`）。これは当レーンの対象監査であり、調整役の段階II全体の監査12,644宣言とは範囲が異なる。
- 新規26本のソース検査でも `sorry`・独自の公理宣言は0。`git diff --check` も通過した。公式の入口・監査への登録は調整役にお願いする。

### 最後の二比較と導来計算

1. `CechFrameAdditiveQuasiIso` と `WittSmallFrameAdditiveQuasiIso` は、有限・大きい枠の比較を任意の加法的関手の各項への適用後にも鎖ホモトピー同値で扱う。前回の取り込み点で検査済みの prismatic な枠の二合成の鎖ホモトピーを再利用した。
2. `CompletedCechCoefficientMap` と `WittFiniteCompletedCechBridge` は、指定された半線形な余単体射の完備係数拡大を固定する。純テンソルの単位上で元の射を与える式と、可換な正方形に対する厳密な自然性を持つ。
3. `WittBigCompletedBridge.wittBigCompletedBridge_quasiIso` は、指定された β（`wittBigBridge`）の係数変更後の擬同型。有限橋の係数変更後の擬同型、有限・大きい枠の比較、および実際の橋の正方形で示した。`wittBigCompletedBridge_naturality` は Poly 上の厳密な自然性。
4. `PDCompletedCechBaseChange` と `WittToSmallCompletedBridge.wittToSmallCompletedBridge_quasiIso` は、指定された第二比較（`wittToSmall`）の完備係数変更後の擬同型。有限分冪模型での係数変更同型と枠の比較を使う。`wittToSmallCompletedBridge_naturality` も Poly 上で厳密。
5. 各項の導来計算は、第一比較の有限項では既存の `affineEnvelopeTermCompletedBaseChangeToTargetIso`、大きい項では新規 `BigCechDerivedBaseChange.bigCechTermCompletedDerivedBaseChangeIso` と `bigCechTermPointwiseDerivedBaseChangeIso` を使う。基底の boundedness と元の項の完全平坦性を型・証明に持ち、後者を `affineBigCechTerm_completelyFlat` で示した。
6. 第二比較の実際の完備導来底変換は、設計 §10.5.5–7 に従い `WittPDCompletedDerivedModel` に分けた。大きい Witt 分冪模型から総複体の二射影と枠の比較を通して第0列へ移す。未完備第0列の上に有界な射影模型に通常の導来底変換を適用し、p 完備化する。`wittToSmallDerivedCompletedIso` が小さい分冪 Čech 模型への導来同型、`wittToSmallDerivedModel_projective` が各項の射影性、`wittToSmallDerivedCompletedColumnIso_model_comm` が実際の自由模型の係数射と完備化後の比較の可換式である。p 正則性と完備性も既存の列の比較の仮定として明示した。

各項の H⁰ 完備係数拡大による古典的な複体の比較と、第二比較の完備導来底変換の計算を区別している。後者には有限な射影列を使い、大きい分冪項すべてについて H⁰ の各項の操作だけで導来底変換を計算すると主張していない。完備 pd de Rham の多項式代入と総複体から第0行・第0列への二射影の厳密な自然性は、前回の途中取り込み点で検査済みの部品を使う。

以上で P2 の厳密な模型の段を完了した。Tot の E∞ 構造、関手としての同型への組み立て、RΓ_crys の定義は指示どおり drafts の範囲に残る。CAlg_R の模型の内部への新規参照は追加していない。

### 共通補題の整理候補

`CompleteCochainReduction` の通常商版は、⑤c の `CochainCompleteDetection.cochain_homology_isZero_of_complete_of_scalarCone_isZero` と、こちらの正則な通常商・スカラー錐の比較を組み合わせる形に寄せられる見込みであり、今回は両ファイルを変更していない。

### 今回追加分の登録一覧

前回登録済みの89本とは別に、以下の26本を登録する。

BhattScholze.lean（19本）：

```text
SerrePositivity.BhattScholze.Prismatic.AffineCechPointwiseCoefficients
SerrePositivity.BhattScholze.Prismatic.AffineEnvelopePointwiseCoefficients
SerrePositivity.BhattScholze.Prismatic.BigCechDerivedBaseChange
SerrePositivity.BhattScholze.Prismatic.CechFrameAdditiveQuasiIso
SerrePositivity.BhattScholze.Prismatic.CompletedCechCoefficientMap
SerrePositivity.BhattScholze.Prismatic.CrystallineCompletedTensor
SerrePositivity.BhattScholze.Prismatic.CrystallineWittBridgeAgreement
SerrePositivity.BhattScholze.Prismatic.CrystallineWittTransportedBridge
SerrePositivity.BhattScholze.Prismatic.PDCompletedCechBaseChange
SerrePositivity.BhattScholze.Prismatic.PDCompletedCoefficientComplex
SerrePositivity.BhattScholze.Prismatic.PDTermCompletedTensor
SerrePositivity.BhattScholze.Prismatic.PDTermPointwiseCoefficients
SerrePositivity.BhattScholze.Prismatic.PDTermPointwiseNaturality
SerrePositivity.BhattScholze.Prismatic.WittBigCompletedBridge
SerrePositivity.BhattScholze.Prismatic.WittFiniteCompletedBridge
SerrePositivity.BhattScholze.Prismatic.WittFiniteCompletedCechBridge
SerrePositivity.BhattScholze.Prismatic.WittPDCompletedDerivedModel
SerrePositivity.BhattScholze.Prismatic.WittSmallFrameAdditiveQuasiIso
SerrePositivity.BhattScholze.Prismatic.WittToSmallCompletedBridge
```

root（共通7本）：

```text
SerrePositivity.HomologicalAlgebra.Cosimplicial.CompletedCoefficientMap
SerrePositivity.HomologicalAlgebra.Cosimplicial.MapComplex
SerrePositivity.HomologicalAlgebra.DerivedCompletion.PointwiseExtension
SerrePositivity.HomologicalAlgebra.DerivedCompletion.PointwiseTensor
SerrePositivity.HomologicalAlgebra.DerivedCompletion.PointwiseTensorExt
SerrePositivity.HomologicalAlgebra.DerivedCompletion.RepeatedPrincipalRing
SerrePositivity.HomologicalAlgebra.DerivedCompletion.TensorCompletionUnit
```

段階IIの監査には上記26本を追加する。一時監査には非公開の補助宣言も含めた。P3 の紙の整理と朝に回す順序は、この報告の先の段0相当の節を引き継ぐ。


## P3 続行（2026-11-11 夜、停止点2の取り込み後）

- 調整役の指示に従い main `cba436208` へ fast-forward した。夜間二鍵のスクリプトを反映済み。Nakayama の `CompleteCochainReduction`・`CochainCompleteDetection` は変更していない。
- 対象ビルド済みの新規10本は下記（BS 9本・共通1本）。`/private/tmp/d69-p3-build-4.log` と `/private/tmp/d69-p3-build-5.log` が成功。鍵は `--wait 3600`、一回30分未満で、ビルドの間だけ保持した。
- 基本部品は big affine 結晶厚化の対象・射・圏、基底の下の台環関手、剰余環への誘導射、剰余代数に沿う引き戻しと厳密な関手則、分冪基底の制限を含む。有限主開局所化による Zariski 被覆族と生成位相を定義し、二つの制限関手が被覆族を保つことを示した。
- `CrystallineTransport` は代数同型に沿う分冪厚化の移送と厚化の同型。`CrystallineSiteSmall` は κ の代表型の部分集合に構造を移して、濃度 ≤ κ の厚化の圏の本質的小ささを証明した。この本質的小ささだけなら cutoff の下限は不要。`CrystallineSmallSiteTopology` で、小さい模型のサイト・生成位相・構造環の前層・引き戻しの圏の関手を定めた。構造環の層性はまだ主張していない。
- `CrystallinePDQuotient` は p^{e+2} による商を実際の結晶厚化にする。指数を2から取る理由を docstring に記録した。共通の `ProCechNerveData` は通常の圏での塔・pro 弱終性・各段の有限冪・二重添字関手と、圏同値による pro 弱終性の移送を与える。∞ の極限には触れない。
- 一時監査は10モジュール・217宣言、標準三公理のみ（`/private/tmp/AuditD69P3Ten.lean`、`/private/tmp/d69-p3-audit-ten.log`）。新規ファイルのみ、sorry・独自公理0、既存宣言と公式の入口・監査への変更は0。
- P3 の残り：分冪包の有限冪商の塔・余積・pro 弱終性、主開局所化の分冪構造と構造環の層性、サイトの引き戻しと位相・構造環との照合、多項式 Poincaré の複体比較を実際の塔に接続する。以下は途中記録で、停止点3ではない。

登録候補（10本、未登録）：

```text
SerrePositivity.BhattScholze.Prismatic.CrystallinePDQuotient
SerrePositivity.BhattScholze.Prismatic.CrystallineSmallSiteTopology
SerrePositivity.BhattScholze.Prismatic.CrystallineSiteSmall
SerrePositivity.BhattScholze.Prismatic.CrystallineTransport
SerrePositivity.BhattScholze.Prismatic.CrystallineSiteBasic
SerrePositivity.BhattScholze.Prismatic.CrystallineSitePullback
SerrePositivity.BhattScholze.Prismatic.CrystallineResidue
SerrePositivity.BhattScholze.Prismatic.CrystallineSiteZariski
SerrePositivity.BhattScholze.Prismatic.CrystallineBaseRestriction
SerrePositivity.CategoryTheory.ProCechNerveData
```


### P3 続行 — 商の塔と多項式 span

- `f76aaed51` の10本に続き、新規8本が対象ビルドを通過（`/private/tmp/d69-p3-build-6.log`〜`/private/tmp/d69-p3-build-8.log`）。追加後の一時監査は18モジュール・317宣言、標準三公理のみ（`/private/tmp/AuditD69P3Eighteen.lean`、`/private/tmp/d69-p3-audit-eighteen.log`）。
- `CrystallinePDQuotientLift` は指定した p 冪を消す分冪射を有限冪商からの実際の厚化の射に降ろす。`CrystallinePDQuotientTower` はすべての遷移射の代表元の式と関手則、環・サイトの二つの向きの塔を与える。元の分冪環から任意の厚化への持ち上げがあれば、その塔が pro 弱終であることも示した。これを枠の分冪包へ適用する具体的な最後の宣言は引き続き検査中。
- `CrystallineNilpotentComplete` は既存の `Adic.Complete.isAdicComplete_of_pow_le` を再利用し、任意の結晶厚化の p 完備性を示す。`CrystallineFrameLift` は任意の厚化へ枠の変数を選んで持ち上げ、完備分冪包の普遍性で分冪射を作る。持ち上げ・既存の増強・剰余構造射の正方形も環射の等式で証明した。
- `CrystallineResidueAlgebra` は k/J 代数を基底環上で読む標準構造と核条件。`PDCechResidueEquivalence` は全射な枠の分冪包の剰余同型と、既存の増強との一致。`PDCechCrystallineQuotient` はこの同型の逆を構造射にして、各項の有限冪商を実際の結晶厚化にする。各項の濃度の上限は明示的に仮定する。
- `CrystallinePolynomialSpan` は P1 の枠との同型を P2 の第0行への射影に合成して、実際の分冪 Čech 複体への射影と擬同型を得る。もう一方の脚は既存の `pdDeRhamTotalToCompletedForms` とその擬同型定理。草稿と同じく基底の p 完備性・p 正則性と分冪の p 上の条件を明示する。RΓ の形には組み立てていない。
- 作成中に剰余同型の仮のファイル名が既存の D68 の `CrystallineCechResidue.lean` と一致したため、既存ファイルは HEAD の内容へ完全に戻し、新規分を `PDCechResidueEquivalence.lean` へ移した。最終差分では既存ファイルの変更は0。
- 追加8本も新規ファイルのみで、sorry・独自公理0。Nakayama の二ファイル、公式の入口・監査は変更していない。P3 の停止点3にはまだ達していない。

登録候補への追加（BS 8本）：

```text
SerrePositivity.BhattScholze.Prismatic.CrystallineFrameLift
SerrePositivity.BhattScholze.Prismatic.CrystallineNilpotentComplete
SerrePositivity.BhattScholze.Prismatic.CrystallinePDQuotientLift
SerrePositivity.BhattScholze.Prismatic.CrystallinePDQuotientTower
SerrePositivity.BhattScholze.Prismatic.CrystallinePolynomialSpan
SerrePositivity.BhattScholze.Prismatic.CrystallineResidueAlgebra
SerrePositivity.BhattScholze.Prismatic.PDCechCrystallineQuotient
SerrePositivity.BhattScholze.Prismatic.PDCechResidueEquivalence
```


### P3 続行 — 具体的な零次の塔の pro 弱終性

- `CrystallineCechProWeakTerminal` の対象ビルドが成功（`/private/tmp/d69-p3-build-9.log`）。`pdCechTowerZero_proWeaklyTerminal` は、全射な枠の分冪包の有限冪商の塔について、任意の厚化の p 冪零指数で射を降ろして具体的に証明した。`pdCechSmallTowerZero_proWeaklyTerminal` が小さい模型での同じ宣言。基底の係数構造の両立と、零次の包の濃度が κ に入る仮定を型に持つ。
- `CrystallinePDQuotientMap` と `PDCechResidueNaturality` の対象ビルドも成功（`/private/tmp/d69-p3-build-10.log`）。前者は任意の分冪射を同じ指数の有限冪商の厚化の射へ降ろす。後者は任意の頂点写像が剰余同型とその逆の構造射を保つことを、増強の自然性で示す。
- 一時監査は21モジュール・376宣言、標準三公理のみ（`/private/tmp/AuditD69P3TwentyOne.lean`、`/private/tmp/d69-p3-audit-twentyone.log`）。今回の3本にも sorry・独自公理0。既存宣言・Nakayama の二ファイル・公式登録は変更していない。
- 残りは全 Čech 項の余単体的対象と有限段の余積への接続、分冪包の濃度評価、局所化・構造環の層性など。全 Čech 項の組み立てと指定変数像の延長の存在一意性は作業木で検査中。この記録は停止点3ではない。

登録候補への追加（BS 3本）：

```text
SerrePositivity.BhattScholze.Prismatic.CrystallineCechProWeakTerminal
SerrePositivity.BhattScholze.Prismatic.CrystallinePDQuotientMap
SerrePositivity.BhattScholze.Prismatic.PDCechResidueNaturality
```


### P3 続行 — 全 Čech の塔・各段の有限冪・cutoff

- `5dad04fc8` の21本に続き、新規12本（BS 10本・共通2本）が対象ビルドを通過した（`/private/tmp/d69-p3-build-11.log`〜`/private/tmp/d69-p3-build-17.log`）。一回30分未満、`--wait 3600`、鍵はビルドの間のみ。夜の二鍵は main から取り込んだスクリプトに任せた。
- `CrystallineFrameVariablesLift`・`CrystallineFrameLiftResidue`・`PDCechCrystallineVertices`・`PDCechQuotientVariablesLift` は、指定した全頂点の変数像を厚化の射へ一意に延ばす。分冪包の普遍性、剰余の正方形、指定 p 冪の消滅、変数上での射の判定を明示した。
- `PDCechCrystallineCosimplicial` は各有限 p 冪商を実際の余単体的な厚化の対象にする。`PDCechCrystallineCoproduct.pdCechQuotient_isCoproduct` が、標準頂点の脚による n 次項の余積の普遍性。標的の p 冪の消滅は零次項からの射一本から得た。`pdCechQuotientCechData` は反対圏で指定した有限冪を持つ Čech データ。
- `PDCechCrystallineTower` は遷移の余単体的自然性、二重添字の `pdCechTower`、射影と遷移の両立を含む `pdCechTowerProCechData` を構成した。通常の圏論だけであり、pro 対象の ∞ の極限は作っていない。
- `PDEnvelopeCardinality` は有限分岐の構文木から相対分冪包の形式項への全射を作り、未完備包の濃度を入力環と可算濃度で抑える。共通の `Adic.Cardinality` は古典的な完備化から元の加群の可算列への単射を作る。`CompletedPDEnvelopeCardinality` が両者を接続し、Čech 全項を標準の `cutoff k R` で抑える。
- 濃度条件の精密化：枠の変数は `#S ≤ #k + #R + ℵ₀` としてから包を完備化し、最後に `cutoff k R ≤ κ` を適用する。一般の `#S ≤ κ` だけから κ^ℵ₀=κ を推論してはいない。標準の枠 S=R と有限多項式枠はこの精密化した条件を満たす。既存の `IsCrystallineCutoff` の型は変更しない。
- 共通の `ProCechNerveTransport` は各段の有限冪を保つ関手による pro Čech データの移送。`CrystallineCechCutoff` の `pdCechTowerOfCutoff`・`pdCechProCechDataOfCutoff`・`pdCechSmallTowerOfCutoff_proWeaklyTerminal` は包の濃度を別に仮定せず、cutoff から小さい結晶サイトの塔と各段の Čech データを供給する。
- 一時監査は33モジュール・462宣言、標準三公理のみ（`/private/tmp/AuditD69P3ThirtyThree.lean`、`/private/tmp/d69-p3-audit-thirtythree.log`）。追加12本も新規ファイルだけで、sorry・独自公理0。既存宣言・Nakayama の二ファイル・公式の入口・監査は変更していない。
- 残り：主開局所化の分冪構造、Zariski 位相と引き戻しの照合、構造環の層性と係数制限の自然性、当初の P3 の模型・η の照合の残件を確認する。主開局所化の分数公式と構造前層の引き戻しは作業木で検査中。この記録は停止点3ではない。

登録候補への追加（12本）：

```text
SerrePositivity.BhattScholze.Prismatic.CompletedPDEnvelopeCardinality
SerrePositivity.BhattScholze.Prismatic.CrystallineCechCutoff
SerrePositivity.BhattScholze.Prismatic.CrystallineFrameLiftResidue
SerrePositivity.BhattScholze.Prismatic.CrystallineFrameVariablesLift
SerrePositivity.BhattScholze.Prismatic.PDCechCrystallineCoproduct
SerrePositivity.BhattScholze.Prismatic.PDCechCrystallineCosimplicial
SerrePositivity.BhattScholze.Prismatic.PDCechCrystallineTower
SerrePositivity.BhattScholze.Prismatic.PDCechCrystallineVertices
SerrePositivity.BhattScholze.Prismatic.PDCechQuotientVariablesLift
SerrePositivity.BhattScholze.Prismatic.PDEnvelopeCardinality
SerrePositivity.CategoryTheory.ProCechNerveTransport
SerrePositivity.CommutativeAlgebra.Adic.Cardinality
```


### P3 続行 — 主開局所化・分冪・Zariski coverage

- 新規9本（すべて BS）が鍵付きの対象ビルドを通過した（`/private/tmp/d69-p3-build-19.log`〜`/private/tmp/d69-p3-build-21.log`）。`--wait 3600`、一回30分未満、鍵はビルドの間のみ。
- `PDLocalizationDpow`・`PDLocalizationLaws`・`PDLocalizationAddition`・`PDLocalizationStructure` は、分数の分子の分冪を分母の n 乗で割る公式から、任意の局所化に分冪構造を作る。代表によらないこと、和・積・反復分冪を証明し、存在一意性と、元の環からの合成で分冪射であることを判定する補題まで閉じた。
- `CrystallineSiteLocalization` は、分冪構造・p 冪零・剰余構造射・濃度を保つ標準主開厚化と標準射。`CrystallineLocalizationLift` は任意の主開局所化模型からの延長と合成の等式、射の一意性。
- `CrystallineZariskiRefinement` は任意の厚化の射に沿った被覆を標準主開被覆で細分する。`CrystallineZariskiCoverage` はこの細分で coverage の公理を証明し、以前の sInf による結晶 Zariski 位相と一致することを示す。一般の厚化の引き戻し対象の存在を仮定しない。
- `CrystallineStructurePullback` は小さい模型の構造前層をサイトの引き戻しで制限したものと、元の構造前層との自然同型。同値の単位同型から構成した通常の環値の自然同型であり、∞ の辺にはしていない。
- 一時監査は42モジュール・531宣言、標準三公理のみ（`/private/tmp/AuditD69P3FortyTwo.lean`、`/private/tmp/d69-p3-audit-fortytwo.log`）。今回の9本にも sorry・独自公理0。既存宣言・Nakayama の二ファイル・公式登録は変更していない。
- 残り：主開被覆での環の貼り合わせを結晶構造前層の層条件に接続し、小さいサイト・引き戻し・係数制限を照合する。共通の局所化の貼り合わせ補題は個別検査済みだが、対象ビルド前なので本コミットに含めない。この記録は停止点3ではない。

登録候補への追加（BS 9本）：

```text
SerrePositivity.BhattScholze.Prismatic.CrystallineLocalizationLift
SerrePositivity.BhattScholze.Prismatic.CrystallineSiteLocalization
SerrePositivity.BhattScholze.Prismatic.CrystallineStructurePullback
SerrePositivity.BhattScholze.Prismatic.CrystallineZariskiCoverage
SerrePositivity.BhattScholze.Prismatic.CrystallineZariskiRefinement
SerrePositivity.BhattScholze.Prismatic.PDLocalizationAddition
SerrePositivity.BhattScholze.Prismatic.PDLocalizationDpow
SerrePositivity.BhattScholze.Prismatic.PDLocalizationLaws
SerrePositivity.BhattScholze.Prismatic.PDLocalizationStructure
```


### P3 続行 — 構造環の層性と小さいサイトの二つの関手

- 新規7本（BS 5本・共通2本）が鍵付きの対象ビルドを通過した（`/private/tmp/d69-p3-build-22.log`・`/private/tmp/d69-p3-build-23.log`）。`--wait 3600`、一回30分未満、鍵はビルドの間のみ。
- 共通の `AwayGluing` は任意の主開局所化模型に対する一意な貼り合わせ。添字の重複も許し、標準の主開局所化への比較を通して Mathlib の環の貼り合わせ定理へ帰着した。`AwayEquivalence` は可換な同型の正方形による局所化条件の移送。
- `CrystallineStructureGluing` は、共通主開の実際の結晶厚化への射で両立性を検査して、大きいサイトの型値の構造前層が層であることを示す。`CrystallineSmallStructureSheaf.crystallineStructure_isSheaf` は小さいサイトでの基底環の下の環値の層条件。生成位相を同値による誘導位相で抑え、型値の層性を移し、忘却関手の極限反映で環構造を戻す。
- `CrystallineBaseStructureRestriction` は分冪基底射に沿う小さいサイトの関手と構造環の係数制限との自然同型。剰余代数上の二つの係数構造の両立条件を型に残す。`CrystallineZariskiIso` と `CrystallineSmallCoverMaps` は単位自然同型で主開被覆を移し、剰余代数の引き戻し・分冪基底の制限による小さいサイトの関手が指定被覆族を保つことを明示した。
- 一時監査は49モジュール・559宣言、標準三公理のみ（`/private/tmp/AuditD69P3FortyNine.lean`、`/private/tmp/d69-p3-audit-fortynine.log`）。追加7本も新規ファイルのみ、sorry・独自公理0。既存宣言・Nakayama の二ファイル・公式登録は変更していない。
- ここでの層性は段0で述べた通常の環値の層性。∞ の篩に対する降下や RΓ の定義への組み立ては草稿に残す。残件の照合と塔の構造環への標準射を続ける。この記録は停止点3ではない。

登録候補への追加（7本）：

```text
SerrePositivity.BhattScholze.Prismatic.CrystallineBaseStructureRestriction
SerrePositivity.BhattScholze.Prismatic.CrystallineSmallCoverMaps
SerrePositivity.BhattScholze.Prismatic.CrystallineSmallStructureSheaf
SerrePositivity.BhattScholze.Prismatic.CrystallineStructureGluing
SerrePositivity.BhattScholze.Prismatic.CrystallineZariskiIso
SerrePositivity.CommutativeAlgebra.Localization.AwayEquivalence
SerrePositivity.CommutativeAlgebra.Localization.AwayGluing
```


## 停止点3：P3 完了・BS-D69 の区切り（2026-11-12、実装 347ec8a29）

### 完了と取り込みの順序

- 11月12日朝の調整役の決定により、停止点3の範囲は指示書 §0 の P3（サイト・構造層・Čech の塔・引き戻し・Poincaré の複体比較）。下表と登録一覧の52本でこの範囲を完了した。P1・P2 は既に検収・main 取り込み済みなので、これを BS-D69 の区切りとして報告する。
- **実装の取り込み点は `347ec8a29`**。既存の検証記録は `494450453`、今回の報告更新は文書のみ。登録候補は BS 47本・共通5本の計52本で、末尾に統合一覧を置く。
- 対象ビルドは全52本について成功、一時監査は588宣言・標準三公理のみ。sorry・独自公理0、既存宣言の変更0。今回の完了報告に際して Lean ソースは変更せず、ビルド・監査は直前の同じ実装に対する下記結果を用いる。
- **取り込みは KL-W1 の停止点3の main 取り込みの後**。改名表の指示を受けて枝を追従させ、その時点で必要な対象ビルド・監査を `--wait 3600`、鍵をビルドの間だけ持つ形で行う。先に本レーンの新規コードを main へ取り込まない。入口・公式監査への登録は調整役が行う。

### 検証した範囲

- main `d9e596898` を `6cdce754c` で取り込んだ。衝突なし。main の作業木で編集・ビルドはしていない。
- `PDCechTowerStructure` は分冪 Čech 脈体から有限段の厚化の構造環への標準自然変換、塔の遷移との両立、小さいサイトの構造前層を有限 Čech 段に制限したものと台環模型との自然同型。
- `PDCechFrameSiteMap` は、二つの全射な枠の厳密な比較を有限 p 冪商の実際の厚化の射へ降ろす。分冪・剰余構造射を保つこと、代表元の式、余単体的自然性、標準自然変換との可換正方形を証明した。
- `PDExtraCoordinatesRetraction` は既存の `withExtraCoords p k r` に対する零評価の厳密な余単体的射。`insertPdFactor_retraction` は環の段階での左逆、`pdExtraCoordinatesCochainEquiv` は係数加群の交代余面複体のホモトピー同値、`pdExtraCoordinatesRetraction_quasiIso` はその逆向きの擬同型。係数環は任意で、p 完備性や p 正則性を追加仮定していない。ただし、これは自由な高次座標の因子の収縮であり、草稿の一般 I の `pdDeltaCechNerve` 自体をその因子模型と同定した宣言ではない。
- main 取り込み後、P3 の50本をまとめた対象ビルドが成功（`/private/tmp/d69-p3-build-24.log`、3751 jobs）。その後の残り2本も対象ビルドが成功（`/private/tmp/d69-p3-build-26.log`、3913 jobs）。どちらも `--wait 3600`、一回30分未満、鍵はビルドの間のみ。これは各モジュールとその依存だけの対象ビルドで、root ビルドではない。
- 一時監査は **52モジュール・588宣言、標準三公理のみ**（`/private/tmp/AuditD69P3FiftyTwo.lean`、`/private/tmp/d69-p3-audit-fiftytwo.log`）。sorry・独自公理0。main との差分で、本体は52本すべて新規ファイル。既存宣言、Nakayama の二ファイル、公式の入口・監査は変更していない。

指示書 §0 の P3 の対応：

| 指示書の部品 | 本体の入口・到達点 |
| --- | --- |
| big affine site と小さい模型 | `CrystallineSiteBasic`、`CrystallineSiteSmall`、`CrystallineSmallSiteTopology` |
| 分冪の局所化・Zariski 位相 | `PDLocalizationStructure`、`CrystallineSiteLocalization`、`CrystallineZariskiCoverage` |
| O_crys が通常の環値の層 | `CrystallineSmallStructureSheaf.crystallineStructure_isSheaf` |
| 全 Čech の塔と有限段の余積 | `PDCechCrystallineTower.pdCechTower`、`pdCechTowerProCechData` |
| 濃度と pro 弱終性 | `CrystallineCechCutoff.pdCechSmallTowerOfCutoff_proWeaklyTerminal`。変数数の条件は `#S ≤ #k + #R + ℵ₀`。標準の枠 S=R はこの条件を満たす。 |
| 剰余代数の引き戻し・基底の制限 | `CrystallineStructurePullback`、`CrystallineBaseStructureRestriction`、`CrystallineSmallCoverMaps` |
| 多項式 Poincaré の複体の段 | `CrystallinePolynomialSpan.crystallinePolynomialTotalToCech_quasiIso` と既存の `pdDeRhamTotalToCompletedForms_quasiIso` による二脚。型には基底の p 完備性・p 正則性・分冪の p 上の条件がある。 |
| 塔の構造環・枠の射との照合 | `PDCechTowerStructure`、`PDCechFrameSiteMap` |

### 後回しの項目（11月12日朝の調整役の決定）

段0報告の「多項式の Poincaré、Thm 5.2 の模型」の行に含めた、次の一般 I での追加一般化は、**停止点3に含めず後回し**とする。

1. 一般 I の δ 座標つき相対分冪包と `withExtraCoords` の同定。
2. その包への η の厳密な射。
3. D68 の η との特殊化の等式。

これらは未証明のまま草稿側に残し、今回の52本や完了宣言には数えない。調整役の説明では、E3 の経路で結晶の比較を使うのは結晶的な基底の場合で、D68 の ℤ_p の η で足りる。一般 I の版を使う場所が出たときに、改めて作業範囲へ入れる。

`PDExtraCoordinatesRetraction` の一般係数での自由座標因子の収縮は検証済みだが、上の1〜3を証明したことにはしていない。RΓ の定義、Tot の E∞ 構造、関手 ∞ 圏への組み立ても、指示書どおり草稿に残す。Nakayama の二ファイルの整理は、既に決められた KL-W1 取り込み後の別作業として残し、両ファイルを変更していない。

### 登録候補（P3 全52本、BS 47本・共通5本）

入口・公式監査には未登録。調整役の取り込みのための統合一覧：

```text
SerrePositivity.BhattScholze.Prismatic.CompletedPDEnvelopeCardinality
SerrePositivity.BhattScholze.Prismatic.CrystallineBaseRestriction
SerrePositivity.BhattScholze.Prismatic.CrystallineBaseStructureRestriction
SerrePositivity.BhattScholze.Prismatic.CrystallineCechCutoff
SerrePositivity.BhattScholze.Prismatic.CrystallineCechProWeakTerminal
SerrePositivity.BhattScholze.Prismatic.CrystallineFrameLift
SerrePositivity.BhattScholze.Prismatic.CrystallineFrameLiftResidue
SerrePositivity.BhattScholze.Prismatic.CrystallineFrameVariablesLift
SerrePositivity.BhattScholze.Prismatic.CrystallineLocalizationLift
SerrePositivity.BhattScholze.Prismatic.CrystallineNilpotentComplete
SerrePositivity.BhattScholze.Prismatic.CrystallinePDQuotient
SerrePositivity.BhattScholze.Prismatic.CrystallinePDQuotientLift
SerrePositivity.BhattScholze.Prismatic.CrystallinePDQuotientMap
SerrePositivity.BhattScholze.Prismatic.CrystallinePDQuotientTower
SerrePositivity.BhattScholze.Prismatic.CrystallinePolynomialSpan
SerrePositivity.BhattScholze.Prismatic.CrystallineResidue
SerrePositivity.BhattScholze.Prismatic.CrystallineResidueAlgebra
SerrePositivity.BhattScholze.Prismatic.CrystallineSiteBasic
SerrePositivity.BhattScholze.Prismatic.CrystallineSiteLocalization
SerrePositivity.BhattScholze.Prismatic.CrystallineSitePullback
SerrePositivity.BhattScholze.Prismatic.CrystallineSiteSmall
SerrePositivity.BhattScholze.Prismatic.CrystallineSiteZariski
SerrePositivity.BhattScholze.Prismatic.CrystallineSmallCoverMaps
SerrePositivity.BhattScholze.Prismatic.CrystallineSmallSiteTopology
SerrePositivity.BhattScholze.Prismatic.CrystallineSmallStructureSheaf
SerrePositivity.BhattScholze.Prismatic.CrystallineStructureGluing
SerrePositivity.BhattScholze.Prismatic.CrystallineStructurePullback
SerrePositivity.BhattScholze.Prismatic.CrystallineTransport
SerrePositivity.BhattScholze.Prismatic.CrystallineZariskiCoverage
SerrePositivity.BhattScholze.Prismatic.CrystallineZariskiIso
SerrePositivity.BhattScholze.Prismatic.CrystallineZariskiRefinement
SerrePositivity.BhattScholze.Prismatic.PDCechCrystallineCoproduct
SerrePositivity.BhattScholze.Prismatic.PDCechCrystallineCosimplicial
SerrePositivity.BhattScholze.Prismatic.PDCechCrystallineQuotient
SerrePositivity.BhattScholze.Prismatic.PDCechCrystallineTower
SerrePositivity.BhattScholze.Prismatic.PDCechCrystallineVertices
SerrePositivity.BhattScholze.Prismatic.PDCechFrameSiteMap
SerrePositivity.BhattScholze.Prismatic.PDCechQuotientVariablesLift
SerrePositivity.BhattScholze.Prismatic.PDCechResidueEquivalence
SerrePositivity.BhattScholze.Prismatic.PDCechResidueNaturality
SerrePositivity.BhattScholze.Prismatic.PDCechTowerStructure
SerrePositivity.BhattScholze.Prismatic.PDEnvelopeCardinality
SerrePositivity.BhattScholze.Prismatic.PDExtraCoordinatesRetraction
SerrePositivity.BhattScholze.Prismatic.PDLocalizationAddition
SerrePositivity.BhattScholze.Prismatic.PDLocalizationDpow
SerrePositivity.BhattScholze.Prismatic.PDLocalizationLaws
SerrePositivity.BhattScholze.Prismatic.PDLocalizationStructure
SerrePositivity.CategoryTheory.ProCechNerveData
SerrePositivity.CategoryTheory.ProCechNerveTransport
SerrePositivity.CommutativeAlgebra.Adic.Cardinality
SerrePositivity.CommutativeAlgebra.Localization.AwayEquivalence
SerrePositivity.CommutativeAlgebra.Localization.AwayGluing
```


## KL-W1 停止点3の改名への追従完了（2026-11-12 昼）

- 作業開始時の枝は `7280b7ce5`、作業木は clean。検証済みの52本はすべてコミット済みで、未検証の下書きなし。配布された `kerodon-layout-stop-3/bs-d68-files.json` を `/private/tmp/bs-d69-klw1-20261112/files.json` に写し、枝固有の Lean ファイルと未追跡分を照合した。配布一覧との差分は0で、対象は同じ52本。
- **main 取り込み前**の同じソースと既存成果物から、配布された `klw1_namespace.py collect` で52本すべての参照を収集した。終了コード0。`before_index` は `/private/tmp/bs-d69-klw1-20261112/before_index`。各ソースは収集情報・開始時のハッシュとバイト単位で一致することを確認した。
- 同じ一覧・ソース・参照情報と最終版 `kl-namespace-map.json` で rewrite のプレビューを作成。終了コード0。**書き換え0本・0行、`review.json` は `{}`、残る保留0**。全52本のプレビューが元ソースとバイト単位で一致したため、ソースの編集は不要だった。追加の互換 alias も作っていない。
- 使用した改名表は KL-W1 の作業木と取り込む main で同一。SHA-256 は `kl-module-map.json`: `69207c416cb097073875fd482ae08e9d04f55338f0415f9138502ccafb412b1a`、`kl-namespace-map.json`: `cf1fb1a6d1acea4717a60ee8f5497c1e582db7d331526f73f8fc0f7ffa957944`。
- **追従の merge コミットは `a916536a3`**。main `8f68a475d`（KL-W1 取り込み `19f081dcb` 以降）を専用枝 `math/bs-d68` に取り込んだ。衝突なし。取り込み後も52本はプレビューと同一で、改名表のハッシュも一致した。main の作業木で編集・ビルドはしていない。
- 書き換えファイルが0本なので、その直接 importer に対する追加ビルド対象も0。移動後の推移的な依存の検証として、**P3 の52本すべてを対象ビルドし成功（4196 jobs、終了コード0）**。ログは `/private/tmp/bs-d69-klw1-20261112/build.log`。`with_build_lock.sh --wait 3600` と1700秒の上限を用い、鍵は対象ビルドの間だけ持った。root ビルドは行っていない。
- 対象ビルド終了後に鍵を取り直して、一時監査も実行。**52モジュール・588宣言、標準三公理のみ、終了コード0**。ログは `/private/tmp/bs-d69-klw1-20261112/audit.log`。sorry・独自公理0、既存宣言の変更0を維持している。Nakayama の二ファイル、公式の入口・監査は編集していない。
- 追従結果の一覧・参照収集ログ・プレビュー・空の review・ハッシュの記録は `/private/tmp/bs-d69-klw1-20261112/`。登録候補は上の「P3 全52本、BS 47本・共通5本」の統合一覧どおり。**KL-W1 後の追従と再検証が完了し、停止点3の52本を調整役が取り込める状態**として報告する。一般 I の η の追加一般化は、前節の決定どおり後回しのまま。
