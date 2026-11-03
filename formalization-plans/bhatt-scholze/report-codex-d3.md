# BS-D3　drafts の主張の具体化　作業報告

## 第1部　A5 の先行定義（基準 main `789259c90`）

### 完全 site と比較写像

- A0 の site には `perfectPrism_quotientEquiv` と R → S の合成で A/d 代数構造を与え、cutoff の上界から小さい模型を選んだ。完全対象の包含に沿って O を A 代数値、CAlg_A 値、D(A) 値の順に読む。flat 位相の生成 sieve は一つの (p,d) 完全忠実平坦射からなる被覆のもの。層性の証明で使うのは B₁ ⊗̂_{B₀} B₁ の相対 Čech 項。
- Perfd の余積では、T₁ ⊗̂_R T₂ の中で二つの S 作用の差を割り、その商に既存の `exists_perfectoidization_of_perfectoid_surjective_quotient` を適用する。完備標的への延長で (T₁ ⊗̂_S T₂)_perfd の単位を得る。左右の構造射を指定した `BinaryCofan` を反復し、各標準脚と有限余積の普遍性で単体写像を定めた。A5-2 の普遍環も Prop 8.5 もこの構成には使わない。
- Lemma 4.8 は承認された有界標的版。商の射を一意に持ち上げる証明は `Andre.existsUnique_perfectPrismHomLift_to_bounded` そのもの。B ↦ (S → B/J) を Hom 上も指定して κ 以下の perfectoid 標的への同値を取る。有界性は A0 の site の対象がもつ。原典の Lemma 4.8 の標的は任意の prism。[Bhatt–Scholze, Lemma 4.8](https://arxiv.org/pdf/1905.08229#page=38)
- D3-01 により、第0脚は S2 の CAlg 値 RΓ の射影の型にした。多項式分解では射影を各段で取り、Frobenius 両立性は O の Frobenius の自然性から得る。A3 の `prismMapOfDiscrete` は離散性の仮定の下で H⁰ を読んだもの。各段の脚は τ = Res_{φ_A} として τⁿ(f) に φ_B⁻ⁿ を後合成する。同じ錐の脚として全 B と全 n の整合性を指定し、塔の余極限の脚と完備化単位に沿って Δ_perf から O の極限への比較射を記述した。[Bhatt–Scholze, §8.1](https://arxiv.org/pdf/1905.08229#page=64)

### Semiperfectoid の場合

- G-A5-17 は A_inf の射を有界版 Lemma 4.8 で選び、A2 の完備底変換の単位と S⊗ᴸ_R R₁ → S を合成した比較辺の可逆性を述べる。完備余接複体は A2 の `cotangentWedge` の第1外冪で読む。semiperfectoid の場合はその上界 −1、HT の連結性、Δ と Δ_perf の連結性を順に指定した。L^∧ が次数 −1 に集中するという仮定は使わない。離散性から perfectoid 性へは A7 の `DiscreteCore` を使う。
- `IsSemiperfectoid` に S 自身の導来 p 完備性と perfectoid 環の全射商という条件を置いた。R 線形な全射表示は別の (α)。Cor 7.3 の一つの存在証人から普遍環、環インスタンス、指定単位を取る。Thm 7.4 の全射性でこの標的は cutoff 内にあり、その試験 prism への比較の脚を mod d、H⁰ と順に写すと `perfectoidizationToUniversal` になる。分裂は S の下で、最終比較は環同型とその H⁰ に一致する CAlg_R の頂点同型。
- 根変数は有限台の指数をもつ加法モノイド環で表した。核の生成元を同時に発根する p 完備忠実平坦な拡大を取り、第0段の変数を殺した完備商から底変換後の S への評価を、各段の根の像で指定した。π₁(L/p) の全射性は標準多項式表示の余接複体の p 倍の cone の H⁻¹ をサイクルと境界で指定した。有限部分集合の包含による余錐と完備圏での perfd の余極限を経て、有限変数では全段の根を殺す商を Prop 7.10 で得る。最後に全射性を反映する。

### 依存先・要確認

- `PerfectSite.lean` の `-- 要確認：ScalarRestriction へ` は1件、`discreteRestrictionIso`。離散な A 代数 B の構造射を φ_A と合成したものの離散埋め込みと、元の埋め込みの `cAlgRestrictScalars φ_A` による制限を比較する。この同型を通して完備な試験環の Frobenius の逆を読んだ。`ScalarRestriction.lean` は編集していない。
- 第0脚の仮置きは A0/S2 の CAlg 値 RΓ の射影待ち。A2 の `prismaticCohomologyCAlg` はこの基準でまだ `True`。A4 の `discreteDeltaFrobenius`、`completeCAlgInclusion`、`modPrismFunctor`、`directHodgeTateUnit` を既存の名前で使用した。A2 の底変換 (4)、HT filtration の具体化も証明の依存先。W9-III-08 の完備テンソルの perfectoid 性は、2a 後の E3 非依存の芯を使う予定。
