# BS-D3　drafts の主張の具体化　作業報告

## 第1部　停止点1完了・A5 の先行定義（基準 main `789259c90`）

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
- D3-02（`2bb0d406c`）で、全 `PerfUnder_u` の opposite に対し S3 側の `CechNerveDataLarge` の四欄を供給できた。κ 以下の完全 site は小さい `CechNerveData` のまま。大きい版の極限判定 `isLimitCone_iff_restrict_cech_large` は基盤待ちで、使用先は次の停止点の `limit_perfUnder_eq_tot`。停止点1では両極限の一致は使わない。

### 件数と確認範囲

基準にあった結論 `True` を PerfectSite で8件、SemiperfectoidCase で17件、計25件具体化した。さらに `universalPerfectoidRing : Type u := sorry` を選択した普遍環に置き換えた。二種類の集計は計26件。既に型を持っていた `perfectFlatTopology`、`IsSemiperfectoid`、`universalPerfectoidUnit` の本体、環インスタンスや比較用の補助宣言は別集計。対象2ファイルの `True` 宣言・`Type u := sorry` はいずれも0件。`-- 要確認：` は PerfectSite 1件、SemiperfectoidCase 0件。

設計側の `3acedf8eb`（有界版 Lemma 4.8）、`1480a4e5c`（D3-01）、`2bb0d406c`（D3-02）を読み、最後の二つに取り込まれた A5 の途中差分も含めて照合した。ほかに新しい設計判断はない。原典と照合した箇所、既存の宣言名と引数、基準の25件の名前、import パス、括弧、差分の空白を静的に確認した。指示どおり Lean の型検査・ビルドは行っていない。停止点2には進んでいない。

## 第2部　停止点2・A5 の降下と Prop 8.5（基準 main `624dfe2f2`）

### 具体化した宣言

| ファイル | 基準で結論が `True` だった宣言 | 主張 |
| --- | ---: | --- |
| RootAdjunction | 2 | 通常の環の filtered 余極限の比較射 `colimit.post` は同型。多項式環への根添加の標準射は p 完備忠実平坦。 |
| StrongDescent | 11 | Δ と Δ_perf の根添加の射についての Lemma 8.6、一変数への帰着、任意の離散係数での RHom、Koszul による上界、de Rham 比較と Cartier 射。 |
| WeaklyInitialAndDescent | 15 | E 被覆、弱始対象、大小の Čech 極限、filtered 余極限との交換、有限型への帰着、Lemma 8.6 による左右の降下。 |
| PerfectSiteComparison | 8 | Prop 8.5 の比較射と位相版、κ 版・Type u 版の極限、prism の選択、Cor 7.3 との一致、animated 版と系4。 |

計36件。指示書の PerfectSiteComparison は7件とあるが、列挙された名前と基準ファイルには系4を含めて8件ある。別に、既に型のあった `rootClosure_isSemiperfectoid` で perfectoid 基底の証人 `hR` を明示した。四ファイルで結論 `True` と `Type u := sorry` はいずれも0件。

- 根添加では、E の各段を多項式環の商、E を通常の環の可算余極限とした。係数と変数の添字を同じ射で移すので、filtered 比較は指定された `colimit (D ⋙ E) → E (colimit D)`。S̃ の各段では完備化し、用途を弱始性と濃度評価に限った。有限型への帰着に使う被覆では `E(colimit D)^∧` と各段の完備余極限を比較する。多項式環から T_∞ への射は変数を第0段の根に送る。平坦性はこの射の加群構造についての `IsCompletelyFaithfullyFlat`。
- Lemma 8.6 は実際の根添加射を `discreteDeltaFunctor` と `directPerfectionFunctor` で送った二辺について `IsDescendableOver` を述べる。一変数の内部補題にだけ index ≤ 2 が現れる。C=A/(p,φ⁻¹(d)) 上の任意の離散加群 L を取ると、二乗した fiber からの RHom は `(∏ (C[X^p] ⊗_C L))[1]` で上界は −1。有限二元 Koszul 複体 K の Postnikov 各段に随伴を適用し、双対可能な K での RHom とテンソルの比較を経て、冪の塔の逆極限で M に戻る。de Rham 比較は両端の同型が根添加射と可換であること、Cartier は次数 0・1 の積を保つ指定鎖写像が擬同型であることを型にした。
- E 被覆の弱始性は `C^∧ → E(C)^∧ → Q(E(C)^∧)` に対する補題として明示した。全 perfectoid 標的には `IsWeaklyTerminalLarge`、κ 側には小さい S3 を使い、E3 の `targetCAlgDiagram` の極限錐を同じ Tot の頂点に取る。完全 site 上の O の極限は perfectoid 試験環の prism を与える関手の点ごとの右 Kan 拡張で関手化した。mod d を取った Ō は別の CAlg_R 値前層。降下の両側に用いる錐は S → S̃^• の増大から得る指定錐で、射影は広い押し出しの構造射と完備化単位の合成。
- Prop 8.5 は停止点1の比較射自身の `IsIso`。J ≤ flat のときは O の J 層性と S2 により同じ比較を RΓ_J に移す。animated 版の始域は `CompleteAnimatedAlgebra p R`、試験 site は π₀ S で取る。系4は切り捨て単位 S → π₀ S の `prismaticPerfectionAnimated` と `perfectoidizationAnimated` による像の可逆性。どの同型を用いるかが分かるよう、単に両端の頂点が同型であるという形から射を区別した。

### 要確認と依存先

`-- 要確認：` は RootAdjunction 0件、StrongDescent 5件、WeaklyInitialAndDescent 1件、PerfectSiteComparison 3件。内訳は次のとおり。

| 場所 | 待っているもの |
| --- | --- |
| StrongDescent・`fiberSquareRHom` | M15 の Mod_D の fiber・相対テンソル・内部 Hom と D(A) への忘却。D は一般に非離散。 |
| StrongDescent・`prismScalarExtension` | ScalarRestriction へ。M13 の `cAlgRestrictScalars q` の左随伴としての CAlg 係数拡大。D 側は既存の `derivedInfinityBaseChange`。 |
| StrongDescent・`rootDeRhamSource` | A1-5。一変数の外積付き de Rham cdga の E∞ 実現。 |
| StrongDescent・`rootDeRhamAugmentation` | A1-5。X を第0段の変数に、dX を 0 に送る射の実現。 |
| StrongDescent・`rootMap_modP_eq_deRham` | A1-5 の `deRham_iso_polynomial_modP`、`deRham_iso_rootAlgebra_modP` の型と自然性。 |
| WeaklyInitialAndDescent・`limit_perfUnder_eq_tot` | D3-02。S3 の `isLimitCone_iff_restrict_cech_large` とその錐の延長。小さい版の `exists_limitCone_of_cech` は型付き。 |
| PerfectSiteComparison・`perfectCoefficientPresentable` | G12 の CAlg_A の presentability。S4 の `sheafification_exists_cAlg` に渡す。 |
| PerfectSiteComparison・`perfdOverPerfectPrism` | BS-D4 で、別の完全 prism 上の離散 Frobenius を、Lemma 4.8 を通じて A4 の `discreteDeltaFrobenius` の同じ成分に接続する。 |
| PerfectSiteComparison・`piZeroReflection` | A2 の π₀ と切り捨て単位。完備な離散代数の埋め込み `completeDiscreteToAnimated` の左随伴の型で指定。 |

A2 待ちの Δ、Frobenius、完備 CAlg への反射、mod d には、A4・A7 の `discreteDeltaFrobenius`、`completeCAlgInclusion`、`reflectCompleteCAlg`、`modPrismFunctor`、`prismaticPerfectionAnimated`、`perfectoidizationAnimated` を通した。後二者は既存の `animatedDelta` と `animatedDeltaFrobenius` を使う。G-A5-17、(5) と完備テンソルとの可換性、任意の位相に対する S2・S4 は証明の依存先。A7 の UniversalProperty に依存する単位を A5 に持ち込まず、π₀ の単位は A7-1 の離散埋め込みから取った。

### 設計との差と確認範囲

途中で、離散環上の `IsDescendable` と当初は引数のなかった `IsDescendableOver` のどちらも Δ_T 上の射を受け取れないことを報告した。D3-04（`df86ebb71`）で基盤側に非離散底の型が確定したので、それに合わせた。押し出し・Tot・テンソル・RHom・Frobenius 余極限・完備化の証明は Shared/Descendable の一般底版 (a)〜(h) 待ち。ほかに設計上の変更はない。

基準との差分には `df86ebb71` に入った RootAdjunction と WeaklyInitialAndDescent の途中差分も含めて照合した。指定四ファイルの元の宣言名と件数、既存の定義の向き、実ファイルの import パス、括弧と空白を静的に確認した。Lean の型検査・ビルドは実行していない。停止点3の A6 は未着手。
