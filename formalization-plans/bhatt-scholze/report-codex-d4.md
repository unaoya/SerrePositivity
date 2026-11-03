# BS-D4 作業報告

## 第 1 部　A2（停止点 1）

開始基準は main `9f9e0b6c2`。対象は `drafts/A2/` の四本。作業中に設計側の D4-01（`947be6174`）が入り、そのコミットにも A2 四本の途中差分が含まれる。以下は開始基準と停止点のファイルを比べた件数で、途中差分を二重に数えていない。

### 宣言と型

| ファイル | 旧結論が `True` の件数 | 具体化した内容 |
|---|---:|---|
| AnimatedAlgebra | 5 | 標準の変数包含を脚とする二項余積の `IsColimit`、Yoneda の充満忠実性、各頂点の多項式による sifted 表示、離散埋め込みの多項式上の回収と充満忠実性。F2 の `sigma_exists_leftKanExtension_with_recovery` から延長と制限同型を選び、`siftedRestriction_equivalence` で関手圏の一意性を表した。 |
| DerivedPrismaticCohomology | 9 | 完備部分圏と反射の単位、CAlg 値の構造前層と RΓ、Rem 4.19 の Tot との頂点同型。多項式射と Frobenius の作用は試験 prism での射影の可換式を含む。延長した Frobenius は多項式上の回収同型と両立する関手圏の辺。忘却・離散制限・実際の H⁰ 代数も定めた。 |
| HodgeTateFiltration | 7 | 完備圏内の Lan、同じ増大余錐の後続辺と Δ̄ への脚、Poly 上の有界性、自然な次数商と `[−i]`、完備圏の余極限としての exhaustiveness、Fil₀ と導来 p 完備化の自然同型。CAlg 値の HT 単位は忘却後に第 0 脚に一致する。 |
| BaseChangeAndTensor | 5 | 完備底変換の自然同型 (4)、sifted 余極限保存、標準の二つの変数包含の Künneth、任意の二項余積の保存 (5)、D32（指定された animated 完備化単位の像が可逆）。G-A2-10 は二つの完全 prism の間で、底を制限した離散代数の比較の成分について述べた。 |

指示書の「25 件、うち底変換 4 件」の列挙には D32 まで含めて底変換が 5 件あり、旧結論が `True` の宣言は計 **26 件**。別に `polyCompletion : Type u := sorry` を A0 の `prismPolynomialCompletion` に置き換えた。二種類の仮置きを合わせると **27 件**。新設の補助宣言や、もともと関手の型をもっていた定義の具体化はこの数に含めていない。

### A4・A5・A7 からの接続

表の P は基底 prism、e は P の商と R の環同型 `A ⧸ P.ideal ≃+* R`。合成や制限を要する行にはそれも記した。呼出側のファイルは編集していない。

| 呼出側の仮置き | A2 の宣言と接続 |
|---|---|
| A4 `discreteDeltaFrobenius` | `discreteFrobeniusComponent`。e で離散入力を A/d 上に読み替え、`derivedPrismaticFrobenius` をその入力で評価する。 |
| A4 `directHodgeTateUnit` | `hodgeTateUnitFromInput` を離散入力に制限し `discreteRealizationIso` と e で移送する。これは完備化単位と `hodgeTateUnitCAlg` の合成。 |
| A4 `completeCAlgInclusion` | `prismCompleteInclusion P`。 |
| A4 `reflectCompleteCAlg` | `prismCompletion P`。随伴は `prismCompleteReflection`、単位は `prismCompletionUnit`。 |
| A4 `modPrismFunctor` | `prismModIdeal P ≫ cAlgBaseChange e.toRingHom`。合成した係数射が θ。 |
| A7 `animatedDelta` | `deltaOverQuotientIso P hP e`。完備入力の包含、`animatedScalarExtension e.symm.toRingHom`、Δ の順。prism の射に沿う比較は `derivedPrismaticCohomology_baseChange`。 |
| A7 `animatedDeltaFrobenius` | `derivedPrismaticFrobenius P hP` を上と同じ包含・係数移送で前合成する。値側の半線形性は `cAlgRestrictScalars`。 |
| A7 `animatedRealization` | `animatedCAlgRealization`。多項式環の `algebraEmbedding` の sifted 延長。 |
| A7 `animatedPerfdUnit` | `hodgeTateUnitFromInput` の完備入力への制限を e で移送する。これが Fil₀ の脚。塔の第 0 脚から perfection へ進む残りの合成は A7 にある。 |
| A5 `perfdOverPerfectPrism` | `perfdValueOverPrism`。離散 Frobenius の正の反復による塔の余極限を prism 完備化し、mod d と e で係数を移す。有界性は完全 prism の商が perfectoid であることから供給する。 |
| A5 `piZeroReflection` | `completePiZeroReflection`。全域の `animatedPiZeroAdjunction` を完備な始域と完備離散代数へ制限し、随伴の単位で X → π₀X を指定する。 |

D3-01 の A5 の第 0 脚は別に `polySectionsCone`・`polySectionsProjection` から `discreteEvaluation` に接続した。多項式段では構造層の極限錐から射影を取り、離散 S では多項式分解から試験 prism への錐を得る。完全 site への制限後の極限性は A5 の降下で示す。

### 設計判断と要確認

D4-01 は HT の係数について設計側で解決済み。一般 k の `cotangentWedgeGeneral` は Shared の通常の `forms k (Fin n) i` を離散 **加群**として D(k) に入れ、導来 p 完備化する。A1 と接続する `polyForms_boundedComparison` は有界 prism の k=A/d の場合に限って H⁰ 完備化 `completedForms` と比較する。離散 S での値の S 加群構造は `cotangentWedgeAtAlgebra` で表した。

| ファイル | 証明時に接続する入口 |
|---|---|
| AnimatedAlgebra | 新しい仮名なし。P_Σ の結果は F2 の既存名。離散前層の評価・離散実現の証明は draft の穴。 |
| DerivedPrismaticCohomology | ① G-A2-3・9 の CAlg 完備反射。② G12 の `CAlg_R A` の presentability と S2 の層化。③ Shared の `totEInfinity_isLimitCone`。④ A0/S2 の site・RΓ の関手性（`PolyDeltaData.map_eval` の全単体への持ち上げと cutoff の比較）。 |
| HodgeTateFiltration | ① DerivedGeneral の主元 p の完備反射。② DerivedGeneral/Truncation の自然な増大列・余単位・cofiber。③ Shared の `completedForms_eq_derivedCompletion_of_boundedTorsion` は設計側に名前があり、現時点の結論は `True`。 |
| BaseChangeAndTensor | ScalarRestriction の `cAlgBaseChange_restrictScalars_adjunction` の単位。現在は `True` なので `perfectBaseComparison` に型を置いた。多項式上の比較証明は A1 の Cor 4.12 と Thm 6.3 に依存する。 |

### 確認の範囲

コメントを除いた宣言を開始基準と比較し、A2 四本には上記二種類の仮置きが 0 件であることを確認した。参照名は本体・Mathlib・基盤 drafts と照合し、四本の括弧と実際の import 先、`git diff --check` を静的に確認した。ビルド・Lean の型検査は行っていない。ここは停止点 1 で、A3 と A1 は次の停止点の対象。
