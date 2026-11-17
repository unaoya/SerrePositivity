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

D4-01 の回答に合わせ、`hodgeTatePoly_gr` の結論には二つの比較を同じ Ω = LΛ_p(forms) で記した。第一項は `cotangentWedge` の多項式への制限が Ω に戻る自然同型（`siftedLanIso`）、第二項は Ω[−i] が次数商であること。現行の `Derived.completion` には p と d の明示引数がないため、A2 では主元 p の反射 `pCompletionReflection` を使い、基盤側で (p,0) へ特殊化する箇所を要確認に残した。

### 確認の範囲

コメントを除いた宣言を開始基準と比較し、A2 四本には上記二種類の仮置きが 0 件であることを確認した。参照名は本体・Mathlib・基盤 drafts と照合し、四本の括弧と実際の import 先、`git diff --check` を静的に確認した。ビルド・Lean の型検査は行っていない。ここは停止点 1 で、A3 と A1 は次の停止点の対象。

## 第 2 部　A3（停止点 2）

基準は main `b7881adac`。対象は `drafts/A3/DiscreteCase.lean` と `drafts/A3/LciAndQuasiregular.lean`。A2 の停止点 1 までの宣言を用いた。

### 具体化した宣言

| ファイル | 旧結論が `True` | 主張 |
|---|---:|---|
| DiscreteCase | 3 | `deltaStructure_of_envelopeIso` は指定された Frobenius 両立な A 環同型に沿って δ 構造を移す。`discrete_weaklyInitial` は p ねじれなしの標的 Y に対し、環の側で A2 の評価脚に等しい prism 射を与える。`exists_initial_of_discrete` は源も p ねじれなしのとき、この充満部分圏で自己評価の冪等射を分裂した始対象を得る。 |
| LciAndQuasiregular（Ex 7.9） | 5 | `lciDerivedEnvelope` は U→A に沿う E の完備導来底変換。`lciDerivedEnvelope_eq_prismatic` は完備 CAlg の頂点同型。`lciDerivedEnvelope_isEnvelope_of_discrete` は離散化後の H⁰Δ・HT 単位を備えた envelope。`lci_envelope_surjective_invert_p_universal` は U/d とその変数商が p ねじれなしの普遍例で、指定した mod d の比較射を p で局所化したときの全射性。`prismaticCohomology_lci_eq_envelope` は Koszul 正則性と商の有界 p 冪ねじれの下での envelope と始性。 |
| LciAndQuasiregular（Prop 7.10） | 5 | `qrsp_isDiscretePrismatic` と `qrsp_completelyFaithfullyFlat` は一般の qrsp の離散性と HT 単位 S→H⁰Δ/d の p 完全忠実平坦性。`regularSemiperfectoid_prismatic` は有限根付き商 T での G-A2-10、A′ 上の Ex 7.9、A 上の始性。`qrsp_initial` は一般形の記録。`rootQuotient_prismatic_perfection_eq` は任意の根の族の S′ について Cor 7.3 の具体的候補との S′ 上の唯一の完全 prism 同型を述べる。 |

合計 **13 件**。別に `Type u := sorry` の四宣言（`discretePrismaticRing`、`universalLciPrismRing`、`ainfPrismRing`、`regularSemiperfectoid`）を具体化した。`IsDiscreteHodgeTate` は Δ̄ の次数零への集中、`IsDiscretePrismatic` は Δ の次数零への集中と H⁰Δ での d の正則性。有界性と κ に入る濃度は `discretePrismOver` の独立の引数とした。A3 二本のコードには `True` が残っていない。

### 証明の依存と原典の範囲

- Lemma 7.7 の H⁰ 環、HT 単位、Frobenius、試験 prism への評価を A2 に接続した。`prismMapOfDiscrete_natural` は評価の自然性を記録する。Lemma 7.8 ではこの自然な脚が `Under X` への切断を与え、`IsIdempotentComplete` で自己評価を分裂する。Ex 7.9 の全 prism への普遍性は `IsPrismaticEnvelope.lift` による。
- G-A3-10 は、B と Δ の比較、HT による離散性、`lciCompletionH0Comparison`、通常テンソルの `lciTensorDelta` と `lciTensorDelta_map_iff`、完備化からの一意延長の順。H⁰ の段では既存の `derivedComplexCompletion_h0_map_isIso` を p と d に適用する。W₂ の段は両因子の切断で判定する。変数 envelope の平坦性の底は A₀。
- D39 の qrsp には完備性、perfectoid 環からの全射、有界 p 冪ねじれ、完備余接複体の平坦性の四条件を置いた。最後の条件では A2 の `cotangentWedgeAtAlgebra` から S 加群を取り、シフト後の導来 mod p が次数零の平坦な S/p 加群であることを求める。
- T の比較に使う A2 の入口は `perfectBaseComparison_isIso`。これは `derivedPrismaticCohomology_baseChange` と乗法の合成についての G-A2-10。E3 の S′ の始性は `rootQuotient_initial` で有限部分族の T から得る。一般の `qrsp_initial` の証明は W9-I-43 の別単位。
- W9-I-44 では R′ に根を添加してから A′ = A_inf(R′) と r = (R′→S′) ∘ θ を取った。非零枝で p の非単元性、r の全射性、r(d′) = 0 を `exists_perfectoidization_of_perfectPrism_quotient` に渡す。始 prism の完全化からの一意延長には `existsUnique_deltaPerfectionPDCompletionHom` を使う。零枝では R′、S′、完全化の商が `Subsingleton` になる。

### D4-02 と A1 から渡す引数

元の A1 の `universalOrientedPrismRing` に p の明示引数・環インスタンスがなかった点は D4-02（`e901167e4`）で解決方針が決まった。A3 は任意の有界 P₀ と分類射を使う。停止点 3 の A1 で次を代入する。

| A3 の引数 | A1 からの入力 |
|---|---|
| A₀ と `[CommRing A₀]`、P₀ | p を明示する `universalOrientedPrismRing`、その環インスタンス、`universalOrientedPrism` |
| `h₀ : IsBoundedPrism P₀` | `universalOrientedPrism_bounded` |
| `g : OrientedPrism.Hom P₀ P` と `hd : g.toRingHom P₀.generator = P.generator` | `universalOrientedPrism_hom` の唯一の射とその生成元の式 |
| U の自由変数の像 | 与えられた f。A3 の `lciClassifyingMap` は U→A の基底との両立と各変数が fᵢ に写ることを返す。 |

G-A3-7 用の U/d とその変数商の p ねじれなしは、普遍 A₀ の特性を用いる箇所で供給する。D4-02 以外に設計変更を要した点はない。

### 要確認と静的確認

- `DiscreteCase` の G-A3-9 は、A2 の Frobenius と mod p の E∞ 演算の比較を要する。そこから δ 構造を回収する G-A3-6 には既存の `DeltaStructure.existsUnique_of_frobeniusLift` があり、標的が p ねじれなしの場合の δ 両立には `DeltaStructure.isDeltaHom_of_map_frobeniusLift` がある。同型への移送には `DeltaStructure.comapEquiv` を使った。濃度条件は定理の `hs` で受ける。
- `LciAndQuasiregular` の `padicBaseAlgebra` は、完備 S 上の標準 ℤ_p 作用を主元完備化の単位に接続する箇所。G-A3-7 の局所化全射は Koszul・bar の計算を証明する予定の補題で、外部引用にはしていない。
- 宣言の結論・裸の `Type u := sorry` を開始基準と比較した。コメントを除いて括弧の対応と `True` の残数を調べ、実際の import 先と `git diff --check` を確認した。Lean の型検査・ビルドは行っていない。

## 第 3 部　A1（停止点 3、最終）

A1 の開始基準は main `dacf638b5`。変更対象は `drafts/A1/` の四本と本報告。設計側の D4-03（`b17815ca5`）、D4-05（`6d0a0fa08`）、D4-04 の再訂正（`709a83741`）を読み、最後の値を採用した。履歴を確認すると、A1 四本のうち二本の途中差分が設計側の `32384e535` と `6d0a0fa08` に含まれている。履歴はそのままにし、第 3 部の件数は `dacf638b5` との差から一度だけ数えた。

### A1 の宣言

| ファイル | 旧結論が `True` | 型に含めたもの |
|---|---:|---|
| CrystallineInput | 2 | `crystalline_deRham_polynomial_Zp` は p 完備な二つの CAlg 値多項式図式の自然同型、mod p の Bockstein の可換式、根の後続遷移の可換式を一組とする。左辺は多項式射の mod p に依存し、右辺は持ち上げの連続形式を引き戻す。CAlg の射が積と単位を保つ。`hodgeTate_of_deRham_cartier` はこの入力から導く系。有限変数 Cartier の次数 1 は dXⱼ を [Xⱼ^(p−1)dXⱼ] に送る。 |
| HodgeTateMap | 5 | `reducedModel` は Rem 4.19 の各項を、基底から送った d で割る余単体的環。`hodgeTateMapZero` は構造射 sec の次数零の余輪体。`hodgeTateMapOne` は R 線形で f dg ↦ f β(η⁰g) を満たす。`bockstein_sq_zero` は cup による平方零。`hodgeTateMap` は各次数の線形写像と、単位・積・微分との両立を含む。 |
| HodgeTateComparison | 14 | `hodgeTate_iso_polynomial_Zp`、`hodgeTate_iso_crystalline`、`universalOrientedPrism_frobenius_flat`、`crystallineCoverMap_conservative`、`crystallineCoverMap_torAmplitude`、`crystallineCoverMap_prismaticCohomology`、`hodgeTate_iso_of_construction61`、`baseChangeB`、`baseChangeC`、`baseChangeB_conservative`、`baseChange_cechAlexanderAffine_eq`、`hodgeTate_iso`、`bockstein_sq_zero'`、`prismaticCohomology_baseChange'`。b̂* は同値を反映し、b̂*・ĉ* の両方で指定した Čech 模型の Tot を保存する。一変数の加群比較から H²=0 を得て平方零に進み、一般 r の dg 比較へ進む。 |
| DeRhamComparisonPoly | 4 | `deRham_iso_polynomial_crystalline` は Lemma 4.20 の結晶基底変換。`deRham_iso_polynomial_universal` は ψ、J つき pd 脈体、W→C に沿う最後の底変換を通る自然同型。`deRham_iso_polynomial_modP` は各成分がその普遍比較の底変換であることを指定。`deRham_iso_rootAlgebra_modP` は T_∞/p の離散埋め込みとの同型と、T→T_∞ に対する可換四角形。 |

A1 で旧結論が `True` の宣言は **25 件**。指示書の「24 件」は HodgeTateComparison の列挙が実際には 14 件であるため 1 件少ない。別に裸の型だった `affineAlgebra`、`hodgeTateCohomology'`、`universalDistinguishedRing`、`universalOrientedPrismRing`、`crystallineCoverRing` を具体化した。`HodgeTateIsoStatement` と `PrismaticCohomologyBaseChangeStatement` は述語の本体を置き換えたので、この 25 件には含めない。

### 設計判断と要確認

- **D68・D69**　恒久的な文献入力は `crystalline_deRham_polynomial_Zp` の一件。G-A1-14 の `pdRow_contractible` は j>0 に限定した。G-A1-16 では pd 包の δ⁰ 座標と追加 δ 座標の Čech 因子を分け、追加座標を零にする切断を使う。G-A1-17 は `pdPolynomialComparison` として独立に置き、J 上同じ二つの多項式射の持ち上げが同じ射を誘導する条件を含めた。これらと Witt 側の橋は証明予定。比較射を構成したのち A₀→A に沿って移す。
- **D4-03・D4-05**　Bockstein は A を係数環とし、`cohomologyEquivHomology` で cup の H に移した `regularBockstein` を使う。Shared の `bockstein_leibniz` の本証明は基盤待ち。完備形式は `completedDeRhamComplex`、`completedWedge`、`completedDeRhamD` を使い、微分は k 線形。E∞ 実現は可換モノイド複体から `commutativeAlgebraFunctor` と `Operad.restrictAlgebra (augmentation k)` を経て `algebraCAlgSource` に送る。同名の source の頂点は `cAlgVertex` と標準同型。
- **D20・D4-04**　`FlatKoszulComparison` は H₀ の平坦性と全次数の標準底変換射の全単射性。Construction 6.1 の `torAmplitude_modP_le_one` は α mod p の通常の上界 1。`crystallineCoverMap_torAmplitude` は全 K を量化する A0 §2.9 の Koszul 版で上界 **3**。B/p の A 上の Tor 次元の上界 2 に、Kos_B(p,pu) の零元の一段が加わる。普遍 A₀ では K=A₀/(p,d) に対し H⁻³=B/p≠0。利用側の `crystallineCoverMap_finiteTorAmplitude` は有限性だけを公開する。
- **残る接続**　CrystallineInput の `pdTotMap` は Shared の `totEInfinity_map` の型付け待ち。HodgeTateComparison の `moduleReflection` は DerivedGeneral の (p,d) を指定する反射待ち。DeRhamComparisonPoly の `primeAlgReflection` は G-A2-9 の主元 p の CAlg 反射待ち。A0 の `IsCompletelyRegularRel` の本体と D20 の式の接続は A0 実装時に行う。D4-03 の指定どおり A1 からは `hd_reg` を渡す。基盤の `regularShortExact` は、定義の本体が `sorry` の段階でもこの引数が残る形にする必要がある。

### A3 の引数 ← A1 の宣言

| A3 の引数 | 今回の A1 の宣言 |
|---|---|
| A₀、環構造、P₀ | p を明示引数にした `universalOrientedPrismRing p` とその `CommRing`、`universalOrientedPrism p`。ℤ の自由 δ 環で p と互いに素な整数と δ(d) を δ 局所化し、(p,d) 完備化した。 |
| h₀ | `universalOrientedPrism_bounded`。A₀/d₀ の p 正則性を使う。 |
| g と hd、自由変数の像 | `universalOrientedPrism_hom P` の唯一の射と生成元の式、既存 A3 の `lciClassifyingMap` の fᵢ。 |
| Ex 7.9 の特殊化 | `prismaticCohomology_lci_universal` でこれらを A3 の `prismaticCohomology_lci_eq_envelope` に渡す。A3 が使う A2 の底変換・A1 の HT 比較より後の DeRhamComparisonPoly に置いた。 |

### A5 の仮置き → A1 の宣言

| A5/StrongDescent | A1 の接続と係数 |
|---|---|
| `rootDeRhamSource C` | `rootSource p C` = `formsVertex p C 1`。ここで C の標数は p なので完備 de Rham 形式は通常の多項式形式と一致する。 |
| `rootDeRhamAugmentation` | `rootFormsAugmentation p P 1`。次数零では `rootDegreeZeroMap` により X を X₀ mod p に送り、離散標的で正次数は零。 |
| `rootMap_modP_eq_deRham` | `deRham_iso_rootAlgebra_modP p P hP hperf 1` の可換式。左脚は `completedPolynomialRecovery` と `deRham_iso_polynomial_modP`、右脚は根の列の余極限で T_∞/p に至る同型。A5 では `baseChange_phiInv_eq_frobeniusTwist` の係数同型 A/(p,φ⁻¹(d)) ≃ (A/d)/p に沿って移す。 |

### BS-D4 全体

| 停止点 | 結論が `True` だった宣言 | 別に具体化した `Type u := sorry` |
|---|---:|---:|
| 1　A2 | 26 | 1 |
| 2　A3 | 13 | 4 |
| 3　A1 | 25 | 5 |
| 合計 | **64** | **10** |

比較の基準は各部の開始コミット。BS-D4 でこの二種類の仮置きを置き換えた名前つき宣言は計 **74 件**。下記の一覧では、コメントを除いた宣言の結論が `True` であるものだけを数えた。証明、補助宣言、構造体の欄、述語の右辺の変更はこの数に加えていない。

<details>
<summary>drafts 全体に残る、結論が True の名前つき宣言（53件）</summary>

- `DerivedGeneral/CompletionFunctor.lean`（5件）　`completion_isReflective`、`completion_tensor_koszul`、`completion_exact`、`complete_colimit`、`completedBaseChange`
- `DerivedGeneral/ScalarRestriction.lean`（4件）　`derivedInfinityBaseChange_restrictScalars_adjunction`、`cAlgBaseChange_restrictScalars_adjunction`、`derivedInfinityRestrictScalars_completion`、`cAlgRestrictScalars_h0`
- `DerivedGeneral/Truncation.lean`（5件）　`truncationLE_counit`、`truncation_cofiber`、`tStructure_axioms`、`truncationLE_of_isConnective`、`derived_nakayama`
- `Shared/CosimplicialBockstein.lean`（2件）　`bockstein_leibniz`、`bockstein_natural`
- `Shared/CosimplicialEInfinity.lean`（5件）　`totEInfinity_forget`、`totEInfinity_cohomologyRing`、`totEInfinity_isLimitCone`、`totEInfinity_map`、`derivedGlobalSectionsCAlg_eq_totEInfinity`
- `Shared/DeRhamPolynomial.lean`（1件）　`completedForms_eq_derivedCompletion_of_boundedTorsion`
- `Shared/Descendable.lean`（16件）　`isDescendableOver_unit_iff`、`isDescendableOver_pushout`、`isDescendableOver_comp`、`isDescendableOver_tensor`、`isDescendableOver_tot_equiv`、`hasDescentIndexLEOver_two_of_rhom`、`hasDescentIndexLEOver_frobeniusColimit`、`isDescendableOver_complete`、`isDescendable_baseChange`、`isDescendable_comp`、`isDescendable_tensor`、`isDescendable_tot_equiv`、`hasDescentIndexLE_two_of_rhom`、`hasDescentIndexLE_frobeniusColimit`、`isDescendable_complete`、`isDescendable_of_faithfullyFlat`
- `Shared/EInfinityPowerOperation.lean`（4件）　`powerOperationZero_zero`、`powerOperationZero_natural`、`powerOperationZero_natTrans`、`powerOperationZero_eq_frobenius_tot`
- `Sheaves/CAlgValued.lean`（3件）　`forget_conservative`、`forget_sheafify`、`forget_derivedGlobalSections`
- `Sheaves/CechConerveLimit.lean`（1件）　`isLimitCone_iff_restrict_cech_large`
- `Sheaves/GlobalSections.lean`（1件）　`sheafifyUnit_isEquivalence_of_isSheaf`
- `Sheaves/SpaceValued.lean`（6件）　`sheafification_exists_spaces`、`sheafify_discrete_eq`、`localEquiv_of_sheafifyIso`、`discretePushout_isDiscrete`、`sectionsOf_pushout`、`sectionsOf_colimit`

</details>

結論以外の仮置きとして、Shared/DeRhamPolynomial の `exists_unique_dgHom` の仮定 `hlin`、Shared/Descendable の `finiteColimits`・`retracts`・`shifts`・`tensor` の四欄、Sheaves/GlobalSections の二位相比較の存在文中の `True` が残る。A6/ArcSheafProperty の `ValuativeCoverFamily (fun _ => True)` は全付値試験環を選ぶ意図的な述語。A0〜A9 に、結論を `True` にした仮置きはない。

**確認の範囲**　四本の宣言名を開始基準と比較し、コメントを除いて二種類の仮置き、新しい axiom、括弧、実際の import 先を静的に確認した。`git diff --check` を実行した。ビルド・Lean の型検査は行っていない。E3 の証明と各 draft の本体への取り込みは BS-D4 の対象外。
