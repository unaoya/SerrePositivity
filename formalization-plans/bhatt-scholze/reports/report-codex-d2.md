# BS-D2 作業報告

## 第1部　A0 の Frobenius の標的で途中停止

開始時の HEAD は main `68ed1ec05`、作業ツリー・index は空。最初の `prismaticCohomologyFrobenius` の標的について、design-status §2 (A) と D2 指示書 §1 が指す既存宣言を調べた。必要な∞関手と既存宣言の型が異なるため、指示書 §0 の停止条件に従って `True` を残した。具体化した対象宣言は0件。A4 以降は未着手で、停止点1には未到達。

### 指定された名前と必要な型

環準同型 `f : S →+* T` に対し、必要なのは各 T 加群の作用を `s • m = f(s) • m` として読む導来スカラー制限、すなわち `derivedInfinityCategory T ⟶ derivedInfinityCategory S` である。A0 では `f = P.deltaStructure.frobeniusLift : A →+* A`。この関手を Δ の頂点で評価して初めて、Frobenius の標的 φ_{A*}Δ が決まる。

| 照合した宣言 | ソースで確認した型と役割 |
| --- | --- |
| `DGRestrictScalars`、`dgNerveRestrictScalarsIso`（InfinityCategories/Derived/ScalarRestrictionNerve.lean:24,128） | T 線形 dg 圏 D の Hom の係数を S に制限する。得られる同型は `dgNerve S (DGRestrictScalars f D) ≅ dgNerve T D` で、対象は同じ。D に `Semifree T` を入れても左辺の対象は T 上の semifree 複体である。 |
| `derivedInfinityCategory`、`derivedInfinityBaseChange`（InfinityCategories/Derived/InfinityCategory.lean:23、BaseChange.lean:22） | D(S) の模型は `dgNerve S (Semifree S)`。底変更は `derivedInfinityCategory S ⟶ derivedInfinityCategory T` で、係数拡大の dg 関手に上記の nerve 同型を合成して作る。 |
| `derivedRestrictScalars`、`derivedRestrictScalarsFactors`（HomologicalAlgebra/DerivedRestriction.lean:17,22） | 通常の導来圏の関手 `DerivedCategory (ModuleCat T) ⥤ DerivedCategory (ModuleCat S)` と、複体の各項での制限との比較。必要な作用と向きは持つが、∞圏の間の単体的集合の射はこの型から取り出せない。 |

S = T = A の場合にも区別は残る。例えば有界 prism (ℤ_p[[x]], (p)) で係数には恒等、x には x^p を施す Frobenius 持ち上げを取る。自由加群 A のスカラー制限は x の作用が x^p 倍となり、A 加群として 1, x, …, x^{p−1} を基底に持つ。dg nerve の係数制限同型はその自由加群を同じ対象に保つ。これは Frobenius 射そのものへの反例ではなく、二つの操作の違いである。

### 再開に要る仕様

導来スカラー制限 Res_f の∞圏での入口を指定する。例えば `Res_f : derivedInfinityCategory T ⟶ derivedInfinityCategory S` を `derivedInfinityBaseChange f` の右随伴として指定すれば、逆向きの関手とその意味が揃う。A0 の結論は Δ から `Res_f.app _ Δ` への辺となる。構成では S2 の `derivedGlobalSections_map` に O_Δ → Res_f O_Δ を渡し、標的の RΓ を Res_f Δ と比較する。A4 の CAlg 値の制限とその正の反復についても別途型を照合する。

今回は未発見名を Lean に仮置きした箇所は0件。調査は本体・drafts・Mathlib のソース検索のみで、Lean 実行・型検査・ビルドはしていない。

## 第2部　停止点1完了（A0 の Frobenius と A4）

第1部は `641c7db03`。再開時の HEAD は `378b17471`。調整側の `acebb81cc` で M13 の f が明示引数となり、CAlg 版と忘却比較が加わった。`7be013b32` で A2 の離散 Frobenius 成分を A4 で仮置きする方針が記録された。これらを参照して A0・A4 を完了した。`acebb81cc` には同時作業中の A0 の Frobenius と A4 の完全 prism の具体化の一部も入っている。集計は BS-D2 の開始基準 `68ed1ec05` から行った。

| ファイル | 開始時の True から具体化 | 内容 |
| --- | ---: | --- |
| A0/PrismaticSite | 1 | `prismaticCohomologyFrobenius` は Δ から `derivedInfinityRestrictScalars P.deltaStructure.frobeniusLift` を Δ で評価した頂点への D(A) の辺。頂点の評価には `.app (Opposite.op ⦋0⦌)` を使った。 |
| A4/Perfectoidization | 7 | `frobeniusTower` は持ち上げた ℕ の nerve から CAlg_A への図式。第 n 頂点は Res_φⁿ(Δ_S)、第 n 後続辺は Res_φⁿ(φ_S)。実際の余極限余錐を選び、(p,d) 完備化の単位と第0脚から Δ_S→Δ_perf を指定した。shift は Res_φ Δ_perf への可逆な辺で、第0脚と Frobenius が可換。d での底変換の値が S_perfd である。Lemma 8.4 の (a) は忘却後の D^{≥0}、(b) は H⁰ の p ねじれなし・p 完備性・shift を Frobenius とする完全 δ 構造と基底射の整合、(c) は d の正則性と S_perfd の D^{≥0}。完全 prism の生成元には基底の d の像を指定した。filtered 余極限は、指定余錐を完備代数の圏に送った錐が余極限である形で述べた。 |
| A4/InterfaceFields | 7 | 本体の `completionFunctor` と `completionAlgebraUnit` を再利用。E3 の `perfd` は S↦(S^∧)_perfd、`unit` は S→S^∧、Fil₀→Δ̄、余極限の第0脚と完備化単位の mod d の三つの `FunctorHom` の合成。完備な S での比較は、指定完備化単位の**逆同型**を写してから点ごとの比較を合成した。単位成分の一致は、この同じ同型を通したホモトピー圏の射の等号。H⁰ は実際の Barratt–Eccles 代数の `homologyCommRing`・`homologyAlgebra` を使い、E3 の `ringFunctor`・`moduleIso`・`map_compat`・`unit`・`unit_compat` に接続した。 |
| A4/AfterComparison | 2 | 任意の離散 S で、E3 の値と、S 自身に塔・余極限・完備化・mod d を施した直接の式との頂点同型を述べた。証明は D32 の animated 完備化を経て Prop 8.5 系4を使う。Example 8.3 は、標数 p で通常の環の Frobenius 順系の余極限を取り、p 完備化した離散 R 代数との頂点同型。R の作用は順系の第0脚と完備化単位の合成で与える。 |

上の **17件**に加えて、`perfectPrismRing : Type u := sorry` を具体化した。非零の perfectoid 環では A_inf(R) = W(PreTilt R p)、零環では零環。Fontaine 射の核を選んだ prism のイデアルと同定し、商と R の環同型をその同じ射から取る。新規補助宣言を除く二種類の仮置きの合計は **18件**。対象4ファイルには結論の `: True := …` も `: Type u := sorry` も残っていない。

### A2 待ちの仮置き

- `discreteDeltaFrobenius` は `derivedPrismaticFrobenius` の離散 U における CAlg_A の辺。承認どおり型と理由を置いた。BS-D4 で A2 の自然変換の成分に置き換える。CAlg の正の反復は `cAlgRestrictScalars_comp` と両立し、忘却は `cAlgRestrictScalars_forget` で D(A) の反復に移す。
- `directHodgeTateUnit` は S→LΛ_p S≃Fil₀→Δ̄_S の `FunctorHom`。A2 の `hodgeTateUnitCAlg` もまだ True を返すため、BS-D4 でその離散部分への制限に接続する。E3 に使う `hodgeTateUnit` と `toPerfection` は完備化関手に沿った前合成。
- `completePerfectionFunctor` の coherence は A2 の Frobenius 自然変換の塔を関手圏で取って与える。BS-D4 では `CompleteCAlg P` の prism 引数と包含を明示する必要がある。filtered 余極限の証明で、animated な入力の導来完備化をその H⁰ と同一視することは使っていない。

### 要確認・設計との差

`Perfectoidization.lean` の `要確認` は6箇所。最初の三つは A2/G-A4-4 の基盤名、後の三つは ScalarRestriction 側へ渡す補題である。

1. `completeCAlgInclusion` — 完備 CAlg の充満部分圏の包含。
2. `reflectCompleteCAlg` — (p,d) 完備化の反射。A4 では包含との合成と単位の型も明示した。
3. `modPrismFunctor` — A→A/d≃R に沿う CAlg 底変換。`modPrismAdjunction` は対応する係数制限との随伴。
4. `restrictFrobeniusTowerColimit` — 完全基底の φ_A に沿う制限が指定された塔の余極限錐を保つこと。
5. `restrictFrobeniusCompletion` — 同じ制限と (p,d) 完備化との `FunctorIso`。
6. `restrictH0Equiv` — 制限前後の H⁰ の台の環の標準同型。`restrictH0Equiv_base` に係数作用を f に沿って読む等式を置いた。

A0 には指定外の既存注記2箇所（`structurePresheafDerived` の小さい nerve の比較と `hodgeTateCohomology` の導来テンソル）が残る。InterfaceFields・AfterComparison は0件。第1部の食い違いは M13 の D 版・CAlg 版で解決した。A2 の Frobenius 成分の仮置き以外に、新たな数学的主張の変更はない。

今回の確認は、参照名のソース照合、変更4ファイルでの対象宣言・import 先・括弧の照合、`git diff --check`。Lean の実行・型検査・ビルドは行っていない。A2 と DerivedGeneral/ScalarRestriction は編集していない。停止点2（A7）以降は未着手。

## 第 3 部　停止点 2（A7、基準 main `bfbc0167e`）

A7 の4ファイルで、基準コミットにあった結論 `True` の宣言 **22 件**を具体化した。既に型のあった `e3Universal` は別に扱い、E3 の欄に合わせて基底の perfectoid 性と完備化を経る証明の入口を明示した。

| ファイル | 件数 | 今回の型 |
| --- | ---: | --- |
| A7/AnimatedDomain | 2 | `animatedForget` を通して底の導来加群の p 完備性を判定する充満部分圏、そこへの反射と随伴の単位。導来 mod pⁿ の塔は、通常の R ← R[t] → R を animated な塔の圏で押し出し、X と R 上で導来テンソルして作る。完備化の頂点をもつ極限錐と、完備離散代数の埋め込みを指定した。π₀(X)/pⁿ の遷移が全射なのでこの系の lim¹ が消える。 |
| A7/AnimatedPerfectoidization | 10 | 二側 bar を Δ[1] の単体の要素圏から Δᵒᵖ への左 Kan 延長で表した。次数 n の n+2 個の因子は左端・n 個の中央・右端。押し出し余錐が Δ・Frobenius の余極限・完備化・mod d の各段で余極限になる条件を置いた。塔の後続辺は τⁿ(φ)、τ は Frobenius に沿う係数制限。完備 CAlg の押し出し余錐から、入力の押し出しを perfd で送った余錐へ移る辺が Prop 8.13 の標準比較射で、その辺の可逆性を結論とした。離散版との比較は完備離散代数の nerve 上の `FunctorIso`。 |
| A7/DiscreteCore | 3 | d 完備な Δ_perf の離散性、H⁰(Δ_perf) 上の完全 prism（生成元は基底の d の像、その商は H⁰(S_perfd) と環同型）、H⁰(S_perfd) の perfectoid 性。A4 の `prismaticPerfection_h0_perfectDelta` と `prismaticPerfectionPrism` を参照する。 |
| A7/UniversalProperty | 7 | perfectoid T で指定単位が可逆になること、比較の脚の mod d による延長の存在、G-A7-8 の等式、自己テンソルの同値と乗法の等式、環準同型の一意性、完備離散 S での Cor 8.14。任意の離散 S に対する `e3Universal` は S^∧ に適用し、A4 の三つの `_of_complete` と `completion_existsUnique` により E3 の単位へ戻す。 |

G-A7-8 では P = H⁰(FS) の離散表示を H⁰ で規格化し、F(η_S) と η_P を同じ始域の射として比較する。証明の入口は A5 の極限の脚 λ_f ∘ q = λ_f から得る q = id_P と比較の自然性。続く自己テンソルの同値 e には、Prop 8.13 の左右の脚を η_P の後に合成すると両方とも恒等になる条件を付けた。これにより e ∘ η_X = m を、離散とは限らない X の E∞ 実現からの射として書ける。離散標的 T への写像は Hom(π₀X,T) で判定する。AnimatedDomain と DiscreteCore は A5 を参照する証明を必要としない。

### 要確認と A2 待ち

`-- 要確認：` は **5 箇所**。BS-D4 で接続する型と既存の仮置きの対応は次のとおり。

1. AnimatedDomain の `animatedForget`。A2 の `exists_siftedExtension` が返す sifted 保存と、多項式生成系への制限同型を具体化する。
2. AnimatedPerfectoidization の `animatedDelta`。A/d ≃ R に沿って R 代数を A/d 代数として読む animated 基底移送。A4 では同じ向きを通常の `Under.map` で扱っている。
3. 同ファイルの `animatedDeltaFrobenius`。A2 の `derivedPrismaticFrobenius` の自然変換。離散成分には A4 の `discreteDeltaFrobenius` を使う。完備圏の包含・反射・mod d は A4 の `completeCAlgInclusion`・`reflectCompleteCAlg`・`modPrismFunctor` を使用した。
4. UniversalProperty の `animatedRealization`。A2 の `hodgeTateUnitCAlg` の始域になる animated 代数の E∞ 実現。多項式環の離散 E∞ 実現からの sifted 延長で指定した。
5. 同ファイルの `animatedPerfdUnit` 内の Fil₀ の射。A2 の `hodgeTateUnitCAlg` を完備入力に制限し、同じ塔の第0脚と完備化単位の mod d を合成する。`animatedPerfdUnit_discrete` は、離散制限が A4 の `directHodgeTateUnit ≫ directToPerfection` に一致する等式。

DiscreteCore の要確認は0件。A5 の `perfectoidization_semiperfectoid_iso` と `perfectionComparisonLeg` は証明の依存先で、A7 の宣言の型には仮の A5 成分を追加していない。

### 設計との照合

A7 の主張に設計との食い違いはない。D60 の完備 animated 定義域、W9-II-23 の単位の整合性、W9-II-24 の A5 より前に置く二ファイルを維持した。

関連する基盤に一件、A7 の範囲外の注意がある。`ScalarRestriction.lean` の `cAlgRestrictScalars_isColimitCone` は任意の環写像と任意の図式形状を量化する。しかし ℤ → 𝔽₂ に沿う制限は、𝔽₂ 代数の始対象 𝔽₂ を ℤ 代数の始対象へ送らない（空図式が反例）。押し出しや sequential 余極限にはこの反例は当たらない。A7 では完全 prism の φ_A が自己同型であることから τ と完備圏へのその制限が押し出しを保つことを使った。この基盤宣言は使わず、ScalarRestriction も A4 も編集していない。

基準コミットと宣言名を照合し、22 件すべてが残り、A7 の4ファイルに `True` が残らないことを確認した。参照名・import パス・括弧・`git diff --check` を静的に確認した。Lean による型検査・ビルドは行っていない。証明は理由付きの `sorry`。停止点 3（A8）は未着手。

## 第4部　A8 の途中停止（基準 main `6a7e6ec04`）

### 具体化した宣言

`A8/AlmostConnectivity.lean` の11件中9件を具体化した。一般の J に対する `perfectoidKernel` は B3 の `toQuotientPerfectoidization` と商写像の合成の核であり、単項 g 用の既存 `perfectoidIdeal` から独立している。

- `IsAlmostConnective` は i > 0 の各 `derivedInfinityHomology R i M` を K が零化する条件。`IsJAlmostZero` は全次数での条件。完備テンソルは D(R) の二つの頂点の semifree 複体を `cochainTensor` でテンソルし、`derivedComplexCompletionFunctor` で完備化した頂点。
- `restrictScalars_perfectoidQuotient_fullyFaithful` は完備部分圏上の係数制限の完全忠実性と指定した極限錐・余極限余錐の保存。`isAlmostZero_iff_completedTensor_isZero` の非有界の場合はこの像で Postnikov の極限・完備余極限を取る。 `isAlmostConnective_iff_completedTensor_connective`、`isAlmostConnective_completedFilteredColimit`、`connective_iff_almost` を同じ K、B と完備テンソルで記述した。G-A8-8 はこの余極限の主張に使わない。
- `perfectoidIdeal_radical`、`isAlmostZero_radical`、`isAlmostZero_iff_forall_gen` を具体化。最後の証明の入口は Q の π₀ を経る Prop 8.5 系4 と、その後の Prop 8.13 の比較。

### 停止規則に該当する点

a8-design §3.1 と `perfectoidIdeal_baseChange` の docstring には (JR′)_perfd = J_perfd R′ とある。f : R → R′、K = J_perfd として、右辺を `K.map f` と読むことと、p 進閉包を取ることは別の Lean の主張である。

Prop 8.13 による比較は B の**完備**底変換であり、R′ からこの完備商への核を比較する。通常の `K.map f` との等号をここから得るには、`K.map f` 自体が p 進閉であることをさらに示す必要がある。有限生成 J と p 完全平坦な射に対する Fayolle の Proposition 2.9 には、この右辺に明示的に p 進閉包が付く。J が有限生成でも K の有限生成性は仮定されていない。閉包を外す根拠は確認できなかった。通常の等式への反例を確認したわけではない。[Fayolle, *Centers of perfectoid purity*, Proposition 2.9](https://jep.centre-mersenne.org/item/10.5802/jep.313.pdf)

一般 J では完備底変換への単位の核を比較し、有限生成 J のイデアル等式には閉包を明記するか、通常の `Ideal.map` の閉性を別に示すか、設計側の判断を求めた。主張を書き替えず、`perfectoidIdeal_baseChange` と `isAlmostZero_baseChange_iff` の直前で止めた。

### 現在の件数と確認範囲

今回具体化した9件に新規の仮名による `-- 要確認：` は0件。上記の設計判断は1件。A8 の対象40件中、残る `True` は31件（AlmostConnectivity の上の2件、AlmostPurityConnectivity の12件、IntegralDiscreteness の17件。宣言名の一覧は BS-D1 報告第7部）。BS-D2 全体では結論の `True` を17 + 22 + 9 = 48件具体化し、停止点1での `perfectPrismRing : Type u` も含めると49件。A8 の型の仮置き `trivialCoverComparison`、`integralClosureInLocalization`、`integralClosureCompletion` も残る。停止点3の検収・最終総括には未到達。

参照名と引数をリポジトリで照合し、差分に `git diff --check` を実施。型検査とビルドは行っていない。

## 第5部　停止点3完了（A8）と BS-D2 の総括

基準は main `6a7e6ec04`。第4部の停止事項は設計側で D2-02 として解決した。今回の A8 の途中差分は `be5d982fe`、`c4b9e3caa` にも取り込まれた。両コミットを維持し、以下の件数は基準からの通算で数える。

| ファイル | 元の `True` | そのほかに具体化した型と射 |
| --- | ---: | --- |
| A8/AlmostConnectivity | 11 | 一般の J に対する B3 の標準射と核 K、完備部分圏での係数制限、非有界な完備複体での Prop 10.4 と Lemma 10.5。D2-02 の底変換は `K → R` を完備底変換して H⁰ を取った指定射の単射性・像の等式。 |
| A8/AlmostPurityConnectivity | 12 | S は有限表示有限。Thm 7.14 と主開分裂を経由し、指定された分裂同型を引数に S と Rʳ の像の生成部分代数 S′、二つの構造射、その整性・局所化後の全単射性・S′ の加群完備性を記述。Cor 8.12 の代数 U,V とイデアル I の完備性を明示し、perfd による指定射の fibre の J-almost 零性を結論にした。Thm 10.9 の結論は正次数に限る。 |
| A8/IntegralDiscreteness | 17 | G-A8-6・8・9、層別長の帰納、G-A8-10・11、Thm 10.11 と E3 への接続。被約化での比較は商写像自体の可逆性。D70 の T は S_red[1/g] の部分代数、T̂ は `completionRing` の構造射をもつ R 代数。S→T は整、S→T̂ は ArcOutside。生の T の非完備例も存在命題として記述した。 |

帰納段では `StratumRing`、`HasEtaleFactorization` と `exists_finiteEtaleStratification` を使い、Lemma 10.12 の入口には指定の `hZp` を置いた。Q = S ⊗̂ᴸ_R R/g の perfd から、π₀Q = S/g の perfd へは Prop 8.5 系4、S_perfd ⊗̂ᴸ_R (R/g)_perfd へは Prop 8.13 で比較する。`quotientTensor_comparisons` は R₁ = (R/g)_perfd との完備テンソルの π₀ を経る比較も含む。残りの層は R₁ に底変換した後で被約化する。

G-A8-11 の系には、各有限表示有限代数 A_λ から T への**指定された脚**があり、その脚から誘導する A_λ[1/g] → B が全単射である。各 A_λ に Thm 10.9 を適用し、G-A8-1 の完備 filtered 余極限の系で T̂_perfd に移す。Cor 8.12 の適用先は S→T̂。G-A8-8 は有限表示有限の連結性を得た後、一般の整代数に移す段でのみ使う。完全 prism の余極限には p 完備化、次に d 完備化を施す。E3 の `integral` は animated な LΛ_p S とその π₀ = completionRing S の perfd を系4で比較して得る。

### 設計判断と要確認

- **D2-02。** (JR′)_perfd は完備テンソル K ⊗̂_R R′ → R′ の像。有限生成 J のイデアルの式には K R′ の p 進閉包が現れる。K が有限生成なら閉包との一致を得られるが、J_perfd は一般には有限生成でない。almost 零性の反映には K′ ≃ K ⊗̂_R R′ だけを使う。[Fayolle, Proposition 2.9](https://jep.centre-mersenne.org/item/10.5802/jep.313.pdf)
- 商の p 冪ねじれ有界だけから通常の `Ideal.map` との一致は導かない。反例は V を p ねじれなしの混標数 perfectoid 付値環、R = V⟨x₁^{1/p∞},x₂^{1/p∞},…⟩、J = ker(R→V)、R′ = R⟨t^{1/p∞}⟩ とするもの。J=K。R′/p は R/p 上自由で、R,R′ は p ねじれなしなので Tor₁ᴿ(R′,V/p)=0。V の p 倍の短完全列により R′/KR′ = R′⊗_R V は p ねじれなし。一方 ∑_{n≥1} pⁿxₙtⁿ は KR′ の閉包に入る。KR′ に入るなら係数の全てが有限個の k₁,…,k_s ∈ K の生成イデアルに入る。p を反転するとその真のイデアルが正則列 x₁,…,x_{s+1} を含んでしまう。正則性はモノミアル係数で判定でき、s 元で生成する真のイデアルはそのような列を含まない（生成元の Koszul コホモロジーは次数 s で商環、長さ s+1 の正則列を含めば次数 ≤ s で零）。設計側の決定どおり追加補題は置かなかった。
- A8 の3ファイルに、名前未確定の `-- 要確認：` は0件。依存する証明には A5 の `perfectoidization_piZero`、A6 の `perfectoidization_excision` と E3 非依存の Lemma 10.3 の芯が残る。Thm 7.14 のソースは `Andre/Transfinite/Tower.lean`、主開分裂は `IsAbsolutelyIntegrallyClosed.finiteEtaleAway_exists_finite_cover`、付値環への延長は `existsUnique_valuation_extension_of_integral_away_bijective` を照合した。A2 の仮名は増やしていない。
- 以前の要確認は第2部の A4 の6箇所（A2 の3件と ScalarRestriction の3件）、第3部の A7 の5箇所。第1部の D と CAlg の係数制限の区別は M13 で解決した。A4 の基盤側の3件には一般形が追加され、CAlg の全余極限保存の範囲は D2-01 で修正済み。A2 との接続待ちの離散 Frobenius・Fil₀ の射と完備圏の包含・反射・mod d の対応は第2〜3部の一覧に従う。D2-02 以外の A8 の主張変更はない。

### BS-D2 全体の件数

| 停止点 | 結論の `True` を具体化 | `Type u := sorry` を具体化 |
| --- | ---: | ---: |
| 1（A0 残り・A4） | 17 | 1 |
| 2（A7） | 22 | 0 |
| 3（A8 残り） | 40 | 3 |
| **合計** | **79** | **4** |

二種類の仮置きを直した既存宣言は **83件**。A8 の型3件は `trivialCoverComparison`、`integralClosureInLocalization`、`integralClosureCompletion`。既に具体的な型を持っていた G-A8-6 と `e3Integral` の引数・証明方針の整備、新設の補助宣言は集計外。BS-D2 の指定ファイルに残る結論の `True` は0件。

<details>
<summary>drafts 全体に残る、結論が文字どおり True の名前つき宣言（194件）</summary>

- `A1/CrystallineInput.lean`（2件）　`crystalline_deRham_polynomial_Zp`、`hodgeTate_of_deRham_cartier`
- `A1/DeRhamComparisonPoly.lean`（4件）　`deRham_iso_polynomial_crystalline`、`deRham_iso_polynomial_universal`、`deRham_iso_polynomial_modP`、`deRham_iso_rootAlgebra_modP`
- `A1/HodgeTateComparison.lean`（14件）　`hodgeTate_iso_polynomial_Zp`、`hodgeTate_iso_crystalline`、`universalOrientedPrism_frobenius_flat`、`crystallineCoverMap_conservative`、`crystallineCoverMap_torAmplitude`、`crystallineCoverMap_prismaticCohomology`、`hodgeTate_iso_of_construction61`、`baseChangeB`、`baseChangeC`、`baseChangeB_conservative`、`baseChange_cechAlexanderAffine_eq`、`hodgeTate_iso`、`bockstein_sq_zero'`、`prismaticCohomology_baseChange'`
- `A1/HodgeTateMap.lean`（5件）　`reducedModel`、`hodgeTateMapZero`、`hodgeTateMapOne`、`bockstein_sq_zero`、`hodgeTateMap`
- `A2/AnimatedAlgebra.lean`（5件）　`polyCoproduct_isCoproduct`、`polyYoneda_fullyFaithful`、`animatedAlgebra_siftedColimits`、`discreteToAnimated_poly`、`discreteToAnimated_fullyFaithful`
- `A2/BaseChangeAndTensor.lean`（5件）　`derivedPrismaticCohomology_baseChange`、`derivedPrismaticCohomology_siftedColimit`、`prismaticCohomologyPoly_tensor`、`derivedPrismaticCohomology_tensor`、`derivedPrismaticCohomology_completion_animated`
- `A2/DerivedPrismaticCohomology.lean`（9件）　`completeCAlg_siftedColimits`、`prismaticCohomologyCAlg`、`prismaticCohomologyCAlg_eq_totEInfinity`、`prismaticFrobeniusPoly`、`derivedPrismaticCohomology_preservesSifted`、`derivedPrismaticCohomology_poly`、`derivedPrismaticFrobenius`、`derivedPrismaticCohomologyDerived`、`derivedPrismaticCohomology_h0_ring`
- `A2/HodgeTateFiltration.lean`（7件）　`hodgeTatePoly_gr`、`hodgeTatePoly_bounded`、`hodgeTateFiltration_step`、`hodgeTateFiltration_gr`、`hodgeTateFiltration_exhaustive`、`hodgeTateFiltration_zero`、`hodgeTateUnitCAlg`
- `A3/DiscreteCase.lean`（3件）　`deltaStructure_of_envelopeIso`、`discrete_weaklyInitial`、`exists_initial_of_discrete`
- `A3/LciAndQuasiregular.lean`（10件）　`lciDerivedEnvelope`、`lciDerivedEnvelope_eq_prismatic`、`lciDerivedEnvelope_isEnvelope_of_discrete`、`lci_envelope_surjective_invert_p_universal`、`prismaticCohomology_lci_eq_envelope`、`qrsp_isDiscretePrismatic`、`qrsp_completelyFaithfullyFlat`、`regularSemiperfectoid_prismatic`、`qrsp_initial`、`rootQuotient_prismatic_perfection_eq`
- `A5/PerfectSite.lean`（8件）　`perfUnder_cechNerveData`、`perfectSite_cechNerveData`、`perfectStructurePresheaf`、`perfectStructurePresheaf_isSheaf`、`perfectPrism_hom_lift_unique`、`perfectSiteEquivPerfectoidUnder`、`perfectionComparisonLeg`、`perfectionComparison`
- `A5/PerfectSiteComparison.lean`（8件）　`perfectionComparison_isIso`、`perfectionComparison_isIso_topology`、`perfectoidization_isLimit`、`perfectoidization_isLimit_u`、`perfectoidization_indep`、`perfectoidization_semiperfectoid`、`perfectionComparison_isIso_animated`、`perfectoidization_piZero`
- `A5/RootAdjunction.lean`（2件）　`algebraicRootClosure_filteredColimit`、`polyAlgebraToRoot_pCompletelyFaithfullyFlat`
- `A5/SemiperfectoidCase.lean`（17件）　`baseComparison`、`cotangent_perfectoid_vanish`、`derivedPrismaticCohomology_baseIndep`、`cotangent_shift_connective_of_semiperfectoid`、`hodgeTate_connective_of_semiperfectoid`、`prismaticPerfection_connective_of_semiperfectoid`、`perfectoidization_discrete_of_semiperfectoid`、`perfectoidization_isIntegralPerfectoid_of_semiperfectoid`、`universalPerfectoidUnit_isPerfectoidization`、`perfectoidizationToUniversal`、`perfectoidizationToUniversal_splitSurjective`、`exists_perfectoid_surjection`、`rootQuotient_to_perfectoidization_surjective`、`rootQuotient_finite_reduction`、`rootQuotient_unit_surjective`、`surjective_unit_of_semiperfectoid`、`perfectoidization_semiperfectoid_iso`
- `A5/StrongDescent.lean`（11件）　`prismaticCohomology_rootMap_descendable`、`prismaticPerfection_rootMap_descendable'`、`rootMap_descendable_of_one`、`rootMap_fiber_rhom_coconnective`、`coconnective_of_modBaseChange`、`rhom_baseChange_koszul_connection`、`baseChange_phiInv_eq_frobeniusTwist`、`rootMap_modP_eq_deRham`、`deRhamOneVariable_formal`、`squareZero_rhom_coconnective`、`rootMap_descendable_one`
- `A5/WeaklyInitialAndDescent.lean`（15件）　`algebraicRootCover_properties`、`cech_independent_of_flatSemiperfectoidCover`、`perfectoidTargetWeaklyInitial`、`perfectoidTargetWeaklyInitial_isWeaklyInitial`、`limit_perfUnder_eq_tot`、`limit_perfectSite_eq_tot`、`limit_perfUnder_eq_limit_perfectSite`、`tot_coconnective_filteredColimit`、`limit_perfectSite_filteredColimit`、`perfectionComparison_isIso_of_finiteType_cases`、`rootCover_isSemiperfectoid`、`prismaticPerfection_rootCover_descent`、`perfUnder_leftAdjoint_initial`、`limit_perfectSite_rootCover_descent`、`perfectionComparison_isIso_of_finiteType`
- `A6/Excision.lean`（6件）　`sectionsOf_homSheaf_eq_perfectoidization`、`homPresheafPushout_localEquiv`、`perfectoidization_excision`、`quotient_isModuleComplete`、`homPresheaf_completionRing_iso`、`sectionsOf_homSheaf_eq_e3Perfd`
- `A6/PerfectoidFiniteProduct.lean`（1件）　`fontaineTheta_prod_compat`
- `A6/SheafOfSetsExcision.lean`（13件）　`isArcCover_of_arcOutside`、`isArcCover_diagonal_of_arcOutside`、`isArcCover_quotient_split`、`perfectoid_factor_of_idempotent`、`perfdUnderProdEquiv`、`perfectoidization_prod`、`excision_of_excision_prod`、`extendArcSheaf`、`sheafOfSets_excision`、`homSheaf`、`hom_homSheaf_eq`、`homSheaf_pushout`、`homSheaf_quotient_mono`
- `DerivedGeneral/CompletionFunctor.lean`（5件）　`completion_isReflective`、`completion_tensor_koszul`、`completion_exact`、`complete_colimit`、`completedBaseChange`
- `DerivedGeneral/ScalarRestriction.lean`（3件）　`derivedInfinityBaseChange_restrictScalars_adjunction`、`derivedInfinityRestrictScalars_completion`、`cAlgRestrictScalars_h0`
- `DerivedGeneral/Truncation.lean`（5件）　`truncationLE_counit`、`truncation_cofiber`、`tStructure_axioms`、`truncationLE_of_isConnective`、`derived_nakayama`
- `Shared/CosimplicialBockstein.lean`（4件）　`regularShortExact`、`bockstein_leibniz`、`bockstein_sq`、`bockstein_natural`
- `Shared/CosimplicialCupProduct.lean`（1件）　`cohomologyCup_map`
- `Shared/CosimplicialEInfinity.lean`（5件）　`totEInfinity_forget`、`totEInfinity_cohomologyRing`、`totEInfinity_isLimitCone`、`totEInfinity_map`、`derivedGlobalSectionsCAlg_eq_totEInfinity`
- `Shared/Descendable.lean`（9件）　`IsDescendableOver`、`isDescendable_baseChange`、`isDescendable_comp`、`isDescendable_tensor`、`isDescendable_tot_equiv`、`hasDescentIndexLE_two_of_rhom`、`hasDescentIndexLE_frobeniusColimit`、`isDescendable_complete`、`isDescendable_of_faithfullyFlat`
- `Shared/EInfinityPowerOperation.lean`（4件）　`powerOperationZero_zero`、`powerOperationZero_natural`、`powerOperationZero_natTrans`、`powerOperationZero_eq_frobenius_tot`
- `Sheaves/CAlgValued.lean`（3件）　`forget_conservative`、`forget_sheafify`、`forget_derivedGlobalSections`
- `Sheaves/GlobalSections.lean`（1件）　`sheafifyUnit_isEquivalence_of_isSheaf`
- `Sheaves/SpaceValued.lean`（9件）　`sheafification_exists_spaces`、`sheafify_discrete_eq`、`localEquiv_of_sheafifyIso`、`discretePushout_isDiscrete`、`sectionsOf`、`sectionsOf_colimit`、`sectionsOf_representable`、`sections_localEquiv_iso`、`sectionsOf_eq_limit_elements`

</details>

BS-D1 第7部と同じく、コメント・証明・仮定だけに現れる True は集計外。BS-D1 時点の270件から BS-D2 の79件を引き、別途追加された ScalarRestriction の3件を加えて194件。基準の A8 の宣言名40件、import のファイルパス、括弧、変更範囲、差分の空白を静的に確認した。指定どおり Lean の型検査・ビルドは行っていない。
