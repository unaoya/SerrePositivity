# BS 設計段階の状態と要確認の一覧（2026-11-02）

概要：BS の設計段階（ビルドなし、`drafts/` に骨組み）の到達点と、骨組みに残した「要確認」の分類。A0〜A1 の設計書・骨組みを一度見直した結果。
方針：要確認を五つに分ける：(A) 基盤の名前を探すだけ、(B) BS 側で決める設計の細部、(C) ∞ 側の窓に依存、(D) 論文の層の区切り 2b の後に
HA を読んでから、(E) 結晶側の黒箱。A・B は中身を書く段階の最初に片づけ、C・D は時期を待ち、E は独立の作業単位。
規約：状態の表は進捗報告の書式（一段目は全項目、進行中の親の下は二段目を全項目、一項目一行）。日付は絶対表記。
決定の一覧は各設計書（U・D・D-S・D-A1 番号）を正本とし、ここでは所在だけ示す。
使われ方：設計段階の進捗の正本。調整役への中間報告の元。中身を書く段階に入るときの作業一覧。

## 1. 状態

| 単位 | 設計書 | 骨組み（drafts） | 紙の検証 | 中身 |
| --- | --- | --- | --- | --- |
| ∞ 層 S1 層条件 | infinity-sheaves-design §1・§3 | Sheaves/SheafCondition | — | C（JoinCone.ulift、生成系で十分の補題） |
| ∞ 層 S2 Γ・RΓ | 同 | Sheaves/GlobalSections | — | C（層化の存在 S4 は入力） |
| ∞ 層 S3 脚注 10 | 同 §1 | Sheaves/CechConerveLimit | — | C（G9・G10） |
| ∞ 層 S4 層化の存在 | 同 §1 の 1〜4 | GlobalSections の `sheafification_exists` | — | C（G3・G4・G6・G8） |
| ∞ 層 S5 完全性 | 同 §1 の 5 | 未 | — | C（G7） |
| ∞ 層 S6 κ | 同 §5 | A0/PrismaticSite の `essentiallySmall` | 済（a0 §5.1 の 4） | B（構造の移送） |
| ∞ 層 S7 D(A) への適用 | 同 §4 G3 | 未 | — | C |
| A0-1 site・Not 4.16 | a0-design §2.1〜2.4・2.7 | A0/PrismaticSite | 済（κ） | A（4 件）・B（κ 不変性の形） |
| A0-2 Čech–Alexander | a0-design §2.8 | A0/CechAlexander | 済（弱始性・余積） | A（1 件）・B（R の形、cechKernel、型合わせ） |
| A0-3a Def 2.42 | a0-design §2.5 | A0/PrismaticEnvelope | — | A（Koszul の名前） |
| A0-3c Prop 3.13 の定義と変数の場合 | a0-design §2.5 | A0/PrismaticEnvelope | 済（a0 §5.1 の 1・2） | A（完備テンソル）・B（閉包の定義） |
| A0-3b Lemma 3.7(2)(3) | a0-design §2.6 | 未 | 自由加群の場合は済（a0 §5.1 の 1） | D |
| A0-3d Cor 3.12 | a0-design §2.6 | PrismaticSite の `flatTopology_refine` のみ | 未（a0 §5 の 5・6） | D |
| A0-4 Lemma 4.22・4.20 | a0-design §2.9 | 未 | — | D |
| A1-1 de Rham・η^* | a1-design §2.1・2.2 | A1/HodgeTateMap、Shared/{CupProduct,Bockstein,DeRhamPolynomial} | — | B（R の形、線形性の述べ方、係数環）・A（忘却関手） |
| A1-4 Prop 6.2・Thm 6.3 | a1-design §2.4・2.5・§3 | A1/HodgeTateComparison | 未（a1 §8 の 5〜7） | A（Flat の形）・D（G-A1-4・5・13） |
| A1-2 結晶側の対象 | a1-design §2.3 | 未 | 未（a1 §8 の 1・2） | E |
| A1-3 Lemma 5.4・Thm 5.2 β・Cartier・Cor 5.5 | a1-design §3 の 3〜6 | 未 | 未（a1 §8 の 3・4） | E |
| A2-1 animated 代数（P_Σ）・離散環の埋め込み | a2-design §2.1 | A2/AnimatedAlgebra | 未（a2 §7 の 1） | A（Yoneda の名前、集合値前層の離散埋め込み） |
| A2-2 Δ の Kan 延長・Frobenius・(1) | a2-design §2.2 | A2/DerivedPrismaticCohomology | — | C（G-A2-3・4）、G-A1-11 |
| G-A1-11 CAlg 値の層・RΓ、模型の E∞ 構造 | a1-design G-A1-11、a2-design §2.2 | Sheaves/CAlgValued、Shared/CosimplicialEInfinity | — | C（G12、U の保存性、Barratt–Eccles の余鎖作用の形） |
| A2-3 HT filtration・cotangentWedge | a2-design §2.3 | A2/HodgeTateFiltration | 未（a2 §7 の 2） | C（G-A2-2） |
| G-A2-2 D(A) の t 構造・切り捨て | a2-design §3 | DerivedGeneral/Truncation | — | C（置き場所は調整役、BS が骨組み） |
| G-A2-3 (p,d) 完備化の ∞ 関手 | a2-design §3 | DerivedGeneral/CompletionFunctor | — | C・D（HA の名前は 2b 後） |
| A2-4 完備化不変性・(4)・(5) | a2-design §2.4 | A2/BaseChangeAndTensor | 未（a2 §7 の 3・4） | C・D |
| A3-1 Lemma 7.8、Lemma 7.7(2)(3) | a3-design §2.1 | A3/DiscreteCase | — | A（Mathlib の冪等完備・Under）、C（S2 の極限の脚） |
| A3-2 Lemma 7.7(1′)(1″) | a3-design §2.1 | A3/DiscreteCase | — | A（Rem 2.2 の δ 構造の名前） |
| A3-3 Ex 7.9 | a3-design §2.2 | A3/LciAndQuasiregular | 未（a3 §8 の 1〜3） | E′（p 反転の議論 G-A3-7 は A3 の黒箱）、G-A3-1・2 |
| A3-4 qrsp・Prop 7.10・Cor 7.3 との接続 | a3-design §2.3 | A3/LciAndQuasiregular | 未（a3 §8 の 4〜6） | G-A3-3・4・8、RootEnvelope の対応表 |
| A4-1 Not 8.1・Def 8.2 | a4-design §2.1 | A4/Perfectoidization | — | C（G-A4-2・3・4）、A（Thm 3.10 の prism の名前） |
| A4-3 E3 の perfd・unit・h0 | a4-design §2.3 | A4/InterfaceFields | — | A（`completionRing` の関手版、CAlg_R の H⁰ の環）、D（2b の改名） |
| A4-2 Lemma 8.4 | a4-design §2.2 | A4/Perfectoidization | 済（a4 §5 の P⁰ の筋） | G-A4-1、A（Lemma 2.34 の名前）、A3-2 |
| G-A4-1 E∞-F_p 代数の P⁰ | a4-design §3 | Shared/EInfinityPowerOperation | — | C（置き場所は `EInfinity/PowerOperation/`、M14。担当は A4 の中身の段階で。Barratt–Eccles の作用の型） |
| A4-4 Example 8.3 | a4-design §2.4 | A4/Perfectoidization | — | A5 の後（Prop 8.5 を使う）。A6 で要るか確認 |
| A5-1 完全 site・Lemma 4.8・比較写像・Prop 8.5 の主張と系・E3 の limitCone | a5-design §2 | A5/PerfectSiteComparison、A5/InterfaceLimitCone | — | A（`PerfectPrismHomLift`、Cor 7.3 の対象、`SmallModel`）、C（S2・S3）、D（A0-3d の制限 G-A5-5） |
| A5-2 semiperfectoid の場合・G-A5-17 | a5-design §3.4 | A5/SemiperfectoidCase | 未（a5 §8 の 5） | G-A5-10・11・17、A2-3、A3-4 |
| A5-4 弱始対象・filtered 余極限・降下の形式部分 | a5-design §3.1〜3.3 | A5/WeaklyInitialAndDescent | 未（a5 §8 の 1〜4） | G-A5-2・7・8・14 |
| A5-3 descendability・Lemma 8.6 | a5-design §2.4・§3.5 | Shared/Descendable、A5/StrongDescent | 未（a5 §8 の 6・7） | G-A5-1（置き場所 `EInfinity/Descendable/`、M15）・6・12・13・15（A1-5） |
| A6-1 arc site・cover-dense | a6-design §2.1 | A6/ArcSite | 済（a6 §9） | A（Mathlib `IsCoverDense`・`SmallModel`）、G-A6-3 |
| A6-3 集合の層の等式・perfd の有限積 | a6-design §3.2 の 1〜4 | A6/SheafOfSetsExcision | 未（a6 §8 の 5・6） | A（Mathlib `Sheaf`・`sheafEquiv`）、G-A6-2・9 |
| A6-2 Prop 8.10・三つの引用 | a6-design §2.2・§3.1 | A6/ArcSheafProperty | 未（a6 §8 の 2・3） | E′（G-A6-1a・1b `sorry`、1c は証明）、G-A6-4〜7 |
| A6-4 Cor 8.12・E3 の excision | a6-design §2.3・§3.2 の 5・6 | A6/Excision | 未（a6 §8 の 4） | C（S8）、G-A6-10 |
| S8 空間値の層・局所性 | a6-design §2.4 | Sheaves/SpaceValued | — | C（置き場所は M12e：Sheaves/SpaceValued/・Sheaves/Discrete/・F2/。前提 G13 と S4 非安定版） |
| A7-1 Def 8.2 の animated 版・(5) 相対版・Prop 8.13 | a7-design §2.1・§2.2 | A7/AnimatedPerfectoidization | 未（a7 §7 の 1・2・6） | C（G-A7-1・2：P_Σ の押し出し・完備化）、G-A7-4 |
| A7-2 Cor 8.14・E3 の universal | a7-design §2.3 | A7/UniversalProperty | 未（a7 §7 の 3〜5） | A（`IsPerfectoidization`、`completionRing` の普遍性）、A5-2 の芯の共有 |
| A8-1 Prop 10.4 複体版・Lemma 10.5・J-almost の基本 | a8-design §2.1・§3.1 | A8/AlmostConnectivity | 未（a8 §8 の 1） | B5 の既存、A7 |
| A8-2 Thm 10.9 の J-almost 連結性 | a8-design §2.2・§3.2 | A8/AlmostPurityConnectivity | 未（a8 §8 の 2） | A（Thm 7.14・aic エタールの名前）、A6-4、A7 |
| A8-3 Lemma 10.12 | a8-design §2.3・§3.4 | A8/Stratification | 未（a8 §8 の 5） | A（Mathlib：noetherian・極小素イデアル・分離閉包・エタール locus）、G-A8-4・5・7。独立した Codex の単位、置き場所は `CommutativeAlgebra/UniversalHomeomorphism/`・`EtaleStratification/`（2a の後） |
| A8-4 Thm 10.11・E3 の integral | a8-design §2.4・§3.3 | A8/IntegralDiscreteness | 未（a8 §8 の 3・4・6） | G-A8-6・8・9、A5・A7 |
| A9-1 界面の組み立て・E3 の消去 | a9-design | A9/Assembly | — | A4〜A8 の全欄。Inputs の書き換えは中身の段階 |
| A1-5 Thm 6.4 の多項式・mod p | a1-design §9 | A1/DeRhamComparisonPoly | 未（a1 §9.5） | E（黒箱を de Rham 形に、D68）、D（Lemma 4.20、A0-4）、A1-4 |

骨組みの規模：41 本、約 5,200 行（`sorry` 198、置き場の `True` 259）。コミットは 2ff4f3f09・48dd7ef31・e87797ee2・95c3ba18e・29c57f835・b70d99517・3d81d9f9d・37675c4b0 ほか（A6 まで）。

## 2. 要確認の分類

### (A) 基盤の名前を探すだけ（中身を書く段階の最初に。ビルドなしで grep で済む）

| 箇所 | 探すもの |
| --- | --- |
| Shared/CosimplicialCupProduct:80 | CommRingCat の余単体的対象 → ModuleCat の忘却（`forget₂`） |
| Sheaves/GlobalSections:84 | 関手 ∞ 圏 `(ihom K).obj E` の頂点 ↔ 射 `K ⟶ E`（Core の `functorVertex` の逆） |
| Sheaves/GlobalSections:115 | `IsReflectiveSubcategory` の中身から反射関手を取り出す形 |
| Sheaves/GlobalSections:138 | E の辺の可逆性の述語（`FunctorIso` か同値辺） |
| Sheaves/SheafCondition:98 | `uliftFunctor` と join の可換性（`JoinCone.ulift`。F2/Presentable の宇宙比較） |
| A0/PrismaticSite:230 | `uliftFunctor.obj (nerve (SmallModel C)) ⟶ nerve C`（ULift の圏の nerve との比較） |
| A0/PrismaticSite:249 | D(A) の `⊗^L A/d` |
| A0/PrismaticSite:260 | φ_A に沿うスカラー制限 D(A) → D(A) |
| A0/PrismaticEnvelope:52 | Koszul 複体のホモロジー（HA/Koszul*） |
| A0/PrismaticEnvelope:156 | 完備テンソル（BS/Perfectoidization/CompletedTensor、HA/DerivedCompletion/CompletedBaseChange*） |
| A0/CechAlexander:88、Shared/DeRhamPolynomial:125 | 一変数の導来 p 完備化 H⁰（E3 の `completionRing`） |
| A1/HodgeTateComparison:106 | Frobenius に沿う `Module.Flat` の述べ方 |

### (B) BS 側で決める設計の細部（決定：2026-11-02）

| 箇所 | 決定 |
| --- | --- |
| R の具体形（A0/CechAlexander:114・197、A1/HodgeTateMap:39） | R := `MvPolynomial (Fin r) (A ⧸ P.ideal)` の一変数 p 進完備化の H⁰（E3 の `completionRing` と同じ道具）。A0 の `cechAlexanderAffine` と A1 の `affineAlgebra` を同じ定義にする。一般の集合 T 上も同じ |
| `cechKernel`（A0/CechAlexander:88）と閉包（A0/PrismaticEnvelope:98） | J := ker(B → H⁰ の一変数導来 p 完備化 (B ⧸ J₀B))。`of_closure` はこの核と J₀B の envelope が一致すること |
| `regularShortExact` の係数環（Shared/CosimplicialBockstein:82） | 係数は基底 A（A 加群として）。R 線形性は別に付ける |
| η^1 の線形性（Shared/DeRhamPolynomial:110） | H^0 の P 加群構造を η^0 で入れ、η^1 は P 線形写像 Ω^1 → H^1（H^1 は H^0 加群）として述べる |
| `cohomology` の関手性（Shared/CosimplicialCupProduct:121） | 余単体的環の射 f : X ⟶ Y に対し `cohomologyMap f i : cohomology X i → cohomology Y i`（環の射、cup 積を保つ） |
| `cechShape` と `structurePresheafDerived` の型合わせ（A0/CechAlexander:160〜175） | `cechNerveData` を `PrismOverSmall` の側で作り（`equivSmallModel` で移送）、S3 を `PrismaticSite` 上の前層 `structurePresheafDerived` に適用する |
| κ 不変性の形（A0/PrismaticSite:272） | κ₀ ≤ κ ≤ κ′ の site の包含関手 ι と、ι に沿う前層の制限で `derivedGlobalSections` を比較する同型（頂点の等号は主張しない） |

### (C) ∞ 側の窓に依存（infinity-sheaves-design §4・§9。W2b の後、担当未定）

G3（D(A) presentable）、G4（Fun の presentable 性）、G6（局所置換の存在）、G8（X ⊗ M と Yoneda）、G9（Čech 脈体の実現または Bousfield–Kan）、
G10（Tot ＝ 全複体）、`isSheaf_toGrothendieck_iff`（生成系で十分）、`JoinCone.ulift`（宇宙）、S5・S7。BS 側は骨組みのまま待つ。

### (D) 論文の層の区切り 2b の後（HA/DerivedCompletion を読んでから）

A0-3b（Lemma 3.7(2) 一般形・(3)）、A0-3d（Cor 3.12 (a)〜(e)。有限段の Amitsur は新規）、A0-4（Tor 振幅・Lemma 4.22・4.20）、
G-A1-4（導来 Nakayama）、G-A1-5（完全忠実平坦の保存性）、G-A1-13（底変換の合成）。改名表は調整役から。

### (E) 結晶側の黒箱と arc 降下の引用（独立の作業単位。いつでも書ける）

A1-2（D^•、η、Lemma 2.36 の変数の場合）、A1-3（Lemma 5.4、pd 包の Čech 脈体 ≃ de Rham 複体、Cartier、Cor 5.5）。
結論は `hodgeTate_iso_polynomial_Zp` 一つ。BS と独立な部分（余単体的ホモトピー、pd-Poincaré、Cartier）は `drafts/Shared/` に。

## 3. 決定の所在

| 番号 | 内容 | 正本 |
| --- | --- | --- |
| U1・U3・U4 | Type u と κ、向き付き有界基底、完備化は導来完備化の H⁰ | infinity-sheaves-design §0・§5、ノート D5・D16 |
| β（U2） | RΓ は層化と Γ（γ 案は不採用） | infinity-sheaves-design §0 |
| D-S1 | Čech 層（hypersheaf との差は離散な層で消える） | infinity-sheaves-design §2・§2.1、ノート D17 |
| D-S2〜D-S5 | κ、D(A) 値→CAlg 値、左完全性は安定性で、1 圏の位相データ | infinity-sheaves-design §6 |
| D19〜D24 | 向き付き、Def 2.42 の離散化、Prop 3.13 の範囲、生成位相、Čech 余脈体は添字で、Lemma 4.21 不要 | a0-design §4・§6 |
| Tot 非正規化、Čech (b)、HA は 2b の後 | | a0-design §6 |
| D25〜D30 | Thm 5.2 β、微分形式、模型の環構造、捻りなし、一般の r、E を作らない | a1-design §5・§7 |
| 順序 | A1-1 → A1-4 → A1-2 → A1-3、結晶は最小限 | a1-design §6 |
| D31〜D35 | P_Σ、完備化不変性、gr が (∧^i L)^∧ の定義、Poly の添字、CAlg_A 値 | a2-design §4・§6 |
| D36〜D40 | Lemma 7.7(1) は特別な場合だけ、Δ^init 不要、BR30 閉じる、qrsp は余接複体で、Prop 7.10 の範囲 | a3-design §4・§7 |
| D41〜D44 | Def 8.2 は p 完備な S に、perfd の欄は (S^∧)_perfd、φ_A^{n*}、Lemma 8.4 は内部で要る、P⁰ は BS が骨組み | a4-design §4・§6 |
| D45 改訂、D68・D69 | Prop 8.5 は導来 p 完備な animated S（site は π_0 S）で系 4 を述べる（決定 6、11-02）；結晶の黒箱は仕様つきの de Rham 形一つ＋G-A1-17；Thm 6.4 の帰着は A_0 上で原典の経路 | a5-design §5・§7.1、a1-design §9.3・§9.4 |
| D45〜D52 | S は導来 p 完備な animated（D45 改訂、系 4 を含む）、位相の順序、κ と Type u の一致（余積は Perfd_{S/} の (T₁ ⊗̂_S T₂)_perfd を Lemma 4.8 で移す、W9-II-06）、D48 取り下げ（G-A5-17 = G-A2-10）、descendable は Mat16 の定義、de Rham 入力は A1-5、S̃ は ω 段、Cor 7.3 との一致 | a5-design §5・§7 |
| D63〜D67 | Thm 10.9 は連結性だけ原典 (1)(2) で、n = 1 は Perfd_{S/} = Perfd_{S_red/}、Lemma 10.12 は原典の形、Prop 10.4 は必要な同値、E3 は S^∧ 経由 | a8-design §5・§7 |
| D68〜D69 | 結晶の黒箱は de Rham 形一つ、Thm 6.4 の帰着は Prop 6.2 の経路 | a1-design §9.3・§9.4 |
| D60〜D62、D15 | Def 8.2 の定義域を原典（animated）に戻す、基底 R 固定、Cor 8.14 は離散 S、環版 Prop 8.13 は後で系に（BR31） | a7-design §4・§6 |
| D20 訂正 | Def 2.42 の平坦性はホモロジーの底変換同型（高次の消滅ではない。Codex W9-I-01 の反例 (Z_p,(p))） | a0-design §2.5・§4 |
| D53〜D59 | arc site は affine（affCompl_κ ⊃ affPerfd_κ）、有限族、Cor 8.11 は affine 版を記録、三つの引用は別々に `sorry`、S8、S′ × S/I は有限積の保存で戻す、BM18 は affine 版 | a6-design §5・§7・§9・§10 |

## 3.1 調整役からの返答（2026-11-02、main 26f1f4d94）

- Shared 3 本の置き場所：cup 積・Bockstein は `HomologicalAlgebra/Cosimplicial/`、de Rham は `CommutativeAlgebra/DeRham/`（新設、HA の第一層＝一般論）。
  移すのは 2b の後。名前は論文の層に予約してもらう。それまで drafts/Shared/ のまま。
- 2b の改名表は `BhattScholze/` に加えて `HomologicalAlgebra/DerivedCompletion/` の分も回る（(D) の読解に使う）。
- Sheaves の骨組みで使っている基盤の名前は実在を確認済み（nerve・ihom は Mathlib）。形の確認は W2b 後の窓の判断のとき。F1B・F2 の改名は
  W2b・W2c の改名表で回る。
- A2 の設計（P_Σ・左 Kan 延長・CAlg_R の API を読む）は進めてよい。読むだけでビルドなし。
- （main 600e578d7、M13）DerivedGeneral 2 本の置き場所は `InfinityCategories/Derived/`（一般の t 構造の定義を切り出すなら Stable/）。時期は段 G、
  W2b の後。CompletionFunctor は 2b の改名表を受けてから。それまで drafts/DerivedGeneral/ のまま。
- （main 431c40741、M14）G-A4-1（P⁰）の置き場所は `EInfinity/PowerOperation/`（新設、BarrattEccles・Operad の隣。Barratt–Eccles の作用の型はそこで確認）。
  時期は A4 の中身を書く段階まで不要、担当（E2 レーンか BS か）はそのとき決める。BS 固有の骨組みは Perfectoidization/Derived/ の隣の仮置きでよい。
- （main 86acd98db、M15）G-A5-1（descendability）の置き場所は `EInfinity/Descendable/`（新設。CAlg と D(A) の両方を使う。EInfinity は Derived を import 済み）。
  E∞ を使わない thick ⊗-ideal・index・安定性の部分は Derived/ へ下ろしてよい。時期・担当は M14 と同じ（段 G、A5 の中身を書く段階で決める）。
- （main 7b8b96286、M12e）S8 の置き場所：(1)(5)(6) は `Sheaves/SpaceValued/`、(2)(3) は `Sheaves/Discrete/`、(4) の一般部分（HTT 5.1.5.6、el(F) 上の極限）は
  M12b と同じ `F2/`。前提に G13（𝒮 の presentable 性）と S4 の非安定版を追加。時期・担当は M12 と同じ。
- （同）Prop 8.10 の引用 3 件の `sorry` 定理は drafts/ の間は問題なし。`SerrePositivity/` に入れるときに `scripts/make_area_audits.py` の許可一覧の更新が要る
  （そのとき調整役に知らせる）。
- （11-02）論文の層の **2a**（CA の perfectoid 部分を BS へ、CLMST の整理、Perfectoidization* 12 本の Perfectoid/ への統合）が 11-05 の全ビルドに向けて開始。
  **2a の取り込みまで BhattScholze/・CLMST/ の Lean には手を入れない**（drafts/ はそのまま）。取り込み後に改名表（BhattScholze/・CLMST/・prop247_ の宣言名）が回る。
  **2b**（HA/DerivedCompletion）は 11-06 の見込みで、その改名表も回る。Codex レビュー W9 は読むだけなので影響なし。
- （main 26f9f7fc5）Lemma 10.12（A8-3）の置き場所は `CommutativeAlgebra/UniversalHomeomorphism/`（普遍同相の一般論）と `CommutativeAlgebra/EtaleStratification/`
  （層別の本体）。どちらも 2a の後に新規ファイルだけで入れ、論文の層へ名前を予約。独立した Codex の単位、担当は 2a の後。A8-1・A8-2・A8-4 の仮置きも問題なし。

## 4. 次の作業（提案）

1. A1-5 の決定（a1-design §9.4）の反映。その後は中身の段階へ：調整役と暦（W2b・2b の後）、(A) の名前探し、A1-2/A1-3 の黒箱の骨組み。
2. （済）A6（excision の欄）、A7（universal の欄）、A8（integral の欄）、A9（界面の組み立て）の設計書と骨組みは 11-02 に完了。
3. (E) の骨組み（A1-2・A1-3）。
4. (A) は中身を書く段階の最初に、(C)・(D) は時期を待つ。G-A4-1（P⁰）は `EInfinity/PowerOperation/`（M14）、担当は A4 の中身の段階で。

## 5. Codex レビュー W9 の指摘と扱い（2026-11-02）

正本：`review-codex-w9.md`。指示書：`bhatt-scholze-codex-w9.md`。

| 指摘 | 重さ | 扱い |
| --- | --- | --- |
| W9-I-01 D20 の「高次の消滅」は偽（基底 (Z_p,(p)) の H₁ = F_p） | 致命 | **訂正済み**（a0-design §2.5・§4、drafts/A0/PrismaticEnvelope の `IsCompletelyRegularRel`）：HA 7.2.2.10 の平坦性（H₀ 平坦＋全次数の底変換同型）。変数の場合は満たす。下流は不変 |
| W9-I-02 `cechShape` の始域 | 要修正 | 訂正済み（持ち上げた N(Δ)） |
| W9-I-03 `derivedGlobalSections_of_le` の頂点の等号 | 要修正 | 訂正済み（可逆な辺で） |
| W9-I-04 S3 の宇宙（E3 の添字圏は大きい） | 要修正 | 記録（infinity-sheaves-design §12、骨組みに注記）。中身の段階で大きい添字圏の版を足す |
| W9-I-05 CAlg 値の層化と U の両立 | 要確認 | `forget_sheafify` を別の主張として置いた。S4 の非安定版（M12e の前提）の一部 |
| W9-I-06 `True` の置き場・A 代数構造 | 要修正 | `ringPresheafToCAlg` の入力を A 代数値関手に。`of_closure`・`prismaticEnvelope_baseChange_of_variables` は主張を文で追記。残りの `True` は中身の段階で型にする（drafts/README の規約） |
| W9-I-07 Γ の説明 | 軽微 | 訂正済み |
| W9-I-08 ノート・状態表の不整合 | 要修正 | 訂正済み（05 の Thm 6.4 行、index と 07 の BR30、本表 §4 の 2） |
| W9-I-09 変数変換後の対の等式に閉包が落ちている | 要修正 | 訂正済み（a0-design §5.1 の 2：(d, Z)^−、`of_closure` で結ぶ、A/d = 0 は別扱い） |
| W9-I-10 `flatTopology` の篩の置き場（op X）、refine の被覆先 | 要修正 | 訂正済み（drafts/A0/PrismaticSite） |
| W9-I-11 κ の許容条件（κ^{ℵ₀} = κ） | 要確認 | `IsAdmissibleCutoff` を追加し `flatTopology_refine` の仮定に（drafts/A0/PrismaticSite）。a0-design §2.7 は中身の段階で追従 |
| W9-I-12 `HasEnvelopes` に濃度の条件がない | 要確認 | `HasEnvelopes` に濃度 ≤ cutoff を追加（多項式 R では模型との一意同型で供給） |
| W9-I-13 PD Čech 脈体 D_0^• 自体を切断つきとする行の証明は誤り（H¹(D_0^•/p) ≠ 0） | 致命 | **訂正済み**（a1-design §3 の 6：j ≥ 1 の行 Ω^j_{D_0^•} の収縮 G-A1-14（Bhatt–de Jong Lemma 2.15–2.17）、j = 0 の行は収縮しない。retraction による (ii) の比較も撤回） |
| W9-I-14 pd 微分の明示 | 要修正 | 訂正済み（G-A1-7 を pd 微分加群・pd de Rham 複体に） |
| W9-I-15 D69：保存性だけでは比較射が作れない | 要確認 | **訂正済み**（a1-design §9.1・§9.3：原典 Thm 6.4 の ψ・W(A_0/d_0) の経路を A_0 上で行い（p ねじれなしは A_0 で成立）、完全 prism へ底変換。D69 の決定は差し替えた案で再提示） |
| W9-I-16 Lemma 5.4 の無限変数 | 要修正 | G-A1-15（filtered 余極限）を追加 |
| W9-I-17 a1-design 前半の Thm 6.4「不要」 | 軽微 | 訂正済み（§0・§6） |
| W9-I-18 δ 座標つき D^• に列の Poincaré 議論を直接当てられない（t^p が H⁰ に残る） | 致命 | **訂正済み**（a1-design §3 の 6 (ii)：追加座標の Čech 因子 E^• = Q^{⊗(•+1)} の収縮で D_0^• → D^• が擬同型、G-A1-16） |
| W9-I-19 J つきの比較は Z_p の黒箱と Lemma 4.20 だけでは出ない | 要確認 | 反映済み（G-A1-17 を A1-3 の独立補題に。黒箱は Z_p のまま一つ） |
| W9-I-20 D69 の最後の W → A_0/d_0 の底変換 | 要修正 | 訂正済み（a1-design §9.1 の 2 に係数の列を明記） |
| W9-I-21 Bockstein の β² = 0 の説明、π∘ι = 0、係数環 | 要修正 | 訂正済み（drafts/Shared/CosimplicialBockstein） |
| W9-I-22 de Rham の d は P^∧ 線形でない | 要修正 | 訂正済み（drafts/Shared/DeRhamPolynomial） |
| W9-I-23 `hodgeTate_iso`・`prismaticCohomology_baseChange'` の二重宣言 | 要修正 | 訂正済み（HodgeTateMap 側を述語に） |
| W9-I-24 CAlg の錐の指定（正規化模型、AW との比較） | 要確認 | 反映済み（drafts/Shared/CosimplicialEInfinity の方針） |
| W9-I-25 r = 1 → Lemma 4.10 → 一般 r の順序 | 要確認 | 反映済み（a1-design §3 の 2、HodgeTateComparison の方針） |
| W9-I-26 HT filtration・導来外冪を D(A) で Kan 延長すると完備性が失われる（Fil_0 ≠ R^∧） | 致命 | **訂正済み**（a2-design §2.3・D33：D(k)_{p-comp} 内の延長 LΛ_p ∘ Lan、exhaustive は完備圏で、G-A2-9；drafts/A2/HodgeTateFiltration） |
| W9-I-27 φ_{A*} は CAlg_A の全余極限を保たない | 要修正 | 訂正済み（sifted に。a2-design §2.2、DerivedPrismaticCohomology） |
| W9-I-28 切り捨ては dg 関手にならない；connective の名前が原典と逆 | 要修正 | 訂正済み（Truncation：相対圏の局所化または t 構造の随伴；`IsConnectiveAt` = D^{≤n}、`IsCoconnectiveAt` = D^{≥n} に入れ替え、A4 の参照も） |
| W9-I-29 animated 完備化と `completionRing` = H⁰ の区別 | 要確認 | 反映済み（a2-design §2.4・D32、BaseChangeAndTensor）。E3 との接続は perfd の段で Prop 8.5 系 4 が要る → **a5-design §7.1 の決定項目 6（Prop 8.5 を animated S で、D45 改訂）** |
| W9-I-30 E3 の `unit` は CAlg の関手射 | 要確認 | 反映済み（Fil_0 → Δ̄ を CAlg で：`hodgeTateUnitCAlg`、a2-design §2.3） |
| W9-I-31 `Poly` の k パラメータ | 要修正 | 訂正済み（AnimatedAlgebra） |
| W9-I-32 qrsp の定義に有界 p 冪ねじれがない（S = ∏ O_C/(p^n) が反例） | 致命 | **訂正済み**（a3-design §1・§2.3・D39、`IsQuasiregularSemiperfectoid.boundedTorsion`） |
| W9-I-33 Lemma 7.7 の仮定は Δ̄ の離散性；有界性は自動でない | 要修正 | 訂正済み（a3-design §2.1、`IsDiscreteHodgeTate` → `IsDiscretePrismatic`、`discretePrism` の `hbdd`） |
| W9-I-34 源の p ねじれなしでは δ 射が出ない；φ mod p は独立補題に | 要修正 | 反映済み（δ 射は p ねじれなしの標的に限定、G-A3-9 追加）。**D36 の射の範囲は (a) で決定（11-02）** |
| W9-I-35 Δ_{T/A} ≃ Δ_{T/A′} は A2 (4) ではない | 要修正 | 訂正済み（G-A5-17 を G-A2-10 として A2 の隣に前倒し、A3 §2.3・`regularSemiperfectoid_prismatic`） |
| W9-I-36 HT の多項式入口の値の圏、一般の k の余接複体 | 要修正 | 訂正済み（`hodgeTatePoly` を D(k) 値に、`cotangentWedgeGeneral` の注記） |
| W9-I-37 一般への帰着の順序（B の離散性を先に） | 要確認 | 反映済み（a3-design §2.2：B_univ ⊗̂ A の離散性を導来 Nakayama で、紙 7） |
| W9-I-38 無限 filtration の離散性の説明、gr¹ の shift、G-A2-5 | 要修正 | 訂正済み（a3-design §2.2：有界ねじれによる議論、gr¹ は次数 0、J と J̄ の区別；a2-design G-A2-5 は sifted） |
| W9-I-39 「B_univ は A_univ 上完全平坦」は偽（f = dY で f の乗法が零） | 致命 | **訂正済み**（a3-design §2.2 を原典 Ex 7.9 の順序に：B := E ⊗̂^L_U A（CAlg）を普遍の比較の底変換で Δ_{R/A} と同一視し、HT の離散性から B 離散・Tor 独立、δ 環の押し出しの普遍性で envelope と全 prism の中の始性。G-A3-10、骨組み `lciDerivedEnvelope*`） |
| W9-I-40 p ねじれなしへ制限後も全 prism の始性が結論に残る | 要修正 | 訂正済み（`exists_initial_of_discrete` は部分圏での始性。Ex 7.9・Prop 7.10 の全 prism の始性は envelope の普遍性から。A5 で要る Lemma 7.7(3) の δ 射は完全 prism への脚だけ） |
| W9-I-41 完備化後の離散性を Tor 独立と言い換えない | 要修正 | 訂正済み（a3-design §2.2 (iii)：H⁰ 比較 `derivedComplexCompletion_h0_map_isIso` で B ≃ H⁰ LΛ_I(E ⊗_U A)） |
| W9-I-42 非完全 δ 環の押し出しに `PerfectDeltaTensor` は使えない | 要修正 | 訂正済み（G-A3-10 (a)：W₂ への切断で通常の δ 押し出し、`existsUnique_deltaPDCompletionHom`） |
| W9-I-43 一般 qrsp の始性と T・S′ の始性を区別 | 要修正 | 訂正済み（公開する始性は T・S′ に絞る。`qrsp_initial` は別単位・E3 不要と注記） |
| W9-I-44 既存 Cor 7.3 入口へ渡すデータ | 要修正 | 訂正済み（a3-design §2.3：A′ = A_inf(R′)、r : A′ → S′、非単元・零環の分岐、`existsUnique_deltaPerfectionPDCompletionHom`。G-A3-8′） |
| W9-I-45 G-A3-9 は φ と E∞ 演算の比較を含む | 要確認 | 反映済み（G-A3-9 の仕様に追加。段 II で A4 の P⁰ と同時に検証） |
| W9-I-46 ノートの表記の同期 | 軽微 | ノート第 7 章（Lemma 7.7 の入口は Δ̄、Prop 7.10 の射は Δ̄ へ、RootEnvelope は完全化後の比較）を更新 |
| **段 I の総括（W9 続き 6）** | — | 新たな致命なし。段 II（A4〜A7）へ進む。残る要修正・要確認は上表のとおり反映済み（G-A3-9 の比較は段 II で） |
| **段 II 開始（W9 第 2 部）** | — | A4 の途中で停止、以下を反映 |
| W9-II-01 D42：φ_* と φ^* の同一視で塔の遷移射が型をもたない | 致命 | **訂正済み**（a4-design §2.1・D42・G-A4-3、`frobeniusTower`：原典どおり φ_{A*}^n の塔。D42 撤回） |
| W9-II-02 P⁰ と levelwise Frobenius の比較を p 重 cup 積で説明できない | 要修正 | 訂正済み（coherent な自然変換（Lurie の強さ）と Tot・実現への移送。a4-design §2.2 (a)・G-A4-1、EInfinityPowerOperation） |
| W9-II-03 D41 の説明が D32 だけ | 要修正 | 訂正済み（二段：animated D32 ＋ Prop 8.5 系 4） |
| W9-II-04 H⁰(Δ_perf) に A3 の離散 Δ 用定理を直接当てられない | 要修正 | 訂正済み（C/p ↪ H⁰(X/p) の単射、一般の Rem 2.2 = G-A4-8/G-A3-6、prism 性を直接組み立て） |
| W9-II-05 単位名とノートの coconnective 欄 | 軽微 | 訂正済み（InterfaceFields、ノート第 8 章） |
| W9-II-06 完全 site の余積を B ⊗̂_A B′ とすると S 構造射の一致が失われる（S = F_p[t] の反例） | 致命 | **訂正済み**（a5-design §2.1：Perfd_{S/} の余積 (T₁ ⊗̂_S T₂)_perfd（Cor 7.3 の普遍性）を Lemma 4.8 の圏同値で完全 site へ。flat 被覆の相対 Čech 項（G-A5-5）とは区別。`perfectSite_cechNerveData`） |
| W9-II-07 比較写像の脚に旧記法 φ_A^{n*} が残る | 要修正 | 訂正済み（f_n = φ_B^{-n} ∘ f : Res_φ^n Δ_S → B。a5-design §2.2、`perfectionLeg`） |
| W9-II-08 D45 改訂と旧「離散のみ・系 4 なし」の併存 | 要修正 | 訂正済み（a5-design 冒頭・§0・§1・§6、骨組みの概要・規約、本表の D45〜D52 行） |
| （決定 11-02）D36 の射の範囲 (a) | — | 記録済み（a3-design §7.1）。Lemma 7.7(3) の δ 射は p ねじれなしの標的、始性はその部分圏；Ex 7.9・Prop 7.10 の全 prism の始性は envelope の普遍性から |
| （決定 11-02）D68 (a)・D69 (a)・決定 6 (a) | — | 記録済み。A5 の骨組みの定義域（`S : Type u` → `CompleteAnimatedAlgebra`）の書き換えは中身の段階で。animated 版の主張 `perfectionComparison_isIso_animated`・系 4 `perfectoidization_piZero` を A5-1 に追加 |

既存の作業ツリーの差分（`exposition/ja/infinity*` ほか 43 件）は他セッションのもので、BS のレビューの受入条件は「新たな差分が報告ファイルだけ」と読む。

