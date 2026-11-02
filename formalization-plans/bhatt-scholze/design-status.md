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
| A2-3 HT filtration・cotangentWedge | a2-design §2.3 | 未 | 未（a2 §7 の 2） | C（G-A2-2） |
| G-A2-2 D(A) の t 構造・切り捨て | a2-design §3 | DerivedGeneral/Truncation | — | C（置き場所は調整役、BS が骨組み） |
| G-A2-3 (p,d) 完備化の ∞ 関手 | a2-design §3 | DerivedGeneral/CompletionFunctor | — | C・D（HA の名前は 2b 後） |
| A2-4 完備化不変性・(4)・(5) | a2-design §2.4 | 未 | 未（a2 §7 の 3・4） | C・D |
| A3〜A9 | 未 | 未 | — | — |

骨組みの規模：11 本、約 1,700 行（`sorry` 85、置き場の `True` 38）。コミットは 2ff4f3f09・48dd7ef31・e87797ee2・95c3ba18e。

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

### (E) 結晶側の黒箱（独立の作業単位。いつでも書ける）

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

## 3.1 調整役からの返答（2026-11-02、main 26f1f4d94）

- Shared 3 本の置き場所：cup 積・Bockstein は `HomologicalAlgebra/Cosimplicial/`、de Rham は `CommutativeAlgebra/DeRham/`（新設、HA の第一層＝一般論）。
  移すのは 2b の後。名前は論文の層に予約してもらう。それまで drafts/Shared/ のまま。
- 2b の改名表は `BhattScholze/` に加えて `HomologicalAlgebra/DerivedCompletion/` の分も回る（(D) の読解に使う）。
- Sheaves の骨組みで使っている基盤の名前は実在を確認済み（nerve・ihom は Mathlib）。形の確認は W2b 後の窓の判断のとき。F1B・F2 の改名は
  W2b・W2c の改名表で回る。
- A2 の設計（P_Σ・左 Kan 延長・CAlg_R の API を読む）は進めてよい。読むだけでビルドなし。
- （main 600e578d7、M13）DerivedGeneral 2 本の置き場所は `InfinityCategories/Derived/`（一般の t 構造の定義を切り出すなら Stable/）。時期は段 G、
  W2b の後。CompletionFunctor は 2b の改名表を受けてから。それまで drafts/DerivedGeneral/ のまま。

## 4. 次の作業（提案）

1. A2 の設計書（Construction 7.6：多項式代数からの左 Kan 延長、HT filtration、底変換 (4)、余極限 (5)、CAlg 値の Δ（G-A1-11））。
   ∞ 側の P_Σ・左 Kan 延長・CAlg_R の API の確認から。
2. (B) の決定を骨組みへ反映（短い。A2 の設計の後でも可）。
3. (E) の骨組み（A1-2・A1-3）。
4. (A) は中身を書く段階の最初に、(C)・(D) は時期を待つ。
