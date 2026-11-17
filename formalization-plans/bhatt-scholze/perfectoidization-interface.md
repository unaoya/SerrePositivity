# Perfectoid 化の界面：原典照合と E3 / E2a の型草案（Π1）

2026-10-18。状態：Π1 の原典照合と Π2 の界面・導出の公開型。
Π2-8・Π3 完了（G1 達成）。perfectoid 側に残す文献入力は
`BhattScholze.Inputs.exists_perfectoidizationInterfaceE3` の一件。
旧二入口は公開名・型を保って界面からの証明に置換し、CLMST の利用箇所は変更していない。
主定理の未証明依存は、この入力と `Section4.supportedRankK0_descent`・`theorem_3_1_K0` の三件。
界面の具体的構成・降下の証明と E2 の表示比較は別工程として残る。
正本の計画は [infinity-categories.md](../archive/stage-i/infinity-lanes/infinity-categories.md) §0・§6、
[derived-infinity-category.md](../archive/stage-i/infinity-lanes/derived-infinity-category.md) §0、
モデルの工程は [e-infinity-algebras.md](../archive/stage-i/infinity-lanes/e-infinity-algebras.md)。
§4・§5 のコードは **型の草案**。既存宣言と設計用の略記を区別する。
§7 末尾は実装した公開宣言の名前と型である。

## 1. 原文（著者版の印刷ページ = PDF の1始まりページ）

出典は [BS 著者版](../../paper/refs/BS-prisms-author.pdf)
（[公開元](https://people.mpim-bonn.mpg.de/scholze/prisms.pdf)）。arXiv 版の番号に置き換えない。
とくに指定された「Thm 8.10」は、この版では **Proposition 8.10**。

| 番号・頁 | 原文の文言・式（抜粋） | 界面での役割 |
| --- | --- | --- |
| Thm 1.17(1), p.9 | “Let R be a perfectoid ring and let S be an integral R-algebra.” / “There is a perfectoid ring S_perfd with a map S → S_perfd such that any map from S to a perfectoid ring factors uniquely over S_perfd.” | 非完備を含む任意の整代数。有限・有限表示への制限なし |
| Def 8.2(1), p.63 | “Fix a derived p-complete simplicial R-algebra S.” / `Δ_{S/A,perf} := (colim(Δ_{S/A} → φ*Δ_{S/A} → φ²*Δ_{S/A} → …))^∧ ∈ D(A)` | 完備化は導来 `(p,I)` 完備化 |
| Def 8.2(2), p.63 | `S_perfd := Δ_{S/A,perf} ⊗ᴸ_A A/I ∈ D(R)` / “This is a p-complete E∞-S-algebra.” | perfd、単位、乗法と完備性の供給元 |
| Lemma 8.4, pp.63–64 | “For any derived p-complete simplicial R-algebra S, both Δ_{S/A,perf} and S_perfd lie in D≥0.” | cochain 規約で `Hⁱ = 0 (i < 0)` |
| Prop 8.5, pp.64–65 | “For any choice of topology … between the flat and the chaotic topology” 比較は同値。`S_perfd ≃ RΓ((S/A)^perf_Δ, Ō_Δ) ≃ lim_{S→R′} R′` は “the derived limit of R′ over all maps from S to perfectoid rings R′” | 極限形。任意の S に対する反射随伴の主張ではない |
| Prop 8.10, pp.67–68 | “The presheaf O on Perfd is a sheaf” / affine `X = Spf R` では `Hⁱ_arc(X,O) = 0 (i > 0)`。さらに “For any p-adic formal scheme T, the functor X ↦ Hom(X,T) is an arc-sheaf on Perfd.” | arc 降下の根拠 |
| Cor 8.11, pp.68–69 | “For any p-complete ring S, one has S_perfd = RΓ_arc(Spf S,O).” | Prop 8.10 と excision の間の段階 |
| Cor 8.12, p.69 | “Let S → S′ be a map of derived p-complete rings” と “some derived p-complete ideal I ⊂ S”。階数1の p-complete valuation ring `V` への `S → V` が `I` を消さなければ “there is a unique extension to a map S′ → V”。結論は下記の四角形が “a pullback square of E∞-S-algebras (in particular, in the derived category of S-modules).” | 完備な通常の環、通常のイデアルによる excision |
| Prop 8.13, pp.69–70 | “The functor S ↦ S_perfd … is symmetric monoidal” / `S₁,perfd ⊗̂ᴸ_{S₃,perfd} S₂,perfd → (S₁ ⊗̂ᴸ_{S₃} S₂)_perfd` is an equivalence | 導来完備テンソル。引き戻し保存の主張とは異なる |
| Cor 8.14, p.70 | “Assume that S_perfd is connective (or, equivalently by Lemma 8.4, concentrated in degree 0). Then S_perfd is a perfectoid ring, and S → S_perfd is the universal map from S to a perfectoid ring.” | **離散の場合**の perfectoid 性と普遍性の直接の出典 |
| Thm 10.11, p.82 | “Let R → S be the p-completion of an integral map.” / “Consequently, S_perfd is discrete and a perfectoid ring.” | integral 欄の離散性の直接の出典 |

完備化の規約は §1.2, p.10 の “These are taken in the derived sense unless otherwise specified.”
同頁は導来完備加群の核・余核・像・拡大による閉性、および通常の完備化との違いも明記する。

Cor 8.12 の四角形の順序を固定する：

```text
P(S) ───────→ P(T)
 │              │
 ↓              ↓
P(S/I) ─────→ P(T/IT),       IT = I.map f.toRingHom.
```

原文の `S′/I` は `T/IT`。通常の商であり、`T ⊗ᴸ_S S/I` への置換ではない。
脚注14は整写像が `V(I)` の外で同型なら付値環条件を満たすと述べる。
原文の証明末尾にある `F(S)=…×…F(S)` は右端が `F(S/I)` であるべき誤植と読めるが、
界面には証明中のその式を採らず、命題本文の四角形を採る。

## 2. 記号・対象範囲・制限した極限（改訂）

`p : ℕ`、`[Fact p.Prime]`、`[CommRing R]`、`hR : IsIntegralPerfectoid R p` を固定する。
BS の perfectoid とこの述語の同値（零環も含む）は一般の比較補題として必要。
`D := derivedInfinityCategory R`、`H i X` は D3 の同値から得るコホモロジー加群、
`Disc X := ∀ i : ℤ, i ≠ 0 → IsZero (H i X)`。`D≥0` と離散を混同しない。

`J(S)` は S の次数0複体を D の semifree 模型にしたもの。`J : nerve A_R ⟶ D` は
ホモトピー整合的な関手として構成する（環を semifree 複体と文字どおり同一視しない）。
`Nat∞(F,G)` は `nerve A_R ⊗ Δ[1] → D` で両端が F,G のデータ。
`edge F f`、`v F S` は関手の辺と頂点。以下の `H0RingData` 等は新設予定の補助型。

### 2.1 採用する limit 欄と Prop 8.5 の制限

`A_R` は **Type u のすべての通常の可換 R 代数**の1圏（設計上の略記）。
`PerfUnder_u(S)` は対象 `(T : Type u,hT,k : S →+* T)`、射 `l : T →+* T′` が `l.comp k = k′` を満たす圏。
T の R 作用は `R → S → T`。異なる R 作用を持つ標的もこの方法で扱う。
`F_S : nerve (PerfUnder_u S) → D` は `(T,k) ↦ J(T)`、射も同じ環準同型から作る。
添字は **この向き**であり opposite にしない。`(C,η)` が始対象なら `lim F_S ≃ J(C)`。
極限に関する用語は coinitial / initial（しばしば「始対象の cofinality」と呼ぶもの）。
`PerfUnder_u(S)` の対象は Type (u+1) だが、`derivedInfinityCategory R : SSet.{u+1}` なので
この nerve を始域に持つ錐と `IsLimitCone` は述べられる。対象宇宙と Hom 宇宙は別に記帳する。
二宇宙版 `initialCofinality` は `{I : Type v} [Category.{w} I]` と
`X : SSet.{max v w}` を取り、対象 Type (u+1)・Hom Type u のこの圏へ適用できる。
この用途では Hom の ULift も不要である。
これは加群の宇宙や D(R) の拡大とは区別する。任意のそのサイズの極限の存在も仮定しない。
**採用形**は `cone : JoinCone F_S`、`cone.vertex = v P S`（または指定同値）、`IsLimitCone cone`。

以下は原文 pp.64–65 の証明を Type u 内で読み直した確認であり、原文に宇宙添字があるという引用ではない。

1. まず導来 p 完備な離散 S を扱う。p.64 は各 x に対し
   `S_x = S⟨X,Y⟩/(x-X^p-pY)` を作り、“Repeating this transfinitely” により
   すべての perfectoid 標的への写像が延びる semiperfectoid `S → U` を作る。
   元全体での添字、有限変数多項式・商・p 完備化・必要な超限列は u-small に取れる。
   完備化が可算極限を使うため、単に可算回で十分とはせず、u 内の非可算正則長で反復する。
   これは Prop 7.2 の証明 (p.55) が使う完備化と ω₁-filtered colimit の交換と同じサイズ管理。
   各段階で全元に対する操作を行い、極限段階で p 完備化する。固定した標的 T への延長は
   各段階の根の選択から超限帰納で作る。u-small な可算積とこの長さの和・商の閉性を使う。
   Cor 7.3 (p.56) により `Q₀ := U_perfd` も Type u に構成でき、`Q₀ → T` は各 T に存在する。
   ここでの U は「全標的への写像を延長できる」cover であり、平坦性を追加で主張しない。
2. p.65 の Čech–Alexander 計算は `U_n := (U ⊗_S … ⊗_S U)^∧`（n+1因子）、
   `Q_n := (U_n)_perfd` の cosimplicial 環で計算するもの。各項は u-small、semiperfectoid 側の
   Cor 7.3 を使う。導来テンソルで作る場合も Prop 8.5 直前の π₀ 依存性で同じ通常の標的圏を得る。
   完備テンソルと Cor 7.3 の普遍性から、各 `(T,k) ∈ PerfUnder_u(S)` に自然に
   `Hom_S(Q_n,T) ≅ Hom_S(U_n,T) ≅ Hom_S(U,T)^(n+1) ≅ Hom_S(Q₀,T)^(n+1)`。
   これは Q_n がこの圏で Q₀ の n+1 個の coproduct であることも示す。
   U_n の mod p で Frobenius が全射なので semiperfectoid 性が保たれる。
   Hom の同定は n と T に自然で、coface は因子の挿入、codegeneracy は因子の乗法に対応する。
3. `q : Δ → PerfUnder_u(S), [n] ↦ Q_n` と置く。各 T について `L_T := Hom_S(Q₀,T)` は非空。
   comma 圏 `(q ↓ T)` は、単体集合 `[n] ↦ L_T^(n+1)` の単体の圏である。
   この単体集合は L_T 上の indiscrete groupoid の nerve。L_T の一点を選び前置する
   extra degeneracy により可縮。単体の圏にも `id → prepend ← const(選んだ0単体)` があり、nerve は可縮。
   よって [HTT Thm 4.1.3.1](https://www.math.ias.edu/~lurie/papers/HTT.pdf) の双対から q は coinitial。
   comma の射は `α : [n] → [m]` と `f_n = f_m ∘ q(α)` の組なので、使うのは
   `(q ↓ T)` であり `(T ↓ q)` ではない。環の圏と affine site の向きをここで区別する。
   **弱始対象 Q₀ の包含一点だけが coinitial だとは主張しない。**
4. したがって `lim_{PerfUnder_u(S)} F_S ≃ Tot_{[n]∈Δ} J(Q_n)`。
   原文の Čech 計算が右辺を S_perfd と同定する。右辺は u-small な可算図式の導来極限であり、
   積・fiber の複体模型で同じ宇宙に存在する。構造写像、錐、H⁰ の環準同型もこの比較で追う。
   原典の全標的版と制限版を比較したい場合も、同じ Q_• への二つの制限で比較できる。

以上により、**制限した limit 欄を採用できる**。小さい cover、各 Q_n の普遍性、comma 圏の
可縮性を明示することが根拠であり、「大きな極限を制限しても同じ」という無条件の一般原理ではない。
Π2 ではこの特定の錐の極限性を文献入力の欄として受け取り、任意の巨大極限を実装する必要はない。
将来このサイズ管理を再検討して宇宙拡大案に戻すなら、D と Alg_E の宇宙拡大の充満忠実性、
Hⁱ・単位・有限極限との整合、同じ Q_• の Tot の宇宙変更比較と u-small 模型への降下が必要になる。
具体的には拡大関手 `ι` について、この Čech 図式に対する
`ι(Tot J(Q_•)) ≃ Tot ι(J(Q_•))`、両宇宙の q の coinitiality、
`ι(J_u T) ≃ J_v T` の自然性から指定錐を降ろす。充満忠実性だけでは極限の比較は出ない。

### 2.2 非完備 S の拡張と `IsModuleComplete` の関係

`C_R ⊂ A_R` は `IsModuleComplete S (p : S) (ModuleCat.of S S)` を満たす充満部分圏。
`S^∧` は animated R 代数の導来 p 完備化、`U(S^∧) ≃ Λ_p(S[0])` とする。
底の Λ_p は `Rlim_n Kos(S[0];p^n)`。これは `S ⊗ᴸ_ℤ ℤ/p^n` の塔でも計算できるが、
p が S の零因子になり得るので `S ⊗ᴸ_S S/(p^n)` と同一視しない（BS p.10 脚注5）。
`S^∧` は connective（cochain `D≤0`）であり、一般には離散とは限らない。

出典は BS §1.2, pp.10–11 と [Stacks 091P](https://stacks.math.columbia.edu/tag/091P)
（局所化から全次数の Hom の消滅）、[091V](https://stacks.math.columbia.edu/tag/091V)
（完備化の左随伴性）、[0920](https://stacks.math.columbia.edu/tag/0920)
（Koszul 極限による表示）。cochain の上界保存は [0H83](https://stacks.math.columbia.edu/tag/0H83)
と単位の mod p 同値から、または塔の最上次の遷移全射性から示す。
**環の Map の比較は 091V の加群の Hom 全単射だけを引用して済ませない。**

Lean では `IsModuleComplete A a M := IsComplete A a (M[0])` で、後者は
`∀ n : ℤ, Hom(A[1/a][0],M[0][n]) = 0`。これは上の完備性と一致する。
`isModuleComplete_algebraMap_iff`（ScalarRestriction.lean）で S 上と R 上の p を比較できる。
既存 `IsIntegralPerfectoid.isModuleComplete` / `.isModuleComplete_algebra`
（CommutativeAlgebra/PerfectoidDerivedComplete.lean）が perfectoid T の完備性を供給する。
また既存 `derivedComplexCompletionFunctor`、`derivedComplexCompletionUnit`、
`derivedComplexCompletionHomEquiv`（ComplexCompletionReflection.lean）は
`Hom(Λ_p X,Y) ≃ Hom(X,Y)` を完備 Y に対して証明済み。ただしこれは加群のホモトピー圏の結果。

環の段階では `S^∧₀ := H⁰(Λ_p(S[0]))` に既存の完備化代数の環構造を入れる。
`derivedComplexCompletionFunctor_homology_isModuleComplete` で S^∧₀ は導来 p 完備、
`completionH0_existsUnique_algHom`（CompletionH0AlgebraUniversal.lean）を次数0の代数に適用すると
`(S^∧₀ →ₐ[R] T) ≃ (S →ₐ[R] T)` を、指定された完備化単位との前合成で得る。
これは乗法保存も証明した既存定理で、R 作用を各写像から入れれば環準同型版になる。
connective な animated 代数から離散 T への写像空間は離散で、π₀ が通常の環の Hom なので、
`Map(S^∧,T) ≃ disc Hom(H⁰S^∧,T) ≃ disc Hom(S,T) ≃ Map(S,T)`。
必要なのはこの **離散標的に対する**式であり、全非離散代数への反射性をここで追加しない。
E∞ 表示で述べる場合の離散切断の出典は HA Prop 7.1.3.15・7.1.3.18、animated 版も π₀ の随伴性。

この鎖では三つの段階を区別する。(i) 091V と全シフトへの適用は完備な**加群**への
写像空間の比較、(ii) `completionH0_existsUnique_algHom` は H⁰ での**環**の乗法を含む
一意延長、(iii) HA の connective な代数の 0 切断は、その環 Hom を離散標的への Map と
同定する一般定理である。perfectoid T は通常の離散環として使うので (ii)・(iii) で十分。
`S^∧` と既存の Koszul 完備化代数の底・乗法・単位の比較は E2 の一般比較補題として残す。

Lean に要求する具体的な補題は次のとおり（名称は役割の略記）：

| 補題 | 正確に必要な結論 | 担当・根拠 |
| --- | --- | --- |
| 完備性比較 | `IsModuleComplete S p T ↔ IsModuleComplete T p T`（`S →+* T` に沿う作用） | DerivedCompletion / ScalarRestriction、`map_natCast` |
| 環 Hom の延長 | 完備 T に対し `∃! g : S^∧₀ →+* T, g.comp η = f` | DerivedCompletion の上記代数定理と一変数完備化の比較 |
| 延長の自然性 | `ext(f ∘ a) = ext(f) ∘ completionMap(a)`、`ext(b ∘ f) = b ∘ ext(f)`（b の標的も完備） | Π/Completion。一意性から証明 |
| 完備始域の単位 | S が `IsModuleComplete` なら `η : S →+* S^∧₀` は環同型 | 加群完備化単位の同型と乗法保存 |
| 添字圏の比較 | 単位との前合成と一意延長が互いに逆、標的忘却関手と両立 | Π/Completion。標的 T の台は Type u のまま |
| 完備化 Map | connective な完備化の比較を経て `Map(S^∧,T) ≃ Map(S,T)`、前合成は単位で与える | E2。HA 7.1.3.15・18 と上記環 Hom 同値 |

§0 の元の始域からの拡張は `P(S) := P_C(S^∧₀)` とし、単位は `S → S^∧₀ → P_C(S^∧₀)`。
Prop 8.5 の π₀ 依存性によりこれは `(S^∧)_perfd` と同じである。
上の Hom 比較の標的・射についての自然性から `PerfUnder_u(S^∧₀) ≌ PerfUnder_u(S)`、
かつ F と指定錐の比較を得る。S が C_R にあれば完備化単位は同型で、元の界面へ戻る。
この方法なら E3 の Lean 実装に animated 代数全体の構築を要求せずに非完備 S を扱える。
残る一般補題は、次数0代数と既存完備化代数の包装、単位付き環 Hom 同値の自然性、
添字圏同値と錐の輸送、D3 での Λ_p・単位・H⁰ の比較。Map そのものの実装は E2a の担当。

## 3. 各欄の出典と導出鎖

| 欄 | 原典 → 一般定理 → 採用する主張 |
| --- | --- |
| perfd | Def 8.2 の関手的構成 → 底の導来加群へ忘却 → E3 の P。E2a では E∞ 代数のモデル表示比較を通して P_E を選ぶ。非完備 S は §2 の拡張 |
| unit | Def 8.2 の E∞-S 代数構造 → 構造写像 `S → S_perfd` と自然性。E3 は底の辺と H⁰ の環準同型をともに保持。Prop 8.5 の比較はこの単位と両立 |
| H⁰ の環構造 | E∞ 構造 → π₀ の可換環構造と射の乗法保存。E3 は `H0RingData` として明記。別証明は Prop 8.5 → `D≥0` 上の H⁰ の極限保存 → 通常の環の極限から環構造を移す。比較は各射・単位・極限の射影に自然 |
| coconnective | **2026-10-26 に削除**。Lemma 8.4 → `∀ i < 0, Hⁱ(P S)=0` はどの橋からも読まれず、`sorry` が必要より強い主張を仮定していたため、E3 と CAlg 版の両方から外した（bhatt-scholze-e3-coconnective.md） |
| universal（離散時） | Cor 8.14 → H⁰(P S) の perfectoid 性と一意因子分解。Cor 8.14 の証明は導来 Nakayama・Lemma 7.7・Lemma 2.34 と Prop 8.13 を使う。E2a の写像空間形には離散代数間の Map^h が離散な環準同型集合である一般比較を足す |
| limit | Prop 8.5 と §2.1 の u-small Čech・coinitiality の確認 → 制限した極限表示 → E∞ 代数の極限を底で計算する HA Cor 3.2.2.5 → E3 の `IsLimitCone`。E2a も `PerfUnder_u(S)` を使う。S 上の指定錐、単位、H⁰ の各射影の乗法整合性も保持 |
| integral | Thm 10.11（p 完備化した整写像）→ 離散かつ perfectoid。非完備整代数への拡張は §2.2。別の検算：Thm 1.17(1) の普遍環が `PerfUnder_u S` の始対象 → 制限した極限計算 → 同じ離散対象。界面から存在入力を導く際はこの検算を証明に逆流させない |
| excision | Prop 8.10 → Cor 8.11 → Cor 8.12 の E∞-S 代数の引き戻し → HA Cor 3.2.2.5 と R へのスカラー制限の極限保存 → E3 の D(R) の引き戻し。E2a はモデル表示比較 → Alg_E(R) の homotopy 引き戻し。右 Quillen な U が底の homotopy 引き戻しを保存 |

一般定理の確認先は [HA, 2017-09-18 版](https://www.math.ias.edu/~lurie/papers/HA.pdf)：
Cor 3.2.2.5 (p.359) は極限を評価で計算する定理、Prop 7.1.3.18 (p.1219) は離散代数の同定。
homotopy **limit** と ∞ 極限の比較は Prop **1.3.4.23** (p.119)。
計画書にある 1.3.4.24 は **colimit** の定理なので、この用途には使わない。
H⁰ の極限保存は cochain の `D≥0` 上で H⁰ が heart への右随伴であることから示す。
全 D(R) 上の H⁰ に対する無条件の極限保存は主張しない。

## 4. E3：CAlg_R を型に含めない草案

`H0RingData P` は次のデータ・等式を持つ補助構造とする：
通常の環の関手 `B : A_R ⥤ CommRingCat.{u}` と自然な R 代数構造、
加群として `B(S) ≅ H 0 (v P S)`、環準同型 `η₀(S) : S →+* B(S)`、
`H⁰(unit_S)` との一致と自然性。`H⁰(edge P f)` は B(f) の底の線形写像。
`BSLimitConeData` は `F_S : nerve (PerfUnder_u S) ⟶ derivedInfinityCategory R` 上の
`JoinCone F_S`、頂点と `v P S` の同定、
単位から S 上の錐になる条件、各 H⁰ 射影 `B(S) →+* T` とその積・単位・自然性を持つ。
底の極限だけに、無関係な環構造を添える型にはしない。

```lean
-- 以下の A_R, J, H, Nat∞, H0RingData, BSLimitConeData 等は設計上の略記。
structure PerfectoidizationInterfaceE3 (R : Type u) [CommRing R]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p) where
  perfd : nerve A_R ⟶ derivedInfinityCategory R
  unit : Nat∞ J perfd
  h0 : H0RingData perfd unit
  -- h0.B は通常の環の関手、h0.η₀ は指定された環準同型。
  coconnective : ∀ S (i : ℤ), i < 0 → IsZero (H i (v perfd S))
  universal : ∀ S, Disc (v perfd S) →
    IsPerfectoidization p (h0.η₀ S)
  limitCone : ∀ S, BSLimitConeData perfd unit h0 S
  limit_isLimit : ∀ S, IsLimitCone (limitCone S).cone
  integral : ∀ S, Algebra.IsIntegral R S →
    Disc (v perfd S) ∧ IsIntegralPerfectoid (h0.B.obj S) p
  excision : ∀ (S T : A_R) (f : S →ₐ[R] T) (I : Ideal S),
    IsModuleComplete S (p : S) (ModuleCat.of S S) →
    IsModuleComplete T (p : T) (ModuleCat.of T T) →
    IsModuleComplete S (p : S) (ModuleCat.of S I) →
    ArcOutside f I → IsPullbackSquare (perfdSquare perfd f I)
```

`perfdSquare` は上記の **通常の商の可換四角形**の nerve を perfd で写した
`Δ[1] ⊗ Δ[1] ⟶ derivedInfinityCategory R`。可換性を証明した四辺だけでなく、
その可換性を実現する2単体も固定する（D4 の fiber 比較で必要）。
`ArcOutside` は §6 の harc の量化をそのまま略記する。integral の perfectoid 性は
universal からも従うが、原文との照合用に明記した冗長な成分である。
perfd の導来 p 完備性は Def 8.2 から従い、limit と完備対象の極限閉性からも回収できる。
`IsModuleComplete` を一般の導来対象へ直接適用せず、D3 を通した `IsComplete` を使う。

E3 の universal は **環の射**の普遍性である。`Map_D(P S,J T) ≃ Map_D(J S,J T)`
という線形写像の主張に取り替えてはいけない。

## 5. E2a：Alg_E のモデル圏内の草案

`AlgE R` は unital な Σ-cofibrant E∞ オペラッド E の非有界 cochain R 代数の圏、
`U : AlgE R ⥤ Ch(R)` は転送モデル構造の右 Quillen な忘却関手。
`jE` は `E → Com` 経由の次数0代数の関手。`Maph` は frame による homotopy function complex。
`P_E : A_R ⥤ AlgE R` は関手的模型の選択。単位の型には関手的 cofibrant replacement `Q` を選び、
`jInput := jE ⋙ Q` と `jInput → jE` の弱同値を使って `unitE : jInput ⟶ P_E` を保持する。
図式の厳密化もモデル一般論の責務であり、必要なら coherent diagram から始める。
`HE i A` は複体 U(A) の i 次コホモロジー、`DiscE A := ∀ i ≠ 0, IsZero (HE i A)`。
`H0E` は E の演算から得る通常の可換環の関手。unitE・錐射の H⁰ は環準同型。
単位の H⁰ は `H⁰(jInput S) ≅ S` を通して `η₀ : S →+* H0E(P_E S)` と読む。

```lean
structure PerfectoidizationInterfaceE2a (R : Type u) [CommRing R]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p) where
  perfd : A_R ⥤ AlgE R
  unit : jInput ⟶ perfd
  h0 : H0RingComparison perfd unit  -- H0E と底の H⁰、η₀ の一致
  coconnective : ∀ S (i : ℤ), i < 0 → IsZero (HE i (perfd.obj S))
  discrete_perfectoid : ∀ S, DiscE (perfd.obj S) →
    IsIntegralPerfectoid (H0E (perfd.obj S)) p
  universal : ∀ S, DiscE (perfd.obj S) → ∀ (T : A_R),
    IsIntegralPerfectoid T p →
    WeakEquivalence (precompMaph (unit.app S) (jE.obj T))
  -- precompMaph : Map^h(perfd S,jE T) → Map^h(jInput S,jE T)
  -- 後者は jInput S → jE S により Map^h(jE S,jE T) と弱同値。
  limitCone : ∀ S, HomotopyCone (perfectoidTargetDiagram_u jE S)
  limit_vertex : ∀ S, WeakEquivalenceTo
    (perfd.obj S) ((limitCone S).vertex)
  limit_isLimit : ∀ S, IsHomotopyLimitCone (limitCone S)
  limit_unit : ∀ S, ConeOverSourceCompatibility
    (limitCone S) (limit_vertex S) (unit.app S)
  integral : ∀ S, Algebra.IsIntegral R S →
    DiscE (perfd.obj S) ∧ IsIntegralPerfectoid (H0E (perfd.obj S)) p
  excision : ∀ (S T : A_R) (f : S →ₐ[R] T) (I : Ideal S),
    IsModuleComplete S (p : S) (ModuleCat.of S S) →
    IsModuleComplete T (p : T) (ModuleCat.of T T) →
    IsModuleComplete S (p : S) (ModuleCat.of S I) →
    ArcOutside f I → IsHomotopyPullbackSquare (perfdSquareE perfd f I)
```

`WeakEquivalenceTo` は必要な zigzag とその弱同値性、`ConeOverSourceCompatibility` は
§4 と同じ S 上の指定錐・単位との両立を表す補助型。単なる Ho(Alg_E) の引き戻しではない。
`IsHomotopyPullbackSquare(A,B,C,D)` は、任意の X に対する比較
`Map^h(X,A) → Map^h(X,B) ×^h_{Map^h(X,D)} Map^h(X,C)` が弱同値であること。
`IsHomotopyLimitCone` も `Map^h(X,vertex) → holim_i Map^h(X,F_i)` で検出する。
同値な計算方法は図式を Reedy fibrant に置換して通常の極限を取るもの。
`universal` の precomposition は cofibrant replacement / frame も関手的に選んで定義する。
離散 P_E(S) は離散代数 `jE(H0E(P_E(S)))` と弱同値であり、両側の Map^h が
離散な R 代数準同型集合に弱同値になる。π₀ の全単射から E3 の universal を得る。
任意の環準同型 `S → T` に対して R 作用をその合成で入れれば、R 線形版から
`IsPerfectoidization` が要求するすべての環準同型の普遍性になる。

**モデル表示の責務。** 転送・Σ-cofibrancy・Map^h・右 Quillen 性だけでは、BS の E∞ 対象を
自動的に Alg_E の対象と同定できない。具体的な一般定理は Hinich,
[*Rectification of Algebras and Modules*](https://www.maths.tcd.ie/EMIS/journals/DMJDMV/vol-20/25.pdf),
Thm 4.1.1 (p.902)。§2.4.6 (p.887) の homotopically sound は admissible かつ Σ-cofibrant。
基底 k=R、位相的オペラッド O=Com、sound replacement `E → C_*(Com;R)=Com_R` として適用し、
`Alg_E(R)[W⁻¹] ≃ CAlg(D(R))` を得る。底への整合性は同論文 §4.2 の図式(49)、
j・H⁰ は離散部分の比較で追う。この表示定理の Lean 実装は E2 の比較工程に残る。
HA Thm 4.5.4.7 は
freely powered 等の仮定を持つ **strict commutative algebra** の定理であり、任意標数の
Ch(R) にそのまま適用しない。E の admissibility・Σ-cofibrancy を E2a で確認して上の定理を使う。
E2a の界面自体に CAlg や coherent nerve を導入する必要はなく、E2b の実装とは区別できる。
ただし「表示比較が不要」という意味での γ 不要とは主張しない。

E2a → E3 は U の homotopy 極限保存、Ch(R) と semifree の D(R) の比較、
homotopy 極限と ∞ 極限の比較（HA 1.3.4.23）を通す。右 Quillen 性だけから
`IsPullbackSquare` という quasicategory の述語へ飛ばさない。

## 6. 現在の二入力の正確な対象と導出

### 6.1 整代数の存在入力

[Inputs/Perfectoidization.lean](../SerrePositivity/BhattScholze/Inputs/Perfectoidization.lean) の型：

```lean
exists_perfectoidization_of_integral
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Algebra.IsIntegral R S]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p) :
    ∃ (C : Type u) (_ : CommRing C) (f : S →+* C), IsPerfectoidization p f
```

`IsPerfectoidization p f` の定義は
`IsIntegralPerfectoid C p ∧ ∀ T [CommRing T], IsIntegralPerfectoid T p →
∀ g : S →+* T, ∃! l : C →+* T, l.comp f = g`。
E3 では `integral S` で離散性を得て `universal S` を適用し、
`C := h0.B.obj S`、`f := h0.η₀ S` を取る。E2a では integral と discrete_perfectoid、
Map^h の離散比較と π₀ の全単射から同じ型を得る。
有限性・有限表示性・有界 p 冪ねじれ・S の完備性は追加しない。

### 6.2 Excision 入力

[Inputs/ArcExcision.lean](../SerrePositivity/BhattScholze/Inputs/ArcExcision.lean) の量化を固定する：

```lean
(R S T : Type u) [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
(p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
(f : S →ₐ[R] T) (I : Ideal S)
(hS : IsModuleComplete S (p : S) (ModuleCat.of S S))
(hT : IsModuleComplete T (p : T) (ModuleCat.of T T))
(hI : IsModuleComplete S (p : S) (ModuleCat.of S I))
(harc : ∀ (V : Type u) [CommRing V] [IsDomain V] [ValuationRing V],
  ringKrullDim V = 1 → IsAdicComplete (Ideal.span {(p : V)}) V →
  ∀ k : S →+* V, ¬ (I ≤ RingHom.ker k) → ∃! l : T →+* V, l.comp f.toRingHom = k)
{C D Q E : Type u} [CommRing C] [CommRing D] [CommRing Q] [CommRing E]
{ηS : S →+* C} {ηT : T →+* D} {ηQ : S ⧸ I →+* Q} {ηE : T ⧸ I.map f.toRingHom →+* E}
(hC : IsPerfectoidization p ηS) (hD : IsPerfectoidization p ηT)
(hQ : IsPerfectoidization p ηQ) (hE : IsPerfectoidization p ηE)
```

結論は `IsPullback (CommRingCat.ofHom a) (CommRingCat.ofHom b)
(CommRingCat.ofHom c) (CommRingCat.ofHom d)`。四辺は正確に：

```lean
a := IsPerfectoidization.map hC hD f.toRingHom
b := IsPerfectoidization.map hC hQ (Ideal.Quotient.mk I)
c := IsPerfectoidization.map hD hE (Ideal.Quotient.mk (I.map f.toRingHom))
d := IsPerfectoidization.map hQ hE
  (Ideal.quotientMap (I.map f.toRingHom) f.toRingHom Ideal.le_comap_map)
```

現入力は差写像の全射性を含めない。界面からは次の強い結論まで証明する。

1. hS,hI と `0 → I → S → S/I → 0` の三角から `S/I` の導来 p 完備性を得る。
   `T/IT` の完備性や IT の完備性は仮定にない。右下の perfectoid 化は §2 の拡張で読み、
   その導来 p 完備化への移行で全 perfectoid 標的への写像が変わらないことを示す。
   Cor 8.12 の右下の表記はこの意味で型を与える。IT の完備性を追加してはいけない。
2. hC は `(C,ηS)` が `PerfUnder_u S` の始対象であることそのもの。
   `limit_isLimit` と既存 `initialCofinality`（Core/InitialCofinality.lean）から
   `P(S) ≃ J(C)` を、S 上の錐と単位に両立する形で得る。他の3頂点も同様。
   したがって4頂点とも離散。H⁰ の射影の乗法保存から同定は環同型となる。
   H⁰ の極限表示だけで満足せず、**導来対象全体**の同値まで使う。
3. 単位の自然性と `IsPerfectoidization.lift_unique` / `map_comp` で
   H⁰ の4辺を上記 a,b,c,d に同定する。指定された普遍環を別の選択に取り替えない。
4. excision → D4 により、指定された可換性ホモトピーの四角形から fiber 列
   `P(S) → P(T) ⊕ P(S/I) → P(T/IT)` を得る。第2射は右辺 − 下辺。
   D3・D4 のシフト整合的な比較で Mathlib の distinguished triangle に移す。
5. 長完全列の部分は
   `H⁻¹(P(T/IT)) → H⁰(P(S)) → H⁰(P(T)) ⊕ H⁰(P(S/I)) → H⁰(P(T/IT)) → H¹(P(S))`。
   Lemma 8.4 で左端が0となり環の引き戻しを得る。さらに手順2の離散性で右端が0となり、
   `0 → C → D × Q → E → 0` が短完全、`(x,y) ↦ c(x) - d(y)` が全射。
   **coconnective だけでは最後の全射性は出ない**。a,b,c,d 個々の全射性は主張しない。
6. 既存 `ringHom_isPullback_of_distinguished_single_triangle` または
   `algHom_isPullback_of_module_shortExact`（CommutativeAlgebra/DerivedSingleTrianglePullback.lean）
   で `CommRingCat` の元の `IsPullback` へ渡す。差は加法群・加群の写像で、環準同型ではない。

### 6.3 CLMST への供給元

`BhattScholze/PerfectoidizationExcision.lean` の
`klCanonicalExcisionSquare_of_excision` は hQ,hE に既存の閉側の普遍単位を入れ、
左右辺を `lift_unique`、下辺を `perfectoidizationClosedComparison_eq_map` で一致させる。
`klCanonicalExcisionSquare_of_integral_away` は整性と awayMap の全単射から harc を供給する。
`CLMST/KLAicTorFromExcision.lean` の `KLCanonicalExcisionSquare` はまさにこの4辺の略記。
供給先は `CLMST/KLFiniteComparisonExcision.lean` の `klFiniteComparisonExcision_of_perfectoid`、
`CLMST/Prop247Proof.lean` の `prop247_finiteComparison_excision` と実 rank 図式の hPB。
Π3 で取り替えるのは元の Inputs の証明の供給元であり、これらの環・単位・4辺は保持する。
`KLCanonicalSingleTriangleBridge.lean` は指定された整数加群の三角から同じ四角形へ渡す既存の橋。

## 7. Π2 の一般補題・工程表と原文からの変更点

| 一般補題・工程 | 用途と現在の境界 |
| --- | --- |
| D3 の Hⁱ・シフト、D4 の有限引き戻しと fiber の同定、長完全列 | D3 の既存同値に加え、D4 の指定四辺と符号まで整合する比較が必要 |
| 次数0埋め込み J の関手性、heart の充満忠実性、H⁰ と `D≥0` の極限 | E3 の H⁰ 環、始対象による同定。D(R) の線形な Hom を環の Hom と混同しない |
| `initialCofinality` → 始対象の値が極限、極限錐の一意性と自然性 | 既存は slice 制限の trivial Kan fibration。指定錐と頂点の同定を包む補題を追加 |
| 導来 p 完備性の定義の比較、完備化の反射性、スカラー制限、三角・極限閉性 | `IsModuleComplete` は全次数の局所化からの Hom 消滅。通常の完備性と無条件に同一視しない |
| 離散 perfectoid の BS / Lean 比較、零環の扱い | 原文の各 perfectoid 条件を `IsIntegralPerfectoid` に移す |
| `PerfUnder_u` のサイズ、u-small cover と Q_•、Čech coinitiality | §2.1 の特定の極限錐を保証する。一般の巨大極限や D の宇宙拡大は要求しない |
| Alg_E の転送モデル構造、U の homotopy 極限保存、frame、表示比較 | E2a の責務。HA 4.5.4.7 の無条件適用を避ける |
| 離散 E∞ 代数の切断と Map^h の環 Hom 比較 | E2a の離散時 universal → 既存 `IsPerfectoidization` |
| 環の射影・単位と H⁰ の自然性、短完全列から環の引き戻し | 後半の橋は既存。前半の比較等式と差写像の全射性を証明する |

### Π2：E3 の型を置く順序と担当

以下の担当はレーン・モジュールの責務を指す。実装した公開型は本節末尾に記録する。
配置は `BhattScholze/PerfectoidizationInterface/`。一般補題を文献入力の欄へ混ぜない。

| 順序 | Lean に置くもの・受入条件 | 一般補題の担当と依存 |
| --- | --- | --- |
| Π2-0 記号・宇宙 | `A_R`、`C_R`、`PerfUnder_u` と忘却図式の1圏のデータ。対象 Type (u+1)、標的環 Type u を固定 | Π/Setup。nerve の Hom 宇宙の調整は α。巨大極限の存在 instance を置かない |
| Π2-1 底の関手 | `J : nerve A_R → D(R)`、Hⁱ、`Disc`、自然変換・辺の評価を包装 | β/D と α。D3、次数0埋め込みの関手性と H⁰ の比較。perfd・unit の欄の型をここで固定 |
| Π2-2 完備化の橋 | `S^∧₀` と単位を通常の R 代数の関手に包装。完備性と C_R 上の単位同型を証明 | DerivedCompletion が Λ・単位・H⁰ 完備性・環の一意延長を供給済み。Π/Completion が自然性・制限した標的圏同値・錐の輸送を担当。animated Map は E2 に留保 |
| Π2-3 H⁰・limit データ | `H0RingData`、`BSLimitConeData` を定義。射影・単位の環準同型と各自然性を型に含める | Π/LimitData。α は既存 `JoinCone`・`IsLimitCone`、β は H⁰ の自然性を供給。H⁰ の極限保存は α/β の一般補題 |
| Π2-4 構造体 | perfd、unit、h0、coconnective、離散時 universal、limit、integral、excision の型を宣言 | Π/Interface。excision の四角形・2単体は元の商図式から作る。D4 の定理の証明を待たず構造体の型を置ける |
| Π2-5 始対象の橋 | `hC : IsPerfectoidization p η` から `P(S) ≃ J(C)` を指定錐・単位に両立して導く。4辺を map に同定 | α は §2.1 の二宇宙対応と `initialCofinality` からの極限計算・一意性、Π/Comparison は環同型と `lift_unique` の比較等式を担当。ここで全4頂点の離散性を得る |
| Π2-6 存在入力 | integral → Disc → universal で `exists_perfectoidization_of_integral` と同じ型を証明 | Π/Integral。§2.2 の包装により非完備 S も扱う。既存の存在入力を証明中に使わない |
| Π2-7 Excision 入力 | 四頂点の Disc を仮定として受け取り、excision → D4 → 指定された差の fiber 列 → 長完全列 → 短完全列・差の全射性・環の引き戻し | β/D4・D6a の公開定理を使い、Π/Excision が既存の4辺へ輸送。最後は既存 DerivedSingleTrianglePullback の橋を使う。Disc の供給は Π2-5 後半の `specified_disc` で埋める（Π2-7′） |
| Π2-8 存在と監査 | E3 界面の存在だけを一つの文献入力にする。二入力の界面依存版を監査 | Π/Existence。BS の各命題・§2 の紙上導出に対応する。旧 Inputs の置換と CLMST の付替えは Π3 として別に行う |

Π2-3 の limit 欄は特定の錐の極限性を受け取るので、§2.1 の cover 構成を Lean で先に
実装する必要はない。存在入力の根拠をさらに形式化する段階では、BS/§7 が U・Q_n と環の
Hom の表示、α が「有限 coproduct 冪による Čech 図式の coinitiality」と comma 圏の可縮性、
β が可算 Tot、Π が指定錐への同定を担当する。既存 `initialCofinality` だけでこの
Čech coinitiality まで証明済みとは扱わない。
同様に §2.2 の animated 完備化と既存の加群完備化の乗法・単位付き比較、離散標的への
Map と π₀ の比較は E2 が担当し、E3 の二入力への橋は環 Hom の既存定理で閉じる。

型を置く順序は `0 → 1 → 2 → 3 → 4`、その後 `5` と `6`、最後に `7 → 8`。
Π2-6 は Π2-5 を待たず、界面の integral・universal のみで進められる。
各欄の一般補題の帰属は、perfd・unit が Π2-1、H⁰ が Π2-3、coconnective の判定が β/D、
universal の通常環への包装が Π2-5、limit の coinitiality が α、integral の非完備拡張が
Π2-2・6、excision の長完全列が β/D6a、環への帰結が Π2-7 である。
D6a の `derivedSquareFiberTriangle_distinguished`・`derivedSquareInfinityHomologyLongExact`、
D6b の `moduleHeartHomEquiv`、D6c の `derivedInfinityDisc_iff`・
`derivedInfinityDiscEdge_invertible` は公開済み。Π2-7 では Disc の消滅条件から直接
長完全列の両端を消せる。指定普遍環との H⁰ 環同型と四辺の一致は universal と単位の自然性で得る。
Π2-5 後半は別途、始対象への制限と極限錐の一意性から指定錐・単位付き導来同値を持つ。

採用する変更は、(i) Cor 8.12 を E3 では D(R) で述べる、(ii) E2a では homotopy
引き戻し・Map^h で述べる、(iii) universal を Cor 8.14 の **離散時**に限定する、
(iv) Prop 8.5 の limit を `PerfUnder_u(S)` に制限し H⁰ の乗法整合性も保持する、(v) 非完備整代数のため始域を拡張する、
(vi) 既存の環の入力を得た後に、追加の帰結として差写像の全射性も示す、の6点。
Prop 8.13 の対称モノイダル性自体はこの最小界面の欄に加えず、Cor 8.14 の根拠として記録した。
界面の存在を一つの文献入力に集約しても、この文書に挙げた一般比較補題の証明まで
完了したことにはならない。Π1 の成果と Π2・Π3 の完了を分けて監査する。

### Π2-0

```lean
namespace SerrePositivity.BhattScholze.PerfectoidizationInterface
universe u
open CategoryTheory SerrePositivity.DerivedCompletion
A_R (R : Type u) [CommRing R] : Type (u + 1)
ofAlgebra (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] : A_R R
completeProperty (R : Type u) [CommRing R] (p : ℕ) : ObjectProperty (A_R R)
C_R (R : Type u) [CommRing R] (p : ℕ) : Type (u + 1)
completeInclusion (R : Type u) [CommRing R] (p : ℕ) : C_R R p ⥤ A_R R
perfectoidTargetProperty (p : ℕ) [Fact p.Prime] (S : CommRingCat.{u}) :
    ObjectProperty (Under S)
PerfUnder_u (p : ℕ) [Fact p.Prime] (S : CommRingCat.{u}) : Type (u + 1)
perfectoidTargetInclusion (p : ℕ) [Fact p.Prime] (S : CommRingCat.{u}) :
    PerfUnder_u p S ⥤ Under S
targetAlgebra (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime] (S : A_R R) :
    PerfUnder_u p S.right ⥤ A_R R
algebraNerve (R : Type u) [CommRing R] : SSet.{u + 1}
perfectoidTargetNerve (p : ℕ) [Fact p.Prime] (S : CommRingCat.{u}) : SSet.{u + 1}
end SerrePositivity.BhattScholze.PerfectoidizationInterface
```

### Π2-1

```lean
namespace SerrePositivity.BhattScholze.PerfectoidizationInterface
universe u
open CategoryTheory CategoryTheory.Limits DifferentialGraded
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable (R : Type u) [CommRing R]
J : algebraNerve R ⟶ derivedInfinityCategory R
vertex (F : algebraNerve R ⟶ derivedInfinityCategory R) (S : A_R R) :
    (derivedInfinityCategory R) _⦋0⦌
edge (F : algebraNerve R ⟶ derivedInfinityCategory R) {S T : A_R R} (f : S ⟶ T) :
    (derivedInfinityCategory R).Edge (vertex R F S) (vertex R F T)
HFunctor (i : ℤ) : derivedInfinityHomotopyCategory R ⥤ ModuleCat.{u} R
H (i : ℤ) (x : (derivedInfinityCategory R) _⦋0⦌) : ModuleCat.{u} R
HMap (i : ℤ) {x y : (derivedInfinityCategory R) _⦋0⦌}
    (e : (derivedInfinityCategory R).Edge x y) : H R i x ⟶ H R i y
HIso (i : ℤ) (x : (derivedInfinityCategory R) _⦋0⦌) :
    H R i x ≅ (derivedInfinityCategoryVertexEquiv R x).val.homology i
JHZeroIso (S : A_R R) :
    H R 0 (vertex R (J R) S) ≅ (discreteAlgebraModule R).obj S
Disc (x : (derivedInfinityCategory R) _⦋0⦌) : Prop
NatInfinity (F G : algebraNerve R ⟶ derivedInfinityCategory R) : Type (u + 1)
component {F G : algebraNerve R ⟶ derivedInfinityCategory R}
    (η : NatInfinity R F G) (S : A_R R) :
    (derivedInfinityCategory R).Edge (vertex R F S) (vertex R G S)
targetDiagram (p : ℕ) [Fact p.Prime] (S : A_R R) :
    perfectoidTargetNerve p S.right ⟶ derivedInfinityCategory R
end SerrePositivity.BhattScholze.PerfectoidizationInterface
```

### Π2-2

```lean
namespace SerrePositivity.BhattScholze.PerfectoidizationInterface
universe u
open CategoryTheory SerrePositivity.DerivedCompletion SerrePositivity.InfinityCategories
open scoped Simplicial
variable (p : ℕ)
def completionRing (S : CommRingCat.{u}) : CommRingCat.{u}
def completionUnit (S : CommRingCat.{u}) : S ⟶ completionRing p S
theorem completionRing_complete (S : CommRingCat.{u}) :
    IsModuleComplete (completionRing p S) (p : completionRing p S)
      (ModuleCat.of (completionRing p S) (completionRing p S))
theorem complete_along_map {S T : CommRingCat.{u}} (f : S ⟶ T)
    (hT : IsModuleComplete T (p : T) (ModuleCat.of T T)) :
    letI
theorem completion_existsUnique {S T : CommRingCat.{u}} (f : S ⟶ T)
    (hT : IsModuleComplete T (p : T) (ModuleCat.of T T)) :
    ∃! g : completionRing p S ⟶ T, completionUnit p S ≫ g = f
def completionLift {S T : CommRingCat.{u}} (f : S ⟶ T)
    (hT : IsModuleComplete T (p : T) (ModuleCat.of T T)) : completionRing p S ⟶ T
@[simp] theorem completionLift_comp {S T : CommRingCat.{u}} (f : S ⟶ T)
    (hT : IsModuleComplete T (p : T) (ModuleCat.of T T)) :
    completionUnit p S ≫ completionLift p f hT = f
theorem completion_hom_ext {S T : CommRingCat.{u}}
    (hT : IsModuleComplete T (p : T) (ModuleCat.of T T))
    {f g : completionRing p S ⟶ T}
    (h : completionUnit p S ≫ f = completionUnit p S ≫ g) : f = g
def completionMap {S T : CommRingCat.{u}} (f : S ⟶ T) :
    completionRing p S ⟶ completionRing p T
@[simp] theorem completionMap_comp {S T : CommRingCat.{u}} (f : S ⟶ T) :
    completionUnit p S ≫ completionMap p f = f ≫ completionUnit p T
@[simp] theorem completionMap_id (S : CommRingCat.{u}) : completionMap p (𝟙 S) = 𝟙 _
@[simp] theorem completionMap_comp_map {S T U : CommRingCat.{u}} (f : S ⟶ T) (g : T ⟶ U) :
    completionMap p (f ≫ g) = completionMap p f ≫ completionMap p g
def ringCompletionFunctor : CommRingCat.{u} ⥤ CommRingCat.{u}
def completionUnitIso (S : CommRingCat.{u})
    (hS : IsModuleComplete S (p : S) (ModuleCat.of S S)) : S ≅ completionRing p S
def completionFunctor (R : Type u) [CommRing R] : A_R R ⥤ A_R R
def completionAlgebraUnit (R : Type u) [CommRing R] : 𝟭 (A_R R) ⟶ completionFunctor p R
def completionAlgebraUnitIso (R : Type u) [CommRing R] (S : C_R R p) :
    S.obj ≅ (completionFunctor p R).obj S.obj
variable [Fact p.Prime]
def targetRestriction (S : CommRingCat.{u}) :
    PerfUnder_u p (completionRing p S) ⥤ PerfUnder_u p S
def targetExtension (S : CommRingCat.{u}) :
    PerfUnder_u p S ⥤ PerfUnder_u p (completionRing p S)
def completionTargetEquivalence (S : CommRingCat.{u}) :
    PerfUnder_u p (completionRing p S) ≌ PerfUnder_u p S
def restrictCone {K L X : SSet.{u + 1}} {F : K ⟶ X}
    (c : JoinCone F) (f : L ⟶ K) : JoinCone (f ≫ F)
theorem restrictCone_vertex {K L X : SSet.{u + 1}} {F : K ⟶ X}
    (c : JoinCone F) (f : L ⟶ K) : (restrictCone c f).vertex = c.vertex
theorem targetRestriction_algebra (R : Type u) [CommRing R] (S : A_R R) :
    targetRestriction p S.right ⋙ targetAlgebra R p S =
      targetAlgebra R p ((completionFunctor p R).obj S)
theorem targetExtension_algebra (R : Type u) [CommRing R] (S : A_R R) :
    targetExtension p S.right ⋙ targetAlgebra R p ((completionFunctor p R).obj S) =
      targetAlgebra R p S
theorem targetDiagram_restriction (R : Type u) [CommRing R] (S : A_R R) :
    nerveMap (targetRestriction p S.right) ≫ targetDiagram R p S =
      targetDiagram R p ((completionFunctor p R).obj S)
theorem targetDiagram_extension (R : Type u) [CommRing R] (S : A_R R) :
    nerveMap (targetExtension p S.right) ≫
        targetDiagram R p ((completionFunctor p R).obj S) = targetDiagram R p S
def completionRestrictCone (R : Type u) [CommRing R] (S : A_R R)
    (c : JoinCone (targetDiagram R p S)) :
    JoinCone (targetDiagram R p ((completionFunctor p R).obj S))
def completionExtendCone (R : Type u) [CommRing R] (S : A_R R)
    (c : JoinCone (targetDiagram R p ((completionFunctor p R).obj S))) :
    JoinCone (targetDiagram R p S)
theorem completionRestrictCone_vertex (R : Type u) [CommRing R] (S : A_R R)
    (c : JoinCone (targetDiagram R p S)) : (completionRestrictCone p R S c).vertex = c.vertex
theorem completionExtendCone_vertex (R : Type u) [CommRing R] (S : A_R R)
    (c : JoinCone (targetDiagram R p ((completionFunctor p R).obj S))) :
    (completionExtendCone p R S c).vertex = c.vertex
end SerrePositivity.BhattScholze.PerfectoidizationInterface
```

### Π2-3

```lean
namespace SerrePositivity.BhattScholze.PerfectoidizationInterface
universe u
open CategoryTheory CategoryTheory.Limits SerrePositivity.InfinityCategories
open scoped Simplicial
variable (R : Type u) [CommRing R]
structure H0RingData (P : algebraNerve R ⟶ derivedInfinityCategory R)
    (η : NatInfinity R (J R) P) where
  ringFunctor : A_R R ⥤ A_R R
  moduleIso : ∀ S, (discreteAlgebraModule R).obj (ringFunctor.obj S) ≅ H R 0 (vertex R P S)
  map_compat : ∀ {S T} (f : S ⟶ T),
    (discreteAlgebraModule R).map (ringFunctor.map f) ≫ (moduleIso T).hom =
      (moduleIso S).hom ≫ HMap R 0 (edge R P f)
  unit : 𝟭 (A_R R) ⟶ ringFunctor
  unit_compat : ∀ S,
    (JHZeroIso R S).hom ≫ (discreteAlgebraModule R).map (unit.app S) ≫ (moduleIso S).hom =
      HMap R 0 (component R η S)

def joinLegSimplex {K : SSet.{u + 1}} (x : K _⦋0⦌) : (join (Δ[0] : SSet.{u + 1}) K) _⦋1⦌

def targetUnitMap (p : ℕ) [Fact p.Prime] (S : A_R R) (T : PerfUnder_u p S.right) :
    S ⟶ (targetAlgebra R p S).obj T

theorem targetUnitMap_naturality (p : ℕ) [Fact p.Prime] (S : A_R R)
    {T U : PerfUnder_u p S.right} (f : T ⟶ U) :
    targetUnitMap R p S T ≫ (targetAlgebra R p S).map f = targetUnitMap R p S U

structure BSLimitConeData (p : ℕ) [Fact p.Prime]
    (P : algebraNerve R ⟶ derivedInfinityCategory R) (η : NatInfinity R (J R) P)
    (h0 : H0RingData R P η) (S : A_R R) where
  cone : JoinCone (targetDiagram R p S)
  vertex_eq : cone.vertex = vertex R P S
  sourceCone : JoinCone (nerveMap (targetAlgebra R p S))
  source_vertex : sourceCone.vertex = ComposableArrows.mk₀ S
  source_legs : ∀ T, sourceCone.val.app _ (joinLegSimplex (ComposableArrows.mk₀ T)) =
    ComposableArrows.mk₁ (targetUnitMap R p S T)
  overSource : (sliceOver (targetDiagram R p S)).Edge (sourceCone.postcomp (J R)) cone
  overSource_unit : (overSource.map (sliceOverProjection (targetDiagram R p S))).edge =
    (component R η S).edge
  projectionEdge : ∀ T : PerfUnder_u p S.right,
    (derivedInfinityCategory R).Edge (vertex R P S) (vertex R (J R) ((targetAlgebra R p S).obj T))
  projectionEdge_eq : ∀ T, (projectionEdge T).edge =
    cone.val.app _ (joinLegSimplex (ComposableArrows.mk₀ T))
  projection : ∀ T : PerfUnder_u p S.right, h0.ringFunctor.obj S ⟶ (targetAlgebra R p S).obj T
  projection_unit : ∀ T, h0.unit.app S ≫ projection T = targetUnitMap R p S T
  projection_naturality : ∀ {T U : PerfUnder_u p S.right} (f : T ⟶ U),
    projection T ≫ (targetAlgebra R p S).map f = projection U
  projection_compat : ∀ T,
    (h0.moduleIso S).hom ≫ HMap R 0 (projectionEdge T) ≫
        (JHZeroIso R ((targetAlgebra R p S).obj T)).hom =
      (discreteAlgebraModule R).map (projection T)
end SerrePositivity.BhattScholze.PerfectoidizationInterface
```

### Π2-4

```lean
namespace SerrePositivity.BhattScholze.PerfectoidizationInterface
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open SerrePositivity.InfinityCategories SerrePositivity.DerivedCompletion
open scoped Simplicial
variable (R : Type u) [CommRing R]
def ordinarySquare {A B C D : A_R R} (a : A ⟶ B) (b : A ⟶ C)
    (c : B ⟶ D) (d : C ⟶ D) (w : a ≫ c = b ≫ d) :
    (Δ[1] : SSet.{u + 1}) ⊗ Δ[1] ⟶ algebraNerve R

theorem ordinarySquare_triangle_zero {A B C D : A_R R} (a : A ⟶ B) (b : A ⟶ C)
    (c : B ⟶ D) (d : C ⟶ D) (w : a ≫ c = b ≫ d) :
    squareTriangle 0 ≫ ordinarySquare R a b c d w =
      SSet.yonedaEquiv.symm (ComposableArrows.mk₂ b d)

theorem ordinarySquare_triangle_one {A B C D : A_R R} (a : A ⟶ B) (b : A ⟶ C)
    (c : B ⟶ D) (d : C ⟶ D) (w : a ≫ c = b ≫ d) :
    squareTriangle 1 ≫ ordinarySquare R a b c d w =
      SSet.yonedaEquiv.symm (ComposableArrows.mk₂ a c)

def quotientAlgebra (S : A_R R) (I : Ideal S.right) : A_R R

def quotientProjection (S : A_R R) (I : Ideal S.right) : S ⟶ quotientAlgebra R S I

def quotientComparison {S T : A_R R} (f : S ⟶ T) (I : Ideal S.right) :
    quotientAlgebra R S I ⟶ quotientAlgebra R T (I.map f.right.hom)

theorem quotientSquare_commutes {S T : A_R R} (f : S ⟶ T) (I : Ideal S.right) :
    f ≫ quotientProjection R T (I.map f.right.hom) =
      quotientProjection R S I ≫ quotientComparison R f I

def perfdSquare (P : algebraNerve R ⟶ derivedInfinityCategory R)
    {S T : A_R R} (f : S ⟶ T) (I : Ideal S.right) :
    (Δ[1] : SSet.{u + 1}) ⊗ Δ[1] ⟶ derivedInfinityCategory R

theorem perfdSquare_triangle_zero (P : algebraNerve R ⟶ derivedInfinityCategory R)
    {S T : A_R R} (f : S ⟶ T) (I : Ideal S.right) :
    squareTriangle 0 ≫ perfdSquare R P f I =
      SSet.yonedaEquiv.symm (ComposableArrows.mk₂
        (quotientProjection R S I) (quotientComparison R f I)) ≫ P

theorem perfdSquare_triangle_one (P : algebraNerve R ⟶ derivedInfinityCategory R)
    {S T : A_R R} (f : S ⟶ T) (I : Ideal S.right) :
    squareTriangle 1 ≫ perfdSquare R P f I =
      SSet.yonedaEquiv.symm (ComposableArrows.mk₂ f
        (quotientProjection R T (I.map f.right.hom))) ≫ P

def ArcOutside (p : ℕ) {S T : A_R R} (f : S ⟶ T) (I : Ideal S.right) : Prop

structure PerfectoidizationInterfaceE3 (R : Type u) [CommRing R]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p) where
  perfd : algebraNerve R ⟶ derivedInfinityCategory R
  unit : NatInfinity R (J R) perfd
  h0 : H0RingData R perfd unit
  coconnective : ∀ S (i : ℤ), i < 0 → IsZero (H R i (vertex R perfd S))
  universal : ∀ S, Disc R (vertex R perfd S) →
    IsPerfectoidization p (h0.unit.app S).right.hom
  limitCone : ∀ S, BSLimitConeData R p perfd unit h0 S
  limit_isLimit : ∀ S, IsLimitCone (limitCone S).cone
  integral : ∀ (S : A_R R),
    (letI : Algebra R S.right := S.hom.hom.toAlgebra; Algebra.IsIntegral R S.right) →
    Disc R (vertex R perfd S) ∧ IsIntegralPerfectoid (h0.ringFunctor.obj S).right p
  excision : ∀ {S T : A_R R} (f : S ⟶ T) (I : Ideal S.right),
    IsModuleComplete S.right (p : S.right) (ModuleCat.of S.right S.right) →
    IsModuleComplete T.right (p : T.right) (ModuleCat.of T.right T.right) →
    IsModuleComplete S.right (p : S.right) (ModuleCat.of S.right I) →
    ArcOutside R p f I → IsPullbackSquare (perfdSquare R perfd f I)
end SerrePositivity.BhattScholze.PerfectoidizationInterface
```

### Π2-5（始対象の宣言）

```lean
namespace SerrePositivity.BhattScholze.PerfectoidizationInterface
universe u
open CategoryTheory CategoryTheory.Limits
variable (p : ℕ) [Fact p.Prime]
specifiedTarget (S : CommRingCat.{u}) {C : Type u} [CommRing C]
    (η : S →+* C) (hC : IsPerfectoidization p η) : PerfUnder_u p S
specifiedTargetTo (S : CommRingCat.{u}) {C : Type u} [CommRing C]
    (η : S →+* C) (hC : IsPerfectoidization p η) (T : PerfUnder_u p S) :
    specifiedTarget p S η hC ⟶ T
specifiedTarget_isInitial (S : CommRingCat.{u}) {C : Type u} [CommRing C]
    (η : S →+* C) (hC : IsPerfectoidization p η) : IsInitial (specifiedTarget p S η hC)
end SerrePositivity.BhattScholze.PerfectoidizationInterface
```

### Π2-6

```lean
namespace SerrePositivity.BhattScholze.PerfectoidizationInterface
universe u
exists_perfectoidization_of_integral
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Algebra.IsIntegral R S]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (F : PerfectoidizationInterfaceE3 R p hR) :
    ∃ (C : Type u) (_ : CommRing C) (f : S →+* C), IsPerfectoidization p f
end SerrePositivity.BhattScholze.PerfectoidizationInterface
```

### Π2-7（Disc を仮定する excision の橋）

```lean
namespace SerrePositivity.BhattScholze.PerfectoidizationInterface
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open SerrePositivity.InfinityCategories
open scoped Simplicial
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R]
theorem squareHZero_shortExact
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ derivedInfinityCategory R)
    (hF : IsPullbackSquare F)
    (hD : IsZero (derivedInfinityHomology R (-1) (derivedSquareTargetVertex F)))
    (hA : IsZero (derivedInfinityHomology R 1 (pullbackCone F).vertex)) :
    (derivedSquareInfinityHomology₂ F hF 0).ShortExact

abbrev underAlgebra (S : A_R R) : Algebra R S.right

attribute [local instance] underAlgebra

def underAlgHom {S T : A_R R} (f : S ⟶ T) : S.right →ₐ[R] T.right

variable {P : algebraNerve R ⟶ derivedInfinityCategory R}
    {η : NatInfinity R (J R) P} (h0 : H0RingData R P η)
    {A B C D : A_R R} (a : A ⟶ B) (b : A ⟶ C)
    (c : B ⟶ D) (d : C ⟶ D) (w : a ≫ c = b ≫ d)
def h0SquareShortComplex : ShortComplex (ModuleCat.{u} R)

theorem h0SquareShortComplex_shortExact
    (hF : IsPullbackSquare (ordinarySquare R a b c d w ≫ P))
    (hA : Disc R (vertex R P A)) (hD : Disc R (vertex R P D)) :
    (h0SquareShortComplex R h0 a b c d w).ShortExact

theorem h0Square_isPullback
    (hF : IsPullbackSquare (ordinarySquare R a b c d w ≫ P))
    (hA : Disc R (vertex R P A)) (hD : Disc R (vertex R P D)) :
    IsPullback (h0.ringFunctor.map a).right (h0.ringFunctor.map b).right
      (h0.ringFunctor.map c).right (h0.ringFunctor.map d).right

theorem h0Square_difference_surjective
    (hF : IsPullbackSquare (ordinarySquare R a b c d w ≫ P))
    (hA : Disc R (vertex R P A)) (hD : Disc R (vertex R P D)) :
    Function.Surjective (fun x : (h0.ringFunctor.obj B).right × (h0.ringFunctor.obj C).right =>
      (h0.ringFunctor.map c).right.hom x.1 - (h0.ringFunctor.map d).right.hom x.2)

variable (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (F : PerfectoidizationInterfaceE3 R p hR)
def h0PerfectoidEquiv (S : A_R R) (hS : Disc R (vertex R F.perfd S))
    {C : Type u} [CommRing C] (ηC : S.right →+* C) (hC : IsPerfectoidization p ηC) :
    (F.h0.ringFunctor.obj S).right ≃+* C

theorem h0PerfectoidEquiv_unit (S : A_R R) (hS : Disc R (vertex R F.perfd S))
    {C : Type u} [CommRing C] (ηC : S.right →+* C) (hC : IsPerfectoidization p ηC) :
    (h0PerfectoidEquiv R p hR F S hS ηC hC).toRingHom.comp (F.h0.unit.app S).right.hom = ηC

theorem h0PerfectoidEquiv_naturality {S T : A_R R} (f : S ⟶ T)
    (hS : Disc R (vertex R F.perfd S)) (hT : Disc R (vertex R F.perfd T))
    {C D : Type u} [CommRing C] [CommRing D]
    (ηC : S.right →+* C) (ηD : T.right →+* D)
    (hC : IsPerfectoidization p ηC) (hD : IsPerfectoidization p ηD) :
    (h0PerfectoidEquiv R p hR F T hT ηD hD).toRingHom.comp
        (F.h0.ringFunctor.map f).right.hom =
      (IsPerfectoidization.map hC hD f.right.hom).comp
        (h0PerfectoidEquiv R p hR F S hS ηC hC).toRingHom

theorem specifiedSquare_of_disc
    {A B C D : A_R R} (a : A ⟶ B) (b : A ⟶ C)
    (c : B ⟶ D) (d : C ⟶ D) (w : a ≫ c = b ≫ d)
    (hF : IsPullbackSquare (ordinarySquare R a b c d w ≫ F.perfd))
    (hA : Disc R (vertex R F.perfd A)) (hB : Disc R (vertex R F.perfd B))
    (hC : Disc R (vertex R F.perfd C)) (hD : Disc R (vertex R F.perfd D))
    {A' B' C' D' : Type u} [CommRing A'] [CommRing B'] [CommRing C'] [CommRing D']
    {ηA : A.right →+* A'} {ηB : B.right →+* B'}
    {ηC : C.right →+* C'} {ηD : D.right →+* D'}
    (hA' : IsPerfectoidization p ηA) (hB' : IsPerfectoidization p ηB)
    (hC' : IsPerfectoidization p ηC) (hD' : IsPerfectoidization p ηD) :
    let a' := IsPerfectoidization.map hA' hB' a.right.hom
    let b' := IsPerfectoidization.map hA' hC' b.right.hom
    let c' := IsPerfectoidization.map hB' hD' c.right.hom
    let d' := IsPerfectoidization.map hC' hD' d.right.hom
    IsPullback (CommRingCat.ofHom a') (CommRingCat.ofHom b')
        (CommRingCat.ofHom c') (CommRingCat.ofHom d') ∧
      Function.Surjective (fun x : B' × C' => c' x.1 - d' x.2)

theorem excision_of_disc {S T : A_R R} (f : S ⟶ T) (I : Ideal S.right)
    (hS : SerrePositivity.DerivedCompletion.IsModuleComplete S.right (p : S.right)
      (ModuleCat.of S.right S.right))
    (hT : SerrePositivity.DerivedCompletion.IsModuleComplete T.right (p : T.right)
      (ModuleCat.of T.right T.right))
    (hI : SerrePositivity.DerivedCompletion.IsModuleComplete S.right (p : S.right)
      (ModuleCat.of S.right I)) (harc : ArcOutside R p f I)
    (dS : Disc R (vertex R F.perfd S)) (dT : Disc R (vertex R F.perfd T))
    (dQ : Disc R (vertex R F.perfd (quotientAlgebra R S I)))
    (dE : Disc R (vertex R F.perfd (quotientAlgebra R T (I.map f.right.hom))))
    {C D Q E : Type u} [CommRing C] [CommRing D] [CommRing Q] [CommRing E]
    {ηS : S.right →+* C} {ηT : T.right →+* D}
    {ηQ : S.right ⧸ I →+* Q} {ηE : T.right ⧸ I.map f.right.hom →+* E}
    (hC : IsPerfectoidization p ηS) (hD : IsPerfectoidization p ηT)
    (hQ : IsPerfectoidization p ηQ) (hE : IsPerfectoidization p ηE) :
    let a := IsPerfectoidization.map hC hD f.right.hom
    let b := IsPerfectoidization.map hC hQ (Ideal.Quotient.mk I)
    let c := IsPerfectoidization.map hD hE (Ideal.Quotient.mk (I.map f.right.hom))
    let d := IsPerfectoidization.map hQ hE
      (Ideal.quotientMap (I.map f.right.hom) f.right.hom Ideal.le_comap_map)
    IsPullback (CommRingCat.ofHom a) (CommRingCat.ofHom b)
        (CommRingCat.ofHom c) (CommRingCat.ofHom d) ∧
      Function.Surjective (fun x : D × Q => c x.1 - d x.2)

theorem perfectoidization_excision_of_disc
    (S T : Type u) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (F : PerfectoidizationInterfaceE3 R p hR) (f : S →ₐ[R] T) (I : Ideal S)
    (hS : SerrePositivity.DerivedCompletion.IsModuleComplete S (p : S) (ModuleCat.of S S))
    (hT : SerrePositivity.DerivedCompletion.IsModuleComplete T (p : T) (ModuleCat.of T T))
    (hI : SerrePositivity.DerivedCompletion.IsModuleComplete S (p : S) (ModuleCat.of S I))
    (harc : ∀ (V : Type u) [CommRing V] [IsDomain V] [ValuationRing V],
      ringKrullDim V = 1 → IsAdicComplete (Ideal.span {(p : V)}) V →
      ∀ k : S →+* V, ¬ (I ≤ RingHom.ker k) →
        ∃! l : T →+* V, l.comp f.toRingHom = k)
    (dS : Disc R (vertex R F.perfd (ofAlgebra R S)))
    (dT : Disc R (vertex R F.perfd (ofAlgebra R T)))
    (dQ : Disc R (vertex R F.perfd (quotientAlgebra R (ofAlgebra R S) I)))
    (dE : Disc R (vertex R F.perfd (quotientAlgebra R (ofAlgebra R T) (I.map f.toRingHom))))
    {C D Q E : Type u} [CommRing C] [CommRing D] [CommRing Q] [CommRing E]
    {ηS : S →+* C} {ηT : T →+* D}
    {ηQ : S ⧸ I →+* Q} {ηE : T ⧸ I.map f.toRingHom →+* E}
    (hC : IsPerfectoidization p ηS) (hD : IsPerfectoidization p ηT)
    (hQ : IsPerfectoidization p ηQ) (hE : IsPerfectoidization p ηE) :
    let a := IsPerfectoidization.map hC hD f.toRingHom
    let b := IsPerfectoidization.map hC hQ (Ideal.Quotient.mk I)
    let c := IsPerfectoidization.map hD hE (Ideal.Quotient.mk (I.map f.toRingHom))
    let d := IsPerfectoidization.map hQ hE
      (Ideal.quotientMap (I.map f.toRingHom) f.toRingHom Ideal.le_comap_map)
    IsPullback (CommRingCat.ofHom a) (CommRingCat.ofHom b)
        (CommRingCat.ofHom c) (CommRingCat.ofHom d) ∧
      Function.Surjective (fun x : D × Q => c x.1 - d x.2)

end SerrePositivity.BhattScholze.PerfectoidizationInterface
```

### Π2-5（指定錐・単位付き比較）

```lean
namespace SerrePositivity.BhattScholze.PerfectoidizationInterface
universe u v w
open CategoryTheory CategoryTheory.Limits SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial
theorem sliceIdentityCone_terminal {X : SSet.{u}} [Quasicategory X] (x : X _⦋0⦌) :
    IsTerminalVertex (sliceIdentityCone x)

def initialValueCone {I : Type v} [Category.{w} I] {c : I} (hc : IsInitial c)
    {X : SSet.{max v w}} (F : nerve I ⟶ X) : JoinCone F

theorem initialValueCone_restriction {I : Type v} [Category.{w} I] {c : I} (hc : IsInitial c)
    {X : SSet.{max v w}} (F : nerve I ⟶ X) :
    ((initialRestriction F c).app (Opposite.op ⦋0⦌) (initialValueCone hc F)).val =
      SSet.const (F.app _ (nerveVertex c))

theorem initialValueCone_isLimit {I : Type v} [Category.{w} I] {c : I} (hc : IsInitial c)
    {X : SSet.{max v w}} [Quasicategory X] (F : nerve I ⟶ X) :
    IsLimitCone (initialValueCone hc F)

def coneHomotopyMap {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    (q : X ⟶ Y) :
    SSet.Truncated.HomotopyCategory₂ ((SSet.truncation 2).obj X) ⥤
      SSet.Truncated.HomotopyCategory₂ ((SSet.truncation 2).obj Y)

theorem coneHomotopyMap_homMk {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    (q : X ⟶ Y) {x y : X _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj X) x y) :
    (coneHomotopyMap q).map (SSet.Truncated.HomotopyCategory₂.homMk e) =
      SSet.Truncated.HomotopyCategory₂.homMk (e.map ((truncation 2).map q))

theorem coneEdge_isIso_of_edge_eq {X : SSet.{u}} [Quasicategory X]
    {x y x' y' : X _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj X) x y)
    (e' : SSet.Truncated.Edge (X := (truncation 2).obj X) x' y')
    (h : e.edge = e'.edge) [IsIso (SSet.Truncated.HomotopyCategory₂.homMk e')] :
    IsIso (SSet.Truncated.HomotopyCategory₂.homMk e)

theorem initialValueCone_leg {I : Type v} [Category.{w} I] {c : I} (hc : IsInitial c)
    {X : SSet.{max v w}} (F : nerve I ⟶ X) :
    (derivedConeLeg (initialValueCone hc F) (nerveVertex c)).edge =
      (SSet.Truncated.Edge.id (X := (truncation 2).obj X) (F.app _ (nerveVertex c))).edge

def initialLimitConeIso {I : Type v} [Category.{w} I] {c : I} (hc : IsInitial c)
    {X : SSet.{max v w}} [Quasicategory X] (F : nerve I ⟶ X)
    (a : JoinCone F) (ha : IsLimitCone a) :
    (SSet.HomotopyCategory.mk a : hoFunctor.obj (sliceOver F)) ≅
      SSet.HomotopyCategory.mk (initialValueCone hc F)

def initialLimitConeEdge {I : Type v} [Category.{w} I] {c : I} (hc : IsInitial c)
    {X : SSet.{max v w}} [Quasicategory X] (F : nerve I ⟶ X)
    (a : JoinCone F) (ha : IsLimitCone a) :
    SSet.Truncated.Edge (X := (truncation 2).obj (sliceOver F)) a (initialValueCone hc F)

theorem initialLimitConeEdge_homMk {I : Type v} [Category.{w} I] {c : I} (hc : IsInitial c)
    {X : SSet.{max v w}} [Quasicategory X] (F : nerve I ⟶ X)
    (a : JoinCone F) (ha : IsLimitCone a) :
    SSet.Truncated.HomotopyCategory₂.homMk (initialLimitConeEdge hc F a ha) =
      (terminalVertexIso₂ ha (initialValueCone_isLimit hc F)).hom

theorem initialLimitConeEdge_path {I : Type v} [Category.{w} I] {c : I} (hc : IsInitial c)
    {X : SSet.{max v w}} [Quasicategory X] (F : nerve I ⟶ X)
    (a : JoinCone F) (ha : IsLimitCone a) :
    (homotopyCategoryBridge (sliceOver F)).functor.map
        (SSet.Truncated.HomotopyCategory₂.homMk (initialLimitConeEdge hc F a ha)) =
      (initialLimitConeIso hc F a ha).hom

theorem initialLimitConeEdge_leg {I : Type v} [Category.{w} I] {c : I} (hc : IsInitial c)
    {X : SSet.{max v w}} [Quasicategory X] (F : nerve I ⟶ X)
    (a : JoinCone F) (ha : IsLimitCone a) (t : (nerve I) _⦋0⦌) :
    SSet.Truncated.HomotopyCategory₂.homMk
        ((initialLimitConeEdge hc F a ha).map ((truncation 2).map (sliceOverProjection F))) ≫
      SSet.Truncated.HomotopyCategory₂.homMk (derivedConeLeg (initialValueCone hc F) t) =
        SSet.Truncated.HomotopyCategory₂.homMk (derivedConeLeg a t)

theorem initialLimitLeg_isIso {I : Type v} [Category.{w} I] {c : I} (hc : IsInitial c)
    {X : SSet.{max v w}} [Quasicategory X] (F : nerve I ⟶ X)
    (a : JoinCone F) (ha : IsLimitCone a) :
    IsIso (SSet.Truncated.HomotopyCategory₂.homMk (derivedConeLeg a (nerveVertex c)))

end SerrePositivity.BhattScholze.PerfectoidizationInterface
```

```lean
namespace SerrePositivity.BhattScholze.PerfectoidizationInterface
universe u v w
open CategoryTheory CategoryTheory.Limits SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial
attribute [local instance] HasDerivedCategory.standard
variable (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R]
def specifiedAlgebra (S : A_R R) {C : Type u} [CommRing C]
    (ηC : S.right →+* C) (hC : IsPerfectoidization p ηC) : A_R R

theorem coneLeg_edge {K X : SSet.{u + 1}} {G : K ⟶ X}
    (a : JoinCone G) (v : K _⦋0⦌) :
    (derivedConeLeg a v).edge = a.val.app _ (joinLegSimplex v)

variable (hR : IsIntegralPerfectoid R p) (F : PerfectoidizationInterfaceE3 R p hR)
    (S : A_R R) {C : Type u} [CommRing C]
    (ηC : S.right →+* C) (hC : IsPerfectoidization p ηC)

def specifiedLimitConeIso :
    (SSet.HomotopyCategory.mk (F.limitCone S).cone :
        SSet.hoFunctor.obj (sliceOver (targetDiagram R p S))) ≅
      SSet.HomotopyCategory.mk (initialValueCone
        (specifiedTarget_isInitial p S.right ηC hC) (targetDiagram R p S))

theorem specifiedProjection_isIso :
    IsIso (SSet.Truncated.HomotopyCategory₂.homMk
      ((F.limitCone S).projectionEdge (specifiedTarget p S.right ηC hC)).toTruncated)

def specifiedDerivedIso :
    (⟨vertex R F.perfd S⟩ : derivedInfinityHomotopyCategory R) ≅
      ⟨vertex R (J R) (specifiedAlgebra p R S ηC hC)⟩

theorem specifiedDerivedIso_unit :
    SSet.Truncated.HomotopyCategory₂.homMk (component R F.unit S).toTruncated ≫
        (specifiedDerivedIso p R hR F S ηC hC).hom =
      SSet.Truncated.HomotopyCategory₂.homMk
        (edge R (J R) (targetUnitMap R p S (specifiedTarget p S.right ηC hC))).toTruncated

include ηC hC in
theorem specified_disc : Disc R (vertex R F.perfd S)

theorem specifiedRingProjection_isIso :
    IsIso ((F.limitCone S).projection (specifiedTarget p S.right ηC hC)).right

def specifiedRingIso : (F.h0.ringFunctor.obj S).right ≅ CommRingCat.of C

theorem specifiedRingIso_unit :
    (specifiedRingIso p R hR F S ηC hC).hom.hom.comp (F.h0.unit.app S).right.hom = ηC

end SerrePositivity.BhattScholze.PerfectoidizationInterface
```

### Π2-7′（離散性仮定の解消）

```lean
namespace SerrePositivity.BhattScholze.PerfectoidizationInterface
universe u v w
open CategoryTheory CategoryTheory.Limits SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial
open SerrePositivity.DerivedCompletion
variable (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) (F : PerfectoidizationInterfaceE3 R p hR)
    (f : S →ₐ[R] T) (I : Ideal S)
    (hS : IsModuleComplete S (p : S) (ModuleCat.of S S))
    (hT : IsModuleComplete T (p : T) (ModuleCat.of T T))
    (hI : IsModuleComplete S (p : S) (ModuleCat.of S I))
    (harc : ∀ (V : Type u) [CommRing V] [IsDomain V] [ValuationRing V],
      ringKrullDim V = 1 → IsAdicComplete (Ideal.span {(p : V)}) V →
      ∀ k : S →+* V, ¬ (I ≤ RingHom.ker k) →
        ∃! l : T →+* V, l.comp f.toRingHom = k)
    {C D Q E : Type u} [CommRing C] [CommRing D] [CommRing Q] [CommRing E]
    {ηS : S →+* C} {ηT : T →+* D}
    {ηQ : S ⧸ I →+* Q} {ηE : T ⧸ I.map f.toRingHom →+* E}
    (hC : IsPerfectoidization p ηS) (hD : IsPerfectoidization p ηT)
    (hQ : IsPerfectoidization p ηQ) (hE : IsPerfectoidization p ηE)


include F hS hT hI harc in
theorem perfectoidization_excision :
    let a := IsPerfectoidization.map hC hD f.toRingHom
    let b := IsPerfectoidization.map hC hQ (Ideal.Quotient.mk I)
    let c := IsPerfectoidization.map hD hE (Ideal.Quotient.mk (I.map f.toRingHom))
    let d := IsPerfectoidization.map hQ hE
      (Ideal.quotientMap (I.map f.toRingHom) f.toRingHom Ideal.le_comap_map)
    IsPullback (CommRingCat.ofHom a) (CommRingCat.ofHom b)
        (CommRingCat.ofHom c) (CommRingCat.ofHom d) ∧
      Function.Surjective (fun x : D × Q => c x.1 - d x.2)

include F hS hT hI harc in
theorem perfectoidization_excision_isPullback :
    IsPullback
      (CommRingCat.ofHom (IsPerfectoidization.map hC hD f.toRingHom))
      (CommRingCat.ofHom (IsPerfectoidization.map hC hQ (Ideal.Quotient.mk I)))
      (CommRingCat.ofHom (IsPerfectoidization.map hD hE (Ideal.Quotient.mk (I.map f.toRingHom))))
      (CommRingCat.ofHom (IsPerfectoidization.map hQ hE
        (Ideal.quotientMap (I.map f.toRingHom) f.toRingHom Ideal.le_comap_map)))

include F hS hT hI harc hC in
theorem perfectoidization_excision_difference_surjective :
    Function.Surjective (fun x : D × Q =>
      IsPerfectoidization.map hD hE (Ideal.Quotient.mk (I.map f.toRingHom)) x.1 -
      IsPerfectoidization.map hQ hE
        (Ideal.quotientMap (I.map f.toRingHom) f.toRingHom Ideal.le_comap_map) x.2)

end SerrePositivity.BhattScholze.PerfectoidizationInterface
```
