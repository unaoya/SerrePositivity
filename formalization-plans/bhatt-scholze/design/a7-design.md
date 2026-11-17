# A7 の設計：perfectoid 化の対称モノイダル性と離散な場合の普遍性（原典 Prop 8.13、Cor 8.14、2026-11-02）

概要：E3 を消す道筋の単位 A7。原典 BS 著者版 §8.2 の末尾：S ↦ S_perfd（perfectoid 環からの写像をもつ導来 p 完備な単体的環から、導来 p 完備な
E∞ 環へ）は対称モノイダル、すなわち任意の図式 S_1 ← S_3 → S_2 に対し S_{1,perfd} ⊗̂^L_{S_{3,perfd}} S_{2,perfd} → (S_1 ⊗̂^L_{S_3} S_2)_perfd が
同値（Prop 8.13）。S_perfd が連結（⇔ Lemma 8.4 により離散）なら S_perfd は perfectoid 環で S → S_perfd は perfectoid 環への普遍な写像（Cor 8.14）。
これが E3 の欄 `universal`。
方針：Prop 8.13 は原典どおり Construction 7.6 (5)（Δ の対称モノイダル性、A2-4）を完全化と mod d に通す。そのために Def 8.2 を原典の定義域
（導来 p 完備な単体的 R 代数）で述べ直す必要がある：Cor 8.14 の証明に出る S_perfd ⊗̂^L_S S_perfd は離散でないので、A4 の離散版だけでは
Prop 8.13 を使えない（D60）。Cor 8.14 は原典どおり：離散 ⇒ Δ_perf 離散で完全 prism（A4・A5-2 の芯）⇒ perfectoid；普遍性は
(S_perfd ⊗̂^L_S S_perfd)_perfd ≃ S_perfd（Prop 8.13 と、perfectoid T で T_perfd = T）から。
規約：基底 R（Not 8.1）を固定し、S_i は R 代数（原典の「perfectoid 環からの写像をもつ」）。E3 の始域の離散 S は S^∧ を経由（D41）。
Lean の名前は仮。ビルドしない。
使われ方：E3 の `universal`。Prop 8.13 の環版（既存 `TensorCompatibility`）は A7 の後に導来版の系へ置き換える（D15、BR31）。

## 0. 範囲と前提

- 含む：Def 8.2 の animated 版（導来 p 完備な animated R 代数の充満部分 ∞ 圏の上、A4 の離散版はその制限）、Construction 7.6 (5) の相対版
  （S_3 上のテンソル）、Prop 8.13、perfectoid T で T_perfd ≃ T、Cor 8.14、E3 の `universal`。
- 含まない：Prop 8.13 の環版の置き換え（BR31、中身の後）、単体的 S での Cor 8.14（E3 は離散）。
- 前提：A2（`AnimatedAlgebra`、Δ、(5) `derivedPrismaticCohomology_tensor`、sifted 余極限の保存、`discreteToAnimated_fullyFaithful`）、
  A4（Def 8.2、Lemma 8.4、`prismaticPerfectionPrism`、`e3Perfd`・`e3Unit`・`e3H0RingData`）、A5（Prop 8.5 の極限、`perfectionComparisonLeg`、A5-2 の
  離散性の芯と `perfectoidization_semiperfectoid_iso`）、DerivedGeneral（完備化）、既存：`IsPerfectoidization`（`CommutativeAlgebra/IntegralPerfectoid`）、
  `completionRing` の普遍性（Interface.lean:237）、環版 Prop 8.13（`TensorCompatibility`、参照のみ）。

## 1. 原典の項目と形式化の対応

| 原典 | 扱い | Lean の形（§2） | 既存・不足 | 単位 |
| --- | --- | --- | --- | --- |
| Def 8.2（定義域） | 定義（原典の定義域に戻す）：導来 p 完備な animated R 代数の上の Δ_perf・S_perfd。A4 の離散版は制限 | `CompleteAnimatedAlgebra R`、`prismaticPerfectionAnimated`、`perfectoidizationAnimated`、`perfectoidizationAnimated_discrete` | G-A7-1 | A7-1 |
| Constr 7.6 (5) 相対版 | 定理：Δ_{S_1 ⊗̂_{S_3} S_2} ≃ Δ_{S_1} ⊗̂_{Δ_{S_3}} Δ_{S_2} | `derivedPrismaticCohomology_relativeTensor` | A2-4 の (5)、G-A7-2 | A7-1 |
| Prop 8.13 | 定理（原典の形：導来 p 完備な animated S_i） | `perfectoidization_relativeTensor` | G-A7-4 | A7-1 |
| perfectoid の perfd | 定理：T perfectoid ⇒ T → T_perfd は同値 | `perfectoidization_of_perfectoid` | A5-2（R′(T) = T） | A7-2 |
| Cor 8.14 前半 | 定理（S 離散）：S_perfd 離散 ⇒ perfectoid 環 | `perfectoidization_isIntegralPerfectoid_of_discrete` | A4・A5-2 の芯（G-A7-5） | A7-2 |
| Cor 8.14 後半 | 定理：S → S_perfd は perfectoid 環への普遍な写像 | `perfectoidization_isPerfectoidization_of_discrete` | Prop 8.13、G-A7-6 | A7-2 |
| E3 `universal` | 構成（任意の離散 S、S^∧ 経由） | `e3Universal` | D41、`completionRing` の普遍性 | A7-2 |
| D15・BR31 | 記録：環版は導来版の系に（A7 の中身の後） | — | `TensorCompatibility` | 後 |

## 2. 定義の形

### 2.1 Def 8.2 の animated 版（D60）

- `CompleteAnimatedAlgebra R`：`AnimatedAlgebra R`（A2-1、P_Σ(Poly_R)）の充満部分 ∞ 圏で、底の D(R) 対象（G-A7-1 の忘却 `animatedForget`）が
  導来 p 完備なもの。原典 Def 8.2 の "derived p-complete simplicial R-algebra"。
- `prismaticPerfectionAnimated : CompleteAnimatedAlgebra R ⟶ CAlg_A`：A2-2 の `derivedPrismaticCohomology`（AnimatedAlgebra 上、CAlg_A 値）を
  制限し、Frobenius の塔の余極限と (p,d) 完備化（A4-1 と同じ構成を関手の段で）。`perfectoidizationAnimated := ⊗^L_A A/d`。
- 離散版との一致：`discreteToAnimated`（A2-1）は導来 p 完備な離散環を `CompleteAnimatedAlgebra` に送り、`perfectoidizationAnimated ∘ discreteToAnimated`
  は A4-1 の `perfectoidization`（点ごと）・A4-3 の `perfectoidizationFunctor` と一致（定義の展開）。E3 の欄 `e3Perfd` はそのまま。
- 完備化：animated R 代数の導来 p 完備化（G-A7-1）。相対テンソル S_1 ⊗̂^L_{S_3} S_2 は AnimatedAlgebra の押し出し（G-A7-2）の完備化。

### 2.2 Prop 8.13

- 主張：S_1 ← S_3 → S_2（`CompleteAnimatedAlgebra R`）に対し、自然な射 S_{1,perfd} ⊗̂^L_{S_{3,perfd}} S_{2,perfd} → (S_1 ⊗̂^L_{S_3} S_2)_perfd
  （CAlg_R の押し出しの完備化から、perfd の関手性で）は同値。
- 証明：(5) の相対版で Δ_{S_1 ⊗̂_{S_3} S_2} ≃ Δ_{S_1} ⊗̂_{Δ_{S_3}} Δ_{S_2}（G-A7-2：押し出しは bar 構成の sifted 余極限、Δ は sifted 余極限と
  絶対テンソルを保つ）。完全化：colim_φ は φ 両立の相対テンソルと可換（sequential 余極限の対角、G-A7-4）、完備化は対称モノイダルな局所化、
  mod d は (X ⊗̂_Z Y) ⊗ A/d = (X ⊗ A/d) ⊗̂_{Z ⊗ A/d} (Y ⊗ A/d)。
- E3 で使う特別な場合：S_1 = S_2 = S_perfd（離散 perfectoid）、S_3 = S（離散）。主張は原典の形で述べ、証明は一様。

### 2.3 Cor 8.14 と E3 の欄

- `perfectoidization_of_perfectoid (T)`：T perfectoid（R 代数）なら T → T_perfd は同値。A5-2 の `perfectoidization_semiperfectoid_iso` で
  R′(T) = T（T は自分自身の普遍 perfectoid 化）。
- 芯（G-A7-5、A5-2 から切り出す）：S_perfd 離散 ⇒ Δ_{S,perf} 離散（d 進 Nakayama）⇒ 完全 p 完備 δ 環（A4 `prismaticPerfection_h0_perfectDelta`）
  ⇒ 完全 prism（`prismaticPerfectionPrism`）⇒ S_perfd = Δ_perf/d は perfectoid 環（Thm 3.10、`quotient_isIntegralPerfectoid`）。
- 普遍性：S′ perfectoid、S → S′ が与えられたとき：
  - 存在：比較写像の脚 Δ_{S,perf} → B_{S′}（A5-1 `perfectionComparisonLeg`）の mod d が S_perfd → S′（S の下）。
  - 一意性（原典）：g_1, g_2 : S_perfd → S′ が S 上で一致すれば、η := (g_1, g_2) : X := S_perfd ⊗̂^L_S S_perfd → S′。S′ は perfectoid なので
    η は X → X_perfd → S′_perfd ≃ S′ を通り（関手性と `perfectoidization_of_perfectoid`）、X_perfd ≃ S_perfd ⊗̂_{S_perfd} S_perfd ≃ S_perfd
    （Prop 8.13 と (S_perfd)_perfd ≃ S_perfd）。この合成 X → S_perfd は乗法 m（紙 3。**W9-II-23：単位の自然性だけでは出ない**。先に**単位の整合性**
    F(η_S) = η_P（F = perfd、P = S_perfd、G-A7-8）を A5 の極限表示の脚から示す：脚 λ_f : P → T（f : S → T、T perfectoid）で f = η_S の脚 q : P → P を取る。任意の
    f について λ_f 自身が添字圏 Perfd_{S/} の射 (P, η_S) → (T, f) なので錐の可換性から λ_f ∘ q = λ_f、P・T は離散で脚が射を識別するので q = id_P。極限比較の S に
    関する自然性と η_P の可逆性から η_P^{-1} ∘ F(η_S) = q = id_P、よって F(η_S) = η_P。次に Prop 8.13 の比較 F(P) ⊗̂_{F(S)} F(P) → F(X) の二つの脚は F(i_1)・F(i_2)。
    上の一致と η_P の逆で左辺を P ⊗̂_P P ≃ P と同一視し、逆向きを e : F(X) → P とすると、単位の自然性から e ∘ η_X ∘ i_j = e ∘ F(i_j) ∘ η_P = id_P、押し出しの普遍性で
    e ∘ η_X = m。Cor 8.14 の一意性は使っていない）。よって η = g ∘ m、g_1 = η ∘ i_1 = g = g_2。
    離散な環の間の animated／E∞ 代数の射は環準同型（`discreteToAnimated_fullyFaithful`、G-A7-6）。
- `e3Universal (S) (hS : IsDiscrete R (e3Perfd S))`（11-13 追記：drafts の型は `IsTheoryDiscrete`（EInfinity/Perfectoidization/TheoryInterface:39）、D71〜D73）：`IsPerfectoidization p (e3H0RingData.unit.app S)`。S^∧ について Cor 8.14、
  perfectoid 環は p 完備なので S → T は S^∧ → T を一意に通る（`completionRing` の普遍性、Interface.lean:237）、`e3Perfd_of_complete`・
  `e3Unit_of_complete`・`e3H0_of_complete`（A4-3）で欄の射に読み替える。

## 3. 必要な一般論（G-A7）

| # | 内容 | 既存 | 使う箇所 |
| --- | --- | --- | --- |
| G-A7-1 | animated R 代数の底の D(R) 対象（`animatedForget`：Poly → D(R) の sifted 余極限保存延長）、導来 p 完備性、p 完備化（反射的局所化、代数構造と両立）、離散の埋め込みとの整合 | A2-1（埋め込み）、DerivedGeneral/CompletionFunctor（D(R) 側） | Def 8.2 の定義域 |
| G-A7-2 | AnimatedAlgebra の押し出し（相対テンソル）＝bar 構成の幾何学的実現（sifted 余極限、HA 4.4.2.8 の類似）；sifted 余極限と絶対テンソルを保つ関手は相対テンソルを保つ；完備版 | A2-4 の (5)・sifted 余極限 | (5) 相対版 |
| G-A7-3 | perfectoid T ⇒ T_perfd ≃ T | A5-2（R′(T) = T） | Cor 8.14 |
| G-A7-4 | colim_φ・完備化・⊗ A/d が相対テンソルと可換（φ 両立の sequential 余極限の対角、対称モノイダル局所化、cofib(d)） | G-A4-2・G-A2-3・G-A5-3 | Prop 8.13 |
| G-A7-5 | 芯：S_perfd 離散 ⇒ 完全 prism ⇒ perfectoid（A5-2 の `perfectoidization_discrete_of_semiperfectoid` の仮定を「離散」に） | A4・A5-2 | Cor 8.14 前半 |
| G-A7-6 | 押し出しからの射は対の射；離散な対象の間の射は環準同型（π_0 Map = Hom） | A2-1 `discreteToAnimated_fullyFaithful` | Cor 8.14 後半 |
| G-A7-7 | `completionRing` の普遍性（p 完備な標的への射は S^∧ を一意に通る） | 既存（Interface.lean:237） | E3 の欄 |
| G-A7-8 | 単位の整合性（W9-II-23）：P = S_perfd 離散のとき F(η_S) = η_P（A5 の極限の脚 q = id_P と比較の自然性から。一意性の先取りなし） | A5-1 の極限表示 | Cor 8.14 の乗法 m |

## 4. 原典との差

| 番号 | 原典 | 本書 | 評価 |
| --- | --- | --- | --- |
| D60 | Def 8.2 は導来 p 完備な単体的 R 代数の上 | A4 では離散 S で述べた。A7 で原典の定義域（導来 p 完備な animated R 代数の充満部分 ∞ 圏）に戻し、離散版はその制限とする | A4 の D41・A5 の D45 の「離散」は E3 の始域の話で、定義は原典の定義域で置く。Cor 8.14 の証明に animated な S_perfd ⊗̂^L_S S_perfd が要るので必要 |
| D61 | 「perfectoid 環からの写像をもつ」単体的環 | 基底 R を固定し R 代数で述べる | Not 8.1 の設定と同じ。A によらないこと（Prop 8.5 系 2）で一般に戻る |
| D62 | Cor 8.14 は単体的 S | 離散 S（E3 の始域）。非完備 S は S^∧ 経由（D41） | 特別な場合 |
| D15 | Prop 8.13 の環版（既存）は普遍性から直接 | 導来版ができたら環版はその系（BR31）。A7 の中身の後に置き換える | 重複の解消は後 |

## 5. 単位と順序

| 単位 | 内容 | 依存 |
| --- | --- | --- |
| A7-1 | Def 8.2 の animated 版、(5) の相対版、Prop 8.13 | A2、A4、G-A7-1・2・4 |
| A7-2 | `perfectoidization_of_perfectoid`、芯 G-A7-5、Cor 8.14、E3 の `universal` | A7-1、A4-3、A5 |

骨組みは A7-1 → A7-2。A5-2 の該当補題の仮定の書き換え（G-A7-5）は A7-2 で行う。
**配置（W9-II-24、2026-11-03）**：A5 が G-A7-5 と G-A7-1 を使うので、両者を A7-2・A7-1 の普遍性／Prop 8.13 のモジュールに同居させると import が閉じない。
数学的な循環ではなく配置の問題（芯の入力は A4・導来 Nakayama・完全 prism の商だけで、Prop 8.5 や Cor 8.14 後半は不要）。そこで
- `drafts/A7/DiscreteCore.lean`：G-A7-5 の芯（`prismaticPerfection_discrete_of_perfectoidization_discrete`・`perfectoidization_perfectPrism_of_discrete`・
  `perfectoidization_isIntegralPerfectoid_of_discrete`）。A4 と DerivedGeneral だけを import し、A5/SemiperfectoidCase と A7/UniversalProperty が import する。
- `drafts/A7/AnimatedDomain.lean`：G-A7-1（`animatedForget`・`CompleteAnimatedAlgebra`・`animatedCompletion`・`discreteToAnimated_complete`）。A2 と DerivedGeneral
  だけを import し、D45 改訂後の A5/PerfectSiteComparison と A7/AnimatedPerfectoidization が import する。
所有単位は A7 のまま（A7-2・A7-1）。

## 6. 決定事項

決定（2026-11-02、ユーザー）：1〜4 とも推奨どおり。
- 1：Def 8.2 は導来 p 完備な animated R 代数の充満部分 ∞ 圏 `CompleteAnimatedAlgebra R` の上で定義し、A4 の離散版はその制限（D60）。
- 2：Prop 8.13 は原典の形で述べる。
- 3：BR31 は記録し、A7 の中身の後に環版を導来版の系へ置き換える。
- 4：A5-2 の離散性の補題の仮定を「S_perfd が離散」にした芯 G-A7-5 を A7-2 に置き、A5-2 と Cor 8.14 で共有する（宣言の置き場所は独立ファイル `A7/DiscreteCore.lean`、W9-II-24）。

相談した選択肢（記録）：

1. **Def 8.2 の定義域（D60）**：導来 p 完備な animated R 代数の充満部分 ∞ 圏で定義し、A4 の離散版をその制限にする（推奨。原典の定義域そのもの。
   Cor 8.14 の証明に animated な対象 S_perfd ⊗̂^L_S S_perfd の perfd が要る）／離散のまま、必要なテンソルの perfd だけ別に定義する（ad hoc、非推奨）。
2. **Prop 8.13 の述べ方**：原典の形（任意の導来 p 完備な animated S_1 ← S_3 → S_2）で述べる（推奨。証明は (5) から一様で、特別な場合に絞っても
   短くならない）／E3 で使う場合（S_1 = S_2 = S_perfd、S_3 = S、離散）だけ。
3. **BR31（環版を導来版の系に）**：記録し、A7 の中身ができた後に置き換える（推奨）／今は触れない。
4. **A5-2 の芯の切り出し（G-A7-5）**：A5-2 の離散性の補題の仮定を「S_perfd が離散」にして Cor 8.14 と共有する（推奨）／A7 で別に書く。

## 7. 紙で確かめる項目

1. 押し出し（相対テンソル）が bar 構成の sifted 余極限であること、Δ がそれを保つこと（G-A7-2）。
2. colim_φ と相対テンソルの可換性（φ の捻りの扱い。Frobenius の塔の対角）。
3. Cor 8.14：X → X_perfd と Prop 8.13 の同値の合成が乗法 m に一致すること（**単位の自然性だけでは不足**、W9-II-23：G-A7-8 の単位の整合性 F(η_S) = η_P を A5 の極限の脚から先に示す）。
4. 一意性の議論を π_0 Map で行ってよいこと（離散な標的）。
5. E3 の欄：S^∧ 経由の読み替え（`completionRing` の普遍性と A4-3 の `_of_complete` 三つ）。
6. A4 の離散版 Def 8.2 と animated 版の一致（`discreteToAnimated` の像が完備であること、完備化の整合）。

W9 続き 6（2026-11-03）：1〜6 すべて紙で ○（3 は G-A7-8 を補って）。補記：6 では animated p 完備化を単体的可換環としての導来 mod p^n の逆極限で構成できる
（π_0 の商の遷移が全射なので lim¹ は現れず animated 圏に留まる；底の加群で完備性を判定し、完備対象への反射という普遍性を使う）ことを G-A7-1 に記す。
導来 p 完備な**離散** S では底の加群が S 自身なので埋め込みは `CompleteAnimatedAlgebra` に入り A4 の版と一致するが、一般の離散 S の animated 完備化は高次ホモトピーを
もち得るので、その場合まで離散との一致は主張しない。4 では「animated な連結対象から離散標的への Map が 0 切り捨てで Hom(π_0 X, T)」を使い、非連結な一般の E∞ 始域には
拡張しない。
