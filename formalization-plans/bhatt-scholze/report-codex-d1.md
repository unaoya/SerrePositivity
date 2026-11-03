# BS-D1 報告

## 第1部：A6/ArcSite の途中（指示書 §3 による停止）

基準：main `e743b6a57`。開始時 HEAD は `e93809f7f`、作業ツリー・index は空。
基準以降のコミットは変更していない。対象 ArcSite の開始時の内容は基準と同じだった。
指示書を最後まで読み、design-status §2 (A)、a6-design §2.1・§2.2・§4、RootAdjunction・PerfectoidFiniteProduct の記法を参照した。

### 結果

**停止点1（ArcSite 全体の完了）には未到達。** `isSheaf_arc_iff_cech` で、docstring が指す既存 `S3.CechNerveData` の積の形と必要な相対 Čech 項の形が一致しないことを確認した。
指示書 §3 の「既存の名前の形が docstring の前提と合わない」に従い、この宣言は `True` のまま残し、以降の G-A6-11・G-A6-3 等には進んでいない。
新しい数学的主張や仮の公理を導入して補うことはしていない。

変更は `drafts/A6/ArcSite.lean` と本報告だけ。ビルド・Lean 実行は一切していない。

### 具体化した範囲

| 既存宣言 | 今回の型・定義の具体化 |
| --- | --- |
| `AffCompl` | `CommRingCat.{u}` 内で、`IsModuleComplete S (p : S) (ModuleCat.of S S)` と `Cardinal.mk S ≤ κ` を満たす充満部分圏の `SmallModel`。本質的小ささは理由つき sorry の instance とした。 |
| `AffPerfd` | 上の小さい圏内で、忘却先の環が `IsIntegralPerfectoid` を満たす対象の充満部分圏。既に Type u なのでさらに SmallModel を重ねない。 |
| 上二つの Category instance | `SmallModel` と `ObjectProperty.FullSubcategory` の既存 instance を利用。 |
| `affPerfdInclusion` | 上の対象条件の `ObjectProperty.ι`。対象・射の向きは環側。 |
| `arcTopology` | 有限族 R→B_i を忘却関手で環準同型へ移し、`IsArcCoverFamily` なら opposite の `Sieve.generate (Presieve.ofArrows …)` を含む位相の sInf。 |
| `arcTopologyPerfd` | `(affPerfdInclusion p κ).op.inducedTopology (arcTopology p κ)`。この定義自体には cover-dense の仮定は不要。 |
| `isArcCoverFamily_baseChange` | p 完備な R・R′・B_i、f_i・g と被覆性を明示。g と f_i に沿う代数構造を letI で入れ、`completionRing p (CommRingCat.of (B_i ⊗[R] R′))` への右包含と完備化単位の合成が arc 被覆、という型。 |
| `isArcCoverFamily_comp` | 有限族 f_i と各有限族 g_ij の被覆性から、Sigma 添字の合成族 g_ij∘f_i の被覆性。 |
| `isArcCoverFamily_prod_iff` | 元の有限族の被覆性と、`RingHom.pi f` を一点族とした被覆性の同値。空添字も除外していない。 |

計 **既存の名前つき宣言8件＋Category instance 2件**を具体化した。既存の True 宣言を置き換えたのは coverage の三件。
補助として `affComplProperty`・`AffComplLarge`・`affComplLarge_essentiallySmall`・`affComplForget`・`affPerfdProperty` の5件を同じファイルに追加した。
定理と本質的小ささの証明はすべて `sorry -- 理由`。圏構造の既存 instance の利用や定義の展開以外の証明は書いていない。
`IsArcCoverFamily` の既存の定義、試験付値環の範囲、忠実平坦性は変えていない。

底変換の完備テンソルは一般の p 完備環を扱うため、perfectoid 性を仮定する定理へ無理に適用せず、通常の相対テンソルの完備化 H⁰ と明示した。
本体 `completedTensorH0PrincipalRingEquiv` はこの H⁰ と既存の導来完備テンソルの H⁰ を比較し、通常のテンソルの p ねじれなしを要求しない。
対象の完備性を指定する引数は元の site の範囲の明示であり、perfectoid という強い仮定は追加していない。

### 停止理由：相対 Čech データの型

| 指摘 | 内容 |
| --- | --- |
| D1-01 | `drafts/Sheaves/CechConerveLimit.lean` の `CechNerveData (U : 𝒟)` は、各 n で `IsLimit (Fan.mk … (proj n))` を要求する。これは圏 𝒟 内の絶対積 U^{n+1}。一方、`ArcSite.isSheaf_arc_iff_cech` の docstring が要求する S⊗̂_R S は、被覆の基底 R を固定した相対テンソル。 |

これは単なる名前の未発見ではなく、既存構造の引数と普遍性の形の違いである。
例えば R=S=F_p[t]、被覆を恒等射とすると、相対 Čech の第1項は S⊗_R S=S。
一方、全 p 完備環の圏の絶対余積は S⊗̂_{ℤ_p}S=F_p[t₁,t₂] であり、同じ対象ではない（標数 p なのでこの計算では p 完備化は変化を与えない）。
従って `CechNerveData (op S)` をそのまま全 arc site の中で渡す型は書かなかった。

**推奨する具体化の方向**：個々の射 f:op S→op R が生成する sieve の圏を使う。
C=(AffCompl p κ)ᵒᵖ、Q=`Sieve.generate (Presieve.ofArrows … f)`、𝒟=`sieveCategory Q` とし、U は f 自身の対象とする。
Q の射は f を経由するので U は 𝒟 で弱終となり、𝒟 内の U の積は基底 op R 上の相対積を表す。
この 𝒟 で `CechNerveData U` を供給し、前層を sieve の圏へ制限して S3 を適用すれば、個々の生成 sieve に対する降下と相対 Čech の Tot の比較を述べられる。
別案は `Over (op R)`（環側の `Under R` の opposite）で相対 Čech データを作り、生成 sieve との比較を明示する方法である。ただし全スライスで U が弱終とは限らず、S3 の弱終性を省略してはならない。

合わせて次の二つの主張を区別する必要がある。

1. docstring の「**個々の単射被覆が生成する sieve** の層条件 ⇔ 相対 Čech の Tot の条件」。推奨はこれをまず具体化すること。
2. 名前からも読める「**位相全体の層であること** ⇔ 被覆ごとの Čech 条件」。これは S1 の生成系の補題、有限族からの帰着、適用する site・前層を明記する別の接続が要る。a6-design §2.2 の単射への帰着は perfectoid の構造前層 O について書かれているので、全 affCompl の任意の前層へ無断で一般化しない。

この区別と相対データの供給を未確定のまま別の命題で True を埋めることを避け、指示通り停止した。S3 や設計書は編集していない。

### 名前を照合した箇所（ソースを読むだけ）

| 名前 | 確認先・形 |
| --- | --- |
| `EssentiallySmall`・`SmallModel`・`equivSmallModel` | Mathlib `CategoryTheory/EssentiallySmall.lean:44,56,66`。EssentiallySmall.{u} の証拠から Type u の模型。equiv の inverse は模型→元の圏。 |
| `ObjectProperty.FullSubcategory`・`ObjectProperty.ι` | Mathlib `CategoryTheory/ObjectProperty/FullSubcategory.lean:39,59`。対象は obj/property、射と Category は既存の誘導圏。 |
| `Functor.inducedTopology` | Mathlib `CategoryTheory/Sites/InducedTopology.lean:50`。任意の関手に定義される。DenseSubsite の比較定理に付く条件とは別。 |
| `Presieve.ofArrows`・`Sieve.generate` | Mathlib `CategoryTheory/Sites/Sieves/{Presieve,Basic}.lean`。opposite の対象 op R へ向かう射の族を指定。 |
| `IsModuleComplete` | 本体 `HomologicalAlgebra/DerivedCompletion/Module.lean:26`。環 R は明示引数であり `IsModuleComplete R f M` と書く。指示書の旧 HA パスは現行の名前を rg で確認した。 |
| `completionRing`・`completionUnit`・`completion_existsUnique` | 本体 `BhattScholze/Perfectoidization/Derived/Interface.lean:206,211,235`。引数・値は CommRingCat、単位の `.hom` を環準同型として使う。 |
| `completedTensorH0PrincipalRingEquiv` | 本体 `HomologicalAlgebra/DerivedCompletion/CompletedTensorH0RingTransport.lean:25`。一般の環の相対テンソルの完備化 H⁰ との比較。 |
| `Algebra.TensorProduct.includeRight` | Mathlib `RingTheory/TensorProduct/Basic.lean:277`。R′→ₐ[R]B_i⊗[R]R′。 |
| `RingHom.pi` | Mathlib `Algebra/Ring/Pi.lean:157`。有限族から積への環準同型。 |
| `CechNerveData`・`isLimitCone_iff_restrict_cech` | drafts/Sheaves/CechConerveLimit。絶対積の Fan、弱終性、前層上の錐の制限の同値。今回の停止点。 |

仮の未発見名を新しく使った箇所は **0件**。ファイル内の `要確認` は **3箇所**（停止理由1、未着手の R₀ の既存例1、付値延長1）で、10超ではない。
本質的小ささの証明が sorry であることは未発見名ではなく、設計通りに今後証明する補題である。

### 未着手と検証

- `isSheaf_arc_iff_cech` は True のまま。以降の perfectoidBaseRing・baseExtension とその性質、付値環拡大、exists_baseExtension_lift、exists_perfectoid_arcCover、cover-dense は元のまま。
- ArcSheafProperty、Stratification、A0 の作業には進んでいない。停止点1完了とは報告しない。
- ビルド・lake env lean・Lean の型検査は未実施。具体化した型のコンパイル成功は主張しない。
- ソース上の向き・引数・宇宙を照合し、`git diff --check`、変更ファイルの限定、停止箇所以降が未変更であることを確認する。コミットは ArcSite と本報告だけに限定する。

## 第2部（停止点1の続き、D1-02 で途中停止）

基準・開始時 HEAD は main `3628dc9ca`。開始時の作業ツリーと index は空だった。
D1-01 の決定に従い、`drafts/A6/ArcSite.lean` に (1) と一点被覆の `arcCoverage` を具体化した。
**(2) の `arcTopology_eq_toGrothendieck` には反例がある。** 指示書 §3 の停止規則を適用し、基準にあった等式の `by sorry` と `isSheaf_arc_iff_cech` の `True` を残した。G-A6-11・G-A6-3 以降は未着手で、停止点1には未到達である。

### D1-01 の具体化

| 宣言 | 結果 |
| --- | --- |
| `IsSingletonArcCover`・`arcSinglePresieve`・`arcSingleSieve` | 環側の f を一点族の `IsArcCoverFamily` に渡し、site 側で `f.op` の Unit 添字の presieve と生成 sieve Q を作る。「単射被覆」は指示にある一点族の意味で用いた。 |
| `arcSieveGenerator`・`arcSieveGenerator_weaklyTerminal` | U の対象を `Over.mk f.op` と `Sieve.le_generate` による所属証拠で指定した。Q の任意の射は f.op を経由するので U は `sieveCategory Q` で弱終である。 |
| `arcSieveCechData` | `CechNerveData U` の周囲の圏は `sieveCategory Q`。含まれる各 Fan の極限性は op R 上の相対積の普遍性を表す。第 n 項は S の R 上の (n+1) 重テンソルの `completionRing` で実現でき、n+1≥1 なので射影を通じて Q の対象になる。 |
| `isSheaf_generateSieve_iff_cech` | 任意の E 値前層 F と一点 arc 被覆 f に対し、`IsLimitCone (restrictionCone F Q)` と、その同じ錐を `cechShape (arcSieveCechData … f)` に制限した錐の極限性を同値とした。S3 に渡す前層は `restriction F Q`。 |
| `arcCoverage` | 被覆 presieve を一点 arc 被覆 f の `arcSinglePresieve` と等しいものとした。`Coverage.pullback` の証明穴には、相対完備テンソルへの二脚と既存の底変換補題から `FactorsThruAlong` を供給する理由を付した。 |

相対完備テンソル冪と底変換を小さい模型に置く箇所で、設計 §2.1 の濃度条件を `Fact ((κ + ℵ₀)^ℵ₀ ≤ κ)` と明示した。許容される無限の κ で κ^{ℵ₀}=κ なら満たす。S1 の `sieveCategory`・`restrictionCone`、S3 の `IsWeaklyTerminal`・`CechNerveData`・`cechShape`・`isLimitCone_iff_restrict_cech`、本体 `Core/LimitConeExtension` の `restrictJoinCone`、Mathlib の `Presieve.ofArrows.mk`・`Sieve.le_generate`・`Coverage.coverings`・`Coverage.pullback` をソースで照合した。仮の未発見名は追加していない。

### D1-02　有限族の位相と一点族の位相が異なる

`isArcCoverFamily_prod_iff` が比較するのは付値環への射の持ち上げ条件である。R→B_i は R→∏B_i を経由するので、有限族の生成 sieve は積への一射の生成 sieve に含まれる。この包含から、**大きい sieve の被覆性を小さい sieve へ移すことはできない**。

具体的に k=𝔽_p、R=k×k とし、二つの射影 R→k を取る。有限環なので許容する κ の範囲に入り、p=0 なので導来 p 完備である。

1. 二射の族は arc 被覆である。整域である試験付値環では (1,0) の像が 0 か 1 になり、R からの射はどちらかの射影を通る。拡大は恒等射でよい。積への射 R→k×k も恒等射なので一点被覆である。
2. 二射が生成する sieve の射 R→T は、必ず片方の射影を経由する。その射は単独では arc 被覆になれない。反対側の射影で試験環 V=k[[t]] へ写すと、ある冪等元の像が T では 0、V では 1 になる。V は p 進完備な階数1の付値環で、忠実平坦な拡大 W に移しても 0 と 1 は一致しない。
3. 一点 arc 被覆は恒等射を含み、合成と底変換で閉じる。この場合「一点 arc 被覆の射を含む sieve」は Grothendieck 位相をなす。引き戻しは底変換、局所性は二段の一点被覆の合成から従う。この位相は一点 coverage の生成位相と等しい。従って二射の sieve は `arcTopology` では被覆、`arcCoverage.toGrothendieck` では非被覆である。差は空族を除いても生じる。

任意の E 値前層に対する (2) 自体にも簡単な反例がある。E を集合の圏の nerve とし、二点集合 K に値を取る定数前層 F を考える。どの一点 Čech 図式も K の定数図式となり、Δ は可縮なので Tot は K。従って F はすべての一点 Čech 条件を満たす。他方、零環から非零の試験付値環への単位的環準同型は存在しない。このため零環上の**空の有限族**は `IsArcCoverFamily` を満たす。`arcTopology` の層にはその空図式の極限 F(0)≃* が必要であり、F(0)=K はこの条件を満たさない。

**再開に必要な設計判断**は、全ての前層を対象とする層判定に有限族の降下をどう残すかである。現在の `arcTopology` と任意の F を保つなら、finite-family coverage を S1 に渡し、各有限族の Čech 図式（各次数で交叉項ごとの F の値の積）で判定する形が取れる。積への一射を使うなら、F が有限積環を値の圏の積に送る条件（空積を含む）と、その比較を明示する必要がある。D1-01 の (1) はどちらでも使える。この判断は記録のみとし、設計書・(2) の主張には適用していない。

### 確認範囲

今回の編集は `drafts/A6/ArcSite.lean` と本報告への追記のみ。G-A6-11 の節以降は基準と同じで、ArcSheafProperty・Stratification・A0 には進んでいない。ArcSite の `要確認` は3箇所（D1-02 と、従前の R₀ の例・付値延長）。文字列上の比較と `git diff --check` で確認し、Lean 実行・ビルド・型検査は行っていない。

## 第3部（停止点1完了）

基準・開始時 HEAD は main `f1947a44c`。作業開始時の `git status --short` は空だった。**停止点1に到達した。** ArcSite 内の最後の7件の `True` を具体化し、D1-02 の三定義と G-A6-11・G-A6-3 から cover-dense までの主張・証明方針を記入した。証明穴には理由を添えた。今回の確認はソース上の型と依存の照合までで、Lean の実行・型検査・ビルドは行っていない。

### D1-02 の反映

| 宣言 | 書いた内容 |
| --- | --- |
| `arcFamilyCoverage` | 有限添字、環の族、環側の射、その `IsArcCoverFamily` を指定し、opposite 側でその `Presieve.ofArrows` が被覆 presieve に等しいことを要求した。底変換の証明穴には `isArcCoverFamily_baseChange` と完備テンソルの二脚を使う。 |
| `extensiveCoverage` | `X.unop` からの射影が `Fan.mk` の極限錐をなす有限族を取った。積の代表を一つ選ぶことへの依存がなく、空族では環側の終対象（零環）が現れる。底変換では直交冪等元による有限積分解を使う。 |
| `isArcCoverFamily_projections` | 任意の有限環族について `Pi.evalRingHom` の族が `IsArcCoverFamily` を満たす形にした。付値環への射は一因子を通り、空積から非零付値環への単位的射は存在しない。 |
| `PreservesFiniteRingProducts` | 環側の任意の有限積錐を `opOp` で前層の定義域へ運び、`nerveCone` と宇宙の持ち上げを経て F と合成した錐が `IsLimitCone` になること。空添字なら F(0) の終対象性である。 |

有限族に対する位相は `arcTopology_eq_toGrothendieck_family`、一点被覆・有限積射影への分解は `arcTopology_eq_sup` に対応する。`k × k → k` の二射の族は射影族として新しい coverage に入る。零環上の空族も入るので、前報の二点集合の定数前層は有限積保存条件で除かれる。任意の E 値前層の判定では、S1-E `isSheaf_extensive_iff_preservesFiniteProducts` の証明は基盤待ちのままである。

### G-A6-11・G-A6-3 と Lemma 8.8

| 宣言 | 書いた内容 |
| --- | --- |
| `perfectoidBaseRing`・`perfectoidBaseRoot` | `PadicInt p` を入力環と同じ宇宙へ持ち上げ、可算変数の多項式環に `X₀ − p` と全 `X_{n+1}^p − X_n` の関係を課して `completionRing` を取った。第 n 根は `X_n` の商と完備化単位による像。係数の射を通して `ℤ_p` 代数構造を入れた。perfectoid 性は a6-design §8.8 の完全 prism の商との比較を証明穴に記した。 |
| `baseExtension`・`baseExtensionUnit` | `hS : IsModuleComplete S (p : S) (ModuleCat.of S S)` から標準の `arcPadicIntMap` を供給し、その作用による `S ⊗[PadicInt p] R₀` の完備化 H⁰ を S₀ とした。R₀ 代数構造は右の脚、S→S₀ は左の脚に、それぞれ同じ完備化単位を合成する。環構造は両方とも `completionRing` のものを使う。 |
| `baseExtension_cardinal_le`・`baseExtensionUnit_pCompletelyFaithfullyFlat` | `#S₀ ≤ (#S + ℵ₀)^ℵ₀`。後者は指定した S→S₀ から `letI` で作用を入れ、`IsCompletelyFaithfullyFlat (Ideal.span {(p : S)}) S₀` と述べた。完備忠実平坦性は記録用。 |
| `exists_perfectoid_valuation_extension`・`perfectoidBaseRing_toValuationExtension` | 同じ W 上に階数1・p 完備・perfectoid 性、忠実平坦な e と `ρ 0 = p`、`ρ (n+1)^p = ρ n` を持つ列を返す。R₀→W は指定根をその ρ に送る。`ValuationRing` の整域 instance は既存の `isDomain` 欄を明示した。V・W の濃度には κ を課さない。 |
| `exists_baseExtension_lift` | 補助の `_of_map` は、選んだ e と b:R₀→W を固定して `l:S₀→W` が `e ∘ k` と b の両方に制限されることを述べる。元の宣言は `k:S→V` から W・e・l を同時に返す。 |
| `exists_perfectoid_arcCover` | `g:S₀→T`、T の perfectoid 性と濃度上限、および `g ∘ baseExtensionUnit` が一点族として arc 被覆であることを返す。証明では R₀ 上の `rootClosure` を S₀ に施し、その semiperfectoid 性と Cor 7.3 で T を取る。試験射を持ち上げる際は、上で選んだ W に `rootClosure_extends` と普遍環の普遍性で延ばす。 |
| `affPerfdInclusion_isCoverDense` | 定義済みの包含の opposite に `Functor.isCoverDense_of_generate_singleton_functor_π_mem` を適用するところまで書いた。`#S ≤ κ` と cutoff 条件から `#T ≤ κ` を得て小さい模型に移し、一点被覆の生成 sieve の所属を示すのが残る証明穴である。 |

`baseExtension` に完備性を明示したのは、一般の環に対する `ℤ_p` 作用を仮定せず、設計が対象とする p 完備環 S 自身から作用を取るためである。`arcPadicIntMap` の構成は整数の完備化からの一意延長を使う証明予定の補助定義。`affPerfdInclusion_isCoverDense` の κ の仮定は、相対 Čech と coverage が既に使う `Fact ((κ + ℵ₀)^ℵ₀ ≤ κ)` と揃えた。

### 照合・引き継ぎ

- Mathlib の `Coverage`、`Fan.mk`・`IsLimit`、`opOp`・`Functor.mapCone`、`Pi.evalRingHom`、`PadicInt`・`ULift.ringEquiv`、`MvPolynomial.X`・`C`、テンソルの `includeLeftRingHom`・`includeRight`、`ValuationRing`、`Functor.isCoverDense_of_generate_singleton_functor_π_mem` の向きと引数をソースで確認した。
- 本体の `F1B.nerveCone`、`JoinCone.ulift`、`completionRing`・`completionUnit`・`completion_existsUnique`、`IsModuleComplete`、`IsCompletelyFaithfullyFlat` と既存 Cor 7.3 の入口を照合した。名前の新規仮置きは0件。ArcSite の `要確認` は付値の整拡大への延長の実装名についての既存1件である。
- 今回指定の ArcSite に `True` または `Type u := sorry` のままの宣言は残っていない。S1-E・G-A6-3・G-A6-11 等の証明は予定の `sorry` として残る。`git diff --check` と変更パスを確認し、報告は既存本文に追記した。
- 次の停止点2では `ArcSheafProperty.lean` の対象宣言に加え、O（CAlg_ℤ 値）と Hom(T, −)（集合値）の有限積保存を一件ずつ明示する。Prop 8.10 の構造前層が affPerfd_κ 上にあることに合わせ、積錐の判定の定義域を揃えて使う。

## 第4部（停止点2の途中、G-A6-4 の零環）

基準・開始時 HEAD は main `734b702ba`。開始時の作業ツリー・index は空。**停止点2には未到達。** 三引用と G-A6-1 の結論を具体化した後、`completedTensor_tilt` に必要な `PreTilt` の環構造の仮定が設計の入力を覆わないことを確認した。指示書 §3 に従い、同宣言は `True` のまま停止した。

### 今回具体化した主張

| 宣言 | 入力・結論 |
| --- | --- |
| `IsVCoverFamily`・`IsArcCoverFamilyCharP` | 通常の付値環の試験射を、同じ W 上の忠実平坦な e と持ち上げ l の等式で述べた。v は全階数、標数 p の arc は V・W とも Krull 次元 ≤1（体を含む）。基底・係数の標数は適用側の F_p 代数で与える。 |
| `cech_exact_of_vCover_perfect`（1a） | 基準の宣言は入力が既に具体的で、**結論だけが `True`** だった。同じ引用・同じ仮定の下で `AugmentedRingCechExact (affineFamilyCech B f)` に直した。有限族の積への射の相対 Čech 余脈体を作り、加法群への忘却、交代余面写像の微分を使う。増大射の単射性、第0項の核・像の一致、全正次数の完全性を含む。 |
| `arcSheaf_of_vSheaf_of_valuationSquares`（1b） | `A_R (ULift (ZMod p))` の nerve から `derivedInfinityCategory (ULift ℤ)` への共変 F、ℵ₀-filtered 余極限の保存、全 A における `IsCoconnectiveAt … 0` を入力にした。結論は arc 層 ⇔（v 層かつ全試験四角形が cartesian）。V は F_p 代数・付値整域で `IsAlgClosed (FractionRing V)`、P は素イデアル。`ordinarySquare` で標準の局所化・商・剰余体への二射を指定し、F で送った四角形に `IsPullbackSquare` を課した。 |
| `valuationRing_milnorSquare`・`valuationRing_milnorSquare_perfect`（1c） | `MilnorShortExact P` は V→V_P×V/P の対角射の単射性、中央の `Function.Exact`、κ(P) への差写像の全射性。左の写像は局所化と商、右は V_P の剰余から V/P の剰余を引く。一般版は証明予定、標数 p の完全付値環版は暫定引用。docstring の核の説明も、V_P→κ(P) の核が V の P の像であるという計算に揃えた。 |
| `cech_exact_of_arcCover_perfect` | 上と同じ有限族・増大 Čech 複体について、完全環上の arc 被覆性を入力とする完全性。1a・1b・1c から導く証明の穴に理由を付した。 |

1b では、任意の F の有限族降下を、その族が生成する sieve の指定錐で表した。添字は、A→D がいずれかの A→B_i を経由するような `Under A` の充満部分圏である。空族なら空図式になる。`AsSmall.{u+1}` を使って通常の錐を `F1B.nerveCone` の宇宙に揃え、元の関手 F へ後合成した。試験環 V・W に κ の上限を課していない。整数係数の宇宙には `ULift.{u} ℤ` を選んだ。Prop 8.10 の構造前層 O の宣言にはまだ達していない。

### D1-03　完備テンソルの零環の分岐

`IsIntegralPerfectoid O p` は零環を `Subsingleton O` として含む。本体 `Perfectoidization/CompletedTensor.lean:187` の `integralPerfectoid_completedTensor_pure_and_h0` はこの一般性を保つ。一方、Mathlib `RingTheory/Perfection.lean:634` の `PreTilt O p` は型として定義されるが、同ファイル `:639`〜`:650` の `CommRing`・`CharP`・`PerfectRing` instance が使うのは `[Fact (¬ IsUnit (p : O))]` である。基準の本体・Mathlib を検索した範囲で、零環を含む tilt の環構造と射を一括して与える既存の入口は見つからなかった。

この仮定は S・S′ がともに非零でも問題になる。k=𝔽_p、R=k×k、S と S′ をそれぞれ異なる射影による k とする。この三環は非零の perfectoid 環である。冪等元 (1,0) の作用は S で 1、S′ で 0 なので S⊗_R S′=0。両因子は R の直和因子で射影的であり、高次 Tor も零。したがって導来完備テンソルの H⁰ は零環となる。この環では p=0=1 が単元なので、既存 instance に渡す `¬ IsUnit p` は偽である。原典の比較同型への反例ではなく、現在の Lean の型の前提への反例である。

**再開案**：零環を含む perfectoid 環の全域で環値の tilt とその射を指定する。非零の場合は既存 `PreTilt` の環構造を使い、零環の場合は一元環とし、その場合を跨ぐ射も指定する。その上で G-A6-4 は一般の底変換に対する環同型として述べられる。別案は零環の分岐と非零の場合の比較を別補題にし、両者から一般版を組み立てること。S・S′・完備テンソルすべてを非零と仮定するだけでは上の例が抜ける。どちらの案も今回のコードには適用していない。

### 確認と残件

- Mathlib の `Arrow.augmentedCechConerve`、`alternatingCofaceMapComplex`、`Function.Exact`、`AsSmall.up/down`、`Localization.AtPrime`・`Ideal.ResidueField`・`IsLocalRing.residue` をソースで確認した。本体では `ordinarySquare`・`IsPullbackSquare`・`PreservesSmallKappaFilteredColimits` と完備テンソルの入口を、drafts では `IsCoconnectiveAt` と `ringPresheafToCAlg` の型を読んだ。1b の二つの剰余の合成と sieve の錐の自然性には理由つきの証明穴を置いた。
- `completedTensor_tilt` 以降の主張は基準のまま。G-A6-5〜7、Prop 8.10、O と Hom(T, −) の有限積保存、Cor 8.11 の記録は再開後の対象である。ArcSheafProperty 内の `要確認` は D1-03 の1件。
- 今回の編集は ArcSheafProperty と本報告への追記だけ。ビルド・Lean 実行・型検査は行っていない。

## 第5部（停止点2完了）

開始時の HEAD は main `7fff2bcc6`。作業ツリー・index は空だった。`drafts/A6/ArcSheafProperty.lean` に残っていた10件の `True` を具体化し、O と Hom の有限積保存を一件ずつ加えた。今回の具体化は定理の型と定義までで、証明は理由つきの `sorry` である。

| 宣言 | 型にした内容 |
| --- | --- |
| `witt_exact_of_perfect`・`modD_exact_of_regular`（G-A6-5） | 増大項と全次数で p = 0 かつ p 乗が全単射な環の図式 B に対し、B の増大複体が完全なら全ての有限長 W_n(B) と W(B) の増大複体が完全。Witt 関手は交代和を作る前に各環と各構造射に作用する。d は増大項の Witt 元で、第1 Witt 係数を単元とし、増大項の d と全ての構造射による像に正則性を課した。商の図式は各構造射で同じ d を送って割る。証明予定は V の短完全列、全射な切断塔の Rlim、d の乗法の cofiber の順。 |
| `untilt_rankOneValuationRing`・`tilt_rankOneValuationRing`（G-A6-6） | 完全 a 進完備な階数1付値環 V の distinguished 元 d（a = d.coeff 0）から U = W(V)/(d) の perfectoid 性、階数1と p 完備性、標準係数射を持ち上げた V ≃ U^♭ を述べた。a = 0 なら U ≃ V。逆向きは perfectoid な p 完備階数1付値環 W について W^♭ の整域性・付値環性・階数1・完全性。tilt の値は `tiltRing`。 |
| `tilt_arcCoverFamily` | 一点 arc 被覆 f から、二成分 `tiltMap p f` と a による局所化の標準射の `IsArcCoverFamilyCharP` を述べた。単元なら局所化、階数1の非零非単元なら V→V̂ の忠実平坦性、階数1で零なら V 自身の untilt、階数0の非単元なら完全体から完全な階数1付値環への忠実平坦な拡大を使う。後二つの階数を混同しないよう完備化と体の拡大に別の補題を置いた。 |
| `cech_completion_kills_inverted`（G-A6-7） | A→B × A[1/a] の相対増大複体の完全性から、A→B の相対余脈体を各次数で導来 a 進完備化した H⁰ の増大複体の完全性を得る。同時に、a が可逆となる任意の A→T について完備化の Koszul 複体の全次数のホモロジーが零。新しい完備化関手の射は `principalCompletionUnitRingHom` を通る一意延長。 |
| `cech_exact_of_arcCover_perfectoid`（Prop 8.10） | 一点 arc 被覆 R→S の `Arrow.augmentedCechConerve` を `ringCompletionFunctor p` で次数ごとに完備化し、`AugmentedRingCechExact` を課した。第1次の交叉項は R 上の完備テンソルで、増大項と第0項は完備化単位で R, S に戻る。被覆の仮定に単射性を追加していない。 |
| O・Hom の有限積保存と層性 | `PreservesFiniteRingProductsOnPerfd` は AffPerfd の錐を包含で AffCompl に送り、その像が有限積なら前層で送った錐が極限であること。G-A6-12 で空積を含む有限積はこの制限に残る。O は標準射 ULift ℤ→T を備えた図式を `ringPresheafToCAlg` に渡した。結論は `Sheaves.IsSheaf (arcTopologyPerfd p κ) …`。Hom(T,−) は集合値の通常の関手で、結論は `Presieve.IsSheaf`。誘導位相では ArcSite の二つの生成系を包含に沿って制限し、積保存と一点被覆の相対 Čech 条件を別々に使う。 |
| `perfectoidization_eq_arcCohomology`（Cor 8.11、記録） | S は AffCompl の対象とし、S→T を対象とする `StructuredArrow S (affPerfdInclusion p κ)` の opposite 上に slice 位相を置いた。R→S→T による CAlg_R 値の O に S2 の `derivedGlobalSections` を適用。p 完備な S で S_perfd を表す A5 の `perfectoidizationCone` の頂点から、この RΓ への可逆な辺を結論にした。比較に使うのは A5 の `perfectoidization_isLimit` の κ 版。κ の閉性と基底の濃度上限、S2 の層化・presentability のデータを明示した。 |

### 要確認・設計との照合

- 未発見名の仮置き、ArcSheafProperty 内の `要確認`、対象の `: True := …` はいずれも0件。Mathlib の `CosimplicialObject.Augmented.whiskeringObj`、`TruncatedWittVector.mk`、`Ideal.quotientMap`、`StructuredArrow.proj`、`Presieve.IsSheaf` の定義を照合した。本体の `wittDeltaStructure_isDistinguished_iff`、`wittQuotientTiltMap`、一元の Koszul 完備化・単位・普遍性、`ringCompletionFunctor`、drafts の A5 の錐、S1・S2・S4 の定義も照合した。
- 零環を含む箇所では `CharP B p` の代わりに `(p : B) = 0` と `PerfectRing B p` を使った。`CharP` は n の像が零であることと p∣n の同値を全ての n で要求し、零環で n = 1 とすると成立しない。G-A6-1 を適用するのは設計 §3.1(3) の積 B = S^♭ × R^♭[1/a] への一点族である。a = 0 のとき局所化因子自身に `CharP` は要求しない。基底が零なら図式全体が零。積が零ならその一点被覆の試験射がない場合を別に扱う（非零の完全 F_p 代数には素点の剰余体への試験射がある）。
- §3 の停止を要する新しい設計差は見つからなかった。Prop 8.10 の一次的な結論には docstring に合わせて増大交代和複体の完全性を選んだ。Cor 8.11 は affPerfd_κ/S の上だけで述べた。A5 の極限性や S1 の生成系の補題など、証明で使う drafts 側の入力は未証明である。
- 検査は宣言・依存名のソース照合、対象の仮置きの検索、変更パスの確認、`git diff --check`。ビルド・Lean 実行・型検査はしていない。編集は ArcSheafProperty と本報告への追記だけ。停止点3（A8）以降は未着手。

## 第6部（停止点3の途中、標数 p の判定の核）

開始時の HEAD は main `a9dc3a164`、作業ツリー・index は空。G-A8-4 の定義と三つの性質を具体化した。`isUniversalHomeomorphism_iff_charP` で「核が冪零」の二つの読みが同値でないため、指示書 §3 に従いその宣言は `True` のまま残した。停止点3には未到達。

### 具体化した宣言

| 宣言 | 入力と結論 |
| --- | --- |
| `IsUniversalHomeomorphism` | 整性は既存の `f.IsIntegral`。Spec の全射性と単射性はいずれも `PrimeSpectrum.comap f` に課した。各 Q ∈ Spec B に対し P = f⁻¹Q とし、標準射 `Ideal.ResidueField.map P Q.asIdeal f rfl` の `toAlgebra` で κ(P)→κ(Q) の純非分離性を課した。 |
| `isUniversalHomeomorphism_baseChange` | f : A→B と g : A→C が与える二つの代数構造を局所的に指定し、f の普遍同相性から右の脚 C→B⊗_A C の普遍同相性を結論にした。 |
| `isUniversalHomeomorphism_comp` | A→B と B→C の普遍同相性からその合成の普遍同相性を得る。 |
| `isUniversalHomeomorphism_of_nilpotent_kernel` | 全射 f と `IsNilpotent (RingHom.ker f)` を仮定する十分条件。ここでは核イデアル全体の冪零性を仮定してよい。 |

### 停止理由と反例

今回の指示と draft の docstring は、一般の F_p 代数の射の**必要十分条件**にも「核が冪零」と書いている。直前の十分条件と同じ `IsNilpotent (RingHom.ker f)` を入れると、必要性が成り立たない。

k = F_p、A = k[x₁,x₂,…]/(x₁²,x₂²,…) とし、すべての xᵢ を 0 に送る f : A→k を取る。核 I の各元 z は zᵖ = 0 を満たす。実際、z は有限個の正次数単項式の和で、Frobenius は加法的である。よって全ての素イデアルが I を含み、商写像は Spec で全単射で剰余体は k→k。写像は整なので今回の定義による普遍同相であり、全射だから「各元のある p 冪が像に入る」も満たす。しかし全ての n ≥ 1 で x₁⋯xₙ は Iⁿ の非零元である。この単項式はどの xᵢ² でも割れない。従って I は冪零イデアルでない。

W9 の「Lemma 10.12 の残部」（`review-codex-w9.md` 2907–2908、2915行）は一般の nil イデアルには一様な指数を要求せず、広げる際にも核の nil 性を使う。これに対応する判定の右辺の候補は
`RingHom.ker f ≤ nilradical A ∧ ∀ b : B, ∃ n : ℕ, b ^ (p ^ n) ∈ f.range`。
左の条件は `mem_nilradical` により各核元が冪零であることを表す。Mathlib の `PrimeSpectrum.isHomeomorph_comap` にもこの条件が現れる（同補題の結論は Spec の位相同型）。この読みを採用するか、イデアル自体の冪零性を必要とする別の一般性に限るかが、再開時の確認点である。Lemma 10.12 自体への反例ではない。

### 確認と残件

- 新しい未発見名の仮置きとファイル内の名前に関する `要確認` は0件。`PrimeSpectrum.comap_asIdeal`、`Ideal.ResidueField.map` の等式の向き、`IsPurelyInseparable`、`Algebra.TensorProduct.includeRight`、本体での `IsNilpotent (RingHom.ker f)` の使用例をソースで照合した。
- 標数 p の判定以降の7定理（完全環から被約環の場合、純非分離、近似、一般点、主開への拡張、最終層別を含む）は基準のまま。変更は `drafts/A8/Stratification.lean` と本報告のみ。ビルド・Lean 実行・型検査はしていない。

### 第6部の続き（核の意味を確定、停止点3完了）

前半のコミットは `03206fb58`。ユーザーの回答と a8-design の決定（`7a59fd9ed`）に従い、G-A8-4 の核の条件を `RingHom.ker f ≤ nilradical A` に統一した。全射の補題は `isUniversalHomeomorphism_of_nil_kernel` に改名し、同値判定の指数は `∀ b : B, ∃ n : ℕ, b ^ (p ^ n) ∈ f.range` とした。基底の条件 `(p : A) = 0` は射 f を通じて B にも伝わり、零環も含む。G-A8-5 の全射性は A で p 冪根を取り B の被約性で示し、単射性は A の被約性と核の nil 性で示す。核全体の一様な指数はどちらにも使わない。

| 宣言 | 型にした内容 |
| --- | --- |
| `isUniversalHomeomorphism_of_isPurelyInseparable` | 体の純非分離拡大の構造射の普遍同相性。有限分離拡大については別の補題で、有限次元性・分離性を入力に `Algebra.Etale` を結論にした。 |
| `exists_noetherianApproximation` | ℤ_(p) を ℤ の (p) での局所化として表し、hZp から R への射を作った。指定の有限係数集合を含む有限生成部分代数 R₀、noetherian 性、有限表示有限 R₀ 代数 S₀、右の脚の R 作用に関する S₀⊗_{R₀}R ≃ₐ[R] S を返す。証明では表示にモニック関係を加え、その係数も用いて R₀ を生成する。 |
| `generic_structure` | 極小点の有限性、その剰余体の積 K が R の全商環であること、(K⊗_R S)_red の K 代数としての体の有限積分解。各体因子にはその下の極小点を指定した。同じ点の上の複数因子と、因子のない点も許す。各拡大の相対分離閉包 M は基底体上有限エタールで L/M は純非分離。p 可逆な基底体の標数は 0 で M→L は全単射。 |
| `spread_out_generic` | noetherian 基底で全ての極小点を含む D(g) を取り、その上の指定された環の射を有限エタール射と普遍同相に分解する。後者が p 反転後に誘導する射の全単射性も条件に含めた。 |
| `exists_finiteEtaleStratification` | n と g : Fin n → R の存在、全 g の生成イデアルが ⊤、各層で元の射の誘導射と分解の合成が一致すること、p = 0 または可逆であること。分解は同じ中間環 T に有限性・エタール性・普遍同相性・p 反転後の同型を課す。証明の穴には、近似環上で真に小さい V(g₁) への noetherian 帰納と (pgᵢ,gᵢ) による細分を記した。 |

`earlierIdeal` は厳密に j < i の元だけを取り、`StratumRing I g` は (R/√I)[1/g]。これは (R/I)_red[1/g] の表示である。S 側は f に沿って I を延長し、それから根基を取り f(g) を反転する。`stratumUnit` と `stratumMap` は商・局所化の標準射から構成した。p 反転後の同型は、存在する任意の環同型ではなく同じ T→Sᵢ の誘導射に対する `Function.Bijective` として記録した。

**確認結果。** `Ideal.ResidueField.map`、`IsLocalization.lift`、`IsLocalization.Away.lift`・`map`、`Ideal.quotientMap`、`Algebra.TensorProduct.includeRight`、`Subalgebra.FG`、`Ideal.finite_minimalPrimes_of_isNoetherianRing`、`separableClosure`、`Algebra.FormallyEtale.of_isSeparable`、`Algebra.isOpen_etaleLocus` をソースで照合した。未発見名の仮置き・ファイル内の「要確認」は0件。前半の核の解釈以外に設計との差は見つからなかった。対象の `: True`／`Type u := sorry` は残っていない。静的な差分・変更パスの確認のみで、Lean 実行・型検査・ビルドは未実施。停止点4（A0）には進んでいない。

## 第7部（停止点4完了・BS-D1 総括）

開始時の HEAD は main `3191ee550`、作業ツリーと index は空。A0 の指定9宣言を具体化した。作業中に調整側で記録された a0-design §2.7・§2.8′ の決定（`9dcd2250c`、`53f1f253c`、`fb6ae98d4`）を読んで反映した。今回の編集は A0 の三本と本報告への追記だけである。

### A0 の宣言と設計判断

| 宣言 | 入力・結論 |
| --- | --- |
| `prismaticCohomology_cutoff_invariant` | `HasEnvelopes P R` と二つの許容 cutoff κ ≤ κ′ を入力とする。環側では濃度の証拠だけを緩め、小さい模型に移して opposite を取った包含 ι を Site に置いた。比較は O_Δ のみに対するもの。κ′ の O を ι に沿って制限した前層と κ の O の `FunctorIso`、κ′ の RΓ から制限の RΓ および κ の RΓ への可逆な辺を述べた。共通の C^• は濃度 ≤ cutoff A R。比較定理本体は同じ名前空間で CechAlexander の Tot 比較直後に移した。これで Site→CechAlexander→Site の循環を生じない。 |
| `IsPrismaticEnvelope.of_closure` | J₀ ⊆ B について、商への射と `principalCompletionUnitRingHom` の合成の核 J を定義し、J₀ ≤ J を明示した。同じ δ 代数、prism Q、単位 η のまま J₀ と J の envelope の普遍性が同値。証明を A/d = 0 とそれ以外に分けた。後者では試験標的 D/dD の導来 p 完備性を使う。CechAlexander の `cechKernel` も、評価の核を B に延長してからこの同じ閉包を取る。 |
| `prismaticEnvelope_baseChange_of_variables` | 有界 prism の射 f と変数の envelope を入力とし、B′ と C′ は A′⊗_A B と A′⊗_A C の (p,d′) 完備化の H⁰。既存の `PDCompletionH0`、環構造、`pdCompletionUnit` と左右の脚を指定した。延長イデアル J′ での envelope、C′ の有界 prism、二脚での δ 構造の両立、η′ の二つの制限を結論に含めた。 |
| `cechNerveData`・`cechAlexander_isLimitCone_iff` | 標準頂点 [0]→[n] の像を脚とする余錐そのものの `IsColimit` を `cechAlexander_isCoproduct` に置いた。`IsColimit` はデータなので Lean の宣言は `def`。この脚を `equivSmallModel` で送り opposite を取った射が S3 の射影。構造射は同じ余単体的対象から取り、`proj_map` は頂点包含の合成に対応する。O_Δ 上の錐の極限性の同値は S3 の `isLimitCone_iff_restrict_cech` の適用。 |
| `prismaticCohomology_eq_cechAlexanderTot` | 任意の指定 Tot 極限錐 t に対し、同じ頂点をもつ O_Δ 上の極限錐を `exists_limitCone_of_cech` で返す。別に、Cor 3.12(d)・S2 を使う Δ の頂点から t の頂点への可逆な辺を述べた。独立に選んだ二つの極限の頂点には等号を要求しない。 |
| `cechAlexanderAffine` | R を (A/d)[X₁,…,Xᵣ] の一変数導来 p 完備化 H⁰ とし、環構造、単位、A/d 作用を指定。次数 n の変数は Fin r × Fin(n+1) の持ち上げ。イデアルは d と全差 Xⱼ⁽ⁱ⁾−Xⱼ⁽⁰⁾ で生成される。各項はその envelope と単位 η を持ち、site の構造射が copy 0 の座標を与える。θ の射は各座標を θ(i) に送る一意な射を選ぶ。A1 の `affineAlgebra` は同じ定義を使う設計で、A1 の draft 自体は従来の仮置きのまま。 |
| `cechAlexanderAffine_computes`・`cechAlexanderAffine_baseChange` | 前者は両モデルに S3 を適用し、指定した二つの Tot の間と Δ から affine Tot への可逆な辺を結論にした。後者は各次数で、上の完備底変換環から A′ 側の項への環同型を与える。δ 構造・prism イデアル・係数 A′ の射との両立、元の項からの prism 射との両立、各 copy の座標の像を指定した。 |

元の `cechAlexander_isCoproduct` の存在量化だけでは、その脚が `cechAlexander.map` の標準頂点であると分からず、S3 の `proj_map` を作れなかった。もう一つの相違は Site に置かれていた定理が後段の `HasEnvelopes` を必要とする点である。いずれも上記の承認済みの形で解決した。`cutoff` の基数式は元どおりで、引数を `cutoff A R` に統一した。

### 要確認と検査範囲

新しい未発見名の仮置きは0件。A0 三本に残る既存の `要確認` は次の通り（同一事項の重複は一件とする）。

- PrismaticSite の `structurePresheafDerived` の小さい nerve からの比較、`hodgeTateCohomology` の A/d との導来テンソル、`prismaticCohomologyFrobenius` の φ_A に沿うスカラー制限。
- PrismaticEnvelope の `IsCompletelyRegularRel` の Koszul ホモロジーの API。
- CechAlexander は0件。以前の対象では ArcSite の付値の整拡大への延長についての既存注記が一件ある。

`PrincipalCompletionH0`・`principalCompletionUnitRingHom`、`PDCompletionH0`・`pdCompletionCommRing`・`pdCompletionUnit`、`relativeFreeInitialPolynomialMap`、`OrientedPrism.Hom`、`SimplexCategory.const`、`equivSmallModel`、S1〜S3 の錐と制限、`F2.Presentable.IsPresentable`、`IsInvertibleEdge` のソースを照合した。確認は差分・宣言の位置と依存順・仮置きの検索まで。Lean の実行・型検査・ビルドは行っていない。Cor 3.12(d)、S2・S3 や envelope の存在などの証明は引き続き drafts の証明課題である。

### BS-D1 全体の件数と残る True

指示書の開始基準 `e743b6a57` と現在の対象6ファイルを比較した。下表は、元の**名前つき宣言**で結論が `: True := …` または本体が `: Type u := sorry` だったものを一宣言一回で数えた。改名した nil 核の補題、移した cutoff 定理はそれぞれ一件。補助定義、instance、構造体の個別フィールド、元から具体的な結論の宣言の修正はこの数には含めない。

| 開始時のファイル | True を具体化 | Type u の仮置きを具体化 |
| --- | ---: | ---: |
| A6/ArcSite | 10 | 4 |
| A6/ArcSheafProperty | 16 | 0 |
| A8/Stratification | 10 | 0 |
| A0/PrismaticSite | 1 | 0 |
| A0/PrismaticEnvelope | 2 | 0 |
| A0/CechAlexander | 6 | 0 |
| 合計 | **45** | **4** |

したがって元の仮置きから具体化した宣言は **49件**。停止点4の指定9件に残る `True` は0件。対象6ファイル全体の残件一覧は `A0/PrismaticSite.lean` の **`prismaticCohomologyFrobenius` 一件**で、BS-D1 の指定外。次の一覧は他の drafts も含め、コメントを除き名前つき宣言の結論が文字通り `True` のものを数えた。型中の命題変数や `∃ …, True`、証明の `sorry` は別の集計対象である。

<details>
<summary>drafts 全体の True 宣言一覧（270件、うち BS-D1 の指定対象0件）</summary>

- `A0/PrismaticSite.lean`（1件）　`prismaticCohomologyFrobenius`
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
- `A4/AfterComparison.lean`（2件）　`e3Perfd_eq_direct`、`perfectoidization_charP`
- `A4/InterfaceFields.lean`（7件）　`perfectoidizationFunctor_vertex`、`e3Perfd_of_complete`、`e3Perfd_derived`、`hodgeTateUnit`、`toPerfection`、`e3Unit_of_complete`、`e3H0_of_complete`
- `A4/Perfectoidization.lean`（7件）　`frobeniusTower`、`prismaticPerfectionFrobenius`、`prismaticPerfection_coconnective`、`prismaticPerfection_h0_perfectDelta`、`perfectoidization_coconnective`、`prismaticPerfectionPrism`、`prismaticPerfection_filteredColimit`
- `A5/PerfectSite.lean`（8件）　`perfUnder_cechNerveData`、`perfectSite_cechNerveData`、`perfectStructurePresheaf`、`perfectStructurePresheaf_isSheaf`、`perfectPrism_hom_lift_unique`、`perfectSiteEquivPerfectoidUnder`、`perfectionComparisonLeg`、`perfectionComparison`
- `A5/PerfectSiteComparison.lean`（8件）　`perfectionComparison_isIso`、`perfectionComparison_isIso_topology`、`perfectoidization_isLimit`、`perfectoidization_isLimit_u`、`perfectoidization_indep`、`perfectoidization_semiperfectoid`、`perfectionComparison_isIso_animated`、`perfectoidization_piZero`
- `A5/RootAdjunction.lean`（2件）　`algebraicRootClosure_filteredColimit`、`polyAlgebraToRoot_pCompletelyFaithfullyFlat`
- `A5/SemiperfectoidCase.lean`（17件）　`baseComparison`、`cotangent_perfectoid_vanish`、`derivedPrismaticCohomology_baseIndep`、`cotangent_shift_connective_of_semiperfectoid`、`hodgeTate_connective_of_semiperfectoid`、`prismaticPerfection_connective_of_semiperfectoid`、`perfectoidization_discrete_of_semiperfectoid`、`perfectoidization_isIntegralPerfectoid_of_semiperfectoid`、`universalPerfectoidUnit_isPerfectoidization`、`perfectoidizationToUniversal`、`perfectoidizationToUniversal_splitSurjective`、`exists_perfectoid_surjection`、`rootQuotient_to_perfectoidization_surjective`、`rootQuotient_finite_reduction`、`rootQuotient_unit_surjective`、`surjective_unit_of_semiperfectoid`、`perfectoidization_semiperfectoid_iso`
- `A5/StrongDescent.lean`（11件）　`prismaticCohomology_rootMap_descendable`、`prismaticPerfection_rootMap_descendable'`、`rootMap_descendable_of_one`、`rootMap_fiber_rhom_coconnective`、`coconnective_of_modBaseChange`、`rhom_baseChange_koszul_connection`、`baseChange_phiInv_eq_frobeniusTwist`、`rootMap_modP_eq_deRham`、`deRhamOneVariable_formal`、`squareZero_rhom_coconnective`、`rootMap_descendable_one`
- `A5/WeaklyInitialAndDescent.lean`（15件）　`algebraicRootCover_properties`、`cech_independent_of_flatSemiperfectoidCover`、`perfectoidTargetWeaklyInitial`、`perfectoidTargetWeaklyInitial_isWeaklyInitial`、`limit_perfUnder_eq_tot`、`limit_perfectSite_eq_tot`、`limit_perfUnder_eq_limit_perfectSite`、`tot_coconnective_filteredColimit`、`limit_perfectSite_filteredColimit`、`perfectionComparison_isIso_of_finiteType_cases`、`rootCover_isSemiperfectoid`、`prismaticPerfection_rootCover_descent`、`perfUnder_leftAdjoint_initial`、`limit_perfectSite_rootCover_descent`、`perfectionComparison_isIso_of_finiteType`
- `A6/Excision.lean`（6件）　`sectionsOf_homSheaf_eq_perfectoidization`、`homPresheafPushout_localEquiv`、`perfectoidization_excision`、`quotient_isModuleComplete`、`homPresheaf_completionRing_iso`、`sectionsOf_homSheaf_eq_e3Perfd`
- `A6/PerfectoidFiniteProduct.lean`（1件）　`fontaineTheta_prod_compat`
- `A6/SheafOfSetsExcision.lean`（13件）　`isArcCover_of_arcOutside`、`isArcCover_diagonal_of_arcOutside`、`isArcCover_quotient_split`、`perfectoid_factor_of_idempotent`、`perfdUnderProdEquiv`、`perfectoidization_prod`、`excision_of_excision_prod`、`extendArcSheaf`、`sheafOfSets_excision`、`homSheaf`、`hom_homSheaf_eq`、`homSheaf_pushout`、`homSheaf_quotient_mono`
- `A7/AnimatedDomain.lean`（2件）　`animatedCompletion`、`discreteToAnimated_complete`
- `A7/AnimatedPerfectoidization.lean`（10件）　`relativeTensor`、`relativeTensor_eq_bar`、`preservesRelativeTensor_of_siftedAndTensor`、`derivedPrismaticCohomology_relativeTensor`、`perfectoidizationAnimated_discrete`、`frobeniusColimit_relativeTensor`、`completion_relativeTensor`、`modD_relativeTensor`、`perfectoidization_relativeTensorMap`、`perfectoidization_relativeTensor`
- `A7/DiscreteCore.lean`（3件）　`prismaticPerfection_discrete_of_perfectoidization_discrete`、`perfectoidization_perfectPrism_of_discrete`、`perfectoidization_isIntegralPerfectoid_of_discrete`
- `A7/UniversalProperty.lean`（7件）　`perfectoidization_of_perfectoid`、`exists_extension_of_perfectoid`、`perfectoidization_map_unit_eq_unit`、`selfTensor_perfectoidization_eq`、`selfTensor_unit_eq_mul`、`extension_unique_of_perfectoid`、`perfectoidization_isPerfectoidization_of_discrete`
- `A8/AlmostConnectivity.lean`（11件）　`IsAlmostConnective`、`restrictScalars_perfectoidQuotient_fullyFaithful`、`isAlmostZero_iff_completedTensor_isZero`、`isAlmostConnective_iff_completedTensor_connective`、`isAlmostConnective_completedFilteredColimit`、`connective_iff_almost`、`perfectoidIdeal_radical`、`isAlmostZero_radical`、`isAlmostZero_iff_forall_gen`、`perfectoidIdeal_baseChange`、`isAlmostZero_baseChange_iff`
- `A8/AlmostPurityConnectivity.lean`（12件）　`finitePresentation_isModuleComplete`、`span_singleton_isModuleComplete`、`almostConnective_of_aic_baseChange`、`exists_principal_splitting_cover`、`trivialCoverComparison_finite`、`trivialCoverComparison_integral`、`trivialCoverComparison_localization_iso`、`trivialCoverComparison_isModuleComplete`、`arcOutside_of_integral_of_localization_iso`、`perfectoidization_almostIso_of_localization_iso`、`perfectoidization_pow_eq`、`perfectoidization_almostConnective_of_finiteEtaleAway`
- `A8/IntegralDiscreteness.lean`（17件）　`perfectoidization_red`、`integral_isFilteredColimit_finitePresentation`、`isIntegralPerfectoid_completedFilteredColimit`、`perfectoidization_discrete_of_finitePresentation_connective`、`perfectoidization_connective_of_stratification_one`、`perfectoidization_quotient_connective_of_ih`、`integralClosureInLocalization_integral`、`integralClosureInLocalization_arcOutside`、`integralClosure_not_complete_counterexample`、`integralClosureCompletion_isModuleComplete`、`arcOutside_completionRing`、`perfectoidization_almostIso_integralClosureCompletion`、`exists_finitePresentation_approximation_fixedLocalization`、`perfectoidization_almostConnective_of_stratification`、`perfectoidization_connective_of_finitePresentation`、`prismaticPerfection_discrete_of_integral`、`perfectoidization_isIntegralPerfectoid_of_integral`
- `DerivedGeneral/CompletionFunctor.lean`（5件）　`completion_isReflective`、`completion_tensor_koszul`、`completion_exact`、`complete_colimit`、`completedBaseChange`
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
