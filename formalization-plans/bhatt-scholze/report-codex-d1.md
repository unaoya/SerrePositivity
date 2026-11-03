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
