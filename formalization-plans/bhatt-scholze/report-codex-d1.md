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
