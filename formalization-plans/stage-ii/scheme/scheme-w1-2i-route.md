# SC-W1 2i：段0（G-A6-1、経路Bの組み立て）

> 承認・再開更新（11-17夕）：外枠9,000行・66署名を事前承認。main 1fb2c6dccの取り込みと対象確認後に再開した。照合・合成則の追加と超過時の切り分けは指示書末尾に従う。現在の実装・検証・規模は [2i進捗記録](scheme-w1-2i-report.md)。以下の「段0で停止」「外枠未承認」は段0提出時の履歴。

2026-11-17、math/scheme。2g-2は数学cc1d70c10・報告6f1996722、2hは数学7971aefe8・完成報告27e593ae5。**2iのLeanの追加はしていない。この紙と署名データを提出して停止する。** 指示書末尾「先に段0の紙を出して止まる」による停止で、承認待ちを2hの作業へ遡らせない。

型の正本は [ArcRouteB.lean](../../bhatt-scholze/drafts/A6/ArcRouteB.lean)。最終型は同じ `ArcRouteBGoal`、G-A6-1（完全F_p代数の有限族のarc被覆の、元の積への一射の増大Čech完全性）。[a6-design](../../bhatt-scholze/design/a6-design.md) §4の経路BをOに特殊化する。BM18 Thm1.7・∞・一般W_n・有限射影E・非affineへの拡張は使わない。2hでBS17入力と本体の完全性述語の定義的な一致を検証済み。

## 組み立てと、既存の入口の点検

[BM18 Prop4.8とLemma4.7](https://arxiv.org/pdf/1807.04725v4#page=28) の構造層の場合を、以下の代数的な補題で組み立てる。対応番号は各署名に記した。補題の型・設計・見積りはこの形式化のための計画である。詳しい既存の紙は [BS-W12報告](../../bhatt-scholze/reports/report-codex-w12.md) §2.1・§2.2。

1. Uは元の一射のarc判定と、任意の完全係数への底変換後のČech完全性を固定する。有限族と一射は同じ積・同じ付値拡大で比較する。
2. Mは**既存の有限表示模型**をそのまま使う。FinitePresentationModelCategory/Filtered/Colimitは一般の基底で使え、Noether仮定はない。対象は既存SmallModel、脚は元の代数射のまま。有限表示模型の完全化がarc被覆なのは、元のBへ向かう指定脚による細分のためであり、模型の被覆判定を有限段へ降ろす循環はない。
3. IとQは剰余体の点、有限表示による区間への因子化、完全化への延長と切断を接続する。端点の図式・余極限・因子化・Zornは既存。新しく必要なのは指定区間と次元の照合・実際の点の供給・各仮定の代入である。
4. Oは重なる区間の**普遍**Čech完全性を貼る。既存の `Arc.cechExact_of_overlapTensor` はB:Under Vに対する入口で、任意の完全V代数Tの増大項への普遍版ではない。Tが非平坦でもTor消滅で係数の短完全列を保ち、そのT上のmoduleCechに適用する。O01〜03の三つの指定tensor同型で、区間の和を基底にした場合を同じV上の正規化した係数と照合する。
5. Pは超積・積・付値試験環・正次数への代入。既存の `cechExact_of_ultraproducts` もB:Under(ΠV_i)の入口なので、任意の完全Tに対する普遍版P01を別に作る。平坦局所化T→T⊗R R_Uとtensorの結合を通して、ホモロジーを元のR加群として零性検出する。
6. TとVは正本の定義と既に書かれた条件付きの証明を本体の現行名で移す。元のdraft全体を今回ビルドしたという主張ではない。B01/B02でP06の行と、2hから得るV05の列を、既存B1の同じ二重Čechの消去へ渡す。

**指定構成の点検**：既存模型・Frobenius順極限・probe product・Cech各項は変更しない。弱い存在の命題から別の模型をchooseしていない。Q/Iの点・有限段の因子化はその命題自体が存在を要求するところでだけ使う。既存main宣言の本体の置き換えは0件。単なるČech完全性を任意の非平坦な底変換へ反映したことにはしない。

## 置き場所と共有の表記

新規の組み立ては `SerrePositivity/AlgebraicGeometry/ArcRouteB/`、名前空間 `SerrePositivity.AlgebraicGeometry.ArcRouteB` を提案する。スキーム論レーンの新規ファイルをAlgebraicGeometryに置く規約を保つ。既存のB1〜B5はimportして使い、移動・改変しない。

| モジュール案 | 署名群 |
| --- | --- |
| Definitions | T00〜T05、U01〜U03、O07 |
| UniversalCech | U04〜U09、M12、P00 |
| PerfectedModels | M01〜M11、I00 |
| IntervalSections | I01〜I10、Q01 |
| IntervalGluing | O01〜O06・O08・O09、I11・I12 |
| ProductDetection | P01〜P06 |
| ArcCechExact | T06、V01〜V06、B01・B02 |

上は配置案で、ファイル名ではなく以下のDAGでimportを分割する（例：IntervalSectionsのI08はIntervalGluingのO07をDefinitionsから読む）。IntervalSectionsはO08/O09に依存せず、IntervalGluingはSectionsに依存する。登録は最後に入口と直接のimporterだけを対象ビルドする。deprecated aliasは不要な新規名である。

全署名の共有の文脈は次。各署名はこの文脈以外のsection変数を使わず、補題の型に必要な仮定を全て書いている。`Arc`は既存のBhattScholze.Perfectoidization.Arcの名前空間、AGの既存宣言はopenで参照する。以下は**紙の署名**で、Lean本体や型検査済みの下書きではない。

```lean
universe u
open CategoryTheory CategoryTheory.Limits
open SerrePositivity SerrePositivity.AlgebraicGeometry
open SerrePositivity.BhattScholze.Perfectoidization
open scoped Simplicial TensorProduct
namespace SerrePositivity.AlgebraicGeometry.ArcRouteB
```

U01の値は常に同じ `algebraMap T (T ⊗[A] B)`。M05/M06の対象・脚は既存のsmall modelのもの、M08/M09はその同じCjのFrobenius順極限と、H01を合成した指定脚。O04の三項はT、(T⊗V V_b)×(T⊗V V/a)、T⊗V V[a,b]で、写像は元の単位と制限の差。P03は実際のunderCechInclusionの第0因子。これらを単なる存在仮定に置き換えない。

## 規模と一覧

**一覧：済み0／全体66（うち追加66・2i段0の初期一覧）。** 正本の定義・条件付き補題の移設も署名に含めた数で、2hの16署名やB1〜B5の既存本体は数えていない。型の提案66件、★17件。既存構成の法則に本数の停止枠を設けるという意味ではない。

素の合計 **1,783〜4,255行**、各署名を係数2で補正した合計 **3,566〜8,510行**。入口登録・モジュールのヘッダ等の予備150〜300行を別に確保し、完成見込み **3,716〜8,810行**、提案外枠 **9,000行**（上端8,810に約2.2%の余裕）。2iの外枠はまだ承認されていないので、この数を根拠にLeanへ進まない。★は普遍版・元の射を保つtensor比較・FP模型の交換・弱Nullstellensatzの接続で膨らみやすい箇所。

半分の約4,500行で実測と残りを報告する案。紙にない署名、型の変更、既存main本体の変更、または上端が外枠を超える場合は承認された停止規則に従う。超過時は完成した署名のまとまりまでをコミットし、残部を次の停止点の紙へ切り離す案である。

| ID | 名前 | 素の行数 | 係数2 | 依存 |
| --- | --- | ---: | ---: | --- |
| U01 | `arcBaseChangeHom` | 5–12 | 10–24 | 既存のみ |
| U02 | `PerfectRingCechUniversalExact` | 5–10 | 10–20 | U01 |
| U03 | `IsArcHom` | 5–12 | 10–24 | 既存のみ |
| U04 | `isArcHom_pi_iff` | 25–60 | 50–120 | U03, T02 |
| U05 | `isArcHom_baseChange` | 20–45 | 40–90 | U01, U03 |
| U06 | `isArcHom_of_refinement` | 8–18 | 16–36 | U03 |
| U07 | `perfectRingCechUniversalExact_baseChange` | 25–65 | 50–130 | U01, U02 |
| U08 | `perfectRingCechUniversalExact_of_flat_factor` | 35–90 | 70–180 | U02 |
| U09 | `perfectTensor_of_primeCast_eq_zero` | 35–65 | 70–130 | 既存のみ |
| M01 | `frobeniusDirectLimit_primeCast_eq_zero` | 5–12 | 10–24 | 既存のみ |
| M02 ★ | `frobeniusDirectLimit_perfectRing` | 55–130 | 110–260 | M01 |
| M03 | `frobeniusDirectLimitDesc` | 8–18 | 16–36 | 既存のみ |
| M04 | `frobeniusDirectLimitDesc_comp_of_zero` | 8–20 | 16–40 | M03 |
| M05 | `finitePresentationModelUnderDiagram` | 20–50 | 40–100 | 既存のみ |
| M06 | `finitePresentationModelUnderCocone` | 12–30 | 24–60 | M05 |
| M07 | `finitePresentationModelUnderCoconeIsColimit` | 20–55 | 40–110 | M06 |
| M08 ★ | `perfectedModelDiagram` | 45–100 | 90–200 | M02, M05, I00 |
| M09 | `perfectedModelCocone` | 20–55 | 40–110 | M03, M04, M08 |
| M10 ★ | `perfectedModelCoconeIsColimit` | 60–150 | 120–300 | M07, M09 |
| M11 | `perfectedModel_isArcHom` | 10–25 | 20–50 | U06, M09 |
| M12 ★ | `perfectRingCechUniversalExact_of_filtered_models` | 45–100 | 90–200 | U02 |
| I00 | `perfectedAlgebraUnit` | 6–15 | 12–30 | 既存のみ |
| I01 ★ | `intervalRingSpectrumOrderIso` | 45–110 | 90–220 | 既存のみ |
| I02 | `intervalRing_krullDim_le_one_of_no_prime_between` | 15–40 | 30–80 | I01 |
| I03 | `intervalRingOfFullSpectrumEquiv` | 25–65 | 50–130 | 既存のみ |
| I04 ★ | `exists_fp_residue_point_of_perfectedArc` | 60–160 | 120–320 | U03, I00, Q01 |
| I05 | `exists_right_interval_fp_section` | 35–85 | 70–170 | 既存のみ |
| I06 | `exists_left_interval_fp_section` | 35–85 | 70–170 | 既存のみ |
| I07 | `perfectedAlgebraUnit_universalExact_of_section` | 30–75 | 60–150 | U08, M03, M04, I00 |
| O01 ★ | `intervalTensorLocalizationEquiv` | 45–110 | 90–220 | 既存のみ |
| O02 ★ | `intervalTensorQuotientEquiv` | 45–110 | 90–220 | 既存のみ |
| O03 ★ | `intervalTensorIntersectionEquiv` | 45–110 | 90–220 | 既存のみ |
| O04 | `overlapTensorModuleComplex` | 40–95 | 80–190 | 既存のみ |
| O05 ★ | `overlapTensorModuleComplex_shortExact` | 70–170 | 140–340 | U09, O04 |
| O06 ★ | `perfectRingCechUniversalExact_of_overlap` | 65–160 | 130–320 | U02, U09, O05 |
| O07 | `GoodArcInterval` | 5–12 | 10–24 | U02 |
| O08 | `goodArcInterval_sub` | 30–70 | 60–140 | U07, O07 |
| O09 ★ | `goodArcInterval_glue` | 75–180 | 150–360 | O01, O02, O03, O06, O08 |
| I08 | `goodArcInterval_of_rank_le_one` | 30–70 | 60–140 | U05, U08, U09, O07 |
| I09 ★ | `goodArcInterval_right` | 50–120 | 100–240 | I02, I04, I05, I07, I08, M02 |
| I10 ★ | `goodArcInterval_left` | 50–120 | 100–240 | I02, I04, I06, I07, I08, M02 |
| I11 | `perfectedFpArc_universalExact` | 35–85 | 70–170 | I03, I08, I09, I10, O08, O09, M02 |
| I12 | `aicValuationArc_universalExact` | 35–85 | 70–170 | I11, M10, M11, M12 |
| P00 | `perfectRing_pi_of_primeCast_eq_zero` | 8–25 | 16–50 | 既存のみ |
| P01 ★ | `perfectRingCechUniversalExact_of_ultraproducts` | 90–210 | 180–420 | U02, U09 |
| P02 | `aicValuationProductArc_universalExact` | 40–100 | 80–200 | P00, P01, I12, U05, U09 |
| P03 | `probeCechFirstFactor` | 6–18 | 12–36 | 既存のみ |
| P04 | `probeCechFirstFactor_comp` | 5–15 | 10–30 | P03 |
| P05 ★ | `probeChangeToTermIso` | 45–115 | 90–230 | P03, P04, U01 |
| P06 | `probeArc_positiveRows` | 35–85 | 70–170 | P02, P05, U05, U09 |
| T00 | `ValuativeCoverFamily` | 5–12 | 10–24 | 既存のみ |
| T01 | `IsVCoverFamily` | 3–6 | 6–12 | T00 |
| T02 | `IsArcCoverFamilyCharP` | 3–6 | 6–12 | T00 |
| T03 | `affineFamilyCech` | 4–8 | 8–16 | 既存のみ |
| T04 | `BS17VCechInput` | 7–12 | 14–24 | T01, T03 |
| T05 | `ArcRouteBGoal` | 7–12 | 14–24 | T02, T03 |
| T06 | `bs17VCechInput` | 3–8 | 6–16 | T04 |
| V01 | `cechExact_of_affineVCover_from_BS17` | 20–35 | 40–70 | T04 |
| V02 | `cechExact_of_perfectAffineVCover_from_BS17` | 35–60 | 70–120 | V01 |
| V03 | `cechExact_valuationProbeProduct_from_BS17` | 8–18 | 16–36 | V02 |
| V04 | `isAffineVCover_tensor` | 20–35 | 40–70 | 既存のみ |
| V05 | `cechExact_valuationProbeProduct_tensor_from_BS17` | 12–28 | 24–56 | V02, V04, U09 |
| V06 | `cechExact_of_valuationProbeTests` | 25–45 | 50–90 | V03, V05 |
| B01 | `cechExact_of_arcHom_perfect` | 8–20 | 16–40 | P06, V06, T06 |
| B02 | `cech_exact_of_arcCover_perfect` | 12–28 | 24–56 | B01, U04, T05, P00 |
| Q01 ★ | `nonempty_algHom_of_isAlgClosed` | 40–100 | 80–200 | 既存のみ |

## 依存順と出口

型・依存・見積りの機械可読な正本は [scheme-w1-2i-signatures.json](scheme-w1-2i-signatures.json)。IDの重複なし、提案した短名の重複なし、全依存先の存在を確認した。既存本体の宣言の短名との静的照合で一致したのはT00のValuativeCoverFamilyだけで、これは新しいArcRouteB名前空間内の既存定義の別名である。

DFSで **66頂点・109辺、循環0**。次のトポロジカル順で進められる。

`U01 → U02 → U03 → T00 → T02 → U04 → U05 → U06 → U07 → U08 → U09 → M01 → M02 → M03 → M04 → M05 → M06 → M07 → I00 → M08 → M09 → M10 → M11 → M12 → I01 → I02 → I03 → Q01 → I04 → I05 → I06 → I07 → O01 → O02 → O03 → O04 → O05 → O06 → O07 → O08 → O09 → I08 → I09 → I10 → I11 → I12 → P00 → P01 → P02 → P03 → P04 → P05 → P06 → T01 → T03 → T04 → T05 → T06 → V01 → V02 → V03 → V04 → V05 → V06 → B01 → B02`

主経路は、2h → T06/V03/V05 → V06の列、およびM/I/O → I12 → P01/P02 → P06の行を、B01で同じB1の比較へ合わせ、U04/P00で元の有限族へ戻してB02に至る。M/I/O/PがBS17入力を仮定する循環はない。

再検査は次のPython（依存名が全て一覧にあることと循環を検査し、補正前後の規模を集計）。Leanを起動せず鍵は不要。

```python
import json
from pathlib import Path
n = json.loads(Path('formalization-plans/stage-ii/scheme/scheme-w1-2i-signatures.json').read_text())
a = {x['id']: x for x in n}
assert len(a) == len(n)
active, done = set(), set()
def visit(i):
    assert i in a and i not in active
    if i in done: return
    active.add(i)
    for j in a[i]['deps']: visit(j)
    active.remove(i); done.add(i)
for i in a: visit(i)
print(len(done), sum(len(x['deps']) for x in n))
print(sum(x['lo'] for x in n), sum(x['hi'] for x in n))
```

## 完全な署名と補題ごとの筋

### U01

```lean
def arcBaseChangeHom {A B T : Type u} [CommRing A] [CommRing B]
    [CommRing T] (f : A →+* B) (g : A →+* T) :
    letI := f.toAlgebra; letI := g.toAlgebra
    T →+* T ⊗[A] B
```

依存：既存のみ。素5〜12行、係数2：10〜24行。原典・位置：形式化用：指定した底変換の射。

既存：CommRingCat.tensorProd、Algebra.TensorProduct.includeLeft。

筋／法則の代入の理由：同じ構造射を使い、存在命題から選ばない。

### U02

```lean
def PerfectRingCechUniversalExact (p : ℕ)
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) : Prop :=
  ∀ (T : Type u) [CommRing T] [PerfectRing T p] (g : A →+* T),
    Cech.IsCechExact (Arrow.mk (CommRingCat.ofHom (arcBaseChangeHom f g)))
```

依存：U01。素5〜10行、係数2：10〜20行。原典・位置：BM18 Prop 4.8 の O に特殊化した補助述語。

既存：Cech.IsCechExact @ HomologicalAlgebra/Cech/Basic.lean。

筋／法則の代入の理由：非平坦な底変換も量化する。plain な完全性からの推論はしない。

### U03

```lean
def IsArcHom {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) : Prop :=
  ∀ (V : CommRingCat.{u}) [IsDomain V] [ValuationRing V],
    ringKrullDim V ≤ 1 → ∀ k : A →+* V,
    ∃ (W : CommRingCat.{u}) (hW : IsDomain W),
      letI : IsDomain W := hW
      ValuationRing W ∧ ringKrullDim W ≤ 1 ∧
      ∃ (e : V →+* W) (l : B →+* W), e.FaithfullyFlat ∧ l.comp f = e.comp k
```

依存：既存のみ。素5〜12行、係数2：10〜24行。原典・位置：BM18 Def 1.2、正本の族の一射版。

既存：ArcRouteB.ValuativeCoverFamily @ drafts/A6/ArcRouteB.lean:31。

筋／法則の代入の理由：階数を保つ元の証人をそのまま使う。

### U04

```lean
theorem isArcHom_pi_iff {A : Type u} [CommRing A]
    {ι : Type u} [Finite ι] (B : ι → Type u) [∀ i, CommRing (B i)]
    (f : ∀ i, A →+* B i) :
    IsArcHom (RingHom.pi f) ↔ IsArcCoverFamilyCharP B f
```

依存：U03, T02。素25〜60行、係数2：50〜120行。原典・位置：BM18 Def 1.2、有限族と一射の橋。

既存：exists_factor_evalRingHom_of_isDomain、isAffineVCoverFamily_iff_pi @ AG/AffineVCoverFamily.lean。

筋／法則の代入の理由：G0 の積から整域への因子化の同じ証人で rank の仮定も保つ。

### U05

```lean
theorem isArcHom_baseChange {A B T : Type u} [CommRing A]
    [CommRing B] [CommRing T] (f : A →+* B) (g : A →+* T)
    (hf : IsArcHom f) : IsArcHom (arcBaseChangeHom f g)
```

依存：U01, U03。素20〜45行、係数2：40〜90行。原典・位置：BM18 §2 の被覆の底変換。

既存：coefficientTensorLift @ CommutativeAlgebra/PerfectRing.lean:82。

筋／法則の代入の理由：付値拡大を変えず、二つの射の可換性で tensor lift を作る。

### U06

```lean
theorem isArcHom_of_refinement {A B C : Type u} [CommRing A]
    [CommRing B] [CommRing C] (f : A →+* B) (g : A →+* C)
    (r : B →+* C) (hr : r.comp f = g) (hg : IsArcHom g) : IsArcHom f
```

依存：U03。素8〜18行、係数2：16〜36行。原典・位置：BM18 Prop 4.8 (1) の有限表示模型への移行。

既存：IsArcHom の証人。

筋／法則の代入の理由：持ち上げた射と r を合成するだけ。

### U07

```lean
theorem perfectRingCechUniversalExact_baseChange (p : ℕ)
    {A B T : Type u} [CommRing A] [CommRing B] [CommRing T]
    [PerfectRing T p] (f : A →+* B) (g : A →+* T)
    (hf : PerfectRingCechUniversalExact p f) :
    PerfectRingCechUniversalExact p (arcBaseChangeHom f g)
```

依存：U01, U02。素25〜65行、係数2：50〜130行。原典・位置：形式化用：普遍完全性の代入則。

既存：Algebra.TensorProduct の結合・単位同型、Cech.ringCechExact_iff_of_iso。

筋／法則の代入の理由：任意の T 代数への二回の底変換と一回の底変換を同じ標準射で比較。

### U08

```lean
theorem perfectRingCechUniversalExact_of_flat_factor (p : ℕ)
    {A B W : Type u} [CommRing A] [CommRing B] [CommRing W]
    (f : A →+* B) (e : A →+* W) (l : B →+* W)
    (he : e.FaithfullyFlat) (hl : l.comp f = e) :
    PerfectRingCechUniversalExact p f
```

依存：U02。素35〜90行、係数2：70〜180行。原典・位置：BM18 Prop 4.8 (2)、切断後の忠実平坦反映。

既存：Cech.isCechExact_of_retraction、isCechExact_baseChange_iff @ HomologicalAlgebra/Cech/。

筋／法則の代入の理由：T→T⊗A W は忠実平坦で、そこで B の Cech に同じ l による切断がある。

### U09

```lean
theorem perfectTensor_of_primeCast_eq_zero (p : ℕ) [Fact p.Prime]
    (A T B : Type u) [CommRing A] [CommRing T] [CommRing B]
    [Algebra A T] [Algebra A B] [PerfectRing A p] [PerfectRing T p]
    [PerfectRing B p] (hp : (p : A) = 0) : PerfectRing (T ⊗[A] B) p
```

依存：既存のみ。素35〜65行、係数2：70〜130行。原典・位置：形式化用：零環も含む完全 tensor。

既存：perfectCoefficientTensor_perfectRing、正本の private perfectTensor_of_p_eq_zero @ ArcRouteB.lean。

筋／法則の代入の理由：正本の既存の零環分岐を移し、本体に狭い CharP を追加しない。

### M01

```lean
theorem frobeniusDirectLimit_primeCast_eq_zero
    (p : ℕ) (hp : p.Prime) (A : Type u) [CommRing A] (hA : (p : A) = 0) :
    (p : FrobeniusDirectLimit A p hp hA) = 0
```

依存：既存のみ。素5〜12行、係数2：10〜24行。原典・位置：形式化用：完全化の係数。

既存：frobeniusDirectLimitOf @ AG/FrobeniusDirectLimit.lean:54。

筋／法則の代入の理由：段0の環準同型で p=0 を移す。

### M02 ★

```lean
theorem frobeniusDirectLimit_perfectRing
    (p : ℕ) [Fact p.Prime] (A : Type u) [CommRing A] (hA : (p : A) = 0) :
    PerfectRing (FrobeniusDirectLimit A p (Fact.out : p.Prime) hA) p
```

依存：M01。素55〜130行、係数2：110〜260行。原典・位置：BM18 Prop 4.8 (1)、有限表示環の完全化。

既存：frobeniusDirectLimitOf_eq_iff @ AG/FrobeniusDirectLimit.lean:66。

筋／法則の代入の理由：根は一段後の同じ元。単射性は有限段の等式判定で一段をずらす。

### M03

```lean
def frobeniusDirectLimitDesc (p : ℕ) [Fact p.Prime]
    {C D : Type u} [CommRing C] [CommRing D] [PerfectRing D p]
    (hC : (p : C) = 0) (hD : (p : D) = 0) (f : C →+* D) :
    FrobeniusDirectLimit C p (Fact.out : p.Prime) hC →+* D
```

依存：既存のみ。素8〜18行、係数2：16〜36行。原典・位置：形式化用：完全な値域への延長。

既存：frobeniusDirectLimitMap @ AG/FrobeniusDirectLimitMap.lean:26、perfectFrobeniusLimitEquiv @ AG/PerfectFrobeniusDirectLimit.lean。

筋／法則の代入の理由：Frob(f) と H01 の元の D への同型を合成。

### M04

```lean
theorem frobeniusDirectLimitDesc_comp_of_zero (p : ℕ) [Fact p.Prime]
    {C D : Type u} [CommRing C] [CommRing D] [PerfectRing D p]
    (hC : (p : C) = 0) (hD : (p : D) = 0) (f : C →+* D) :
    (frobeniusDirectLimitDesc p hC hD f).comp
      (frobeniusDirectLimitOf C p (Fact.out : p.Prime) hC 0) = f
```

依存：M03。素8〜20行、係数2：16〜40行。原典・位置：形式化用：延長が元の射を保つ法則。

既存：frobeniusDirectLimitMap_of、perfectFrobeniusLimitEquiv_comp_of_zero。

筋／法則の代入の理由：段0の二つの既存法則の代入。

### M05

```lean
def finitePresentationModelUnderDiagram (A B : Type u)
    [CommRing A] [CommRing B] [Algebra A B] :
    FinitePresentationModelIndex A B ⥤ Under (CommRingCat.of A)
```

依存：既存のみ。素20〜50行、係数2：40〜100行。原典・位置：BM18 Prop 4.8 (1) の元の模型。

既存：finitePresentationModelSmallDiagram @ AG/FinitePresentationModelCategory.lean:80。

筋／法則の代入の理由：同じ SmallModel の各対象に元の代数構造射を付ける。新しい模型を choose しない。

### M06

```lean
def finitePresentationModelUnderCocone (A B : Type u)
    [CommRing A] [CommRing B] [Algebra A B] :
    Cocone (finitePresentationModelUnderDiagram A B)
```

依存：M05。素12〜30行、係数2：24〜60行。原典・位置：形式化用：同じ模型の指定脚。

既存：finitePresentationModelSmallCocone @ AG/FinitePresentationModelCategory.lean:84。

筋／法則の代入の理由：点は Under.mk(ofHom(algebraMap A B))、脚は既存 cocone の脚。

### M07

```lean
def finitePresentationModelUnderCoconeIsColimit (A B : Type u)
    [CommRing A] [CommRing B] [Algebra A B] :
    IsColimit (finitePresentationModelUnderCocone A B)
```

依存：M06。素20〜55行、係数2：40〜110行。原典・位置：形式化用：模型を Under へ保った余極限。

既存：finitePresentationModelSmallCoconeIsColimit @ AG/FinitePresentationModelColimit.lean:94。

筋／法則の代入の理由：filtered な添字と Under の忘却の connected 余極限で同じ脚を保つ。

### M08 ★

```lean
def perfectedModelDiagram (p : ℕ) [Fact p.Prime]
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [PerfectRing A p] (hp : (p : A) = 0) :
    FinitePresentationModelIndex A B ⥤ Under (CommRingCat.of A)
```

依存：M02, M05, I00。素45〜100行、係数2：90〜200行。原典・位置：BM18 Prop 4.8 (1)、同じ有限表示模型の完全化。

既存：frobeniusDirectLimitMap_comp/id @ AG/FrobeniusDirectLimitMap.lean:71,82。

筋／法則の代入の理由：j の終域は同じ Cj の Frob 順極限。源は元の A、単位は Of0∘unitj。

### M09

```lean
def perfectedModelCocone (p : ℕ) [Fact p.Prime]
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [PerfectRing A p] [PerfectRing B p] (hp : (p : A) = 0) :
    Cocone (perfectedModelDiagram p A B hp)
```

依存：M03, M04, M08。素20〜55行、係数2：40〜110行。原典・位置：形式化用：完全化した模型の指定脚。

既存：H01 自然性、M03。

筋／法則の代入の理由：点は元の A→B、脚は χB∘Frob(model→B)。

### M10 ★

```lean
def perfectedModelCoconeIsColimit (p : ℕ) [Fact p.Prime]
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [PerfectRing A p] [PerfectRing B p] (hp : (p : A) = 0) :
    IsColimit (perfectedModelCocone p A B hp)
```

依存：M07, M09。素60〜150行、係数2：120〜300行。原典・位置：BM18 Prop 4.8 (1)、完全化と模型の余極限の交換。

既存：frobeniusArrowFamilyTargetCoconeIsColimit @ AG/FrobeniusArrowFamilyColimit.lean:20。

筋／法則の代入の理由：既存の Fubini を適用し H01 で源と終点を元へ戻す。Noether 帰着なし。

### M11

```lean
theorem perfectedModel_isArcHom (p : ℕ) [Fact p.Prime]
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [PerfectRing A p] [PerfectRing B p] (hp : (p : A) = 0)
    (hf : IsArcHom (algebraMap A B)) (j : FinitePresentationModelIndex A B) :
    IsArcHom ((perfectedModelDiagram p A B hp).obj j).hom.hom
```

依存：U06, M09。素10〜25行、係数2：20〜50行。原典・位置：BM18 Prop 4.8 (1)、被覆の細分。

既存：perfectedModelCocone の脚、U06。

筋／法則の代入の理由：元の arc 被覆 B に向かう指定脚がそのまま細分。有限段の判定の降下を仮定しない。

### M12 ★

```lean
theorem perfectRingCechUniversalExact_of_filtered_models
    (p : ℕ) {A : Type u} [CommRing A]
    {J : Type u} [SmallCategory J] [IsFiltered J]
    (D : J ⥤ Under (CommRingCat.of A)) (c : Cocone D) (hc : IsColimit c)
    (hD : ∀ j, PerfectRingCechUniversalExact p (D.obj j).hom.hom) :
    PerfectRingCechUniversalExact p c.pt.hom.hom
```

依存：U02。素45〜100行、係数2：90〜200行。原典・位置：BM18 Prop 4.8 (1)、構造層に特殊化。

既存：Cech.isCechExact_colimit @ HomologicalAlgebra/Cech/Filtered.lean:99。

筋／法則の代入の理由：各 T への tensor は余極限を保つ。指定脚の Arrow 余極限を使う。

### I00

```lean
def perfectedAlgebraUnit (p : ℕ) [Fact p.Prime]
    (V C : Type u) [CommRing V] [CommRing C] [Algebra V C]
    (hp : (p : V) = 0) :
    V →+* FrobeniusDirectLimit C p (Fact.out : p.Prime)
      (by rw [← map_natCast (algebraMap V C), hp, map_zero])
```

依存：既存のみ。素6〜15行、係数2：12〜30行。原典・位置：形式化用：同じ模型の完全化への単位。

既存：frobeniusDirectLimitOf @ AG/FrobeniusDirectLimit.lean:54。

筋／法則の代入の理由：定義は Of0.comp(algebraMap V C)。M08 の各対象でも同じ式。

### I01 ★

```lean
def intervalRingSpectrumOrderIso {V : Type u} [CommRing V]
    {a b : PrimeSpectrum V} (h : a ≤ b) :
    PrimeSpectrum (ValuationIntervalRing h) ≃o Set.Icc a b
```

依存：既存のみ。素45〜110行、係数2：90〜220行。原典・位置：BM18 Def 4.6 の区間とスペクトルの照合。

既存：IsLocalization.AtPrime.primeSpectrumOrderIso @ Mathlib/RingTheory/Localization/AtPrime/Basic.lean:150、Ideal.primeSpectrumQuotientOrderIsoZeroLocus @ Spectrum/Prime/RingHom.lean:265。

筋／法則の代入の理由：商と局所化の既存の順序同型を合成する。

### I02

```lean
theorem intervalRing_krullDim_le_one_of_no_prime_between
    {V : Type u} [CommRing V] {a b : PrimeSpectrum V} (h : a ≤ b)
    (hgap : ∀ c : PrimeSpectrum V, a ≤ c → c ≤ b → c = a ∨ c = b) :
    ringKrullDim (ValuationIntervalRing h) ≤ 1
```

依存：I01。素15〜40行、係数2：30〜80行。原典・位置：BM18 Prop 4.8 (2)、隣接する端点。

既存：Order.krullDim_le_one_iff、I01。

筋／法則の代入の理由：区間の素点は端点二つだけなので長さ2の真の鎖がない。

### I03

```lean
def intervalRingOfFullSpectrumEquiv {V : Type u} [CommRing V]
    [IsDomain V] [ValuationRing V] (a b : PrimeSpectrum V)
    (ha : a.asIdeal = ⊥) (hb : b.asIdeal = IsLocalRing.maximalIdeal V)
    (h : a ≤ b) : ValuationIntervalRing h ≃ₐ[V] V
```

依存：既存のみ。素25〜65行、係数2：50〜130行。原典・位置：形式化用：全スペクトルの区間環を元へ戻す。

既存：intervalRingLift、intervalRing_hom_ext @ ValuationInterval/Basic.lean:64,83。

筋／法則の代入の理由：下端の商は零イデアル、上端の外は既に単元。元の構造射を逆とする。

### I04 ★

```lean
theorem exists_fp_residue_point_of_perfectedArc
    (p : ℕ) [Fact p.Prime] {V C : Type u} [CommRing V] [IsDomain V]
    [ValuationRing V] [CommRing C] [Algebra V C] [Algebra.FinitePresentation V C]
    (hV : IsAbsolutelyIntegrallyClosed V) [PerfectRing V p] (hp : (p : V) = 0)
    (hf : IsArcHom (perfectedAlgebraUnit p V C hp)) (a : PrimeSpectrum V) :
    ∃ g : C →ₐ[V] a.asIdeal.ResidueField, True
```

依存：U03, I00, Q01。素60〜160行、係数2：120〜320行。原典・位置：BM18 Prop 4.8 (3),(4)、剰余体の点。

既存：IsAbsolutelyIntegrallyClosed.primeResidue_isAlgClosed @ ValuationInterval/Basic.lean:122、Mathlib の弱 Nullstellensatz。

筋／法則の代入の理由：arc の階数0試験で fiber が非零。代数閉剰余体上の有限型代数に点を取る。

### I05

```lean
theorem exists_right_interval_fp_section
    {V C : Type u} [CommRing V] [IsDomain V] [ValuationRing V]
    [CommRing C] [Algebra V C] [Algebra.FinitePresentation V C]
    (a : PrimeSpectrum V) (hne : ∃ b, a < b)
    (hdense : ∀ b, a < b → ∃ c, a < c ∧ c < b)
    (g : C →ₐ[V] a.asIdeal.ResidueField) :
    ∃ (b : PrimeSpectrum V) (hab : a < b), Nonempty (C →ₐ[V] ValuationIntervalRing hab.le)
```

依存：既存のみ。素35〜85行、係数2：70〜170行。原典・位置：BM18 Prop 4.8 (3)。

既存：exists_intervalRingFactor_of_finitePresentation @ ValuationInterval/FinitePresentation.lean:43、exists_primeAbove_not_mem @ Endpoint.lean:24。

筋／法則の代入の理由：既存の上からの区間族の ideal 条件を代入。元の C を変えず有限表示で因子化。

### I06

```lean
theorem exists_left_interval_fp_section
    {V C : Type u} [CommRing V] [IsDomain V] [ValuationRing V]
    [CommRing C] [Algebra V C] [Algebra.FinitePresentation V C]
    (b : PrimeSpectrum V) (hne : ∃ a, a < b)
    (hdense : ∀ a, a < b → ∃ c, a < c ∧ c < b)
    (g : C →ₐ[V] b.asIdeal.ResidueField) :
    ∃ (a : PrimeSpectrum V) (hab : a < b), Nonempty (C →ₐ[V] ValuationIntervalRing hab.le)
```

依存：既存のみ。素35〜85行、係数2：70〜170行。原典・位置：BM18 Prop 4.8 (4)。

既存：exists_intervalRingFactor_of_finitePresentation @ ValuationInterval/FinitePresentation.lean:43、exists_primeBelow_mem @ Endpoint.lean:53。

筋／法則の代入の理由：I05 と双対の既存の下からの区間族。

### I07

```lean
theorem perfectedAlgebraUnit_universalExact_of_section
    (p : ℕ) [Fact p.Prime] {V C D : Type u} [CommRing V] [CommRing C]
    [CommRing D] [Algebra V C] [Algebra V D] [PerfectRing D p]
    (hp : (p : V) = 0) (g : C →ₐ[V] D) :
    PerfectRingCechUniversalExact p
      (arcBaseChangeHom (perfectedAlgebraUnit p V C hp) (algebraMap V D))
```

依存：U08, M03, M04, I00。素30〜75行、係数2：60〜150行。原典・位置：BM18 Prop 4.8 (3),(4)、点の延長と切断。

既存：frobeniusDirectLimitDesc、Cech.isCechExact_of_retraction。

筋／法則の代入の理由：g を完全な D まで延長し tensor の切断を作る。D の任意の底変換でも切断が残る。

### O01 ★

```lean
def intervalTensorLocalizationEquiv {V : Type u} [CommRing V]
    {a b d : PrimeSpectrum V} (hab : a ≤ b) (hbd : b ≤ d) :
    ValuationIntervalRing (hab.trans hbd) ⊗[V] Localization.AtPrime b.asIdeal
      ≃ₐ[V] ValuationIntervalRing hab
```

依存：既存のみ。素45〜110行、係数2：90〜220行。原典・位置：BM18 Prop 4.8 (5)、区間上の局所化の照合。

既存：intervalRingLift/hom_ext、Algebra.TensorProduct.lift。

筋／法則の代入の理由：同じ V の元で両側を評価して逆を確かめる。下端を正規化する choose はない。

### O02 ★

```lean
def intervalTensorQuotientEquiv {V : Type u} [CommRing V]
    {a c d : PrimeSpectrum V} (hac : a ≤ c) (hcd : c ≤ d) :
    ValuationIntervalRing (hac.trans hcd) ⊗[V] (V ⧸ c.asIdeal)
      ≃ₐ[V] ValuationIntervalRing hcd
```

依存：既存のみ。素45〜110行、係数2：90〜220行。原典・位置：BM18 Prop 4.8 (5)、区間上の閉制限の照合。

既存：intervalRingLift/hom_ext、Ideal.Quotient.lift、TensorProduct.lift。

筋／法則の代入の理由：下端の商と上端の逆元の同じ普遍性を比較。

### O03 ★

```lean
def intervalTensorIntersectionEquiv {V : Type u} [CommRing V]
    {a c b d : PrimeSpectrum V} (hac : a ≤ c) (hcb : c ≤ b) (hbd : b ≤ d) :
    ValuationIntervalRing (hac.trans (hcb.trans hbd)) ⊗[V] ValuationIntervalRing hcb
      ≃ₐ[V] ValuationIntervalRing hcb
```

依存：既存のみ。素45〜110行、係数2：90〜220行。原典・位置：BM18 Prop 4.8 (5)、交わりの照合。

既存：intervalRingLift/hom_ext、TensorProduct.lift。

筋／法則の代入の理由：既に区間 [c,b] で成り立つ単位と零関係を使う。

### O04

```lean
def overlapTensorModuleComplex {V T : Type u} [CommRing V] [CommRing T]
    [Algebra V T] {a b : PrimeSpectrum V} (h : a ≤ b) :
    ShortComplex (ModuleCat.{u} T)
```

依存：既存のみ。素40〜95行、係数2：80〜190行。原典・位置：BM18 Prop 4.8 (5)、図式(6)の T 係数。

既存：Arc.overlapModuleComplex @ Arc/Milnor/ArcIntervalOverlap.lean:80。

筋／法則の代入の理由：項は T、(T⊗V V_b)×(T⊗V V/a)、T⊗V V[a,b]。写像は元の単位と制限の差。

### O05 ★

```lean
theorem overlapTensorModuleComplex_shortExact
    (p : ℕ) [Fact p.Prime] {V T : Type u} [CommRing V] [IsDomain V]
    [ValuationRing V] [CommRing T] [Algebra V T] [PerfectRing V p]
    [PerfectRing T p] (hp : (p : V) = 0)
    {a b : PrimeSpectrum V} (h : a ≤ b) :
    (overlapTensorModuleComplex (T := T) h).ShortExact
```

依存：U09, O04。素70〜170行、係数2：140〜340行。原典・位置：BM18 Prop 4.8 (5)、Milnor の Tor 消滅。

既存：Arc.overlapModuleComplex_shortExact @ ArcIntervalOverlap.lean:96、Arc.valuationRing_milnorSquare_perfect @ ArcValuationMilnor.lean:87、ArcMilnorTensor。

筋／法則の代入の理由：任意の T は平坦と仮定しない。完全環どうしの Tor 消滅で短完全性を保存。

### O06 ★

```lean
theorem perfectRingCechUniversalExact_of_overlap
    (p : ℕ) [Fact p.Prime] {V B : Type u} [CommRing V] [IsDomain V]
    [ValuationRing V] [CommRing B] [PerfectRing V p] [PerfectRing B p]
    (hp : (p : V) = 0) (f : V →+* B) {a b : PrimeSpectrum V} (h : a ≤ b)
    (hl : PerfectRingCechUniversalExact p (arcBaseChangeHom f
      (algebraMap V (Localization.AtPrime b.asIdeal))))
    (hq : PerfectRingCechUniversalExact p (arcBaseChangeHom f (Ideal.Quotient.mk a.asIdeal)))
    (hr : PerfectRingCechUniversalExact p (arcBaseChangeHom f
      (algebraMap V (ValuationIntervalRing h)))) : PerfectRingCechUniversalExact p f
```

依存：U02, U09, O05。素65〜160行、係数2：130〜320行。原典・位置：BM18 Prop 4.8 (5)、構造層の普遍版。

既存：Arc.acyclic_of_tensorShortExact、moduleCech_tor_subsingleton @ ArcCechMilnor.lean:52、cechExact_baseChange_iff_tensorCochain @ :32。

筋／法則の代入の理由：各完全 T 上の moduleCech に O05 を使い、三つの底変換を tensor 結合で照合。

### O07

```lean
def GoodArcInterval (p : ℕ) {V B : Type u} [CommRing V] [CommRing B]
    (f : V →+* B) (a b : PrimeSpectrum V) : Prop :=
  ∀ h : a ≤ b, PerfectRingCechUniversalExact p
    (arcBaseChangeHom f (algebraMap V (ValuationIntervalRing h)))
```

依存：U02。素5〜12行、係数2：10〜24行。原典・位置：BM18 Lemma 4.7 に渡す述語。

既存：U02、ValuationIntervalRing @ Basic.lean:38。

筋／法則の代入の理由：区間ごとに完全な係数の全てを量化する。

### O08

```lean
theorem goodArcInterval_sub (p : ℕ) {V B : Type u} [CommRing V] [CommRing B]
    (f : V →+* B) {a b c d : PrimeSpectrum V}
    (h : GoodArcInterval p f a b) (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b)
    [PerfectRing (ValuationIntervalRing hcd) p] : GoodArcInterval p f c d
```

依存：U07, O07。素30〜70行、係数2：60〜140行。原典・位置：BM18 Lemma 4.7 の sub 法則。

既存：intervalRingMap @ Basic.lean:92、tensor 結合同型。

筋／法則の代入の理由：区間の同じ制限射へ U07 を代入し、二回と一回の底変換を比較。

### O09 ★

```lean
theorem goodArcInterval_glue (p : ℕ) [Fact p.Prime]
    {V B : Type u} [CommRing V] [IsDomain V] [ValuationRing V]
    [CommRing B] [PerfectRing V p] [PerfectRing B p] (hp : (p : V) = 0)
    (f : V →+* B) {a b c d : PrimeSpectrum V} (hac : a ≤ c) (hcb : c ≤ b)
    (hbd : b ≤ d) (h₁ : GoodArcInterval p f a b) (h₂ : GoodArcInterval p f c d) :
    GoodArcInterval p f a d
```

依存：O01, O02, O03, O06, O08。素75〜180行、係数2：150〜360行。原典・位置：BM18 Lemma 4.7 の glue、Prop 4.8 (5)。

既存：O01–03、O06、tensor associator。

筋／法則の代入の理由：任意の V[a,d] 代数 T へ正規化した係数の短完全列を適用。三つの指定同型で比較。

### I08

```lean
theorem goodArcInterval_of_rank_le_one (p : ℕ) [Fact p.Prime]
    {V B : Type u} [CommRing V] [IsDomain V] [ValuationRing V]
    [CommRing B] [PerfectRing V p] [PerfectRing B p] (hp : (p : V) = 0)
    (f : V →+* B) (hf : IsArcHom f) {a b : PrimeSpectrum V} (h : a ≤ b)
    (hdim : ringKrullDim (ValuationIntervalRing h) ≤ 1) : GoodArcInterval p f a b
```

依存：U05, U08, U09, O07。素30〜70行、係数2：60〜140行。原典・位置：BM18 Prop 4.8 (2)。

既存：valuationRing_interval/perfectRing_interval @ Basic.lean:104,128。

筋／法則の代入の理由：区間環自身で arc を試し、忠実平坦な付値拡大上の切断を U08 に渡す。

### I09 ★

```lean
theorem goodArcInterval_right (p : ℕ) [Fact p.Prime]
    {V C : Type u} [CommRing V] [IsDomain V] [ValuationRing V] [CommRing C]
    [Algebra V C] [Algebra.FinitePresentation V C] [PerfectRing V p]
    (hV : IsAbsolutelyIntegrallyClosed V) (hp : (p : V) = 0)
    (hf : IsArcHom (perfectedAlgebraUnit p V C hp)) {a b : PrimeSpectrum V}
    (hab : a < b) : ∃ c, a < c ∧ GoodArcInterval p (perfectedAlgebraUnit p V C hp) a c
```

依存：I02, I04, I05, I07, I08, M02。素50〜120行、係数2：100〜240行。原典・位置：BM18 Prop 4.8 (3)、Lemma 4.7 right。

既存：exists_primeAbove_not_mem、finitePresentation factor、I08。

筋／法則の代入の理由：直後の点があれば I02/I08、なければ I04/I05/I07。場合分けも署名内に含める。

### I10 ★

```lean
theorem goodArcInterval_left (p : ℕ) [Fact p.Prime]
    {V C : Type u} [CommRing V] [IsDomain V] [ValuationRing V] [CommRing C]
    [Algebra V C] [Algebra.FinitePresentation V C] [PerfectRing V p]
    (hV : IsAbsolutelyIntegrallyClosed V) (hp : (p : V) = 0)
    (hf : IsArcHom (perfectedAlgebraUnit p V C hp)) {a b : PrimeSpectrum V}
    (hab : a < b) : ∃ c, c < b ∧ GoodArcInterval p (perfectedAlgebraUnit p V C hp) c b
```

依存：I02, I04, I06, I07, I08, M02。素50〜120行、係数2：100〜240行。原典・位置：BM18 Prop 4.8 (4)、Lemma 4.7 left。

既存：exists_primeBelow_mem、finitePresentation factor、I08。

筋／法則の代入の理由：直前の点と稠密な下側の二場合を I09 と別に照合。

### I11

```lean
theorem perfectedFpArc_universalExact (p : ℕ) [Fact p.Prime]
    {V C : Type u} [CommRing V] [IsDomain V] [ValuationRing V] [CommRing C]
    [Algebra V C] [Algebra.FinitePresentation V C] [PerfectRing V p]
    (hV : IsAbsolutelyIntegrallyClosed V) (hp : (p : V) = 0)
    (hf : IsArcHom (perfectedAlgebraUnit p V C hp)) :
    PerfectRingCechUniversalExact p (perfectedAlgebraUnit p V C hp)
```

依存：I03, I08, I09, I10, O08, O09, M02。素35〜85行、係数2：70〜170行。原典・位置：BM18 Prop 4.8、Lemma 4.7 の適用。

既存：valuationIntervalProperty_of_localExtensions @ ValuationInterval/Zorn.lean:99。

筋／法則の代入の理由：point は I08、sub は O08、right/left は I09/I10、glue は O09。全区間を I03 で元へ戻す。

### I12

```lean
theorem aicValuationArc_universalExact (p : ℕ) [Fact p.Prime]
    {V B : Type u} [CommRing V] [IsDomain V] [ValuationRing V] [CommRing B]
    [PerfectRing V p] [PerfectRing B p] (hV : IsAbsolutelyIntegrallyClosed V)
    (hp : (p : V) = 0) (f : V →+* B) (hf : IsArcHom f) :
    PerfectRingCechUniversalExact p f
```

依存：I11, M10, M11, M12。素35〜85行、係数2：70〜170行。原典・位置：BM18 Prop 4.8 (1) の完結、O の場合。

既存：既存 finitePresentationModelSmallCoconeIsColimit と M10/M12。

筋／法則の代入の理由：f.toAlgebra の同じ模型に I11、filtered 余極限で元の B へ戻す。

### P00

```lean
theorem perfectRing_pi_of_primeCast_eq_zero (p : ℕ) [Fact p.Prime]
    {ι : Type u} (V : ι → Type u) [∀ i, CommRing (V i)] [∀ i, PerfectRing (V i) p]
    (hp : ∀ i, (p : V i) = 0) : PerfectRing (∀ i, V i) p
```

依存：既存のみ。素8〜25行、係数2：16〜50行。原典・位置：形式化用：任意積・空積の完全性。

既存：finitePi_primePower_bijective @ AG/PerfectAffineVCoverCech.lean（有限性の仮定なし）。

筋／法則の代入の理由：2h の点ごとの全単射性を PerfectRing へ戻す。空積の CharP は要求しない。

### P01 ★

```lean
theorem perfectRingCechUniversalExact_of_ultraproducts
    (p : ℕ) [Fact p.Prime] {ι : Type u} (R : ι → Type u)
    [∀ i, CommRing (R i)] [PerfectRing (∀ i, R i) p]
    [∀ U : Ultrafilter ι, PerfectRing (RingUltraproduct R U) p]
    {B : Type u} [CommRing B] (hp : (p : ∀ i, R i) = 0)
    (f : (∀ i, R i) →+* B)
    (hU : ∀ U : Ultrafilter ι, PerfectRingCechUniversalExact p
      (arcBaseChangeHom f (algebraMap (∀ i, R i) (RingUltraproduct R U)))) :
    PerfectRingCechUniversalExact p f
```

依存：U02, U09。素90〜210行、係数2：180〜420行。原典・位置：BM18 Lemma 3.25 の O・完全係数での普遍版。

既存：subsingleton_of_ultraproduct_tensor @ Arc/Descent/ArcCechUltraproduct.lean:34、Cech.moduleCech_acyclic_iff、平坦な homology base change。

筋／法則の代入の理由：任意の T の H を積環へ係数制限する。T_U⊗T H≅R_U⊗R H を指定結合同型で比較し零性を検出。

### P02

```lean
theorem aicValuationProductArc_universalExact
    (p : ℕ) [Fact p.Prime] {ι : Type u} (V : ι → Type u)
    [∀ i, CommRing (V i)] [∀ i, IsDomain (V i)] [∀ i, ValuationRing (V i)]
    [∀ i, PerfectRing (V i) p] (hV : ∀ i, IsAbsolutelyIntegrallyClosed (V i))
    (hp : ∀ i, (p : V i) = 0) {B : Type u} [CommRing B] [PerfectRing B p]
    (f : (∀ i, V i) →+* B) (hf : IsArcHom f) : PerfectRingCechUniversalExact p f
```

依存：P00, P01, I12, U05, U09。素40〜100行、係数2：80〜200行。原典・位置：BM18 Prop 4.8 から積への移行、Lemma 3.25。

既存：valuationRing_ultraproduct/aic_ultraproduct/perfectRing_ultraproduct_of_aic @ CommutativeAlgebra/Ultraproduct/Basic.lean:58,95,101。

筋／法則の代入の理由：超積上の arc 被覆へ I12、任意の完全 T へ P01。空の積も零性検出の量化で処理。

### P03

```lean
def probeCechFirstFactor {A : Type u} [CommRing A] (n : ℕ) :
    (∀ t : Arc.ValuationProbeIndex A, Arc.ValuationProbe A t) →+*
      ((Cech.underCech (Under.mk (CommRingCat.ofHom
        (Arc.valuationProbeProductMap A)))).right.obj ⦋n⦌).right
```

依存：既存のみ。素6〜18行、係数2：12〜36行。原典・位置：形式化用：積射の正次数の指定係数射。

既存：Cech.underCechInclusion @ HomologicalAlgebra/Cech/BaseChange.lean:60。

筋／法則の代入の理由：定義は同じ ⦋n⦌ の第0因子 inclusion の right.hom。

### P04

```lean
theorem probeCechFirstFactor_comp {A : Type u} [CommRing A] (n : ℕ) :
    (probeCechFirstFactor (A := A) n).comp (Arc.valuationProbeProductMap A) =
      ((Cech.underCech (Under.mk (CommRingCat.ofHom
        (Arc.valuationProbeProductMap A)))).right.obj ⦋n⦌).hom.hom
```

依存：P03。素5〜15行、係数2：10〜30行。原典・位置：形式化用：源の一致。

既存：Under の射の可換性、Cech.underCechInclusion。

筋／法則の代入の理由：Under の可換三角形そのもの。

### P05 ★

```lean
def probeChangeToTermIso {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (n : ℕ) :
    Cech.changeToTerm (Under.mk (CommRingCat.ofHom (Arc.valuationProbeProductMap A)))
      (Under.mk (CommRingCat.ofHom f)) (n + 1) ≅
    Arrow.mk (CommRingCat.ofHom (arcBaseChangeHom
      (arcBaseChangeHom f (Arc.valuationProbeProductMap A))
      (probeCechFirstFactor (A := A) n)))
```

依存：P03, P04, U01。素45〜115行、係数2：90〜230行。原典・位置：形式化用：B1 に渡す正次数の二回の底変換。

既存：Cech.changeToTerm @ Composition.lean:54、tensor associator。

筋／法則の代入の理由：指定した第0因子で R_n を R 代数とし、R_n⊗R(R⊗A B) と R_n⊗A B を Arrow として比較。

### P06

```lean
theorem probeArc_positiveRows (p : ℕ) [Fact p.Prime]
    {A B : Type u} [CommRing A] [CommRing B] [PerfectRing A p] [PerfectRing B p]
    (hp : (p : A) = 0) (f : A →+* B) (hf : IsArcHom f) :
    ∀ j, 0 < j → Cech.IsCechExact (Cech.changeToTerm
      (Under.mk (CommRingCat.ofHom (Arc.valuationProbeProductMap A)))
      (Under.mk (CommRingCat.ofHom f)) j)
```

依存：P02, P05, U05, U09。素35〜85行、係数2：70〜170行。原典・位置：BM18 Lemma 3.4、B1 の一方の軸の消去。

既存：Arc.valuationProbe_aic/product_perfectRing @ ArcValuationProduct.lean:66,133、Cech.cechConerve_perfectRing。

筋／法則の代入の理由：積へ底変換した被覆に P02。正次数の完全な R_j への普遍完全性を P05 で移す。

### T00

```lean
abbrev ValuativeCoverFamily (rank : CommRingCat.{u} → Prop)
    {A : Type u} [CommRing A] {ι : Type u} [Finite ι]
    (B : ι → Type u) [∀ i, CommRing (B i)] (f : ∀ i, A →+* B i) : Prop :=
  SerrePositivity.AlgebraicGeometry.ValuativeCoverFamily rank B f
```

依存：既存のみ。素5〜12行、係数2：10〜24行。原典・位置：正本 ArcRouteB.lean:31 と同じ量化。

既存：AG.ValuativeCoverFamily @ AG/AffineVCoverFamily.lean。

筋／法則の代入の理由：正本の witness・rank を一切変えず、既存定義を別名で使う。

### T01

```lean
def IsVCoverFamily {A : Type u} [CommRing A] {ι : Type u} [Finite ι]
    (B : ι → Type u) [∀ i, CommRing (B i)] (f : ∀ i, A →+* B i) : Prop :=
  ValuativeCoverFamily (fun _ => True) B f
```

依存：T00。素3〜6行、係数2：6〜12行。原典・位置：正本 ArcRouteB.lean:41、BS17 Def 2.1。

既存：T00。

筋／法則の代入の理由：同じ定義の移設。

### T02

```lean
def IsArcCoverFamilyCharP {A : Type u} [CommRing A] {ι : Type u} [Finite ι]
    (B : ι → Type u) [∀ i, CommRing (B i)] (f : ∀ i, A →+* B i) : Prop :=
  ValuativeCoverFamily (fun V => ringKrullDim V ≤ 1) B f
```

依存：T00。素3〜6行、係数2：6〜12行。原典・位置：正本 ArcRouteB.lean:46、BM18 Def 1.2。

既存：T00。

筋／法則の代入の理由：p 完備 arc 位相の別定義へ置き換えない。

### T03

```lean
def affineFamilyCech {A : Type u} [CommRing A] {ι : Type u} [Finite ι]
    (B : ι → Type u) [∀ i, CommRing (B i)] (f : ∀ i, A →+* B i) :
    CosimplicialObject.Augmented CommRingCat.{u} :=
  (Arrow.mk (CommRingCat.ofHom (RingHom.pi f))).augmentedCechConerve
```

依存：既存のみ。素4〜8行、係数2：8〜16行。原典・位置：正本 ArcRouteB.lean:51、元の有限族の増大項。

既存：元の積への一射。

筋／法則の代入の理由：同じ定義の移設。

### T04

```lean
def BS17VCechInput (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ {A : Type u} [CommRing A] [CharP A p] [PerfectRing A p]
    {ι : Type u} [Finite ι] (B : ι → Type u) [∀ i, CommRing (B i)]
    [∀ i, CharP (B i) p] [∀ i, PerfectRing (B i) p]
    (f : ∀ i, A →+* B i), IsVCoverFamily B f →
    Cech.AugmentedRingCechExact (affineFamilyCech B f)
```

依存：T01, T03。素7〜12行、係数2：14〜24行。原典・位置：正本 ArcRouteB.lean:58、G-A6-1a。

既存：AG.cech_exact_of_vCover_perfect @ AG/PerfectAffineVCoverCech.lean。

筋／法則の代入の理由：2h で量化・述語の一致を検証する入口。

### T05

```lean
def ArcRouteBGoal (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ {A : Type u} [CommRing A] [CharP A p] [PerfectRing A p]
    {ι : Type u} [Finite ι] (B : ι → Type u) [∀ i, CommRing (B i)]
    [∀ i, CharP (B i) p] [∀ i, PerfectRing (B i) p]
    (f : ∀ i, A →+* B i), IsArcCoverFamilyCharP B f →
    Cech.AugmentedRingCechExact (affineFamilyCech B f)
```

依存：T02, T03。素7〜12行、係数2：14〜24行。原典・位置：正本 ArcRouteB.lean:67、G-A6-1。

既存：ArcSheafProperty.lean の cech_exact_of_arcCover_perfect。

筋／法則の代入の理由：最終型の正本をそのまま保持する。

### T06

```lean
theorem bs17VCechInput (p : ℕ) [Fact p.Prime] : BS17VCechInput.{u} p
```

依存：T04。素3〜8行、係数2：6〜16行。原典・位置：BS17 Thm 4.1(i)、2h の出口。

既存：AG.cech_exact_of_vCover_perfect @ AG/PerfectAffineVCoverCech.lean。

筋／法則の代入の理由：2h の定理へ引数を渡すだけ。

### V01

```lean
theorem cechExact_of_affineVCover_from_BS17
    (p : ℕ) [Fact p.Prime] (hBS17 : BS17VCechInput.{u} p)
    {A B : Type u} [CommRing A] [CommRing B] [CharP A p] [CharP B p]
    [PerfectRing A p] [PerfectRing B p] (f : A →+* B) (hf : Arc.IsAffineVCover f) :
    Cech.IsCechExact (Arrow.mk (CommRingCat.ofHom f))
```

依存：T04。素20〜35行、係数2：40〜70行。原典・位置：正本 ArcRouteB.lean:75 の条件付き補題の移設。

既存：RingEquiv.piUnique、Cech.ringCechExact_iff_of_iso。

筋／法則の代入の理由：正本の一元族と積の Arrow 同型の証明を native 名で再検証。

### V02

```lean
theorem cechExact_of_perfectAffineVCover_from_BS17
    (p : ℕ) [Fact p.Prime] (hBS17 : BS17VCechInput.{u} p)
    {A B : Type u} [CommRing A] [CommRing B] [PerfectRing A p] [PerfectRing B p]
    (hp : (p : A) = 0) (f : A →+* B) (hf : Arc.IsAffineVCover f) :
    Cech.IsCechExact (Arrow.mk (CommRingCat.ofHom f))
```

依存：V01。素35〜60行、係数2：70〜120行。原典・位置：正本 ArcRouteB.lean:96 の零環を含む入口。

既存：正本の zero/nontrivial 分岐、Cech.isCechExact_of_retraction。

筋／法則の代入の理由：同じ零環分岐を保持して CharP の非零性を外へ仮定しない。

### V03

```lean
theorem cechExact_valuationProbeProduct_from_BS17 (p : ℕ) [Fact p.Prime]
    (hBS17 : BS17VCechInput.{u} p) (A : Type u) [CommRing A]
    [PerfectRing A p] (hp : (p : A) = 0) :
    Cech.IsCechExact (Arrow.mk (CommRingCat.ofHom (Arc.valuationProbeProductMap A)))
```

依存：V02。素8〜18行、係数2：16〜36行。原典・位置：正本 ArcRouteB.lean:125、B5 の入力。

既存：Arc.valuationProbeProduct_vCover @ ArcValuationProduct.lean:123。

筋／法則の代入の理由：既存の v 被覆と完全性を V02 へ代入。

### V04

```lean
theorem isAffineVCover_tensor {A B D : Type u}
    [CommRing A] [CommRing B] [CommRing D] [Algebra A B] [Algebra A D]
    (h : Arc.IsAffineVCover (algebraMap A B)) :
    Arc.IsAffineVCover (algebraMap D (D ⊗[A] B))
```

依存：既存のみ。素20〜35行、係数2：40〜70行。原典・位置：正本 ArcRouteB.lean:134 の底変換の法則。

既存：coefficientTensorLift、AG の被覆の底変換。

筋／法則の代入の理由：元の付値拡大と tensor lift を保った移設。

### V05

```lean
theorem cechExact_valuationProbeProduct_tensor_from_BS17
    (p : ℕ) [Fact p.Prime] (hBS17 : BS17VCechInput.{u} p)
    (A D : Type u) [CommRing A] [CommRing D] [Algebra A D]
    [PerfectRing A p] [PerfectRing D p] (hp : (p : A) = 0) :
    let R := ∀ t : Arc.ValuationProbeIndex A, Arc.ValuationProbe A t
    letI : Algebra A R := (Arc.valuationProbeProductMap A).toAlgebra
    Cech.IsCechExact (Arrow.mk (CommRingCat.ofHom (algebraMap D (D ⊗[A] R))))
```

依存：V02, V04, U09。素12〜28行、係数2：24〜56行。原典・位置：正本 ArcRouteB.lean:172、B1 のもう一方の軸。

既存：Arc.valuationProbeProduct_perfectRing、V02。

筋／法則の代入の理由：任意の完全 D で v 被覆を底変換し BS17 を適用。

### V06

```lean
theorem cechExact_of_valuationProbeTests (p : ℕ) [Fact p.Prime]
    (hBS17 : BS17VCechInput.{u} p) {A : Type u} [CommRing A]
    (B : Under (CommRingCat.of A)) [PerfectRing A p] [PerfectRing B.right p]
    (hp : (p : A) = 0)
    (hrow : ∀ j, 0 < j → Cech.IsCechExact (Cech.changeToTerm
      (Under.mk (CommRingCat.ofHom (Arc.valuationProbeProductMap A))) B j)) :
    Cech.IsCechExact (Arrow.mk B.hom)
```

依存：V03, V05。素25〜45行、係数2：50〜90行。原典・位置：正本 ArcRouteB.lean:190、BM18 Lemma 3.4。

既存：Cech.isCechExact_iff_of_tensorCech @ Composition.lean:137。

筋／法則の代入の理由：正本の条件付き証明を移す。他方の軸は V05、hrow は P06 で供給。

### B01

```lean
theorem cechExact_of_arcHom_perfect (p : ℕ) [Fact p.Prime]
    {A B : Type u} [CommRing A] [CommRing B] [PerfectRing A p] [PerfectRing B p]
    (hp : (p : A) = 0) (f : A →+* B) (hf : IsArcHom f) :
    Cech.IsCechExact (Arrow.mk (CommRingCat.ofHom f))
```

依存：P06, V06, T06。素8〜20行、係数2：16〜40行。原典・位置：BM18 Prop 4.8 の O 版と B1 の最終合成。

既存：P06 と V06、2h。

筋／法則の代入の理由：正次数の行と BS17 の列を同じ二重 Cech で消去する。

### B02

```lean
theorem cech_exact_of_arcCover_perfect
    (p : ℕ) [Fact p.Prime] : ArcRouteBGoal.{u} p
```

依存：B01, U04, T05, P00。素12〜28行、係数2：24〜56行。原典・位置：G-A6-1、正本 ArcRouteBGoal。

既存：有限族と積への一射の橋、P00。

筋／法則の代入の理由：元の有限族の積の完全性を使い B01 へ渡す。最終 conerve と増大項を変えない。

### Q01 ★

```lean
theorem nonempty_algHom_of_isAlgClosed (k C : Type u) [Field k]
    [IsAlgClosed k] [CommRing C] [Nontrivial C] [Algebra k C]
    [Algebra.FiniteType k C] : Nonempty (C →ₐ[k] k)
```

依存：既存のみ。素40〜100行、係数2：80〜200行。原典・位置：BM18 Prop 4.8 (3),(4) で使う弱 Nullstellensatz。

既存：MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal @ Mathlib/RingTheory/Nullstellensatz.lean:151、Algebra.FiniteType の多項式表示。

筋／法則の代入の理由：有限生成表示の真の核を含む極大イデアルを一点の評価へ送り、元の代数への因子化を取る。


## 既存宣言の所在（現在のソースから照合）

各署名の「既存」の短縮表記を以下で引く。`AG/` は `SerrePositivity/AlgebraicGeometry/`、`Arc/` は `SerrePositivity/BhattScholze/Perfectoidization/Arc/`。Mathlibの構成の一般的な法則はここにある元の構成に付属するものを使う。主な供給宣言について、実際の宣言位置を静的に照合した。private宣言を外から呼ぶ計画はない。

| 既存宣言 | 場所 |
| --- | --- |
| `SerrePositivity.AlgebraicGeometry.ValuativeCoverFamily` | `SerrePositivity/AlgebraicGeometry/AffineVCover.lean:27` |
| `SerrePositivity.AlgebraicGeometry.exists_factor_evalRingHom_of_isDomain` | `SerrePositivity/AlgebraicGeometry/FiniteProductDomainFactor.lean:17` |
| `SerrePositivity.AlgebraicGeometry.isAffineVCoverFamily_iff_pi` | `SerrePositivity/AlgebraicGeometry/AffineVCoverFamily.lean:20` |
| `SerrePositivity.coefficientTensorLift` | `SerrePositivity/CommutativeAlgebra/PerfectRing.lean:82` |
| `SerrePositivity.coefficientTensorLift_tmul` | `SerrePositivity/CommutativeAlgebra/PerfectRing.lean:92` |
| `SerrePositivity.perfectCoefficientTensor_perfectRing` | `SerrePositivity/CommutativeAlgebra/PerfectRing.lean:137` |
| `SerrePositivity.AlgebraicGeometry.frobeniusDirectLimitOf` | `SerrePositivity/AlgebraicGeometry/FrobeniusDirectLimit.lean:54` |
| `SerrePositivity.AlgebraicGeometry.frobeniusDirectLimitOf_eq_iff` | `SerrePositivity/AlgebraicGeometry/FrobeniusDirectLimit.lean:66` |
| `SerrePositivity.AlgebraicGeometry.frobeniusDirectLimitMap` | `SerrePositivity/AlgebraicGeometry/FrobeniusDirectLimitMap.lean:26` |
| `SerrePositivity.AlgebraicGeometry.frobeniusDirectLimitMap_comp` | `SerrePositivity/AlgebraicGeometry/FrobeniusDirectLimitMap.lean:71` |
| `SerrePositivity.AlgebraicGeometry.frobeniusDirectLimitMap_id` | `SerrePositivity/AlgebraicGeometry/FrobeniusDirectLimitMap.lean:82` |
| `SerrePositivity.AlgebraicGeometry.perfectFrobeniusLimitEquiv` | `SerrePositivity/AlgebraicGeometry/PerfectFrobeniusDirectLimit.lean:79` |
| `SerrePositivity.AlgebraicGeometry.perfectFrobeniusLimitEquiv_naturality` | `SerrePositivity/AlgebraicGeometry/PerfectFrobeniusDirectLimit.lean:128` |
| `SerrePositivity.AlgebraicGeometry.finitePi_primePower_bijective` | `SerrePositivity/AlgebraicGeometry/PerfectAffineVCoverCech.lean:27` |
| `SerrePositivity.AlgebraicGeometry.cech_exact_of_vCover_perfect` | `SerrePositivity/AlgebraicGeometry/PerfectAffineVCoverCech.lean:51` |
| `SerrePositivity.AlgebraicGeometry.FinitePresentationModelCategory` | `SerrePositivity/AlgebraicGeometry/FinitePresentationModelCategory.lean:30` |
| `SerrePositivity.AlgebraicGeometry.FinitePresentationModelIndex` | `SerrePositivity/AlgebraicGeometry/FinitePresentationModelCategory.lean:77` |
| `SerrePositivity.AlgebraicGeometry.finitePresentationModelSmallDiagram` | `SerrePositivity/AlgebraicGeometry/FinitePresentationModelCategory.lean:80` |
| `SerrePositivity.AlgebraicGeometry.finitePresentationModelSmallCocone` | `SerrePositivity/AlgebraicGeometry/FinitePresentationModelCategory.lean:84` |
| `SerrePositivity.AlgebraicGeometry.finitePresentationModelSmallCoconeIsColimit` | `SerrePositivity/AlgebraicGeometry/FinitePresentationModelColimit.lean:94` |
| `SerrePositivity.AlgebraicGeometry.frobeniusArrowFamilyTargetCoconeIsColimit` | `SerrePositivity/AlgebraicGeometry/FrobeniusArrowFamilyColimit.lean:20` |
| `SerrePositivity.intervalRingLift` | `SerrePositivity/CommutativeAlgebra/ValuationInterval/Basic.lean:64` |
| `SerrePositivity.intervalRing_hom_ext` | `SerrePositivity/CommutativeAlgebra/ValuationInterval/Basic.lean:83` |
| `SerrePositivity.intervalRingMap` | `SerrePositivity/CommutativeAlgebra/ValuationInterval/Basic.lean:92` |
| `SerrePositivity.valuationRing_interval` | `SerrePositivity/CommutativeAlgebra/ValuationInterval/Basic.lean:104` |
| `SerrePositivity.aic_interval` | `SerrePositivity/CommutativeAlgebra/ValuationInterval/Basic.lean:117` |
| `SerrePositivity.IsAbsolutelyIntegrallyClosed.primeResidue_isAlgClosed` | `SerrePositivity/CommutativeAlgebra/ValuationInterval/Basic.lean:122` |
| `SerrePositivity.perfectRing_interval` | `SerrePositivity/CommutativeAlgebra/ValuationInterval/Basic.lean:128` |
| `SerrePositivity.exists_primeAbove_not_mem` | `SerrePositivity/CommutativeAlgebra/ValuationInterval/Endpoint.lean:24` |
| `SerrePositivity.exists_primeBelow_mem` | `SerrePositivity/CommutativeAlgebra/ValuationInterval/Endpoint.lean:53` |
| `SerrePositivity.intervalAboveColimitIsoResidue` | `SerrePositivity/CommutativeAlgebra/ValuationInterval/Endpoint.lean:97` |
| `SerrePositivity.intervalBelowColimitIsoResidue` | `SerrePositivity/CommutativeAlgebra/ValuationInterval/Endpoint.lean:115` |
| `SerrePositivity.exists_intervalRingFactor_of_finitePresentation` | `SerrePositivity/CommutativeAlgebra/ValuationInterval/FinitePresentation.lean:42` |
| `SerrePositivity.valuationIntervalProperty_of_localExtensions` | `SerrePositivity/CommutativeAlgebra/ValuationInterval/Zorn.lean:99` |
| `SerrePositivity.Cech.isCechExact_of_retraction` | `SerrePositivity/HomologicalAlgebra/Cech/Split.lean:38` |
| `SerrePositivity.Cech.isCechExact_baseChange_iff` | `SerrePositivity/HomologicalAlgebra/Cech/BaseChange.lean:233` |
| `SerrePositivity.Cech.underCechInclusion` | `SerrePositivity/HomologicalAlgebra/Cech/BaseChange.lean:60` |
| `SerrePositivity.Cech.changeToTerm` | `SerrePositivity/HomologicalAlgebra/Cech/Composition.lean:54` |
| `SerrePositivity.Cech.isCechExact_iff_of_tensorCech` | `SerrePositivity/HomologicalAlgebra/Cech/Composition.lean:137` |
| `SerrePositivity.Cech.isCechExact_colimit` | `SerrePositivity/HomologicalAlgebra/Cech/Filtered.lean:99` |
| `SerrePositivity.perfectRing_tor_subsingleton_of_char_eq_zero` | `SerrePositivity/HomologicalAlgebra/PerfectRingTor.lean:74` |
| `SerrePositivity.subsingleton_of_ultraproduct_tensor` | `SerrePositivity/BhattScholze/Perfectoidization/Arc/Descent/ArcCechUltraproduct.lean:34` |
| `SerrePositivity.cechExact_of_ultraproducts` | `SerrePositivity/BhattScholze/Perfectoidization/Arc/Descent/ArcCechUltraproduct.lean:65` |
| `SerrePositivity.valuationRing_ultraproduct` | `SerrePositivity/CommutativeAlgebra/Ultraproduct/Basic.lean:58` |
| `SerrePositivity.aic_ultraproduct` | `SerrePositivity/CommutativeAlgebra/Ultraproduct/Basic.lean:95` |
| `SerrePositivity.perfectRing_ultraproduct_of_aic` | `SerrePositivity/CommutativeAlgebra/Ultraproduct/Basic.lean:101` |
| `SerrePositivity.BhattScholze.Perfectoidization.Arc.valuationRing_milnorSquare_perfect` | `SerrePositivity/BhattScholze/Perfectoidization/Arc/Valuations/ArcValuationMilnor.lean:87` |
| `SerrePositivity.BhattScholze.Perfectoidization.Arc.overlapModuleComplex_shortExact` | `SerrePositivity/BhattScholze/Perfectoidization/Arc/Milnor/ArcIntervalOverlap.lean:96` |
| `SerrePositivity.BhattScholze.Perfectoidization.Arc.shortExact_tensorLeft_of_tor` | `SerrePositivity/BhattScholze/Perfectoidization/Arc/Milnor/ArcMilnorTensor.lean:30` |
| `SerrePositivity.BhattScholze.Perfectoidization.Arc.acyclic_of_tensorShortExact` | `SerrePositivity/BhattScholze/Perfectoidization/Arc/Milnor/ArcMilnorDetection.lean:92` |
| `SerrePositivity.BhattScholze.Perfectoidization.Arc.tensorCochain_prod_acyclic` | `SerrePositivity/BhattScholze/Perfectoidization/Arc/Milnor/ArcMilnorDetection.lean:56` |
| `SerrePositivity.BhattScholze.Perfectoidization.Arc.tensorCochain_unitIso` | `SerrePositivity/BhattScholze/Perfectoidization/Arc/Milnor/ArcMilnorDetection.lean:105` |
| `SerrePositivity.BhattScholze.Perfectoidization.Arc.moduleCech_tor_subsingleton` | `SerrePositivity/BhattScholze/Perfectoidization/Arc/Milnor/ArcCechMilnor.lean:52` |
| `SerrePositivity.BhattScholze.Perfectoidization.Arc.cechExact_baseChange_iff_tensorCochain` | `SerrePositivity/BhattScholze/Perfectoidization/Arc/Milnor/ArcCechMilnor.lean:32` |
| `SerrePositivity.BhattScholze.Perfectoidization.Arc.cechExact_of_overlapTensor` | `SerrePositivity/BhattScholze/Perfectoidization/Arc/Descent/ArcCechOverlap.lean:29` |
| `SerrePositivity.BhattScholze.Perfectoidization.Arc.valuationProbe_aic` | `SerrePositivity/BhattScholze/Perfectoidization/Arc/Valuations/ArcValuationProduct.lean:66` |
| `SerrePositivity.BhattScholze.Perfectoidization.Arc.valuationProbeProductMap` | `SerrePositivity/BhattScholze/Perfectoidization/Arc/Valuations/ArcValuationProduct.lean:83` |
| `SerrePositivity.BhattScholze.Perfectoidization.Arc.valuationProbeProduct_vCover` | `SerrePositivity/BhattScholze/Perfectoidization/Arc/Valuations/ArcValuationProduct.lean:123` |
| `SerrePositivity.BhattScholze.Perfectoidization.Arc.valuationProbeProduct_perfectRing` | `SerrePositivity/BhattScholze/Perfectoidization/Arc/Valuations/ArcValuationProduct.lean:133` |
| `SerrePositivity.Cech.cechConerve_perfectRing` | `SerrePositivity/BhattScholze/Perfectoidization/Arc/Descent/ArcPerfectCech.lean:30` |
| `CommRingCat.tensorProd` | `.lake/packages/mathlib/Mathlib/Algebra/Category/Ring/Under/Basic.lean:127` |
| `CommRingCat.tensorProdIsoPushout` | `.lake/packages/mathlib/Mathlib/Algebra/Category/Ring/Under/Basic.lean:160` |
| `Algebra.TensorProduct.includeLeftRingHom` | `.lake/packages/mathlib/Mathlib/RingTheory/TensorProduct/Basic.lean:227` |
| `Algebra.TensorProduct.comm` | `.lake/packages/mathlib/Mathlib/RingTheory/TensorProduct/Maps.lean:374` |
| `Algebra.TensorProduct.assoc` | `.lake/packages/mathlib/Mathlib/RingTheory/TensorProduct/Maps.lean:443` |
| `IsLocalization.AtPrime.primeSpectrumOrderIso` | `.lake/packages/mathlib/Mathlib/RingTheory/Localization/AtPrime/Basic.lean:150` |
| `Ideal.primeSpectrumQuotientOrderIsoZeroLocus` | `.lake/packages/mathlib/Mathlib/RingTheory/Spectrum/Prime/RingHom.lean:265` |
| `Algebra.FiniteType.iff_quotient_mvPolynomial` | `.lake/packages/mathlib/Mathlib/RingTheory/FiniteType.lean:132` |
| `MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal` | `.lake/packages/mathlib/Mathlib/RingTheory/Nullstellensatz.lean:151` |

模型のfiltered性は `FinitePresentationModelFiltered.lean:41,45` の既存instance、代数閉剰余体は `IsAbsolutelyIntegrallyClosed.primeResidue_isAlgClosed`。IsAbsolutelyIntegrallyClosedはclassではなく明示的なProp引数として渡す。P03/P04は既存underCechInclusionの同じ第0因子であり、任意の構造射を新しく選ばない。

## 利用側と、解消するsorry

| 対象 | この段での扱い |
| --- | --- |
| drafts/A6/ArcSheafProperty.lean:117（sorry:121） `cech_exact_of_vCover_perfect`（G-A6-1a） | 2hの7971aefe8ですでに同じ型の供給を完成。2iではT06から使う。draft本体の無関係な証明は変更しない。 |
| drafts/A6/ArcSheafProperty.lean:196 `cech_exact_of_arcCover_perfect`（G-A6-1）と直後のsorry | B02で同じ量化・有限族・元の増大conerveの主張を供給し、このsorryを置き換えられる状態にする。2i完了時にこの型の接続を小さい検証で示す。 |
| drafts/A6/ArcRouteB.lean `ArcRouteBGoal` | この段の出口の正本。条件付きV01〜V06に残っているhBS17はT06で閉じ、正次数のhrowはP06で閉じる。最終定理の仮定には残さない。 |
| drafts/A6/ArcSheafProperty.lean `arcSheaf_of_vSheaf_of_valuationSquares`（G-A6-1b、BM18 Thm1.7） | 使わず、解消したとは数えない。一般の導来・∞値の判定法は作らない。 |
| `valuationRing_milnorSquare_perfect`（G-A6-1c） | 既存本体の入力として使う。O05/O06はその係数の短完全列・TorのAPIを使う。 |
| tilt・Witt・非affine・他のA6のsorry | この段の範囲外。 |

## 検証順の提案と停止

承認後の最初の束はDefinitions＋Uの法則、続いてMの指定模型とFrobenius完全化。次にQ/Iの点と区間、Oの三つの同型と普遍版、Pの普遍超積と正次数、最後にV/Bを組み立てる。署名DAGを先に守り、各新規ファイルの原稿の対象検証→同一バイト本体への移送→直接のimporter→別鍵の所有宣言の小さい監査、の順とする。鍵は --class impl --wait 3600、ビルドと監査の間で解放する。rootと下流全ビルドは調整役。

この段0では、型つき一覧・既存APIの所在・原典対応・DAG・補正した規模と危険箇所の紙までを提出した。**2iのLeanは追加していない。一覧：済み0／全体66（うち追加66）。** 指示書の明示的な停止点として、2iの経路・署名・外枠の検収までここで停止する。mainへの取り込みは行わない。


## 追加の照合・合成則（11-17夕の事前承認）

L01の完全な型・依存・原典上の位置・素と係数2の見込み・追加条件の確認は [照合法則の台帳](scheme-w1-2i-law-ledger.md)。元の66署名の型は不変。現在は67署名（うち追加1）、元の見積表は提出時の記録として保存する。


L02（環射とB1のUnderの底変換の指定Arrow比較）も同じ事前承認条件で[台帳](scheme-w1-2i-law-ledger.md)に記録。元の署名の型を変えず、現在68署名（うち追加2）。


既存の完全係数の構成の抽出L03・L04も[台帳](scheme-w1-2i-law-ledger.md)に記録。元の署名は不変、現在70署名（うち追加4）。


同じmoduleCechの係数検出の適用を分けるL05も[台帳](scheme-w1-2i-law-ledger.md)に記録。元の署名は不変、現在71署名（うち追加5）。


## 完了（11-17夜）

一覧：済み71／全体71（うち照合・分割の追加5）、未完0。本体・入口2,330行、検証用Leanを含め2,437行。出口と引き継ぎ・型の一致・対象ビルドと所有宣言監査は[最終報告](scheme-w1-2i-report.md)と[検証データ](scheme-w1-2i-verification.json)。2i完成で⑥を閉じる。
