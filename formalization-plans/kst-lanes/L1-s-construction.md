# K-L1：∞-S• 構成と連結 K

## 1. 目標・担当範囲

小さい安定 ∞ 圏 C の全 gapped 図式から S•C を構成し、core・実現・loop により連結 K を定義する。
反復 S• による連結スペクトル、加法性、π₀ と三角圏の Grothendieck 群の比較、dg 圏への適用までを証明する。
引用を証明の代用にせず、追加公理・sorry を使わない。条件付き成果を無条件の完成と数えない。

所有：`SerrePositivity/KST/SConstruction/`、namespace `SerrePositivity.KST.SConstruction`。
Core 公開名・型を変更しない。Stable（α-S）、F1 の core（α2）、Spectra（L9）、比較・plus（L2）は読み取り専用。

## 2. 原典・正本

- `k-theory-kst-route.md` §4 D1、§5 K1・K0、§6、§10-5・11・12・13、§13 決定2・5・9・12。
- `foundations.md`。非連結化の最終定義は BGT、暫定実装は Schlichting。非連結化は今回の範囲外。
- `L11-paper.md` §5・11・12・13・S1。特に以下の文言補正を採用する。
- BGT v4 Definition 7.1、Lemma 7.3、Remark 7.4（gapped と第一行）。
- Fiore–Pieper Lemma 4.24、Proposition 4.27、Theorem 4.35、Corollary 3.35（McCarthy 型加法性）。
- HTT 4.3.2.15（相対余極限拡張）、5.1.2.2（関手圏の点ごとの極限・双対）。

## 3. 工程

| 工程 | ファイル | 完了条件 |
| --- | --- | --- |
| L1a | Gapped.lean | Ar[n] と nerve、ihom、零対角・pushout 条件、充満部分単体集合 S_n、単体的関手性 |
| L1b | FirstRow.lean | 第一行制限、相対境界持ち上げ性、trivial Kan fibration |
| L1c | KSpace.lean | 各段の core、対角実現・Kan 置換・Ω、反復 S• と L9 BF スペクトルへの接続 |
| L1d | Additivity.lean | McCarthy 型ホモトピーによる実現後の加法性 |
| L1e | PiZero.lean | π₀ K(C) ≃+ TriangulatedK0(h C)、対象類と自然性 |
| L1f | DGApplication.lean | K(N_dg(Perf_dg D))、dg 関手性、Morita 不変性 |
| L1g | 別途指示 | fibration 定理、filtered 余極限、Bass、非連結化 |

## 4. 設計と実装前の文言

### Ar と gapped

Ar[n] は Fin(n+1) の対 (i,j), i≤j の成分ごとの順序の圏。
単調写像 θ:[m]→[n] は (i,j)↦(θi,θj) を誘導する。
図式圏は ihom(N Ar[n],C)。gapped は全対角 F(i,i) が零対象であり、
i≤j≤k≤l に対する F(i,k)→F(i,l), F(j,k)→F(j,l) の全四角が pushout となる条件。
S_n はこの頂点条件による充満部分単体集合。順序写像による前合成は条件を保つため、
選択を含まず Δᵒᵖ 上の単体的対象を与える。退化する四角にも同じ pushout 条件を課す。

### §10-13：gapped と第一行

原典の結論は Gap([n],C)→Fun(Δ^{1,…,n},C) の ∞ 圏の同値である。
これだけから literal な trivial Kan fibration と結論しない。
要求された元の制限写像について、有限個の相対 cocartesian completion を積み上げ、
零対象と余極限錐の相対境界持ち上げ性から全境界に対する RLP を証明する。
n=0 は零対象の空間として別処理する。全 gapped 図式を保ち、第一行の選択模型に置換しない。
不足する相対拡張補題は本レーン内で証明する。設計変更が必要なら実装前に提案する。
Ar[n] と正方形の積から (0,i),(0,j),(i,i),(i,j) への自然な添字写像を用い、
gapped 図式の全 cofiber 四角形を一つの族として取り出す。
その族は右上角の評価で元の図式を厳密に回収するため、境界上の既存データを保持できる。
相対 cofiber 補完をこの Ar[n] パラメーターに適用する際は、第一行と対角での条件を同時に固定する。
得られる右上角の図式の全四角形が押し出しとなることは、余極限の普遍性と押し出しの貼り合わせから
別に証明する。単に各区間に cofiber を持つことだけで gapped 条件を結論しない。
点ごとの余極限・押し出しを関手 ∞ 圏へ移す向きは、相対始点境界充填と内部 Hom の交換で証明する。
正次元のパラメーター境界では全頂点が指定されているため、境界を厳密に保つ補完の gapped 性は
全部分複体の頂点条件から回収できる。零次元の gapped 性および出力の第一行の厳密な回収は別条件として残す。

### §10-11：加法性

E(A,C,B) の cofiber 列から subobject・quotient への射について、
|core S•E|→|core S•A|×|core S•B| が同値となることを証明する。
E≃A×B という ∞ 圏レベルの誤った主張にはしない。
Fiore–Pieper の McCarthy 型の経路を用い、普遍的 cocartesian completion の制限自明
ファイブレーションでパラメータ付き pushout を選び、単体ホモトピー、単体積版 Quillen A、
対角実現、object/core 比較を証明する。Waldhausen の元の証明からの経路変更を明記する。

### §10-12：最小 fibration 定理（後続 L1g の仕様）

C 安定、D thick、W={f | cofib(f)∈D}。W の2-out-of-3・pushout・extension 安定性が必要。
∞ 局所化と dg 商の比較には mapping 空間の比較まで要求し、H⁰ の Verdier 普遍性で代用しない。
冪等完備化は K₀ を変えるため、連結 K の局所化を全冪等完備 Verdier 列に無条件では課さない。
最終的な非連結 K(D)→K(C)→K((C/D)^idem) の fiber 列へは、必要な cofinality 条件を明示した
連結版と Schlichting suspension を経由する。L11 では ∞ 版全体は未検証である。
今回の L1a–f の成果としてこの定理を完成扱いしない。

### K と界面

L9 の基点・Ω・π_* の座標に従う。BF 模型は単射 ΣX_n→X_(n+1) と、随伴の全基点 π_* 同型。
厳密な Ω 同型を要求しない。未着 API は明示的な入力として隔離し、証明済みの構成と区別する。
π₀ は一般 dg 圏の H⁰D でなく、小さい Perf の H⁰ の TriangulatedK0 と比較する。
S4 未着時は cofiber 列の像が distinguished triangle になる仮定を明記する。
相対 K は L9 のスペクトル fiber を優先し、次数ごとの kernel/cokernel から復元しない。
Kₙ の境界・比較同型は自然性と対象類の式を含む。宇宙は S1.1 に従い小さい模型にそろえる。

## 5. 検証・保存

各保存単位で `lake build SerrePositivity.KST.SConstruction` と
`lake env lean scripts/audit_kst_s_construction.lean` を実行する。
公開宣言を #check / #print axioms で監査し、許可するのは propext、Classical.choice、Quot.sound のみ。
全体ビルドは工程の区切りで行う。自分の import 閉包外の並行作業の失敗は記録して続ける。
自分の検証済みファイルだけを保存し、経緯はコミットメッセージに記す。

## 6. 現在地・主要宣言

**L1a・L1b 完了。L1c が次工程。L1d–f 未完了、L1g は別途指示待ち。**
L1b は元の全 gapped 図式の制限写像そのものについて、全次数・全境界の RLP を証明した。
追加の存在仮定や出力の gapped 性の仮定は残っていない。

### 6.1 S• の構成

以下で `C : SSet.{u}`、`m,n,l : ℕ`。`Ar n : Type u` は `i≤j` の対の成分順序圏。

| 公開宣言 | 正確な型・前提 |
| --- | --- |
| `arNerve` | `(n : ℕ) → SSet.{u}` |
| `arMap` | `(Fin (m+1) →o Fin (n+1)) → (Ar m →o Ar n)` |
| `arNerveMap` | `(θ : Fin (m+1) →o Fin (n+1)) → (arNerve m ⟶ arNerve n)` |
| `diagramSpace` | `(n : ℕ) → (C : SSet.{u}) → SSet.{u}`、値は `(ihom (arNerve n)).obj C` |
| `IsGapped` | `(F : arNerve n ⟶ C) → Prop`、全対角が零頂点で、全弱不等式 `i≤j≤k≤l` の `arSquare i j k l ≫ F` が押し出し |
| `IsGapped.precomp` | `IsGapped F → (θ : Fin (m+1) →o Fin (n+1)) → IsGapped (arNerveMap θ ≫ F)` |
| `gappedSubcomplex` | `(n : ℕ) → (C : SSet.{u}) → (diagramSpace n C).Subcomplex` |
| `sConstruction` | `(n : ℕ) → (C : SSet.{u}) → SSet.{u}` |
| `sConstruction_quasicategory` | `[Quasicategory C] → Quasicategory (sConstruction n C)` |
| `sMap` | `(C : SSet.{u}) → (θ : Fin (m+1) →o Fin (n+1)) → (sConstruction n C ⟶ sConstruction m C)` |
| `sMap_id` | `sMap C OrderHom.id = 𝟙 (sConstruction n C)` |
| `sMap_comp` | `sMap C (φ.comp θ) = sMap C φ ≫ sMap C θ` |
| `simplicialSConstruction` | `(C : SSet.{u}) → (SimplexCategoryᵒᵖ ⥤ SSet.{u})` |

### 6.2 第一行と選択空間

| 公開宣言 | 正確な型・前提 |
| --- | --- |
| `firstRowNerve` | `(n : ℕ) → SSet.{u}`、値は `nerve (ULift (Fin n))` |
| `firstRowRestriction` | `(n : ℕ) → (C : SSet.{u}) → (sConstruction n C ⟶ (ihom (firstRowNerve n)).obj C)` |
| `firstRowSimplexIso` | `(n : ℕ) → ((Δ[n] : SSet.{u}) ≅ firstRowNerve (n+1))` |
| `exists_gapped_extension_of_zeroFrame` | `{n : ℕ} → {C : SSet.{u}} → [Quasicategory C] → [IsStable C] → (F : frameNerve n ⟶ C) → IsZeroFrameVertex (functorVertex F) → ∃ G : arNerve n ⟶ C, IsGapped G ∧ frameInclusion n ≫ G = F` |
| `exists_gapped_with_firstRow` | `(n : ℕ) → (C : SSet.{u}) → [Quasicategory C] → [IsStable C] → (p : firstRowNerve n ⟶ C) → ∃ G : arNerve n ⟶ C, IsGapped G ∧ firstRowInclusion n ≫ G = p` |
| `firstRowRestriction_vertex_surjective` | `(n : ℕ) → (C : SSet.{u}) → [Quasicategory C] → [IsStable C] → Function.Surjective ((firstRowRestriction n C).app (Opposite.op ⦋0⦌))` |
| `firstRowRestriction_hasLiftingProperty_boundary` | `(n r : ℕ) → (C : SSet.{u}) → [Quasicategory C] → [IsStable C] → HasLiftingProperty (boundary (r+1)).ι (firstRowRestriction n C)` |
| `firstRowRestriction_trivialKanFibration` | `(n : ℕ) → (C : SSet.{u}) → [Quasicategory C] → [IsStable C] → TrivialKanFibration (firstRowRestriction n C)` |
| `firstRowEquivalence` | `(n : ℕ) → (C : SSet.{u}) → [Quasicategory C] → [IsStable C] → QCatEquivalence (sConstruction n C) ((ihom (firstRowNerve n)).obj C)` |
| `firstRowRestriction_vertexFiber_isContractibleKan` | `(n : ℕ) → (C : SSet.{u}) → [Quasicategory C] → [IsStable C] → (d : ((ihom (firstRowNerve n)).obj C) _⦋0⦌) → IsContractibleKan (vertexFiber (firstRowRestriction n C) d)` |

正次元は全頂点が境界で指定されることと、枠を保つ相対 cofiber 補完を使う。
零次元は零対角の枠を、零射を含む全 span を固定して補完する。
補完後の右上角の実際の図式の普遍性を、選んだ cofiber 正方形の普遍性と取り違えない。
その接続は以下の比較を通じて証明している。

- `D` は `arCofiberUnitSquare`、`T` は `arCofiberComparisonSquare`、`U` は `arCofiberComparisonUnitSquare`。
- 内部横座標の prism は `T→U`。左側は対角の枠の恒等辺、右側は形状自体が定値。
- 区間の第二端点の prism は `T→H(a)`。左側は固定 span の左辺、右側は定値。
- 区間の第一端点の prism は `D→U`。下側は固定 span の第一辺の終点、上側は定値。
- 全ての縦辺が恒等なので、三つを合成して `D≅H(a)` を得る。
- `cofiberFamilyUnitComparisonIso` の `D≅標準抽出` と合わせ、選んだ正方形の押し出し性を標準抽出へ移す。
- `isGapped_iff_originSquares` の横・縦の相殺から、全四つ組の押し出し性を得る。

この普遍性の移送は quasicategory 性だけを使う。
安定性は零対象と cofiber の存在を通じ、枠を補完する段階にだけ必要である。

### 6.3 完成に用いる公開宣言の正確なヘッダー

以下は namespace `SerrePositivity.KST.SConstruction`、`universe u`、
`open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet`、
`open SerrePositivity.InfinityCategories`、`open scoped Simplicial` の下の宣言ヘッダー。
本文を除いて掲載する。既存の補助 API を含む全公開型は監査スクリプトの `#check` でも検査する。

**CofiberComparisonPrisms.lean**

```text
def squareHorizontalPrism : (Δ[1] : SSet.{u}) ⊗ (Δ[1] ⊗ Δ[1]) ⟶ Δ[1] ⊗ Δ[1]

def squareVerticalPrism : (Δ[1] : SSet.{u}) ⊗ (Δ[1] ⊗ Δ[1]) ⟶ Δ[1] ⊗ Δ[1]

def cofiberTopCorner : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ Δ[1] ⊗ Δ[1]

lemma squareHorizontalPrism_zero :
    prismEndpoint 0 (Δ[1] ⊗ Δ[1] : SSet.{u}) ≫ squareHorizontalPrism = 𝟙 _

lemma squareHorizontalPrism_one :
    prismEndpoint 1 (Δ[1] ⊗ Δ[1] : SSet.{u}) ≫ squareHorizontalPrism = cofiberUnitCorner

lemma squareVerticalPrism_zero :
    prismEndpoint 0 (Δ[1] ⊗ Δ[1] : SSet.{u}) ≫ squareVerticalPrism = 𝟙 _

lemma squareVerticalPrism_one :
    prismEndpoint 1 (Δ[1] ⊗ Δ[1] : SSet.{u}) ≫ squareVerticalPrism = cofiberTopCorner

def arFixedStartSquare {n : ℕ} (a : Ar.{u} n) : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ arNerve n

def arCofiberComparisonSquare {n : ℕ} (a : Ar.{u} n) :
    (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ arNerve n ⊗ (Δ[1] ⊗ Δ[1])

def arCofiberComparisonUnitSquare {n : ℕ} (a : Ar.{u} n) :
    (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ arNerve n ⊗ (Δ[1] ⊗ Δ[1])

def arCofiberHorizontalPrism {n : ℕ} (a : Ar.{u} n) :
    (Δ[1] : SSet.{u}) ⊗ (Δ[1] ⊗ Δ[1]) ⟶ arNerve n ⊗ (Δ[1] ⊗ Δ[1])

def arCofiberTargetPrism {n : ℕ} (a : Ar.{u} n) :
    (Δ[1] : SSet.{u}) ⊗ (Δ[1] ⊗ Δ[1]) ⟶ arNerve n ⊗ (Δ[1] ⊗ Δ[1])

def arCofiberSourcePrism {n : ℕ} (a : Ar.{u} n) :
    (Δ[1] : SSet.{u}) ⊗ (Δ[1] ⊗ Δ[1]) ⟶ arNerve n ⊗ (Δ[1] ⊗ Δ[1])

lemma arFixedStartSquare_unitCorner {n : ℕ} (a : Ar.{u} n) :
    cofiberUnitCorner ≫ arFixedStartSquare a = SSet.const (ComposableArrows.mk₀ a)

lemma arSquare_topCorner {n : ℕ} (a : Ar.{u} n) :
    cofiberTopCorner ≫ arSquare 0 a.down.val.1 a.down.val.1 a.down.val.2
      (Fin.zero_le _) le_rfl a.down.property = arFixedStartSquare a

lemma arCofiberHorizontalPrism_zero {n : ℕ} (a : Ar.{u} n) :
    prismEndpoint 0 (Δ[1] ⊗ Δ[1] : SSet.{u}) ≫ arCofiberHorizontalPrism a =
      arCofiberComparisonSquare a

lemma arCofiberHorizontalPrism_one {n : ℕ} (a : Ar.{u} n) :
    prismEndpoint 1 (Δ[1] ⊗ Δ[1] : SSet.{u}) ≫ arCofiberHorizontalPrism a =
      arCofiberComparisonUnitSquare a

lemma arCofiberTargetPrism_zero {n : ℕ} (a : Ar.{u} n) :
    prismEndpoint 0 (Δ[1] ⊗ Δ[1] : SSet.{u}) ≫ arCofiberTargetPrism a =
      arCofiberComparisonSquare a

lemma arCofiberTargetPrism_one {n : ℕ} (a : Ar.{u} n) :
    prismEndpoint 1 (Δ[1] ⊗ Δ[1] : SSet.{u}) ≫ arCofiberTargetPrism a =
      lift (SSet.const (ComposableArrows.mk₀ a)) (𝟙 _)

lemma arCofiberSourcePrism_zero {n : ℕ} (a : Ar.{u} n) :
    prismEndpoint 0 (Δ[1] ⊗ Δ[1] : SSet.{u}) ≫ arCofiberSourcePrism a =
      arCofiberUnitSquare a

lemma arCofiberSourcePrism_one {n : ℕ} (a : Ar.{u} n) :
    prismEndpoint 1 (Δ[1] ⊗ Δ[1] : SSet.{u}) ≫ arCofiberSourcePrism a =
      arCofiberComparisonUnitSquare a
```

**CofiberComparisonEdges.lean**

```text
def squareVertexLine (x y : Fin 2) : (Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ (Δ[1] ⊗ Δ[1])

lemma arCofiberHorizontalPrism_left {n : ℕ} (a : Ar.{u} n) (y : Fin 2) :
    squareVertexLine 0 y ≫ arCofiberHorizontalPrism a =
      lift (SSet.const (ComposableArrows.mk₀
        (⟨arObj a.down.val.1 a.down.val.1 le_rfl, Or.inr rfl⟩ : FrameAr n)))
        (lift (𝟙 (Δ[1] : SSet.{u})) (SSet.const (stdSimplex.obj₀Equiv.symm y))) ≫
          (frameInclusion n ▷ (Δ[1] ⊗ Δ[1] : SSet.{u}))

lemma arCofiberHorizontalPrism_right {n : ℕ} (a : Ar.{u} n) (y : Fin 2) :
    squareVertexLine 1 y ≫ arCofiberHorizontalPrism a =
      SSet.const (ComposableArrows.mk₀ a,
        (stdSimplex.obj₀Equiv.symm (1 : Fin 2), stdSimplex.obj₀Equiv.symm y))

lemma arCofiberTargetPrism_left {n : ℕ} (a : Ar.{u} n) (y : Fin 2) :
    squareVertexLine 0 y ≫ arCofiberTargetPrism a =
      lift (squareBottomEdge ≫ arFixedStartSquare a)
        (SSet.const (stdSimplex.obj₀Equiv.symm y)) ≫
          (arNerve n ◁ squareLeftEdge)

lemma arCofiberTargetPrism_right {n : ℕ} (a : Ar.{u} n) (y : Fin 2) :
    squareVertexLine 1 y ≫ arCofiberTargetPrism a =
      SSet.const (ComposableArrows.mk₀ a,
        (stdSimplex.obj₀Equiv.symm (1 : Fin 2), stdSimplex.obj₀Equiv.symm y))

lemma arCofiberSourcePrism_lower {n : ℕ} (a : Ar.{u} n) (x : Fin 2) :
    squareVertexLine x 0 ≫ arCofiberSourcePrism a =
      lift ((lift (SSet.const (stdSimplex.obj₀Equiv.symm x)) (𝟙 (Δ[1] : SSet.{u}))) ≫
        arSquare 0 a.down.val.1 a.down.val.1 a.down.val.2 (Fin.zero_le _) le_rfl a.down.property)
        (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) ≫
          (arNerve n ◁ squareBottomEdge)

lemma arCofiberSourcePrism_upper {n : ℕ} (a : Ar.{u} n) (x : Fin 2) :
    squareVertexLine x 1 ≫ arCofiberSourcePrism a =
      SSet.const (ComposableArrows.mk₀
        (arObj a.down.val.1 (intervalStep a.down.val.1 a.down.val.2 a.down.property x)
          (le_intervalStep _ _ _ _)),
        (stdSimplex.obj₀Equiv.symm (1 : Fin 2), stdSimplex.obj₀Equiv.symm (1 : Fin 2)))

lemma frameCofiberSquareMap_diagonal_horizontal {n : ℕ} (i : Fin (n + 1)) (y : Fin 2) :
    lift (SSet.const (ComposableArrows.mk₀
      (⟨arObj i i le_rfl, Or.inr rfl⟩ : FrameAr.{u} n)))
      (lift (𝟙 (Δ[1] : SSet.{u})) (SSet.const (stdSimplex.obj₀Equiv.symm y))) ≫
        frameCofiberSquareMap n =
      SSet.const (ComposableArrows.mk₀
        (arCofiberZeroInputOrder n (arObj i i le_rfl, ULift.up y)))

lemma arCofiberZeroInputMap_fixedStart {n : ℕ} (a : Ar.{u} n) (y : Fin 2) :
    lift (squareBottomEdge ≫ arFixedStartSquare a)
      (SSet.const (stdSimplex.obj₀Equiv.symm y)) ≫ arCofiberZeroInputMap n =
      SSet.const (ComposableArrows.mk₀ (arCofiberZeroInputOrder n (a, ULift.up y)))

lemma arCofiberInputMap_fixedTarget {n : ℕ} (a : Ar.{u} n) (x : Fin 2) :
    lift ((lift (SSet.const (stdSimplex.obj₀Equiv.symm x)) (𝟙 (Δ[1] : SSet.{u}))) ≫
      arSquare 0 a.down.val.1 a.down.val.1 a.down.val.2 (Fin.zero_le _) le_rfl a.down.property)
      (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) ≫ arCofiberInputMap n =
      SSet.const (ComposableArrows.mk₀
        (⟨arObj 0 (intervalStep a.down.val.1 a.down.val.2 a.down.property x) (Fin.zero_le _),
          Or.inl rfl⟩ : FrameAr n))
```

**CofiberComparisonIsos.lean**

```text
def functorIsoOfSquareConstantPrism {C : SSet.{u}} [Quasicategory C]
    (P : (Δ[1] : SSet.{u}) ⊗ (Δ[1] ⊗ Δ[1]) ⟶ C)
    (h : ∀ x y : Fin 2, ∃ z : C _⦋0⦌, squareVertexLine x y ≫ P = SSet.const z) :
    FunctorIso (prismEndpoint 0 (Δ[1] ⊗ Δ[1] : SSet.{u}) ≫ P)
      (prismEndpoint 1 (Δ[1] ⊗ Δ[1] : SSet.{u}) ≫ P)

lemma arCofiberHorizontalPrism_constant {n : ℕ} {C : SSet.{u}}
    (E : arNerve n ⊗ (Δ[1] ⊗ Δ[1]) ⟶ C) (F : frameNerve n ⟶ C)
    (h : (frameInclusion n ▷ (Δ[1] ⊗ Δ[1] : SSet.{u})) ≫ E = frameCofiberSquareMap n ≫ F)
    (a : Ar.{u} n) (x y : Fin 2) :
    ∃ z : C _⦋0⦌, squareVertexLine x y ≫ (arCofiberHorizontalPrism a ≫ E) = SSet.const z

lemma arCofiberTargetPrism_constant {n : ℕ} {C : SSet.{u}}
    (E : arNerve n ⊗ (Δ[1] ⊗ Δ[1]) ⟶ C) (F : frameNerve n ⟶ C)
    (h : (arNerve n ◁ squareLeftEdge) ≫ E = arCofiberZeroInputMap n ≫ F)
    (a : Ar.{u} n) (x y : Fin 2) :
    ∃ z : C _⦋0⦌, squareVertexLine x y ≫ (arCofiberTargetPrism a ≫ E) = SSet.const z

lemma arCofiberSourcePrism_constant {n : ℕ} {C : SSet.{u}}
    (E : arNerve n ⊗ (Δ[1] ⊗ Δ[1]) ⟶ C) (F : frameNerve n ⟶ C)
    (h : (arNerve n ◁ squareBottomEdge) ≫ E = arCofiberInputMap n ≫ F)
    (a : Ar.{u} n) (x y : Fin 2) :
    ∃ z : C _⦋0⦌, squareVertexLine x y ≫ (arCofiberSourcePrism a ≫ E) = SSet.const z

def arCofiberHorizontalComparisonIso {n : ℕ} {C : SSet.{u}} [Quasicategory C]
    (E : arNerve n ⊗ (Δ[1] ⊗ Δ[1]) ⟶ C) (F : frameNerve n ⟶ C)
    (h : (frameInclusion n ▷ (Δ[1] ⊗ Δ[1] : SSet.{u})) ≫ E = frameCofiberSquareMap n ≫ F)
    (a : Ar.{u} n) :
    FunctorIso (arCofiberComparisonSquare a ≫ E) (arCofiberComparisonUnitSquare a ≫ E)

def arCofiberTargetComparisonIso {n : ℕ} {C : SSet.{u}} [Quasicategory C]
    (E : arNerve n ⊗ (Δ[1] ⊗ Δ[1]) ⟶ C) (F : frameNerve n ⟶ C)
    (h : (arNerve n ◁ squareLeftEdge) ≫ E = arCofiberZeroInputMap n ≫ F)
    (a : Ar.{u} n) :
    FunctorIso (arCofiberComparisonSquare a ≫ E)
      (lift (SSet.const (ComposableArrows.mk₀ a)) (𝟙 (Δ[1] ⊗ Δ[1] : SSet.{u})) ≫ E)

def arCofiberSourceComparisonIso {n : ℕ} {C : SSet.{u}} [Quasicategory C]
    (E : arNerve n ⊗ (Δ[1] ⊗ Δ[1]) ⟶ C) (F : frameNerve n ⟶ C)
    (h : (arNerve n ◁ squareBottomEdge) ≫ E = arCofiberInputMap n ≫ F)
    (a : Ar.{u} n) :
    FunctorIso (arCofiberUnitSquare a ≫ E) (arCofiberComparisonUnitSquare a ≫ E)

def arCofiberSelectedSquareComparisonIso {n : ℕ} {C : SSet.{u}} [Quasicategory C]
    (E : arNerve n ⊗ (Δ[1] ⊗ Δ[1]) ⟶ C) (F : frameNerve n ⟶ C)
    (hframe : (frameInclusion n ▷ (Δ[1] ⊗ Δ[1] : SSet.{u})) ≫ E = frameCofiberSquareMap n ≫ F)
    (hleft : (arNerve n ◁ squareLeftEdge) ≫ E = arCofiberZeroInputMap n ≫ F)
    (hbottom : (arNerve n ◁ squareBottomEdge) ≫ E = arCofiberInputMap n ≫ F)
    (a : Ar.{u} n) :
    FunctorIso (arCofiberUnitSquare a ≫ E)
      (lift (SSet.const (ComposableArrows.mk₀ a)) (𝟙 (Δ[1] ⊗ Δ[1] : SSet.{u})) ≫ E)

def arCofiberCanonicalSquareComparisonIso {n : ℕ} {C : SSet.{u}} [Quasicategory C]
    (E : arNerve n ⊗ (Δ[1] ⊗ Δ[1]) ⟶ C) (F : frameNerve n ⟶ C)
    (hframe : (frameInclusion n ▷ (Δ[1] ⊗ Δ[1] : SSet.{u})) ≫ E = frameCofiberSquareMap n ≫ F)
    (hleft : (arNerve n ◁ squareLeftEdge) ≫ E = arCofiberZeroInputMap n ≫ F)
    (hbottom : (arNerve n ◁ squareBottomEdge) ≫ E = arCofiberInputMap n ≫ F)
    (a : Ar.{u} n) :
    FunctorIso
      (arSquare 0 a.down.val.1 a.down.val.1 a.down.val.2 (Fin.zero_le _) le_rfl a.down.property ≫
        lift (𝟙 (arNerve n)) (SSet.const
          (stdSimplex.obj₀Equiv.symm (1 : Fin 2), stdSimplex.obj₀Equiv.symm (1 : Fin 2))) ≫ E)
      (lift (SSet.const (ComposableArrows.mk₀ a)) (𝟙 (Δ[1] ⊗ Δ[1] : SSet.{u})) ≫ E)
```

**CofiberCompletionGapped.lean**

```text
def arSquareFamilyApex {n : ℕ} {C : SSet.{u}}
    (E : arNerve n ⊗ (Δ[1] ⊗ Δ[1]) ⟶ C) : arNerve n ⟶ C

lemma arSquareFamilyApex_frame {n : ℕ} {C : SSet.{u}}
    (E : arNerve n ⊗ (Δ[1] ⊗ Δ[1]) ⟶ C) (F : frameNerve n ⟶ C)
    (h : (frameInclusion n ▷ (Δ[1] ⊗ Δ[1] : SSet.{u})) ≫ E = frameCofiberSquareMap n ≫ F) :
    frameInclusion n ≫ arSquareFamilyApex E = F

lemma isGapped_arSquareFamilyApex {n : ℕ} {C : SSet.{u}} [Quasicategory C]
    (E : arNerve n ⊗ (Δ[1] ⊗ Δ[1]) ⟶ C) (F : frameNerve n ⟶ C)
    (hF : IsZeroFrameVertex (functorVertex F))
    (hframe : (frameInclusion n ▷ (Δ[1] ⊗ Δ[1] : SSet.{u})) ≫ E = frameCofiberSquareMap n ≫ F)
    (hleft : (arNerve n ◁ squareLeftEdge) ≫ E = arCofiberZeroInputMap n ≫ F)
    (hbottom : (arNerve n ◁ squareBottomEdge) ≫ E = arCofiberInputMap n ≫ F)
    (hpushout : ∀ a : Ar.{u} n, IsPushoutSquare
      (lift (SSet.const (ComposableArrows.mk₀ a)) (𝟙 (Δ[1] ⊗ Δ[1] : SSet.{u})) ≫ E)) :
    IsGapped (arSquareFamilyApex E)
```

**FixedSpanCofiberGapped.lean**

```text
lemma arSquareFamilyDiagram_span {n : ℕ} {C : SSet.{u}}
    (H : arNerve n ⟶ (ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj C) (F : frameNerve n ⟶ C)
    (h : H ≫ (pre spanSquareBoundary).app C = frameCofiberSpanFamily F) :
    (arNerve n ◁ spanSquareBoundary) ≫ arSquareFamilyDiagram H = arCofiberSpanMap n ≫ F

lemma arSquareFamilyDiagram_left {n : ℕ} {C : SSet.{u}}
    (H : arNerve n ⟶ (ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj C) (F : frameNerve n ⟶ C)
    (h : H ≫ (pre spanSquareBoundary).app C = frameCofiberSpanFamily F) :
    (arNerve n ◁ squareLeftEdge) ≫ arSquareFamilyDiagram H = arCofiberZeroInputMap n ≫ F

lemma arSquareFamilyDiagram_bottom {n : ℕ} {C : SSet.{u}}
    (H : arNerve n ⟶ (ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj C) (F : frameNerve n ⟶ C)
    (h : H ≫ (pre spanSquareBoundary).app C = frameCofiberSpanFamily F) :
    (arNerve n ◁ squareBottomEdge) ≫ arSquareFamilyDiagram H = arCofiberInputMap n ≫ F

lemma arSquareFamilyDiagram_at {n : ℕ} {C : SSet.{u}}
    (H : arNerve n ⟶ (ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj C) (a : Ar.{u} n) :
    lift (SSet.const (ComposableArrows.mk₀ a)) (𝟙 (Δ[1] ⊗ Δ[1] : SSet.{u})) ≫
      arSquareFamilyDiagram H =
        (functorVertexEquiv (Δ[1] ⊗ Δ[1] : SSet.{u}) C).symm
          (H.app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ a))

lemma isGapped_cofiberFamily_of_fixed_span {n : ℕ} {C : SSet.{u}} [Quasicategory C]
    (H : arNerve n ⟶ cofiberDiagrams C) (F : frameNerve n ⟶ C)
    (hF : IsZeroFrameVertex (functorVertex F))
    (hframe : frameInclusion n ≫ H = zeroFrameCofiberFamily F hF)
    (hspan : H ≫ cofiberSpan C = frameCofiberSpanFamily F) :
    IsGapped (H ≫ cofiberApex C)
```

**FrameSpanExtension.lean**

```text
lemma frameCofiberFamily_span {n : ℕ} {C : SSet.{u}} (F : frameNerve n ⟶ C) :
    frameCofiberFamily F ≫ (pre spanSquareBoundary).app C =
      frameInclusion n ≫ frameCofiberSpanFamily F

lemma exists_cofiberFamily_of_zeroFrame {n : ℕ} {C : SSet.{u}} [Quasicategory C] [IsStable C]
    (F : frameNerve n ⟶ C) (hF : IsZeroFrameVertex (functorVertex F)) :
    ∃ H : arNerve n ⟶ cofiberDiagrams C,
      frameInclusion n ≫ H = zeroFrameCofiberFamily F hF ∧
      H ≫ cofiberSpan C = frameCofiberSpanFamily F

lemma exists_gapped_extension_of_zeroFrame {n : ℕ} {C : SSet.{u}}
    [Quasicategory C] [IsStable C]
    (F : frameNerve n ⟶ C) (hF : IsZeroFrameVertex (functorVertex F)) :
    ∃ G : arNerve n ⟶ C, IsGapped G ∧ frameInclusion n ≫ G = F
```

**FirstRowFibration.lean**

```text
lemma zeroFrameVertex_of_zero_diagonal {n : ℕ} {C : SSet.{u}} (F : arNerve n ⟶ C)
    (hz : ∀ i : Fin (n + 1), IsZeroVertex (F.app (Opposite.op ⦋0⦌)
      (ComposableArrows.mk₀ (arObj i i le_rfl)))) :
    IsZeroFrameVertex (functorVertex (frameInclusion n ≫ F))

lemma exists_gapped_with_firstRow (n : ℕ) (C : SSet.{u}) [Quasicategory C] [IsStable C]
    (p : firstRowNerve n ⟶ C) :
    ∃ G : arNerve n ⟶ C, IsGapped G ∧ firstRowInclusion n ≫ G = p

lemma firstRowRestriction_vertex_surjective (n : ℕ) (C : SSet.{u})
    [Quasicategory C] [IsStable C] :
    Function.Surjective ((firstRowRestriction n C).app (Opposite.op ⦋0⦌))

instance firstRowRestriction_trivialKanFibration (n : ℕ) (C : SSet.{u})
    [Quasicategory C] [IsStable C] : TrivialKanFibration (firstRowRestriction n C)

def firstRowEquivalence (n : ℕ) (C : SSet.{u}) [Quasicategory C] [IsStable C] :
    QCatEquivalence (sConstruction n C) ((ihom (firstRowNerve n)).obj C)

lemma firstRowRestriction_vertexFiber_isContractibleKan (n : ℕ) (C : SSet.{u})
    [Quasicategory C] [IsStable C] (d : ((ihom (firstRowNerve n)).obj C) _⦋0⦌) :
    IsContractibleKan (vertexFiber (firstRowRestriction n C) d)
```

### 6.4 検証と残件

対象ビルド・標準三公理のみの監査を保存前に実施する。工程区切りの全体ビルドも一度実行する。
その結果は以下に記す。

L1c–f は未完了。次は各 S_n の core、単体的 Kan 複体、対角実現と Kan 置換、L9 の Ω と BF 模型への接続。
L9 の未着 API を使う箇所だけ明示的な入力として扱い、K 理論の主張を仮定で置き換えない。
L1d の加法性、L1e の π₀、L1f の dg 関手性と Morita 不変性はその後の工程。
L1g は別途指示待ち。

保存前の検証結果：

- `lake build SerrePositivity.KST.SConstruction` 成功（2099 jobs）。
- `lake env lean scripts/audit_kst_s_construction.lean` 成功（460 宣言）。全宣言は `propext`、`Classical.choice`、`Quot.sound` の範囲内。
- 工程区切りの `lake build` 成功（10632 jobs）。
- `git diff --check` 成功。追加公理・sorry なし。

L1c に向けた読取確認：α2 の `quasicategoryCoreFunctor`、L9 の `KanSequence`、
`KanSequence.OmegaCondition`、`KanSequence.toOmegaSpectrum` が存在する。
BF の構造射は `suspension (level n).space ⟶ (level (n+1)).space`、完成した模型への束ね直しは
構造射の単射性と随伴射の全基点での `KanPiIsomorphism` を要求する。
これらは他レーンの API として読み取り専用で使い、証明なしの入力で L1c の完成を主張しない。
