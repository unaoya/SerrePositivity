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

**L1a・L1b 完了。L1c 進行中（空間模型・零対象比較・後合成・有限反復対象と零方向の可縮性、関手圏・S_n・有限反復の安定性まで実装済み）。L1d–f 未完了、L1g は別途指示待ち。**
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

L1c は各 S_n の core、単体的 Kan 複体、点つき対角実現、Kan 置換と L9 の Ω による空間模型まで実装済み。
実現の連結性と零対象の選択による K 空間の π_* 同型比較も証明済み。
次は反復 S• の構造写像、delooping と Ω 条件、BF 模型への接続および比較の高次整合性。
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

### 6.5 L1c：単体的 Kan core と K 空間

`coreSConstruction n C` は α2 の `quasicategoryCore (sConstruction n C)`。
`simplicialCoreSConstruction`は S• と α2 の core 関手の合成である。
各段の Kan 性は C の quasicategory 性から証明され、安定性を要求しない。
零図式は全ての単体作用で厳密に保たれ、点つき単体集合への関手にも束ねた。
`diagonalCoreSConstruction C` の n 単体は `(ιS_n C)_n` で、射は外側と内側の二つの単体作用の合成。
この対角を実現模型とし、L9 の点つき Kan 置換と Ω を使って `kSpace C` を定義した。
零対象の選択は既存の `chosenZeroVertex C` を使う。

`kanCoreIso` は Kan 複体とその core の比較同型を本レーン内で構成する補題であり、α2 の公開 API を変更しない。
これにより `coreSConstruction 0 C` の可縮 Kan 性を証明した。

以下は namespace・universe・open 宣言を §6.3 と同じとした公開ヘッダー（本文を除く）。

**CoreSimplicial.lean**

```text
def coreSConstruction (n : ℕ) (C : SSet.{u}) : SSet.{u}

instance coreSConstruction_kanComplex (n : ℕ) (C : SSet.{u}) [Quasicategory C] :
    KanComplex (coreSConstruction n C)

def coreSMap {m n : ℕ} (C : SSet.{u}) (θ : Fin (m + 1) →o Fin (n + 1)) :
    coreSConstruction n C ⟶ coreSConstruction m C

def simplicialCoreSConstruction (C : SSet.{u}) : SimplexCategoryᵒᵖ ⥤ SSet.{u}

instance simplicialCoreSConstruction_obj_kanComplex (C : SSet.{u}) [Quasicategory C]
    (n : SimplexCategoryᵒᵖ) : KanComplex ((simplicialCoreSConstruction C).obj n)

def coreSConstructionZeroVertex (n : ℕ) {C : SSet.{u}} [Quasicategory C]
    (z : C _⦋0⦌) (hz : IsZeroVertex z) : (coreSConstruction n C) _⦋0⦌

lemma coreSMap_zeroVertex {m n : ℕ} {C : SSet.{u}} [Quasicategory C]
    (θ : Fin (m + 1) →o Fin (n + 1)) (z : C _⦋0⦌) (hz : IsZeroVertex z) :
    (coreSMap C θ).app (Opposite.op ⦋0⦌) (coreSConstructionZeroVertex n z hz) =
      coreSConstructionZeroVertex m z hz

def diagonalCoreSConstruction (C : SSet.{u}) : SSet.{u}

lemma diagonalCoreSConstruction_obj (C : SSet.{u}) (n : SimplexCategoryᵒᵖ) :
    (diagonalCoreSConstruction C).obj n = (coreSConstruction n.unop.len C).obj n

lemma diagonalCoreSConstruction_map (C : SSet.{u}) {d e : SimplexCategoryᵒᵖ}
    (f : d ⟶ e) (x : (diagonalCoreSConstruction C).obj d) :
    (diagonalCoreSConstruction C).map f x =
      ((simplicialCoreSConstruction C).obj e).map f
        (((simplicialCoreSConstruction C).map f).app d x)

def kanCoreIso (X : SSet.{u}) [KanComplex X] : X ≅ (quasicategoryCore X : SSet.{u})

lemma coreSConstructionZero_isContractibleKan (C : SSet.{u}) [Quasicategory C]
    [HasZeroVertex C] : IsContractibleKan (coreSConstruction 0 C)
```

**PointedCoreSimplicial.lean**

```text
def pointedCoreSConstruction (n : ℕ) (C : SSet.{u}) [Quasicategory C] [HasZeroVertex C] :
    PointedSimplicialSet.{u}

instance pointedCoreSConstruction_kanComplex (n : ℕ) (C : SSet.{u})
    [Quasicategory C] [HasZeroVertex C] : KanComplex (pointedCoreSConstruction n C).right

def pointedCoreSMap {m n : ℕ} (C : SSet.{u}) [Quasicategory C] [HasZeroVertex C]
    (θ : Fin (m + 1) →o Fin (n + 1)) :
    pointedCoreSConstruction n C ⟶ pointedCoreSConstruction m C

def simplicialPointedCoreSConstruction (C : SSet.{u}) [Quasicategory C] [HasZeroVertex C] :
    SimplexCategoryᵒᵖ ⥤ PointedSimplicialSet.{u}

lemma simplicialPointedCoreSConstruction_forget (C : SSet.{u})
    [Quasicategory C] [HasZeroVertex C] :
    simplicialPointedCoreSConstruction C ⋙ PointedSimplicialSet.forget =
      simplicialCoreSConstruction C
```

**KSpace.lean**

```text
def pointedSRealization (C : SSet.{u}) [Quasicategory C] [HasZeroVertex C] :
    PointedSimplicialSet.{u}

def kanSRealization (C : SSet.{u}) [Quasicategory C] [HasZeroVertex C] :
    PointedSimplicialSet.{u}

instance kanSRealization_kanComplex (C : SSet.{u}) [Quasicategory C] [HasZeroVertex C] :
    KanComplex (kanSRealization C).right

def sRealizationToKan (C : SSet.{u}) [Quasicategory C] [HasZeroVertex C] :
    pointedSRealization C ⟶ kanSRealization C

lemma sRealizationToKan_anodyne (C : SSet.{u}) [Quasicategory C] [HasZeroVertex C] :
    anodyneExtensions (sRealizationToKan C).right

def kSpace (C : SSet.{u}) [Quasicategory C] [HasZeroVertex C] : PointedSimplicialSet.{u}

instance kSpace_kanComplex (C : SSet.{u}) [Quasicategory C] [HasZeroVertex C] :
    KanComplex (kSpace C).right
```

**未完了の範囲**：L1c 全体は未完了。対角の Kan 性は主張せず、構成済みの Kan 置換を通している。
実現の連結性と零対象による基点の変更の空間レベルの π_* 同型比較は §6.6 で証明済み。
反復 S• による delooping、スペクトルの構造射と Ω 条件、比較の高次整合性、連結スペクトルとしての検証は未完了。
L9 の `PointedSequence.kanReplacement` と `KanSequence.cofibrantOmegaSpectrum` は既に存在するため、
自分で証明すべき Ω 条件を未着 API という名の入力にしない。
L1d–f は未完了、L1g は別途指示待ち。

この保存単位の検証：`lake build SerrePositivity.KST.SConstruction` 成功（2234 jobs）、
`lake env lean scripts/audit_kst_s_construction.lean` 成功（484 宣言、標準三公理のみ）。
L1c の途中成果なので全体ビルドは繰り返さず、工程全体の完成時に実施する。

### 6.6 L1c：実現の連結性と零対象の選択の比較

`diagonalZeroColumn X` は零段 `X₀` から二重単体集合の対角への写像で、零単体では恒等。
連結成分で全射なので、零段が連結なら対角も連結になる。
`coreSConstruction 0 C` の可縮性を適用して対角の連結性を証明した。
既存の `PiZeroLocalization.inverts_anodyne` を実際の π₀ の全単射として使い、
Kan 置換した実現 `kanSRealization C` の連結性も証明した。安定性はこの段階では不要。

基点の変更は、可縮な零段の core で二つの零図式を辺で結び、対角と Kan 置換へ送って構成する。
その辺を自由 path 空間の基点に取り、両端への評価を loop へ送る。
両方の評価は全ての単射に RLP を持つため、L9 の `KanPiIsomorphism` を満たす。
この条件は全基点と、π₀ を含む全自然数次数を量化する。

`kSpaceAtZero C z hz` は同じ Kan 実現で基点だけを零図式 z の像に変えた loop 空間。
既定の零対象では公開 `kSpace C` と厳密に等しい。
`kSpace_zeroChoice_comparison` は任意の零対象に対し、公開 K 空間とその K 空間への
二つの π_* 同型を持つ共通の点つき Kan 複体を構成する。
これは空間レベルの選択の比較であり、反復 S• の構造射との自然性・高次整合性を完成扱いしない。

以下は §6.3 と同じ namespace・universe の公開ヘッダー（本文を除く）。

**DiagonalConnected.lean**

```text
def diagonalZeroColumn (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    X.obj (Opposite.op ⦋0⦌) ⟶ Functor.diag SimplexCategoryᵒᵖ ⋙ Functor.uncurry.obj X

lemma diagonalZeroColumn_zero (X : SimplexCategoryᵒᵖ ⥤ SSet.{u})
    (x : (X.obj (Opposite.op ⦋0⦌)) _⦋0⦌) :
    (diagonalZeroColumn X).app (Opposite.op ⦋0⦌) x = x

lemma diagonalZeroColumn_piZero_surjective (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    Function.Surjective (SSet.mapπ₀ (diagonalZeroColumn X))

lemma diagonal_preconnected_of_zero (X : SimplexCategoryᵒᵖ ⥤ SSet.{u})
    [SSet.IsPreconnected (X.obj (Opposite.op ⦋0⦌))] :
    SSet.IsPreconnected (Functor.diag SimplexCategoryᵒᵖ ⋙ Functor.uncurry.obj X)

lemma diagonal_connected_of_zero (X : SimplexCategoryᵒᵖ ⥤ SSet.{u})
    [SSet.IsConnected (X.obj (Opposite.op ⦋0⦌))] :
    SSet.IsConnected (Functor.diag SimplexCategoryᵒᵖ ⋙ Functor.uncurry.obj X)

instance diagonalCoreSConstruction_isConnected (C : SSet.{u}) [Quasicategory C]
    [HasZeroVertex C] : SSet.IsConnected (diagonalCoreSConstruction C)
```

**RealizationConnected.lean**

```text
lemma mapPiZero_bijective_of_anodyne {A B : SSet.{u}} (f : A ⟶ B)
    (hf : anodyneExtensions f) : Function.Bijective (SSet.mapπ₀ f)

lemma isConnected_of_anodyne {A B : SSet.{u}} [SSet.IsConnected A]
    (f : A ⟶ B) (hf : anodyneExtensions f) : SSet.IsConnected B

lemma sRealizationToKan_piZero_bijective (C : SSet.{u}) [Quasicategory C] [HasZeroVertex C] :
    Function.Bijective (SSet.mapπ₀ (sRealizationToKan C).right)

instance kanSRealization_isConnected (C : SSet.{u}) [Quasicategory C] [HasZeroVertex C] :
    SSet.IsConnected (kanSRealization C).right
```

**PointedPathComparison.lean**

```text
instance pointedOfVertex_kanComplex (X : SSet.{u}) [KanComplex X] (x : X _⦋0⦌) :
    KanComplex (PointedSimplicialSet.ofVertex X x).right

lemma pathEvaluation_eq_evaluateFunctorAt (X : SSet.{u}) (t : Fin 2) :
    Spectra.KanPath.evaluation X t =
      evaluateFunctorAt (Y

def pointedPathAt {X : SSet.{u}} (p : (Δ[1] : SSet.{u}) ⟶ X) : PointedSimplicialSet.{u}

def pointedPathEndpoint {X : SSet.{u}} (p : (Δ[1] : SSet.{u}) ⟶ X) (t : Fin 2) :
    pointedPathAt p ⟶ PointedSimplicialSet.ofVertex X
      (p.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm t))

instance pointedPathAt_kanComplex {X : SSet.{u}} [KanComplex X] (p : (Δ[1] : SSet.{u}) ⟶ X) :
    KanComplex (pointedPathAt p).right

lemma pointedPathEndpoint_rlp {X : SSet.{u}} [KanComplex X]
    (p : (Δ[1] : SSet.{u}) ⟶ X) (t : Fin 2) :
    (MorphismProperty.monomorphisms SSet.{u}).rlp (pointedPathEndpoint p t).right

def loopPathEndpoint {X : SSet.{u}} (p : (Δ[1] : SSet.{u}) ⟶ X) (t : Fin 2) :
    Spectra.loopSpace (pointedPathAt p) ⟶
      Spectra.loopSpace (PointedSimplicialSet.ofVertex X
        (p.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm t)))

lemma loopPathEndpoint_rlp {X : SSet.{u}} [KanComplex X]
    (p : (Δ[1] : SSet.{u}) ⟶ X) (t : Fin 2) :
    (MorphismProperty.monomorphisms SSet.{u}).rlp (loopPathEndpoint p t).right

lemma loopPathEndpoint_piIsomorphism {X : SSet.{u}} [KanComplex X]
    (p : (Δ[1] : SSet.{u}) ⟶ X) (t : Fin 2) :
    Spectra.KanPiIsomorphism (loopPathEndpoint p t).right

lemma exists_loopBasepointComparison {X : SSet.{u}} [KanComplex X]
    {x y : X _⦋0⦌} (e : SSet.Edge x y) :
    ∃ P : Spectra.PointedKanComplex.{u},
      ∃ (f : P.space ⟶ Spectra.loopSpace (PointedSimplicialSet.ofVertex X x))
        (g : P.space ⟶ Spectra.loopSpace (PointedSimplicialSet.ofVertex X y)),
        Spectra.KanPiIsomorphism f.right ∧ Spectra.KanPiIsomorphism g.right

lemma kanComparison_congr_left {A A' B : PointedSimplicialSet.{u}}
    [KanComplex A.right] [KanComplex A'.right] [KanComplex B.right] (h : A = A')
    (hc : ∃ P : Spectra.PointedKanComplex.{u}, ∃ (f : P.space ⟶ A) (g : P.space ⟶ B),
      Spectra.KanPiIsomorphism f.right ∧ Spectra.KanPiIsomorphism g.right) :
    ∃ P : Spectra.PointedKanComplex.{u}, ∃ (f : P.space ⟶ A') (g : P.space ⟶ B),
      Spectra.KanPiIsomorphism f.right ∧ Spectra.KanPiIsomorphism g.right
```

**ZeroChoiceComparison.lean**

```text
def diagonalZeroVertexEdge (C : SSet.{u}) [Quasicategory C] [HasZeroVertex C]
    (z z' : C _⦋0⦌) (hz : IsZeroVertex z) (hz' : IsZeroVertex z') :
    SSet.Edge (X

def realizationZeroPoint (C : SSet.{u}) [Quasicategory C] [HasZeroVertex C]
    (z : C _⦋0⦌) (hz : IsZeroVertex z) : (kanSRealization C).right _⦋0⦌

def realizationZeroEdge (C : SSet.{u}) [Quasicategory C] [HasZeroVertex C]
    (z z' : C _⦋0⦌) (hz : IsZeroVertex z) (hz' : IsZeroVertex z') :
    SSet.Edge (realizationZeroPoint C z hz) (realizationZeroPoint C z' hz')

def kSpaceAtZero (C : SSet.{u}) [Quasicategory C] [HasZeroVertex C]
    (z : C _⦋0⦌) (hz : IsZeroVertex z) : PointedSimplicialSet.{u}

instance kSpaceAtZero_kanComplex (C : SSet.{u}) [Quasicategory C] [HasZeroVertex C]
    (z : C _⦋0⦌) (hz : IsZeroVertex z) : KanComplex (kSpaceAtZero C z hz).right

lemma kSpaceAtZero_comparison (C : SSet.{u}) [Quasicategory C] [HasZeroVertex C]
    (z z' : C _⦋0⦌) (hz : IsZeroVertex z) (hz' : IsZeroVertex z') :
    ∃ P : Spectra.PointedKanComplex.{u},
      ∃ (f : P.space ⟶ kSpaceAtZero C z hz) (g : P.space ⟶ kSpaceAtZero C z' hz'),
        Spectra.KanPiIsomorphism f.right ∧ Spectra.KanPiIsomorphism g.right

lemma ofVertex_basepoint_eq (X : PointedSimplicialSet.{u}) :
    PointedSimplicialSet.ofVertex X.right (PointedSimplicialSet.basepoint X) = X

lemma realizationZeroPoint_chosen (C : SSet.{u}) [Quasicategory C] [HasZeroVertex C] :
    realizationZeroPoint C (chosenZeroVertex C).vertex (chosenZeroVertex C).isZero =
      PointedSimplicialSet.basepoint (kanSRealization C)

lemma kSpaceAtZero_chosen (C : SSet.{u}) [Quasicategory C] [HasZeroVertex C] :
    kSpaceAtZero C (chosenZeroVertex C).vertex (chosenZeroVertex C).isZero = kSpace C

lemma kSpace_zeroChoice_comparison (C : SSet.{u}) [Quasicategory C] [HasZeroVertex C]
    (z : C _⦋0⦌) (hz : IsZeroVertex z) :
    ∃ P : Spectra.PointedKanComplex.{u},
      ∃ (f : P.space ⟶ kSpace C) (g : P.space ⟶ kSpaceAtZero C z hz),
        Spectra.KanPiIsomorphism f.right ∧ Spectra.KanPiIsomorphism g.right
```

**現在地・未完了**：L1a・L1b は完了。L1c は連結 Kan 実現と K 空間、その空間レベルの基点変更の比較まで証明済み。
反復 S• の構造写像、delooping、Ω 条件、BF の連結スペクトル、構造射との比較の自然性・高次整合性は未完了。
L1d–f は未完了、L1g は別途指示待ち。

この保存単位の検証：`lake build SerrePositivity.KST.SConstruction` 成功（2254 jobs）、
`lake env lean scripts/audit_kst_s_construction.lean` 成功（515 宣言、標準三公理のみ）。
追加公理・sorry なし。L1c 全体は未完了なので、全体ビルドは工程完了時に行う。

### 6.7 L1c：後合成と有限反復の対象

`PreservesSConstructionData f` は、零頂点と実際の押し出し正方形を保つという本レーンの入力条件。
α-S の安定性の定義を変更せず、h 圏の通常の押し出しに置き換えない。
この条件から `IsGapped.postcomp`、S_n の後合成 `sPostcomp`、core と対角の写像を構成した。
S_n の恒等・合成・単体作用との可換性、および対角の恒等・合成則は厳密等号である。
零図式は像の零対象の零図式へ厳密に送られる。

点つきの公開 `kSpace` の間の厳密な写像には、既定の零対象の頂点を厳密に保つ
`PreservesChosenZero f` をさらに明示する。
この条件の下で `pointedSPostcomp`、`kanSPostcomp`、`kSpacePostcomp` を構成し、K 空間写像の恒等・合成則を証明した。
一般の exact な射では零対象の像は既定の零対象と同型でも頂点の等号とは限らない。
§6.6 の基点比較をこの写像と coherent に組み合わせる部分は未完了であり、
今回の厳密な基点保存条件を一般の dg 関手に対する関手性の証明の代用にしない。

`iteratedSConstruction ns C` は既存の全 gapped 図式の S 構成を有限回そのまま反復した対象。
リストの先頭が最も外側。空リストでは C、`n::ns` では `sConstruction n (iteratedSConstruction ns C)`。
core は最後に取り、Kan core を S の入力にする別構成にはしない。
全ての反復対象の quasicategory 性と零対象、core の Kan 性を証明した。
任意の位置の次数が零なら、反復対象自体と core は可縮 Kan 複体になる。
これは reduced な境界条件の可縮性であり、全ての境界が同じ一点に厳密に等しいという主張ではない。

以下は §6.3 と同じ namespace・universe の公開ヘッダー（本文を除く）。

**ExactMaps.lean**

```text
def PreservesSConstructionData {C D : SSet.{u}} (f : C ⟶ D) : Prop

lemma preservesSConstructionData_id (C : SSet.{u}) : PreservesSConstructionData (𝟙 C)

lemma PreservesSConstructionData.comp {C D E : SSet.{u}} {f : C ⟶ D} {g : D ⟶ E}
    (hf : PreservesSConstructionData f) (hg : PreservesSConstructionData g) :
    PreservesSConstructionData (f ≫ g)

lemma IsGapped.postcomp {n : ℕ} {C D : SSet.{u}} {F : arNerve n ⟶ C}
    (hF : IsGapped F) (f : C ⟶ D) (hf : PreservesSConstructionData f) : IsGapped (F ≫ f)
```

**Postcomposition.lean**

```text
def sPostcomp (n : ℕ) {C D : SSet.{u}} (f : C ⟶ D) (hf : PreservesSConstructionData f) :
    sConstruction n C ⟶ sConstruction n D

lemma sPostcomp_ι (n : ℕ) {C D : SSet.{u}} (f : C ⟶ D) (hf : PreservesSConstructionData f) :
    sPostcomp n f hf ≫ (gappedSubcomplex n D).ι =
      (gappedSubcomplex n C).ι ≫ (ihom (arNerve n)).map f

lemma sPostcomp_id (n : ℕ) (C : SSet.{u}) :
    sPostcomp n (𝟙 C) (preservesSConstructionData_id C) = 𝟙 (sConstruction n C)

lemma sPostcomp_comp (n : ℕ) {C D E : SSet.{u}} (f : C ⟶ D) (g : D ⟶ E)
    (hf : PreservesSConstructionData f) (hg : PreservesSConstructionData g) :
    sPostcomp n (f ≫ g) (hf.comp hg) = sPostcomp n f hf ≫ sPostcomp n g hg

lemma sPostcomp_sMap {m n : ℕ} {C D : SSet.{u}} (f : C ⟶ D)
    (hf : PreservesSConstructionData f) (θ : Fin (m + 1) →o Fin (n + 1)) :
    sPostcomp n f hf ≫ sMap D θ = sMap C θ ≫ sPostcomp m f hf

def simplicialSPostcomp {C D : SSet.{u}} (f : C ⟶ D) (hf : PreservesSConstructionData f) :
    simplicialSConstruction C ⟶ simplicialSConstruction D

def simplicialCoreSPostcomp {C D : SSet.{u}} (f : C ⟶ D) (hf : PreservesSConstructionData f) :
    simplicialCoreSConstruction C ⟶ simplicialCoreSConstruction D

def diagonalSPostcomp {C D : SSet.{u}} (f : C ⟶ D) (hf : PreservesSConstructionData f) :
    diagonalCoreSConstruction C ⟶ diagonalCoreSConstruction D

lemma sPostcomp_zeroVertex (n : ℕ) {C D : SSet.{u}} [Quasicategory C] [Quasicategory D]
    (f : C ⟶ D) (hf : PreservesSConstructionData f) (z : C _⦋0⦌) (hz : IsZeroVertex z) :
    (sPostcomp n f hf).app (Opposite.op ⦋0⦌) (sConstructionZeroVertex n z hz) =
      sConstructionZeroVertex n (f.app (Opposite.op ⦋0⦌) z) (hf.1 z hz)

lemma diagonalSPostcomp_id (C : SSet.{u}) :
    diagonalSPostcomp (𝟙 C) (preservesSConstructionData_id C) = 𝟙 (diagonalCoreSConstruction C)

lemma diagonalSPostcomp_comp {C D E : SSet.{u}} (f : C ⟶ D) (g : D ⟶ E)
    (hf : PreservesSConstructionData f) (hg : PreservesSConstructionData g) :
    diagonalSPostcomp (f ≫ g) (hf.comp hg) = diagonalSPostcomp f hf ≫ diagonalSPostcomp g hg

lemma diagonalSPostcomp_zeroVertex {C D : SSet.{u}} [Quasicategory C] [Quasicategory D]
    (f : C ⟶ D) (hf : PreservesSConstructionData f) (z : C _⦋0⦌) (hz : IsZeroVertex z) :
    (diagonalSPostcomp f hf).app (Opposite.op ⦋0⦌) (coreSConstructionZeroVertex 0 z hz) =
      coreSConstructionZeroVertex 0 (f.app (Opposite.op ⦋0⦌) z) (hf.1 z hz)
```

**PointedPostcomposition.lean**

```text
def PreservesChosenZero {C D : SSet.{u}} [HasZeroVertex C] [HasZeroVertex D] (f : C ⟶ D) : Prop

lemma preservesChosenZero_id (C : SSet.{u}) [HasZeroVertex C] : PreservesChosenZero (𝟙 C)

lemma PreservesChosenZero.comp {C D E : SSet.{u}}
    [HasZeroVertex C] [HasZeroVertex D] [HasZeroVertex E] {f : C ⟶ D} {g : D ⟶ E}
    (hf : PreservesChosenZero f) (hg : PreservesChosenZero g) : PreservesChosenZero (f ≫ g)

def pointedSPostcomp {C D : SSet.{u}} [Quasicategory C] [Quasicategory D]
    [HasZeroVertex C] [HasZeroVertex D] (f : C ⟶ D)
    (hf : PreservesSConstructionData f) (hzero : PreservesChosenZero f) :
    pointedSRealization C ⟶ pointedSRealization D

lemma pointedSPostcomp_id (C : SSet.{u}) [Quasicategory C] [HasZeroVertex C] :
    pointedSPostcomp (𝟙 C) (preservesSConstructionData_id C) (preservesChosenZero_id C) =
      𝟙 (pointedSRealization C)

lemma pointedSPostcomp_comp {C D E : SSet.{u}}
    [Quasicategory C] [Quasicategory D] [Quasicategory E]
    [HasZeroVertex C] [HasZeroVertex D] [HasZeroVertex E]
    (f : C ⟶ D) (g : D ⟶ E) (hf : PreservesSConstructionData f) (hg : PreservesSConstructionData g)
    (hfzero : PreservesChosenZero f) (hgzero : PreservesChosenZero g) :
    pointedSPostcomp (f ≫ g) (hf.comp hg) (hfzero.comp hgzero) =
      pointedSPostcomp f hf hfzero ≫ pointedSPostcomp g hg hgzero

def kanSPostcomp {C D : SSet.{u}} [Quasicategory C] [Quasicategory D]
    [HasZeroVertex C] [HasZeroVertex D] (f : C ⟶ D)
    (hf : PreservesSConstructionData f) (hzero : PreservesChosenZero f) :
    kanSRealization C ⟶ kanSRealization D

def kSpacePostcomp {C D : SSet.{u}} [Quasicategory C] [Quasicategory D]
    [HasZeroVertex C] [HasZeroVertex D] (f : C ⟶ D)
    (hf : PreservesSConstructionData f) (hzero : PreservesChosenZero f) :
    kSpace C ⟶ kSpace D

lemma kSpacePostcomp_id (C : SSet.{u}) [Quasicategory C] [HasZeroVertex C] :
    kSpacePostcomp (𝟙 C) (preservesSConstructionData_id C) (preservesChosenZero_id C) =
      𝟙 (kSpace C)

lemma kSpacePostcomp_comp {C D E : SSet.{u}}
    [Quasicategory C] [Quasicategory D] [Quasicategory E]
    [HasZeroVertex C] [HasZeroVertex D] [HasZeroVertex E]
    (f : C ⟶ D) (g : D ⟶ E) (hf : PreservesSConstructionData f) (hg : PreservesSConstructionData g)
    (hfzero : PreservesChosenZero f) (hgzero : PreservesChosenZero g) :
    kSpacePostcomp (f ≫ g) (hf.comp hg) (hfzero.comp hgzero) =
      kSpacePostcomp f hf hfzero ≫ kSpacePostcomp g hg hgzero
```

**IteratedObjects.lean**

```text
def iteratedSConstruction : List ℕ → SSet.{u} → SSet.{u}

instance iteratedSConstruction_quasicategory (ns : List ℕ) (C : SSet.{u}) [Quasicategory C] :
    Quasicategory (iteratedSConstruction ns C)

instance iteratedSConstruction_hasZeroVertex (ns : List ℕ) (C : SSet.{u}) [Quasicategory C]
    [HasZeroVertex C] : HasZeroVertex (iteratedSConstruction ns C)

def iteratedZeroVertex (ns : List ℕ) {C : SSet.{u}} [Quasicategory C]
    (z : C _⦋0⦌) (hz : IsZeroVertex z) : ZeroVertex (iteratedSConstruction ns C)

def iteratedCoreSConstruction (ns : List ℕ) (C : SSet.{u}) : SSet.{u}

instance iteratedCoreSConstruction_kanComplex (ns : List ℕ) (C : SSet.{u}) [Quasicategory C] :
    KanComplex (iteratedCoreSConstruction ns C)

lemma sConstruction_isZeroVertex_of_contractible (n : ℕ) {C : SSet.{u}}
    [Quasicategory C] (h : IsContractibleKan C) (v : (sConstruction n C) _⦋0⦌) :
    IsZeroVertex v

lemma sConstruction_isContractibleKan_of_contractible (n : ℕ) {C : SSet.{u}}
    [Quasicategory C] (h : IsContractibleKan C) : IsContractibleKan (sConstruction n C)

lemma iteratedSConstruction_isContractibleKan_of_zero_mem (ns : List ℕ) (C : SSet.{u})
    [Quasicategory C] [HasZeroVertex C] (h : 0 ∈ ns) :
    IsContractibleKan (iteratedSConstruction ns C)

lemma iteratedCoreSConstruction_isContractibleKan_of_zero_mem (ns : List ℕ) (C : SSet.{u})
    [Quasicategory C] [HasZeroVertex C] (h : 0 ∈ ns) :
    IsContractibleKan (iteratedCoreSConstruction ns C)
```

**現在地・未完了**：L1a・L1b は完了。L1c は空間模型・連結性・基点比較、保存条件を持つ射の後合成、
有限反復の対象と零方向の可縮性まで証明済み。
S_n とその reindexing が零対象・押し出しの保存条件を保つこと、多単体的な反復 S• の全構造射、
境界の coherent な潰し、delooping、Ω 条件、BF の連結スペクトルとその自然性は未完了。
今回 `PreservesSConstructionData (sPostcomp n f hf)` を証明したとは扱わない。
L1d–f は未完了、L1g は別途指示待ち。

この保存単位の検証：`lake build SerrePositivity.KST.SConstruction` 成功（2258 jobs）、
`lake env lean scripts/audit_kst_s_construction.lean` 成功（551 宣言、標準三公理のみ）。
追加公理・sorry なし。L1c 全体の完成時に全体ビルドを行う。

## 6.8 trivial Kan fibration に沿う普遍性と安定性

零対象・一般の余錐の余極限性・押し出し・引き戻しを保ち反映し、安定性を源へ反映する。
第一行制限への適用も証明。Core/・Stable/ の公開定義は変更しない。

**TrivialFibrationUniversality.lean**

```text
def mapJoinCocone {K X Y : SSet.{u}} (f : X ⟶ Y) {p : K ⟶ X} (c : JoinCocone p) :
    JoinCocone (p ≫ f)

instance sliceUnderPostcomp_of_trivialKanFibration {K E B : SSet.{u}}
    (p : K ⟶ E) (q : E ⟶ B) [TrivialKanFibration q] :
    TrivialKanFibration (sliceUnderPostcomp p q)

lemma isColimitCone_iff_mapJoinCocone_of_trivialKanFibration {K E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B] (q : E ⟶ B) [TrivialKanFibration q]
    {p : K ⟶ E} (c : JoinCocone p) : IsColimitCone c ↔ IsColimitCone (mapJoinCocone q c)

lemma isZeroVertex_iff_of_trivialKanFibration {E B : SSet.{u}} [Quasicategory E] [Quasicategory B]
    (q : E ⟶ B) [TrivialKanFibration q] (z : E _⦋0⦌) :
    IsZeroVertex z ↔ IsZeroVertex (q.app (Opposite.op ⦋0⦌) z)

lemma isPushoutSquare_iff_postcomp_of_trivialKanFibration {E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B] (q : E ⟶ B) [TrivialKanFibration q]
    (F : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ E) : IsPushoutSquare F ↔ IsPushoutSquare (F ≫ q)

lemma isPullbackSquare_iff_postcomp_of_trivialKanFibration {E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B] (q : E ⟶ B) [TrivialKanFibration q]
    (F : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ E) : IsPullbackSquare F ↔ IsPullbackSquare (F ≫ q)

lemma preservesSConstructionData_of_trivialKanFibration {E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B] (q : E ⟶ B) [TrivialKanFibration q] :
    PreservesSConstructionData q

lemma firstRowRestriction_preservesSConstructionData (n : ℕ) (C : SSet.{u})
    [Quasicategory C] [IsStable C] : PreservesSConstructionData (firstRowRestriction n C)

```

**TrivialFibrationStability.lean**

```text
lemma squareRightEdge_mono : Mono (squareRightEdge.{u})

lemma squareBottomEdge_mono : Mono (squareBottomEdge.{u})

lemma hasZeroVertex_of_trivialKanFibration {E B : SSet.{u}} [Quasicategory E] [Quasicategory B]
    [HasZeroVertex B] (q : E ⟶ B) [TrivialKanFibration q] : HasZeroVertex E

lemma fiberSquare_nonempty_of_trivialKanFibration {E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B] [IsStable B] (q : E ⟶ B) [TrivialKanFibration q]
    {x y : E _⦋0⦌} (f : SSet.Truncated.Edge (X

lemma cofiberSquare_nonempty_of_trivialKanFibration {E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B] [IsStable B] (q : E ⟶ B) [TrivialKanFibration q]
    {x y : E _⦋0⦌} (f : SSet.Truncated.Edge (X

lemma isStable_of_trivialKanFibration {E B : SSet.{u}} [Quasicategory E] [Quasicategory B]
    [IsStable B] (q : E ⟶ B) [TrivialKanFibration q] : IsStable E

```

現在地：L1c 継続中。図式圏の安定性、S_n の安定性・構造射の保存性、多単体構造、delooping と Ω 条件は未完了。L1d–f は未完了。

検証：対象ビルド成功（2260 jobs）、公理監査成功（565 宣言、標準三公理のみ）。追加公理・sorry なし。

## 6.9 関手圏・S_n・有限反復の安定性

任意の単体集合 A と安定な quasicategory C に対し Fun(A,C) の安定性を証明。
零脚を持つ span/cospan の点ごとの余極限・極限の存在を証明してから A6 の双方向判定を使う。
第一行制限の trivial Kan fibration により S_n と全有限反復の安定性を反映する。
Core/・Stable/ の公開定義は変更していない。

**TerminalBoundaryTransport.lean**

```text
lemma terminalBoundaryLifting_of_initialBoundaryLifting_op {E B : SSet.{u}}
    (p : E ⟶ B) (x : E _⦋0⦌)
    (hx : InitialBoundaryLifting (SSet.opFunctor.map p) (SSet.opObjEquiv.symm x)) :
    TerminalBoundaryLifting p x

lemma TerminalBoundaryLifting.op_initial {E B : SSet.{u}} {p : E ⟶ B} {x : E _⦋0⦌}
    (hx : TerminalBoundaryLifting p x) :
    InitialBoundaryLifting (SSet.opFunctor.map p) (SSet.opObjEquiv.symm x)

lemma TerminalBoundaryLifting.of_vertexIso {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (p : X ⟶ Y) [InnerFibration p]
    {x y : X _⦋0⦌} (hx : TerminalBoundaryLifting p x) (e : VertexIso x y) :
    TerminalBoundaryLifting p y

```

**LimitBaseTransport.lean**

```text
lemma exists_terminalConeVertex_over_invertible_edge (K X : SSet.{u}) [Quasicategory X]
    (v : ((ihom (join (Δ[0] : SSet.{u}) K)).obj X) _⦋0⦌)
    (hv : TerminalBoundaryLifting (coneRestriction K X) v)
    (b : ((ihom K).obj X) _⦋0⦌)
    (e : SSet.Truncated.Edge (X

lemma HasLimit.of_functorIso {K X : SSet.{u}} [Quasicategory X]
    {p q : K ⟶ X} (hq : HasLimit q) (e : FunctorIso p q) : HasLimit p

lemma hasLimit_iff_of_functorIso {K X : SSet.{u}} [Quasicategory X]
    {p q : K ⟶ X} (e : FunctorIso p q) : HasLimit p ↔ HasLimit q

```

**ZeroCospanData.lean**

```text
def zeroCospanData (C : SSet.{u}) : SSet.{u}

def zeroCospanDataProjection (C : SSet.{u}) : zeroCospanData C ⟶ (ihom (Δ[1] : SSet.{u})).obj C

instance zeroCospanDataProjection_trivialKanFibration (C : SSet.{u}) [HasZeroVertex C] :
    TrivialKanFibration (zeroCospanDataProjection C)

def zeroCospanDataDiagram (C : SSet.{u}) :
    zeroCospanData C ⟶ (ihom (horn 2 2 : SSet.{u})).obj C

lemma zeroCospanDataDiagram_left (C : SSet.{u}) :
    zeroCospanDataDiagram C ≫ (pre horn₂₂.ι₀₂).app C = zeroCospanDataProjection C

lemma zeroCospanDataDiagram_right (C : SSet.{u}) :
    zeroCospanDataDiagram C ≫ (pre horn₂₂.ι₁₂).app C =
      pullback.fst (zeroSourceArrowTarget C)
        (evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) ≫
          (fullSubcomplexOnVertices _ IsZeroSourceArrow).ι

lemma zeroCospan_targets (C : SSet.{u}) :
    (pre horn₂₂.ι₀₂).app C ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
      (pre horn₂₂.ι₁₂).app C ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2))

def zeroCospanDataLift {A C : SSet.{u}} (p : A ⟶ (ihom (horn 2 2 : SSet.{u})).obj C)
    (hp : ∀ v : A _⦋0⦌, IsZeroSourceArrow
      (((pre horn₂₂.ι₁₂).app C).app (Opposite.op ⦋0⦌) (p.app (Opposite.op ⦋0⦌) v))) :
    A ⟶ zeroCospanData C

lemma zeroCospanDataLift_projection {A C : SSet.{u}}
    (p : A ⟶ (ihom (horn 2 2 : SSet.{u})).obj C) (hp) :
    zeroCospanDataLift p hp ≫ zeroCospanDataProjection C = p ≫ (pre horn₂₂.ι₀₂).app C

lemma zeroCospanDataLift_diagram {A C : SSet.{u}}
    (p : A ⟶ (ihom (horn 2 2 : SSet.{u})).obj C) (hp) :
    zeroCospanDataLift p hp ≫ zeroCospanDataDiagram C = p

```

**ZeroCospanChoices.lean**

```text
def zeroCospanFamiliesIso {A C : SSet.{u}} [HasZeroVertex C]
    (p q : A ⟶ (ihom (horn 2 2 : SSet.{u})).obj C)
    (hp : ∀ v : A _⦋0⦌, IsZeroSourceArrow
      (((pre horn₂₂.ι₁₂).app C).app (Opposite.op ⦋0⦌) (p.app (Opposite.op ⦋0⦌) v)))
    (hq : ∀ v : A _⦋0⦌, IsZeroSourceArrow
      (((pre horn₂₂.ι₁₂).app C).app (Opposite.op ⦋0⦌) (q.app (Opposite.op ⦋0⦌) v)))
    (h : p ≫ (pre horn₂₂.ι₀₂).app C = q ≫ (pre horn₂₂.ι₀₂).app C) : FunctorIso p q

def zeroCospanDiagramsIso {C : SSet.{u}} [HasZeroVertex C]
    (p q : (horn 2 2 : SSet.{u}) ⟶ C)
    (hp : IsZeroSourceArrow (functorVertex (horn₂₂.ι₁₂ ≫ p)))
    (hq : IsZeroSourceArrow (functorVertex (horn₂₂.ι₁₂ ≫ q)))
    (h : horn₂₂.ι₀₂ ≫ p = horn₂₂.ι₀₂ ≫ q) : FunctorIso p q

lemma hasLimit_zeroCospan {C : SSet.{u}} [Quasicategory C] [IsStable C]
    (p : (horn 2 2 : SSet.{u}) ⟶ C)
    (hp : IsZeroSourceArrow (functorVertex (horn₂₂.ι₁₂ ≫ p))) : HasLimit p

```

**FiberFromZeroCospans.lean**

```text
lemma fiberSquare_nonempty_of_zeroCospan_limits {X : SSet.{u}} [Quasicategory X]
    [HasZeroVertex X]
    (h : ∀ p : (horn 2 2 : SSet.{u}) ⟶ X,
      IsZeroSourceArrow (functorVertex (horn₂₂.ι₁₂ ≫ p)) → HasLimit p)
    {x y : X _⦋0⦌} (f : SSet.Truncated.Edge (X

```

**FunctorZeroEvaluation.lean**

```text
lemma functor_const_isZeroVertex {A C : SSet.{u}} (z : C _⦋0⦌) (hz : IsZeroVertex z) :
    IsZeroVertex (functorVertex (SSet.const z : A ⟶ C))

instance functor_hasZeroVertex (A C : SSet.{u}) [HasZeroVertex C] :
    HasZeroVertex ((ihom A).obj C)

lemma isZeroVertex_evaluateFunctorAt {A C : SSet.{u}} [Quasicategory C] [HasZeroVertex C]
    {v : ((ihom A).obj C) _⦋0⦌} (hv : IsZeroVertex v) (a : A _⦋0⦌) :
    IsZeroVertex ((evaluateFunctorAt a).app (Opposite.op ⦋0⦌) v)

```

**FunctorCofibers.lean**

```text
lemma cofiberFamilySquare_bottomEdge {A C : SSet.{u}} (H : A ⟶ cofiberDiagrams C) :
    squareBottomEdge ≫ cofiberFamilySquare H =
      internalHomFlipHomEquiv A (Δ[1] : SSet.{u}) C (H ≫ cofiberProjection C)

lemma functor_cofiberSquare_nonempty {A C : SSet.{u}} [Quasicategory C] [IsStable C]
    {x y : ((ihom A).obj C) _⦋0⦌}
    (f : SSet.Truncated.Edge (X

```

**FunctorStability.lean**

```text
lemma zeroSourceArrow_evaluate {A C : SSet.{u}} [Quasicategory C] [HasZeroVertex C]
    (e : (Δ[1] : SSet.{u}) ⟶ (ihom A).obj C)
    (he : IsZeroSourceArrow (functorVertex e)) (a : A _⦋0⦌) :
    IsZeroSourceArrow (functorVertex (e ≫ evaluateFunctorAt a))

lemma zeroTargetArrow_evaluate {A C : SSet.{u}} [Quasicategory C] [HasZeroVertex C]
    (e : (Δ[1] : SSet.{u}) ⟶ (ihom A).obj C)
    (he : IsZeroTargetArrow (functorVertex e)) (a : A _⦋0⦌) :
    IsZeroTargetArrow (functorVertex (e ≫ evaluateFunctorAt a))

lemma functor_zeroCospan_hasPointwiseLimits {A C : SSet.{u}} [Quasicategory C] [IsStable C]
    (p : (horn 2 2 : SSet.{u}) ⟶ (ihom A).obj C)
    (hp : IsZeroSourceArrow (functorVertex (horn₂₂.ι₁₂ ≫ p))) : HasPointwiseLimits p

lemma functor_zeroSpan_hasPointwiseColimits {A C : SSet.{u}} [Quasicategory C] [IsStable C]
    (p : (horn 2 0 : SSet.{u}) ⟶ (ihom A).obj C)
    (hp : IsZeroTargetArrow (functorVertex (horn₂₀.ι₀₂ ≫ p))) : HasPointwiseColimits p

lemma functor_fiberSquare_nonempty {A C : SSet.{u}} [Quasicategory C] [IsStable C]
    {x y : ((ihom A).obj C) _⦋0⦌}
    (f : SSet.Truncated.Edge (X

lemma functor_zeroTriangle_pullback_iff {A C : SSet.{u}} [Quasicategory C] [IsStable C]
    (t : ZeroTriangle ((ihom A).obj C)) :
    IsPullbackSquare t.square ↔ ∀ a : A _⦋0⦌, IsPullbackSquare (t.square ≫ evaluateFunctorAt a)

lemma functor_zeroTriangle_pushout_iff {A C : SSet.{u}} [Quasicategory C] [IsStable C]
    (t : ZeroTriangle ((ihom A).obj C)) :
    IsPushoutSquare t.square ↔ ∀ a : A _⦋0⦌, IsPushoutSquare (t.square ≫ evaluateFunctorAt a)

instance functor_isStable (A C : SSet.{u}) [Quasicategory C] [IsStable C] :
    IsStable ((ihom A).obj C)

```

**SConstructionStability.lean**

```text
instance sConstruction_isStable (n : ℕ) (C : SSet.{u}) [Quasicategory C] [IsStable C] :
    IsStable (sConstruction n C)

instance iteratedSConstruction_isStable (ns : List ℕ) (C : SSet.{u})
    [Quasicategory C] [IsStable C] : IsStable (iteratedSConstruction ns C)

```

現在地：L1a・L1b 完了、L1c 継続中。関手圏・S_n・有限反復の安定性を無条件で証明した（上記の標的の安定性以外の追加仮定なし）。
S_n の reindexing・後合成の押し出し保存、多単体構造、境界の coherent な潰し、delooping・Ω 条件・BF スペクトルは未完了。
L1d–f は未完了、L1g は別途指示待ち。

検証：対象ビルド成功（2271 jobs）、公理監査成功（600 宣言、標準三公理のみ）。追加公理・sorry なし。

## 6.10 構造射の零対象保存・関手圏の cofiber 保存

S_n の包含・面・退化・後合成が全零対象を保つことを証明。
関手圏の添字制限・後合成が零対象と cofiber 正方形を保つことも証明。
任意の押し出しの保存や S_n の後合成の保存条件全体を証明済みとはしない。

**ZeroPreservation.lean**

```text
lemma map_isZeroVertex_of_zero_image {C D : SSet.{u}} [Quasicategory C] [Quasicategory D]
    (f : C ⟶ D) (z : C _⦋0⦌) (hz : IsZeroVertex z)
    (hfz : IsZeroVertex (f.app (Opposite.op ⦋0⦌) z))
    {w : C _⦋0⦌} (hw : IsZeroVertex w) : IsZeroVertex (f.app (Opposite.op ⦋0⦌) w)

lemma gappedInclusion_isZeroVertex {C : SSet.{u}} [Quasicategory C] [HasZeroVertex C]
    (n : ℕ) {v : (sConstruction n C) _⦋0⦌} (hv : IsZeroVertex v) :
    IsZeroVertex ((gappedSubcomplex n C).ι.app (Opposite.op ⦋0⦌) v)

lemma sMap_isZeroVertex {C : SSet.{u}} [Quasicategory C] [HasZeroVertex C]
    {m n : ℕ} (θ : Fin (m + 1) →o Fin (n + 1))
    {v : (sConstruction n C) _⦋0⦌} (hv : IsZeroVertex v) :
    IsZeroVertex ((sMap C θ).app (Opposite.op ⦋0⦌) v)

lemma sPostcomp_isZeroVertex {C D : SSet.{u}} [Quasicategory C] [Quasicategory D]
    [HasZeroVertex C] (n : ℕ) (f : C ⟶ D) (hf : PreservesSConstructionData f)
    {v : (sConstruction n C) _⦋0⦌} (hv : IsZeroVertex v) :
    IsZeroVertex ((sPostcomp n f hf).app (Opposite.op ⦋0⦌) v)

```

**FunctorCofiberPreservation.lean**

```text
lemma ihom_postcomp_evaluate {A C D : SSet.{u}} (f : C ⟶ D) (a : A _⦋0⦌) :
    (ihom A).map f ≫ evaluateFunctorAt a = evaluateFunctorAt a ≫ f

lemma functor_reindex_isZeroVertex {A B C : SSet.{u}} [Quasicategory C] [HasZeroVertex C]
    (i : A ⟶ B) {v : ((ihom B).obj C) _⦋0⦌} (hv : IsZeroVertex v) :
    IsZeroVertex (((pre i).app C).app (Opposite.op ⦋0⦌) v)

lemma functor_postcomp_isZeroVertex {A C D : SSet.{u}} [Quasicategory C] [Quasicategory D]
    [HasZeroVertex C] (f : C ⟶ D)
    (hf : ∀ z, IsZeroVertex z → IsZeroVertex (f.app (Opposite.op ⦋0⦌) z))
    {v : ((ihom A).obj C) _⦋0⦌} (hv : IsZeroVertex v) :
    IsZeroVertex (((ihom A).map f).app (Opposite.op ⦋0⦌) v)

lemma functor_reindex_preserves_cofiber {A B C : SSet.{u}} [Quasicategory C] [IsStable C]
    (i : A ⟶ B) (t : ZeroTriangle ((ihom B).obj C)) (ht : IsCofiberSequence t) :
    IsPushoutSquare (t.square ≫ (pre i).app C)

lemma functor_postcomp_preserves_cofiber {A C D : SSet.{u}}
    [Quasicategory C] [IsStable C] [Quasicategory D]
    (f : C ⟶ D) (hf : PreservesSConstructionData f)
    (t : ZeroTriangle ((ihom A).obj C)) (ht : IsCofiberSequence t) :
    IsPushoutSquare (t.square ≫ (ihom A).map f)

```

現在地：L1c 継続中。S_n の構造射の押し出し保存、多単体的反復の全構造射、境界の coherent な潰し、delooping・Ω 条件・BF スペクトルは未完了。L1d–f 未完了、L1g は別途指示待ち。

検証：対象ビルド成功（2273 jobs）、公理監査成功（609 宣言、標準三公理のみ）。追加公理・sorry なし。

## 6.11 二方向の余極限の交換と gapped 条件の同型不変性

相対始点・終点境界充填の合成、共通の制限射上の相対始対象の比較を証明。
二重余錐の制限射は inner fibration であり、補完の二つの順序は同じ射に対する相対始対象を与える。
これを使い、点ごとの外側余極限を取った後の内側の余極限性を証明した。
完成後の全行に内側余極限が存在するという前提を明示し、省略しない。
gapped 図式への適用では零脚 span の余極限の存在を安定性から供給する方針。
全入力が零対象の押し出しの出力が零対象になること、関手全体の同型による gapped 条件の不変性も証明。
Core/・Stable/ の公開定義は変更していない。

**RelativeUniversalityComposition.lean**

```text
lemma InitialBoundaryLifting.comp {E B D : SSet.{u}} (p : E ⟶ B) (q : B ⟶ D)
    {x : E _⦋0⦌} (hp : InitialBoundaryLifting p x)
    (hq : InitialBoundaryLifting q (p.app (Opposite.op ⦋0⦌) x)) :
    InitialBoundaryLifting (p ≫ q) x

lemma TerminalBoundaryLifting.comp {E B D : SSet.{u}} (p : E ⟶ B) (q : B ⟶ D)
    {x : E _⦋0⦌} (hp : TerminalBoundaryLifting p x)
    (hq : TerminalBoundaryLifting q (p.app (Opposite.op ⦋0⦌) x)) :
    TerminalBoundaryLifting (p ≫ q) x

def relativeInitialVertexIso {E B : SSet.{u}} [Quasicategory E]
    (p : E ⟶ B) [InnerFibration p] {x y : E _⦋0⦌}
    (hx : InitialBoundaryLifting p x) (hy : InitialBoundaryLifting p y)
    (hxy : p.app (Opposite.op ⦋0⦌) x = p.app (Opposite.op ⦋0⦌) y) : VertexIso x y

```

**DoubleCoconeUniversality.lean**

```text
instance ihom_pre_innerFibration {A B K C : SSet.{u}} [Quasicategory C]
    (i : A ⟶ B) [Mono i] : InnerFibration ((ihom K).map ((pre i).app C))

def doubleCoconeRestriction (J K C : SSet.{u}) :
    (ihom (join J (Δ[0] : SSet.{u}))).obj ((ihom (join K (Δ[0] : SSet.{u}))).obj C) ⟶
      (ihom J).obj ((ihom K).obj C)

instance doubleCoconeRestriction_innerFibration (J K C : SSet.{u}) [Quasicategory C] :
    InnerFibration (doubleCoconeRestriction J K C)

lemma doubleCoconeRestriction_otherOrder (J K C : SSet.{u}) :
    doubleCoconeRestriction J K C =
      (ihom (join J (Δ[0] : SSet.{u}))).map (coconeRestriction K C) ≫
        coconeRestriction J ((ihom K).obj C)

lemma doubleCocone_initial_outer_inner {J K C : SSet.{u}} [Quasicategory C]
    (F : join J (Δ[0] : SSet.{u}) ⟶ (ihom (join K (Δ[0] : SSet.{u}))).obj C)
    (houter : IsColimitCone (⟨F, rfl⟩ : JoinCocone (joinInl J Δ[0] ≫ F)))
    (hinner : ∀ j : J _⦋0⦌, InitialBoundaryLifting (coconeRestriction K C)
      ((joinInl J Δ[0] ≫ F).app (Opposite.op ⦋0⦌) j)) :
    InitialBoundaryLifting (doubleCoconeRestriction J K C) (functorVertex F)

lemma doubleCocone_initial_inner_outer {J K C : SSet.{u}} [Quasicategory C]
    (F : join J (Δ[0] : SSet.{u}) ⟶ (ihom (join K (Δ[0] : SSet.{u}))).obj C)
    (hinner : ∀ j : (join J (Δ[0] : SSet.{u})) _⦋0⦌,
      InitialBoundaryLifting (coconeRestriction K C) (F.app (Opposite.op ⦋0⦌) j))
    (houter : IsColimitCone (⟨F ≫ coconeRestriction K C, rfl⟩ :
      JoinCocone (joinInl J Δ[0] ≫ F ≫ coconeRestriction K C))) :
    InitialBoundaryLifting (doubleCoconeRestriction J K C) (functorVertex F)

def doubleCoconeUniversalIso {J K C : SSet.{u}} [Quasicategory C]
    (F G : join J (Δ[0] : SSet.{u}) ⟶ (ihom (join K (Δ[0] : SSet.{u}))).obj C)
    (hF : InitialBoundaryLifting (doubleCoconeRestriction J K C) (functorVertex F))
    (hG : InitialBoundaryLifting (doubleCoconeRestriction J K C) (functorVertex G))
    (he : (doubleCoconeRestriction J K C).app (Opposite.op ⦋0⦌) (functorVertex F) =
      (doubleCoconeRestriction J K C).app (Opposite.op ⦋0⦌) (functorVertex G)) : FunctorIso F G

```

**ColimitInterchange.lean**

```text
lemma colimitInterchange_initialBoundary {J K C : SSet.{u}} [Quasicategory C]
    (F : join J (Δ[0] : SSet.{u}) ⟶ (ihom (join K (Δ[0] : SSet.{u}))).obj C)
    (houter : IsPointwiseColimitCone (⟨F, rfl⟩ : JoinCocone (joinInl J Δ[0] ≫ F)))
    (hinner : ∀ j : J _⦋0⦌, InitialBoundaryLifting (coconeRestriction K C)
      ((joinInl J Δ[0] ≫ F).app (Opposite.op ⦋0⦌) j))
    (hex : ∀ j : (join J (Δ[0] : SSet.{u})) _⦋0⦌,
      HasColimit ((functorVertexEquiv K C).symm
        ((F ≫ coconeRestriction K C).app (Opposite.op ⦋0⦌) j))) :
    ∀ j : (join J (Δ[0] : SSet.{u})) _⦋0⦌,
      InitialBoundaryLifting (coconeRestriction K C) (F.app (Opposite.op ⦋0⦌) j)

```

**ColimitComparison.lean**

```text
def colimitCoconeIsoOfDiagramIso {K C : SSet.{u}} [Quasicategory C]
    {p q : K ⟶ C} (c : JoinCocone p) (d : JoinCocone q)
    (hc : IsColimitCone c) (hd : IsColimitCone d) (e : FunctorIso p q) : FunctorIso c.val d.val

def pushoutSquareIsoOfSpanIso {C : SSet.{u}} [Quasicategory C]
    (F G : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ C)
    (hF : IsPushoutSquare F) (hG : IsPushoutSquare G)
    (e : FunctorIso (pushoutSpan F) (pushoutSpan G)) : FunctorIso F G

lemma isZeroVertex_pushout_apex_of_zeroSpan {C : SSet.{u}} [Quasicategory C] [HasZeroVertex C]
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ C) (hF : IsPushoutSquare F)
    (hp : ∀ a : (horn 2 0 : SSet.{u}) _⦋0⦌,
      IsZeroVertex ((pushoutSpan F).app (Opposite.op ⦋0⦌) a)) :
    IsZeroVertex (squareVertex F 1 1)

```

**GappedIso.lean**

```text
lemma IsGapped.of_functorIso {n : ℕ} {C : SSet.{u}} [Quasicategory C]
    {F G : arNerve n ⟶ C} (hF : IsGapped F) (e : FunctorIso F G) : IsGapped G

lemma isGapped_iff_of_functorIso {n : ℕ} {C : SSet.{u}} [Quasicategory C]
    {F G : arNerve n ⟶ C} (e : FunctorIso F G) : IsGapped F ↔ IsGapped G

lemma isGapped_of_functorVertex_isZero {n : ℕ} {C : SSet.{u}} [Quasicategory C] [HasZeroVertex C]
    (F : arNerve n ⟶ C) (hF : IsZeroVertex (functorVertex F)) : IsGapped F

```

現在地：L1a・L1b 完了、L1c 継続中。交換補題を標準 cofiber 正方形へ適用し、点ごとの cofiber 補完の gapped 閉性を証明する工程が残る。
S_n の構造射の押し出し保存、多単体構造、境界の coherent な潰し、delooping・Ω 条件・BF スペクトルは未完了。L1d–f 未完了、L1g は別途指示待ち。

検証：対象ビルド成功（2284 jobs）、公理監査成功（626 宣言、標準三公理のみ）。追加公理・sorry なし。

## 6.12 gapped 図式の点ごとの押し出し閉性

二方向の交換を押し出し四角形に適用した。完成後の各 span の余極限の存在は明示的な前提。
零 span の普遍余錐では全頂点が零対象になることを、定値零余錐との関手同型で証明。
これらを使い、gapped な Ar[n] 図式の span に与えた点ごとの余極限の全行が gapped であることを証明した。
零対角を先に証明し、各標準 cofiber span の余極限の存在を安定性から供給して交換補題を適用する。
全四つ組の押し出しは既存の標準 cofiber 正方形による判定で回収する。
任意の span に点ごとの余極限が存在するとは仮定・結論していない。Core/・Stable/ の公開定義は変更していない。

**PushoutInterchange.lean**

```text
lemma squareDiagram_pre {A C : SSet.{u}}
    (i : A ⟶ (Δ[1] ⊗ Δ[1] : SSet.{u}))
    (v : ((ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj C) _⦋0⦌) :
    (functorVertexEquiv A C).symm (((pre i).app C).app (Opposite.op ⦋0⦌) v) =
      i ≫ squareDiagram v

lemma squareDiagram_pushout_iff_initialBoundary {C : SSet.{u}} [Quasicategory C]
    (v : ((ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj C) _⦋0⦌) :
    IsPushoutSquare (squareDiagram v) ↔
      InitialBoundaryLifting (coconeRestriction (horn 2 0 : SSet.{u}) C)
        (((pre spanCoconeSquareIso.hom).app C).app (Opposite.op ⦋0⦌) v)

lemma pushoutInterchange {J C : SSet.{u}} [Quasicategory C]
    (F : join J (Δ[0] : SSet.{u}) ⟶ (ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj C)
    (houter : IsPointwiseColimitCone (⟨F, rfl⟩ : JoinCocone (joinInl J Δ[0] ≫ F)))
    (hinner : ∀ j : J _⦋0⦌,
      IsPushoutSquare (squareDiagram ((joinInl J Δ[0] ≫ F).app (Opposite.op ⦋0⦌) j)))
    (hex : ∀ j : (join J (Δ[0] : SSet.{u})) _⦋0⦌,
      HasColimit (pushoutSpan (squareDiagram (F.app (Opposite.op ⦋0⦌) j)))) :
    ∀ j : (join J (Δ[0] : SSet.{u})) _⦋0⦌,
      IsPushoutSquare (squareDiagram (F.app (Opposite.op ⦋0⦌) j))

```

**ZeroSpanColimit.lean**

```text
lemma zeroSpanColimit_functorVertex_isZero {C : SSet.{u}} [Quasicategory C] [HasZeroVertex C]
    {p : (horn 2 0 : SSet.{u}) ⟶ C} (c : JoinCocone p) (hc : IsColimitCone c)
    (hp : ∀ a : (horn 2 0 : SSet.{u}) _⦋0⦌, IsZeroVertex (p.app (Opposite.op ⦋0⦌) a)) :
    IsZeroVertex (functorVertex c.val)

lemma zeroSpanColimit_all_vertices_zero {C : SSet.{u}} [Quasicategory C] [HasZeroVertex C]
    {p : (horn 2 0 : SSet.{u}) ⟶ C} (c : JoinCocone p) (hc : IsColimitCone c)
    (hp : ∀ a : (horn 2 0 : SSet.{u}) _⦋0⦌, IsZeroVertex (p.app (Opposite.op ⦋0⦌) a))
    (v : (join (horn 2 0 : SSet.{u}) Δ[0]) _⦋0⦌) :
    IsZeroVertex (c.val.app (Opposite.op ⦋0⦌) v)

```

**GappedPointwiseColimit.lean**

```text
lemma functorVertexEquiv_symm_evaluate {A C : SSet.{u}}
    (v : ((ihom A).obj C) _⦋0⦌) (a : A _⦋0⦌) :
    ((functorVertexEquiv A C).symm v).app (Opposite.op ⦋0⦌) a =
      (evaluateFunctorAt a).app (Opposite.op ⦋0⦌) v

lemma functorVertexEquiv_symm_pre {A B C : SSet.{u}} (i : A ⟶ B)
    (v : ((ihom B).obj C) _⦋0⦌) :
    (functorVertexEquiv A C).symm (((pre i).app C).app (Opposite.op ⦋0⦌) v) =
      i ≫ (functorVertexEquiv B C).symm v

lemma gapped_pointwiseColimit_zero_diagonal {n : ℕ} {C : SSet.{u}}
    [Quasicategory C] [HasZeroVertex C]
    (F : join (horn 2 0 : SSet.{u}) Δ[0] ⟶ (ihom (arNerve n)).obj C)
    (hF : IsPointwiseColimitCone (⟨F, rfl⟩ : JoinCocone
      (joinInl (horn 2 0 : SSet.{u}) Δ[0] ≫ F)))
    (hg : ∀ a : (horn 2 0 : SSet.{u}) _⦋0⦌, IsGapped
      ((functorVertexEquiv (arNerve n) C).symm
        ((joinInl (horn 2 0 : SSet.{u}) Δ[0] ≫ F).app (Opposite.op ⦋0⦌) a)))
    (j : (join (horn 2 0 : SSet.{u}) Δ[0]) _⦋0⦌) (i : Fin (n + 1)) :
    IsZeroVertex (((functorVertexEquiv (arNerve n) C).symm (F.app (Opposite.op ⦋0⦌) j)).app
      (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ (arObj i i le_rfl)))

lemma gapped_pointwiseColimit {n : ℕ} {C : SSet.{u}} [Quasicategory C] [IsStable C]
    (F : join (horn 2 0 : SSet.{u}) Δ[0] ⟶ (ihom (arNerve n)).obj C)
    (hF : IsPointwiseColimitCone (⟨F, rfl⟩ : JoinCocone
      (joinInl (horn 2 0 : SSet.{u}) Δ[0] ≫ F)))
    (hg : ∀ a : (horn 2 0 : SSet.{u}) _⦋0⦌, IsGapped
      ((functorVertexEquiv (arNerve n) C).symm
        ((joinInl (horn 2 0 : SSet.{u}) Δ[0] ≫ F).app (Opposite.op ⦋0⦌) a))) :
    ∀ j : (join (horn 2 0 : SSet.{u}) Δ[0]) _⦋0⦌, IsGapped
      ((functorVertexEquiv (arNerve n) C).symm (F.app (Opposite.op ⦋0⦌) j))

```

現在地：L1a・L1b 完了、L1c 継続中。点ごとの押し出し補完が gapped 条件を保つことは証明済み。
S_n の包含による cofiber の保存・反映への接続、構造射の押し出し保存、多単体構造、境界の coherent な潰し、delooping・Ω 条件・BF スペクトルは未完了。
L1d–f 未完了、L1g は別途指示待ち。

検証：対象ビルド成功（2287 jobs）、公理監査成功（635 宣言、標準三公理のみ）。追加公理・sorry なし。
