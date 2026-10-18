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

**L1a・L1b 完了。L1c 進行中（空間模型・零対象比較・後合成・有限反復対象と零方向の可縮性、関手圏・S_n・有限反復の安定性、全多単体構造・入力についての自然性と対角実現の関手性、自然な基点を持つ K 空間の関手と旧模型との全基点 π_* 比較、全零方向の境界の自然な商と局所化・全基点 π_* 比較まで実装済み）。L1d–f 未完了、L1g は別途指示待ち。**
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

## 6.13 S_n の包含と構造射の cofiber 保存

全部分複体の包含による余極限の反映を、内部 Hom の境界持ち上げ性から証明。
点ごとの余極限が存在する S_n の span の普遍余錐を周囲で構成して gapped 閉性で持ち上げ、
S_n 内の任意の普遍余錐と同型に比較して包含後の点ごとの普遍性を得た。
零角つきの正方形では、必要な点ごとの存在を安定性から供給した。
したがって S_n の包含は cofiber の普遍性を追加仮定なしに保ち反映し、Ar の全点で判定できる。
面・退化写像と既存の後合成写像の cofiber 保存も証明した。
任意の押し出しの保存とは区別し、Core/・Stable/ の公開定義は変更していない。

**FullSubcomplexColimits.lean**

```text
lemma ihom_fullSubcomplex_hasLiftingProperty_of_vertexSurjective {A B X : SSet.{u}}
    (K : SSet.{u}) (P : X _⦋0⦌ → Prop) (i : A ⟶ B)
    (hi : Function.Surjective (i.app (Opposite.op ⦋0⦌))) :
    HasLiftingProperty i ((ihom K).map (fullSubcomplexOnVertices X P).ι)

lemma initialBoundaryLifting_reflect_of_boundary_lifting {E B E' B' : SSet.{u}}
    (p : E ⟶ B) (q : E' ⟶ B') (i : E ⟶ E') (j : B ⟶ B') [Mono j]
    (h : i ≫ q = p ≫ j)
    (hi : ∀ n : ℕ, HasLiftingProperty (boundary (n + 1)).ι i)
    {x : E _⦋0⦌} (hx : InitialBoundaryLifting q (i.app (Opposite.op ⦋0⦌) x)) :
    InitialBoundaryLifting p x

lemma isColimitCone_fullSubcomplex_of_ambient {K X : SSet.{u}} [Quasicategory X]
    (P : X _⦋0⦌ → Prop) {p : K ⟶ (fullSubcomplexOnVertices X P : SSet.{u})}
    (c : JoinCocone p)
    (hc : IsColimitCone (mapJoinCocone (fullSubcomplexOnVertices X P).ι c)) :
    IsColimitCone c

```

**GappedColimitCocones.lean**

```text
lemma exists_gapped_pointwiseColimitCocone {n : ℕ} {C : SSet.{u}}
    [Quasicategory C] [IsStable C] (p : (horn 2 0 : SSet.{u}) ⟶ sConstruction n C)
    (hp : HasPointwiseColimits (p ≫ (gappedSubcomplex n C).ι)) :
    ∃ c : JoinCocone p, IsPointwiseColimitCone (mapJoinCocone (gappedSubcomplex n C).ι c)

lemma isColimitCone_gapped_of_pointwise {n : ℕ} {C : SSet.{u}} [Quasicategory C]
    {p : (horn 2 0 : SSet.{u}) ⟶ sConstruction n C} (c : JoinCocone p)
    (hc : IsPointwiseColimitCone (mapJoinCocone (gappedSubcomplex n C).ι c)) :
    IsColimitCone c

lemma isPointwiseColimitCone_gappedInclusion_of_hasPointwiseColimits {n : ℕ} {C : SSet.{u}}
    [Quasicategory C] [IsStable C] {p : (horn 2 0 : SSet.{u}) ⟶ sConstruction n C}
    (hp : HasPointwiseColimits (p ≫ (gappedSubcomplex n C).ι))
    (c : JoinCocone p) (hc : IsColimitCone c) :
    IsPointwiseColimitCone (mapJoinCocone (gappedSubcomplex n C).ι c)

lemma isColimitCone_gappedInclusion_iff_of_hasPointwiseColimits {n : ℕ} {C : SSet.{u}}
    [Quasicategory C] [IsStable C] {p : (horn 2 0 : SSet.{u}) ⟶ sConstruction n C}
    (hp : HasPointwiseColimits (p ≫ (gappedSubcomplex n C).ι)) (c : JoinCocone p) :
    IsColimitCone c ↔ IsColimitCone (mapJoinCocone (gappedSubcomplex n C).ι c)

```

**GappedCofibers.lean**

```text
def gappedInclusionZeroTriangle {n : ℕ} {C : SSet.{u}} [Quasicategory C] [HasZeroVertex C]
    (t : ZeroTriangle (sConstruction n C)) : ZeroTriangle ((ihom (arNerve n)).obj C)

lemma gappedInclusion_zeroSpan_hasPointwiseColimits {n : ℕ} {C : SSet.{u}}
    [Quasicategory C] [IsStable C] (t : ZeroTriangle (sConstruction n C)) :
    HasPointwiseColimits (pushoutSpan t.square ≫ (gappedSubcomplex n C).ι)

lemma gappedInclusion_cofiber_iff {n : ℕ} {C : SSet.{u}} [Quasicategory C] [IsStable C]
    (t : ZeroTriangle (sConstruction n C)) :
    IsCofiberSequence t ↔ IsPushoutSquare (t.square ≫ (gappedSubcomplex n C).ι)

lemma gappedInclusion_cofiber_iff_pointwise {n : ℕ} {C : SSet.{u}}
    [Quasicategory C] [IsStable C] (t : ZeroTriangle (sConstruction n C)) :
    IsCofiberSequence t ↔ ∀ a : (arNerve n) _⦋0⦌,
      IsPushoutSquare (t.square ≫ (gappedSubcomplex n C).ι ≫ evaluateFunctorAt a)

```

**StructureMapCofibers.lean**

```text
lemma sMap_gapped_evaluate {m n : ℕ} (C : SSet.{u})
    (θ : Fin (m + 1) →o Fin (n + 1)) (a : (arNerve m) _⦋0⦌) :
    sMap C θ ≫ (gappedSubcomplex m C).ι ≫ evaluateFunctorAt a =
      (gappedSubcomplex n C).ι ≫ evaluateFunctorAt ((arNerveMap θ).app (Opposite.op ⦋0⦌) a)

lemma sPostcomp_gapped_evaluate (n : ℕ) {C D : SSet.{u}}
    (f : C ⟶ D) (hf : PreservesSConstructionData f) (a : (arNerve n) _⦋0⦌) :
    sPostcomp n f hf ≫ (gappedSubcomplex n D).ι ≫ evaluateFunctorAt a =
      (gappedSubcomplex n C).ι ≫ evaluateFunctorAt a ≫ f

def sMapZeroTriangle {m n : ℕ} {C : SSet.{u}} [Quasicategory C] [HasZeroVertex C]
    (θ : Fin (m + 1) →o Fin (n + 1)) (t : ZeroTriangle (sConstruction n C)) :
    ZeroTriangle (sConstruction m C)

def sPostcompZeroTriangle {n : ℕ} {C D : SSet.{u}} [Quasicategory C] [Quasicategory D]
    [HasZeroVertex C] (f : C ⟶ D) (hf : PreservesSConstructionData f)
    (t : ZeroTriangle (sConstruction n C)) : ZeroTriangle (sConstruction n D)

lemma sMap_preserves_cofiber {m n : ℕ} {C : SSet.{u}} [Quasicategory C] [IsStable C]
    (θ : Fin (m + 1) →o Fin (n + 1)) (t : ZeroTriangle (sConstruction n C))
    (ht : IsCofiberSequence t) : IsCofiberSequence (sMapZeroTriangle θ t)

lemma sPostcomp_preserves_cofiber {n : ℕ} {C D : SSet.{u}}
    [Quasicategory C] [IsStable C] [Quasicategory D] [IsStable D]
    (f : C ⟶ D) (hf : PreservesSConstructionData f) (t : ZeroTriangle (sConstruction n C))
    (ht : IsCofiberSequence t) : IsCofiberSequence (sPostcompZeroTriangle f hf t)

```

現在地：L1a・L1b 完了、L1c 継続中。S_n の包含の cofiber 保存・反映と構造射の cofiber 保存は証明済み。
任意の押し出しに対する構造射の保存、多単体的反復の全構造射、境界の coherent な潰し、delooping・Ω 条件・BF スペクトルは未完了。L1d–f 未完了、L1g は別途指示待ち。

検証：対象ビルド成功（2291 jobs）、公理監査成功（652 宣言、標準三公理のみ）。追加公理・sorry なし。

## 6.14 単体的自己関手・全有限反復の多単体構造と自然性

標準 cofiber 正方形による既存の gapped 判定により、零対象と cofiber を保つ射で同じ S_n の後合成を構成した。
全四つ組の押し出し条件と全 gapped 図式を保持し、従来の保存条件による sPostcomp とは厳密に一致することを証明。
新しい保存条件は恒等・合成・S_n の後合成・面退化で閉じる。従来の全押し出し保存条件は変更していない。
StableModel は既存の IsStable と quasicategory 性を束ねるだけで、Core/・Stable/ の公開定義は変更しない。
S• を安定な入力上の単体的自己関手として束ね、任意の有限反復の全多単体構造を自己関手の合成で構成した。
各対象は既存のリスト版と厳密に一致する。各多次数で安定・quasicategory、各 core は Kan、零方向では可縮。
入力の射について関手的であり、対角実現も関手として構成済み。対角が Kan であるとは主張しない。

**CofiberMaps.lean**

```text
def PreservesCofiberData {C D : SSet.{u}} (f : C ⟶ D) : Prop

lemma PreservesSConstructionData.toCofiberData {C D : SSet.{u}} {f : C ⟶ D}
    (hf : PreservesSConstructionData f) : PreservesCofiberData f

lemma preservesCofiberData_id (C : SSet.{u}) : PreservesCofiberData (𝟙 C)

lemma PreservesCofiberData.comp {C D E : SSet.{u}} {f : C ⟶ D} {g : D ⟶ E}
    (hf : PreservesCofiberData f) (hg : PreservesCofiberData g) : PreservesCofiberData (f ≫ g)

lemma IsGapped.postcomp_of_cofiber {n : ℕ} {C D : SSet.{u}} [Quasicategory D]
    {F : arNerve n ⟶ C} (hF : IsGapped F) (f : C ⟶ D) (hf : PreservesCofiberData f) :
    IsGapped (F ≫ f)

def sPostcompCofiber (n : ℕ) {C D : SSet.{u}} [Quasicategory D]
    (f : C ⟶ D) (hf : PreservesCofiberData f) : sConstruction n C ⟶ sConstruction n D

lemma sPostcompCofiber_ι (n : ℕ) {C D : SSet.{u}} [Quasicategory D]
    (f : C ⟶ D) (hf : PreservesCofiberData f) :
    sPostcompCofiber n f hf ≫ (gappedSubcomplex n D).ι =
      (gappedSubcomplex n C).ι ≫ (ihom (arNerve n)).map f

lemma sPostcompCofiber_eq_sPostcomp (n : ℕ) {C D : SSet.{u}} [Quasicategory D]
    (f : C ⟶ D) (hf : PreservesSConstructionData f) :
    sPostcompCofiber n f (PreservesSConstructionData.toCofiberData hf) = sPostcomp n f hf

lemma sPostcompCofiber_gapped_evaluate (n : ℕ) {C D : SSet.{u}} [Quasicategory D]
    (f : C ⟶ D) (hf : PreservesCofiberData f) (a : (arNerve n) _⦋0⦌) :
    sPostcompCofiber n f hf ≫ (gappedSubcomplex n D).ι ≫ evaluateFunctorAt a =
      (gappedSubcomplex n C).ι ≫ evaluateFunctorAt a ≫ f

lemma sPostcompCofiber_isZeroVertex {n : ℕ} {C D : SSet.{u}}
    [Quasicategory C] [HasZeroVertex C] [Quasicategory D]
    (f : C ⟶ D) (hf : PreservesCofiberData f)
    {v : (sConstruction n C) _⦋0⦌} (hv : IsZeroVertex v) :
    IsZeroVertex ((sPostcompCofiber n f hf).app (Opposite.op ⦋0⦌) v)

lemma preservesCofiberData_sPostcompCofiber (n : ℕ) {C D : SSet.{u}}
    [Quasicategory C] [IsStable C] [Quasicategory D] [IsStable D]
    (f : C ⟶ D) (hf : PreservesCofiberData f) :
    PreservesCofiberData (sPostcompCofiber n f hf)

lemma preservesCofiberData_sMap {m n : ℕ} (C : SSet.{u}) [Quasicategory C] [IsStable C]
    (θ : Fin (m + 1) →o Fin (n + 1)) : PreservesCofiberData (sMap C θ)

```

**CofiberPostcompLaws.lean**

```text
lemma sPostcompCofiber_id (n : ℕ) (C : SSet.{u}) [Quasicategory C] :
    sPostcompCofiber n (𝟙 C) (preservesCofiberData_id C) = 𝟙 (sConstruction n C)

lemma sPostcompCofiber_comp (n : ℕ) {C D E : SSet.{u}} [Quasicategory D] [Quasicategory E]
    (f : C ⟶ D) (g : D ⟶ E) (hf : PreservesCofiberData f) (hg : PreservesCofiberData g) :
    sPostcompCofiber n (f ≫ g) (PreservesCofiberData.comp hf hg) =
      sPostcompCofiber n f hf ≫ sPostcompCofiber n g hg

lemma sPostcompCofiber_sMap {m n : ℕ} {C D : SSet.{u}} [Quasicategory D]
    (f : C ⟶ D) (hf : PreservesCofiberData f) (θ : Fin (m + 1) →o Fin (n + 1)) :
    sPostcompCofiber n f hf ≫ sMap D θ = sMap C θ ≫ sPostcompCofiber m f hf

lemma sPostcompCofiber_zeroVertex (n : ℕ) {C D : SSet.{u}} [Quasicategory C] [Quasicategory D]
    (f : C ⟶ D) (hf : PreservesCofiberData f) (z : C _⦋0⦌) (hz : IsZeroVertex z) :
    (sPostcompCofiber n f hf).app (Opposite.op ⦋0⦌) (sConstructionZeroVertex n z hz) =
      sConstructionZeroVertex n (f.app (Opposite.op ⦋0⦌) z) (hf.1 z hz)

```

**StableModels.lean**

```text
structure StableModel

instance stableModelCategory : Category.{u} StableModel.{u}

def stableModelForget : StableModel.{u} ⥤ SSet.{u}

def sStableModel (n : ℕ) (X : StableModel.{u}) : StableModel.{u}

def sEndofunctor (n : ℕ) : StableModel.{u} ⥤ StableModel.{u}

def sEndofunctorMap {m n : ℕ} (θ : Fin (m + 1) →o Fin (n + 1)) :
    sEndofunctor.{u} n ⟶ sEndofunctor m

def simplicialStableEndofunctor : SimplexCategoryᵒᵖ ⥤ (StableModel.{u} ⥤ StableModel.{u})

```

**MultiSimplicial.lean**

```text
def multiSEndofunctor : (r : ℕ) →
    (Fin r → SimplexCategoryᵒᵖ) ⥤ (StableModel.{u} ⥤ StableModel.{u})

def multiSConstruction (r : ℕ) (X : StableModel.{u}) : (Fin r → SimplexCategoryᵒᵖ) ⥤ SSet.{u}

instance multiSConstruction_quasicategory (r : ℕ) (X : StableModel.{u})
    (d : Fin r → SimplexCategoryᵒᵖ) : Quasicategory ((multiSConstruction r X).obj d)

instance multiSConstruction_isStable (r : ℕ) (X : StableModel.{u})
    (d : Fin r → SimplexCategoryᵒᵖ) : IsStable ((multiSConstruction r X).obj d)

lemma multiSConstruction_obj_succ (r : ℕ) (X : StableModel.{u})
    (d : Fin (r + 1) → SimplexCategoryᵒᵖ) :
    (multiSConstruction (r + 1) X).obj d =
      sConstruction (d 0).unop.len ((multiSConstruction r X).obj (fun i => d i.succ))

lemma multiSConstruction_obj_eq_iterated (r : ℕ) (X : StableModel.{u})
    (d : Fin r → SimplexCategoryᵒᵖ) :
    (multiSConstruction r X).obj d =
      iteratedSConstruction (List.ofFn (fun i => (d i).unop.len)) X.carrier

def multiCoreSConstruction (r : ℕ) (X : StableModel.{u}) :
    (Fin r → SimplexCategoryᵒᵖ) ⥤ SSet.{u}

instance multiCoreSConstruction_kanComplex (r : ℕ) (X : StableModel.{u})
    (d : Fin r → SimplexCategoryᵒᵖ) : KanComplex ((multiCoreSConstruction r X).obj d)

lemma multiSConstruction_isContractibleKan_of_zero_coordinate (r : ℕ) (X : StableModel.{u})
    (d : Fin r → SimplexCategoryᵒᵖ) (i : Fin r) (hi : (d i).unop.len = 0) :
    IsContractibleKan ((multiSConstruction r X).obj d)

lemma multiCoreSConstruction_isContractibleKan_of_zero_coordinate (r : ℕ) (X : StableModel.{u})
    (d : Fin r → SimplexCategoryᵒᵖ) (i : Fin r) (hi : (d i).unop.len = 0) :
    IsContractibleKan ((multiCoreSConstruction r X).obj d)

```

**MultiRealization.lean**

```text
def multiSConstructionFunctor (r : ℕ) :
    StableModel.{u} ⥤ ((Fin r → SimplexCategoryᵒᵖ) ⥤ SSet.{u})

lemma multiSConstructionFunctor_obj (r : ℕ) (X : StableModel.{u}) :
    (multiSConstructionFunctor r).obj X = multiSConstruction r X

def multiCoreSConstructionFunctor (r : ℕ) :
    StableModel.{u} ⥤ ((Fin r → SimplexCategoryᵒᵖ) ⥤ SSet.{u})

lemma multiCoreSConstructionFunctor_obj (r : ℕ) (X : StableModel.{u}) :
    (multiCoreSConstructionFunctor r).obj X = multiCoreSConstruction r X

def multiIndexDiagonal (r : ℕ) : SimplexCategoryᵒᵖ ⥤ (Fin r → SimplexCategoryᵒᵖ)

def multiDiagonalFunctor (r : ℕ) :
    ((Fin r → SimplexCategoryᵒᵖ) ⥤ SSet.{u}) ⥤ SSet.{u}

def multiRealizationFunctor (r : ℕ) : StableModel.{u} ⥤ SSet.{u}

def multiDiagonalCoreSConstruction (r : ℕ) (X : StableModel.{u}) : SSet.{u}

lemma multiDiagonalCoreSConstruction_obj (r : ℕ) (X : StableModel.{u}) (n : SimplexCategoryᵒᵖ) :
    (multiDiagonalCoreSConstruction r X).obj n =
      ((multiCoreSConstruction r X).obj (fun _ => n)).obj n

```

StableModel の公開フィールドは `carrier : SSet.{u}`、`[quasicategory : Quasicategory carrier]`、`[stable : IsStable carrier]`。コンストラクターとこれらの射影も監査対象。

現在地：L1a・L1b 完了、L1c 継続中。S_n の包含・構造射の cofiber 保存、反復に必要な保存条件の閉性、全有限反復の多単体構造・自然性・対角実現の関手性は証明済み。
反復実現の基点と零対象の選択に関する coherent な自然性、零方向の境界の coherent な潰し、Kan 置換、delooping・Ω 条件・BF スペクトルは未完了。
任意の押し出し保存と cofiber 保存条件との同値は未証明。反復の構造射は、証明済みの cofiber 保存条件と元の全 gapped 条件を使う。
L1d–f 未完了、L1g は別途指示待ち。

検証：対象ビルド成功（2296 jobs）、公理監査成功（698 宣言、標準三公理のみ）。追加公理・sorry なし。

## 6.15 同時零段の自然な collapse と旧 K 空間との π_* 比較

任意の単体的単体集合 X について零段 X_0 から対角への包含が単射で自然であることを証明し、
その零段全体を一点へ潰す通常の cofiber を点つき関手として構成した。零頂点の選択を含まない。
可縮 Kan な零段の collapse の可逆性は、同じ単射を持つ pushout cube の既存の HA 定理から導いた。
さらにホーン分解・局所化の Kan fibration 検出・L9 の π_* 定理により、Kan 置換後の全基点・全自然数次数の π_* 同型へ接続した。
値域モデル構造や HT-KQ・追加の検出公理は仮定していない。
正の反復 S の同時零段は既存の零方向の可縮性から可縮。これに collapse と点つき Kan 置換を適用し、
入力について関手的な点つき反復実現と reducedKSpaceFunctor を構成した。
一重の模型は従来の単体的 core と厳密に一致し、旧 kSpace から新模型への実際の写像が全基点 π_* 同型であることを証明。
旧 API の chosen zero 保存を仮定する写像に対して比較の自然性も証明。新しい関手自身には chosen zero 保存を要求しない。
Core/・Stable/・HA/・Spectra/ の公開定義は変更していない。

**DiagonalReduction.lean**

```text
def simplicialDiagonalFunctor : (SimplexCategoryᵒᵖ ⥤ SSet.{u}) ⥤ SSet.{u}

instance diagonalZeroColumn_mono (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    Mono (diagonalZeroColumn X)

def diagonalZeroColumnNat :
    (evaluation SimplexCategoryᵒᵖ SSet.{u}).obj (Opposite.op ⦋0⦌) ⟶ simplicialDiagonalFunctor

def reducedDiagonal (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) : PointedSimplicialSet.{u}

def diagonalReductionQuotient (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    simplicialDiagonalFunctor.obj X ⟶ (reducedDiagonal X).right

def reducedDiagonalMap {X Y : SimplexCategoryᵒᵖ ⥤ SSet.{u}} (f : X ⟶ Y) :
    reducedDiagonal X ⟶ reducedDiagonal Y

lemma reducedDiagonalMap_quotient {X Y : SimplexCategoryᵒᵖ ⥤ SSet.{u}} (f : X ⟶ Y) :
    diagonalReductionQuotient X ≫ (reducedDiagonalMap f).right =
      simplicialDiagonalFunctor.map f ≫ diagonalReductionQuotient Y

def reducedDiagonalFunctor : (SimplexCategoryᵒᵖ ⥤ SSet.{u}) ⥤ PointedSimplicialSet.{u}

def diagonalReductionNat : simplicialDiagonalFunctor ⟶
    reducedDiagonalFunctor ⋙ PointedSimplicialSet.forget

```

**LocalizedTrivialFibrations.lean**

```text
lemma map_isIso_of_trivialKanFibration {D : Type v} [Category.{w} D]
    (L : SSet.{u} ⥤ D) (hL : anodyneExtensions.IsInvertedBy L)
    {E B : SSet.{u}} (p : E ⟶ B) [TrivialKanFibration p] : IsIso (L.map p)

```

**ReductionEquivalence.lean**

```text
lemma trivialKanFibration_toUnit_of_contractible {A : SSet.{u}} (hA : IsContractibleKan A) :
    TrivialKanFibration (toUnit A)

lemma cofiberQuotient_image_isIso_of_contractible {D : Type v} [Category.{w} D]
    (L : SSet.{u} ⥤ D) (hL : anodyneExtensions.IsInvertedBy L)
    {A B : SSet.{u}} (i : A ⟶ B) [Mono i] (hA : IsContractibleKan A) :
    IsIso (L.map (PointedObject.cofiberQuotient i))

lemma diagonalReductionQuotient_image_isIso {D : Type v} [Category.{w} D]
    (L : SSet.{u} ⥤ D) (hL : anodyneExtensions.IsInvertedBy L)
    (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) (hX : IsContractibleKan (X.obj (Opposite.op ⦋0⦌))) :
    IsIso (L.map (diagonalReductionQuotient X))

```

**LocalizedPiComparison.lean**

```text
lemma kanPiIsomorphism_of_localized_isIso {A B : SSet.{u}} [KanComplex A] [KanComplex B]
    (f : A ⟶ B) (hf : IsIso (AnodyneHomotopy.anodyneQ.map f)) : Spectra.KanPiIsomorphism f

lemma pointedKanReplacement_map_piIsomorphism_of_localized_isIso
    {A B : PointedSimplicialSet.{u}} (f : A ⟶ B)
    (hf : IsIso (AnodyneHomotopy.anodyneQ.map f.right)) :
    Spectra.KanPiIsomorphism (Spectra.PointedKanReplacement.map f).right

```

**ReducedMultiRealization.lean**

```text
def multiDiagonalDiagramFunctor (r : ℕ) : StableModel.{u} ⥤ (SimplexCategoryᵒᵖ ⥤ SSet.{u})

lemma multiDiagonalDiagram_zero_isContractibleKan (r : ℕ) (X : StableModel.{u}) :
    IsContractibleKan (((multiDiagonalDiagramFunctor (r + 1)).obj X).obj (Opposite.op ⦋0⦌))

def reducedMultiRealizationFunctor (r : ℕ) : StableModel.{u} ⥤ PointedSimplicialSet.{u}

def multiRealizationReductionNat (r : ℕ) : multiRealizationFunctor (r + 1) ⟶
    reducedMultiRealizationFunctor r ⋙ PointedSimplicialSet.forget

lemma multiRealizationReduction_image_isIso {D : Type v} [Category.{w} D]
    (L : SSet.{u} ⥤ D) (hL : anodyneExtensions.IsInvertedBy L) (r : ℕ) (X : StableModel.{u}) :
    IsIso (L.map ((multiRealizationReductionNat r).app X))

def reducedMultiKanRealizationFunctor (r : ℕ) : StableModel.{u} ⥤ PointedSimplicialSet.{u}

instance reducedMultiKanRealization_kanComplex (r : ℕ) (X : StableModel.{u}) :
    KanComplex (((reducedMultiKanRealizationFunctor r).obj X).right)

def reducedKSpaceFunctor : StableModel.{u} ⥤ PointedSimplicialSet.{u}

instance reducedKSpaceFunctor_kanComplex (X : StableModel.{u}) :
    KanComplex ((reducedKSpaceFunctor.obj X).right)

```

**ReductionPointedComparison.lean**

```text
def diagonalReductionPointedMap (X : SimplexCategoryᵒᵖ ⥤ SSet.{u})
    (z : (X.obj (Opposite.op ⦋0⦌)) _⦋0⦌) :
    PointedSimplicialSet.ofVertex (simplicialDiagonalFunctor.obj X)
      ((diagonalZeroColumn X).app (Opposite.op ⦋0⦌) z) ⟶ reducedDiagonal X

lemma diagonalReductionPointedMap_kan_piIsomorphism (X : SimplexCategoryᵒᵖ ⥤ SSet.{u})
    (hX : IsContractibleKan (X.obj (Opposite.op ⦋0⦌)))
    (z : (X.obj (Opposite.op ⦋0⦌)) _⦋0⦌) :
    Spectra.KanPiIsomorphism (Spectra.PointedKanReplacement.map (diagonalReductionPointedMap X z)).right

def diagonalReductionLoopMap (X : SimplexCategoryᵒᵖ ⥤ SSet.{u})
    (z : (X.obj (Opposite.op ⦋0⦌)) _⦋0⦌) :
    Spectra.loopSpace (Spectra.PointedKanReplacement.obj
      (PointedSimplicialSet.ofVertex (simplicialDiagonalFunctor.obj X)
        ((diagonalZeroColumn X).app (Opposite.op ⦋0⦌) z))) ⟶
      Spectra.loopSpace (Spectra.PointedKanReplacement.obj (reducedDiagonal X))

lemma diagonalReductionLoopMap_piIsomorphism (X : SimplexCategoryᵒᵖ ⥤ SSet.{u})
    (hX : IsContractibleKan (X.obj (Opposite.op ⦋0⦌)))
    (z : (X.obj (Opposite.op ⦋0⦌)) _⦋0⦌) :
    Spectra.KanPiIsomorphism (diagonalReductionLoopMap X z).right

```

**ReducedKComparison.lean**

```text
lemma multiDiagonalDiagramFunctor_one_obj (X : StableModel.{u}) :
    (multiDiagonalDiagramFunctor 1).obj X = simplicialCoreSConstruction X.carrier

def reducedSRealizationComparison (X : StableModel.{u}) :
    pointedSRealization X.carrier ⟶ (reducedMultiRealizationFunctor 0).obj X

lemma reducedSRealizationComparison_kan_piIsomorphism (X : StableModel.{u}) :
    Spectra.KanPiIsomorphism (Spectra.PointedKanReplacement.map (reducedSRealizationComparison X)).right

def kSpaceReductionComparison (X : StableModel.{u}) :
    kSpace X.carrier ⟶ reducedKSpaceFunctor.obj X

lemma kSpaceReductionComparison_piIsomorphism (X : StableModel.{u}) :
    Spectra.KanPiIsomorphism (kSpaceReductionComparison X).right

lemma reducedSRealizationComparison_naturality {X Y : StableModel.{u}}
    (f : X.carrier ⟶ Y.carrier) (hf : PreservesSConstructionData f) (hz : PreservesChosenZero f) :
    pointedSPostcomp f hf hz ≫ reducedSRealizationComparison Y =
      reducedSRealizationComparison X ≫ (reducedMultiRealizationFunctor 0).map
        (⟨f, PreservesSConstructionData.toCofiberData hf⟩ : X ⟶ Y)

lemma kSpaceReductionComparison_naturality {X Y : StableModel.{u}}
    (f : X.carrier ⟶ Y.carrier) (hf : PreservesSConstructionData f) (hz : PreservesChosenZero f) :
    kSpacePostcomp f hf hz ≫ kSpaceReductionComparison Y =
      kSpaceReductionComparison X ≫ reducedKSpaceFunctor.map
        (⟨f, PreservesSConstructionData.toCofiberData hf⟩ : X ⟶ Y)

```

現在地：L1a・L1b 完了、L1c 継続中。反復の同時零段を潰した自然な基点・Kan 置換・Ω の関手性と旧 K 空間との全基点 π_* 比較は証明済み。
今回潰したのは全 S 方向が同時に零次数となる段だけ。個々の零方向の境界の合併（fat wedge）の coherent な collapse、反復間の構造写像、delooping・Ω 条件・BF 連結スペクトルは未完了。
任意の押し出し保存と cofiber 保存条件との同値は未証明。L1d–f 未完了、L1g は別途指示待ち。

検証：対象ビルド成功（2348 jobs）、公理監査成功（733 宣言、標準三公理のみ）。追加公理・sorry なし。

## 6.16 全零方向の境界の合併と自然な商

個々の S 方向を零次数に固定する添字関手と、その対角実現への単射を構成した。
方向集合 s の像を R_s とすると、R_(s∪t) = R_s ∩ R_t が厳密に成り立つ。
非空 s に対する R_s の弱可縮性は各段の可縮 Kan 性と HA の対角定理から従う。
境界 B(s,t) := ⋃_(i∈s) R_(insert i t) は、非空 s に対し anodyne 局所化で一点と同値。
交差の計算と部分複体の合併を表す pushout の cube により有限帰納した。

正の反復に対し全方向の合併 B(univ,∅) を潰す `boundaryReducedRealization` を定義し、
入力について厳密に自然な点つき関手と Kan 置換を構成した。商写像は任意の anodyne 反転関手で可逆。
境界・対角実現の Kan 性、選択した零対象の保存は仮定しない。
一般の cofiber 比較を追加し、既存の可縮 Kan 版の名前・型は保持した。
Core・Stable・F1・HA・Spectra のファイルに変更はない。

以下の型は namespace `SerrePositivity.KST.SConstruction` 内。
`StableModel` は quasicategory と安定性を持ち、射は `PreservesCofiberData` を満たす射。
`AnodyneHomotopy.anodyneQ` は anodyne extensions による局所化、
`r : ℕ`、`u v w` は独立の宇宙。各定理に記載した前提以外の仮定はない。

**ZeroDirections.lean**

```lean
def zeroCoordinateFunctor {r : ℕ} (i : Fin r) : Bool → ((Fin r → SimplexCategoryᵒᵖ) ⥤ SimplexCategoryᵒᵖ)

def zeroCoordinateNat {r : ℕ} (i : Fin r) : (b : Bool) →
    zeroCoordinateFunctor i b ⟶ Pi.eval (fun _ : Fin r => SimplexCategoryᵒᵖ) i

def zeroCoordinateRetraction {r : ℕ} (i : Fin r) : (b : Bool) →
    (d : Fin r → SimplexCategoryᵒᵖ) → d i ⟶ (zeroCoordinateFunctor i b).obj d

lemma zeroCoordinateNat_retraction {r : ℕ} (i : Fin r) (b : Bool)
    (d : Fin r → SimplexCategoryᵒᵖ) :
    (zeroCoordinateNat i b).app d ≫ zeroCoordinateRetraction i b d =
      𝟙 ((zeroCoordinateFunctor i b).obj d)

def zeroDirectionsIndex {r : ℕ} (s : Finset (Fin r)) :
    (Fin r → SimplexCategoryᵒᵖ) ⥤ (Fin r → SimplexCategoryᵒᵖ)

def zeroDirectionsIndexNat {r : ℕ} (s : Finset (Fin r)) : zeroDirectionsIndex s ⟶ 𝟭 _

def zeroDirectionsIndexRetraction {r : ℕ} (s : Finset (Fin r))
    (d : Fin r → SimplexCategoryᵒᵖ) : d ⟶ (zeroDirectionsIndex s).obj d

lemma zeroDirectionsIndexNat_retraction {r : ℕ} (s : Finset (Fin r))
    (d : Fin r → SimplexCategoryᵒᵖ) :
    (zeroDirectionsIndexNat s).app d ≫ zeroDirectionsIndexRetraction s d =
      𝟙 ((zeroDirectionsIndex s).obj d)

def zeroDirectionsDiagram {r : ℕ} (s : Finset (Fin r)) (X : StableModel.{u}) :
    SimplexCategoryᵒᵖ ⥤ SSet.{u}

def zeroDirectionsDiagramMap {r : ℕ} (s : Finset (Fin r)) (X : StableModel.{u}) :
    zeroDirectionsDiagram s X ⟶ (multiDiagonalDiagramFunctor r).obj X

def zeroDirectionsInclusion {r : ℕ} (s : Finset (Fin r)) (X : StableModel.{u}) :
    simplicialDiagonalFunctor.obj (zeroDirectionsDiagram s X) ⟶ multiDiagonalCoreSConstruction r X

instance zeroDirectionsInclusion_mono {r : ℕ} (s : Finset (Fin r)) (X : StableModel.{u}) :
    Mono (zeroDirectionsInclusion s X)

lemma zeroDirectionsDiagram_isContractibleKan {r : ℕ} (s : Finset (Fin r)) (hs : s.Nonempty)
    (X : StableModel.{u}) (d : SimplexCategoryᵒᵖ) :
    IsContractibleKan ((zeroDirectionsDiagram s X).obj d)
```

**ZeroDirectionsRanges.lean**

```lean
def zeroCoordinateEndomorphism {r : ℕ} (i : Fin r) (b : Bool) (d : Fin r → SimplexCategoryᵒᵖ) :
    d i ⟶ d i

lemma zeroCoordinateEndomorphism_or {r : ℕ} (i : Fin r) (a b : Bool)
    (d : Fin r → SimplexCategoryᵒᵖ) :
    zeroCoordinateEndomorphism i (a || b) d =
      zeroCoordinateEndomorphism i a d ≫ zeroCoordinateEndomorphism i b d

def zeroDirectionsIndexEndomorphism {r : ℕ} (s : Finset (Fin r))
    (d : Fin r → SimplexCategoryᵒᵖ) : d ⟶ d

lemma zeroDirectionsIndexEndomorphism_union {r : ℕ} (s t : Finset (Fin r))
    (d : Fin r → SimplexCategoryᵒᵖ) :
    zeroDirectionsIndexEndomorphism (s ∪ t) d =
      zeroDirectionsIndexEndomorphism s d ≫ zeroDirectionsIndexEndomorphism t d

def zeroDirectionsRetractionAt {r : ℕ} (s : Finset (Fin r)) (X : StableModel.{u})
    (d : SimplexCategoryᵒᵖ) (x : (multiDiagonalCoreSConstruction r X).obj d) :
    (simplicialDiagonalFunctor.obj (zeroDirectionsDiagram s X)).obj d

lemma zeroDirectionsRetractionAt_leftInverse {r : ℕ} (s : Finset (Fin r)) (X : StableModel.{u})
    (d : SimplexCategoryᵒᵖ) :
    Function.LeftInverse (zeroDirectionsRetractionAt s X d) ((zeroDirectionsInclusion s X).app d)

def zeroDirectionsOperator {r : ℕ} (s : Finset (Fin r)) (X : StableModel.{u})
    (d : SimplexCategoryᵒᵖ) (x : (multiDiagonalCoreSConstruction r X).obj d) :
    (multiDiagonalCoreSConstruction r X).obj d

lemma zeroDirectionsOperator_eq_map {r : ℕ} (s : Finset (Fin r)) (X : StableModel.{u})
    (d : SimplexCategoryᵒᵖ) (x : (multiDiagonalCoreSConstruction r X).obj d) :
    zeroDirectionsOperator s X d x =
      ((multiCoreSConstruction r X).map (zeroDirectionsIndexEndomorphism s (fun _ => d))).app d x

lemma zeroDirectionsOperator_union {r : ℕ} (s t : Finset (Fin r)) (X : StableModel.{u})
    (d : SimplexCategoryᵒᵖ) (x : (multiDiagonalCoreSConstruction r X).obj d) :
    zeroDirectionsOperator (s ∪ t) X d x =
      zeroDirectionsOperator t X d (zeroDirectionsOperator s X d x)

def zeroDirectionsRange {r : ℕ} (s : Finset (Fin r)) (X : StableModel.{u}) :
    (multiDiagonalCoreSConstruction r X).Subcomplex

lemma mem_zeroDirectionsRange_iff {r : ℕ} (s : Finset (Fin r)) (X : StableModel.{u})
    (d : SimplexCategoryᵒᵖ) (x : (multiDiagonalCoreSConstruction r X).obj d) :
    x ∈ (zeroDirectionsRange s X).obj d ↔ zeroDirectionsOperator s X d x = x

lemma zeroDirectionsRange_antitone {r : ℕ} {s t : Finset (Fin r)} (hst : s ⊆ t)
    (X : StableModel.{u}) : zeroDirectionsRange t X ≤ zeroDirectionsRange s X

lemma zeroDirectionsRange_union {r : ℕ} (s t : Finset (Fin r)) (X : StableModel.{u}) :
    zeroDirectionsRange (s ∪ t) X = zeroDirectionsRange s X ⊓ zeroDirectionsRange t X
```

**ZeroDirectionsWeak.lean**

```lean
def zeroDirectionsDiagramToPoint {r : ℕ} (s : Finset (Fin r)) (X : StableModel.{u}) :
    zeroDirectionsDiagram s X ⟶ (Functor.const SimplexCategoryᵒᵖ).obj (𝟙_ SSet.{u})

lemma zeroDirectionsRealization_toPoint_localized_isIso {r : ℕ} (s : Finset (Fin r))
    (hs : s.Nonempty) (X : StableModel.{u}) :
    IsIso (AnodyneHomotopy.anodyneQ.map
      (toUnit (simplicialDiagonalFunctor.obj (zeroDirectionsDiagram s X))))

lemma zeroDirectionsRealization_toPoint_image_isIso {D : Type v} [Category.{w} D]
    (L : SSet.{u} ⥤ D) (hL : anodyneExtensions.IsInvertedBy L) {r : ℕ}
    (s : Finset (Fin r)) (hs : s.Nonempty) (X : StableModel.{u}) :
    IsIso (L.map (toUnit (simplicialDiagonalFunctor.obj (zeroDirectionsDiagram s X))))
```

**ZeroBoundary.lean**

```lean
lemma zeroDirectionsRange_toPoint_localized_isIso {r : ℕ} (s : Finset (Fin r))
    (hs : s.Nonempty) (X : StableModel.{u}) :
    IsIso (AnodyneHomotopy.anodyneQ.map (toUnit (zeroDirectionsRange s X : SSet.{u})))

lemma subcomplex_inf_sup {W : SSet.{u}} (A B C : W.Subcomplex) :
    A ⊓ (B ⊔ C) = (A ⊓ B) ⊔ (A ⊓ C)

lemma subcomplex_sup_toPoint_localized_isIso {W : SSet.{u}} (A B : W.Subcomplex)
    (hA : IsIso (AnodyneHomotopy.anodyneQ.map (toUnit (A : SSet.{u}))))
    (hB : IsIso (AnodyneHomotopy.anodyneQ.map (toUnit (B : SSet.{u}))))
    (hI : IsIso (AnodyneHomotopy.anodyneQ.map (toUnit (A ⊓ B : W.Subcomplex).toSSet))) :
    IsIso (AnodyneHomotopy.anodyneQ.map (toUnit (A ⊔ B : W.Subcomplex).toSSet))

def zeroDirectionsBoundary {r : ℕ} (s t : Finset (Fin r)) (X : StableModel.{u}) :
    (multiDiagonalCoreSConstruction r X).Subcomplex

lemma zeroDirectionsBoundary_insert {r : ℕ} (i : Fin r) (s t : Finset (Fin r)) (X : StableModel.{u}) :
    zeroDirectionsBoundary (insert i s) t X =
      zeroDirectionsRange (insert i t) X ⊔ zeroDirectionsBoundary s t X

lemma zeroDirectionsBoundary_inf {r : ℕ} (i : Fin r) (s t : Finset (Fin r)) (X : StableModel.{u}) :
    zeroDirectionsRange (insert i t) X ⊓ zeroDirectionsBoundary s t X =
      zeroDirectionsBoundary s (insert i t) X

lemma zeroDirectionsBoundary_toPoint_localized_isIso {r : ℕ} (s t : Finset (Fin r))
    (hs : s.Nonempty) (X : StableModel.{u}) :
    IsIso (AnodyneHomotopy.anodyneQ.map (toUnit (zeroDirectionsBoundary s t X : SSet.{u})))

def zeroDirectionsFatBoundary (r : ℕ) (X : StableModel.{u}) :
    (multiDiagonalCoreSConstruction r X).Subcomplex

lemma zeroDirectionsFatBoundary_toPoint_localized_isIso (r : ℕ) (X : StableModel.{u}) :
    IsIso (AnodyneHomotopy.anodyneQ.map (toUnit (zeroDirectionsFatBoundary (r + 1) X : SSet.{u})))
```

**ZeroDirectionsNaturality.lean**

```lean
def zeroDirectionsRealizationFunctor {r : ℕ} (s : Finset (Fin r)) : StableModel.{u} ⥤ SSet.{u}

def zeroDirectionsInclusionNat {r : ℕ} (s : Finset (Fin r)) :
    zeroDirectionsRealizationFunctor.{u} s ⟶ multiRealizationFunctor r

lemma zeroDirectionsInclusionNat_app {r : ℕ} (s : Finset (Fin r)) (X : StableModel.{u}) :
    (zeroDirectionsInclusionNat s).app X = zeroDirectionsInclusion s X

lemma zeroDirectionsRange_image_le {r : ℕ} (s : Finset (Fin r)) {X Y : StableModel.{u}}
    (f : X ⟶ Y) :
    (zeroDirectionsRange s X).image ((multiRealizationFunctor r).map f) ≤ zeroDirectionsRange s Y
```

**BoundaryReduction.lean**

```lean
lemma zeroDirectionsBoundary_image_le {r : ℕ} (s t : Finset (Fin r)) {X Y : StableModel.{u}}
    (f : X ⟶ Y) :
    (zeroDirectionsBoundary s t X).image ((multiRealizationFunctor r).map f) ≤
      zeroDirectionsBoundary s t Y

def zeroDirectionsFatBoundaryMap (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    (zeroDirectionsFatBoundary r X : SSet.{u}) ⟶ (zeroDirectionsFatBoundary r Y : SSet.{u})

lemma zeroDirectionsFatBoundaryMap_ι (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    zeroDirectionsFatBoundaryMap r f ≫ (zeroDirectionsFatBoundary r Y).ι =
      (zeroDirectionsFatBoundary r X).ι ≫ (multiRealizationFunctor r).map f

def boundaryReducedRealization (r : ℕ) (X : StableModel.{u}) : PointedSimplicialSet.{u}

def boundaryReductionQuotient (r : ℕ) (X : StableModel.{u}) :
    multiDiagonalCoreSConstruction (r + 1) X ⟶ (boundaryReducedRealization r X).right

def boundaryReducedRealizationMap (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    boundaryReducedRealization r X ⟶ boundaryReducedRealization r Y

lemma boundaryReducedRealizationMap_quotient (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    boundaryReductionQuotient r X ≫ (boundaryReducedRealizationMap r f).right =
      (multiRealizationFunctor (r + 1)).map f ≫ boundaryReductionQuotient r Y

def boundaryReducedRealizationFunctor (r : ℕ) : StableModel.{u} ⥤ PointedSimplicialSet.{u}

def boundaryReductionNat (r : ℕ) : multiRealizationFunctor (r + 1) ⟶
    boundaryReducedRealizationFunctor r ⋙ PointedSimplicialSet.forget

lemma boundaryReductionQuotient_image_isIso {D : Type v} [Category.{w} D]
    (L : SSet.{u} ⥤ D) (hL : anodyneExtensions.IsInvertedBy L) (r : ℕ) (X : StableModel.{u}) :
    IsIso (L.map (boundaryReductionQuotient r X))

def boundaryKanRealizationFunctor (r : ℕ) : StableModel.{u} ⥤ PointedSimplicialSet.{u}

instance boundaryKanRealization_kanComplex (r : ℕ) (X : StableModel.{u}) :
    KanComplex (((boundaryKanRealizationFunctor r).obj X).right)
```

**ReductionEquivalence.lean**

```lean
lemma cofiberQuotient_image_isIso_of_localized_toPoint {D : Type v} [Category.{w} D]
    (L : SSet.{u} ⥤ D) (hL : anodyneExtensions.IsInvertedBy L)
    {A B : SSet.{u}} (i : A ⟶ B) [Mono i]
    (hA : IsIso (AnodyneHomotopy.anodyneQ.map (toUnit A))) :
    IsIso (L.map (PointedObject.cofiberQuotient i))
```

現在地：L1a・L1b 完了、L1c 継続中。全零方向の境界の自然な collapse とその局所化での比較は証明済み。
旧 K 空間との既存の π_* 比較は同時零段を潰す模型についてであり、今回の全境界商との点つき π_* 比較はまだ接続していない。
反復間の構造写像、delooping・Ω 条件・BF 連結スペクトルは未完了。
任意の押し出し保存と cofiber 保存条件との同値は未証明。L1d–f 未完了、L1g は別途指示待ち。

検証：対象ビルド成功（2950 jobs）、公理監査成功（788 宣言、標準三公理のみ）。追加公理・sorry なし。

## 6.17 全零境界商への点つき比較と K 空間の関手

零次数では添字自己射が恒等となるため、反復実現の全頂点が各零方向の像に属する。
したがって正の反復の任意の頂点を基点とした実現から、全境界商への点つき比較射が作れる。
この射は Kan 置換後に L9 の `KanPiIsomorphism` を満たし、L9 の Ω 後にも同じ性質を持つ。
元の実現や境界の Kan 性を要求せず、追加の補完データも仮定しない。

`boundaryKSpaceFunctor` は全境界を潰す一重 S 実現の Kan 置換の Ω。
全 `StableModel` 射について自然であり、選んだ零対象の保存を要求しない。
従来の `kSpace` からの `kSpaceBoundaryComparison` は全基点・全次数の π_* 同型。
旧 API の後合成と比較する自然性の定理だけは、その API が要求する
`PreservesSConstructionData` と `PreservesChosenZero` を明記する。
既存の `kSpace`、同時零段の商やその比較の名前・型は変更しない。

以下は namespace `SerrePositivity.KST.SConstruction` 内の正確な型。
`StableModel` の構造的前提と `universe u`、`open scoped Simplicial` は §6.16 と同じ。

**BoundaryPointedComparison.lean**

```lean
lemma zeroDirectionsIndexEndomorphism_zero {r : ℕ} (s : Finset (Fin r)) :
    zeroDirectionsIndexEndomorphism s (fun _ => Opposite.op ⦋0⦌) = 𝟙 _

lemma vertex_mem_zeroDirectionsRange {r : ℕ} (s : Finset (Fin r)) (X : StableModel.{u})
    (x : (multiDiagonalCoreSConstruction r X) _⦋0⦌) :
    x ∈ (zeroDirectionsRange s X).obj (Opposite.op ⦋0⦌)

lemma vertex_mem_zeroDirectionsFatBoundary (r : ℕ) (X : StableModel.{u})
    (x : (multiDiagonalCoreSConstruction (r + 1) X) _⦋0⦌) :
    x ∈ (zeroDirectionsFatBoundary (r + 1) X).obj (Opposite.op ⦋0⦌)

def cofiberPointedProjection {A B : SSet.{u}} (i : A ⟶ B) (a : A _⦋0⦌) :
    PointedSimplicialSet.ofVertex B (i.app (Opposite.op ⦋0⦌) a) ⟶ PointedObject.cofiber i

def boundaryReductionPointedMap (r : ℕ) (X : StableModel.{u})
    (x : (multiDiagonalCoreSConstruction (r + 1) X) _⦋0⦌) :
    PointedSimplicialSet.ofVertex (multiDiagonalCoreSConstruction (r + 1) X) x ⟶
      boundaryReducedRealization r X

lemma boundaryReductionPointedMap_kan_piIsomorphism (r : ℕ) (X : StableModel.{u})
    (x : (multiDiagonalCoreSConstruction (r + 1) X) _⦋0⦌) :
    Spectra.KanPiIsomorphism
      (Spectra.PointedKanReplacement.map (boundaryReductionPointedMap r X x)).right

def boundaryReductionLoopMap (r : ℕ) (X : StableModel.{u})
    (x : (multiDiagonalCoreSConstruction (r + 1) X) _⦋0⦌) :
    Spectra.loopSpace (Spectra.PointedKanReplacement.obj
      (PointedSimplicialSet.ofVertex (multiDiagonalCoreSConstruction (r + 1) X) x)) ⟶
      Spectra.loopSpace ((boundaryKanRealizationFunctor r).obj X)

lemma boundaryReductionLoopMap_piIsomorphism (r : ℕ) (X : StableModel.{u})
    (x : (multiDiagonalCoreSConstruction (r + 1) X) _⦋0⦌) :
    Spectra.KanPiIsomorphism (boundaryReductionLoopMap r X x).right
```

**BoundaryKComparison.lean**

```lean
def boundaryKSpaceFunctor : StableModel.{u} ⥤ PointedSimplicialSet.{u}

instance boundaryKSpaceFunctor_kanComplex (X : StableModel.{u}) :
    KanComplex ((boundaryKSpaceFunctor.obj X).right)

def boundarySRealizationComparison (X : StableModel.{u}) :
    pointedSRealization X.carrier ⟶ (boundaryReducedRealizationFunctor 0).obj X

lemma boundarySRealizationComparison_kan_piIsomorphism (X : StableModel.{u}) :
    Spectra.KanPiIsomorphism (Spectra.PointedKanReplacement.map (boundarySRealizationComparison X)).right

def kSpaceBoundaryComparison (X : StableModel.{u}) :
    kSpace X.carrier ⟶ boundaryKSpaceFunctor.obj X

lemma kSpaceBoundaryComparison_piIsomorphism (X : StableModel.{u}) :
    Spectra.KanPiIsomorphism (kSpaceBoundaryComparison X).right

lemma boundarySRealizationComparison_naturality {X Y : StableModel.{u}}
    (f : X.carrier ⟶ Y.carrier) (hf : PreservesSConstructionData f) (hz : PreservesChosenZero f) :
    pointedSPostcomp f hf hz ≫ boundarySRealizationComparison Y =
      boundarySRealizationComparison X ≫ (boundaryReducedRealizationFunctor 0).map
        (⟨f, PreservesSConstructionData.toCofiberData hf⟩ : X ⟶ Y)

lemma kSpaceBoundaryComparison_naturality {X Y : StableModel.{u}}
    (f : X.carrier ⟶ Y.carrier) (hf : PreservesSConstructionData f) (hz : PreservesChosenZero f) :
    kSpacePostcomp f hf hz ≫ kSpaceBoundaryComparison Y =
      kSpaceBoundaryComparison X ≫ boundaryKSpaceFunctor.map
        (⟨f, PreservesSConstructionData.toCofiberData hf⟩ : X ⟶ Y)
```

現在地：L1a・L1b 完了、L1c 継続中。全零境界商の自然な K 空間関手と従来模型との実際の π_* 比較まで証明済み。
反復間の構造写像、delooping・Ω 条件・BF 連結スペクトルは未完了。
任意の押し出し保存と cofiber 保存条件との同値は未証明。L1d–f 未完了、L1g は別途指示待ち。

検証：対象ビルド成功（2952 jobs）、公理監査成功（804 宣言、標準三公理のみ）。追加公理・sorry なし。

## 6.18 各段から対角への組み立てと区間商の自然な比較

構造写像の cylinder を用意するため、任意の単体的単体集合 X について
`diagonalAssembly m X : Δ[m] ⊗ X_m ⟶ diag X` を構成した。
n 次の単体 (α,x) を外側構造射 X(αᵒᵖ)(x) に送る。
入力について自然で、外側の全単体作用素による次数変更と両立する。
各頂点の制限は零段の対角への包含を経由し、零段を潰すと全端点が厳密に基点となる。

区間の境界の任意の高次単体が定値であることから、全境界について同じ式を証明した。
この式を cofiber の普遍性へ渡し、
`cofiber (∂Δ[1] ⊗ X₁ → Δ[1] ⊗ X₁) → reducedDiagonal X` を作った。
源の区間商を関手にまとめ、この比較の厳密な自然性も証明した。
Kan 性・安定性・可縮性などを追加仮定しない。

この区間商の源は X₁ の全両端を一つの基点へ潰す模型であり、指定済みの点つき X₁ の
reduced suspension と同一視していない。完成した S の反復間の構造写像とは数えない。
S₁ の評価との比較、他の零方向を含む全境界商への降下、L9 の円の smash との接続が残る。

以下の正確な型は namespace `SerrePositivity.KST.SConstruction` 内、`universe u`、
`open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet`、
`open scoped Simplicial` の下で記す。

**DiagonalAssembly.lean**

```lean
def diagonalAssembly (m : ℕ) (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    (Δ[m] : SSet.{u}) ⊗ X.obj (Opposite.op ⦋m⦌) ⟶ simplicialDiagonalFunctor.obj X

lemma diagonalAssembly_naturality (m : ℕ) {X Y : SimplexCategoryᵒᵖ ⥤ SSet.{u}}
    (f : X ⟶ Y) :
    ((Δ[m] : SSet.{u}) ◁ f.app (Opposite.op ⦋m⦌)) ≫ diagonalAssembly m Y =
      diagonalAssembly m X ≫ simplicialDiagonalFunctor.map f

lemma diagonalAssembly_reindex {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    (stdSimplex.map θ ▷ X.obj (Opposite.op ⦋n⦌)) ≫ diagonalAssembly n X =
      ((Δ[m] : SSet.{u}) ◁ X.map θ.op) ≫ diagonalAssembly m X

lemma diagonalAssembly_zero (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    diagonalAssembly 0 X =
      snd (Δ[0] : SSet.{u}) (X.obj (Opposite.op ⦋0⦌)) ≫ diagonalZeroColumn X

lemma diagonalAssembly_endpoint (m : ℕ) (θ : ⦋0⦌ ⟶ ⦋m⦌)
    (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    (stdSimplex.map θ ▷ X.obj (Opposite.op ⦋m⦌)) ≫ diagonalAssembly m X =
      ((Δ[0] : SSet.{u}) ◁ X.map θ.op) ≫
        snd (Δ[0] : SSet.{u}) (X.obj (Opposite.op ⦋0⦌)) ≫ diagonalZeroColumn X

lemma diagonalAssembly_endpoint_reduced (m : ℕ) (θ : ⦋0⦌ ⟶ ⦋m⦌)
    (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    (stdSimplex.map θ ▷ X.obj (Opposite.op ⦋m⦌)) ≫ diagonalAssembly m X ≫
        diagonalReductionQuotient X =
      toUnit ((Δ[0] : SSet.{u}) ⊗ X.obj (Opposite.op ⦋m⦌)) ≫ (reducedDiagonal X).hom

lemma intervalBoundary_simplex_constant {n : ℕ} (a : (Δ[1] : SSet.{u}) _⦋n⦌)
    (ha : a ∈ (boundary 1).obj (Opposite.op ⦋n⦌)) :
    stdSimplex.objEquiv a = SimplexCategory.const ⦋n⦌ ⦋1⦌ (a 0)

lemma diagonalAssembly_interval_boundary (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    ((boundary 1).ι ▷ X.obj (Opposite.op ⦋1⦌)) ≫ diagonalAssembly 1 X ≫
        diagonalReductionQuotient X =
      toUnit ((boundary 1 : (Δ[1] : SSet.{u}).Subcomplex).toSSet ⊗
        X.obj (Opposite.op ⦋1⦌)) ≫ (reducedDiagonal X).hom

def diagonalIntervalComparison (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    PointedObject.cofiber ((boundary 1).ι ▷ X.obj (Opposite.op ⦋1⦌)) ⟶
      reducedDiagonal X

lemma diagonalIntervalComparison_quotient (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    PointedObject.cofiberQuotient ((boundary 1).ι ▷ X.obj (Opposite.op ⦋1⦌)) ≫
      (diagonalIntervalComparison X).right =
        diagonalAssembly 1 X ≫ diagonalReductionQuotient X

def diagonalIntervalMap {X Y : SimplexCategoryᵒᵖ ⥤ SSet.{u}} (f : X ⟶ Y) :
    PointedObject.cofiber ((boundary 1).ι ▷ X.obj (Opposite.op ⦋1⦌)) ⟶
      PointedObject.cofiber ((boundary 1).ι ▷ Y.obj (Opposite.op ⦋1⦌))

lemma diagonalIntervalMap_quotient {X Y : SimplexCategoryᵒᵖ ⥤ SSet.{u}} (f : X ⟶ Y) :
    PointedObject.cofiberQuotient ((boundary 1).ι ▷ X.obj (Opposite.op ⦋1⦌)) ≫
      (diagonalIntervalMap f).right =
        ((Δ[1] : SSet.{u}) ◁ f.app (Opposite.op ⦋1⦌)) ≫
          PointedObject.cofiberQuotient ((boundary 1).ι ▷ Y.obj (Opposite.op ⦋1⦌))

def diagonalIntervalFunctor : (SimplexCategoryᵒᵖ ⥤ SSet.{u}) ⥤ PointedSimplicialSet.{u}

def diagonalIntervalComparisonNat : diagonalIntervalFunctor ⟶ reducedDiagonalFunctor
```

現在地：L1a・L1b 完了、L1c 継続中。各段の組み立てと区間商の自然な比較を追加した。
反復間の構造写像、delooping・Ω 条件・BF 連結スペクトルは未完了。
任意の押し出し保存と cofiber 保存条件との同値は未証明。L1d–f 未完了、L1g は別途指示待ち。

検証：対象ビルド成功（2953 jobs）、公理監査成功（818 宣言、標準三公理のみ）。追加公理・sorry なし。

## 6.19 S₁ と元の圏の自然な比較と core の充填性

一次の第一行の添字の nerve と終対象の同型を使い、その内部 Hom 関手を恒等関手と自然に同一視した。
第一行制限と合成した `sOneComparison C : S₁ C → C` は安定な quasicategory について
trivial Kan fibration。零対象・cofiber 補完の選択を定義に含まない。
`PreservesCofiberData` を満たす射の後合成について厳密に自然である。

一般の quasicategory 間の trivial Kan fibration f について、
`quasicategoryCoreMap f` も trivial Kan fibration であることを本レーンで証明した。
元の境界充填を取り、その辺の像が core 内で可逆であることと、
f の充満忠実性による可逆性の反映から、充填を core に持ち上げた。
F1・Core の定義や公開名・型は変更していない。

これを一次段へ適用し、`coreSOneComparison` の全境界充填性と
L9 の `KanPiIsomorphism`（全基点・零次数を含む全次数）を得た。
`StableModel` の射について自然変換にまとめたが、その逆射を自然に選んではいない。
S₁ の比較自体の cofiber 保存、反復をまたぐ比較、既存の区間商・全境界商への接続は未完了。

以下の正確な型は namespace `SerrePositivity.KST.SConstruction` 内、`universe u`、
`open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet`、
`open SerrePositivity.InfinityCategories SerrePositivity.SimplicialModel`、
`open scoped Simplicial` の下で記す。

**CoreTrivialFibration.lean**

```lean
lemma coreMap_trivialKanFibration {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    (f : X ⟶ Y) [TrivialKanFibration f] : TrivialKanFibration (quasicategoryCoreMap f)
```

**SOneComparison.lean**

```lean
def firstRowOneUnitIso : firstRowNerve.{u} 1 ≅ 𝟙_ SSet.{u}

def firstRowOneHomNatIso : ihom (firstRowNerve.{u} 1) ≅ 𝟭 SSet.{u}

def sOneComparison (C : SSet.{u}) : sConstruction 1 C ⟶ C

instance sOneComparison_trivialKanFibration (C : SSet.{u}) [Quasicategory C] [IsStable C] :
    TrivialKanFibration (sOneComparison C)

lemma firstRowRestriction_sPostcompCofiber (n : ℕ) {C D : SSet.{u}} [Quasicategory D]
    (f : C ⟶ D) (hf : PreservesCofiberData f) :
    sPostcompCofiber n f hf ≫ firstRowRestriction n D =
      firstRowRestriction n C ≫ (ihom (firstRowNerve n)).map f

lemma sOneComparison_naturality {C D : SSet.{u}} [Quasicategory D]
    (f : C ⟶ D) (hf : PreservesCofiberData f) :
    sPostcompCofiber 1 f hf ≫ sOneComparison D = sOneComparison C ≫ f

def coreSOneComparison (C : SSet.{u}) :
    coreSConstruction 1 C ⟶ (quasicategoryCore C : SSet.{u})

instance coreSOneComparison_trivialKanFibration (C : SSet.{u})
    [Quasicategory C] [IsStable C] : TrivialKanFibration (coreSOneComparison C)

lemma coreSOneComparison_piIsomorphism (C : SSet.{u}) [Quasicategory C] [IsStable C] :
    Spectra.KanPiIsomorphism (coreSOneComparison C)

lemma coreSOneComparison_naturality {C D : SSet.{u}} [Quasicategory D]
    (f : C ⟶ D) (hf : PreservesCofiberData f) :
    quasicategoryCoreMap (sPostcompCofiber 1 f hf) ≫ coreSOneComparison D =
      coreSOneComparison C ≫ quasicategoryCoreMap f

def coreSOneComparisonNat :
    sEndofunctor 1 ⋙ stableModelForget ⋙ quasicategoryCoreFunctor ⟶
      stableModelForget ⋙ quasicategoryCoreFunctor
```

現在地：L1a・L1b 完了、L1c 継続中。S₁ と元の圏の core の自然な trivial Kan fibration を追加した。
反復間の構造写像、delooping・Ω 条件・BF 連結スペクトルは未完了。
任意の押し出し保存と cofiber 保存条件との同値は未証明。L1d–f 未完了、L1g は別途指示待ち。

検証：対象ビルド成功（2955 jobs）、公理監査成功（830 宣言、標準三公理のみ）。追加公理・sorry なし。

## 6.20 S₁ 比較の完全性と反復の一次方向の自然な比較

既存の trivial Kan fibration の普遍性の保存を S₁ の比較へ適用し、
零対象と全押し出しの保存、および `PreservesCofiberData` を無条件で導いた。
`stableSOneComparisonNat : sEndofunctor 1 → 𝟭 StableModel` は安定圏での自然変換。
`StableModel` の射について自然で、零対象の選択を厳密に保存する仮定は不要。

r+1 重反復の外側の次数を 1 に固定する `oneDirectionIndex r` を構成した。
外側の S₁ の比較を残りの r 重反復へ適用して多単体的自然変換を得た。
各多次数の底の射と core 上の射は trivial Kan fibration。
残りの r 方向と core の次数の対角を取った比較
`oneDirectionRealizationComparison r X` は anodyne 局所化で可逆である。
証明は各段の trivial Kan fibration と HA の対角定理を用い、対角の Kan 性は仮定しない。
入力についての厳密な自然変換にもまとめた。

今回の比較は未点化の実現について。全零境界商・区間商への接続と、円の smash を源とする
反復間の構造写像はまだ構成していない。逆射の自然な選択も含めない。
Core・Stable・F1・HA・Spectra の所有ファイルと公開 API は変更していない。

以下は namespace `SerrePositivity.KST.SConstruction` 内の正確な型。`universe u`、
`open CategoryTheory MonoidalCategory SSet`、
`open SerrePositivity.InfinityCategories SerrePositivity.SimplicialModel`、
`open scoped Simplicial` の下で記す（SOneExact ではさらに `MonoidalClosed` を開く）。

**SOneExact.lean**

```lean
lemma sOneComparison_preservesSConstructionData (C : SSet.{u}) [Quasicategory C] [IsStable C] :
    PreservesSConstructionData (sOneComparison C)

lemma sOneComparison_preservesCofiberData (C : SSet.{u}) [Quasicategory C] [IsStable C] :
    PreservesCofiberData (sOneComparison C)

def stableSOneComparison (X : StableModel.{u}) : (sEndofunctor 1).obj X ⟶ X

def stableSOneComparisonNat : sEndofunctor 1 ⟶ 𝟭 StableModel.{u}
```

**MultiSOneComparison.lean**

```lean
def oneDirectionIndex (r : ℕ) :
    (Fin r → SimplexCategoryᵒᵖ) ⥤ (Fin (r + 1) → SimplexCategoryᵒᵖ)

def multiSOneEndofunctorComparison (r : ℕ) :
    oneDirectionIndex r ⋙ multiSEndofunctor (r + 1) ⟶ multiSEndofunctor r

def multiSOneComparison (r : ℕ) (X : StableModel.{u}) :
    oneDirectionIndex r ⋙ multiSConstruction (r + 1) X ⟶ multiSConstruction r X

lemma multiSOneComparison_app (r : ℕ) (X : StableModel.{u})
    (d : Fin r → SimplexCategoryᵒᵖ) :
    (multiSOneComparison r X).app d = sOneComparison ((multiSConstruction r X).obj d)

instance multiSOneComparison_trivialKanFibration (r : ℕ) (X : StableModel.{u})
    (d : Fin r → SimplexCategoryᵒᵖ) :
    TrivialKanFibration ((multiSOneComparison r X).app d)

def multiCoreSOneComparison (r : ℕ) (X : StableModel.{u}) :
    oneDirectionIndex r ⋙ multiCoreSConstruction (r + 1) X ⟶ multiCoreSConstruction r X

instance multiCoreSOneComparison_trivialKanFibration (r : ℕ) (X : StableModel.{u})
    (d : Fin r → SimplexCategoryᵒᵖ) :
    TrivialKanFibration ((multiCoreSOneComparison r X).app d)

def oneDirectionDiagonalComparison (r : ℕ) (X : StableModel.{u}) :
    multiIndexDiagonal r ⋙ oneDirectionIndex r ⋙ multiCoreSConstruction (r + 1) X ⟶
      multiIndexDiagonal r ⋙ multiCoreSConstruction r X

def oneDirectionRealizationComparison (r : ℕ) (X : StableModel.{u}) :
    simplicialDiagonalFunctor.obj
      (multiIndexDiagonal r ⋙ oneDirectionIndex r ⋙ multiCoreSConstruction (r + 1) X) ⟶
        multiDiagonalCoreSConstruction r X

lemma oneDirectionRealizationComparison_localized_isIso (r : ℕ) (X : StableModel.{u}) :
    IsIso (AnodyneHomotopy.anodyneQ.map (oneDirectionRealizationComparison r X))

lemma multiSOneComparison_naturality (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    Functor.whiskerLeft (oneDirectionIndex r) ((multiSConstructionFunctor (r + 1)).map f) ≫
        multiSOneComparison r Y =
      multiSOneComparison r X ≫ (multiSConstructionFunctor r).map f

lemma multiCoreSOneComparison_naturality (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    Functor.whiskerLeft (oneDirectionIndex r) ((multiCoreSConstructionFunctor (r + 1)).map f) ≫
        multiCoreSOneComparison r Y =
      multiCoreSOneComparison r X ≫ (multiCoreSConstructionFunctor r).map f

def multiCoreSOneComparisonNat (r : ℕ) :
    multiCoreSConstructionFunctor (r + 1) ⋙
      (Functor.whiskeringLeft _ _ _).obj (oneDirectionIndex r) ⟶
        multiCoreSConstructionFunctor r

def oneDirectionRealizationFunctor (r : ℕ) : StableModel.{u} ⥤ SSet.{u}

def oneDirectionRealizationComparisonNat (r : ℕ) :
    oneDirectionRealizationFunctor r ⟶ multiRealizationFunctor r

lemma oneDirectionRealizationComparisonNat_app (r : ℕ) (X : StableModel.{u}) :
    (oneDirectionRealizationComparisonNat r).app X = oneDirectionRealizationComparison r X
```

現在地：L1a・L1b 完了、L1c 継続中。S₁ 比較の cofiber 保存と任意の反復の外側一次方向の自然な比較は証明済み。
全境界商への降下、反復間の構造写像、delooping・Ω 条件・BF 連結スペクトルは未完了。
任意の押し出し保存と一般の cofiber 保存条件との同値は未証明。L1d–f 未完了、L1g は別途指示待ち。

検証：対象ビルド成功（2957 jobs）、公理監査成功（850 宣言、標準三公理のみ）。追加公理・sorry なし。

## 6.21 反復の一次方向の区間と全零境界商への降下

外側を一次に固定した r+1 重反復の実現 A_r(X) に対し、
`multiDiagonalAssembly r X : Δ[1] ⊗ A_r(X) → diag(core S^(r+1) X)` を構成した。
n 単体 (α,x) を、先頭に αᵒᵖ、残りに恒等射を配置した多単体添字の射で写す。
添字の可換式から単体写像であることを証明し、入力についての厳密な自然性も得た。
一般の多単体図式 M に対する `coordinateDiagonalAssembly` で証明してから反復 core S を代入する。

区間の定値単体の像は第零方向を零に固定する自己射で固定されるため、第零方向の零境界に属する。
区間境界の任意の高次単体が定値である既存の計算と合わせ、
区間両端の全体 `∂Δ[1] ⊗ A_r(X)` の像が全零境界に入ることを示した。
その境界への持ち上げと cofiber の関係式から、区間両端を一つの基点に潰した商の点つき射
`multiIntervalBoundaryComparison` を全零境界商へ構成し、入力について自然変換にまとめた。

源はまだ未点化 A_r(X) の両端商である。残りの r 方向の零境界の円筒全体を潰す工程、
L9 の円の smash との同一視、前節の一次方向を消す比較を点つき商へ移す工程が残る。
反復間の完成した suspension 構造写像や delooping としては数えない。
Core・Stable・F1・HA・Spectra の所有ファイルや公開 API は変更していない。

以下は namespace `SerrePositivity.KST.SConstruction` 内の正確な型。`universe u`、
`open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet`、
`open SerrePositivity.InfinityCategories SerrePositivity.SimplicialModel`、
`open scoped Simplicial` の下で記す。`StableModel` の構造以外の追加前提はない。

**MultiDiagonalAssembly.lean**

```lean
def oneDirectionAssemblyIndex (r : ℕ) (d : SimplexCategoryᵒᵖ) (α : d.unop ⟶ ⦋1⦌) :
    (oneDirectionIndex r).obj ((multiIndexDiagonal r).obj d) ⟶
      (multiIndexDiagonal (r + 1)).obj d

lemma oneDirectionAssemblyIndex_naturality (r : ℕ) {d e : SimplexCategoryᵒᵖ}
    (f : d ⟶ e) (α : d.unop ⟶ ⦋1⦌) :
    oneDirectionAssemblyIndex r d α ≫ (multiIndexDiagonal (r + 1)).map f =
      (oneDirectionIndex r).map ((multiIndexDiagonal r).map f) ≫
        oneDirectionAssemblyIndex r e (f.unop ≫ α)

def coordinateDiagonalAssembly (r : ℕ)
    (M : (Fin (r + 1) → SimplexCategoryᵒᵖ) ⥤ SSet.{u}) :
    (Δ[1] : SSet.{u}) ⊗
      simplicialDiagonalFunctor.obj (multiIndexDiagonal r ⋙ oneDirectionIndex r ⋙ M) ⟶
      simplicialDiagonalFunctor.obj (multiIndexDiagonal (r + 1) ⋙ M)

def multiDiagonalAssembly (r : ℕ) (X : StableModel.{u}) :
    (Δ[1] : SSet.{u}) ⊗ (oneDirectionRealizationFunctor r).obj X ⟶
      multiDiagonalCoreSConstruction (r + 1) X

lemma coordinateDiagonalAssembly_naturality (r : ℕ)
    {M N : (Fin (r + 1) → SimplexCategoryᵒᵖ) ⥤ SSet.{u}} (f : M ⟶ N) :
    ((Δ[1] : SSet.{u}) ◁ simplicialDiagonalFunctor.map
      (Functor.whiskerLeft (multiIndexDiagonal r) (Functor.whiskerLeft (oneDirectionIndex r) f))) ≫
        coordinateDiagonalAssembly r N =
      coordinateDiagonalAssembly r M ≫ simplicialDiagonalFunctor.map
        (Functor.whiskerLeft (multiIndexDiagonal (r + 1)) f)

lemma multiDiagonalAssembly_naturality (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    ((Δ[1] : SSet.{u}) ◁ (oneDirectionRealizationFunctor r).map f) ≫
        multiDiagonalAssembly r Y =
      multiDiagonalAssembly r X ≫ (multiRealizationFunctor (r + 1)).map f

lemma oneDirectionAssemblyIndex_constant_fixed (r : ℕ) (d : SimplexCategoryᵒᵖ) (i : Fin 2) :
    oneDirectionAssemblyIndex r d (SimplexCategory.const d.unop ⦋1⦌ i) ≫
        zeroDirectionsIndexEndomorphism {(0 : Fin (r + 1))} (fun _ => d) =
      oneDirectionAssemblyIndex r d (SimplexCategory.const d.unop ⦋1⦌ i)
```

**MultiAssemblyBoundary.lean**

```lean
lemma multiDiagonalAssembly_constant_mem (r : ℕ) (X : StableModel.{u})
    (d : SimplexCategoryᵒᵖ) (i : Fin 2)
    (x : ((oneDirectionRealizationFunctor r).obj X).obj d) :
    ((multiCoreSConstruction (r + 1) X).map
      (oneDirectionAssemblyIndex r d (SimplexCategory.const d.unop ⦋1⦌ i))).app d x ∈
        (zeroDirectionsRange {(0 : Fin (r + 1))} X).obj d

lemma multiDiagonalAssembly_boundary_mem (r : ℕ) (X : StableModel.{u})
    (d : SimplexCategoryᵒᵖ)
    (z : ((boundary 1).toSSet ⊗ (oneDirectionRealizationFunctor r).obj X).obj d) :
    (multiDiagonalAssembly r X).app d
      (((boundary 1).ι ▷ (oneDirectionRealizationFunctor r).obj X).app d z) ∈
        (zeroDirectionsFatBoundary (r + 1) X).obj d

def multiAssemblyBoundaryLift (r : ℕ) (X : StableModel.{u}) :
    (boundary 1).toSSet ⊗ (oneDirectionRealizationFunctor r).obj X ⟶
      (zeroDirectionsFatBoundary (r + 1) X : SSet.{u})

lemma multiAssemblyBoundaryLift_ι (r : ℕ) (X : StableModel.{u}) :
    multiAssemblyBoundaryLift r X ≫ (zeroDirectionsFatBoundary (r + 1) X).ι =
      ((boundary 1).ι ▷ (oneDirectionRealizationFunctor r).obj X) ≫
        multiDiagonalAssembly r X

lemma multiDiagonalAssembly_boundary_condition (r : ℕ) (X : StableModel.{u}) :
    ((boundary 1).ι ▷ (oneDirectionRealizationFunctor r).obj X) ≫
        multiDiagonalAssembly r X ≫ boundaryReductionQuotient r X =
      toUnit ((boundary 1).toSSet ⊗ (oneDirectionRealizationFunctor r).obj X) ≫
        (boundaryReducedRealization r X).hom

def multiIntervalBoundaryComparison (r : ℕ) (X : StableModel.{u}) :
    PointedObject.cofiber ((boundary 1).ι ▷ (oneDirectionRealizationFunctor r).obj X) ⟶
      boundaryReducedRealization r X

lemma multiIntervalBoundaryComparison_quotient (r : ℕ) (X : StableModel.{u}) :
    PointedObject.cofiberQuotient ((boundary 1).ι ▷ (oneDirectionRealizationFunctor r).obj X) ≫
      (multiIntervalBoundaryComparison r X).right =
        multiDiagonalAssembly r X ≫ boundaryReductionQuotient r X
```

**MultiIntervalNaturality.lean**

```lean
def intervalBoundaryQuotientFunctor : SSet.{u} ⥤ PointedSimplicialSet.{u}

def multiIntervalBoundaryFunctor (r : ℕ) : StableModel.{u} ⥤ PointedSimplicialSet.{u}

lemma multiIntervalBoundaryComparison_naturality (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    (multiIntervalBoundaryFunctor r).map f ≫ multiIntervalBoundaryComparison r Y =
      multiIntervalBoundaryComparison r X ≫ (boundaryReducedRealizationFunctor r).map f

def multiIntervalBoundaryComparisonNat (r : ℕ) :
    multiIntervalBoundaryFunctor r ⟶ boundaryReducedRealizationFunctor r
```

現在地：L1a・L1b 完了、L1c 継続中。一次方向の区間から全反復の対角への自然な写像と、両端商から全零境界商への自然な点つき比較は証明済み。
残りの零方向の境界の処理、反復間の構造写像、delooping・Ω 条件・BF 連結スペクトルは未完了。
任意の押し出し保存と一般の cofiber 保存条件との同値は未証明。L1d–f 未完了、L1g は別途指示待ち。

検証：対象ビルド成功（2960 jobs）、公理監査成功（868 宣言、標準三公理のみ）。追加公理・sorry なし。

## 6.22 残りの零方向の cylinder と合併境界の同時 collapse

一次方向を固定した実現 A_r(X) の残りの方向 j を零に固定する図式と、その包含の像を定義した。
零方向の自己射と組み立ての添字の可換式を証明し、像の元の固定点判定を介して、
`Δ[1] ⊗ R_j` の組み立ての像が標的の `R_(j.succ)` に入ることを示した。
`oneDirectionFatBoundary r X := ⨆ j, R_j` とすると、その cylinder 全体も標的の全零境界へ入る。
r=0 ではこの部分複体は空であり、追加の非空性仮定を置かない。

区間の両端と、この残りの全零境界の cylinder の合併を `combinedIntervalBoundary` と定義した。
両射影による逆像の上限という厳密な部分複体である。
組み立てが合併境界全体を標的の全零境界へ写すため、その同時 cofiber 商から
`boundaryReducedRealization r X` への点つき射 `combinedIntervalAssembly` を構成した。
源・標的の Kan 性や境界の可縮性などを追加仮定しない。

この源の商と L9 の円との smash の同型、源の零境界の自然性と弱可縮性、
S₁ 比較の境界商への降下・局所化比較はまだ接続していない。
したがって完成した反復間の suspension 構造写像とは数えない。
Core・Stable・F1・HA・Spectra の所有ファイルや公開 API は変更していない。

以下は namespace `SerrePositivity.KST.SConstruction` 内の正確な型。`universe u`、
`open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet`、
`open SerrePositivity.InfinityCategories SerrePositivity.SimplicialModel`、
`open scoped Simplicial` の下で記す。`StableModel` の構造以外の追加前提はない。

**OneDirectionBoundary.lean**

```lean
lemma oneDirectionAssemblyIndex_zero_commute (r : ℕ) (j : Fin r)
    (d : SimplexCategoryᵒᵖ) (α : d.unop ⟶ ⦋1⦌) :
    (oneDirectionIndex r).map (zeroDirectionsIndexEndomorphism {j} (fun _ => d)) ≫
        oneDirectionAssemblyIndex r d α =
      oneDirectionAssemblyIndex r d α ≫
        zeroDirectionsIndexEndomorphism {j.succ} (fun _ => d)

def oneDirectionZeroDiagram (r : ℕ) (j : Fin r) (X : StableModel.{u}) :
    SimplexCategoryᵒᵖ ⥤ SSet.{u}

def oneDirectionZeroInclusion (r : ℕ) (j : Fin r) (X : StableModel.{u}) :
    simplicialDiagonalFunctor.obj (oneDirectionZeroDiagram r j X) ⟶
      (oneDirectionRealizationFunctor r).obj X

def oneDirectionZeroRange (r : ℕ) (j : Fin r) (X : StableModel.{u}) :
    ((oneDirectionRealizationFunctor r).obj X).Subcomplex

lemma oneDirectionZeroRange_fixed (r : ℕ) (j : Fin r) (X : StableModel.{u})
    (d : SimplexCategoryᵒᵖ) (x : ((oneDirectionRealizationFunctor r).obj X).obj d)
    (hx : x ∈ (oneDirectionZeroRange r j X).obj d) :
    ((multiCoreSConstruction (r + 1) X).map
      ((oneDirectionIndex r).map (zeroDirectionsIndexEndomorphism {j} (fun _ => d)))).app d x = x

lemma multiDiagonalAssembly_zeroRange_mem (r : ℕ) (j : Fin r) (X : StableModel.{u})
    (d : SimplexCategoryᵒᵖ) (a : (Δ[1] : SSet.{u}).obj d)
    (x : ((oneDirectionRealizationFunctor r).obj X).obj d)
    (hx : x ∈ (oneDirectionZeroRange r j X).obj d) :
    (multiDiagonalAssembly r X).app d (a, x) ∈ (zeroDirectionsRange {j.succ} X).obj d

def oneDirectionFatBoundary (r : ℕ) (X : StableModel.{u}) :
    ((oneDirectionRealizationFunctor r).obj X).Subcomplex

lemma multiDiagonalAssembly_fatBoundary_mem (r : ℕ) (X : StableModel.{u})
    (d : SimplexCategoryᵒᵖ) (a : (Δ[1] : SSet.{u}).obj d)
    (x : ((oneDirectionRealizationFunctor r).obj X).obj d)
    (hx : x ∈ (oneDirectionFatBoundary r X).obj d) :
    (multiDiagonalAssembly r X).app d (a, x) ∈ (zeroDirectionsFatBoundary (r + 1) X).obj d
```

**CombinedBoundaryAssembly.lean**

```lean
def combinedIntervalBoundary (r : ℕ) (X : StableModel.{u}) :
    ((Δ[1] : SSet.{u}) ⊗ (oneDirectionRealizationFunctor r).obj X).Subcomplex

lemma combinedIntervalBoundary_image_le (r : ℕ) (X : StableModel.{u}) :
    (combinedIntervalBoundary r X).image (multiDiagonalAssembly r X) ≤
      zeroDirectionsFatBoundary (r + 1) X

def combinedAssemblyBoundaryLift (r : ℕ) (X : StableModel.{u}) :
    (combinedIntervalBoundary r X : SSet.{u}) ⟶
      (zeroDirectionsFatBoundary (r + 1) X : SSet.{u})

lemma combinedAssemblyBoundaryLift_ι (r : ℕ) (X : StableModel.{u}) :
    combinedAssemblyBoundaryLift r X ≫ (zeroDirectionsFatBoundary (r + 1) X).ι =
      (combinedIntervalBoundary r X).ι ≫ multiDiagonalAssembly r X

lemma combinedIntervalBoundary_condition (r : ℕ) (X : StableModel.{u}) :
    (combinedIntervalBoundary r X).ι ≫ multiDiagonalAssembly r X ≫
        boundaryReductionQuotient r X =
      toUnit (combinedIntervalBoundary r X : SSet.{u}) ≫
        (boundaryReducedRealization r X).hom

def combinedIntervalQuotient (r : ℕ) (X : StableModel.{u}) : PointedSimplicialSet.{u}

def combinedIntervalAssembly (r : ℕ) (X : StableModel.{u}) :
    combinedIntervalQuotient r X ⟶ boundaryReducedRealization r X

lemma combinedIntervalAssembly_quotient (r : ℕ) (X : StableModel.{u}) :
    PointedObject.cofiberQuotient (combinedIntervalBoundary r X).ι ≫
      (combinedIntervalAssembly r X).right =
        multiDiagonalAssembly r X ≫ boundaryReductionQuotient r X
```

現在地：L1a・L1b 完了、L1c 継続中。区間の両端と残りの全零境界 cylinder を同時に潰した商から、全反復の全零境界商への点つき射は証明済み。
源の商と円の smash の同一視、S₁ 比較の境界商への接続、反復間の構造写像、delooping・Ω 条件・BF 連結スペクトルは未完了。
任意の押し出し保存と一般の cofiber 保存条件との同値は未証明。L1d–f 未完了、L1g は別途指示待ち。

検証：対象ビルド成功（2962 jobs）、公理監査成功（884 宣言、標準三公理のみ）。追加公理・sorry なし。

## 6.23 一次方向の残りの境界商と S₁ 比較の自然な降下

一次方向を固定した実現 A_r(X) の各零方向の像と全零境界が、入力の全 `StableModel` 射で保存されることを証明した。
一般の多単体図式の零段の包含の自然性を証明してから、反復 S の関手へ代入している。
S₁ の比較は各零方向の像を残りの反復の対応する零方向の像へ送るため、全零境界も保つ。

正の残りの反復数 r+1 に対し、
`oneDirectionReducedRealization r X := cofiber (oneDirectionFatBoundary (r+1) X).ι` を定義した。
その入力についての関手と元の実現からの自然な商写像も構成済み。
S₁ 比較の境界への制限と cofiber の普遍性から、
`oneDirectionReducedComparison : oneDirectionReducedRealization r X → boundaryReducedRealization r X` を得て、
厳密な点つき自然変換にまとめた。

ここで source は未点化実現 A_(r+1)(X) の残りの全零境界を一点へ潰した商。
今回の商写像・降下した比較の局所化可逆性や π_* 同型はまだ証明していない。
そのために源の境界の弱可縮性と元の S₁ 比較の局所化可逆性を接続する工程が残る。
前節の同時商と円の smash の同一視・構造写像への接続も未完了。
Core・Stable・F1・HA・Spectra の所有ファイルや公開 API は変更していない。

以下は namespace `SerrePositivity.KST.SConstruction` 内の正確な型。`universe u`、
`open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet`、
`open SerrePositivity.InfinityCategories SerrePositivity.SimplicialModel`、
`open scoped Simplicial` の下で記す。`StableModel` の構造以外の追加前提はない。

**OneDirectionBoundaryNaturality.lean**

```lean
def oneDirectionZeroRealizationFunctor (r : ℕ) (j : Fin r) : StableModel.{u} ⥤ SSet.{u}

lemma diagonalZeroInclusion_naturality {r : ℕ} (s : Finset (Fin r))
    {M N : (Fin r → SimplexCategoryᵒᵖ) ⥤ SSet.{u}} (f : M ⟶ N) :
    simplicialDiagonalFunctor.map (Functor.whiskerLeft (multiIndexDiagonal r)
      (Functor.whiskerRight (zeroDirectionsIndexNat s) M)) ≫
        simplicialDiagonalFunctor.map (Functor.whiskerLeft (multiIndexDiagonal r) f) =
      simplicialDiagonalFunctor.map (Functor.whiskerLeft (multiIndexDiagonal r)
        (Functor.whiskerLeft (zeroDirectionsIndex s) f)) ≫
          simplicialDiagonalFunctor.map (Functor.whiskerLeft (multiIndexDiagonal r)
            (Functor.whiskerRight (zeroDirectionsIndexNat s) N))

def oneDirectionZeroInclusionNat (r : ℕ) (j : Fin r) :
    oneDirectionZeroRealizationFunctor.{u} r j ⟶ oneDirectionRealizationFunctor r

lemma oneDirectionZeroInclusionNat_app (r : ℕ) (j : Fin r) (X : StableModel.{u}) :
    (oneDirectionZeroInclusionNat r j).app X = oneDirectionZeroInclusion r j X

lemma oneDirectionZeroRange_image_le (r : ℕ) (j : Fin r) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    (oneDirectionZeroRange r j X).image ((oneDirectionRealizationFunctor r).map f) ≤
      oneDirectionZeroRange r j Y

lemma oneDirectionFatBoundary_image_le (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    (oneDirectionFatBoundary r X).image ((oneDirectionRealizationFunctor r).map f) ≤
      oneDirectionFatBoundary r Y

lemma oneDirectionComparison_zeroRange_image_le (r : ℕ) (j : Fin r) (X : StableModel.{u}) :
    (oneDirectionZeroRange r j X).image (oneDirectionRealizationComparison r X) ≤
      zeroDirectionsRange {j} X

lemma oneDirectionComparison_fatBoundary_image_le (r : ℕ) (X : StableModel.{u}) :
    (oneDirectionFatBoundary r X).image (oneDirectionRealizationComparison r X) ≤
      zeroDirectionsFatBoundary r X
```

**OneDirectionReduction.lean**

```lean
def oneDirectionBoundaryMap (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    (oneDirectionFatBoundary r X : SSet.{u}) ⟶ (oneDirectionFatBoundary r Y : SSet.{u})

lemma oneDirectionBoundaryMap_ι (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    oneDirectionBoundaryMap r f ≫ (oneDirectionFatBoundary r Y).ι =
      (oneDirectionFatBoundary r X).ι ≫ (oneDirectionRealizationFunctor r).map f

def oneDirectionReducedRealization (r : ℕ) (X : StableModel.{u}) : PointedSimplicialSet.{u}

def oneDirectionReductionQuotient (r : ℕ) (X : StableModel.{u}) :
    (oneDirectionRealizationFunctor (r + 1)).obj X ⟶ (oneDirectionReducedRealization r X).right

def oneDirectionReducedRealizationMap (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    oneDirectionReducedRealization r X ⟶ oneDirectionReducedRealization r Y

lemma oneDirectionReducedRealizationMap_quotient (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    oneDirectionReductionQuotient r X ≫ (oneDirectionReducedRealizationMap r f).right =
      (oneDirectionRealizationFunctor (r + 1)).map f ≫ oneDirectionReductionQuotient r Y

def oneDirectionReducedRealizationFunctor (r : ℕ) : StableModel.{u} ⥤ PointedSimplicialSet.{u}

def oneDirectionReductionNat (r : ℕ) : oneDirectionRealizationFunctor (r + 1) ⟶
    oneDirectionReducedRealizationFunctor r ⋙ PointedSimplicialSet.forget
```

**OneDirectionReducedComparison.lean**

```lean
def oneDirectionComparisonBoundaryMap (r : ℕ) (X : StableModel.{u}) :
    (oneDirectionFatBoundary (r + 1) X : SSet.{u}) ⟶
      (zeroDirectionsFatBoundary (r + 1) X : SSet.{u})

lemma oneDirectionComparisonBoundaryMap_ι (r : ℕ) (X : StableModel.{u}) :
    oneDirectionComparisonBoundaryMap r X ≫ (zeroDirectionsFatBoundary (r + 1) X).ι =
      (oneDirectionFatBoundary (r + 1) X).ι ≫ oneDirectionRealizationComparison (r + 1) X

def oneDirectionReducedComparison (r : ℕ) (X : StableModel.{u}) :
    oneDirectionReducedRealization r X ⟶ boundaryReducedRealization r X

lemma oneDirectionReducedComparison_quotient (r : ℕ) (X : StableModel.{u}) :
    oneDirectionReductionQuotient r X ≫ (oneDirectionReducedComparison r X).right =
      oneDirectionRealizationComparison (r + 1) X ≫ boundaryReductionQuotient r X

lemma oneDirectionReducedComparison_naturality (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    (oneDirectionReducedRealizationFunctor r).map f ≫ oneDirectionReducedComparison r Y =
      oneDirectionReducedComparison r X ≫ (boundaryReducedRealizationFunctor r).map f

def oneDirectionReducedComparisonNat (r : ℕ) :
    oneDirectionReducedRealizationFunctor r ⟶ boundaryReducedRealizationFunctor r
```

現在地：L1a・L1b 完了、L1c 継続中。一次方向の残りの零境界の商の関手と、S₁ 比較の商への自然な降下は証明済み。
この比較の局所化可逆性・π_* 同型、同時商と円の smash の同一視、反復間の構造写像、delooping・Ω 条件・BF 連結スペクトルは未完了。
任意の押し出し保存と一般の cofiber 保存条件との同値は未証明。L1d–f 未完了、L1g は別途指示待ち。

検証：対象ビルド成功（2965 jobs）、公理監査成功（906 宣言、標準三公理のみ）。追加公理・sorry なし。

## 6.24 一次方向の境界商の弱同値比較

零方向の包含の単射性、像の固定点判定・反単調性・交差の式を任意の多単体図式 M について証明した。
各非空の零方向の交差が各段で可縮 Kan である条件 `CoordinateZeroContractible M` を明記し、
その下で零境界の有限合併が anodyne 局所化で一点と同値になる一般形も証明した。
既存の反復 core S に関する定理の名前・型は保持している。

一次方向を固定した M := oneDirectionIndex r ⋙ multiCoreSConstruction (r+1) X については、
残りの零方向 j を標的の j.succ へ移して、この条件を無条件で証明した。
残りの反復数が正なら、その全零境界は弱可縮となり、商への射影は任意の anodyne 反転関手で可逆。
これと標的の商写像・元の S₁ 比較の局所化可逆性を射影の可換式で合わせて、
`oneDirectionReducedComparison` の局所化可逆性を証明した。

点つき Kan 置換後の比較は L9 の `KanPiIsomorphism`、すなわち全基点・零次数を含む全次数の π_* 同型。
Kan 置換の比較を自然変換にまとめ、Ω 後も同じ π_* 同型であることを示した。
これは同じ反復数の模型の比較であり、反復数を変える delooping の Ω 条件ではない。
元の実現・商の Kan 性は追加仮定しない。
Core・Stable・F1・HA・Spectra の所有ファイルや公開 API は変更していない。

以下は namespace `SerrePositivity.KST.SConstruction` 内の正確な型。`universe u v w`、
`open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet`、
`open SerrePositivity.InfinityCategories SerrePositivity.SimplicialModel`、
`open scoped Simplicial` の下で記す。一般形の `CoordinateZeroContractible` は
定理の前提として明示するが、一次方向を固定した反復への適用では証明済みである。

**CoordinateZeroRanges.lean**

```lean
def coordinateZeroDiagram {r : ℕ} (s : Finset (Fin r)) (M : (Fin r → SimplexCategoryᵒᵖ) ⥤ SSet.{u}) :
    SimplexCategoryᵒᵖ ⥤ SSet.{u}

def coordinateZeroDiagramMap {r : ℕ} (s : Finset (Fin r)) (M : (Fin r → SimplexCategoryᵒᵖ) ⥤ SSet.{u}) :
    coordinateZeroDiagram s M ⟶ multiIndexDiagonal r ⋙ M

def coordinateZeroInclusion {r : ℕ} (s : Finset (Fin r)) (M : (Fin r → SimplexCategoryᵒᵖ) ⥤ SSet.{u}) :
    simplicialDiagonalFunctor.obj (coordinateZeroDiagram s M) ⟶ simplicialDiagonalFunctor.obj (multiIndexDiagonal r ⋙ M)

instance coordinateZeroInclusion_mono {r : ℕ} (s : Finset (Fin r)) (M : (Fin r → SimplexCategoryᵒᵖ) ⥤ SSet.{u}) :
    Mono (coordinateZeroInclusion s M)

def coordinateZeroRetractionAt {r : ℕ} (s : Finset (Fin r)) (M : (Fin r → SimplexCategoryᵒᵖ) ⥤ SSet.{u})
    (d : SimplexCategoryᵒᵖ) (x : (simplicialDiagonalFunctor.obj (multiIndexDiagonal r ⋙ M)).obj d) :
    (simplicialDiagonalFunctor.obj (coordinateZeroDiagram s M)).obj d

lemma coordinateZeroRetractionAt_leftInverse {r : ℕ} (s : Finset (Fin r)) (M : (Fin r → SimplexCategoryᵒᵖ) ⥤ SSet.{u})
    (d : SimplexCategoryᵒᵖ) :
    Function.LeftInverse (coordinateZeroRetractionAt s M d) ((coordinateZeroInclusion s M).app d)

def coordinateZeroOperator {r : ℕ} (s : Finset (Fin r)) (M : (Fin r → SimplexCategoryᵒᵖ) ⥤ SSet.{u})
    (d : SimplexCategoryᵒᵖ) (x : (simplicialDiagonalFunctor.obj (multiIndexDiagonal r ⋙ M)).obj d) :
    (simplicialDiagonalFunctor.obj (multiIndexDiagonal r ⋙ M)).obj d

lemma coordinateZeroOperator_eq_map {r : ℕ} (s : Finset (Fin r)) (M : (Fin r → SimplexCategoryᵒᵖ) ⥤ SSet.{u})
    (d : SimplexCategoryᵒᵖ) (x : (simplicialDiagonalFunctor.obj (multiIndexDiagonal r ⋙ M)).obj d) :
    coordinateZeroOperator s M d x =
      (M.map (zeroDirectionsIndexEndomorphism s (fun _ => d))).app d x

lemma coordinateZeroOperator_union {r : ℕ} (s t : Finset (Fin r)) (M : (Fin r → SimplexCategoryᵒᵖ) ⥤ SSet.{u})
    (d : SimplexCategoryᵒᵖ) (x : (simplicialDiagonalFunctor.obj (multiIndexDiagonal r ⋙ M)).obj d) :
    coordinateZeroOperator (s ∪ t) M d x =
      coordinateZeroOperator t M d (coordinateZeroOperator s M d x)

def coordinateZeroRange {r : ℕ} (s : Finset (Fin r)) (M : (Fin r → SimplexCategoryᵒᵖ) ⥤ SSet.{u}) :
    (simplicialDiagonalFunctor.obj (multiIndexDiagonal r ⋙ M)).Subcomplex

lemma mem_coordinateZeroRange_iff {r : ℕ} (s : Finset (Fin r)) (M : (Fin r → SimplexCategoryᵒᵖ) ⥤ SSet.{u})
    (d : SimplexCategoryᵒᵖ) (x : (simplicialDiagonalFunctor.obj (multiIndexDiagonal r ⋙ M)).obj d) :
    x ∈ (coordinateZeroRange s M).obj d ↔ coordinateZeroOperator s M d x = x

lemma coordinateZeroRange_antitone {r : ℕ} {s t : Finset (Fin r)} (hst : s ⊆ t)
    (M : (Fin r → SimplexCategoryᵒᵖ) ⥤ SSet.{u}) : coordinateZeroRange t M ≤ coordinateZeroRange s M

lemma coordinateZeroRange_union {r : ℕ} (s t : Finset (Fin r)) (M : (Fin r → SimplexCategoryᵒᵖ) ⥤ SSet.{u}) :
    coordinateZeroRange (s ∪ t) M = coordinateZeroRange s M ⊓ coordinateZeroRange t M
```

**CoordinateZeroBoundary.lean**

```lean
def CoordinateZeroContractible {r : ℕ} (M : (Fin r → SimplexCategoryᵒᵖ) ⥤ SSet.{u}) : Prop

def coordinateZeroDiagramToPoint {r : ℕ} (s : Finset (Fin r)) (M : (Fin r → SimplexCategoryᵒᵖ) ⥤ SSet.{u}) :
    coordinateZeroDiagram s M ⟶ (Functor.const SimplexCategoryᵒᵖ).obj (𝟙_ SSet.{u})

lemma coordinateZeroRealization_toPoint_localized_isIso {r : ℕ} (s : Finset (Fin r))
    (hs : s.Nonempty) (M : (Fin r → SimplexCategoryᵒᵖ) ⥤ SSet.{u})
    (hM : CoordinateZeroContractible M) :
    IsIso (AnodyneHomotopy.anodyneQ.map
      (toUnit (simplicialDiagonalFunctor.obj (coordinateZeroDiagram s M))))

lemma coordinateZeroRange_toPoint_localized_isIso {r : ℕ} (s : Finset (Fin r))
    (hs : s.Nonempty) (M : (Fin r → SimplexCategoryᵒᵖ) ⥤ SSet.{u})
    (hM : CoordinateZeroContractible M) :
    IsIso (AnodyneHomotopy.anodyneQ.map (toUnit (coordinateZeroRange s M : SSet.{u})))

def coordinateZeroBoundary {r : ℕ} (s t : Finset (Fin r)) (M : (Fin r → SimplexCategoryᵒᵖ) ⥤ SSet.{u}) :
    (simplicialDiagonalFunctor.obj (multiIndexDiagonal r ⋙ M)).Subcomplex

lemma coordinateZeroBoundary_insert {r : ℕ} (i : Fin r) (s t : Finset (Fin r)) (M : (Fin r → SimplexCategoryᵒᵖ) ⥤ SSet.{u}) :
    coordinateZeroBoundary (insert i s) t M =
      coordinateZeroRange (insert i t) M ⊔ coordinateZeroBoundary s t M

lemma coordinateZeroBoundary_inf {r : ℕ} (i : Fin r) (s t : Finset (Fin r)) (M : (Fin r → SimplexCategoryᵒᵖ) ⥤ SSet.{u}) :
    coordinateZeroRange (insert i t) M ⊓ coordinateZeroBoundary s t M =
      coordinateZeroBoundary s (insert i t) M

lemma coordinateZeroBoundary_toPoint_localized_isIso {r : ℕ} (s t : Finset (Fin r))
    (hs : s.Nonempty) (M : (Fin r → SimplexCategoryᵒᵖ) ⥤ SSet.{u})
    (hM : CoordinateZeroContractible M) :
    IsIso (AnodyneHomotopy.anodyneQ.map (toUnit (coordinateZeroBoundary s t M : SSet.{u})))
```

**OneDirectionWeakComparison.lean**

```lean
lemma oneDirection_coordinateZeroContractible (r : ℕ) (X : StableModel.{u}) :
    CoordinateZeroContractible (oneDirectionIndex r ⋙ multiCoreSConstruction (r + 1) X)

lemma oneDirectionFatBoundary_eq_coordinate (r : ℕ) (X : StableModel.{u}) :
    oneDirectionFatBoundary r X = coordinateZeroBoundary Finset.univ ∅
      (oneDirectionIndex r ⋙ multiCoreSConstruction (r + 1) X)

lemma oneDirectionFatBoundary_toPoint_localized_isIso (r : ℕ) (X : StableModel.{u}) :
    IsIso (AnodyneHomotopy.anodyneQ.map
      (toUnit (oneDirectionFatBoundary (r + 1) X : SSet.{u})))

lemma oneDirectionReductionQuotient_image_isIso {D : Type v} [Category.{w} D]
    (L : SSet.{u} ⥤ D) (hL : anodyneExtensions.IsInvertedBy L) (r : ℕ) (X : StableModel.{u}) :
    IsIso (L.map (oneDirectionReductionQuotient r X))

lemma oneDirectionReducedComparison_localized_isIso (r : ℕ) (X : StableModel.{u}) :
    IsIso (AnodyneHomotopy.anodyneQ.map (oneDirectionReducedComparison r X).right)

lemma oneDirectionReducedComparison_kan_piIsomorphism (r : ℕ) (X : StableModel.{u}) :
    Spectra.KanPiIsomorphism
      (Spectra.PointedKanReplacement.map (oneDirectionReducedComparison r X)).right

def oneDirectionKanRealizationFunctor (r : ℕ) : StableModel.{u} ⥤ PointedSimplicialSet.{u}

instance oneDirectionKanRealization_kanComplex (r : ℕ) (X : StableModel.{u}) :
    KanComplex (((oneDirectionKanRealizationFunctor r).obj X).right)

def oneDirectionKanComparisonNat (r : ℕ) :
    oneDirectionKanRealizationFunctor r ⟶ boundaryKanRealizationFunctor r

def oneDirectionLoopComparisonNat (r : ℕ) :
    oneDirectionKanRealizationFunctor r ⋙
      PointedObject.basedHomFunctor (C

lemma oneDirectionLoopComparison_piIsomorphism (r : ℕ) (X : StableModel.{u}) :
    Spectra.KanPiIsomorphism ((oneDirectionLoopComparisonNat r).app X).right
```

現在地：L1a・L1b 完了、L1c 継続中。S₁ 比較の境界商への降下が局所化可逆であることと、Kan 置換・Ω 後の全基点 π_* 比較は証明済み。
同時商と円の smash の同一視、反復間の構造写像、delooping・Ω 条件・BF 連結スペクトルは未完了。
任意の押し出し保存と一般の cofiber 保存条件との同値は未証明。L1d–f 未完了、L1g は別途指示待ち。

検証：対象ビルド成功（2968 jobs）、公理監査成功（938 宣言、標準三公理のみ）。追加公理・sorry なし。

## 6.25 cofiber の smash の降下と実際の suspension からの写像

点つき単体集合の閉対称モノイダル構造により、左右のテンソル積は cofiber の pushout を保存する。
その二つの pushout から逐次降下し、自由な基点を持つ対象の smash 上の射が両境界を零にするなら、
二つの cofiber の smash から降りることと、二つの商射影で元の射を回収することを証明した。
自由な基点の追加と smash の比較を用い、通常の積上の射が両境界を基点へ送る条件からも降ろせる。
いずれも Kan 性・単射性・弱可縮性などを仮定しない、通常の圏の pushout の構成である。

反復 S の区間の組み立てに適用するため、残りの全零境界の cylinder を標的の全零境界へ制限する射と、
それが標的の境界商の基点へ写る式を構成した。
区間の両端についての既存の式と合わせ、L9 の実際の定義である
`Spectra.suspension (oneDirectionReducedRealization r X)` から
`boundaryReducedRealization (r+1) X` への点つき射 `oneDirectionSuspensionAssembly` を構成した。
二つの商射影で引き戻すと元の区間の組み立ての射を回収する厳密な式も証明済み。

この構成では、前節の同時商と smash の同型を先に作る代わりに、
両境界を基点へ送る式をテンソル pushout の普遍性で直接降ろしている。
源は S₁ 比較の源の境界商であり、標準の境界商の列の連続する二段とはまだ揃えていない。
自然性、S₁ 比較を用いた段の接続と Kan 模型への移送、構造射の単射化、delooping・Ω 条件は未完了。
同時商と円の smash の明示的な同型もまだ証明していないが、今回の suspension の射にはその同型を仮定しない。
Core・Stable・F1・HA・Spectra の所有ファイルや公開 API は変更していない。

以下は namespace `SerrePositivity.KST.SConstruction` 内の正確な型。`universe u`、
`open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet`、
`open scoped Simplicial` の下で記す。SuspensionAssembly ではさらに
`CartesianMonoidalCategory` と `SerrePositivity.InfinityCategories SerrePositivity.SimplicialModel` を開く。

**CofiberTensorDesc.lean**

```lean
lemma tensorCofiberRightSquare {A B : SSet.{u}} (g : A ⟶ B) (Y : PointedSimplicialSet.{u}) :
    IsPushout (Y ◁ PointedObject.adjoinFunctor.map g)
      (Y ◁ PointedObject.toPoint (PointedObject.adjoin A))
      (Y ◁ PointedObject.cofiberProjection g) (Y ◁ PointedObject.fromPoint (PointedObject.cofiber g))

lemma tensorCofiberLeftSquare {A B : SSet.{u}} (f : A ⟶ B) (Y : PointedSimplicialSet.{u}) :
    IsPushout (PointedObject.adjoinFunctor.map f ▷ Y)
      (PointedObject.toPoint (PointedObject.adjoin A) ▷ Y)
      (PointedObject.cofiberProjection f ▷ Y) (PointedObject.fromPoint (PointedObject.cofiber f) ▷ Y)

def tensorCofiberRightDesc {A B : SSet.{u}} (g : A ⟶ B) (Y Z : PointedSimplicialSet.{u})
    (h : Y ⊗ PointedObject.adjoin B ⟶ Z)
    (hg : (Y ◁ PointedObject.adjoinFunctor.map g) ≫ h = 0) :
    Y ⊗ PointedObject.cofiber g ⟶ Z

lemma tensorCofiberRightDesc_quotient {A B : SSet.{u}} (g : A ⟶ B)
    (Y Z : PointedSimplicialSet.{u}) (h : Y ⊗ PointedObject.adjoin B ⟶ Z) (hg) :
    (Y ◁ PointedObject.cofiberProjection g) ≫ tensorCofiberRightDesc g Y Z h hg = h

lemma tensorCofiberRightDesc_point {A B : SSet.{u}} (g : A ⟶ B)
    (Y Z : PointedSimplicialSet.{u}) (h : Y ⊗ PointedObject.adjoin B ⟶ Z) (hg) :
    (Y ◁ PointedObject.fromPoint (PointedObject.cofiber g)) ≫
      tensorCofiberRightDesc g Y Z h hg = 0

def tensorCofiberLeftDesc {A B : SSet.{u}} (f : A ⟶ B) (Y Z : PointedSimplicialSet.{u})
    (h : PointedObject.adjoin B ⊗ Y ⟶ Z)
    (hf : (PointedObject.adjoinFunctor.map f ▷ Y) ≫ h = 0) :
    PointedObject.cofiber f ⊗ Y ⟶ Z

lemma tensorCofiberLeftDesc_quotient {A B : SSet.{u}} (f : A ⟶ B)
    (Y Z : PointedSimplicialSet.{u}) (h : PointedObject.adjoin B ⊗ Y ⟶ Z) (hf) :
    (PointedObject.cofiberProjection f ▷ Y) ≫ tensorCofiberLeftDesc f Y Z h hf = h

lemma tensorCofiberRightDesc_left_zero {A B C D : SSet.{u}} (f : A ⟶ B) (g : C ⟶ D)
    (Z : PointedSimplicialSet.{u}) (h : PointedObject.adjoin B ⊗ PointedObject.adjoin D ⟶ Z)
    (hf : (PointedObject.adjoinFunctor.map f ▷ PointedObject.adjoin D) ≫ h = 0)
    (hg : (PointedObject.adjoin B ◁ PointedObject.adjoinFunctor.map g) ≫ h = 0) :
    (PointedObject.adjoinFunctor.map f ▷ PointedObject.cofiber g) ≫
      tensorCofiberRightDesc g (PointedObject.adjoin B) Z h hg = 0

def cofiberTensorDesc {A B C D : SSet.{u}} (f : A ⟶ B) (g : C ⟶ D)
    (Z : PointedSimplicialSet.{u}) (h : PointedObject.adjoin B ⊗ PointedObject.adjoin D ⟶ Z)
    (hf : (PointedObject.adjoinFunctor.map f ▷ PointedObject.adjoin D) ≫ h = 0)
    (hg : (PointedObject.adjoin B ◁ PointedObject.adjoinFunctor.map g) ≫ h = 0) :
    PointedObject.cofiber f ⊗ PointedObject.cofiber g ⟶ Z

lemma cofiberTensorDesc_quotient {A B C D : SSet.{u}} (f : A ⟶ B) (g : C ⟶ D)
    (Z : PointedSimplicialSet.{u}) (h : PointedObject.adjoin B ⊗ PointedObject.adjoin D ⟶ Z)
    (hf) (hg) :
    (PointedObject.cofiberProjection f ⊗ₘ PointedObject.cofiberProjection g) ≫
      cofiberTensorDesc f g Z h hf hg = h
```

**RawCofiberTensorDesc.lean**

```lean
def adjoinTensorMap {A B : SSet.{u}} (Z : PointedSimplicialSet.{u}) (h : A ⊗ B ⟶ Z.right) :
    PointedObject.adjoin A ⊗ PointedObject.adjoin B ⟶ Z

lemma adjoinTensorMap_precomp {A B C D : SSet.{u}} (f : A ⟶ B) (g : C ⟶ D)
    (Z : PointedSimplicialSet.{u}) (h : B ⊗ D ⟶ Z.right) :
    (PointedObject.adjoinFunctor.map f ⊗ₘ PointedObject.adjoinFunctor.map g) ≫
      adjoinTensorMap Z h = adjoinTensorMap Z ((f ⊗ₘ g) ≫ h)

lemma adjoinTensorMap_zero {A B : SSet.{u}} (Z : PointedSimplicialSet.{u})
    (h : A ⊗ B ⟶ Z.right)
    (hh : h = CartesianMonoidalCategory.toUnit (A ⊗ B) ≫ Z.hom) :
    adjoinTensorMap Z h = 0

lemma adjoinTensorMap_left_zero {A B D : SSet.{u}} (f : A ⟶ B)
    (Z : PointedSimplicialSet.{u}) (h : B ⊗ D ⟶ Z.right)
    (hf : (f ▷ D) ≫ h = CartesianMonoidalCategory.toUnit (A ⊗ D) ≫ Z.hom) :
    (PointedObject.adjoinFunctor.map f ▷ PointedObject.adjoin D) ≫ adjoinTensorMap Z h = 0

lemma adjoinTensorMap_right_zero {B C D : SSet.{u}} (g : C ⟶ D)
    (Z : PointedSimplicialSet.{u}) (h : B ⊗ D ⟶ Z.right)
    (hg : (B ◁ g) ≫ h = CartesianMonoidalCategory.toUnit (B ⊗ C) ≫ Z.hom) :
    (PointedObject.adjoin B ◁ PointedObject.adjoinFunctor.map g) ≫ adjoinTensorMap Z h = 0

def rawCofiberTensorDesc {A B C D : SSet.{u}} (f : A ⟶ B) (g : C ⟶ D)
    (Z : PointedSimplicialSet.{u}) (h : B ⊗ D ⟶ Z.right)
    (hf : (f ▷ D) ≫ h = CartesianMonoidalCategory.toUnit (A ⊗ D) ≫ Z.hom)
    (hg : (B ◁ g) ≫ h = CartesianMonoidalCategory.toUnit (B ⊗ C) ≫ Z.hom) :
    PointedObject.cofiber f ⊗ PointedObject.cofiber g ⟶ Z

lemma rawCofiberTensorDesc_quotient {A B C D : SSet.{u}} (f : A ⟶ B) (g : C ⟶ D)
    (Z : PointedSimplicialSet.{u}) (h : B ⊗ D ⟶ Z.right) (hf) (hg) :
    (PointedObject.cofiberProjection f ⊗ₘ PointedObject.cofiberProjection g) ≫
      rawCofiberTensorDesc f g Z h hf hg = adjoinTensorMap Z h
```

**SuspensionAssembly.lean**

```lean
def zeroCylinderAssemblyLift (r : ℕ) (X : StableModel.{u}) :
    (Δ[1] : SSet.{u}) ⊗ (oneDirectionFatBoundary r X : SSet.{u}) ⟶
      (zeroDirectionsFatBoundary (r + 1) X : SSet.{u})

lemma zeroCylinderAssemblyLift_ι (r : ℕ) (X : StableModel.{u}) :
    zeroCylinderAssemblyLift r X ≫ (zeroDirectionsFatBoundary (r + 1) X).ι =
      ((Δ[1] : SSet.{u}) ◁ (oneDirectionFatBoundary r X).ι) ≫ multiDiagonalAssembly r X

lemma multiDiagonalAssembly_zeroCylinder_condition (r : ℕ) (X : StableModel.{u}) :
    ((Δ[1] : SSet.{u}) ◁ (oneDirectionFatBoundary r X).ι) ≫
        multiDiagonalAssembly r X ≫ boundaryReductionQuotient r X =
      toUnit ((Δ[1] : SSet.{u}) ⊗ (oneDirectionFatBoundary r X : SSet.{u})) ≫
        (boundaryReducedRealization r X).hom

def oneDirectionSuspensionAssembly (r : ℕ) (X : StableModel.{u}) :
    Spectra.suspension (oneDirectionReducedRealization r X) ⟶ boundaryReducedRealization (r + 1) X

def oneDirectionSuspensionProjection (r : ℕ) (X : StableModel.{u}) :
    PointedObject.adjoin (Δ[1] : SSet.{u}) ⊗
      PointedObject.adjoin ((oneDirectionRealizationFunctor (r + 1)).obj X) ⟶
        Spectra.suspension (oneDirectionReducedRealization r X)

lemma oneDirectionSuspensionAssembly_quotient (r : ℕ) (X : StableModel.{u}) :
    oneDirectionSuspensionProjection r X ≫ oneDirectionSuspensionAssembly r X =
      adjoinTensorMap (boundaryReducedRealization (r + 1) X)
        (multiDiagonalAssembly (r + 1) X ≫ boundaryReductionQuotient (r + 1) X)
```

現在地：L1a・L1b 完了、L1c 継続中。L9 の suspension を源とする反復間の比較射は構成済み。
その自然性、段と Kan 模型の接続、構造射の単射化、delooping・Ω 条件・BF 連結スペクトルは未完了。
同時商と円の smash の明示的同型、任意の押し出し保存と一般の cofiber 保存条件との同値は未証明。
L1d–f 未完了、L1g は別途指示待ち。

検証：対象ビルド成功（2973 jobs）、公理監査成功（961 宣言、標準三公理のみ）。追加公理・sorry なし。

## 6.26 suspension の組み立てと随伴射の自然性

自由な基点を加えた対象から cofiber への射影はエピ射であり、左右の tensor もエピ性を保つため、
二つの射影の tensor もエピ射となることを証明した。
したがって cofiber の smash からの射は、その二つの射影への引き戻しで検出できる。
底の商射影の可換式を自由な基点を加えた射影へ移す補題と、基点追加の積上の射の後合成の式も証明した。

これを前節の `oneDirectionSuspensionAssembly` に適用し、
入力の全 `StableModel` 射に関する厳密な自然性を証明して自然変換にまとめた。
証明は射影で検出して元の cylinder の自然性と境界商の自然性へ戻す。
その後 L9 の suspension–loop の Hom 同値を適用し、
`oneDirectionAssemblyAdjoint : oneDirectionReducedRealization r X → Ω(boundaryReducedRealization (r+1) X)` を構成した。
随伴の両変数の自然性から、これも厳密な自然変換となる。逆に戻すと元の suspension の射を回収する。

随伴射の同値性は未証明であり、Ω 条件を追加の仮定として与えてはいない。
また源は S₁ 比較の源の境界商のままで、標準の境界商の列の連続二段としてはまだ束ねていない。
段の接続・Kan 模型への移送・構造射の単射化・delooping は未完了。
Core・Stable・F1・HA・Spectra の所有ファイルや公開 API は変更していない。

以下は namespace `SerrePositivity.KST.SConstruction` 内の正確な型。`universe u`、
`open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet`、`open scoped Simplicial` の下で記す。
一般の外延性・射影の自然性には Kan 性や単射性は要求しない。

**CofiberTensorExt.lean**

```lean
instance cofiberProjection_epi {A B : SSet.{u}} (f : A ⟶ B) :
    Epi (PointedObject.cofiberProjection f)

instance cofiberTensorProjection_epi {A B C D : SSet.{u}} (f : A ⟶ B) (g : C ⟶ D) :
    Epi (PointedObject.cofiberProjection f ⊗ₘ PointedObject.cofiberProjection g)

lemma cofiberTensor_hom_ext {A B C D : SSet.{u}} (f : A ⟶ B) (g : C ⟶ D)
    {Z : PointedSimplicialSet.{u}} (p q : PointedObject.cofiber f ⊗ PointedObject.cofiber g ⟶ Z)
    (h : (PointedObject.cofiberProjection f ⊗ₘ PointedObject.cofiberProjection g) ≫ p =
      (PointedObject.cofiberProjection f ⊗ₘ PointedObject.cofiberProjection g) ≫ q) : p = q
```

**CofiberProjectionNaturality.lean**

```lean
lemma cofiberProjection_naturality_of_quotient {A B C D : SSet.{u}}
    (f : A ⟶ B) (g : C ⟶ D) (a : B ⟶ D)
    (k : PointedObject.cofiber f ⟶ PointedObject.cofiber g)
    (hk : PointedObject.cofiberQuotient f ≫ k.right = a ≫ PointedObject.cofiberQuotient g) :
    PointedObject.adjoinFunctor.map a ≫ PointedObject.cofiberProjection g =
      PointedObject.cofiberProjection f ≫ k

lemma adjoinTensorMap_postcomp {A B : SSet.{u}} {Z W : PointedSimplicialSet.{u}}
    (h : A ⊗ B ⟶ Z.right) (k : Z ⟶ W) :
    adjoinTensorMap Z h ≫ k = adjoinTensorMap W (h ≫ k.right)
```

**SuspensionAssemblyNaturality.lean**

```lean
instance oneDirectionSuspensionProjection_epi (r : ℕ) (X : StableModel.{u}) :
    Epi (oneDirectionSuspensionProjection r X)

lemma oneDirectionCofiberProjection_naturality (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    PointedObject.adjoinFunctor.map ((oneDirectionRealizationFunctor (r + 1)).map f) ≫
        PointedObject.cofiberProjection (oneDirectionFatBoundary (r + 1) Y).ι =
      PointedObject.cofiberProjection (oneDirectionFatBoundary (r + 1) X).ι ≫
        oneDirectionReducedRealizationMap r f

lemma oneDirectionSuspensionProjection_naturality (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    (PointedObject.adjoin (Δ[1] : SSet.{u}) ◁
        PointedObject.adjoinFunctor.map ((oneDirectionRealizationFunctor (r + 1)).map f)) ≫
        oneDirectionSuspensionProjection r Y =
      oneDirectionSuspensionProjection r X ≫
        (PointedSimplicialSet.circle.{u} ◁ oneDirectionReducedRealizationMap r f)

lemma oneDirectionSuspensionAssembly_naturality (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    (PointedSimplicialSet.circle.{u} ◁ oneDirectionReducedRealizationMap r f) ≫
        oneDirectionSuspensionAssembly r Y =
      oneDirectionSuspensionAssembly r X ≫ boundaryReducedRealizationMap (r + 1) f

def oneDirectionSuspensionAssemblyNat (r : ℕ) :
    oneDirectionReducedRealizationFunctor r ⋙ tensorLeft PointedSimplicialSet.circle.{u} ⟶
      boundaryReducedRealizationFunctor (r + 1)
```

**SuspensionAssemblyAdjoint.lean**

```lean
def oneDirectionAssemblyAdjoint (r : ℕ) (X : StableModel.{u}) :
    oneDirectionReducedRealization r X ⟶ Spectra.loopSpace (boundaryReducedRealization (r + 1) X)

lemma oneDirectionAssemblyAdjoint_naturality (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    oneDirectionReducedRealizationMap r f ≫ oneDirectionAssemblyAdjoint r Y =
      oneDirectionAssemblyAdjoint r X ≫
        (PointedObject.basedHomFunctor (C

def oneDirectionAssemblyAdjointNat (r : ℕ) :
    oneDirectionReducedRealizationFunctor r ⟶ boundaryReducedRealizationFunctor (r + 1) ⋙
      PointedObject.basedHomFunctor (C

lemma oneDirectionAssemblyAdjoint_uncurry (r : ℕ) (X : StableModel.{u}) :
    (Spectra.suspensionLoopEquiv (oneDirectionReducedRealization r X)
    (boundaryReducedRealization (r + 1) X)).symm (oneDirectionAssemblyAdjoint r X) =
      oneDirectionSuspensionAssembly r X
```

現在地：L1a・L1b 完了、L1c 継続中。L9 の suspension からの反復間の比較射と随伴射は自然変換として証明済み。
段と Kan 模型の接続、構造射の単射化、delooping・Ω 条件・BF 連結スペクトルは未完了。
同時商と円の smash の明示的同型、任意の押し出し保存と一般の cofiber 保存条件との同値は未証明。
L1d–f 未完了、L1g は別途指示待ち。

検証：対象ビルド成功（2977 jobs）、公理監査成功（975 宣言、標準三公理のみ）。追加公理・sorry なし。

## 6.27 比較と suspension の関手的な単射 Kan 模型

L9 の点つき射の因子分解を任意の添字圏 T 上の自然変換へ適用する一般形を構成した。
対象の宇宙 v と射の宇宙 w は独立。底の射の Arrow 図式と中間対象の関手を使い、
左因子による基点を保つ写像を取り、中間対象・左因子・右因子を自然にまとめた。
左因子は単射、右因子は trivial Kan fibration。標的が Kan なら中間対象も Kan で、右因子は全基点 π_* 同型。
元の射が Kan 複体間の π_* 同型なら左因子も π_* 同型になる。

`oneDirectionKanComparisonNat` にこの分解を適用し、自然な Kan 中間模型
`refinedOneDirectionKanFunctor` と両側の比較を得た。
左は単射で π_* 同型、右は trivial Kan fibration で π_* 同型。
元の比較の同値性は §6.24 で証明済みのものを使用し、新しい前提にしていない。

suspension の比較射には標的の点つき Kan 置換の単位を自然に合成してから分解を適用した。
その結果 `monicSuspensionAssemblyNat` は一次方向の境界商の suspension から
Kan 中間対象への自然な単射となり、その中間対象から元の次の Kan 段への比較は
trivial Kan fibration かつ全基点 π_* 同型である。合成は元の Kan 標的への比較と厳密に一致する。

この分解で suspension の源はまだ未置換の一次方向の境界商である。
Kan な前段の suspension と同じ列の次段を結ぶ構造射としてはまだ束ねていない。
その接続、delooping と Ω 条件は未完了であり、BF 連結スペクトルの完成とは数えない。
Core・Stable・F1・HA・Spectra の所有ファイルや公開 API は変更していない。

以下は namespace `SerrePositivity.KST.SConstruction` 内の正確な型。`universe u v w`、
`open CategoryTheory SSet`、`open SerrePositivity.InfinityCategories` の下で記す。
MonicSuspensionAssembly ではさらに `MonoidalCategory` を開く。
一般の分解には記載の条件以外の前提を置かず、S₁ 比較と suspension への適用は `StableModel` の構造のみを使う。

**NaturalPointedFactorization.lean**

```lean
def pointedTransformationArrows {T : Type v} [Category.{w} T]
    {F G : T ⥤ PointedSimplicialSet.{u}} (α : F ⟶ G) : T ⥤ Arrow SSet.{u}

def pointedTransformationMiddle {T : Type v} [Category.{w} T]
    {F G : T ⥤ PointedSimplicialSet.{u}} (α : F ⟶ G) : T ⥤ PointedSimplicialSet.{u}

def pointedTransformationLeft {T : Type v} [Category.{w} T]
    {F G : T ⥤ PointedSimplicialSet.{u}} (α : F ⟶ G) : F ⟶ pointedTransformationMiddle α

def pointedTransformationRight {T : Type v} [Category.{w} T]
    {F G : T ⥤ PointedSimplicialSet.{u}} (α : F ⟶ G) : pointedTransformationMiddle α ⟶ G

lemma pointedTransformation_fac {T : Type v} [Category.{w} T]
    {F G : T ⥤ PointedSimplicialSet.{u}} (α : F ⟶ G) :
    pointedTransformationLeft α ≫ pointedTransformationRight α = α

instance pointedTransformationLeft_mono {T : Type v} [Category.{w} T]
    {F G : T ⥤ PointedSimplicialSet.{u}} (α : F ⟶ G) (X : T) :
    Mono ((pointedTransformationLeft α).app X).right

instance pointedTransformationRight_trivialKanFibration {T : Type v} [Category.{w} T]
    {F G : T ⥤ PointedSimplicialSet.{u}} (α : F ⟶ G) (X : T) :
    TrivialKanFibration ((pointedTransformationRight α).app X).right

instance pointedTransformationMiddle_kanComplex {T : Type v} [Category.{w} T]
    {F G : T ⥤ PointedSimplicialSet.{u}} (α : F ⟶ G) (X : T) [KanComplex (G.obj X).right] :
    KanComplex ((pointedTransformationMiddle α).obj X).right

lemma pointedTransformationRight_piIsomorphism {T : Type v} [Category.{w} T]
    {F G : T ⥤ PointedSimplicialSet.{u}} (α : F ⟶ G) (X : T) [KanComplex (G.obj X).right] :
    Spectra.KanPiIsomorphism ((pointedTransformationRight α).app X).right

lemma pointedTransformationLeft_piIsomorphism {T : Type v} [Category.{w} T]
    {F G : T ⥤ PointedSimplicialSet.{u}} (α : F ⟶ G) (X : T)
    [KanComplex (F.obj X).right] [KanComplex (G.obj X).right]
    (hα : Spectra.KanPiIsomorphism (α.app X).right) :
    Spectra.KanPiIsomorphism ((pointedTransformationLeft α).app X).right
```

**RefinedOneDirectionComparison.lean**

```lean
def refinedOneDirectionKanFunctor (r : ℕ) : StableModel.{u} ⥤ PointedSimplicialSet.{u}

def refinedOneDirectionLeftNat (r : ℕ) :
    oneDirectionKanRealizationFunctor r ⟶ refinedOneDirectionKanFunctor r

def refinedOneDirectionRightNat (r : ℕ) :
    refinedOneDirectionKanFunctor r ⟶ boundaryKanRealizationFunctor r

lemma refinedOneDirection_fac (r : ℕ) :
    refinedOneDirectionLeftNat r ≫ refinedOneDirectionRightNat r = oneDirectionKanComparisonNat r

instance refinedOneDirectionKan_kanComplex (r : ℕ) (X : StableModel.{u}) :
    KanComplex (((refinedOneDirectionKanFunctor r).obj X).right)

instance refinedOneDirectionLeft_mono (r : ℕ) (X : StableModel.{u}) :
    Mono ((refinedOneDirectionLeftNat r).app X).right

instance refinedOneDirectionRight_trivialKanFibration (r : ℕ) (X : StableModel.{u}) :
    TrivialKanFibration ((refinedOneDirectionRightNat r).app X).right

lemma refinedOneDirectionRight_piIsomorphism (r : ℕ) (X : StableModel.{u}) :
    Spectra.KanPiIsomorphism ((refinedOneDirectionRightNat r).app X).right

lemma refinedOneDirectionLeft_piIsomorphism (r : ℕ) (X : StableModel.{u}) :
    Spectra.KanPiIsomorphism ((refinedOneDirectionLeftNat r).app X).right
```

**MonicSuspensionAssembly.lean**

```lean
def kanTargetSuspensionAssemblyNat (r : ℕ) :
    oneDirectionReducedRealizationFunctor r ⋙ tensorLeft PointedSimplicialSet.circle.{u} ⟶
      boundaryKanRealizationFunctor (r + 1)

def monicSuspensionKanFunctor (r : ℕ) : StableModel.{u} ⥤ PointedSimplicialSet.{u}

def monicSuspensionAssemblyNat (r : ℕ) :
    oneDirectionReducedRealizationFunctor r ⋙ tensorLeft PointedSimplicialSet.circle.{u} ⟶
      monicSuspensionKanFunctor r

def monicSuspensionComparisonNat (r : ℕ) :
    monicSuspensionKanFunctor r ⟶ boundaryKanRealizationFunctor (r + 1)

lemma monicSuspensionAssembly_fac (r : ℕ) :
    monicSuspensionAssemblyNat r ≫ monicSuspensionComparisonNat r = kanTargetSuspensionAssemblyNat r

instance monicSuspensionKan_kanComplex (r : ℕ) (X : StableModel.{u}) :
    KanComplex (((monicSuspensionKanFunctor r).obj X).right)

instance monicSuspensionAssembly_mono (r : ℕ) (X : StableModel.{u}) :
    Mono ((monicSuspensionAssemblyNat r).app X).right

instance monicSuspensionComparison_trivialKanFibration (r : ℕ) (X : StableModel.{u}) :
    TrivialKanFibration ((monicSuspensionComparisonNat r).app X).right

lemma monicSuspensionComparison_piIsomorphism (r : ℕ) (X : StableModel.{u}) :
    Spectra.KanPiIsomorphism ((monicSuspensionComparisonNat r).app X).right
```

現在地：L1a・L1b 完了、L1c 継続中。S₁ の Kan 比較の単射模型と、Kan 標的への suspension の自然な単射分解は証明済み。
前段と次段を同じ Kan 列として接続する工程、delooping・Ω 条件・BF 連結スペクトルは未完了。
同時商と円の smash の明示的同型、任意の押し出し保存と一般の cofiber 保存条件との同値は未証明。
L1d–f 未完了、L1g は別途指示待ち。

検証：対象ビルド成功（2980 jobs）、公理監査成功（1003 宣言、標準三公理のみ）。追加公理・sorry なし。

## 6.28 随伴射の Kan な源への延長と可縮な選択空間

一般の点つき anodyne 射 i:A→B と Kan 標的 Z への点つき射 h:A→Z に対し、
点つき写像空間の制限 `basedHom(B,Z) → basedHom(A,Z)` を h の頂点で引き戻した
厳密な延長空間 `pointedExtensionSpace i h` を定義した。
L9 の点つき制限の全単射 RLP とその基底変換により、その一点への射影は trivial Kan fibration。
延長空間は可縮 Kan であり、頂点から実際の点つき延長 k:B→Z を取り出して i≫k=h を証明した。
したがって延長は実際に存在し、任意の単射パラメータ族に沿う相対的な選択の延長も可能。

反復 S の随伴射については、標的の境界商の Kan 置換の単位を loop で写して合成し、
Kan な loop 標的への自然変換 `kanTargetAssemblyAdjointNat` を構成した。
源の点つき Kan 置換の anodyne 単位に沿う延長空間 `kanAssemblyAdjointChoices r X` は可縮 Kan。
その任意の頂点 v から実際の Kan 複体間の射
`kanAssemblyAdjointAt r X v : oneDirectionKanRealizationFunctor r X → loopBoundaryKanFunctor (r+1) X` を得る。
この射は元の標的 Kan 化した随伴射へ厳密に制限される。存在および全単射パラメータに沿う相対補完も証明済み。

今回は延長の厳密な自然な選択や、その延長射の π_* 同型性は結論に含めない。
可縮な選択空間と相対補完は証明したが、同じ Kan 列としての前後の段の接続はまだ束ねていない。
Ω 条件を追加の仮定にせず、delooping の証明対象として残す。
Core・Stable・F1・HA・Spectra の所有ファイルや公開 API は変更していない。

以下は namespace `SerrePositivity.KST.SConstruction` 内の正確な型。`universe u`、
`open CategoryTheory Limits SSet`、`open SerrePositivity.InfinityCategories`、`open scoped Simplicial` の下で記す。
KanAssemblyAdjoint ではさらに `MonoidalCategory` を開く。一般定理に記した anodyne 性・Kan 性は
具体的な反復 S への適用では証明済みであり、`StableModel` 以外の追加前提は残さない。

**PointedExtensionSpace.lean**

```lean
def pointedExtensionSpace {A B Z : PointedSimplicialSet.{u}} (i : A ⟶ B) (h : A ⟶ Z) : SSet.{u}

lemma pointedExtensionSpace_projection_trivialKanFibration {A B Z : PointedSimplicialSet.{u}}
    (i : A ⟶ B) (hi : anodyneExtensions i.right) (h : A ⟶ Z) [KanComplex Z.right] :
    TrivialKanFibration (pullback.snd (Spectra.PointedMapping.prePointed i Z).right
      (SSet.yonedaEquiv.symm (Spectra.PointedMapping.familyVertex h)))

lemma pointedExtensionSpace_isContractibleKan {A B Z : PointedSimplicialSet.{u}}
    (i : A ⟶ B) (hi : anodyneExtensions i.right) (h : A ⟶ Z) [KanComplex Z.right] :
    IsContractibleKan (pointedExtensionSpace i h)

def pointedExtensionMap {A B Z : PointedSimplicialSet.{u}} (i : A ⟶ B) (h : A ⟶ Z)
    (v : (pointedExtensionSpace i h) _⦋0⦌) : B ⟶ Z

lemma pointedExtensionMap_fac {A B Z : PointedSimplicialSet.{u}} (i : A ⟶ B) (h : A ⟶ Z)
    (v : (pointedExtensionSpace i h) _⦋0⦌) : i ≫ pointedExtensionMap i h v = h

lemma exists_pointedExtension {A B Z : PointedSimplicialSet.{u}} (i : A ⟶ B)
    (hi : anodyneExtensions i.right) (h : A ⟶ Z) [KanComplex Z.right] :
    ∃ k : B ⟶ Z, i ≫ k = h

lemma pointedExtensionSpace_relative_lifting {A B Z : PointedSimplicialSet.{u}}
    (i : A ⟶ B) (hi : anodyneExtensions i.right) (h : A ⟶ Z) [KanComplex Z.right]
    {S T : SSet.{u}} (j : S ⟶ T) [Mono j] (a : S ⟶ pointedExtensionSpace i h) :
    ∃ b : T ⟶ pointedExtensionSpace i h, j ≫ b = a
```

**KanAssemblyAdjoint.lean**

```lean
def loopBoundaryKanFunctor (r : ℕ) : StableModel.{u} ⥤ PointedSimplicialSet.{u}

instance loopBoundaryKan_kanComplex (r : ℕ) (X : StableModel.{u}) :
    KanComplex (((loopBoundaryKanFunctor r).obj X).right)

def kanTargetAssemblyAdjointNat (r : ℕ) :
    oneDirectionReducedRealizationFunctor r ⟶ loopBoundaryKanFunctor (r + 1)

def kanAssemblyAdjointChoices (r : ℕ) (X : StableModel.{u}) : SSet.{u}

lemma kanAssemblyAdjointChoices_isContractibleKan (r : ℕ) (X : StableModel.{u}) :
    IsContractibleKan (kanAssemblyAdjointChoices r X)

def kanAssemblyAdjointAt (r : ℕ) (X : StableModel.{u})
    (v : (kanAssemblyAdjointChoices r X) _⦋0⦌) :
    (oneDirectionKanRealizationFunctor r).obj X ⟶ (loopBoundaryKanFunctor (r + 1)).obj X

lemma kanAssemblyAdjointAt_fac (r : ℕ) (X : StableModel.{u})
    (v : (kanAssemblyAdjointChoices r X) _⦋0⦌) :
    Spectra.PointedKanReplacement.unit.app (oneDirectionReducedRealization r X) ≫
        kanAssemblyAdjointAt r X v = (kanTargetAssemblyAdjointNat r).app X

lemma exists_kanAssemblyAdjoint (r : ℕ) (X : StableModel.{u}) :
    ∃ k : (oneDirectionKanRealizationFunctor r).obj X ⟶ (loopBoundaryKanFunctor (r + 1)).obj X,
      Spectra.PointedKanReplacement.unit.app (oneDirectionReducedRealization r X) ≫ k =
        (kanTargetAssemblyAdjointNat r).app X

instance kanAssemblyAdjointChoices_kanComplex (r : ℕ) (X : StableModel.{u}) :
    KanComplex (kanAssemblyAdjointChoices r X)

lemma kanAssemblyAdjointChoices_relative_lifting (r : ℕ) (X : StableModel.{u})
    {S T : SSet.{u}} (j : S ⟶ T) [Mono j] (a : S ⟶ kanAssemblyAdjointChoices r X) :
    ∃ b : T ⟶ kanAssemblyAdjointChoices r X, j ≫ b = a
```

現在地：L1a・L1b 完了、L1c 継続中。随伴射は Kan な源と loop 標的の間の射へ延長でき、その選択空間の可縮性・全単射パラメータに沿う相対補完まで証明済み。
延長の自然性・段の接続、delooping・Ω 条件・BF 連結スペクトルは未完了。
同時商と円の smash の明示的同型、任意の押し出し保存と一般の cofiber 保存条件との同値は未証明。
L1d–f 未完了、L1g は別途指示待ち。

検証：対象ビルド成功（2988 jobs）、公理監査成功（1020 宣言、標準三公理のみ）。追加公理・sorry なし。


## 6.29 Kan 延長の点つきホモトピー比較と全次数の自然性

指定した点つき射 h:A→Z と anodyne な i:A→B、Kan な標的 Z に対して、
任意の二つの延長 k,l:B→Z を結ぶ実際の基点固定ホモトピーを構成した。
各延長を選択空間の頂点へ戻し、その可縮性から得た辺を点つき写像空間へ写す。
源 A・B の Kan 性はこの一般定理の前提ではない。

これを反復 S の Kan な随伴射へ適用し、任意の選択 v,w の間の基点固定ホモトピーと、
入力の射 f:X→Y に関する二つの合成の間の基点固定ホモトピーを証明した。
自然性の証明では Kan 置換の単位と未延長の随伴射の厳密な自然性を使い、
両経路が同じ射を延長することを確認している。源と標的の選択を整合させる仮定は不要。
ここで結論として記録するホモトピーの固定条件は基点についてである。

全自然数次数（零次数を含む）の誘導写像は選択によらず、入力の射について自然になる。
その実際の誘導写像を集合への関手と自然変換 kanAssemblyHomotopyNat に束ねた。
その成分は選択空間の任意の頂点で計算できる。全基点 π_* 同型性はまだ結論していない。
Core・Stable・F1・HA・Spectra の所有ファイルと公開 API は変更していない。

以下は namespace `SerrePositivity.KST.SConstruction`、`universe u`、
`open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet`、
`open SerrePositivity.InfinityCategories`、`open scoped Simplicial` の下の正確な型。

```lean
def pointedExtensionVertex {A B Z : PointedSimplicialSet.{u}} (i : A ⟶ B) (h : A ⟶ Z)
    (k : B ⟶ Z) (hk : i ≫ k = h) : (pointedExtensionSpace i h) _⦋0⦌

lemma pointedExtensionVertex_projection {A B Z : PointedSimplicialSet.{u}} (i : A ⟶ B) (h : A ⟶ Z)
    (k : B ⟶ Z) (hk : i ≫ k = h) :
    (pullback.fst (Spectra.PointedMapping.prePointed i Z).right
      (SSet.yonedaEquiv.symm (Spectra.PointedMapping.familyVertex h))).app (Opposite.op ⦋0⦌)
        (pointedExtensionVertex i h k hk) = Spectra.PointedMapping.familyVertex k

lemma pointedExtensions_nonempty_mappingEdge {A B Z : PointedSimplicialSet.{u}}
    (i : A ⟶ B) (hi : anodyneExtensions i.right) (h : A ⟶ Z) [KanComplex Z.right]
    (k l : B ⟶ Z) (hk : i ≫ k = h) (hl : i ≫ l = h) :
    Nonempty ((PointedObject.basedHom B Z).right.Edge
      (Spectra.PointedMapping.familyVertex k) (Spectra.PointedMapping.familyVertex l))

lemma pointedExtensions_homotopy {A B Z : PointedSimplicialSet.{u}}
    (i : A ⟶ B) (hi : anodyneExtensions i.right) (h : A ⟶ Z) [KanComplex Z.right]
    (k l : B ⟶ Z) (hk : i ≫ k = h) (hl : i ≫ l = h) :
    ∃ H : SSet.Homotopy k.right l.right,
      B.hom ▷ (Δ[1] : SSet.{u}) ≫ H.h = toUnit (𝟙_ SSet.{u} ⊗ (Δ[1] : SSet.{u})) ≫ Z.hom

lemma kanAssemblyAdjointAt_homotopy (r : ℕ) (X : StableModel.{u})
    (v w : (kanAssemblyAdjointChoices r X) _⦋0⦌) :
    ∃ H : SSet.Homotopy (kanAssemblyAdjointAt r X v).right (kanAssemblyAdjointAt r X w).right,
      ((oneDirectionKanRealizationFunctor r).obj X).hom ▷ (Δ[1] : SSet.{u}) ≫ H.h =
        toUnit (𝟙_ SSet.{u} ⊗ (Δ[1] : SSet.{u})) ≫
          ((loopBoundaryKanFunctor (r + 1)).obj X).hom

lemma kanAssemblyAdjointAt_naturality_homotopy (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (v : (kanAssemblyAdjointChoices r X) _⦋0⦌)
    (w : (kanAssemblyAdjointChoices r Y) _⦋0⦌) :
    ∃ H : SSet.Homotopy
      ((oneDirectionKanRealizationFunctor r).map f ≫ kanAssemblyAdjointAt r Y w).right
      (kanAssemblyAdjointAt r X v ≫ (loopBoundaryKanFunctor (r + 1)).map f).right,
      ((oneDirectionKanRealizationFunctor r).obj X).hom ▷ (Δ[1] : SSet.{u}) ≫ H.h =
        toUnit (𝟙_ SSet.{u} ⊗ (Δ[1] : SSet.{u})) ≫
          ((loopBoundaryKanFunctor (r + 1)).obj Y).hom

lemma kanAssemblyAdjointAt_piMap_eq (r n : ℕ) (X : StableModel.{u})
    (v w : (kanAssemblyAdjointChoices r X) _⦋0⦌) :
    Spectra.pointedHomotopyMap n (kanAssemblyAdjointAt r X v) =
      Spectra.pointedHomotopyMap n (kanAssemblyAdjointAt r X w)

lemma kanAssemblyAdjointAt_piMap_naturality (r n : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (v : (kanAssemblyAdjointChoices r X) _⦋0⦌)
    (w : (kanAssemblyAdjointChoices r Y) _⦋0⦌)
    (a : Spectra.KanHomotopy ((oneDirectionKanRealizationFunctor r).obj X).right n
      ((oneDirectionKanRealizationFunctor r).obj X).basepoint) :
    Spectra.pointedHomotopyMap n (kanAssemblyAdjointAt r Y w)
        (Spectra.pointedHomotopyMap n ((oneDirectionKanRealizationFunctor r).map f) a) =
      Spectra.pointedHomotopyMap n ((loopBoundaryKanFunctor (r + 1)).map f)
        (Spectra.pointedHomotopyMap n (kanAssemblyAdjointAt r X v) a)

def oneDirectionHomotopyFunctor (r n : ℕ) : StableModel.{u} ⥤ Type u

def loopBoundaryHomotopyFunctor (r n : ℕ) : StableModel.{u} ⥤ Type u

def kanAssemblyHomotopyNat (r n : ℕ) :
    oneDirectionHomotopyFunctor r n ⟶ loopBoundaryHomotopyFunctor (r + 1) n

lemma kanAssemblyHomotopyNat_app (r n : ℕ) (X : StableModel.{u})
    (v : (kanAssemblyAdjointChoices r X) _⦋0⦌) :
    (kanAssemblyHomotopyNat r n).app X =
      ↾(Spectra.pointedHomotopyMap n (kanAssemblyAdjointAt r X v))
```

現在地：L1a・L1b 完了、L1c 継続中。Kan 延長の可縮な選択空間に加え、
任意の延長の基点固定ホモトピーによる選択独立性・自然性と、全自然数次数の自然な誘導写像まで証明済み。
Kan な同一の列の段の接続、delooping・Ω 条件・BF 連結スペクトルは未完了。
同時商と円の smash の明示的同型、任意の押し出し保存と一般の cofiber 保存条件との同値は未証明。
L1d–f 未完了、L1g は別途指示待ち。

検証：対象ビルド成功（2992 jobs）、公理監査成功（1032 宣言、標準三公理のみ）。追加公理・sorry なし。


## 6.30 同一の反復段を接続する Kan 列と K 空間の零段

一次方向の Kan 比較の全基点 π_* 同型性（§6.24）に L9 の Whitehead を適用して、
実際の点つき逆射と、両向きの合成を恒等射と比較する基点固定ホモトピーを構成した。
逆射自身も全基点・全自然数次数で π_* 同型である。
この逆射を構成済みの Kan な随伴射へ前合成し、元の全零境界商の Kan 模型から
次の全零境界商の Kan 模型の loop への実際の射 boundaryKanAssemblyAdjoint を得た。
uncurry した構造射で同一の列の段を接続する boundaryKanSequence を構成した。
その第 r 段は r+1 重 S の全零境界商の Kan 置換である。

さらに零段を既定の K 空間、後続段をこの反復 S の列とする kKanSequence を構成した。
座標は K(C), |S C|, |S² C|, … の Kan 模型である。
零段の構造射は smash/loop 随伴の余単位で、その随伴射は厳密に恒等射となる。
したがって零段の随伴構造射の全基点 π_* 同型性は証明済み。
正の段の Ω 条件はこの構成の仮定にせず、引き続き本レーンの未証明の主張として残す。

L9 の Kan 列の逐次置換を両列に適用した。得られる列の全構造射は単射で、
元の列への厳密な比較射は各段で全基点 π_* 同型である。
monicKKanSequence の零段は定義済みの boundaryKSpaceFunctor の値と厳密に一致する。
Kan な前段の suspension と同じ列の次段との接続は今回完了したが、
列の厳密な関手性、正の段の Ω 条件、連結性の検証を済ませた BF スペクトルは未完成。
Core・Stable・F1・HA・Spectra の所有ファイルと公開 API は変更していない。

以下は namespace `SerrePositivity.KST.SConstruction`、`universe u`、
`open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet`、
`open scoped Simplicial` の下の正確な型。

```lean
def oneDirectionKanComparisonInverse (r : ℕ) (X : StableModel.{u}) :
    (boundaryKanRealizationFunctor r).obj X ⟶ (oneDirectionKanRealizationFunctor r).obj X

lemma oneDirectionKanComparison_inverse_homotopy (r : ℕ) (X : StableModel.{u}) :
    ∃ H : SSet.Homotopy (𝟙 (((oneDirectionKanRealizationFunctor r).obj X).right))
      (((oneDirectionKanComparisonNat r).app X ≫ oneDirectionKanComparisonInverse r X).right),
      ((oneDirectionKanRealizationFunctor r).obj X).hom ▷ (Δ[1] : SSet.{u}) ≫ H.h =
        toUnit (𝟙_ SSet.{u} ⊗ (Δ[1] : SSet.{u})) ≫
          ((oneDirectionKanRealizationFunctor r).obj X).hom

lemma oneDirectionKanComparisonInverse_homotopy (r : ℕ) (X : StableModel.{u}) :
    ∃ H : SSet.Homotopy (𝟙 (((boundaryKanRealizationFunctor r).obj X).right))
      ((oneDirectionKanComparisonInverse r X ≫ (oneDirectionKanComparisonNat r).app X).right),
      ((boundaryKanRealizationFunctor r).obj X).hom ▷ (Δ[1] : SSet.{u}) ≫ H.h =
        toUnit (𝟙_ SSet.{u} ⊗ (Δ[1] : SSet.{u})) ≫
          ((boundaryKanRealizationFunctor r).obj X).hom

lemma oneDirectionKanComparisonInverse_piIsomorphism (r : ℕ) (X : StableModel.{u}) :
    Spectra.KanPiIsomorphism (oneDirectionKanComparisonInverse r X).right

def boundaryKanAssemblyAdjoint (r : ℕ) (X : StableModel.{u}) :
    (boundaryKanRealizationFunctor r).obj X ⟶ (loopBoundaryKanFunctor (r + 1)).obj X

def boundaryKanAssemblySigma (r : ℕ) (X : StableModel.{u}) :
    Spectra.suspension ((boundaryKanRealizationFunctor r).obj X) ⟶
      (boundaryKanRealizationFunctor (r + 1)).obj X

lemma boundaryKanAssemblySigma_adjoint (r : ℕ) (X : StableModel.{u}) :
    (Spectra.suspensionLoopEquiv _ _) (boundaryKanAssemblySigma r X) =
      boundaryKanAssemblyAdjoint r X

def boundaryKanSequence (X : StableModel.{u}) : Spectra.KanSequence.{u}

def monicBoundaryKanSequence (X : StableModel.{u}) : Spectra.KanSequence.{u}

instance monicBoundaryKanSequence_sigma_mono (X : StableModel.{u}) (r : ℕ) :
    Mono ((monicBoundaryKanSequence X).sigma r).right

def monicBoundaryKanSequenceProjection (X : StableModel.{u}) :
    Spectra.KanSequence.Hom (monicBoundaryKanSequence X) (boundaryKanSequence X)

lemma monicBoundaryKanSequenceProjection_piIsomorphism (X : StableModel.{u}) (r : ℕ) :
    Spectra.KanPiIsomorphism ((monicBoundaryKanSequenceProjection X).app r).right

def kKanSequenceLevel (X : StableModel.{u}) : ℕ → Spectra.PointedKanComplex.{u}

def kKanSequenceSigma (X : StableModel.{u}) :
    ∀ r, Spectra.suspension (kKanSequenceLevel X r).space ⟶
      (kKanSequenceLevel X (r + 1)).space

def kKanSequence (X : StableModel.{u}) : Spectra.KanSequence.{u}

lemma kKanSequence_zero_adjoint (X : StableModel.{u}) :
    (Spectra.suspensionLoopEquiv _ _) ((kKanSequence X).sigma 0) =
      𝟙 (boundaryKSpaceFunctor.obj X)

lemma kKanSequence_zero_piIsomorphism (X : StableModel.{u}) :
    Spectra.KanPiIsomorphism
      ((Spectra.suspensionLoopEquiv _ _) ((kKanSequence X).sigma 0)).right

def monicKKanSequence (X : StableModel.{u}) : Spectra.KanSequence.{u}

instance monicKKanSequence_sigma_mono (X : StableModel.{u}) (r : ℕ) :
    Mono ((monicKKanSequence X).sigma r).right

def monicKKanSequenceProjection (X : StableModel.{u}) :
    Spectra.KanSequence.Hom (monicKKanSequence X) (kKanSequence X)

lemma monicKKanSequenceProjection_piIsomorphism (X : StableModel.{u}) (r : ℕ) :
    Spectra.KanPiIsomorphism ((monicKKanSequenceProjection X).app r).right

lemma monicKKanSequence_zero (X : StableModel.{u}) :
    ((monicKKanSequence X).level 0).space = boundaryKSpaceFunctor.obj X
```

現在地：L1a・L1b 完了、L1c 継続中。同一の段を接続する実際の Kan 列、
K 空間を零段とする列、その単射構造射への置換と各段の π_* 比較まで証明済み。
正の段の Ω 条件・delooping と連結性を含む BF 連結スペクトル、列の厳密な関手性は未完了。
同時商と円の smash の明示的同型、任意の押し出し保存と一般の cofiber 保存条件との同値は未証明。
L1d–f 未完了、L1g は別途指示待ち。

検証：対象ビルド成功（2996 jobs）、公理監査成功（1054 宣言、標準三公理のみ）。追加公理・sorry なし。


## 6.31 構造射のホモトピー自然性と単射な列間の厳密な射

一次方向の比較の選んだ逆射の自然性を写像空間の成分の等式として証明した。
比較の両方向のホモトピー逆の式と元の比較の自然性を用いる。
これを Kan 延長の自然性と合成し、境界商の随伴構造射、uncurry した suspension 構造射の
成分での自然性を得た。uncurry の成分の保持と loop の余単位の自然性は一般形でも証明した。

kKanSequence の零段には境界商の K 空間の関手、正の段には反復 S の Kan 実現の関手の射を使い、
全段の構造射との成分での可換性を証明した。零段では随伴の余単位の厳密な自然性を使う。
単射置換した源の射影を前合成した後も成分での可換性を保つことを、任意の Kan 列の一般補題で示した。
L9 のホモトピー厳密化により、単射置換した源から元の標的列への厳密な列の射 monicKToRawMap を得た。
各段は元の射影と入力の射の合成と同じ点つきホモトピー成分を保つ。

標的の置換射影は各段で全ての単射に対する RLP を持つ。この射影に沿う L9 の列の持ち上げにより、
入力の射 f:X→Y から実際の厳密な列の射
monicKKanSequenceMap f : Hom (monicKKanSequence X) (monicKKanSequence Y) を構成した。
標的の射影との合成は厳密化済みの射を厳密に回収し、元の各段の射との成分の等式も保つ。
厳密な列の射の構成は追加仮定なし。ただし選んだ射の恒等・合成の関手法則はまだ証明していない。
Ω 条件・連結性を仮定して BF スペクトルが完成したとは数えない。
Core・Stable・F1・HA・Spectra の所有ファイルと公開 API は変更していない。

以下は namespace `SerrePositivity.KST.SConstruction`、`universe u`、
`open CategoryTheory MonoidalCategory SSet`、`open Spectra.PointedMapping` の下の正確な型。

```lean
lemma pointedComponentInverse_naturality {A A' B B' : PointedSimplicialSet.{u}}
    (q : A ⟶ B) (q' : A' ⟶ B') (g : B ⟶ A) (g' : B' ⟶ A')
    (e : A ⟶ A') (b : B ⟶ B')
    (hleft : componentOf (q' ≫ g') = componentOf (𝟙 A'))
    (hright : componentOf (g ≫ q) = componentOf (𝟙 B))
    (hn : e ≫ q' = q ≫ b) :
    componentOf (g ≫ e) = componentOf (b ≫ g')

lemma oneDirectionKanComparisonInverse_naturality_component (r : ℕ)
    {X Y : StableModel.{u}} (f : X ⟶ Y) :
    componentOf (oneDirectionKanComparisonInverse r X ≫
      (oneDirectionKanRealizationFunctor r).map f) =
    componentOf ((boundaryKanRealizationFunctor r).map f ≫
      oneDirectionKanComparisonInverse r Y)

lemma boundaryKanAssemblyAdjoint_naturality_component (r : ℕ)
    {X Y : StableModel.{u}} (f : X ⟶ Y) :
    componentOf ((boundaryKanRealizationFunctor r).map f ≫ boundaryKanAssemblyAdjoint r Y) =
      componentOf (boundaryKanAssemblyAdjoint r X ≫ (loopBoundaryKanFunctor (r + 1)).map f)

lemma pointedComponentUncurry {A B : PointedSimplicialSet.{u}}
    {f g : A ⟶ Spectra.loopSpace B} (h : componentOf f = componentOf g) :
    componentOf ((Spectra.suspensionLoopEquiv A B).symm f) =
      componentOf ((Spectra.suspensionLoopEquiv A B).symm g)

lemma boundaryKanAssemblySigma_naturality_component (r : ℕ)
    {X Y : StableModel.{u}} (f : X ⟶ Y) :
    componentOf (PointedSimplicialSet.circle.{u} ◁ (boundaryKanRealizationFunctor r).map f ≫
      boundaryKanAssemblySigma r Y) =
      componentOf (boundaryKanAssemblySigma r X ≫
        (boundaryKanRealizationFunctor (r + 1)).map f)

lemma pointedLoopCounit_naturality {A B : PointedSimplicialSet.{u}} (f : A ⟶ B) :
    PointedSimplicialSet.circle.{u} ◁
      (PointedObject.basedHomFunctor (C

def kKanSequenceLevelMap {X Y : StableModel.{u}} (f : X ⟶ Y) :
    ∀ r, ((kKanSequence X).level r).space ⟶ ((kKanSequence Y).level r).space

lemma kKanSequenceLevelMap_comm {X Y : StableModel.{u}} (f : X ⟶ Y) (r : ℕ) :
    componentOf (PointedSimplicialSet.circle.{u} ◁ kKanSequenceLevelMap f r ≫
      (kKanSequence Y).sigma r) =
      componentOf ((kKanSequence X).sigma r ≫ kKanSequenceLevelMap f (r + 1))

def monicKToRawLevelMap {X Y : StableModel.{u}} (f : X ⟶ Y) (r : ℕ) :
    ((monicKKanSequence X).level r).space ⟶ ((kKanSequence Y).level r).space

lemma pointedComponent_sequence_precompose {A B C : Spectra.KanSequence.{u}}
    (p : Spectra.KanSequence.Hom A B)
    (f : ∀ r, (B.level r).space ⟶ (C.level r).space)
    (hf : ∀ r, componentOf (PointedSimplicialSet.circle.{u} ◁ f r ≫ C.sigma r) =
      componentOf (B.sigma r ≫ f (r + 1))) (r : ℕ) :
    componentOf (PointedSimplicialSet.circle.{u} ◁ (p.app r ≫ f r) ≫ C.sigma r) =
      componentOf (A.sigma r ≫ (p.app (r + 1) ≫ f (r + 1)))

lemma monicKToRawLevelMap_comm {X Y : StableModel.{u}} (f : X ⟶ Y) (r : ℕ) :
    componentOf (PointedSimplicialSet.circle.{u} ◁ monicKToRawLevelMap f r ≫
      (kKanSequence Y).sigma r) =
      componentOf ((monicKKanSequence X).sigma r ≫ monicKToRawLevelMap f (r + 1))

def monicKToRawMap {X Y : StableModel.{u}} (f : X ⟶ Y) :
    Spectra.KanSequence.Hom (monicKKanSequence X) (kKanSequence Y)

lemma monicKToRawMap_component {X Y : StableModel.{u}} (f : X ⟶ Y) (r : ℕ) :
    componentOf ((monicKToRawMap f).app r) = componentOf (monicKToRawLevelMap f r)

lemma monicKKanSequenceProjection_rlp (X : StableModel.{u}) (r : ℕ) :
    (MorphismProperty.monomorphisms SSet.{u}).rlp
      ((monicKKanSequenceProjection X).app r).right

def monicKKanSequenceMap {X Y : StableModel.{u}} (f : X ⟶ Y) :
    Spectra.KanSequence.Hom (monicKKanSequence X) (monicKKanSequence Y)

lemma monicKKanSequenceMap_projection {X Y : StableModel.{u}} (f : X ⟶ Y) (r : ℕ) :
    (monicKKanSequenceMap f).app r ≫ (monicKKanSequenceProjection Y).app r =
      (monicKToRawMap f).app r

lemma monicKKanSequenceMap_projection_component {X Y : StableModel.{u}} (f : X ⟶ Y) (r : ℕ) :
    componentOf ((monicKKanSequenceMap f).app r ≫ (monicKKanSequenceProjection Y).app r) =
      componentOf ((monicKKanSequenceProjection X).app r ≫ kKanSequenceLevelMap f r)
```

現在地：L1a・L1b 完了、L1c 継続中。同一の Kan 列の接続と単射置換に加え、
構造射の成分での自然性と、入力の射から作る置換列間の厳密な比較射まで証明済み。
正の段の Ω 条件・delooping、連結性を含む BF 連結スペクトル、列の射の関手法則は未完了。
同時商と円の smash の明示的同型、任意の押し出し保存と一般の cofiber 保存条件との同値は未証明。
L1d–f 未完了、L1g は別途指示待ち。

検証：対象ビルド成功（3006 jobs）、公理監査成功（1071 宣言、標準三公理のみ）。追加公理・sorry なし。


## 6.32 列の射の成分での関手法則と段ごとのホモトピー集合の自然同型

単射な K の候補列に構成した射が、恒等・合成を各段の点つき写像空間の成分で保つことを証明した。
元の各段の写像には厳密な関手法則があり、置換後の射との射影の後での成分の等式を計算する。
射影は Kan 複体間の全基点 π_* 同型なので、ホモトピー逆で後合成して射影を打ち消せる。
この打ち消しの一般定理は、射の源が Kan でなくても適用できる。

各段 r、全自然数次数 n に対して kStageHomotopyFunctor r n : StableModel ⥤ Type u を構成した。
その写像は実際の厳密な列の射 monicKKanSequenceMap f が誘導する写像であり、
成分での恒等・合成法則と基点固定ホモトピー不変性から、集合の関手としての法則を厳密に満たす。
零次数も含む。未置換の候補列の各段のホモトピー集合の関手も構成した。
置換射影の誘導写像は自然変換で、各入力において π_* 比較による実際の同値と一致する。
この自然変換を kStageHomotopyIso r n として自然同型に束ねた。追加の Ω 条件は不要。

ここで証明した列の射の法則は各段の点つきホモトピー成分での法則である。
列の射そのものの厳密等号や、スペクトルの高次の coherence はまだ結論していない。
段ごとのホモトピー集合への関手を、要求された ∞ 圏の K スペクトル関手の完成とは数えない。
Core・Stable・F1・HA・Spectra の所有ファイルと公開 API は変更していない。

以下は namespace `SerrePositivity.KST.SConstruction`、`universe u`、
`open CategoryTheory SSet`、`open Spectra.PointedMapping` の下の正確な型。

```lean
lemma pointedComponent_cancel_right_of_piIsomorphism {A E B : PointedSimplicialSet.{u}}
    [KanComplex E.right] [KanComplex B.right] (p : E ⟶ B)
    (hp : Spectra.KanPiIsomorphism p.right) (a b : A ⟶ E)
    (h : componentOf (a ≫ p) = componentOf (b ≫ p)) : componentOf a = componentOf b

lemma kKanSequenceLevelMap_id (X : StableModel.{u}) (r : ℕ) :
    kKanSequenceLevelMap (𝟙 X) r = 𝟙 _

lemma kKanSequenceLevelMap_comp {X Y Z : StableModel.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (r : ℕ) :
    kKanSequenceLevelMap (f ≫ g) r = kKanSequenceLevelMap f r ≫ kKanSequenceLevelMap g r

lemma monicKKanSequenceMap_id_component (X : StableModel.{u}) (r : ℕ) :
    componentOf ((monicKKanSequenceMap (𝟙 X)).app r) =
      componentOf (𝟙 (((monicKKanSequence X).level r).space))

lemma monicKKanSequenceMap_comp_component {X Y Z : StableModel.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (r : ℕ) :
    componentOf ((monicKKanSequenceMap (f ≫ g)).app r) =
      componentOf ((monicKKanSequenceMap f).app r ≫ (monicKKanSequenceMap g).app r)

lemma pointedHomotopyMap_eq_of_component {A B : PointedSimplicialSet.{u}}
    [KanComplex A.right] [KanComplex B.right] {f g : A ⟶ B}
    (h : componentOf f = componentOf g) (n : ℕ) :
    Spectra.pointedHomotopyMap n f = Spectra.pointedHomotopyMap n g

def kStageHomotopyFunctor (r n : ℕ) : StableModel.{u} ⥤ Type u

def rawKStageHomotopyFunctor (r n : ℕ) : StableModel.{u} ⥤ Type u

def kStageHomotopyProjection (r n : ℕ) :
    kStageHomotopyFunctor r n ⟶ rawKStageHomotopyFunctor r n

instance kStageHomotopyProjection_app_isIso (r n : ℕ) (X : StableModel.{u}) :
    IsIso ((kStageHomotopyProjection r n).app X)

def kStageHomotopyIso (r n : ℕ) : kStageHomotopyFunctor r n ≅ rawKStageHomotopyFunctor r n
```

現在地：L1a・L1b 完了、L1c 継続中。構成した厳密な列の射は各段の成分で恒等・合成を保ち、
段ごとの全次数のホモトピー集合の関手と、元の候補列への自然同型まで証明済み。
正の段の Ω 条件・delooping、連結性を含む BF 連結スペクトル、スペクトル関手の構成は未完了。
同時商と円の smash の明示的同型、任意の押し出し保存と一般の cofiber 保存条件との同値は未証明。
L1d–f 未完了、L1g は別途指示待ち。

検証：対象ビルド成功（3008 jobs）、公理監査成功（1082 宣言、標準三公理のみ）。追加公理・sorry なし。


## 6.33 反復実現と全ての正の候補段の連結性

正の回数の反復 core S の対角実現が連結であることを証明した。
同時零段の可縮 Kan 性から零段の連結性を取り、零段から対角への写像の π₀ の全射で移す。
全零境界を潰す射影は anodyne を反転する任意の関手で可逆であるという既証の定理を、
実際の π₀ 関手に適用し、その射影の連結成分での全単射を得た。
これにより全零境界商の連結性を得て、anodyne な Kan 置換の単位に沿って移した。
対角や商そのものの Kan 性を仮定していない。

その結果、kKanSequence X の全ての正の段が連結である。
さらに置換射影の全基点 π_* 同型と、零次数の類と π₀ との実際の同値を使い、
monicKKanSequence X の全ての正の段も連結であることを証明した。
点つき Kan 複体の π_* 同型に沿う連結性の反映は一般補題として記録した。
この連結性は π₀ が一点であるという主張であり、高い次数の消滅を含めてはいない。
零段の K 空間が連結であるとも主張しない。
Core・Stable・F1・HA・Spectra の所有ファイルと公開 API は変更していない。

以下は namespace `SerrePositivity.KST.SConstruction`、`universe u`、
`open CategoryTheory SSet`、`open SerrePositivity.InfinityCategories SerrePositivity.SimplicialModel`
の下の正確な型。

```lean
instance multiDiagonalCoreSConstruction_isConnected (r : ℕ) (X : StableModel.{u}) :
    SSet.IsConnected (multiDiagonalCoreSConstruction (r + 1) X)

lemma boundaryReductionQuotient_piZero_bijective (r : ℕ) (X : StableModel.{u}) :
    Function.Bijective (SSet.mapπ₀ (boundaryReductionQuotient r X))

instance boundaryReducedRealization_isConnected (r : ℕ) (X : StableModel.{u}) :
    SSet.IsConnected (boundaryReducedRealization r X).right

instance boundaryKanRealization_isConnected (r : ℕ) (X : StableModel.{u}) :
    SSet.IsConnected (((boundaryKanRealizationFunctor r).obj X).right)

lemma pointedIsConnected_of_piIsomorphism {A B : PointedSimplicialSet.{u}}
    [KanComplex A.right] [KanComplex B.right] [SSet.IsConnected B.right]
    (f : A ⟶ B) (hf : Spectra.KanPiIsomorphism f.right) : SSet.IsConnected A.right

instance kKanSequence_positive_isConnected (X : StableModel.{u}) (r : ℕ) :
    SSet.IsConnected (((kKanSequence X).level (r + 1)).space).right

instance monicKKanSequence_positive_isConnected (X : StableModel.{u}) (r : ℕ) :
    SSet.IsConnected (((monicKKanSequence X).level (r + 1)).space).right
```

現在地：L1a・L1b 完了、L1c 継続中。反復 S の Kan 列と単射置換、入力の射からの厳密な列の比較射、
各段の成分での恒等・合成法則、段ごとのホモトピー集合の関手と自然な模型比較、
全ての正の候補段の連結性（π₀ が一点）まで証明済み。
正の段の Ω 条件・delooping、高い次数の消滅と負次数消滅を含む BF 連結スペクトル、
スペクトル関手の構成は未完了。
同時商と円の smash の明示的同型、任意の押し出し保存と一般の cofiber 保存条件との同値は未証明。
L1d–f 未完了、L1g は別途指示待ち。

検証：対象ビルド成功（3009 jobs）、公理監査成功（1089 宣言、標準三公理のみ）。追加公理・sorry なし。


## 6.34 単体的経路構成の実際の収縮と S の経路実現の弱可縮性

先頭頂点を追加する既存の SimplexPrefix 関手で前合成し、任意の値の圏 C の単体的対象 X から
第 n 段が X_(n+1) となる経路構成を作った。先頭頂点への制限で元の零段への augmentation を作り、
全次数の σ₀ により追加退化を構成した。全ての追加退化恒等式を既存の単体恒等式で証明した。
値の圏の対象の宇宙と射の宇宙は独立で、極限・充填性の仮定は不要。

値が単体集合の場合、経路構成の対角から元の零段への射影と定数経路の切断を構成した。
切断と射影の合成は元の零段で厳密に恒等となる。
経路実現上では、先頭頂点を固定し、区間の単体に従って各後続頂点を先頭へ移す
単調自己写像 simplicialPathCut を明示し、全単体作用素との自然性と両端点を計算した。
これにより、射影と切断の合成から恒等射への実際の区間ホモトピー
simplicialPathDiagonalContraction を構成した。対角の Kan 性は仮定していない。

経路の対角の射影は全 anodyne 反転関手で可逆であり、元の零段が可縮 Kan なら
経路の対角から一点への射も全 anodyne 反転関手で可逆となる。
この一般定理を単体的 core S に適用し、sPathRealization C の弱可縮性を証明した。
入力は零対象を持つ quasicategory で足り、安定性は追加仮定として不要。

追加した先頭頂点を忘れる面 δ₀ の全単体作用素に関する自然性を証明し、
経路構成から元の単体的対象への自然変換、および対角の境界射を構成した。
S の場合の実際の境界射は sPathRealizationBoundary C である。
この境界射の homotopy fiber の計算、反復 S への適用後の fiber と loop の比較、
既存の suspension 構造射との照合は引き続き未証明。
経路全空間の弱可縮性のみから Ω 条件を結論してはいない。
Core・Stable・F1・HA・Spectra・CategoryTheory の所有ファイルと公開 API は変更していない。

以下は namespace `SerrePositivity.KST.SConstruction`、`universe u v w`、
`open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet`、
`open SerrePositivity.InfinityCategories SerrePositivity.SimplicialModel`、
`open scoped Simplicial` の下の正確な型。

```lean
def simplicialPathVertex (d : SimplexCategory) :
    ⦋0⦌ ⟶ SimplexPrefix.functor.obj d

lemma simplicialPathVertex_zero : simplicialPathVertex ⦋0⦌ =
    SimplexCategory.δ (1 : Fin 2)

lemma simplicialPathVertex_naturality {d e : SimplexCategory} (f : d ⟶ e) :
    simplicialPathVertex d ≫ SimplexPrefix.functor.map f = simplicialPathVertex e

def simplicialPath {C : Type u} [Category.{v} C] (X : SimplicialObject C) :
    SimplicialObject C

def simplicialPathAugmentation {C : Type u} [Category.{v} C] (X : SimplicialObject C) :
    simplicialPath X ⟶ (Functor.const SimplexCategoryᵒᵖ).obj (X.obj (Opposite.op ⦋0⦌))

def augmentedSimplicialPath {C : Type u} [Category.{v} C] (X : SimplicialObject C) :
    SimplicialObject.Augmented C

def simplicialPathExtraDegeneracy {C : Type u} [Category.{v} C] (X : SimplicialObject C) :
    SimplicialObject.Augmented.ExtraDegeneracy (augmentedSimplicialPath X)

def simplicialPathCut (d : SimplexCategory) (t : (Δ[1] : SSet.{u}).obj (Opposite.op d)) :
    SimplexPrefix.functor.obj d ⟶ SimplexPrefix.functor.obj d

lemma simplicialPathCut_naturality {d e : SimplexCategory} (f : d ⟶ e)
    (t : (Δ[1] : SSet.{u}).obj (Opposite.op e)) :
    SimplexPrefix.functor.map f ≫ simplicialPathCut e t =
      simplicialPathCut d ((Δ[1] : SSet.{u}).map f.op t) ≫ SimplexPrefix.functor.map f

lemma simplicialPathCut_zero (d : SimplexCategory) :
    simplicialPathCut d (SimplexPrefix.endpoint.{u} d 0) =
      SimplexCategory.isTerminalZero.from (SimplexPrefix.functor.obj d) ≫
        simplicialPathVertex d

lemma simplicialPathCut_one (d : SimplexCategory) :
    simplicialPathCut d (SimplexPrefix.endpoint.{u} d 1) = 𝟙 (SimplexPrefix.functor.obj d)

def simplicialPathSection (X : SimplicialObject SSet.{u}) :
    (Functor.const SimplexCategoryᵒᵖ).obj (X.obj (Opposite.op ⦋0⦌)) ⟶ simplicialPath X

def simplicialPathDiagonalProjection (X : SimplicialObject SSet.{u}) :
    simplicialDiagonalFunctor.obj (simplicialPath X) ⟶ X.obj (Opposite.op ⦋0⦌)

def simplicialPathDiagonalSection (X : SimplicialObject SSet.{u}) :
    X.obj (Opposite.op ⦋0⦌) ⟶ simplicialDiagonalFunctor.obj (simplicialPath X)

def simplicialPathDiagonalCylinder (X : SimplicialObject SSet.{u}) :
    simplicialDiagonalFunctor.obj (simplicialPath X) ⊗ (Δ[1] : SSet.{u}) ⟶
      simplicialDiagonalFunctor.obj (simplicialPath X)

lemma simplicialPathDiagonalSection_projection (X : SimplicialObject SSet.{u}) :
    simplicialPathDiagonalSection X ≫ simplicialPathDiagonalProjection X = 𝟙 _

lemma simplicialPathDiagonalCylinder_zero (X : SimplicialObject SSet.{u}) :
    SSet.ι₀ ≫ simplicialPathDiagonalCylinder X =
      simplicialPathDiagonalProjection X ≫ simplicialPathDiagonalSection X

lemma simplicialPathDiagonalCylinder_one (X : SimplicialObject SSet.{u}) :
    SSet.ι₁ ≫ simplicialPathDiagonalCylinder X = 𝟙 _

def simplicialPathDiagonalContraction (X : SimplicialObject SSet.{u}) :
    SSet.Homotopy (simplicialPathDiagonalProjection X ≫ simplicialPathDiagonalSection X)
      (𝟙 (simplicialDiagonalFunctor.obj (simplicialPath X)))

lemma simplicialPathDiagonalProjection_image_isIso {D : Type v} [Category.{w} D]
    (L : SSet.{u} ⥤ D) (hL : anodyneExtensions.IsInvertedBy L)
    (X : SimplicialObject SSet.{u}) : IsIso (L.map (simplicialPathDiagonalProjection X))

lemma simplicialPathDiagonal_toPoint_image_isIso {D : Type v} [Category.{w} D]
    (L : SSet.{u} ⥤ D) (hL : anodyneExtensions.IsInvertedBy L)
    (X : SimplicialObject SSet.{u}) (hX : IsContractibleKan (X.obj (Opposite.op ⦋0⦌))) :
    IsIso (L.map (toUnit (simplicialDiagonalFunctor.obj (simplicialPath X))))

def sPathRealization (C : SSet.{u}) : SSet.{u}

def sPathRealizationProjection (C : SSet.{u}) : sPathRealization C ⟶ coreSConstruction 0 C

lemma sPathRealization_toPoint_image_isIso {D : Type v} [Category.{w} D]
    (L : SSet.{u} ⥤ D) (hL : anodyneExtensions.IsInvertedBy L)
    (C : SSet.{u}) [Quasicategory C] [HasZeroVertex C] :
    IsIso (L.map (toUnit (sPathRealization C)))

def simplicialPathTail (d : SimplexCategory) : d ⟶ SimplexPrefix.functor.obj d

lemma simplicialPathTail_naturality {d e : SimplexCategory} (f : d ⟶ e) :
    simplicialPathTail d ≫ SimplexPrefix.functor.map f = f ≫ simplicialPathTail e

def simplicialPathBoundary {C : Type u} [Category.{v} C] (X : SimplicialObject C) :
    simplicialPath X ⟶ X

def simplicialPathDiagonalBoundary (X : SimplicialObject SSet.{u}) :
    simplicialDiagonalFunctor.obj (simplicialPath X) ⟶ simplicialDiagonalFunctor.obj X

def sPathRealizationBoundary (C : SSet.{u}) : sPathRealization C ⟶ diagonalCoreSConstruction C
```

現在地：L1a・L1b 完了、L1c 継続中。前節までの候補列・各段の成分での関手法則・
全正次数の段の連結性に加え、単体的経路構成・実際の対角の変形収縮・S の経路実現の弱可縮性と
境界射まで証明済み。
経路の homotopy fiber 比較と既存の構造射との照合、正の段の Ω 条件・delooping、
高い次数と負次数の消滅を含む BF 連結スペクトル、スペクトル関手の構成は未完了。
同時商と円の smash の明示的同型、任意の押し出し保存と一般の cofiber 保存条件との同値は未証明。
L1d–f 未完了、L1g は別途指示待ち。

検証：対象ビルド成功（3069 jobs）、公理監査成功（1118 宣言、標準三公理のみ）。追加公理・sorry なし。


## 6.35 経路の第一行の全単体的比較と S₁ の照合

経路構成の先頭を保つ単体作用素について、正の端点の nerve の関手
pathFirstRowNerveFunctor を構成した。この関手は stdSimplex と自然に同型であり、
各次数で標準単体と有限順序圏の nerve の既存の同型を使っている。
第一行の Ar への包含は、先頭追加した全単体作用素について厳密に自然である。
この可換式と元の第一行制限の式から、
pathFirstRowRestriction C : simplicialPath (simplicialSConstruction C) → pathFirstRowDiagram C
を自然変換として構成した。標的の第 n 段は Fun(N([n]), C) である。

C が安定な quasicategory の場合、各段の比較は L1b の元の第一行制限の
trivial Kan fibration であり、追加の補完仮定は不要。core を取った比較も各段で
trivial Kan fibration となる。対角比較 pathFirstRowDiagonalComparison C は
anodyne 局所化で可逆である。対角の Kan 性は仮定していない。

入力の射 f:C→D の後合成を、第一行の単体的図式の自然変換として構成した。
D が quasicategory で f が零対象と cofiber を保つとき、S の経路側にも自然変換を構成でき、
第一行比較と後合成は自然変換の厳密な等号で可換となる。chosen zero の厳密な保存は不要。
経路の零次段の第一行比較に一点の内部 Hom の同型を合成すると、
既存の sOneComparison C を厳密に回収する。core の比較についても coreSOneComparison C と厳密に一致する。

今回の比較は経路の全空間と第一行の関手空間との比較である。
境界射の homotopy fiber と Ω の比較、反復 S への適用後の比較、既存の suspension 構造射との
照合全体は未完了。零次段の照合だけで Ω 条件を結論してはいない。
Core・Stable・F1・HA・Spectra・CategoryTheory の所有ファイルと公開 API は変更していない。

以下は namespace `SerrePositivity.KST.SConstruction`、`universe u`、
`open CategoryTheory MonoidalCategory MonoidalClosed SSet`、
`open SerrePositivity.InfinityCategories SerrePositivity.SimplicialModel`、
`open scoped Simplicial` の下の正確な型。

```lean
def pathFirstRowOrderMap {d e : SimplexCategory} (f : d ⟶ e) :
    ULift.{u} (Fin (d.len + 1)) →o ULift.{u} (Fin (e.len + 1))

def pathFirstRowNerveFunctor : SimplexCategory ⥤ SSet.{u}

def pathFirstRowSimplexNatIso : stdSimplex.{u} ≅ pathFirstRowNerveFunctor

lemma pathFirstRowInclusion_naturality {d e : SimplexCategory} (f : d ⟶ e) :
    firstRowInclusion.{u} (d.len + 1) ≫
        arNerveMap (SimplexPrefix.functor.map f).toOrderHom =
      pathFirstRowNerveFunctor.map f ≫ firstRowInclusion (e.len + 1)

def pathFirstRowDiagram (C : SSet.{u}) : SimplicialObject SSet.{u}

instance pathFirstRowDiagram_obj_quasicategory (C : SSet.{u}) [Quasicategory C]
    (d : SimplexCategoryᵒᵖ) : Quasicategory ((pathFirstRowDiagram C).obj d)

def pathFirstRowRestriction (C : SSet.{u}) :
    simplicialPath (simplicialSConstruction C) ⟶ pathFirstRowDiagram C

instance pathFirstRowRestriction_trivialKanFibration (C : SSet.{u})
    [Quasicategory C] [IsStable C] (d : SimplexCategoryᵒᵖ) :
    TrivialKanFibration ((pathFirstRowRestriction C).app d)

def corePathFirstRowRestriction (C : SSet.{u}) :
    simplicialPath (simplicialCoreSConstruction C) ⟶
      pathFirstRowDiagram C ⋙ quasicategoryCoreFunctor

instance corePathFirstRowRestriction_trivialKanFibration (C : SSet.{u})
    [Quasicategory C] [IsStable C] (d : SimplexCategoryᵒᵖ) :
    TrivialKanFibration ((corePathFirstRowRestriction C).app d)

def pathFirstRowDiagonalComparison (C : SSet.{u}) : sPathRealization C ⟶
    simplicialDiagonalFunctor.obj (pathFirstRowDiagram C ⋙ quasicategoryCoreFunctor)

lemma pathFirstRowDiagonalComparison_localized_isIso (C : SSet.{u})
    [Quasicategory C] [IsStable C] :
    IsIso (AnodyneHomotopy.anodyneQ.map (pathFirstRowDiagonalComparison C))

def pathFirstRowDiagramMap {C D : SSet.{u}} (f : C ⟶ D) :
    pathFirstRowDiagram C ⟶ pathFirstRowDiagram D

def pathSConstructionMap {C D : SSet.{u}} [Quasicategory D]
    (f : C ⟶ D) (hf : PreservesCofiberData f) :
    simplicialPath (simplicialSConstruction C) ⟶ simplicialPath (simplicialSConstruction D)

lemma pathFirstRowRestriction_naturality {C D : SSet.{u}} [Quasicategory D]
    (f : C ⟶ D) (hf : PreservesCofiberData f) :
    pathSConstructionMap f hf ≫ pathFirstRowRestriction D =
      pathFirstRowRestriction C ≫ pathFirstRowDiagramMap f

lemma pathFirstRowRestriction_zero (C : SSet.{u}) :
    (pathFirstRowRestriction C).app (Opposite.op ⦋0⦌) ≫ firstRowOneHomNatIso.hom.app C =
      sOneComparison C

lemma corePathFirstRowRestriction_zero (C : SSet.{u}) :
    (corePathFirstRowRestriction C).app (Opposite.op ⦋0⦌) ≫
      quasicategoryCoreMap (firstRowOneHomNatIso.hom.app C) = coreSOneComparison C
```

現在地：L1a・L1b 完了、L1c 継続中。経路全空間の弱可縮性・境界射に加え、
経路の第一行の全単体的な自然変換と対角の弱同値、入力の cofiber 保存射への自然性、
零次段での既存の S₁ 比較の厳密な回収まで証明済み。
反復 S へ移した比較、境界射の homotopy fiber の計算と loop の比較、
正の段の Ω 条件・delooping、負次数消滅を含む BF 連結スペクトル、スペクトル関手の構成は未完了。
同時商と円の smash の明示的同型、任意の押し出し保存と一般の cofiber 保存条件との同値は未証明。
L1d–f 未完了、L1g は別途指示待ち。

検証：対象ビルド成功（3071 jobs）、公理監査成功（1135 宣言、標準三公理のみ）。追加公理・sorry なし。


## 6.36 S と有限反復 S による trivial Kan fibration の保存

内部 Hom の標的への自明ファイブレーションは自明ファイブレーションを誘導することを証明した。
テンソルが単射を保つことから、閉随伴の持ち上げ同値で全ての単射に対する RLP を移している。
さらに頂点条件で定義した全部分複体の制限射について、底の射が自明ファイブレーションで
頂点条件を反映するなら、制限射も自明ファイブレーションとなる一般定理を証明した。
底の持ち上げの全頂点の条件を標的の条件から反映し、境界との可換式を包含の単射性で回収する。
この二つの一般定理では対象の Kan 性や quasicategory 性は不要。

quasicategory 間の自明ファイブレーション p:E→B による後合成は、
対角の零対象性と各四角形の押し出し性の保存・反映から gapped 条件を保存・反映する。
この条件の反映により、既存の sPostcompCofiber n p hf は全 n で trivial Kan fibration となる。
hf は元の射の定義に入る保存条件の証明であり、p の自明ファイブレーション性から
preservesSConstructionData_of_trivialKanFibration と toCofiberData で得られる。
E・B の安定性は一段の保存定理には不要。

安定な入力の圏の射 p:X→Y が底で trivial Kan fibration のとき、
有限反復 multiSEndofunctor の全多次数の射も trivial Kan fibration であることを
反復方向数について帰納して証明した。core の各多次数の射も trivial Kan fibration となる。
対角方向に制限して対角の比較定理を適用すると、
(multiRealizationFunctor r).map p は anodyne 局所化で可逆となる。
元の実現の Kan 性は仮定していない。これで自明ファイブレーションである比較を反復 S へ移す道具を得た。
経路の第一行比較を安定な入力の圏の図式へ束ねてこれらの定理を適用する部分は未実装。
Core・Stable・F1・HA・Spectra の所有ファイルと公開 API は変更していない。

以下は namespace `SerrePositivity.KST.SConstruction`、`universe u`、
`open CategoryTheory MonoidalCategory MonoidalClosed SSet`、
`open SerrePositivity.InfinityCategories SerrePositivity.SimplicialModel`、
`open scoped Simplicial` の下の正確な型。

```lean
instance ihomMap_trivialKanFibration (K : SSet.{u}) {E B : SSet.{u}}
    (p : E ⟶ B) [TrivialKanFibration p] : TrivialKanFibration ((ihom K).map p)

lemma fullSubcomplex_trivialKanFibration_of_reflects {X Y : SSet.{u}}
    (P : X _⦋0⦌ → Prop) (Q : Y _⦋0⦌ → Prop) (p : X ⟶ Y) [TrivialKanFibration p]
    (q : (fullSubcomplexOnVertices X P : SSet.{u}) ⟶ fullSubcomplexOnVertices Y Q)
    (hq : q ≫ (fullSubcomplexOnVertices Y Q).ι = (fullSubcomplexOnVertices X P).ι ≫ p)
    (href : ∀ x, Q (p.app (Opposite.op ⦋0⦌) x) → P x) : TrivialKanFibration q

lemma isGapped_iff_postcomp_of_trivialKanFibration {E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B] (p : E ⟶ B) [TrivialKanFibration p]
    {n : ℕ} (F : arNerve n ⟶ E) : IsGapped F ↔ IsGapped (F ≫ p)

instance sPostcompCofiber_trivialKanFibration (n : ℕ) {E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B] (p : E ⟶ B) [TrivialKanFibration p]
    (hf : PreservesCofiberData p) : TrivialKanFibration (sPostcompCofiber n p hf)

instance multiSEndofunctor_map_trivialKanFibration (r : ℕ) {X Y : StableModel.{u}}
    (p : X ⟶ Y) [TrivialKanFibration p.val] (d : Fin r → SimplexCategoryᵒᵖ) :
    TrivialKanFibration ((((multiSEndofunctor r).obj d).map p).val)

instance multiCoreSConstructionFunctor_map_trivialKanFibration (r : ℕ)
    {X Y : StableModel.{u}} (p : X ⟶ Y) [TrivialKanFibration p.val]
    (d : Fin r → SimplexCategoryᵒᵖ) :
    TrivialKanFibration (((multiCoreSConstructionFunctor r).map p).app d)

lemma multiRealizationFunctor_map_localized_isIso (r : ℕ) {X Y : StableModel.{u}}
    (p : X ⟶ Y) [TrivialKanFibration p.val] :
    IsIso (AnodyneHomotopy.anodyneQ.map ((multiRealizationFunctor r).map p))
```

現在地：L1a・L1b 完了、L1c 継続中。経路の第一行比較に加え、S と有限反復 S が
trivial Kan fibration を保ち、core の実現後に弱同値を与えることまで証明済み。
経路の比較を反復へ移す具体的な束ね、境界射の homotopy fiber と loop の比較、
正の段の Ω 条件・delooping、負次数消滅を含む BF 連結スペクトル、スペクトル関手は未完了。
同時商と円の smash の明示的同型、任意の押し出し保存と一般の cofiber 保存条件との同値は未証明。
L1d–f 未完了、L1g は別途指示待ち。

検証：対象ビルド成功（3073 jobs）、公理監査成功（1142 宣言、標準三公理のみ）。追加公理・sorry なし。


## 6.37 経路の第一行比較の安定な図式への束ねと有限反復の弱可縮性

S の経路図式と第一行の関手圏の図式を StableModel に値を持つ単体的図式として束ねた。
第一行の関手圏は点ごとの安定性を持ち、添字制限は零対象と cofiber を保つ。
第一行制限自体は既証の全押し出しと零対象の保存を使って StableModel の射にまとめた。
比較の自然性は元の第一行制限の自然性のままで、追加の選択を含まない。
忘却後の自然変換は元の pathFirstRowRestriction と厳密に一致する。
第一行の零次段から元の入力への比較も StableModel の射として構成し、
零次比較との合成が既存の stableSOneComparison と厳密に一致することを証明した。

この比較に r 重 S の core の実現の関手を後合成した。
各経路次数の比較は自明ファイブレーションの有限反復による保存定理から弱同値となり、
経路方向も対角に取った iteratedPathFirstRowDiagonalComparison は局所化で可逆である。
反復後の零次比較に、反復で写した第一行の一点の比較を合成すると、
反復で写した既存の stableSOneComparison を厳密に回収する。
座標は最内側が経路の S_(n+1)、その外側に r 個の S_n、core の次数も n とする。
先頭方向を経路にした既存の suspension 構造射との座標の照合全体はまだ行っていない。

可縮 Kan な安定な入力の有限反復 S とその core は、全多次数で可縮 Kan であることを
方向数について帰納して示した。各段から一点への自明ファイブレーションを対角の比較定理へ渡すと、
その反復実現は弱可縮となる。
これを経路の零段 S₀X に適用した。反復実現の関手を後合成した後も経路は一般の経路構成と
定義上同じ形であり、§6.34 の実際の収縮による零段への射影の可逆性が適用できる。
したがって iteratedPathRealization r X は全 r で弱可縮である。
対角比較の可逆性と組み合わせ、iteratedFirstRowRealization r X も弱可縮であることを証明した。
経路・第一行の全対角の Kan 性は仮定していない。

これらは経路全空間の比較と弱可縮性である。境界射の homotopy fiber の計算や
それを loop と比較する実現後の homotopy pullback 性は引き続き未証明。
全空間の弱可縮性から無条件で Ω 条件を推論してはいない。
Core・Stable・F1・HA・Spectra の所有ファイルと公開 API は変更していない。

以下は namespace `SerrePositivity.KST.SConstruction`、`universe u`、
`open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet`、
`open SerrePositivity.InfinityCategories SerrePositivity.SimplicialModel`、
`open scoped Simplicial` の下の正確な型。

```lean
def stableSPathDiagram (X : StableModel.{u}) : SimplicialObject StableModel.{u}

def stablePathFirstRowDiagram (X : StableModel.{u}) : SimplicialObject StableModel.{u}

def stablePathFirstRowRestriction (X : StableModel.{u}) :
    stableSPathDiagram X ⟶ stablePathFirstRowDiagram X

instance stablePathFirstRowRestriction_trivialKanFibration (X : StableModel.{u})
    (d : SimplexCategoryᵒᵖ) : TrivialKanFibration (((stablePathFirstRowRestriction X).app d).val)

lemma stablePathFirstRowRestriction_forget (X : StableModel.{u}) :
    Functor.whiskerRight (stablePathFirstRowRestriction X) stableModelForget =
      pathFirstRowRestriction X.carrier

def stablePathFirstRowZeroComparison (X : StableModel.{u}) :
    (stablePathFirstRowDiagram X).obj (Opposite.op ⦋0⦌) ⟶ X

lemma stablePathFirstRowRestriction_zero (X : StableModel.{u}) :
    (stablePathFirstRowRestriction X).app (Opposite.op ⦋0⦌) ≫
      stablePathFirstRowZeroComparison X = stableSOneComparison X

def iteratedPathRealizationDiagram (r : ℕ) (X : StableModel.{u}) : SimplicialObject SSet.{u}

def iteratedFirstRowRealizationDiagram (r : ℕ) (X : StableModel.{u}) : SimplicialObject SSet.{u}

def iteratedPathFirstRowComparison (r : ℕ) (X : StableModel.{u}) :
    iteratedPathRealizationDiagram r X ⟶ iteratedFirstRowRealizationDiagram r X

lemma iteratedPathFirstRowComparison_app_localized_isIso (r : ℕ) (X : StableModel.{u})
    (d : SimplexCategoryᵒᵖ) :
    IsIso (AnodyneHomotopy.anodyneQ.map ((iteratedPathFirstRowComparison r X).app d))

def iteratedPathRealization (r : ℕ) (X : StableModel.{u}) : SSet.{u}

def iteratedFirstRowRealization (r : ℕ) (X : StableModel.{u}) : SSet.{u}

def iteratedPathFirstRowDiagonalComparison (r : ℕ) (X : StableModel.{u}) :
    iteratedPathRealization r X ⟶ iteratedFirstRowRealization r X

lemma iteratedPathFirstRowDiagonalComparison_localized_isIso (r : ℕ) (X : StableModel.{u}) :
    IsIso (AnodyneHomotopy.anodyneQ.map (iteratedPathFirstRowDiagonalComparison r X))

lemma iteratedPathFirstRowComparison_zero (r : ℕ) (X : StableModel.{u}) :
    (iteratedPathFirstRowComparison r X).app (Opposite.op ⦋0⦌) ≫
        (multiRealizationFunctor r).map (stablePathFirstRowZeroComparison X) =
      (multiRealizationFunctor r).map (stableSOneComparison X)

lemma multiSConstruction_isContractibleKan_of_contractible (r : ℕ) (X : StableModel.{u})
    (hX : IsContractibleKan X.carrier) (d : Fin r → SimplexCategoryᵒᵖ) :
    IsContractibleKan ((multiSConstruction r X).obj d)

lemma multiCoreSConstruction_isContractibleKan_of_contractible (r : ℕ) (X : StableModel.{u})
    (hX : IsContractibleKan X.carrier) (d : Fin r → SimplexCategoryᵒᵖ) :
    IsContractibleKan ((multiCoreSConstruction r X).obj d)

lemma multiRealization_toPoint_localized_isIso_of_contractible (r : ℕ) (X : StableModel.{u})
    (hX : IsContractibleKan X.carrier) :
    IsIso (AnodyneHomotopy.anodyneQ.map (toUnit ((multiRealizationFunctor r).obj X)))

lemma iteratedPathRealization_toPoint_localized_isIso (r : ℕ) (X : StableModel.{u}) :
    IsIso (AnodyneHomotopy.anodyneQ.map (toUnit (iteratedPathRealization r X)))

lemma iteratedFirstRowRealization_toPoint_localized_isIso (r : ℕ) (X : StableModel.{u}) :
    IsIso (AnodyneHomotopy.anodyneQ.map (toUnit (iteratedFirstRowRealization r X)))
```

現在地：L1a・L1b 完了、L1c 継続中。経路と第一行の比較を安定な入力の図式に束ねて
有限反復 S へ移し、全対角の弱同値、零次段の厳密な比較、両全対角の弱可縮性まで証明済み。
反復した境界射の homotopy fiber の計算と loop の比較、既存の構造射との座標の照合、
正の段の Ω 条件・delooping、負次数消滅を含む BF 連結スペクトル、スペクトル関手は未完了。
同時商と円の smash の明示的同型、任意の押し出し保存と一般の cofiber 保存条件との同値は未証明。
L1d–f 未完了、L1g は別途指示待ち。

検証：対象ビルド成功（3076 jobs）、公理監査成功（1163 宣言、標準三公理のみ）。追加公理・sorry なし。


## 6.38 反復した境界図式と既存の多重実現への全単体的座標同型

先頭を忘れる経路の境界の、任意の単体的図式の射に関する自然性を証明した。
安定な入力の S 図式に外側の r 重 S の core の実現を施すことで、
反復した境界の自然変換とその全対角の実際の境界射を構成した。
入力の射による源・標的の図式の写像と全対角の写像も構成し、境界との厳密な自然性を証明した。

最内側の S を用いる標的の座標を既存の多重反復の座標と照合した。
まず全方向を次数 n に固定した対象の一致と、固定 n での安定な自己関手の自然同型を帰納的に証明した。
零回反復では、元の core S の実現、経路実現、経路境界をそれぞれ厳密に回収する。

一般の単体作用素との自然性のため、自己関手の合成のモノイダル構造と、その関手圏の点ごとの
モノイダル構造を使い、diagonalSInnerComparisonNatIso を構成した。
方向数の帰納の始点に左右の単位子、帰納段に結合子を使うため、単体次数と安定な入力の両方について自然。
モノイダル構造の instance は当該モジュール内の local とし、他レーンの公開 API は変更していない。

この比較を入力で評価して core を取り、対角実現で写した。
既存の二重対角で内側の作用を先に適用する順序と、自己関手の水平合成で外側の作用を先に適用する順序の
違いを、自然変換の自然性の式で厳密に交換した。
その結果、実際の単体集合の同型
iteratedSRealizationCoordinateIso r X : iteratedSRealization r X ≅ multiDiagonalCoreSConstruction (r+1) X
を得た。対象の一致だけから構造写像の一致を推論してはいない。

境界射にこの同型を合成し、既存の multiDiagonalCoreSConstruction を標的にした
canonicalIteratedPathBoundary を構成した。さらに既存の全零境界商の射影と点つき Kan 置換の単位を合成し、
reducedIteratedPathBoundary と kanIteratedPathBoundary を構成した。これらは底の単体集合の射である。
源の弱可縮性は前節で証明済みで、標的は既存の各模型そのものを使っている。
ただし源の基点を含む点つき境界の束ねと、canonical な合成射の入力への自然性の個別の式は未記録。

境界射の homotopy fiber を計算したわけではなく、既存の suspension 構造射との照合全体や
正の段の Ω 条件は未証明。全空間が弱可縮で標的が Kan であることだけから、それらを結論してはいない。
Core・Stable・F1・HA・Spectra の所有ファイルと公開 API は変更していない。

以下は namespace `SerrePositivity.KST.SConstruction`、`universe u v`、
`open CategoryTheory MonoidalCategory MonoidalClosed SSet`、
`open SerrePositivity.InfinityCategories`、`open scoped Simplicial` の下の正確な型。
自己関手のテンソルの式は `attribute [local instance] CategoryTheory.endofunctorMonoidalCategory`
および Mathlib の Monoidal.FunctorCategory の点ごとの instance の下で読む。

```lean
lemma simplicialPathBoundary_naturality {C : Type u} [Category.{v} C]
    {X Y : SimplicialObject C} (f : X ⟶ Y) :
    Functor.whiskerLeft SimplexPrefix.functor.op f ≫ simplicialPathBoundary Y =
      simplicialPathBoundary X ≫ f

def stableSConstructionDiagram (X : StableModel.{u}) : SimplicialObject StableModel.{u}

def iteratedSRealizationDiagram (r : ℕ) (X : StableModel.{u}) : SimplicialObject SSet.{u}

def iteratedPathBoundary (r : ℕ) (X : StableModel.{u}) :
    iteratedPathRealizationDiagram r X ⟶ iteratedSRealizationDiagram r X

def iteratedSRealization (r : ℕ) (X : StableModel.{u}) : SSet.{u}

def iteratedPathRealizationBoundary (r : ℕ) (X : StableModel.{u}) :
    iteratedPathRealization r X ⟶ iteratedSRealization r X

def iteratedSRealizationDiagramMap (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    iteratedSRealizationDiagram r X ⟶ iteratedSRealizationDiagram r Y

def iteratedPathRealizationDiagramMap (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    iteratedPathRealizationDiagram r X ⟶ iteratedPathRealizationDiagram r Y

lemma iteratedPathBoundary_naturality (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    iteratedPathRealizationDiagramMap r f ≫ iteratedPathBoundary r Y =
      iteratedPathBoundary r X ≫ iteratedSRealizationDiagramMap r f

def iteratedSRealizationMap (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    iteratedSRealization r X ⟶ iteratedSRealization r Y

def iteratedPathRealizationMap (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    iteratedPathRealization r X ⟶ iteratedPathRealization r Y

lemma iteratedPathRealizationBoundary_naturality (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    iteratedPathRealizationMap r f ≫ iteratedPathRealizationBoundary r Y =
      iteratedPathRealizationBoundary r X ≫ iteratedSRealizationMap r f

lemma multiSConstruction_diagonal_inner (r n : ℕ) (X : StableModel.{u}) :
    (multiSConstruction r (sStableModel n X)).obj (fun _ => Opposite.op ⦋n⦌) =
      (multiSConstruction (r + 1) X).obj (fun _ => Opposite.op ⦋n⦌)

def multiSEndofunctor_diagonal_inner_iso (r n : ℕ) :
    sEndofunctor.{u} n ⋙ (multiSEndofunctor r).obj (fun _ => Opposite.op ⦋n⦌) ≅
      (multiSEndofunctor (r + 1)).obj (fun _ => Opposite.op ⦋n⦌)

lemma iteratedSRealization_zero (X : StableModel.{u}) :
    iteratedSRealization 0 X = diagonalCoreSConstruction X.carrier

lemma iteratedPathRealization_zero (X : StableModel.{u}) :
    iteratedPathRealization 0 X = sPathRealization X.carrier

lemma iteratedPathRealizationBoundary_zero (X : StableModel.{u}) :
    iteratedPathRealizationBoundary 0 X = sPathRealizationBoundary X.carrier

def diagonalSEndofunctor (r : ℕ) :
    SimplexCategoryᵒᵖ ⥤ (StableModel.{u} ⥤ StableModel.{u})

lemma diagonalSEndofunctor_zero :
    diagonalSEndofunctor.{u} 0 = 𝟙_ (SimplexCategoryᵒᵖ ⥤ (StableModel.{u} ⥤ StableModel.{u}))

lemma diagonalSEndofunctor_succ (r : ℕ) :
    diagonalSEndofunctor.{u} (r + 1) = diagonalSEndofunctor r ⊗ simplicialStableEndofunctor

def diagonalSInnerComparisonNatIso (r : ℕ) :
    simplicialStableEndofunctor.{u} ⊗ diagonalSEndofunctor r ≅ diagonalSEndofunctor (r + 1)

def stableEndofunctorCoreEvaluation (X : StableModel.{u}) :
    (StableModel.{u} ⥤ StableModel.{u}) ⥤ SSet.{u}

def diagonalInnerSCoreDiagram (r : ℕ) (X : StableModel.{u}) : SimplicialObject SSet.{u}

def diagonalInnerSCoreDiagramIso (r : ℕ) (X : StableModel.{u}) :
    diagonalInnerSCoreDiagram r X ≅
      diagonalSEndofunctor (r + 1) ⋙ stableEndofunctorCoreEvaluation X

def diagonalInnerSRealizationIso (r : ℕ) (X : StableModel.{u}) :
    simplicialDiagonalFunctor.obj (diagonalInnerSCoreDiagram r X) ≅
      multiDiagonalCoreSConstruction (r + 1) X

def iteratedSRealizationInnerIso (r : ℕ) (X : StableModel.{u}) :
    iteratedSRealization r X ≅ simplicialDiagonalFunctor.obj (diagonalInnerSCoreDiagram r X)

def iteratedSRealizationCoordinateIso (r : ℕ) (X : StableModel.{u}) :
    iteratedSRealization r X ≅ multiDiagonalCoreSConstruction (r + 1) X

def canonicalIteratedPathBoundary (r : ℕ) (X : StableModel.{u}) :
    iteratedPathRealization r X ⟶ multiDiagonalCoreSConstruction (r + 1) X

def reducedIteratedPathBoundary (r : ℕ) (X : StableModel.{u}) :
    iteratedPathRealization r X ⟶ (boundaryReducedRealization r X).right

def kanIteratedPathBoundary (r : ℕ) (X : StableModel.{u}) :
    iteratedPathRealization r X ⟶ ((boundaryKanRealizationFunctor r).obj X).right
```

現在地：L1a・L1b 完了、L1c 継続中。反復した経路の境界図式と入力への自然性、
境界の標的と既存の多重実現との実際の全単体的同型、全零境界商・Kan 模型への接続まで証明済み。
境界射の homotopy fiber と loop の比較、点つき境界の束ね、既存の suspension 構造射との照合、
正の段の Ω 条件・delooping、負次数消滅を含む BF 連結スペクトル、スペクトル関手は未完了。
同時商と円の smash の明示的同型、任意の押し出し保存と一般の cofiber 保存条件との同値は未証明。
L1d–f 未完了、L1g は別途指示待ち。

検証：対象ビルド成功（3081 jobs）、公理監査成功（1193 宣言、標準三公理のみ）。追加公理・sorry なし。


## 6.39 定数経路を潰す点つき反復経路と実際の可縮 Kan 模型

一般の単体的単体集合の経路実現について、元の零段からの定数経路の切断は
射影との合成が恒等であるため単射であることを証明した。その切断の像を cofiber で一点へ潰し、
reducedPathDiagonal とその図式に対する関手を構成した。
経路図式自身の零次段（元の第一段）全体を潰すのではなく、元の零段から来る定数経路の像のみを潰している。
元の零段が弱可縮なら、この商射影は全 anodyne 反転関手で可逆となる。零段自体の Kan 性は不要。

先頭を忘れる経路境界は、定数切断を元の零段の対角への包含 diagonalZeroColumn に送る。
この厳密な式から、境界を reducedPathDiagonal X → reducedDiagonal X という点つき射に降ろした。
商射影の前で元の境界を回収する式と、任意の単体的図式の写像に対する厳密な自然性を証明し、
境界を自然変換 reducedPathDiagonalBoundaryNat にまとめた。
標的はこの時点では一つの零方向を潰す reducedDiagonal であり、既存の全零方向の商との比較は未証明。

具体的な反復 S の図式に適用し、chosen zero を使わない点つき反復経路の関手
pointedIteratedPathFunctor r を構成した。元の零段は S₀X の反復実現なので弱可縮であり、
元の反復経路から点つき商への射影は弱同値となる。したがってこの点つき商自体も弱可縮である。
点つき境界とその入力への自然性は一般の自然変換の前合成から得ている。

L9 の点つき Kan 置換を後合成して pointedIteratedPathKanFunctor r を構成した。
置換の anodyne 単位と元の点つき経路の弱可縮性から、その Kan 模型も弱可縮である。
一般に弱可縮な点つき Kan 複体について、局所化の比較を実際の全基点 π_* 同型へ移し、
点への Kan fibration の相対 Whitehead の充填から全境界の充填を導く一般補題を証明した。
これにより pointedIteratedPathKan_isContractibleKan r X は追加仮定なしで証明済み。
Kan な点つき境界も自然変換にまとめ、可縮 Kan な全空間からの実際の射を得た。

今回の点つき境界の標的は最内側の一つの零方向を潰した模型の Kan 置換。
既存の全零境界商の Kan 模型への点つき比較、前節の canonicalIteratedPathBoundary の降下との照合、
homotopy fiber の計算と Ω の比較は未完了。可縮 Kan な全空間の構成だけで Ω 条件を結論してはいない。
Core・Stable・F1・HA・Spectra の所有ファイルと公開 API は変更していない。

以下は namespace `SerrePositivity.KST.SConstruction`、`universe u v w`、
`open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet`、
`open SerrePositivity.InfinityCategories SerrePositivity.SimplicialModel`、
`open scoped Simplicial` の下の正確な型。

```lean
instance simplicialPathDiagonalSection_mono (X : SimplicialObject SSet.{u}) :
    Mono (simplicialPathDiagonalSection X)

lemma simplicialPathDiagonalSection_naturality {X Y : SimplicialObject SSet.{u}} (f : X ⟶ Y) :
    f.app (Opposite.op ⦋0⦌) ≫ simplicialPathDiagonalSection Y =
      simplicialPathDiagonalSection X ≫
        simplicialDiagonalFunctor.map (Functor.whiskerLeft SimplexPrefix.functor.op f)

def reducedPathDiagonal (X : SimplicialObject SSet.{u}) : PointedSimplicialSet.{u}

def pathDiagonalReductionQuotient (X : SimplicialObject SSet.{u}) :
    simplicialDiagonalFunctor.obj (simplicialPath X) ⟶ (reducedPathDiagonal X).right

def reducedPathDiagonalMap {X Y : SimplicialObject SSet.{u}} (f : X ⟶ Y) :
    reducedPathDiagonal X ⟶ reducedPathDiagonal Y

lemma reducedPathDiagonalMap_quotient {X Y : SimplicialObject SSet.{u}} (f : X ⟶ Y) :
    pathDiagonalReductionQuotient X ≫ (reducedPathDiagonalMap f).right =
      simplicialDiagonalFunctor.map (Functor.whiskerLeft SimplexPrefix.functor.op f) ≫
        pathDiagonalReductionQuotient Y

lemma pathDiagonalReductionQuotient_image_isIso {D : Type v} [Category.{w} D]
    (L : SSet.{u} ⥤ D) (hL : anodyneExtensions.IsInvertedBy L)
    (X : SimplicialObject SSet.{u})
    (hX : IsIso (AnodyneHomotopy.anodyneQ.map (toUnit (X.obj (Opposite.op ⦋0⦌))))) :
    IsIso (L.map (pathDiagonalReductionQuotient X))

def reducedPathDiagonalFunctor :
    (SimplexCategoryᵒᵖ ⥤ SSet.{u}) ⥤ PointedSimplicialSet.{u}

lemma simplicialPathDiagonalSection_boundary (X : SimplicialObject SSet.{u}) :
    simplicialPathDiagonalSection X ≫ simplicialPathDiagonalBoundary X = diagonalZeroColumn X

def reducedPathDiagonalBoundary (X : SimplicialObject SSet.{u}) :
    reducedPathDiagonal X ⟶ reducedDiagonal X

lemma reducedPathDiagonalBoundary_quotient (X : SimplicialObject SSet.{u}) :
    pathDiagonalReductionQuotient X ≫ (reducedPathDiagonalBoundary X).right =
      simplicialPathDiagonalBoundary X ≫ diagonalReductionQuotient X

lemma reducedPathDiagonalBoundary_naturality {X Y : SimplicialObject SSet.{u}} (f : X ⟶ Y) :
    reducedPathDiagonalMap f ≫ reducedPathDiagonalBoundary Y =
      reducedPathDiagonalBoundary X ≫ reducedDiagonalMap f

def reducedPathDiagonalBoundaryNat : reducedPathDiagonalFunctor.{u} ⟶ reducedDiagonalFunctor

lemma pointedIsContractibleKan_of_localized_toPoint (Z : PointedSimplicialSet.{u})
    [KanComplex Z.right]
    (hZ : IsIso (AnodyneHomotopy.anodyneQ.map (toUnit Z.right))) :
    IsContractibleKan Z.right

def iteratedSRealizationDiagramFunctor (r : ℕ) :
    StableModel.{u} ⥤ (SimplexCategoryᵒᵖ ⥤ SSet.{u})

def pointedIteratedPathFunctor (r : ℕ) : StableModel.{u} ⥤ PointedSimplicialSet.{u}

def pointedIteratedPathRealization (r : ℕ) (X : StableModel.{u}) : PointedSimplicialSet.{u}

def pointedIteratedPathQuotient (r : ℕ) (X : StableModel.{u}) :
    iteratedPathRealization r X ⟶ (pointedIteratedPathRealization r X).right

lemma pointedIteratedPathQuotient_image_isIso {D : Type v} [Category.{w} D]
    (L : SSet.{u} ⥤ D) (hL : anodyneExtensions.IsInvertedBy L) (r : ℕ) (X : StableModel.{u}) :
    IsIso (L.map (pointedIteratedPathQuotient r X))

lemma pointedIteratedPath_toPoint_localized_isIso (r : ℕ) (X : StableModel.{u}) :
    IsIso (AnodyneHomotopy.anodyneQ.map (toUnit (pointedIteratedPathRealization r X).right))

def pointedIteratedPathBoundaryNat (r : ℕ) : pointedIteratedPathFunctor.{u} r ⟶
    iteratedSRealizationDiagramFunctor r ⋙ reducedDiagonalFunctor

def pointedIteratedPathBoundary (r : ℕ) (X : StableModel.{u}) :
    pointedIteratedPathRealization r X ⟶ reducedDiagonal (iteratedSRealizationDiagram r X)

lemma pointedIteratedPathBoundary_quotient (r : ℕ) (X : StableModel.{u}) :
    pointedIteratedPathQuotient r X ≫ (pointedIteratedPathBoundary r X).right =
      iteratedPathRealizationBoundary r X ≫
        diagonalReductionQuotient (iteratedSRealizationDiagram r X)

def pointedIteratedPathKanFunctor (r : ℕ) : StableModel.{u} ⥤ PointedSimplicialSet.{u}

instance pointedIteratedPathKan_kanComplex (r : ℕ) (X : StableModel.{u}) :
    KanComplex (((pointedIteratedPathKanFunctor r).obj X).right)

lemma pointedIteratedPathKan_toPoint_localized_isIso (r : ℕ) (X : StableModel.{u}) :
    IsIso (AnodyneHomotopy.anodyneQ.map
      (toUnit (((pointedIteratedPathKanFunctor r).obj X).right)))

lemma pointedIteratedPathKan_isContractibleKan (r : ℕ) (X : StableModel.{u}) :
    IsContractibleKan (((pointedIteratedPathKanFunctor r).obj X).right)

def pointedIteratedPathKanBoundaryNat (r : ℕ) : pointedIteratedPathKanFunctor.{u} r ⟶
    (iteratedSRealizationDiagramFunctor r ⋙ reducedDiagonalFunctor) ⋙
      Spectra.PointedKanReplacement.functor

def pointedIteratedPathKanBoundary (r : ℕ) (X : StableModel.{u}) :
    (pointedIteratedPathKanFunctor r).obj X ⟶
      Spectra.PointedKanReplacement.obj (reducedDiagonal (iteratedSRealizationDiagram r X))
```

現在地：L1a・L1b 完了、L1c 継続中。定数経路の像を潰した自然な点つき反復経路、
一つの零方向の商を標的にした自然な点つき境界、その Kan 置換と全空間の実際の可縮 Kan 性まで証明済み。
全零境界商を標的とする境界への点つき比較、homotopy fiber と loop の比較、
既存の suspension 構造射との照合、正の段の Ω 条件・delooping、
負次数消滅を含む BF 連結スペクトル、スペクトル関手は未完了。
同時商と円の smash の明示的同型、任意の押し出し保存と一般の cofiber 保存条件との同値は未証明。
L1d–f 未完了、L1g は別途指示待ち。

検証：対象ビルド成功（3085 jobs）、公理監査成功（1222 宣言、標準三公理のみ）。追加公理・sorry なし。

### 6.40 最内側の可変次数と最後の零方向の一致

`InnerVariableCoordinates.lean` と `InnerZeroDirectionCoordinates.lean`。
外側の多次数を固定し、最内側の次数を変数とする添字関手と S 自己関手の座標同型を構成した。
零次数を含む全単体作用素について自然性を証明し、自然同型として束ねた。
固定した外側の次数がすべて d のとき、最内側への d の代入は対角添字に一致し、
零次数の代入は既存の最後の零方向の添字に一致する。
零次数から d への作用素についても、両端の添字の等号による輸送を明示して、
既存の `zeroDirectionsIndexNat {Fin.last r}` そのものと一致する式を証明した。

前提：`r : ℕ`、`d : Fin r → SimplexCategoryᵒᵖ` または `d : SimplexCategoryᵒᵖ`。
安定な入力の圏には既存の `StableModel.{u}` を使う。零次数からの作用素の一致に追加の仮定はない。
以下は namespace `SerrePositivity.KST.SConstruction`、`universe u`、
`open CategoryTheory`、`open scoped Simplicial` の下での正確な公開型。

```lean
def innerVariableIndex (r : ℕ) (d : Fin r → SimplexCategoryᵒᵖ) :
    SimplexCategoryᵒᵖ ⥤ (Fin (r + 1) → SimplexCategoryᵒᵖ)

def innerVariableSComparisonIso (r : ℕ) (d : Fin r → SimplexCategoryᵒᵖ)
    (k : SimplexCategoryᵒᵖ) :
    sEndofunctor.{u} k.unop.len ⋙ (multiSEndofunctor r).obj d ≅
      (multiSEndofunctor (r + 1)).obj ((innerVariableIndex r d).obj k)

lemma innerVariableSMap_succ (r : ℕ) (d : Fin (r + 1) → SimplexCategoryᵒᵖ)
    {k l : SimplexCategoryᵒᵖ} (f : k ⟶ l) :
    (multiSEndofunctor.{u} (r + 2)).map ((innerVariableIndex (r + 1) d).map f) =
      Functor.whiskerRight
        ((multiSEndofunctor (r + 1)).map ((innerVariableIndex r (fun i => d i.succ)).map f))
        (sEndofunctor (d 0).unop.len)

lemma innerVariableSComparisonIso_naturality (r : ℕ) (d : Fin r → SimplexCategoryᵒᵖ)
    {k l : SimplexCategoryᵒᵖ} (f : k ⟶ l) :
    Functor.whiskerRight (simplicialStableEndofunctor.{u}.map f) ((multiSEndofunctor r).obj d) ≫
        (innerVariableSComparisonIso r d l).hom =
      (innerVariableSComparisonIso r d k).hom ≫
        (multiSEndofunctor (r + 1)).map ((innerVariableIndex r d).map f)

lemma innerVariableIndex_obj_last (r : ℕ) (d : Fin r → SimplexCategoryᵒᵖ)
    (k : SimplexCategoryᵒᵖ) : (innerVariableIndex r d).obj k (Fin.last r) = k

lemma innerVariableIndex_obj_castSucc (r : ℕ) (d : Fin r → SimplexCategoryᵒᵖ)
    (k : SimplexCategoryᵒᵖ) (i : Fin r) :
    (innerVariableIndex r d).obj k i.castSucc = d i

lemma innerVariableIndex_map_last (r : ℕ) (d : Fin r → SimplexCategoryᵒᵖ)
    {k l : SimplexCategoryᵒᵖ} (f : k ⟶ l) :
    eqToHom (innerVariableIndex_obj_last r d k).symm ≫
      ((innerVariableIndex r d).map f) (Fin.last r) ≫
      eqToHom (innerVariableIndex_obj_last r d l) = f

lemma innerVariableIndex_map_castSucc (r : ℕ) (d : Fin r → SimplexCategoryᵒᵖ)
    {k l : SimplexCategoryᵒᵖ} (f : k ⟶ l) (i : Fin r) :
    eqToHom (innerVariableIndex_obj_castSucc r d k i).symm ≫
      ((innerVariableIndex r d).map f) i.castSucc ≫
      eqToHom (innerVariableIndex_obj_castSucc r d l i) = 𝟙 (d i)

def innerVariableSComparisonNatIso (r : ℕ) (d : Fin r → SimplexCategoryᵒᵖ) :
    simplicialStableEndofunctor.{u} ⋙
        (Functor.whiskeringRight StableModel.{u} StableModel.{u} StableModel.{u}).obj
          ((multiSEndofunctor r).obj d) ≅
      innerVariableIndex r d ⋙ multiSEndofunctor (r + 1)

lemma innerVariableIndex_obj_diagonal (r : ℕ) (d : SimplexCategoryᵒᵖ) :
    (innerVariableIndex r (fun _ => d)).obj d = fun _ => d

lemma innerVariableIndex_obj_zero (r : ℕ) (d : SimplexCategoryᵒᵖ) :
    (innerVariableIndex r (fun _ => d)).obj (Opposite.op ⦋0⦌) =
      (zeroDirectionsIndex {Fin.last r}).obj (fun _ => d)

lemma innerVariableIndex_zero_map (r : ℕ) (d : SimplexCategoryᵒᵖ) :
    eqToHom (innerVariableIndex_obj_zero r d).symm ≫
      (innerVariableIndex r (fun _ => d)).map
        (SimplexCategory.const d.unop ⦋0⦌ 0).op ≫
      eqToHom (innerVariableIndex_obj_diagonal r d) =
        (zeroDirectionsIndexNat {Fin.last r}).app (fun _ => d)
```

現在地：L1a・L1b 完了、L1c 継続中。
可変の最内側の次数の座標比較と、最後の零方向の包含との厳密な一致まで証明済み。
既存の全単体的な反復実現の座標同型との照合、およびこれによる全零境界商への点つき比較は未完了。
homotopy fiber と loop の比較、既存の suspension 構造射との照合、正の段の Ω 条件・delooping、
負次数消滅を含む BF 連結スペクトル、スペクトル関手は未完了。
同時商と円の smash の明示的同型、任意の押し出し保存と一般の cofiber 保存条件との同値は未証明。
L1d–f 未完了、L1g は別途指示待ち。Core および他レーンの公開 API に変更なし。

検証：対象ビルド成功（3087 jobs）、公理監査成功（1234 宣言、標準三公理のみ）。追加公理・sorry なし。

### 6.41 最内側の零方向の包含の自然変換の比較

`InnerZeroDirectionComparison.lean`。
§6.40 の可変の内側の次数の同型に添字の等号を合成し、
最内側の S_0 を最後の零方向の自己関手へ移す同型と、対角次数の同型を作った。
両者の下で、最内側の零次数からの作用が既存の最後の零方向の包含そのものに移ることを、
安定な入力の自己関手の自然変換の厳密等号として証明した。

前提：`r n : ℕ` のみ。以下は namespace `SerrePositivity.KST.SConstruction`、`universe u`、
`open CategoryTheory`、`open scoped Simplicial` の下での正確な公開型。

```lean
def innerZeroDirectionComparisonIso (r n : ℕ) :
    sEndofunctor.{u} 0 ⋙ (multiSEndofunctor r).obj (fun _ => Opposite.op ⦋n⦌) ≅
      (multiSEndofunctor (r + 1)).obj
        ((zeroDirectionsIndex {Fin.last r}).obj (fun _ => Opposite.op ⦋n⦌))

def innerDiagonalComparisonIso (r n : ℕ) :
    sEndofunctor.{u} n ⋙ (multiSEndofunctor r).obj (fun _ => Opposite.op ⦋n⦌) ≅
      (multiSEndofunctor (r + 1)).obj (fun _ => Opposite.op ⦋n⦌)

lemma innerZeroDirectionComparisonIso_inclusion (r n : ℕ) :
    Functor.whiskerRight
        (simplicialStableEndofunctor.{u}.map (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0).op)
        ((multiSEndofunctor r).obj (fun _ => Opposite.op ⦋n⦌)) ≫
      (innerDiagonalComparisonIso r n).hom =
        (innerZeroDirectionComparisonIso r n).hom ≫
          (multiSEndofunctor (r + 1)).map
            ((zeroDirectionsIndexNat {Fin.last r}).app (fun _ => Opposite.op ⦋n⦌))
```

現在地：L1a・L1b 完了、L1c 継続中。
零方向の包含の比較は自己関手の自然変換まで証明済み。
既存の `diagonalSInnerComparisonNatIso` の成分と今回の `innerDiagonalComparisonIso` の一致、
実現への移行、全零境界商への点つき比較は未完了。
特に、関手の等号による同型の型の輸送を成分評価の下で処理する補題が必要。
homotopy fiber と loop の比較、既存の suspension 構造射との照合、正の段の Ω 条件・delooping、
負次数消滅を含む BF 連結スペクトル、スペクトル関手は未完了。
同時商と円の smash の明示的同型、任意の押し出し保存と一般の cofiber 保存条件との同値は未証明。
L1d–f 未完了、L1g は別途指示待ち。Core および他レーンの公開 API に変更なし。

検証：対象ビルド成功（3088 jobs）、公理監査成功（1237 宣言、標準三公理のみ）。追加公理・sorry なし。

### 6.42 内側の零列から全零境界商への自然な点つき比較と経路境界

`DiagonalIterationComponents.lean`、`InnerDiagonalComponents.lean`、`InnerZeroColumn.lean`、
`InnerZeroBoundaryComparison.lean`、`InnerZeroBoundaryNaturality.lean`、`PointedFullPathBoundary.lean`。
既存の `diagonalSInnerComparisonNatIso` と、零方向の包含の比較に使う `innerDiagonalComparisonIso` の
各次数の射が厳密に一致することを証明した。双方を固定次数の結合子による同型へ比較する。
このため `DiagonalIterationNaturality.lean` の既存の補助定義は、同じ結合子・単位子・添字の等号を
`eqToIso` で明示的に合成する実装にした。公開名と型は不変であり、構成の設計変更ではない。

内側の零列の各単体に最後の零方向での具体的な原像を構成し、既存の座標同型の像を厳密に回収した。
その像が全零境界に含まれることから実際の単体的持ち上げを構成し、cofiber の普遍性で
`innerZeroToFullBoundaryComparison` を定義した。この比較は全 anodyne 反転関手で可逆であり、
Kan 置換後は全基点・全自然数次数の L9 の π_* 同型となる。
座標同型と商への比較は安定な入力の射について厳密に自然である。

点つき反復経路の既存の境界に比較を合成し、既存の全零境界商を標的とする自然な点つき境界、
およびその Kan 置換を構成した。商射影に戻すと既存の `reducedIteratedPathBoundary`、
商射影と Kan 置換の単位に戻すと `kanIteratedPathBoundary` そのものを厳密に回収する。
Kan な境界の源は既証明の `pointedIteratedPathKan_isContractibleKan r X` により実際に可縮 Kan。
この事実だけから既存の suspension の随伴が π_* 同型だとは結論しない。

前提：`r n : ℕ`、`X Y : StableModel.{u}`、`f : X ⟶ Y`。
入力には `StableModel` に格納された quasicategory 性・安定性のみを使い、追加仮定はない。
一般の像の可逆性の定理は `L : SSet.{u} ⥤ D` と anodyne 反転性を明記する。
以下は namespace `SerrePositivity.KST.SConstruction`、`universe u v w`、
`open CategoryTheory`、`open scoped Simplicial` の下での正確な公開型。

```lean
lemma diagonalSInnerComparisonNatIso_zero_app (d : SimplexCategoryᵒᵖ) (X : StableModel.{u}) :
    ((diagonalSInnerComparisonNatIso 0).hom.app d).app X =
      𝟙 ((sEndofunctor d.unop.len).obj X)

lemma diagonalSInnerComparisonNatIso_succ_app (r : ℕ) (d : SimplexCategoryᵒᵖ)
    (X : StableModel.{u}) :
    ((diagonalSInnerComparisonNatIso (r + 1)).hom.app d).app X =
      (sEndofunctor d.unop.len).map
        (((diagonalSInnerComparisonNatIso r).hom.app d).app X)

lemma diagonalSInnerComparisonNatIso_app_eq (r n : ℕ) :
    (diagonalSInnerComparisonNatIso.{u} r).hom.app (Opposite.op ⦋n⦌) =
      (multiSEndofunctor_diagonal_inner_iso r n).hom

lemma innerDiagonalTransport_succ (r n : ℕ) :
    (multiSEndofunctor.{u} (r + 2)).map
      (eqToHom (innerVariableIndex_obj_diagonal (r + 1) (Opposite.op ⦋n⦌))) =
      Functor.whiskerRight
        ((multiSEndofunctor (r + 1)).map
          (eqToHom (innerVariableIndex_obj_diagonal r (Opposite.op ⦋n⦌))))
        (sEndofunctor n)

lemma innerDiagonalComparisonIso_zero_app (n : ℕ) (X : StableModel.{u}) :
    (innerDiagonalComparisonIso 0 n).hom.app X = 𝟙 ((sEndofunctor n).obj X)

lemma innerDiagonalComparisonIso_succ_app (r n : ℕ) (X : StableModel.{u}) :
    (innerDiagonalComparisonIso (r + 1) n).hom.app X =
      (sEndofunctor n).map ((innerDiagonalComparisonIso r n).hom.app X)

lemma innerDiagonalComparisonIso_hom_eq (r n : ℕ) :
    (innerDiagonalComparisonIso.{u} r n).hom =
      (multiSEndofunctor_diagonal_inner_iso r n).hom

lemma diagonalSInnerComparisonNatIso_app_eq_inner (r n : ℕ) :
    (diagonalSInnerComparisonNatIso.{u} r).hom.app (Opposite.op ⦋n⦌) =
      (innerDiagonalComparisonIso r n).hom

def iteratedZeroColumnLastZeroPreimage (r : ℕ) (X : StableModel.{u}) (n : ℕ) :
    ((iteratedSRealizationDiagram r X).obj (Opposite.op ⦋0⦌)).obj (Opposite.op ⦋n⦌) →
      (simplicialDiagonalFunctor.obj (zeroDirectionsDiagram {Fin.last r} X)).obj
        (Opposite.op ⦋n⦌)

lemma iteratedZeroColumnLastZeroPreimage_fac (r : ℕ) (X : StableModel.{u}) (n : ℕ)
    (x : ((iteratedSRealizationDiagram r X).obj (Opposite.op ⦋0⦌)).obj (Opposite.op ⦋n⦌)) :
    ((zeroDirectionsInclusion {Fin.last r} X).app (Opposite.op ⦋n⦌))
        (iteratedZeroColumnLastZeroPreimage r X n x) =
      ((diagonalZeroColumn (iteratedSRealizationDiagram r X) ≫
        (iteratedSRealizationCoordinateIso r X).hom).app (Opposite.op ⦋n⦌)) x

lemma iteratedZeroColumn_range_le_fatBoundary (r : ℕ) (X : StableModel.{u}) :
    Subcomplex.range (diagonalZeroColumn (iteratedSRealizationDiagram r X) ≫
      (iteratedSRealizationCoordinateIso r X).hom) ≤ zeroDirectionsFatBoundary (r + 1) X

def iteratedZeroColumnFatBoundaryLift (r : ℕ) (X : StableModel.{u}) :
    (iteratedSRealizationDiagram r X).obj (Opposite.op ⦋0⦌) ⟶
      (zeroDirectionsFatBoundary (r + 1) X : SSet.{u})

lemma iteratedZeroColumnFatBoundaryLift_ι (r : ℕ) (X : StableModel.{u}) :
    iteratedZeroColumnFatBoundaryLift r X ≫ (zeroDirectionsFatBoundary (r + 1) X).ι =
      diagonalZeroColumn (iteratedSRealizationDiagram r X) ≫
        (iteratedSRealizationCoordinateIso r X).hom

def innerZeroToFullBoundaryComparison (r : ℕ) (X : StableModel.{u}) :
    reducedDiagonal (iteratedSRealizationDiagram r X) ⟶ boundaryReducedRealization r X

lemma innerZeroToFullBoundaryComparison_quotient (r : ℕ) (X : StableModel.{u}) :
    diagonalReductionQuotient (iteratedSRealizationDiagram r X) ≫
      (innerZeroToFullBoundaryComparison r X).right =
        (iteratedSRealizationCoordinateIso r X).hom ≫ boundaryReductionQuotient r X

lemma innerZeroToFullBoundaryComparison_image_isIso {D : Type v} [Category.{w} D]
    (L : SSet.{u} ⥤ D) (hL : anodyneExtensions.IsInvertedBy L) (r : ℕ) (X : StableModel.{u}) :
    IsIso (L.map (innerZeroToFullBoundaryComparison r X).right)

lemma iteratedSRealizationCoordinateIso_naturality (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    iteratedSRealizationMap r f ≫ (iteratedSRealizationCoordinateIso r Y).hom =
      (iteratedSRealizationCoordinateIso r X).hom ≫ (multiRealizationFunctor (r + 1)).map f

lemma innerZeroToFullBoundaryComparison_naturality (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    reducedDiagonalMap (iteratedSRealizationDiagramMap r f) ≫ innerZeroToFullBoundaryComparison r Y =
      innerZeroToFullBoundaryComparison r X ≫ boundaryReducedRealizationMap r f

def innerZeroToFullBoundaryComparisonNat (r : ℕ) :
    iteratedSRealizationDiagramFunctor.{u} r ⋙ reducedDiagonalFunctor ⟶
      boundaryReducedRealizationFunctor r where
  app

def innerZeroToFullBoundaryComparisonKanNat (r : ℕ) :
    (iteratedSRealizationDiagramFunctor.{u} r ⋙ reducedDiagonalFunctor) ⋙
        Spectra.PointedKanReplacement.functor ⟶ boundaryKanRealizationFunctor r

lemma innerZeroToFullBoundaryComparisonKan_piIsomorphism (r : ℕ) (X : StableModel.{u}) :
    Spectra.KanPiIsomorphism
      (Spectra.PointedKanReplacement.map (innerZeroToFullBoundaryComparison r X)).right

def pointedFullIteratedPathBoundaryNat (r : ℕ) :
    pointedIteratedPathFunctor.{u} r ⟶ boundaryReducedRealizationFunctor r

def pointedFullIteratedPathBoundary (r : ℕ) (X : StableModel.{u}) :
    pointedIteratedPathRealization r X ⟶ boundaryReducedRealization r X

lemma pointedFullIteratedPathBoundary_quotient (r : ℕ) (X : StableModel.{u}) :
    pointedIteratedPathQuotient r X ≫ (pointedFullIteratedPathBoundary r X).right =
      reducedIteratedPathBoundary r X

def pointedFullIteratedPathKanBoundaryNat (r : ℕ) :
    pointedIteratedPathKanFunctor.{u} r ⟶ boundaryKanRealizationFunctor r

def pointedFullIteratedPathKanBoundary (r : ℕ) (X : StableModel.{u}) :
    (pointedIteratedPathKanFunctor r).obj X ⟶ (boundaryKanRealizationFunctor r).obj X

lemma pointedFullIteratedPathKanBoundary_quotient (r : ℕ) (X : StableModel.{u}) :
    pointedIteratedPathQuotient r X ≫
      (Spectra.PointedKanReplacement.unit.app (pointedIteratedPathRealization r X)).right ≫
      (pointedFullIteratedPathKanBoundary r X).right = kanIteratedPathBoundary r X
```

現在地：L1a・L1b 完了、L1c 継続中。
既存の全単体的な座標同型との照合、内側の零列から全零境界商への自然な点つき比較とその弱同値性、
可縮 Kan な反復経路から既存の Kan な全零境界商への自然な点つき境界と元の境界の回収まで証明済み。
homotopy fiber と loop の比較、実際の fiber と反復 S の実現の比較、
既存の suspension 構造射との照合、正の段の Ω 条件・delooping、
負次数消滅を含む BF 連結スペクトル、スペクトル関手は未完了。
同時商と円の smash の明示的同型、任意の押し出し保存と一般の cofiber 保存条件との同値は未証明。
L1d–f 未完了、L1g は別途指示待ち。Core および他レーンの公開 API に変更なし。

検証：対象ビルド成功（3094 jobs）、公理監査成功（1264 宣言、標準三公理のみ）。追加公理・sorry なし。

### 6.43 反復経路境界の path homotopy fiber と loop の自然な比較

`FiberOverContractibleBase.lean`、`PointedPullbackFiber.lean`、`LoopHomotopyFiber.lean`、
`PathHomotopyFiberNaturality.lean`、`PathHomotopyFiberFunctor.lean`、`IteratedPathHomotopyFiber.lean`。

一般の Kan fibration の底が可縮 Kan なら、その基点上の fiber の包含が全基点 π_* 同型であることを証明した。
証明は全空間の恒等射と底から終対象への射による四角形に、L9 の既存の fiber 比較定理を適用する。
点つき引き戻しの第二射影の基点 fiber と元の射の基点 fiber との厳密な同型も証明した。

点つき射 `f : E ⟶ B` に対して、L9 の `pathEndpoint B : basedPathSpace B ⟶ B` を f に沿って
引き戻した `pathHomotopyFiber f` を定義した。path は時刻零に B の基点から出て、時刻一に f(e) へ至る。
これはこの path による homotopy fiber 模型であり、L9 の mapping path の別の表示との厳密な一致は主張しない。
元の射 f 自体の fibration 性は要求しない。E と B が Kan ならこの引き戻しも Kan である。
L9 の `loopBasedPathFiberIso` の基点保存により点つき同型を作り、引き戻しの基点 fiber を経由して
`loopToPathHomotopyFiber f : loopSpace B ⟶ pathHomotopyFiber f` を構成した。
E が可縮 Kan なら、この実際の写像は全基点・全自然数次数の π_* 同型となる。
この写像は収縮や nullhomotopy の選択を含まず、点つき射の可換正方形について厳密に自然。
可換正方形の恒等・合成法則も証明し、一般の自然変換の fiber と loop 比較を厳密な関手・自然変換へ束ねた。

既存の `pointedFullIteratedPathKanBoundary r X` に適用し、安定な入力についての関手
`iteratedPathHomotopyFiberFunctor r` と自然な `iteratedPathLoopComparisonNat r` を構成した。
経路全空間の既証明の可縮 Kan 性により、その全成分は追加仮定なしで全基点 π_* 同型である。
ここで `B_r X := (boundaryKanRealizationFunctor r).obj X` と書くと、この比較の型は
`Ω B_r X ⟶ iteratedPathHomotopyFiber r X`。
正の段の Ω 条件 `B_r X ⟶ Ω B_(r+1) X` には、さらに
`B_r X` と `iteratedPathHomotopyFiber (r+1) X` との比較と、既存の suspension の随伴との照合が必要である。
零回の反復について `core X ≃ Ω B_0 X` とは主張しない。

前提：一般の fiber 包含の定理は Kan な E・B、Kan fibration p、底の可縮 Kan 性を明記する。
一般の loop 比較は Kan な E・B と E の可縮 Kan 性のみ。反復経路への適用には
`X : StableModel.{u}` 以外の追加仮定はない。自然変換の関手化では入力の圏を
`C : Type v`、`Category.{w} C` として対象と Hom の宇宙を分ける。
以下は namespace `SerrePositivity.KST.SConstruction`、`universe u v w`、
`open CategoryTheory Limits HomotopicalAlgebra SSet`、`open Spectra`、
`open SerrePositivity.InfinityCategories SerrePositivity.SimplicialModel`、
`open SSet.modelCategoryQuillen`、`open scoped Simplicial` の下での正確な公開型。

```lean
lemma fiberTerminalInclusion_isIso (E : SSet.{u}) (e : E _⦋0⦌) :
    IsIso (fiberι (terminal.from E) ((terminal.from E).app _ e))

lemma fiberInclusion_piIsomorphism_of_contractible_base {E B : SSet.{u}}
    [KanComplex E] [KanComplex B] (p : E ⟶ B) [Fibration p]
    (hB : IsContractibleKan B) (e : E _⦋0⦌) :
    KanPiIsomorphism (fiberι p (p.app _ e))

def pointedPullbackFiberTo {E A B : PointedSimplicialSet.{u}} (p : E ⟶ B) (g : A ⟶ B) :
    pointedFiber (pullback.snd p g) ⟶ pointedFiber p

lemma pointedPullbackFiberTo_ι {E A B : PointedSimplicialSet.{u}} (p : E ⟶ B) (g : A ⟶ B) :
    pointedPullbackFiberTo p g ≫ pointedFiberι p =
      pointedFiberι (pullback.snd p g) ≫ pullback.fst p g

def pointedPullbackFiberFrom {E A B : PointedSimplicialSet.{u}} (p : E ⟶ B) (g : A ⟶ B) :
    pointedFiber p ⟶ pointedFiber (pullback.snd p g)

lemma pointedPullbackFiberFrom_ι {E A B : PointedSimplicialSet.{u}} (p : E ⟶ B) (g : A ⟶ B) :
    pointedPullbackFiberFrom p g ≫ pointedFiberι (pullback.snd p g) =
      pullback.lift (pointedFiberι p) 0 (by simp)

def pointedPullbackFiberIso {E A B : PointedSimplicialSet.{u}} (p : E ⟶ B) (g : A ⟶ B) :
    pointedFiber (pullback.snd p g) ≅ pointedFiber p where
  hom

def pathHomotopyFiber {E B : PointedSimplicialSet.{u}} (f : E ⟶ B) :
    PointedSimplicialSet.{u}

def pathHomotopyFiberProjection {E B : PointedSimplicialSet.{u}} (f : E ⟶ B) :
    pathHomotopyFiber f ⟶ E

instance pathHomotopyFiberProjection_fibration {E B : PointedSimplicialSet.{u}}
    (f : E ⟶ B) [KanComplex B.right] : Fibration (pathHomotopyFiberProjection f).right

instance pathHomotopyFiber_kanComplex {E B : PointedSimplicialSet.{u}}
    (f : E ⟶ B) [KanComplex E.right] [KanComplex B.right] :
    KanComplex (pathHomotopyFiber f).right

def loopPointedPathFiberIso (B : PointedSimplicialSet.{u}) :
    loopSpace B ≅ pointedFiber (pathEndpoint B)

def loopToPathHomotopyFiber {E B : PointedSimplicialSet.{u}} (f : E ⟶ B) :
    loopSpace B ⟶ pathHomotopyFiber f

lemma loopToPathHomotopyFiber_projection {E B : PointedSimplicialSet.{u}} (f : E ⟶ B) :
    loopToPathHomotopyFiber f ≫ pathHomotopyFiberProjection f = 0

lemma loopToPathHomotopyFiber_piIsomorphism {E B : PointedSimplicialSet.{u}}
    (f : E ⟶ B) [KanComplex E.right] [KanComplex B.right] (hE : IsContractibleKan E.right) :
    KanPiIsomorphism (loopToPathHomotopyFiber f).right

lemma loopPointedPathFiberIso_hom_ι (B : PointedSimplicialSet.{u}) :
    (loopPointedPathFiberIso B).hom ≫ pointedFiberι (pathEndpoint B) =
      (loopToEndpointHomIso B).hom ≫
        PointedMapping.prePointed (pointedCofiberProjection intervalEndpoint.{u}) B

lemma loopToPathHomotopyFiber_path {E B : PointedSimplicialSet.{u}} (f : E ⟶ B) :
    loopToPathHomotopyFiber f ≫ pullback.fst (pathEndpoint B) f =
      (loopToEndpointHomIso B).hom ≫
        PointedMapping.prePointed (pointedCofiberProjection intervalEndpoint.{u}) B

def pathHomotopyFiberMap {E B E' B' : PointedSimplicialSet.{u}}
    (f : E ⟶ B) (f' : E' ⟶ B') (a : E ⟶ E') (b : B ⟶ B') (h : f ≫ b = a ≫ f') :
    pathHomotopyFiber f ⟶ pathHomotopyFiber f'

lemma pathHomotopyFiberMap_path {E B E' B' : PointedSimplicialSet.{u}}
    (f : E ⟶ B) (f' : E' ⟶ B') (a : E ⟶ E') (b : B ⟶ B') (h : f ≫ b = a ≫ f') :
    pathHomotopyFiberMap f f' a b h ≫ pullback.fst (pathEndpoint B') f' =
      pullback.fst (pathEndpoint B) f ≫ basedPathMap b

lemma pathHomotopyFiberMap_projection {E B E' B' : PointedSimplicialSet.{u}}
    (f : E ⟶ B) (f' : E' ⟶ B') (a : E ⟶ E') (b : B ⟶ B') (h : f ≫ b = a ≫ f') :
    pathHomotopyFiberMap f f' a b h ≫ pathHomotopyFiberProjection f' =
      pathHomotopyFiberProjection f ≫ a

lemma loopToPathHomotopyFiber_naturality {E B E' B' : PointedSimplicialSet.{u}}
    (f : E ⟶ B) (f' : E' ⟶ B') (a : E ⟶ E') (b : B ⟶ B') (h : f ≫ b = a ≫ f') :
    loopToPathHomotopyFiber f ≫ pathHomotopyFiberMap f f' a b h =
      PointedObject.basedHomMap PointedSimplicialSet.circle.{u} b ≫ loopToPathHomotopyFiber f'

lemma pathHomotopyFiberMap_id {E B : PointedSimplicialSet.{u}} (f : E ⟶ B)
    (h : f ≫ 𝟙 B = 𝟙 E ≫ f) :
    pathHomotopyFiberMap f f (𝟙 E) (𝟙 B) h = 𝟙 (pathHomotopyFiber f)

lemma pathHomotopyFiberMap_comp {E B E' B' E'' B'' : PointedSimplicialSet.{u}}
    (f : E ⟶ B) (f' : E' ⟶ B') (f'' : E'' ⟶ B'')
    (a : E ⟶ E') (b : B ⟶ B') (h : f ≫ b = a ≫ f')
    (a' : E' ⟶ E'') (b' : B' ⟶ B'') (h' : f' ≫ b' = a' ≫ f'')
    (h'' : f ≫ (b ≫ b') = (a ≫ a') ≫ f'') :
    pathHomotopyFiberMap f f' a b h ≫ pathHomotopyFiberMap f' f'' a' b' h' =
      pathHomotopyFiberMap f f'' (a ≫ a') (b ≫ b') h''

def pathHomotopyFiberFunctorOfNat {C : Type v} [Category.{w} C]
    {F G : C ⥤ PointedSimplicialSet.{u}} (α : F ⟶ G) : C ⥤ PointedSimplicialSet.{u} where
  obj X

def loopToPathHomotopyFiberNat {C : Type v} [Category.{w} C]
    {F G : C ⥤ PointedSimplicialSet.{u}} (α : F ⟶ G) :
    G ⋙ PointedObject.basedHomFunctor PointedSimplicialSet.circle ⟶
      pathHomotopyFiberFunctorOfNat α where
  app X

def iteratedPathHomotopyFiber (r : ℕ) (X : StableModel.{u}) : PointedSimplicialSet.{u}

instance iteratedPathHomotopyFiber_kanComplex (r : ℕ) (X : StableModel.{u}) :
    KanComplex (iteratedPathHomotopyFiber r X).right

def iteratedPathHomotopyFiberMap (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    iteratedPathHomotopyFiber r X ⟶ iteratedPathHomotopyFiber r Y

def iteratedPathHomotopyFiberFunctor (r : ℕ) : StableModel.{u} ⥤ PointedSimplicialSet.{u}

def iteratedPathLoopComparison (r : ℕ) (X : StableModel.{u}) :
    loopSpace ((boundaryKanRealizationFunctor r).obj X) ⟶ iteratedPathHomotopyFiber r X

lemma iteratedPathLoopComparison_piIsomorphism (r : ℕ) (X : StableModel.{u}) :
    KanPiIsomorphism (iteratedPathLoopComparison r X).right

def iteratedPathLoopComparisonNat (r : ℕ) :
    boundaryKanRealizationFunctor.{u} r ⋙
      PointedObject.basedHomFunctor PointedSimplicialSet.circle ⟶
      iteratedPathHomotopyFiberFunctor r
```

現在地：L1a・L1b 完了、L1c 継続中。
可縮 Kan な反復経路境界の path homotopy fiber、標的の loop からの自然な比較、
その全基点・全自然数次数の π_* 同型まで証明済み。
反復 S の実現と実際の homotopy fiber との比較、既存の suspension 構造射との照合、
正の段の Ω 条件・delooping、負次数消滅を含む BF 連結スペクトル、スペクトル関手は未完了。
L9 の mapping path による fiber 模型との比較は未証明。
同時商と円の smash の明示的同型、任意の押し出し保存と一般の cofiber 保存条件との同値は未証明。
L1d–f 未完了、L1g は別途指示待ち。Core および他レーンの公開 API に変更なし。

検証：対象ビルド成功（3109 jobs）、公理監査成功（1296 宣言、標準三公理のみ）。追加公理・sorry なし。

### 6.44 正の Ω 条件の加法性による fiber 比較の準備

§6.43 の比較だけでは反復 S 実現と fiber の比較は得られない。
L2 の `segalRealization_homotopyPullback` は各面の自然性のホモトピー引き戻し性を要求するため、
この入力を追加仮定にはせず、加法性の補題で供給する。
L1c の Ω 条件に必要な補題を、既に §4 に記録した McCarthy 法に沿って実装する。
L1d の加法性全体を完成扱いしない。原典は L11 §11 と Fiore–Pieper 著者公開版
<https://www-personal.umd.umich.edu/~tmfiore/1/FiorePieperQCatAddNONHouse12.pdf> の
Lemma 4.24、Proposition 4.27、Theorem 4.35、Corollary 3.35。

文言と方針：全 gapped 図式の S_n を維持し、その零単体から object 単体集合 s•C を作る。
core が全ての頂点を含むことから object と core の零単体を同定し、
内部の零単体を退化させて core の対角への実際の比較射を作る。
この比較の弱同値性は Proposition 4.27 に対応する別の証明項目であり定義に含めない。
cofiber 列の模型は S₂C とし、面 δ₂・δ₁・δ₀ と S₁ の既存の比較による
subobject・middle・quotient の完全関手を使う。
これに s• と core 実現を施した (subobject, quotient) の射が McCarthy 法で証明すべき対象。
S₂C と C×C の ∞ 圏としての同値を主張しない。
coherent pushout の相対充填、単体積 Quillen A、object/core の弱同値比較、
面のホモトピー引き戻し条件、既存の構造射との照合はこれから証明する。

実装済み：`DiagonalObjects.lean`、`ObjectSConstruction.lean`、`STwoAdditivityComparison.lean`。
任意の二重単体集合について、各行の内部零単体から対角への定数退化による射と、その厳密な自然性を証明した。
任意の単体集合の頂点と core の頂点の同定を自然同型に束ね、二重単体集合の各行に適用した。
全 gapped S_n の零単体を n 単体とする `objectSConstruction C`、core の対角への比較、
S 図式の射についての厳密な自然性を構成した。安定な入力についての object S 関手も定義した。
S₂ の δ₂・δ₁・δ₀ と既存の S₁ 比較を合成した subobject・middle・quotient は、
cofiber 保存条件を持つ `StableModel` の射であり、入力について厳密に自然。
任意の空間値関手 F に対して `(F(subobject), F(quotient))` を積へ束ねる自然変換を構成した。
積は `SSet` の cartesian tensor を使う。二つの射影の回収式を証明し、
F に object S と一回の core S 実現を代入した加法性の比較射を定義した。

前提：object/core の比較射自体は `C : SSet.{u}` に quasicategory 性を要求しない。
S₂ の三つの完全関手および加法性の比較は `X : StableModel.{u}` とその射を入力とする。
一般の加法性比較の `F : StableModel.{u} ⥤ SSet.{u}` に追加仮定はない。
以下は namespace `SerrePositivity.KST.SConstruction`、`universe u`、
`open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet`、
`open SerrePositivity.InfinityCategories`、`open scoped Simplicial` の下での正確な公開型。

```lean
def diagonalObjects (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) : SSet.{u}

def diagonalObjectInclusion (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    diagonalObjects X ⟶ simplicialDiagonalFunctor.obj X where
  app d

def diagonalObjectInclusionNat :
    (Functor.whiskeringRight SimplexCategoryᵒᵖ SSet.{u} (Type u)).obj
        ((evaluation SimplexCategoryᵒᵖ (Type u)).obj (Opposite.op ⦋0⦌)) ⟶
      simplicialDiagonalFunctor where
  app

def objectSConstruction (C : SSet.{u}) : SSet.{u}

lemma objectSConstruction_obj (C : SSet.{u}) (n : ℕ) :
    (objectSConstruction C).obj (Opposite.op ⦋n⦌) =
      (sConstruction n C).obj (Opposite.op ⦋0⦌)

def coreVertexNatIso :
    (evaluation SimplexCategoryᵒᵖ (Type u)).obj (Opposite.op ⦋0⦌) ≅
      quasicategoryCoreFunctor ⋙
        (evaluation SimplexCategoryᵒᵖ (Type u)).obj (Opposite.op ⦋0⦌)

def coreDiagramObjectsIso :
    (Functor.whiskeringRight SimplexCategoryᵒᵖ SSet.{u} (Type u)).obj
        ((evaluation SimplexCategoryᵒᵖ (Type u)).obj (Opposite.op ⦋0⦌)) ≅
      (Functor.whiskeringRight SimplexCategoryᵒᵖ SSet.{u} SSet.{u}).obj
        quasicategoryCoreFunctor ⋙
      (Functor.whiskeringRight SimplexCategoryᵒᵖ SSet.{u} (Type u)).obj
        ((evaluation SimplexCategoryᵒᵖ (Type u)).obj (Opposite.op ⦋0⦌))

def objectCoreDiagonalComparisonNat :
    (Functor.whiskeringRight SimplexCategoryᵒᵖ SSet.{u} (Type u)).obj
        ((evaluation SimplexCategoryᵒᵖ (Type u)).obj (Opposite.op ⦋0⦌)) ⟶
      (Functor.whiskeringRight SimplexCategoryᵒᵖ SSet.{u} SSet.{u}).obj
        quasicategoryCoreFunctor ⋙ simplicialDiagonalFunctor

def objectSCoreVertexIso (C : SSet.{u}) :
    objectSConstruction C ≅ diagonalObjects (simplicialCoreSConstruction C)

def objectToCoreSRealization (C : SSet.{u}) :
    objectSConstruction C ⟶ simplicialDiagonalFunctor.obj (simplicialCoreSConstruction C)

lemma objectToCoreSRealization_eq (C : SSet.{u}) :
    objectToCoreSRealization C =
      objectCoreDiagonalComparisonNat.app (simplicialSConstruction C)

lemma objectToCoreSRealization_naturality {C D : SSet.{u}}
    (f : simplicialSConstruction C ⟶ simplicialSConstruction D) :
    Functor.whiskerRight f
        ((evaluation SimplexCategoryᵒᵖ (Type u)).obj (Opposite.op ⦋0⦌)) ≫
      objectToCoreSRealization D =
        objectToCoreSRealization C ≫
          simplicialDiagonalFunctor.map (Functor.whiskerRight f quasicategoryCoreFunctor)

def objectSConstructionFunctor : StableModel.{u} ⥤ SSet.{u}

lemma objectSConstructionFunctor_obj (X : StableModel.{u}) :
    objectSConstructionFunctor.obj X = objectSConstruction X.carrier

def sTwoFaceComparisonNat (i : Fin 3) : sEndofunctor.{u} 2 ⟶ 𝟭 StableModel.{u}

def sTwoSubobject (X : StableModel.{u}) : (sEndofunctor 2).obj X ⟶ X

def sTwoMiddle (X : StableModel.{u}) : (sEndofunctor 2).obj X ⟶ X

def sTwoQuotient (X : StableModel.{u}) : (sEndofunctor 2).obj X ⟶ X

def sTwoAdditivityComparisonNat (F : StableModel.{u} ⥤ SSet.{u}) :
    sEndofunctor 2 ⋙ F ⟶ F ⊗ F where
  app X

lemma sTwoAdditivityComparisonNat_fst (F : StableModel.{u} ⥤ SSet.{u}) (X : StableModel.{u}) :
    (sTwoAdditivityComparisonNat F).app X ≫ fst (F.obj X) (F.obj X) =
      F.map (sTwoSubobject X)

lemma sTwoAdditivityComparisonNat_snd (F : StableModel.{u} ⥤ SSet.{u}) (X : StableModel.{u}) :
    (sTwoAdditivityComparisonNat F).app X ≫ snd (F.obj X) (F.obj X) =
      F.map (sTwoQuotient X)

def objectSAdditivityComparisonNat :
    sEndofunctor.{u} 2 ⋙ objectSConstructionFunctor ⟶
      objectSConstructionFunctor ⊗ objectSConstructionFunctor

def coreSAdditivityComparisonNat :
    sEndofunctor.{u} 2 ⋙ multiRealizationFunctor 1 ⟶
      multiRealizationFunctor 1 ⊗ multiRealizationFunctor 1
```

現在地：L1a・L1b 完了、L1c 継続中。
正の Ω 条件に必要な加法性補題の object 単体集合、object/core の自然な比較射、
S₂ の完全な三つの評価と object・core 実現での加法性の具体的な比較射まで構成済み。
coherent pushout を用いる McCarthy の単体ホモトピー、単体積 Quillen A、object/core 比較の弱同値性、
加法性の比較射の弱同値性、面のホモトピー引き戻し条件は未証明。
McCarthy の一般の pushout の選択には、安定性から任意 span の pushout の存在と、
cofiber 保存から任意の pushout の保存を導く補題も必要であり、追加仮定では済ませない。
反復 S 実現と §6.43 の homotopy fiber の比較、既存の構造射との照合、
正の段の Ω 条件・delooping、負次数消滅を含む BF 連結スペクトル、スペクトル関手は未完了。
L1d–f 未完了、L1g は別途指示待ち。Core および他レーンの公開 API に変更なし。

検証：対象ビルド成功（3112 jobs）、公理監査成功（1319 宣言、標準三公理のみ）。追加公理・sorry なし。

### 6.45 安定性からの全 span の押し出し・関手的な選択・完全関手による保存

§6.44 の McCarthy 法に必要な二つの存在・保存補題を追加仮定なしで証明した。
安定性の最小の公理から任意の指定 span の押し出しを構成し、
零対象と cofiber を保つ射は任意の押し出しも保つことを示した。
源は安定な quasicategory、保存の標的は quasicategory のみでよく、標的の安定性は不要。
既存の `PreservesCofiberData`・`PreservesSConstructionData`・`StableModel` の定義・型は変更していない。

任意 span の押し出しは、一方の枝の fiber 四角形の右側に他方の枝を貼り、
零角を持つ左四角形と外側の長方形が cofiber となる表示で得た。
この表示と押し出し貼り合わせの消去により保存を証明し、
元の押し出しには同じ span 上の関手同型で輸送した。
点ごとの余極限の存在も供給し、任意の四角形について gapped 包含の押し出しの保存・反映を得た。
零角を仮定した以前の判定のみに依存する結論ではない。

押し出し図式から span の内部 Hom への射影が trivial Kan fibration であることを証明した。
全 span 上の厳密な単体的切断と、任意の単射で指定した部分を保持する切断の延長を構成した。
任意パラメーターに対する選択空間は可縮 Kan であり、同じ入力の二つの族の関手同型を得た。
完全関手で移した選択と、移した span に選んだ押し出しの族との関手同型も構成済み。
切断は単体的なので退化した恒等射を保つが、指定した恒等 span 上での対象の厳密な正規化は
まだ実装していない。相対切断の延長だけで正規化まで完成したとは数えない。

追加ファイル：`StableSpanPushout.lean`、`StablePushoutFamilies.lean`、
`CofiberPreservesPushout.lean`、`GappedPushoutPreservation.lean`、`StablePushoutPostcomp.lean`。
以下は namespace `SerrePositivity.KST.SConstruction` 内の公開宣言の正確な型。
`Quasicategory`・`IsStable` 等は既存の定義を用いる。

```lean
lemma exists_stable_pushoutPresentation_of_span {X : SSet.{u}} [Quasicategory X] [IsStable X]
    (p : (horn 2 0 : SSet.{u}) ⟶ X) :
    ∃ F : (Δ[2] ⊗ Δ[1] : SSet.{u}) ⟶ X,
      pushoutSpan (pastingSquare F 0) = p ∧
      IsZeroVertex (squareVertex (pastingSquare F 2) 0 1) ∧
      IsPushoutSquare (pastingSquare F 2) ∧ IsPushoutSquare (pastingSquare F 0) ∧
      IsPushoutSquare (pastingSquare F 1)

lemma exists_stable_pushoutSquare_of_span {X : SSet.{u}} [Quasicategory X] [IsStable X]
    (p : (horn 2 0 : SSet.{u}) ⟶ X) :
    ∃ R : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X, pushoutSpan R = p ∧ IsPushoutSquare R

lemma stable_hasColimit_span {X : SSet.{u}} [Quasicategory X] [IsStable X]
    (p : (horn 2 0 : SSet.{u}) ⟶ X) : HasColimit p

instance stable_pushoutProjection_trivialKanFibration (C : SSet.{u})
    [Quasicategory C] [IsStable C] :
    TrivialKanFibration (pushoutProjection C)

lemma exists_relative_stable_pushoutFamily {A B C : SSet.{u}} [Quasicategory C] [IsStable C]
    (i : A ⟶ B) [Mono i] (d : B ⟶ (ihom (horn 2 0 : SSet.{u})).obj C)
    (a : A ⟶ pushoutDiagrams C) (ha : a ≫ pushoutProjection C = i ≫ d) :
    ∃ F : B ⟶ pushoutDiagrams C, i ≫ F = a ∧ F ≫ pushoutProjection C = d

lemma exists_stablePushoutSection_extending {A C : SSet.{u}} [Quasicategory C] [IsStable C]
    (i : A ⟶ (ihom (horn 2 0 : SSet.{u})).obj C) [Mono i]
    (a : A ⟶ pushoutDiagrams C) (ha : a ≫ pushoutProjection C = i) :
    ∃ s : (ihom (horn 2 0 : SSet.{u})).obj C ⟶ pushoutDiagrams C,
      i ≫ s = a ∧ s ≫ pushoutProjection C = 𝟙 _

def stablePushoutFamilySpace {A C : SSet.{u}}
    (d : A ⟶ (ihom (horn 2 0 : SSet.{u})).obj C) : SSet.{u}

lemma stablePushoutFamilySpace_isContractibleKan {A C : SSet.{u}} [Quasicategory C] [IsStable C]
    (d : A ⟶ (ihom (horn 2 0 : SSet.{u})).obj C) :
    IsContractibleKan (stablePushoutFamilySpace d)

def stablePushoutFamiliesIso {A C : SSet.{u}} [Quasicategory C] [IsStable C]
    (d : A ⟶ (ihom (horn 2 0 : SSet.{u})).obj C) (F G : A ⟶ pushoutDiagrams C)
    (hF : F ≫ pushoutProjection C = d) (hG : G ≫ pushoutProjection C = d) : FunctorIso F G

def stablePushoutSection (C : SSet.{u}) [Quasicategory C] [IsStable C] :
    (ihom (horn 2 0 : SSet.{u})).obj C ⟶ pushoutDiagrams C

lemma stablePushoutSection_projection (C : SSet.{u}) [Quasicategory C] [IsStable C] :
    stablePushoutSection C ≫ pushoutProjection C = 𝟙 _

def stablePushoutFunctor (C : SSet.{u}) [Quasicategory C] [IsStable C] :
    (ihom (horn 2 0 : SSet.{u})).obj C ⟶ C

lemma PreservesCofiberData.isPushoutSquare {C D : SSet.{u}} [Quasicategory C] [IsStable C]
    [Quasicategory D] {f : C ⟶ D} (hf : PreservesCofiberData f)
    (R : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ C) (hR : IsPushoutSquare R) :
    IsPushoutSquare (R ≫ f)

lemma PreservesCofiberData.toSConstructionData {C D : SSet.{u}} [Quasicategory C] [IsStable C]
    [Quasicategory D] {f : C ⟶ D} (hf : PreservesCofiberData f) : PreservesSConstructionData f

lemma preservesSConstructionData_iff_cofiberData {C D : SSet.{u}} [Quasicategory C] [IsStable C]
    [Quasicategory D] (f : C ⟶ D) : PreservesSConstructionData f ↔ PreservesCofiberData f

lemma stableModelHom_preservesSConstructionData {X Y : StableModel.{u}} (f : X ⟶ Y) :
    PreservesSConstructionData f.val

lemma functor_span_hasPointwiseColimits {A C : SSet.{u}} [Quasicategory C] [IsStable C]
    (p : (horn 2 0 : SSet.{u}) ⟶ (ihom A).obj C) : HasPointwiseColimits p

lemma functor_pushout_iff_pointwise {A C : SSet.{u}} [Quasicategory C] [IsStable C]
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ (ihom A).obj C) :
    IsPushoutSquare F ↔ ∀ a : A _⦋0⦌, IsPushoutSquare (F ≫ evaluateFunctorAt a)

lemma gappedInclusion_pushout_iff {n : ℕ} {C : SSet.{u}} [Quasicategory C] [IsStable C]
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ sConstruction n C) :
    IsPushoutSquare F ↔ IsPushoutSquare (F ≫ (gappedSubcomplex n C).ι)

lemma gappedInclusion_preservesSConstructionData (n : ℕ) (C : SSet.{u})
    [Quasicategory C] [IsStable C] : PreservesSConstructionData (gappedSubcomplex n C).ι

lemma gappedInclusion_pushout_iff_pointwise {n : ℕ} {C : SSet.{u}}
    [Quasicategory C] [IsStable C]
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ sConstruction n C) :
    IsPushoutSquare F ↔ ∀ a : (arNerve n) _⦋0⦌,
      IsPushoutSquare (F ≫ (gappedSubcomplex n C).ι ≫ evaluateFunctorAt a)

def pushoutDiagramsPostcomp {C D : SSet.{u}} (f : C ⟶ D) (hf : PreservesSConstructionData f) :
    pushoutDiagrams C ⟶ pushoutDiagrams D

lemma pushoutDiagramsPostcomp_ι {C D : SSet.{u}} (f : C ⟶ D)
    (hf : PreservesSConstructionData f) :
    pushoutDiagramsPostcomp f hf ≫ (fullSubcomplexOnVertices _ IsPushoutDiagramVertex).ι =
      (fullSubcomplexOnVertices _ IsPushoutDiagramVertex).ι ≫ (ihom (Δ[1] ⊗ Δ[1])).map f

lemma pushoutDiagramsPostcomp_projection {C D : SSet.{u}} (f : C ⟶ D)
    (hf : PreservesSConstructionData f) :
    pushoutDiagramsPostcomp f hf ≫ pushoutProjection D =
      pushoutProjection C ≫ (ihom (horn 2 0 : SSet.{u})).map f

def stablePushoutSection_postcompIso {C D : SSet.{u}} [Quasicategory C] [IsStable C]
    [Quasicategory D] [IsStable D] (f : C ⟶ D) (hf : PreservesCofiberData f) :
    FunctorIso (stablePushoutSection C ≫ pushoutDiagramsPostcomp f hf.toSConstructionData)
      ((ihom (horn 2 0 : SSet.{u})).map f ≫ stablePushoutSection D)
```

現在地：L1a・L1b 完了、L1c 継続中。
McCarthy 法の全 span の存在・完全関手による保存・単体的な pushout の選択と比較を証明済み。
指定した恒等 span 上の正規化、McCarthy の単体ホモトピー、単体積 Quillen A、
object/core 比較と加法性比較の弱同値性、面のホモトピー引き戻し条件は未証明。
反復 S 実現と §6.43 の homotopy fiber の比較、既存の構造射との照合、
正の段の Ω 条件・delooping、負次数消滅を含む BF 連結スペクトル、スペクトル関手は未完了。
L1d–f 未完了、L1g は別途指示待ち。Core および他レーンの公開 API に変更なし。

検証：対象ビルド成功（3134 jobs）、公理監査成功（1344 宣言、標準三公理のみ）。追加公理・sorry なし。

### 6.46 恒等な枝を持つ二つの span 族の同時正規化

§6.45 に残していた恒等 span 上の対象・四角形の厳密な正規化を証明した。
Fiore–Pieper Notation 3.26・Proposition 3.28（著者公開版 pp.40–42）に従い、
二つの枝のうちどちらかが恒等である標準 span の二つの像の和を使う。
向きごとに別々の切断を選ぶだけでは同時正規化を意味しないため、
共通部分で標準四角形が厳密に一致することを確認してから貼り合わせた。
`false` は横方向に一定（下辺が恒等）、`true` は縦方向に一定（左辺が恒等）の四角形。
重なりの一致は、二つの像への冪等な射の交差した復元がともに共通始点の一定図式となる
形状の等号から得た。高次の比較を同型に弱めた主張ではない。

`jointNormalizedPushoutSection C` は全 span の内部 Hom 上の単一の厳密な切断であり、
二つの `identitySpanFamily b C` に対して同時に `identityPushoutFamily b C` を回収する。
全単体次数での式なので、退化した恒等射の保存だけを主張していた以前の選択より強い。
既存の `stablePushoutSection` の公開定義・型は変更せず、二つの選択の関手同型も構成した。

追加ファイル：`IdentityPushoutShapes.lean`、`IdentityPushoutOverlap.lean`、
`IdentityPushoutUnion.lean`、`JointNormalizedPushoutSection.lean`。
以下は namespace `SerrePositivity.KST.SConstruction` 内の公開宣言の正確な型。

```lean
def identityPushoutShape (b : Bool) : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ Δ[1]

lemma identityPushoutShape_isPushout {C : SSet.{u}} [Quasicategory C] (b : Bool)
    (g : (Δ[1] : SSet.{u}) ⟶ C) : IsPushoutSquare (identityPushoutShape b ≫ g)

def identitySpanShape (b : Bool) : (horn 2 0 : SSet.{u}) ⟶ Δ[1]

def identitySpanSection (b : Bool) : (Δ[1] : SSet.{u}) ⟶ horn 2 0

lemma identitySpanSection_shape (b : Bool) :
    identitySpanSection b ≫ identitySpanShape b = 𝟙 (Δ[1] : SSet.{u})

def identitySpanFamily (b : Bool) (C : SSet.{u}) :
    (ihom (Δ[1] : SSet.{u})).obj C ⟶ (ihom (horn 2 0 : SSet.{u})).obj C

instance identitySpanFamily_mono (b : Bool) (C : SSet.{u}) : Mono (identitySpanFamily b C)

def identityPushoutFamily (b : Bool) (C : SSet.{u}) [Quasicategory C] :
    (ihom (Δ[1] : SSet.{u})).obj C ⟶ pushoutDiagrams C

lemma identityPushoutFamily_ι (b : Bool) (C : SSet.{u}) [Quasicategory C] :
    identityPushoutFamily b C ≫ (fullSubcomplexOnVertices _ IsPushoutDiagramVertex).ι =
      (pre (identityPushoutShape b)).app C

lemma identityPushoutFamily_projection (b : Bool) (C : SSet.{u}) [Quasicategory C] :
    identityPushoutFamily b C ≫ pushoutProjection C = identitySpanFamily b C

def identitySquareReconstruction (b : Bool) (C : SSet.{u}) :
    (ihom (horn 2 0 : SSet.{u})).obj C ⟶ (ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj C

lemma identitySpanFamily_reconstruction (b : Bool) (C : SSet.{u}) :
    identitySpanFamily b C ≫ identitySquareReconstruction b C =
      (pre (identityPushoutShape b)).app C

lemma identitySquareReconstruction_cross (C : SSet.{u}) :
    (pre (identitySpanSection true)).app C ≫ identitySpanFamily true C ≫
        identitySquareReconstruction false C =
      (pre (identitySpanSection false)).app C ≫ identitySpanFamily false C ≫
        identitySquareReconstruction true C

lemma identitySquareReconstruction_overlap (C : SSet.{u}) (n : SimplexCategoryᵒᵖ)
    (v : ((ihom (horn 2 0 : SSet.{u})).obj C).obj n)
    (h₀ : v ∈ (Subcomplex.range (identitySpanFamily false C)).obj n)
    (h₁ : v ∈ (Subcomplex.range (identitySpanFamily true C)).obj n) :
    (identitySquareReconstruction false C).app n v =
      (identitySquareReconstruction true C).app n v

def subcomplexUnionMap {X Y : SSet.{u}} (S T : X.Subcomplex) (f g : X ⟶ Y)
    (h : ∀ n v, v ∈ S.obj n → v ∈ T.obj n → f.app n v = g.app n v) :
    ((S ⊔ T : X.Subcomplex) : SSet.{u}) ⟶ Y

def identitySpanSubcomplex (C : SSet.{u}) : ((ihom (horn 2 0 : SSet.{u})).obj C).Subcomplex

def identityUnionSquare (C : SSet.{u}) :
    (identitySpanSubcomplex C : SSet.{u}) ⟶ (ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj C

lemma identityUnionSquare_on_family (C : SSet.{u}) (b : Bool) (n : SimplexCategoryᵒᵖ)
    (g : ((ihom (Δ[1] : SSet.{u})).obj C).obj n)
    (v : (identitySpanSubcomplex C).obj n) (hv : v.val = (identitySpanFamily b C).app n g) :
    (identityUnionSquare C).app n v = ((pre (identityPushoutShape b)).app C).app n g

lemma identityUnionSquare_span (C : SSet.{u}) :
    identityUnionSquare C ≫ (pre spanSquareBoundary).app C = (identitySpanSubcomplex C).ι

def identityUnionPushoutFamily (C : SSet.{u}) [Quasicategory C] :
    (identitySpanSubcomplex C : SSet.{u}) ⟶ pushoutDiagrams C

lemma identityUnionPushoutFamily_projection (C : SSet.{u}) [Quasicategory C] :
    identityUnionPushoutFamily C ≫ pushoutProjection C = (identitySpanSubcomplex C).ι

lemma exists_jointNormalizedPushoutSection (C : SSet.{u}) [Quasicategory C] [IsStable C] :
    ∃ s : (ihom (horn 2 0 : SSet.{u})).obj C ⟶ pushoutDiagrams C,
      (identitySpanSubcomplex C).ι ≫ s = identityUnionPushoutFamily C ∧
        s ≫ pushoutProjection C = 𝟙 _

def jointNormalizedPushoutSection (C : SSet.{u}) [Quasicategory C] [IsStable C] :
    (ihom (horn 2 0 : SSet.{u})).obj C ⟶ pushoutDiagrams C

lemma jointNormalizedPushoutSection_projection (C : SSet.{u}) [Quasicategory C] [IsStable C] :
    jointNormalizedPushoutSection C ≫ pushoutProjection C = 𝟙 _

lemma jointNormalizedPushoutSection_union (C : SSet.{u}) [Quasicategory C] [IsStable C] :
    (identitySpanSubcomplex C).ι ≫ jointNormalizedPushoutSection C =
      identityUnionPushoutFamily C

lemma jointNormalizedPushoutSection_identity (b : Bool) (C : SSet.{u})
    [Quasicategory C] [IsStable C] :
    identitySpanFamily b C ≫ jointNormalizedPushoutSection C = identityPushoutFamily b C

def jointNormalizedPushoutSection_comparison (C : SSet.{u}) [Quasicategory C] [IsStable C] :
    FunctorIso (jointNormalizedPushoutSection C) (stablePushoutSection C)
```

現在地：L1a・L1b 完了、L1c 継続中。
McCarthy 法の一般 pushout の存在・保存・単体的な選択に加え、恒等 span の両向きの同時正規化まで証明済み。
図式圏に移した正規化付き pushout の添字制限との両立、McCarthy の単体ホモトピー、単体積 Quillen A、
object/core 比較と加法性比較の弱同値性、面のホモトピー引き戻し条件は未完了。
反復 S 実現と §6.43 の homotopy fiber の比較、既存の構造射との照合、
正の段の Ω 条件・delooping、負次数消滅を含む BF 連結スペクトル、スペクトル関手は未完了。
L1d–f 未完了、L1g は別途指示待ち。Core および他レーンの公開 API に変更なし。

検証：対象ビルド成功（3172 jobs）、公理監査成功（1371 宣言、標準三公理のみ）。追加公理・sorry なし。

### 6.47 同じ選択による図式圏の押し出しと添字制限の厳密な両立

§6.46 の単一の正規化した選択を全ての図式圏に共通に使う構成を実装した。
Fiore–Pieper Corollary 3.35（著者公開版 pp.43–44）の添字制限との両立に対応する。
`normalizedPushoutSquareChoice C` を固定し、任意の族 `d : K → Fun(span,C)` に後合成した後、
内部 Hom の二変数の交換で `square → Fun(K,C)` に移す。
任意の `i : L → K` による添字制限との式を厳密な射の等号で証明したため、
面写像と退化写像の両方に同じ選択を適用できる。
図式圏ごとに新たな押し出し切断を選び、その間に同型を選ぶ方法ではない。

得た四角形が実際に図式圏の押し出しであることは、評価後の四角形を選択の頂点へ戻し、
§6.45 の点ごとの押し出し判定で証明した。入力 span の厳密な回収と、
両向きの恒等 span 上での標準四角形の厳密な回収も証明した。
`selectedFunctorPushout` は族へ交換する操作も含めた、図式圏の任意の指定 span に対する直接の API。
任意の `K` と任意の span に対し、入力を保持する押し出しと添字制限の厳密な両立を与える。
この段階だけで McCarthy ホモトピーの構成や加法性を完成したとは数えない。

追加ファイル：`DiagramPushoutChoice.lean`。
以下は namespace `SerrePositivity.KST.SConstruction` 内の公開宣言の正確な型。
`flipFamily_evaluate` は全ての単体集合について成立し、他の宣言は標的 `C` の
quasicategory 性と安定性を要求する。添字 `K,L` に有限性・Kan 性等は要求しない。

```lean
lemma flipFamily_evaluate {K A C : SSet.{u}} (F : K ⟶ (ihom A).obj C) (k : K _⦋0⦌) :
    internalHomFlipHomEquiv K A C F ≫ evaluateFunctorAt k =
      (functorVertexEquiv A C).symm (F.app (Opposite.op ⦋0⦌) k)

def normalizedPushoutSquareChoice (C : SSet.{u}) [Quasicategory C] [IsStable C] :
    (ihom (horn 2 0 : SSet.{u})).obj C ⟶ (ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj C

lemma normalizedPushoutSquareChoice_span (C : SSet.{u}) [Quasicategory C] [IsStable C] :
    normalizedPushoutSquareChoice C ≫ (pre spanSquareBoundary).app C = 𝟙 _

lemma normalizedPushoutSquareChoice_identity (b : Bool) (C : SSet.{u})
    [Quasicategory C] [IsStable C] :
    identitySpanFamily b C ≫ normalizedPushoutSquareChoice C =
      (pre (identityPushoutShape b)).app C

def chosenPushoutFamily {K C : SSet.{u}} [Quasicategory C] [IsStable C]
    (d : K ⟶ (ihom (horn 2 0 : SSet.{u})).obj C) :
    K ⟶ (ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj C

def chosenDiagramPushout {K C : SSet.{u}} [Quasicategory C] [IsStable C]
    (d : K ⟶ (ihom (horn 2 0 : SSet.{u})).obj C) :
    (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ (ihom K).obj C

lemma chosenDiagramPushout_span {K C : SSet.{u}} [Quasicategory C] [IsStable C]
    (d : K ⟶ (ihom (horn 2 0 : SSet.{u})).obj C) :
    spanSquareBoundary ≫ chosenDiagramPushout d = internalHomFlipHomEquiv K _ C d

lemma chosenDiagramPushout_isPushout {K C : SSet.{u}} [Quasicategory C] [IsStable C]
    (d : K ⟶ (ihom (horn 2 0 : SSet.{u})).obj C) : IsPushoutSquare (chosenDiagramPushout d)

lemma chosenDiagramPushout_reindex {K L C : SSet.{u}} [Quasicategory C] [IsStable C]
    (i : L ⟶ K) (d : K ⟶ (ihom (horn 2 0 : SSet.{u})).obj C) :
    chosenDiagramPushout (i ≫ d) = chosenDiagramPushout d ≫ (pre i).app C

lemma chosenDiagramPushout_identity {K C : SSet.{u}} [Quasicategory C] [IsStable C]
    (b : Bool) (g : K ⟶ (ihom (Δ[1] : SSet.{u})).obj C) :
    chosenDiagramPushout (g ≫ identitySpanFamily b C) =
      identityPushoutShape b ≫ internalHomFlipHomEquiv K _ C g

def selectedFunctorPushout {K C : SSet.{u}} [Quasicategory C] [IsStable C]
    (p : (horn 2 0 : SSet.{u}) ⟶ (ihom K).obj C) :
    (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ (ihom K).obj C

lemma selectedFunctorPushout_span {K C : SSet.{u}} [Quasicategory C] [IsStable C]
    (p : (horn 2 0 : SSet.{u}) ⟶ (ihom K).obj C) :
    pushoutSpan (selectedFunctorPushout p) = p

lemma selectedFunctorPushout_isPushout {K C : SSet.{u}} [Quasicategory C] [IsStable C]
    (p : (horn 2 0 : SSet.{u}) ⟶ (ihom K).obj C) : IsPushoutSquare (selectedFunctorPushout p)

lemma selectedFunctorPushout_reindex {K L C : SSet.{u}} [Quasicategory C] [IsStable C]
    (i : L ⟶ K) (p : (horn 2 0 : SSet.{u}) ⟶ (ihom K).obj C) :
    selectedFunctorPushout (p ≫ (pre i).app C) = selectedFunctorPushout p ≫ (pre i).app C
```

現在地：L1a・L1b 完了、L1c 継続中。
McCarthy 法の一般 pushout の存在・保存・単体的選択・両向きの恒等 span の同時正規化に加え、
図式圏への共通の選択の移送と、任意の添字制限との厳密な両立まで証明済み。
McCarthy の具体的な単体ホモトピー、単体積 Quillen A、object/core 比較と加法性比較の弱同値性、
面のホモトピー引き戻し条件は未完了。
反復 S 実現と §6.43 の homotopy fiber の比較、既存の構造射との照合、
正の段の Ω 条件・delooping、負次数消滅を含む BF 連結スペクトル、スペクトル関手は未完了。
L1d–f 未完了、L1g は別途指示待ち。Core および他レーンの公開 API に変更なし。

検証：対象ビルド成功（3173 jobs）、公理監査成功（1385 宣言、標準三公理のみ）。追加公理・sorry なし。

### 6.48 零対象上で恒等となる零射の自然変換

Fiore–Pieper Lemma 4.24（著者公開版 p.58）と Example 9.14（pp.82–83）で使う、
零対象から恒等関手への自然変換と恒等関手から零対象への自然変換を構成した。
指定された `ZeroVertex C` の始対象性・終対象性のみを使い、
`Quasicategory C` や `IsStable C` を追加の仮定にはしていない。
零対象上で恒等になるという正規化は、単に成分のホモトピー類を固定する主張ではなく、
零対象で一定な任意のパラメーター付き図式上で prism 全体が厳密に一定になる式で証明した。

一般の相対版では `S : B.Subcomplex` 上で零対象に一定な `f : B → C` を入力にする。
区間の両端と `interval × S` の和で図式を貼り合わせ、
外にある単体の区間成分は両端を通るため、時刻零の始点または時刻一の終点の零対象性で延長した。
始点・終点と既存の部分への制限を同時に厳密に保持する。
恒等関手に適用する際には零対象の生成部分複体を固定して選んだ。
`false` は零対象から恒等関手へ、`true` は恒等関手から零対象への向き。

追加ファイル：`ZeroNaturalTransformations.lean`。
以下は namespace `SerrePositivity.KST.SConstruction` 内の公開宣言の正確な型。
自然変換を関手同型・弱同値とは主張しておらず、これだけから S• 後のホモトピーや
K 空間の可縮性を結論しない。McCarthy の具体的な補完図式での利用は後続の証明。

```lean
lemma exists_relative_zeroPrism {B C : SSet.{u}} (z : ZeroVertex C) (b : Bool)
    (S : B.Subcomplex) (f : B ⟶ C) (hf : S.ι ≫ f = SSet.const z.vertex) :
    ∃ H : (Δ[1] : SSet.{u}) ⊗ B ⟶ C,
      prismEndpoint 0 B ≫ H = (if b then f else SSet.const z.vertex) ∧
      prismEndpoint 1 B ≫ H = (if b then SSet.const z.vertex else f) ∧
      (Δ[1] ◁ S.ι) ≫ H = SSet.const z.vertex

def zeroNaturalTransformation {C : SSet.{u}} (z : ZeroVertex C) (b : Bool) :
    (Δ[1] : SSet.{u}) ⊗ C ⟶ C

lemma zeroNaturalTransformation_zero {C : SSet.{u}} (z : ZeroVertex C) (b : Bool) :
    prismEndpoint 0 C ≫ zeroNaturalTransformation z b =
      (if b then 𝟙 C else SSet.const z.vertex)

lemma zeroNaturalTransformation_one {C : SSet.{u}} (z : ZeroVertex C) (b : Bool) :
    prismEndpoint 1 C ≫ zeroNaturalTransformation z b =
      (if b then SSet.const z.vertex else 𝟙 C)

lemma zeroNaturalTransformation_fixed {C : SSet.{u}} (z : ZeroVertex C) (b : Bool) :
    (Δ[1] ◁ (Subcomplex.ofSimplex z.vertex).ι) ≫ zeroNaturalTransformation z b =
      SSet.const z.vertex

lemma zeroNaturalTransformation_constant {A C : SSet.{u}} (z : ZeroVertex C) (b : Bool) :
    (Δ[1] ◁ (SSet.const z.vertex : A ⟶ C)) ≫ zeroNaturalTransformation z b =
      SSet.const z.vertex
```

現在地：L1a・L1b 完了、L1c 継続中。
一般 pushout の存在・保存・単体的選択・両向きの同時正規化、
図式圏への移送・添字制限との厳密な両立に加え、零対象上で正規化した零射の自然変換を証明済み。
McCarthy の具体的な単体ホモトピー、単体積 Quillen A、object/core 比較と加法性比較の弱同値性、
面のホモトピー引き戻し条件は未完了。
反復 S 実現と §6.43 の homotopy fiber の比較、既存の構造射との照合、
正の段の Ω 条件・delooping、負次数消滅を含む BF 連結スペクトル、スペクトル関手は未完了。
L1d–f 未完了、L1g は別途指示待ち。Core および他レーンの公開 API に変更なし。

検証：対象ビルド成功（3174 jobs）、公理監査成功（1391 宣言、標準三公理のみ）。追加公理・sorry なし。

### 6.49 S₂ と全 cofiber 正方形の相対比較・完全性・反復 S 実現の比較

McCarthy 法で実際の正方形を扱うため、S₂ の全 gapped Ar[2] 図式から、
全 cofiber 正方形への中央制限 `sTwoCofiberRestriction` を構成した。
この制限写像そのものが trivial Kan fibration であることを証明した。
零次元では指定正方形に外側の零対角を補い、正次元では中央部分複体と
パラメーター境界を同時に固定して延長した。新しい Ar[2] 単体には最初の零対角か
最後の零対角が含まれるため、その始対象性・終対象性で相対充填できる。
正次元の境界充填は C に quasicategory 性すら要求せず、
零次元の gapped 性の構成を合わせる際に `Quasicategory C` を要求する。
`IsStable C` はこの trivial Kan fibration の証明の前提ではない。

cofiber 正方形全体の quasicategory 性、C が安定なときの安定性、
制限写像の零対象・任意の押し出しの保存も証明した。
単体的に選んだ切断は中央の正方形を厳密に回収し、
切断自身も零対象と任意の押し出しを保存する。
制限後に補完し直す合成と恒等関手の関手同型、および quasicategory の同値を構成した。
切断の入力 C に関する自然性や、S₂ における厳密な両側逆は主張しない。

`cofiberStableModel` と、安定な入力間の完全関手 `sTwoCofiberComparison`・
`sTwoCofiberInverse` を構成した。
`multiRealizationFunctor` による任意回数の反復 S•・core・対角実現でも、
比較の像が anodyne 局所化で同型になることを既存の保存定理から証明した。
これにより正方形表示で得る加法性を既存の core S 実現へ移す比較を用意した。
object S の比較の弱同値性や、零対象を一つに固定した正方形部分模型への比較は未証明。

追加ファイル：`STwoCofiberRestriction.lean`、`STwoCofiberLifting.lean`、`STwoCofiberModel.lean`。
以下は namespace `SerrePositivity.KST.SConstruction` 内の公開宣言の正確な型。

```lean
lemma isGapped_two_middle {C : SSet.{u}} {F : arNerve 2 ⟶ C} (hF : IsGapped F) :
    IsZeroVertex (squareVertex (arTwoMiddleSquare ≫ F) 0 1) ∧
      IsPushoutSquare (arTwoMiddleSquare ≫ F)

def sTwoCofiberRestriction (C : SSet.{u}) : sConstruction 2 C ⟶ cofiberDiagrams C

lemma sTwoCofiberRestriction_ι (C : SSet.{u}) :
    sTwoCofiberRestriction C ≫ (fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι =
      (gappedSubcomplex 2 C).ι ≫ (pre arTwoMiddleSquare).app C

lemma sTwoCofiberRestriction_vertex_surjective (C : SSet.{u}) [Quasicategory C] :
    Function.Surjective ((sTwoCofiberRestriction C).app (Opposite.op ⦋0⦌))

lemma sTwoCofiberRestriction_hasLiftingProperty_boundary (n : ℕ) (C : SSet.{u}) :
    HasLiftingProperty (boundary (n + 1)).ι (sTwoCofiberRestriction C)

instance sTwoCofiberRestriction_trivialKanFibration (C : SSet.{u}) [Quasicategory C] :
    TrivialKanFibration (sTwoCofiberRestriction C)

instance cofiberDiagrams_quasicategory (C : SSet.{u}) [Quasicategory C] :
    Quasicategory (cofiberDiagrams C)

instance cofiberDiagrams_isStable (C : SSet.{u}) [Quasicategory C] [IsStable C] :
    IsStable (cofiberDiagrams C)

lemma sTwoCofiberRestriction_preservesSConstructionData (C : SSet.{u}) [Quasicategory C] :
    PreservesSConstructionData (sTwoCofiberRestriction C)

def cofiberStableModel (X : StableModel.{u}) : StableModel.{u}

def sTwoCofiberComparison (X : StableModel.{u}) : sStableModel 2 X ⟶ cofiberStableModel X

def sTwoCofiberSection (C : SSet.{u}) [Quasicategory C] : cofiberDiagrams C ⟶ sConstruction 2 C

lemma sTwoCofiberSection_projection (C : SSet.{u}) [Quasicategory C] :
    sTwoCofiberSection C ≫ sTwoCofiberRestriction C = 𝟙 _

lemma sTwoCofiberSection_preservesSConstructionData (C : SSet.{u}) [Quasicategory C] :
    PreservesSConstructionData (sTwoCofiberSection C)

def sTwoCofiberInverse (X : StableModel.{u}) : cofiberStableModel X ⟶ sStableModel 2 X

def sTwoCofiberSection_comparison (C : SSet.{u}) [Quasicategory C] :
    FunctorIso (sTwoCofiberRestriction C ≫ sTwoCofiberSection C) (𝟙 (sConstruction 2 C))

def sTwoCofiberEquivalence (C : SSet.{u}) [Quasicategory C] :
    QCatEquivalence (sConstruction 2 C) (cofiberDiagrams C)

lemma sTwoCofiberComparison_realization_localized_isIso (r : ℕ) (X : StableModel.{u}) :
    IsIso (SerrePositivity.SimplicialModel.AnodyneHomotopy.anodyneQ.map
      ((multiRealizationFunctor r).map (sTwoCofiberComparison X)))
```

現在地：L1a・L1b 完了、L1c 継続中。
§6.45–48 の pushout の選択・正規化・零射の自然変換に加え、
全 cofiber 正方形表示との相対比較と反復 core S 実現での弱同値まで証明済み。
McCarthy の具体的な単体ホモトピー、単体積 Quillen A、object/core 比較と加法性比較の弱同値性、
面のホモトピー引き戻し条件は未完了。
反復 S 実現と §6.43 の homotopy fiber の比較、既存の構造射との照合、
正の段の Ω 条件・delooping、負次数消滅を含む BF 連結スペクトル、スペクトル関手は未完了。
L1d–f 未完了、L1g は別途指示待ち。Core および他レーンの公開 API に変更なし。

検証：対象ビルド成功（3177 jobs）、公理監査成功（1409 宣言、標準三公理のみ）。追加公理・sorry なし。

### 6.50 自然同値による object S の実ホモトピー・自明ファイブレーションの像の弱同値

Fiore–Pieper Proposition 4.27 の object/core 比較で必要となる、
完全関手の自然同値による object S のホモトピーを構成した。
区間の n 単体から Ar[n] の区間の左端で読む時刻 `arTimeCoordinate` を作り、
自然変換をその可変時刻に評価した図式を object S の n 単体にする。
可変時刻の図式と元の始点の図式の間には、二つの時刻の min による prism がある。
指定時刻の頂点が零ならその成分は恒等辺、一なら元の自然変換の辺になるため、
元の自然変換が点ごとに可逆なら関手同型となる。gapped 性はこの同型で輸送した。

この構成の面・退化の自然性と両端を厳密に確認し、元の既存の
`objectSConstructionFunctor.map f` と `.map g` の間の実際の `SSet.Homotopy` を得た。
特に関手同型 `FunctorIso f.val g.val` だけから点ごとの可逆性を供給する公開構成
`objectSHomotopyOfFunctorIso` を実装した。元の object S を別模型へ置換していない。
任意の可逆でない自然変換によるホモトピーは主張しない。

さらに安定な入力間の trivial Kan fibration に対し、厳密な切断を選び、
その切断の零対象・任意の押し出しの保存を射影の反映から証明した。
二つの合成と恒等関手の関手同型から object S の二つの実ホモトピーを構成し、
object S の射が単体ホモトピー同値であることを証明した。
その像が anodyne 局所化で同型であることも、実ホモトピーを等号に送って逆を作ることで証明した。
object S の Kan 性や object/core 比較の弱同値性は仮定にしていない。
§6.49 の S₂ と全 cofiber 正方形の比較が object S の後も弱同値になることへ適用済み。

追加ファイル：`VariableTimeHomotopy.lean`、`VariableTimeEquivalence.lean`、
`ObjectSVertices.lean`、`ArTimeCoordinates.lean`、`ObjectSHomotopy.lean`、`ObjectSTrivialFibration.lean`。
以下は namespace `SerrePositivity.KST.SConstruction` 内の公開宣言の正確な型。
可変時刻の同型では標的の quasicategory 性と点ごとの可逆性を明示している。
object S の関手の射についての結論では `StableModel` の既存の完全関手を使う。

```lean
def intervalMinOrder : ULift.{u} (Fin 2 × Fin 2) →o ULift.{u} (Fin 2)

def intervalMin : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ Δ[1]

lemma intervalMin_app_zero {n : ℕ} (s : (Δ[1] : SSet.{u}) _⦋n⦌) :
    intervalMin.app (Opposite.op ⦋n⦌)
        (s, PinchedHom.constant (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) n) =
      PinchedHom.constant (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) n

lemma intervalMin_app_one {n : ℕ} (s : (Δ[1] : SSet.{u}) _⦋n⦌) :
    intervalMin.app (Opposite.op ⦋n⦌)
      (s, PinchedHom.constant (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) n) = s

def variableTimeShape {A : SSet.{u}} (τ : A ⟶ (Δ[1] : SSet.{u})) : A ⊗ Δ[1] ⟶ A ⊗ Δ[1]

lemma variableTimeShape_zero {A : SSet.{u}} (τ : A ⟶ (Δ[1] : SSet.{u})) :
    SSet.ι₀ ≫ variableTimeShape τ = (SSet.ι₀ : A ⟶ A ⊗ Δ[1])

lemma variableTimeShape_one {A : SSet.{u}} (τ : A ⟶ (Δ[1] : SSet.{u})) :
    SSet.ι₁ ≫ variableTimeShape τ = lift (𝟙 A) τ

def variableTimeImage {A C D : SSet.{u}} {f g : C ⟶ D} (H : SSet.Homotopy f g)
    (F : A ⟶ C) (τ : A ⟶ (Δ[1] : SSet.{u})) : A ⟶ D

lemma variableTimeImage_pre {A B C D : SSet.{u}} {f g : C ⟶ D} (H : SSet.Homotopy f g)
    (F : A ⟶ C) (τ : A ⟶ (Δ[1] : SSet.{u})) (i : B ⟶ A) :
    i ≫ variableTimeImage H F τ = variableTimeImage H (i ≫ F) (i ≫ τ)

lemma variableTimeImage_zero {A C D : SSet.{u}} {f g : C ⟶ D} (H : SSet.Homotopy f g)
    (F : A ⟶ C) :
    variableTimeImage H F (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) = F ≫ f

lemma variableTimeImage_one {A C D : SSet.{u}} {f g : C ⟶ D} (H : SSet.Homotopy f g)
    (F : A ⟶ C) :
    variableTimeImage H F (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) = F ≫ g

def variableTimeHomotopy {A C D : SSet.{u}} {f g : C ⟶ D} (H : SSet.Homotopy f g)
    (F : A ⟶ C) (τ : A ⟶ (Δ[1] : SSet.{u})) :
    SSet.Homotopy (F ≫ f) (variableTimeImage H F τ)

lemma variableTimeHomotopy_isInvertible {A C D : SSet.{u}} [Quasicategory D]
    {f g : C ⟶ D} (H : SSet.Homotopy f g)
    (hH : ∀ c, IsInvertibleEdge (simplicialHomotopyVertexEdge H c).toTruncated)
    (F : A ⟶ C) (τ : A ⟶ (Δ[1] : SSet.{u})) (a : A _⦋0⦌) :
    IsInvertibleEdge (simplicialHomotopyVertexEdge (variableTimeHomotopy H F τ) a).toTruncated

def variableTimeImageIso {A C D : SSet.{u}} [Quasicategory D] {f g : C ⟶ D}
    (H : SSet.Homotopy f g)
    (hH : ∀ c, IsInvertibleEdge (simplicialHomotopyVertexEdge H c).toTruncated)
    (F : A ⟶ C) (τ : A ⟶ (Δ[1] : SSet.{u})) :
    FunctorIso (F ≫ f) (variableTimeImage H F τ)

lemma IsGapped.variableTimeImage {C D : SSet.{u}} [Quasicategory D] {f g : C ⟶ D}
    (H : SSet.Homotopy f g)
    (hH : ∀ c, IsInvertibleEdge (simplicialHomotopyVertexEdge H c).toTruncated)
    (hf : PreservesCofiberData f) {n : ℕ} {F : arNerve n ⟶ C} (hF : IsGapped F)
    (τ : arNerve n ⟶ (Δ[1] : SSet.{u})) : IsGapped (variableTimeImage H F τ)

def gappedObjectVertex {n : ℕ} {C : SSet.{u}} (F : arNerve n ⟶ C) (hF : IsGapped F) :
    (sConstruction n C) _⦋0⦌

lemma gappedDiagram_gappedObjectVertex {n : ℕ} {C : SSet.{u}}
    (F : arNerve n ⟶ C) (hF : IsGapped F) : gappedDiagram (gappedObjectVertex F hF) = F

lemma gappedDiagram_injective {n : ℕ} {C : SSet.{u}} :
    Function.Injective (@gappedDiagram n C)

lemma gappedDiagram_sMap {m n : ℕ} {C : SSet.{u}} (θ : Fin (m + 1) →o Fin (n + 1))
    (v : (sConstruction n C) _⦋0⦌) :
    gappedDiagram ((sMap C θ).app (Opposite.op ⦋0⦌) v) = arNerveMap θ ≫ gappedDiagram v

lemma gappedDiagram_objectS_map {C : SSet.{u}} {n m : SimplexCategoryᵒᵖ} (α : n ⟶ m)
    (v : (objectSConstruction C).obj n) :
    gappedDiagram ((objectSConstruction C).map α v) =
      arNerveMap α.unop.toOrderHom ≫ gappedDiagram v

lemma gappedDiagram_sPostcompCofiber {n : ℕ} {C D : SSet.{u}} [Quasicategory D]
    (f : C ⟶ D) (hf : PreservesCofiberData f) (v : (sConstruction n C) _⦋0⦌) :
    gappedDiagram ((sPostcompCofiber n f hf).app (Opposite.op ⦋0⦌) v) = gappedDiagram v ≫ f

lemma gappedDiagram_objectSFunctor_map {X Y : StableModel.{u}} (f : X ⟶ Y)
    (n : SimplexCategoryᵒᵖ) (v : (objectSConstruction X.carrier).obj n) :
    gappedDiagram ((objectSConstructionFunctor.map f).app n v) = gappedDiagram v ≫ f.val

def arFirstEndpointOrder (n : ℕ) : Ar.{u} n →o ULift.{u} (Fin (n + 1))

def arFirstEndpoint (n : ℕ) : arNerve.{u} n ⟶ Δ[n]

def arTimeCoordinate {n : ℕ} (s : (Δ[1] : SSet.{u}) _⦋n⦌) : arNerve.{u} n ⟶ Δ[1]

lemma arTimeCoordinate_naturality {n m : SimplexCategoryᵒᵖ} (α : n ⟶ m)
    (s : (Δ[1] : SSet.{u}).obj n) :
    arNerveMap α.unop.toOrderHom ≫ arTimeCoordinate s = arTimeCoordinate ((Δ[1]).map α s)

lemma arTimeCoordinate_constant (n : ℕ) (i : Fin 2) :
    arTimeCoordinate (PinchedHom.constant (stdSimplex.obj₀Equiv.symm i) n) =
      (SSet.const (stdSimplex.obj₀Equiv.symm i) : arNerve.{u} n ⟶ Δ[1])

def objectSHomotopyVertex {X Y : StableModel.{u}} {f g : X ⟶ Y}
    (H : SSet.Homotopy f.val g.val)
    (hH : ∀ c, IsInvertibleEdge (simplicialHomotopyVertexEdge H c).toTruncated)
    {n : ℕ} (v : (sConstruction n X.carrier) _⦋0⦌) (s : (Δ[1] : SSet.{u}) _⦋n⦌) :
    (sConstruction n Y.carrier) _⦋0⦌

lemma objectSHomotopyVertex_diagram {X Y : StableModel.{u}} {f g : X ⟶ Y}
    (H : SSet.Homotopy f.val g.val)
    (hH : ∀ c, IsInvertibleEdge (simplicialHomotopyVertexEdge H c).toTruncated)
    {n : ℕ} (v : (sConstruction n X.carrier) _⦋0⦌) (s : (Δ[1] : SSet.{u}) _⦋n⦌) :
    gappedDiagram (objectSHomotopyVertex H hH v s) =
      variableTimeImage H (gappedDiagram v) (arTimeCoordinate s)

def objectSHomotopyMap {X Y : StableModel.{u}} {f g : X ⟶ Y}
    (H : SSet.Homotopy f.val g.val)
    (hH : ∀ c, IsInvertibleEdge (simplicialHomotopyVertexEdge H c).toTruncated) :
    objectSConstruction X.carrier ⊗ Δ[1] ⟶ objectSConstruction Y.carrier

def objectSHomotopy {X Y : StableModel.{u}} {f g : X ⟶ Y}
    (H : SSet.Homotopy f.val g.val)
    (hH : ∀ c, IsInvertibleEdge (simplicialHomotopyVertexEdge H c).toTruncated) :
    SSet.Homotopy (objectSConstructionFunctor.map f) (objectSConstructionFunctor.map g)

def objectSHomotopyOfFunctorIso {X Y : StableModel.{u}} {f g : X ⟶ Y}
    (e : FunctorIso f.val g.val) :
    SSet.Homotopy (objectSConstructionFunctor.map f) (objectSConstructionFunctor.map g)

lemma preservesSConstructionData_section_of_trivialKanFibration {E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B] (p : E ⟶ B) [TrivialKanFibration p]
    (s : B ⟶ E) (hs : s ≫ p = 𝟙 _) : PreservesSConstructionData s

lemma objectS_map_isSimplicialHomotopyEquivalence_of_inverse {X Y : StableModel.{u}}
    (p : X ⟶ Y) (s : Y ⟶ X) (h₀ : FunctorIso (p.val ≫ s.val) (𝟙 X.carrier))
    (h₁ : FunctorIso (s.val ≫ p.val) (𝟙 Y.carrier)) :
    IsSimplicialHomotopyEquivalence (objectSConstructionFunctor.map p)

lemma objectS_map_isSimplicialHomotopyEquivalence_of_trivialKanFibration
    {X Y : StableModel.{u}} (p : X ⟶ Y) [TrivialKanFibration p.val] :
    IsSimplicialHomotopyEquivalence (objectSConstructionFunctor.map p)

lemma objectS_map_localized_isIso_of_trivialKanFibration {X Y : StableModel.{u}}
    (p : X ⟶ Y) [TrivialKanFibration p.val] :
    IsIso (AnodyneHomotopy.anodyneQ.map (objectSConstructionFunctor.map p))

lemma sTwoCofiberComparison_objectS_localized_isIso (X : StableModel.{u}) :
    IsIso (AnodyneHomotopy.anodyneQ.map
      (objectSConstructionFunctor.map (sTwoCofiberComparison X)))
```

現在地：L1a・L1b 完了、L1c 継続中。
object S の自然同値による実ホモトピー、および trivial Kan fibration の object S の像の弱同値まで証明済み。
object/core 比較の次の段階は、全ての辺が同値の図式の圏 D(m,w) を用意し、
時刻零への評価の trivial Kan fibration と、内部 Hom の交換による core S の各行との比較を証明する。
定数図式の包含の自然性と、今回の object S の弱同値の保存を合わせて、対角比較に接続する。
この D(m,w) の構成・評価の充填性・core S との比較はまだ未証明であり、
元の `objectToCoreSRealization` の弱同値性を完成扱いしない。
McCarthy の具体的な単体ホモトピー、単体積 Quillen A、object/core 比較と加法性比較の弱同値性、
面のホモトピー引き戻し条件は未完了。
反復 S 実現と §6.43 の homotopy fiber の比較、既存の構造射との照合、
正の段の Ω 条件・delooping、負次数消滅を含む BF 連結スペクトル、スペクトル関手は未完了。
L1d–f 未完了、L1g は別途指示待ち。Core および他レーンの公開 API に変更なし。

検証：対象ビルド成功（3183 jobs）、公理監査成功（1446 宣言、標準三公理のみ）。追加公理・sorry なし。

### 6.51 D(m,w) の全同値図式・単体的構造・頂点評価の inner fibration・零次数

Fiore–Pieper Proposition 4.27 の D(m,w) のため、任意の添字 K に対する
全同値図式の圏 `equivalenceDiagrams K C` を定義した。
対象は K の全辺を C の同値へ送る図式であり、図式間の自然変換は全て保持する。
従って C の core からなる関手単体集合そのものとは定義していない。
この対象の頂点は `K → core C` の実際の射と同値であることも証明したが、
自然変換まで core の射に制限した同型とは主張しない。

任意の添字制限、指定頂点での評価、定数図式の包含を構成し、
添字制限の恒等・合成、評価との両立、定数図式の包含の自然性を厳密な等号で証明した。
K=Δ[m] では単体的図式 `simplicialEquivalenceDiagrams` と、
定値図式からの自然変換 `constantEquivalenceDiagramNat` にまとめた。
指定頂点があるとき定数図式の評価は厳密に恒等となる。

一点からの内部 Hom の評価を、定数図式を逆に持つ実際の同型として構成した。
一般の評価は一点への制限とこの同型の合成になるため、C が quasicategory なら inner fibration。
全同値図式の包含も inner fibration なので、その指定頂点での評価も inner fibration である。
さらに D(0,w) の評価と定数図式の包含が、任意の C について実際の同型を与えることを証明した。
この零次数の同型から正次数の trivial Kan fibration を結論したわけではない。

標準単体の零頂点から恒等射への `simplexInitialContraction` も構成した。
時刻零は零頂点への定数、時刻一は恒等であり、零頂点上では全時刻で厳密に一定。
次の段階でこの収縮を全同値図式へ適用し、評価と定数図式の合成の自然同値を作る。
評価の inner fibration 性、定数図式による頂点の全射性、自然同値からの充満忠実性を合わせ、
既存の `IsFullyFaithful.trivialKanFibration_of_surjective` へ接続する方針。
一般の m での自然同値・充満忠実性・全境界の持ち上げはまだ未証明。

追加ファイル：`EquivalenceDiagrams.lean`、`EquivalenceDiagramFunctoriality.lean`、
`EquivalenceDiagramVertices.lean`、`FunctorVertexEvaluation.lean`、`SimplexInitialContraction.lean`。
以下は namespace `SerrePositivity.KST.SConstruction` 内の公開宣言の正確な型。
全同値図式の定義・制限・定数包含・対象の対応・一点評価の同型には quasicategory 性は不要。
全同値図式の quasicategory 性と評価の inner fibration 性には標的の quasicategory 性を要求する。

```lean
def IsEquivalenceDiagramVertex {K C : SSet.{u}} (v : ((ihom K).obj C) _⦋0⦌) : Prop

def equivalenceDiagrams (K C : SSet.{u}) : SSet.{u}

def equivalenceDiagramι (K C : SSet.{u}) : equivalenceDiagrams K C ⟶ (ihom K).obj C

instance equivalenceDiagrams_quasicategory (K C : SSet.{u}) [Quasicategory C] :
    Quasicategory (equivalenceDiagrams K C)

lemma isEquivalenceDiagramVertex_functorVertex {K C : SSet.{u}} (F : K ⟶ C) :
    IsEquivalenceDiagramVertex (functorVertex F) ↔
      ∀ s : K _⦋1⦌, IsInvertibleEdge (edgeOfSimplex (F.app (Opposite.op ⦋1⦌) s))

def equivalenceDiagramReindex {K L : SSet.{u}} (i : L ⟶ K) (C : SSet.{u}) :
    equivalenceDiagrams K C ⟶ equivalenceDiagrams L C

lemma equivalenceDiagramReindex_ι {K L : SSet.{u}} (i : L ⟶ K) (C : SSet.{u}) :
    equivalenceDiagramReindex i C ≫ equivalenceDiagramι L C =
      equivalenceDiagramι K C ≫ (pre i).app C

def equivalenceDiagramEvaluation (K C : SSet.{u}) (k : K _⦋0⦌) :
    equivalenceDiagrams K C ⟶ C

def equivalenceDiagramConstant (K C : SSet.{u}) : C ⟶ equivalenceDiagrams K C

lemma equivalenceDiagramConstant_ι (K C : SSet.{u}) :
    equivalenceDiagramConstant K C ≫ equivalenceDiagramι K C = curry (snd K C)

lemma equivalenceDiagramConstant_evaluation (K C : SSet.{u}) (k : K _⦋0⦌) :
    equivalenceDiagramConstant K C ≫ equivalenceDiagramEvaluation K C k = 𝟙 C

lemma equivalenceDiagramReindex_id (K C : SSet.{u}) :
    equivalenceDiagramReindex (𝟙 K) C = 𝟙 (equivalenceDiagrams K C)

lemma equivalenceDiagramReindex_comp {K L M : SSet.{u}} (i : L ⟶ K) (j : M ⟶ L)
    (C : SSet.{u}) :
    equivalenceDiagramReindex (j ≫ i) C = equivalenceDiagramReindex i C ≫
      equivalenceDiagramReindex j C

lemma equivalenceDiagramReindex_evaluation {K L : SSet.{u}} (i : L ⟶ K)
    (C : SSet.{u}) (l : L _⦋0⦌) :
    equivalenceDiagramReindex i C ≫ equivalenceDiagramEvaluation L C l =
      equivalenceDiagramEvaluation K C (i.app (Opposite.op ⦋0⦌) l)

lemma equivalenceDiagramConstant_reindex {K L : SSet.{u}} (i : L ⟶ K) (C : SSet.{u}) :
    equivalenceDiagramConstant K C ≫ equivalenceDiagramReindex i C =
      equivalenceDiagramConstant L C

def simplicialEquivalenceDiagrams (C : SSet.{u}) : SimplexCategoryᵒᵖ ⥤ SSet.{u}

def constantEquivalenceDiagramNat (C : SSet.{u}) :
    (Functor.const SimplexCategoryᵒᵖ).obj C ⟶ simplicialEquivalenceDiagrams C

def equivalenceDiagramVertexOfCoreMap {K C : SSet.{u}} (F : K ⟶ (quasicategoryCore C : SSet.{u})) :
    (equivalenceDiagrams K C) _⦋0⦌

def equivalenceDiagramCoreMap {K C : SSet.{u}} (v : (equivalenceDiagrams K C) _⦋0⦌) :
    K ⟶ (quasicategoryCore C : SSet.{u})

def equivalenceDiagramVerticesEquiv (K C : SSet.{u}) :
    (equivalenceDiagrams K C) _⦋0⦌ ≃ (K ⟶ (quasicategoryCore C : SSet.{u}))

def pointFunctorEvaluationIso (C : SSet.{u}) : (ihom (Δ[0] : SSet.{u})).obj C ≅ C

lemma evaluateFunctorAt_factor {K C : SSet.{u}} (k : K _⦋0⦌) :
    (pre (SSet.yonedaEquiv.symm k)).app C ≫ (pointFunctorEvaluationIso C).hom =
      evaluateFunctorAt k

instance evaluateFunctorAt_innerFibration {K C : SSet.{u}} [Quasicategory C] (k : K _⦋0⦌) :
    InnerFibration (evaluateFunctorAt (Y

instance equivalenceDiagramEvaluation_innerFibration (K C : SSet.{u}) [Quasicategory C]
    (k : K _⦋0⦌) : InnerFibration (equivalenceDiagramEvaluation K C k)

def zeroEquivalenceDiagramEvaluationIso (C : SSet.{u}) :
    equivalenceDiagrams (Δ[0] : SSet.{u}) C ≅ C

instance zeroEquivalenceDiagramEvaluation_isIso (C : SSet.{u}) :
    IsIso (equivalenceDiagramEvaluation (Δ[0] : SSet.{u}) C
      (stdSimplex.obj₀Equiv.symm (0 : Fin 1)))

def simplexInitialOrder (n : ℕ) : Fin 2 × Fin (n + 1) →o Fin (n + 1)

def simplexInitialContraction (n : ℕ) : (Δ[1] : SSet.{u}) ⊗ Δ[n] ⟶ Δ[n]

lemma simplexInitialContraction_zero (n : ℕ) :
    prismEndpoint 0 (Δ[n] : SSet.{u}) ≫ simplexInitialContraction n =
      SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin (n + 1)))

lemma simplexInitialContraction_one (n : ℕ) :
    prismEndpoint 1 (Δ[n] : SSet.{u}) ≫ simplexInitialContraction n = 𝟙 _

lemma simplexInitialContraction_firstVertex (n : ℕ) :
    (Δ[1] ◁ SSet.yonedaEquiv.symm (stdSimplex.obj₀Equiv.symm (0 : Fin (n + 1)))) ≫
      simplexInitialContraction n = SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin (n + 1)))
```

現在地：L1a・L1b 完了、L1c 継続中。
§6.50 の object S のホモトピー不変性と自明ファイブレーションの像の弱同値に加え、
D(m,w) の単体的構造・対象の core への図式との対応・評価の inner fibration・D(0,w) の同型を証明済み。
一般の m での評価の trivial Kan fibration、core S の各行との比較、
元の `objectToCoreSRealization` の弱同値性は未完了。
McCarthy の具体的な単体ホモトピー、単体積 Quillen A、加法性比較の弱同値性、
面のホモトピー引き戻し条件も未完了。
反復 S 実現と §6.43 の homotopy fiber の比較、既存の構造射との照合、
正の段の Ω 条件・delooping、負次数消滅を含む BF 連結スペクトル、スペクトル関手は未完了。
L1d–f 未完了、L1g は別途指示待ち。Core および他レーンの公開 API に変更なし。

検証：対象ビルド成功（3188 jobs）、公理監査成功（1477 宣言、標準三公理のみ）。追加公理・sorry なし。

### 6.52 D(m,w) の評価の自明ファイブレーションと object S の行の弱同値

標準単体の零頂点からの収縮を、全同値図式に制限した前合成の自然同値へ移した。
充満包含の充満忠実性で元の全同値図式の圏に持ち上げ、評価と定数図式が逆同値となることを証明した。
既存の inner fibration 性と頂点の全射性を合わせ、任意の m において元の評価が trivial Kan fibration となる。
この評価で安定性を反映し、定数図式の完全性と object S の後の局所化同型を証明した。
Core・F1B・Stable・他レーンのファイルと公開 API に変更なし。

主要公開宣言（namespace `SerrePositivity.KST.SConstruction`、宇宙 `u`）：

```lean
def restrictedPrecompositionIso {A B C E : SSet.{u}} [Quasicategory C]
    {f g : A ⟶ B} (H : SSet.Homotopy f g) (i : E ⟶ (ihom B).obj C)
    (hH : ∀ (v : E _⦋0⦌) (a : A _⦋0⦌), IsInvertibleEdge (edgeOfSimplex
      (((functorVertexEquiv B C).symm (i.app (Opposite.op ⦋0⦌) v)).app (Opposite.op ⦋1⦌)
        (simplicialHomotopyVertexEdge H a).edge))) :
    FunctorIso (i ≫ (pre f).app C) (i ≫ (pre g).app C)

lemma pre_constant_evaluation {K C : SSet.{u}} (k : K _⦋0⦌) :
    (pre (SSet.const k : K ⟶ K)).app C = evaluateFunctorAt k ≫ curry (snd K C)

def simplexInitialHomotopy (n : ℕ) :
    SSet.Homotopy (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin (n + 1))))
      (𝟙 (Δ[n] : SSet.{u}))

def equivalenceDiagramEvaluation_comparison (n : ℕ) (C : SSet.{u}) [Quasicategory C] :
    FunctorIso
      (equivalenceDiagramEvaluation (Δ[n] : SSet.{u}) C (stdSimplex.obj₀Equiv.symm 0) ≫
        equivalenceDiagramConstant Δ[n] C) (𝟙 (equivalenceDiagrams Δ[n] C))

def equivalenceDiagramEvaluationEquivalence (n : ℕ) (C : SSet.{u}) [Quasicategory C] :
    QCatEquivalence (equivalenceDiagrams (Δ[n] : SSet.{u}) C) C

instance equivalenceDiagramEvaluation_trivialKanFibration (n : ℕ) (C : SSet.{u})
    [Quasicategory C] : TrivialKanFibration
      (equivalenceDiagramEvaluation (Δ[n] : SSet.{u}) C (stdSimplex.obj₀Equiv.symm 0))

instance equivalenceDiagrams_isStable (n : ℕ) (C : SSet.{u})
    [Quasicategory C] [IsStable C] : IsStable (equivalenceDiagrams (Δ[n] : SSet.{u}) C)

def equivalenceDiagramStableModel (n : ℕ) (X : StableModel.{u}) : StableModel.{u}

def equivalenceDiagramStableEvaluation (n : ℕ) (X : StableModel.{u}) :
    equivalenceDiagramStableModel n X ⟶ X

def equivalenceDiagramStableConstant (n : ℕ) (X : StableModel.{u}) :
    X ⟶ equivalenceDiagramStableModel n X

lemma equivalenceDiagramStableConstant_evaluation (n : ℕ) (X : StableModel.{u}) :
    equivalenceDiagramStableConstant n X ≫ equivalenceDiagramStableEvaluation n X = 𝟙 X

lemma equivalenceDiagramStableEvaluation_objectS_localized_isIso (n : ℕ)
    (X : StableModel.{u}) : IsIso (AnodyneHomotopy.anodyneQ.map
      (objectSConstructionFunctor.map (equivalenceDiagramStableEvaluation n X)))

lemma equivalenceDiagramStableConstant_objectS_localized_isIso (n : ℕ)
    (X : StableModel.{u}) : IsIso (AnodyneHomotopy.anodyneQ.map
      (objectSConstructionFunctor.map (equivalenceDiagramStableConstant n X)))
```

前提：一般の前合成の補題は標的 C の quasicategory 性とホモトピー成分の可逆性を要求する。
評価の自明ファイブレーションは C の quasicategory 性のみ、安定模型と object S の弱同値は X : StableModel を要求する。

現在地：L1a・L1b 完了、L1c 継続中。一般の m での D(m,w) の評価と object S の定数包含の弱同値は証明済み。
core S の各行との同型、元の `objectToCoreSRealization` の弱同値、McCarthy の単体ホモトピー、
単体積 Quillen A、加法性、面のホモトピー引き戻し条件は未完了。
反復 S 実現と §6.43 の homotopy fiber の比較、構造射との照合、正の段の Ω 条件・delooping、
負次数消滅を含む BF 連結スペクトルとスペクトル関手も未完了。L1d–f 未完了、L1g は別途指示待ち。

検証：対象ビルド成功（3193 jobs）、公理監査成功（1490 宣言、propext・Classical.choice・Quot.sound のみ）。追加公理・sorry なし。

### 6.53 D(m,w) の object S と core S の交換した行の同型

零対象と全押し出しの保存を関手同型で移す補題、評価と定数関手の完全性、
D(m,w) の包含の完全性、関手圏と全同値図式の gapped 条件の判定を証明した。
Ar[n] と Δ[m] の内部 Hom の交換によって、gapped 全同値図式の対象と
Δ[m] から core(S_n C) への実際の族の間に厳密な同値を構成した。
Ar の制限との自然性と Yoneda 同値を用いて、m を固定した行の単体集合の同型
`objectCoreRowIso m C` に束ねた。単なる頂点の全単射でなく、全ての面・退化と可換する。

主要公開宣言（namespace `SerrePositivity.KST.SConstruction`、宇宙 `u`）：

```lean
lemma PreservesSConstructionData.of_functorIso {A B : SSet.{u}} [Quasicategory B]
    {f g : A ⟶ B} (hf : PreservesSConstructionData f) (e : FunctorIso f g) :
    PreservesSConstructionData g

lemma evaluateFunctorAt_preservesSConstructionData {K C : SSet.{u}}
    [Quasicategory C] [IsStable C] (k : K _⦋0⦌) :
    PreservesSConstructionData (evaluateFunctorAt (Y

lemma constantFunctor_evaluation {K C : SSet.{u}} (k : K _⦋0⦌) :
    curry (snd K C) ≫ evaluateFunctorAt k = 𝟙 C

lemma constantFunctor_preservesSConstructionData (K C : SSet.{u})
    [Quasicategory C] [IsStable C] : PreservesSConstructionData (curry (snd K C))

lemma equivalenceDiagramι_preservesSConstructionData (m : ℕ) (C : SSet.{u})
    [Quasicategory C] [IsStable C] :
    PreservesSConstructionData (equivalenceDiagramι (Δ[m] : SSet.{u}) C)

lemma isGapped_functor_iff_pointwise {n : ℕ} {K C : SSet.{u}}
    [Quasicategory C] [IsStable C] (F : arNerve n ⟶ (ihom K).obj C) :
    IsGapped F ↔ ∀ k : K _⦋0⦌, IsGapped (F ≫ evaluateFunctorAt k)

lemma isGapped_equivalenceDiagramι_iff {n m : ℕ} {C : SSet.{u}}
    [Quasicategory C] [IsStable C]
    (F : arNerve n ⟶ equivalenceDiagrams (Δ[m] : SSet.{u}) C) :
    IsGapped F ↔ IsGapped (F ≫ equivalenceDiagramι Δ[m] C)

instance diagramSpace_quasicategory (n : ℕ) (C : SSet.{u}) [Quasicategory C] :
    Quasicategory (diagramSpace n C)

def gappedFamilyLift {n : ℕ} {K C : SSet.{u}} (F : K ⟶ diagramSpace n C)
    (hF : ∀ k : K _⦋0⦌,
      IsGapped ((functorVertexEquiv (arNerve n) C).symm (F.app (Opposite.op ⦋0⦌) k))) :
    K ⟶ sConstruction n C

lemma gappedFamilyLift_ι {n : ℕ} {K C : SSet.{u}} (F : K ⟶ diagramSpace n C)
    (hF : ∀ k : K _⦋0⦌,
      IsGapped ((functorVertexEquiv (arNerve n) C).symm (F.app (Opposite.op ⦋0⦌) k))) :
    gappedFamilyLift F hF ≫ (gappedSubcomplex n C).ι = F

def coreGappedFamilyLift {n : ℕ} {K C : SSet.{u}} [Quasicategory C]
    (F : K ⟶ diagramSpace n C)
    (hF : ∀ k : K _⦋0⦌,
      IsGapped ((functorVertexEquiv (arNerve n) C).symm (F.app (Opposite.op ⦋0⦌) k)))
    (he : ∀ s : K _⦋1⦌,
      IsInvertibleEdge (edgeOfSimplex (F.app (Opposite.op ⦋1⦌) s))) :
    K ⟶ (quasicategoryCore (sConstruction n C) : SSet.{u})

lemma coreGappedFamilyLift_ι {n : ℕ} {K C : SSet.{u}} [Quasicategory C]
    (F : K ⟶ diagramSpace n C)
    (hF : ∀ k : K _⦋0⦌,
      IsGapped ((functorVertexEquiv (arNerve n) C).symm (F.app (Opposite.op ⦋0⦌) k)))
    (he : ∀ s : K _⦋1⦌,
      IsInvertibleEdge (edgeOfSimplex (F.app (Opposite.op ⦋1⦌) s))) :
    coreGappedFamilyLift F hF he ≫ (quasicategoryCore (sConstruction n C)).ι ≫
      (gappedSubcomplex n C).ι = F

lemma flipFamily_vertex {A B C : SSet.{u}} (F : A ⟶ (ihom B).obj C) (b : B _⦋0⦌) :
    (functorVertexEquiv A C).symm
      ((internalHomFlipHomEquiv A B C F).app (Opposite.op ⦋0⦌) b) =
      F ≫ evaluateFunctorAt b

lemma isInvertibleFunctorEdge_iff_pointwise {K C : SSet.{u}} [Quasicategory C]
    {x y : ((ihom K).obj C) _⦋0⦌}
    (e : SSet.Truncated.Edge (X

lemma flipEquivalenceDiagram_edge {A K C : SSet.{u}} [Quasicategory C]
    (F : A ⟶ equivalenceDiagrams K C) (s : K _⦋1⦌) :
    IsInvertibleEdge (edgeOfSimplex
      ((internalHomFlipHomEquiv A K C (F ≫ equivalenceDiagramι K C)).app
        (Opposite.op ⦋1⦌) s))

lemma flipGappedEquivalenceDiagram_vertex {n m : ℕ} {C : SSet.{u}}
    [Quasicategory C] [IsStable C]
    (F : arNerve n ⟶ equivalenceDiagrams (Δ[m] : SSet.{u}) C) (hF : IsGapped F)
    (k : (Δ[m] : SSet.{u}) _⦋0⦌) :
    IsGapped ((functorVertexEquiv (arNerve n) C).symm
      ((internalHomFlipHomEquiv (arNerve n) (Δ[m] : SSet.{u}) C
        (F ≫ equivalenceDiagramι Δ[m] C)).app (Opposite.op ⦋0⦌) k))

def gappedEquivalenceDiagramCoreMap {n m : ℕ} {C : SSet.{u}}
    [Quasicategory C] [IsStable C]
    (v : (sConstruction n (equivalenceDiagrams (Δ[m] : SSet.{u}) C)) _⦋0⦌) :
    (Δ[m] : SSet.{u}) ⟶ (quasicategoryCore (sConstruction n C) : SSet.{u})

lemma gappedEquivalenceDiagramCoreMap_ι {n m : ℕ} {C : SSet.{u}}
    [Quasicategory C] [IsStable C]
    (v : (sConstruction n (equivalenceDiagrams (Δ[m] : SSet.{u}) C)) _⦋0⦌) :
    gappedEquivalenceDiagramCoreMap v ≫ (quasicategoryCore (sConstruction n C)).ι ≫
      (gappedSubcomplex n C).ι =
      internalHomFlipHomEquiv (arNerve n) (Δ[m] : SSet.{u}) C
        (gappedDiagram v ≫ equivalenceDiagramι Δ[m] C)

lemma flipCoreGappedFamily_vertex {n : ℕ} {K C : SSet.{u}}
    (F : K ⟶ (quasicategoryCore (sConstruction n C) : SSet.{u}))
    (a : (arNerve n) _⦋0⦌) :
    IsEquivalenceDiagramVertex
      ((internalHomFlipHomEquiv K (arNerve n) C
        (F ≫ (quasicategoryCore (sConstruction n C)).ι ≫ (gappedSubcomplex n C).ι)).app
          (Opposite.op ⦋0⦌) a)

def coreGappedEquivalenceDiagram {n : ℕ} {K C : SSet.{u}}
    (F : K ⟶ (quasicategoryCore (sConstruction n C) : SSet.{u})) :
    arNerve n ⟶ equivalenceDiagrams K C

lemma coreGappedEquivalenceDiagram_ι {n : ℕ} {K C : SSet.{u}}
    (F : K ⟶ (quasicategoryCore (sConstruction n C) : SSet.{u})) :
    coreGappedEquivalenceDiagram F ≫ equivalenceDiagramι K C =
      internalHomFlipHomEquiv K (arNerve n) C
        (F ≫ (quasicategoryCore (sConstruction n C)).ι ≫ (gappedSubcomplex n C).ι)

lemma coreGappedEquivalenceDiagram_isGapped {n m : ℕ} {C : SSet.{u}}
    [Quasicategory C] [IsStable C]
    (F : (Δ[m] : SSet.{u}) ⟶ (quasicategoryCore (sConstruction n C) : SSet.{u})) :
    IsGapped (coreGappedEquivalenceDiagram F)

def coreGappedEquivalenceDiagramVertex {n m : ℕ} {C : SSet.{u}}
    [Quasicategory C] [IsStable C]
    (F : (Δ[m] : SSet.{u}) ⟶ (quasicategoryCore (sConstruction n C) : SSet.{u})) :
    (sConstruction n (equivalenceDiagrams (Δ[m] : SSet.{u}) C)) _⦋0⦌

def gappedEquivalenceDiagramVerticesEquiv (n m : ℕ) (C : SSet.{u})
    [Quasicategory C] [IsStable C] :
    (sConstruction n (equivalenceDiagrams (Δ[m] : SSet.{u}) C)) _⦋0⦌ ≃
      ((Δ[m] : SSet.{u}) ⟶ (quasicategoryCore (sConstruction n C) : SSet.{u}))

lemma gappedEquivalenceDiagramCoreMap_sMap {l n m : ℕ} {C : SSet.{u}}
    [Quasicategory C] [IsStable C] (θ : Fin (l + 1) →o Fin (n + 1))
    (v : (sConstruction n (equivalenceDiagrams (Δ[m] : SSet.{u}) C)) _⦋0⦌) :
    gappedEquivalenceDiagramCoreMap
        ((sMap (equivalenceDiagrams (Δ[m] : SSet.{u}) C) θ).app (Opposite.op ⦋0⦌) v) =
      gappedEquivalenceDiagramCoreMap v ≫ quasicategoryCoreMap (sMap C θ)

def objectCoreRowIso (m : ℕ) (C : SSet.{u}) [Quasicategory C] [IsStable C] :
    objectSConstruction (equivalenceDiagrams (Δ[m] : SSet.{u}) C) ≅
      simplicialCoreSConstruction C ⋙
        (evaluation SimplexCategoryᵒᵖ (Type u)).obj (Opposite.op ⦋m⦌)
```

前提：行の同型と全同値図式の gapped 判定は `[Quasicategory C] [IsStable C]`。
一般の gapped/core 族の持ち上げには、型に記した頂点条件と辺の可逆性を要求する。
これらの条件は元の gapped 全同値図式から証明しており、行の同型に追加仮定はない。

現在地：L1a・L1b 完了、L1c 継続中。D(m,w) の object S と core S の各行の同型まで証明済み。
定数包含との照合、元の `objectToCoreSRealization` の弱同値、McCarthy の具体的な単体ホモトピー、
単体積 Quillen A、加法性、面のホモトピー引き戻し条件は未完了。
反復 S 実現と §6.43 の homotopy fiber の比較、構造射との照合、正の段の Ω 条件・delooping、
負次数消滅を含む BF 連結スペクトルとスペクトル関手も未完了。L1d–f 未完了、L1g は別途指示待ち。
Core と他レーンの公開名・型は変更していない。

検証：対象ビルド成功（3198 jobs）、公理監査成功（1516 宣言、標準三公理のみ）。追加公理・sorry なし。
