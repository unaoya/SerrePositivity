# E∞ 代数のモデル圏（レーン E2）

作成日：2026-10-18。状態：計画。ε の経路として E2（モデル圏）を採用（2026-10-18 決定）。
全体の正本は [infinity-categories.md](infinity-categories.md) §0・§5。

## 0. 位置づけ

G1 の界面（perfectoid 化とその性質の束）を述べる場である CAlg_R を、
Ch(R) 上の E∞ オペラッド（Barratt–Eccles）の代数のモデル圏で実現する。
三段で進める。

| 段 | 内容 | 使い先 |
| --- | --- | --- |
| E2a（モデル圏まで） | オペラッド・Barratt–Eccles・E∞-dg 代数・転送モデル構造・右 Quillen な忘却関手・homotopy function complex | 界面の欄を「Alg_E の homotopy 引き戻し」「homotopy 写像空間」で述べる。γ を待たずに G1 の CAlg 版へ昇格できる |
| E2b（∞ 圏化、γ） | Alg_E の cofibrant 対象の単体的豊穣化と coherent nerve、homotopy 極限 = ∞ 極限、Quillen 随伴 = ∞ 随伴 | 界面を Lurie の言葉（quasicategory の引き戻し）で述べる。K 理論の Sp と共有 |
| E2c（BS の続き用） | 余単体的 E∞-dg 代数の Tot と余単体的可換環への E∞ 作用（Berger–Fresse）、単体的可換環のモデル圏と多項式解像度 | BS §4・§7・§8 の構成 |

E1（∞ オペラッド）は採らない。後で HA の定理を文字どおり引用したくなった場合に、
E2b ≃ E1 の比較（HA 4.5.4.7 型の rectification）を任意項目として検討する。

## 1. 既存資産

- `HomotopicalAlgebra/`：Mathlib `ModelCategory` 上の Quillen 随伴（H1）、Under（H2）、
  転送（`Transfer/Recognition.lean`：生成類から Mathlib の `ModelCategory` を構成、acyclicity は明示仮定；
  `Transfer/Right.lean`：右随伴が fibration と弱同値を作る転送）、Smith の定理、
  Bousfield 局所化、Reedy、`HomotopyFunctionComplex/`（frame による導来写像空間）、
  `Monoidal/`（モノイダルモデル圏、monoid axiom）。
- `Spectra/SymmetricSequence/`：対称列と Day 畳み込み（オペラッドの合成積の素材）。
- `DifferentialGraded/Complexes/Cells.lean`：`complexSphere`・`complexDisk`（射影モデル構造の生成 cofibration）。
- `InfinityCategories/Derived/`：semifree の閉性（cone・fiber・直和・テンソル・底変更）。
- Mathlib：`SmallObject`、`CategoryWithCofibrations/Fibrations/WeakEquivalences`、`ModelCategory`。
- 未整備：Ch(A) の非有界射影モデル構造（Mathlib は `CochainComplex.Plus` の injective のみ）、
  オペラッド、対称群作用つき複体。

## 2. E2a の工程

| 工程 | 内容 | 原典 |
| --- | --- | --- |
| E2a-0 | Ch(A) の非有界射影モデル構造：弱同値 = 擬同型、fibration = 各次数全射、生成 cofibration `complexSphere (n+1) → complexDisk n`、生成 trivial cofibration `0 → complexDisk n`。`Transfer/Recognition.lean` で構成 | Hovey, Model Categories 2.3.11 |
| E2a-1 | Ch(A) 上の対称オペラッド：各 arity n の複体 P(n) と Σ_n 右作用、合成、単位。代数、代数の射、自由代数 Sym_P（⊕ (P(n) ⊗ A^{⊗n})_{Σ_n}）、自由 ⊣ 忘却 | Loday–Vallette、Berger–Moerdijk 2003 §1 |
| E2a-2 | Barratt–Eccles オペラッド E：EΣ_n（Σ_n の translation 亜群の nerve）の正規化鎖。各 arity が可縮、Σ-cofibrant（各 E(n) が Σ_n 上自由な次数ごとの基底を持つ）、E → Com | Barratt–Eccles 1974、Berger–Fresse 2004 §1 |
| E2a-3 | Alg_E の転送モデル構造：弱同値・fibration は忘却で作る。`Transfer/Right.lean` を適用。acyclicity（生成 trivial cofibration の自由代数の pushout が弱同値）は Berger–Moerdijk §5／Hinich の filtration 議論で証明 | Hinich 1997 Thm 4.1.1、Berger–Moerdijk 2003 Thm 4.1 |
| E2a-4 | U : Alg_E → Ch(A) は右 Quillen、全対象 fibrant、homotopy 引き戻し・homotopy 極限は底で計算。E 代数の H⁰ が可換環であること、離散可換代数は E 代数（E → Com 経由） | 同上 |
| E2a-5 | homotopy function complex Map^h(A, B)（`HomotopyFunctionComplex/` の frame を Alg_E に適用）、π₀ Map^h = Ho(Alg_E) の Hom | Hovey §5、Dwyer–Kan |

## 3. E2b（γ）の工程

| 工程 | 内容 | 原典 |
| --- | --- | --- |
| γ1 | 局所 Kan な単体的圏の coherent nerve は quasicategory（Mathlib `SimplicialNerve` に対して） | HTT 1.1.5.10、Kerodon 2.4.5.1 |
| γ2 | Alg_E の cofibrant 対象の単体的豊穣化（Hopf オペラッド E による B ⊗ N^*(Δ^•) 型、または Dwyer–Kan 単体的局所化）と CAlg_R := N^hc | Berger–Moerdijk 2006、Hinich、Dwyer–Kan |
| γ3 | homotopy 極限 = ∞ 極限、右 Quillen ⇒ ∞ 極限保存、Quillen 随伴 ⇒ ∞ 随伴 | HTT 4.2.4.1、5.2.4.6 |

γ2 の単体的豊穣化が E2b の最大のリスクである。E2a の完了時点で方式を決める。

## 4. 受入基準と記録

dg-nerve.md §4 と同じ（ビルド、標準 3 公理、docstring、計画への記録）。
配置は `SerrePositivity/EInfinity/`（E2a）、namespace `SerrePositivity.EInfinity`。
集約ファイルをルートに 1 行で追加する。既存の `HomotopicalAlgebra/`・`Spectra/` は編集せず、
必要な一般補題は新規ファイルに置く。

## 5. 記録

（各工程の完了時に追記する。）

### E2a-0

```lean
universe u
open CategoryTheory Limits HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.EInfinity
variable (A : Type u) [CommRing A]

projectiveGeneratingCofibrations : MorphismProperty (Complex A)
projectiveGeneratingTrivialCofibrations : MorphismProperty (Complex A)
projectiveFibrations : MorphismProperty (Complex A)

disk_lifting_iff_surjective {K L : Complex A} (f : K ⟶ L) (n : ℤ) :
  HasLiftingProperty (0 : (HomologicalComplex.zero : Complex A) ⟶ complexDisk A n) f ↔
    Function.Surjective (f.f n)

projectiveGeneratingTrivialCofibrations_rlp :
  (projectiveGeneratingTrivialCofibrations A).rlp = projectiveFibrations A

sphereToDisk_lifting_iff {K L : Complex A} (f : K ⟶ L) (n : ℤ) :
  HasLiftingProperty (complexSphereToDisk A n) f ↔ complexBoundaryLiftAt A f n

projectiveGeneratingCofibrations_rlp :
  (projectiveGeneratingCofibrations A).rlp =
    projectiveFibrations A ⊓ HomologicalComplex.quasiIso (ModuleCat A) (.up ℤ)

sphere_finitelyPresentable (n : ℤ) : IsFinitelyPresentable.{u} (complexSphere A n)
zero_finitelyPresentable : IsFinitelyPresentable.{u} (HomologicalComplex.zero : Complex A)

projectiveGeneratingCofibrations_smallObjectArgument :
  (projectiveGeneratingCofibrations A).HasSmallObjectArgument.{u}

projectiveGeneratingTrivialCofibrations_smallObjectArgument :
  (projectiveGeneratingTrivialCofibrations A).HasSmallObjectArgument.{u}

projectiveGeneratingTrivialCofibrations_acyclic :
  (projectiveGeneratingTrivialCofibrations A).rlp.llp ≤
    HomologicalComplex.quasiIso (ModuleCat A) (.up ℤ)

projectiveFibrationStructure : HomotopicalAlgebra.CategoryWithFibrations (Complex A)
projectiveWeakEquivalenceStructure : HomotopicalAlgebra.CategoryWithWeakEquivalences (Complex A)
projectiveCofibrationStructure : HomotopicalAlgebra.CategoryWithCofibrations (Complex A)
projectiveModelCategory : HomotopicalAlgebra.ModelCategory (Complex A)

projectiveModelCategory_weakEquivalences :
  @HomotopicalAlgebra.weakEquivalences (Complex A) _
    (projectiveModelCategory A).categoryWithWeakEquivalences =
      HomologicalComplex.quasiIso (ModuleCat A) (.up ℤ)

projectiveModelCategory_fibrations :
  @HomotopicalAlgebra.fibrations (Complex A) _
    (projectiveModelCategory A).categoryWithFibrations = projectiveFibrations A

projectiveModelCategory_cofibrantlyGenerated :
  letI := projectiveModelCategory A
  SerrePositivity.ModelGeneration.CofibrantlyGenerated.{u}
    (projectiveGeneratingCofibrations A) (projectiveGeneratingTrivialCofibrations A)

end SerrePositivity.EInfinity
```

### γ1：局所 Kan な単体的圏の coherent nerve（完了）

配置・namespace：`InfinityCategories/Coherent/`、
`SerrePositivity.InfinityCategories.Coherent`。集約は `InfinityCategories/Coherent.lean`。

```lean
simplicialNerve_quasicategory (C : Type u)
    [CategoryTheory.Category.{v} C] [CategoryTheory.SimplicialCategory C]
    [∀ X Y : C, SSet.KanComplex (CategoryTheory.SimplicialCategory.sHom X Y)] :
    SSet.Quasicategory (CategoryTheory.SimplicialNerve C)
```

| 主要な構成 | 宣言・型の所在 |
| --- | --- |
| 空洞部分の Kan 延長 | `hornHollowHom_extension`：内部ホーンと端点 Hom の Kan 性から、全ての既知面を固定する全区間 Hom の写像が存在 |
| 豊穣関手への復元 | `hornFilledFunctor`：その延長と面の制限則から thickening 上の `EnrichedFunctor SSet` |
| 元のホーンとの一致 | `hornFilledFunctor_face`：各 `j ≠ i` で復元した単体の `δ j` が `σ.app _ (horn.face i j hj)` に等しい |

全234宣言の正確な型・前提・依存公理は `scripts/audit_coherent_nerve.lean` の
`#check @`・`#print axioms` が正本。数学は `InfinityCategories/README.md` の γ1 節。
実施の経緯・検証はコミットに置く。追加の充填・整合性仮定はない。

### γ1.5：Dold–Kan 豊穣化と dg nerve の比較（進行中）

前提は `[CommRing R] [DGCategory R D]`。namespace は `DoldKanComparison`。
γ1.5a の設計と符号は `InfinityCategories/README.md` に記録済み。
γ1.5b の単体的圏と局所 Kan 性、γ1.5c の比較写像と低次の一致は完了。

```lean
standardDoldKanModuleIso (x y : D) : standardModule x y ≅ doldKanHomModule x y
homModuleDoldKanIso (x y : D) : homModule x y ≅ doldKanHomModule x y
doldKanSimplicialCategory : SimplicialCategory (ClosedCategory R D)
doldKanSimplicialCategory_locallyKan (x y : ClosedCategory R D) :
  SSet.KanComplex (SimplicialCategory.sHom x y)
doldKanCoherentNerve : SSet.{max u v}
coherentSimplex {n : ℕ} (s : doldKanCoherentNerve _⦋n⦌) : DGNerve.Simplex R D n
coherentComparison : doldKanCoherentNerve (R := R) (D := D) ⟶ dgNerve R D
coherentComparison_essentiallySurjective : IsEssentiallySurjective
  (coherentComparison (R := R) (D := D))
coherentPinchedStandardComparison (x y : D) :
  coherentPinchedHom (R := R) x y ⟶
    SSet.uliftFunctor.{v,u}.obj (standardHomSpace (R := R) x y)
standardHomToCoherentPinched (x y : ClosedCategory R D) :
  SSet.uliftFunctor.{v,u}.obj (standardHomSpace (R := R) (D := D) x y) ⟶
    coherentPinchedHom (R := R) (D := D) x y
standardHomToCoherentPinched_comp (x y : ClosedCategory R D) :
  standardHomToCoherentPinched (R := R) x y ≫
    coherentPinchedStandardComparison (R := R) (D := D) x y = 𝟙 _
coherentComparison_fullyFaithful_iff_standard :
  IsFullyFaithful (coherentComparison (R := R) (D := D)) ↔
    ∀ x y : D,
      IsSimplicialHomotopyEquivalence (coherentPinchedStandardComparison (R := R) x y)
```

Hom を実際の Mathlib Γ と自然同型で同定し、AW の全豊穣則と方程式の保存を証明済み。
`coherentSimplexData_equation` が立方体評価による全ての既存 dg 方程式を証明する。
`coherentSimplex_pullback` は全単調写像で引き戻しと可換で、退化も含む。
`coherentComparison_obj`・`coherentComparison_edgeHom`・`coherentComparison_triangleHom` は
対象、二端点だけの Path の零成分、`{0,2} → {0,1,2}` の旗の次数 −1 の成分との一致。
三角形に追加の負号はない。追加の単射性・整合性・充填の仮定はない。

γ1.5d では全頂点を対象から再構成する `coherentVertexEquiv` を構成し、本質的全射性を証明済み。
`coherentPinchedComparison` は実際の pinched Hom の射、標準座標での各成分は N4 回収成分に
`degreeSign (J.card−1)` を掛けた値。全ての面・退化と可換である。
`standardHomToCoherentPinched` は F1 の確定済みの最大頂点の構成と自然性から得る逆向きの射。
`cubeEvaluation_maximum` は降順立方体の評価が唯一の昇順旗の評価に `degreeSign m` を掛けた値と証明する。
`standardHomToCoherentPinched_comp` は片側の合成が全次数で厳密に恒等となることを証明する。
昇順旗の像の同定と端点の移送から実際の成分を計算し、次数符号の二重作用を相殺する。
`coherentPinchedComparison_eq_pinchedHomMap` は固定端点の射を Core の射の端点移送に厳密に同定する。
全頂点の再構成と自然同型による移送により、標準座標の射での充満忠実性の判定も完成した。
F1 の補助解像の旗を native Path に送り、最大元と末尾への正規化した引き戻しを同定した。
`resolutionHomValue s F : StandardSimplex R x y d` は各旗での実際の Hom 写像の値。
`resolutionHomValue_standard` は標準 Hom からの射の値を最大元での引き戻しに同定する。
`resolutionHomValue_pullback` は固定した任意の s について旗の全ての引き戻しとの可換性を証明する。
`resolutionHomMap s : coherentResolutionSimplex n ⟶ standardHomSpace x y` は実際の単体集合の射。
`resolutionHomMap_standard` は標準単体から来る場合に最大元の射影を通る射へ同定する。
`resolutionHomMap_reindex` は s の面・退化と `coherentResolutionMap` の前合成との整合を証明する。
旗の押し出しと Path の像の一致から導き、旗と s の両方の次数について自然性が揃った。
`resolutionHomEquiv x y n` は固定次数の pinched 単体と解像から標準 Hom への射の型の同値。
実際の `resolutionHomMap` を F1 の確定済みの構成に厳密に同定し、両側の回収則を移した。
逆構成の面・退化との整合も `resolutionHomEquiv_symm_reindex` で証明済み。
`resolutionHomIso` はこれを単体集合の同型にまとめる。
`standardHomToCoherentPinched_resolutionHomIso` は逆向きの射を解像の標準比較射へ厳密に同定する。
`coherentComparison_fullyFaithful_iff_resolution` は厳密な片側の逆と Kan 性を使い、
充満忠実性を全ての標準 Hom に対する解像の標準比較射の実際のホモトピー同値性と同値にする。
残りはこの右辺の証明と ∞ 圏の同値。一般の解像の境界の貼り合わせは未接続。
低次の基底では `resolutionProjectionIsoOfLeOne` が `n ≤ 1` の解像の射影を厳密な同型にする。
`standardCoherentPinchedEquivOfLeOne` は同じ次数での標準 Hom と coherent pinched 単体の同値。
逆方向は実際の標準比較射で、反対側の合成も単体上で厳密に恒等となる。高次の同値性は未証明。
`normalizeResolutionFlag` は一般の増大集合族を最初の最大元で正規化し、全引き戻しと可換。
`resolutionInsertHomotopy i` は解像の恒等射から `k ↦ max i k` の押し出しへの実際のホモトピー。
選んだ i 以外の頂点を追加しないことも証明済み。
`resolutionHornInsertHomotopy i` は台で定義したホーンの旗の部分複体内への制限。
i ≠ 0 では終端の射が零頂点を除く面を通る厳密な因子分解も証明済み。
ホーンの左 Kan 拡張との同定、縮約の完成、比較射の反対側の合成のホモトピーは未証明。
Kan 標的の前合成の実際のホモトピー同値性を使い、向き付きホモトピー不変性と二対六則を証明した。
`resolutionPositiveFace_inclusion_isKanPrecompositionEquivalence` は i ≠ 0 のホーンの旗の模型に
零頂点を除く旗の面を含める射について、この条件を証明する。
標準ホーン側も同じ面の包含の比較を証明し、面の射影の可換正方形で解像側へ接続した。
`resolutionHornProjection_isKanPrecompositionEquivalence_of_ne_zero` は i ≠ 0 のホーンの射影が
任意の Kan 標的への写像空間で実際のホモトピー同値を与えることを証明する。
i = 0、ホーンの左 Kan 拡張との同定、一般の解像の比較の同値性は未証明。
判定への移送や片側の逆の性質だけでは、充満忠実性やホモトピー同値を証明したとは数えない。
A3e の `qCatEquivalenceOfFullyFaithfulEssentiallySurjective` は実装済みで、写像空間の比較後に適用する。

公開625宣言の正確な型・全前提・依存公理は `scripts/audit_dold_kan_comparison.lean` の
`#check @`・`#print axioms` が正本。依存公理は標準三公理のみ。
詳しい API と数学は `InfinityCategories/README.md`、整理前の索引は
[archive/e-infinity-algebras-gamma1.5-api.md](archive/e-infinity-algebras-gamma1.5-api.md) を参照する。
