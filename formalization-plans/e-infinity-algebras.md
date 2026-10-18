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

### γ1.5：Dold–Kan 豊穣化と dg nerve の比較（完了）

前提は `[CommRing R] [DGCategory R D]`。namespace は `DoldKanComparison`。
正本の数学・符号・設計は `InfinityCategories/README.md` に置く。

| 工程 | 完成した内容 |
| --- | --- |
| γ1.5a | 比較の向き `N^hc(C_Δ) → N_dg(C)`、切断と次数・AW の符号、写像空間による証明方針 |
| γ1.5b | Hom を実際の Mathlib Γ と自然同型で同定、全 AW 豊穣則、局所 Kan 性と coherent nerve |
| γ1.5c | 全ての面・退化と可換な比較射、頂点・辺・三角形の成分の一致 |
| γ1.5d | 実際の pinched 比較射のホモトピー逆、充満忠実性と本質的全射性、A3e による同値 |

```lean
standardDoldKanModuleIso (x y : D) : standardModule x y ≅ doldKanHomModule x y
doldKanSimplicialCategory : SimplicialCategory (ClosedCategory R D)
doldKanSimplicialCategory_locallyKan (x y : ClosedCategory R D) :
  SSet.KanComplex (SimplicialCategory.sHom x y)
coherentComparison : doldKanCoherentNerve (R := R) (D := D) ⟶ dgNerve R D
coherentComparison_obj {n : ℕ} (s : doldKanCoherentNerve _⦋n⦌) (a : Fin (n + 1)) :
  (coherentComparison.app (Opposite.op ⦋n⦌) s).obj a = s.obj (.mk (ULift.up a))
coherentPinchedStandardComparison_homotopyEquivalence (x y : ClosedCategory R D) :
  IsSimplicialHomotopyEquivalence
    (coherentPinchedStandardComparison (R := R) (D := D) x y)
coherentPinchedComparison_homotopyEquivalence (x y : D) :
  IsSimplicialHomotopyEquivalence (coherentPinchedComparison (R := R) (D := D) x y)
coherentComparison_fullyFaithful : IsFullyFaithful (coherentComparison (R := R) (D := D))
coherentComparison_essentiallySurjective :
  IsEssentiallySurjective (coherentComparison (R := R) (D := D))
coherentComparisonEquivalence :
  QCatEquivalence (doldKanCoherentNerve (R := R) (D := D)) (dgNerve R D)
coherentComparisonEquivalence_hom :
  (coherentComparisonEquivalence (R := R) (D := D)).hom =
    coherentComparison (R := R) (D := D)
coherentComparison_isQCatEquivalence :
  IsQCatEquivalence (coherentComparison (R := R) (D := D))
```

頂点は元の対象、辺は二端点だけの Path の零成分、三角形は `{0,2} → {0,1,2}` の旗の
次数 −1 の成分に一致する。三角形に追加の負号はない。
`standardHomToCoherentPinched_comp` は逆順の合成の厳密な恒等式、
`coherentPinchedStandardComparison_oppositeHomotopy` は同じ二射の反対側の合成の実際のホモトピー。

F1 の確定済みの一般の解像の射影の同値性により、余単位をホモトピーまで降下する。
円筒の比較と随伴によるホモトピーの転置、前合成による反映で両合成を計算する。
`resolutionComparison_homotopyEquivalence K` の前提は K の Kan 性のみで、
右随伴の値の Kan 性を追加しない。この逆を宇宙の持ち上げで移し、既存の判定から
具体的な比較射の充満忠実性を得て A3e に適用した。
局所ホーン補題の i = 0 への拡張は最終証明に必要としない。
γ1.5 の未完了項目はない。E2b 本体と γ3 は後続の別工程。

公開645宣言の正確な型・全前提・依存公理は `scripts/audit_dold_kan_comparison.lean` の
`#check @`・`#print axioms` が正本。依存公理は標準三公理のみ。
詳しい API と数学は `InfinityCategories/README.md`、整理前の索引は
[archive/e-infinity-algebras-gamma1.5-api.md](archive/e-infinity-algebras-gamma1.5-api.md) を参照する。
実施の経緯と検証はコミットメッセージに置く。

### γ3：homotopy 極限と ∞ 極限の比較（進行中）

正本は本書 §3 と `foundations.md` §1。γ1.5 の後に N が担当し、𝒮（F2）・Sp（L9）・E2b が共有する。
γ3a の紙の限定形と証明方針は `InfinityCategories/README.md` に記録済み。
HTT 4.2.4.1 の双対と Kerodon Corollary 7.5.4.6 を基準とする。
局所 Kan な単体的圏 C の strict な錐について、全ての x で
`sHom(x,L) ≅ lim_I sHom(x,F−) → holim_I sHom(x,F−)` が同値なら極限錐となる形を採用する。
可縮性を検出する対象はこの比較の導来ファイバーで、strict な Hom の極限自体ではない。

| 工程 | 現在地 |
| --- | --- |
| γ3a | 限定した主張、原典、仮定、pinched Hom による検出、適用条件と宇宙を記録済み |
| γ3b | q′ の切断比較と native な制限の主可換式を証明。局所 Kan 性と Hom 極限条件から、離散図式・一脚 fibration の cospan・fibration の塔の strict な錐が ∞ 極限錐となる定理を公開。元の非反転の end・q_x と反転係数の直接比較は未完了 |
| γ3c | 𝒮 の実際の任意の小さい積、一脚 Kan fibration の引き戻し、Kan fibration の可算塔の極限を既存の図式上の IsLimitCone として公開。台と Kan 複体の圏の普遍性、全 Hom 条件も検証済み。Sp は未完了 |

Sp では raw sHom の局所 Kan 性と極限の cofibrancy を省略せず、必要なら cofibrant-fibrant
置換後の錐を公開する。実装は `InfinityCategories/HomotopyLimits/` と専用監査に置く。

γ3b の部分 API は `HomotopyLimits` 集約と `scripts/audit_homotopy_limits.lean` に置く。
公開844宣言。`representableHomotopyLimitComparison c x` は実際の sHom から end への射、
`representableHomotopyLimitComparison_factorization c x h` は θκ への厳密な分解、
`representableHomotopyLimitComparison_naturality c f` は始対象に関する厳密な自然性。
重み付き end の普遍性・通常の随伴と極限保存も公開。正確な型と数学は README に置く。
coherent な錐から end の点への対応と pinched Hom の fiber 比較が未完了なので、γ3b は未完了。

離散図式では実際の κ_x と、豊穣積の Hom の極限性を前提とする q_x の同型性を証明済み。
`spaceEmptyProductCone_isLimitCone : IsLimitCone spaceEmptyProductCone` は追加の比較仮定なし。
`towerLimit_kanComplex` は零段の Kan 性と隣接遷移の Fibration 性、
`towerLimitπ_zero_fibration` は隣接遷移の Fibration 性のみを前提とする。
Sp の接続先は `KST/Spectra/CoherentNerve.lean` の L9 の Ω スペクトルの coherent nerve。

`strictCoherentDiagram F` と `strictCoherentCone c` は実際の SSet の図式と JoinCone。
対象・Hom の宇宙を区別し、始域は明示的な ULift N(I)。
`strictCoherentCone_vertex` と `strictCoherentConeLeg_eq` は頂点と各脚を元の strict な錐と同定する。
局所 Kan 性・極限性・一般の coherent な錐の strict 化をこの構成の前提にしない。

`weightedSections_tower_kanComplex` と `bousfieldKanHolim_tower_kanComplex` は零段の Kan 性と
隣接遷移の Fibration 性で塔の end の Kan 性を証明。重みは任意で、添字は AsSmall.{u} ℕᵒᵖ。
`weightedSectionsPre_tower_exists_section` は成分ごとに anodyne な重みの制限の厳密な切断を構成。
`weightedSectionsPre_tower_trivialKanFibration` と
`weightedSectionsPre_tower_homotopyEquivalence` は同じ前提で、制限そのものの
trivial Kan fibration 性と単体的ホモトピー同値性を証明する。
重みと境界の pushout-product に沿う相対的延長を用いる。正確な型は README と監査に記録。
塔で κ_x に適用する重みの比較は実装済み。coherent な錐の写像空間の比較は未完了。

補助重み V(i) = N(WithInitial(I/i)) と W → V、U = 定値 Δ[0] → V を構成した。
`bousfieldKanConeWeightPoint_tower_trivialKanFibration` は零段 Kan・隣接遷移 Fibration の
塔で一点側の制限が trivial Kan fibration であることを証明する。
`bousfieldKanConeWeightComparison_tower_homotopyEquivalence c hc` は同じ前提と `IsLimit c` から、
strict な錐の頂点から V の end への比較射のホモトピー同値性を証明する。
c.pt の Kan 性は結論に必要な証明の中で導出する。
`bousfieldKanConeComparison_factorization c` はその射の後で W に制限すると元の κ になる式。
W → V の成分ごとの anodyne 性は、nerve の反転同型と共通の終対象を保つ単射の
right anodyne 性から証明した。その end の制限は trivial Kan fibration。
`bousfieldKanLimitComparison_tower_homotopyEquivalence H` は零段 Kan・隣接遷移 Fibration の
塔について実際の κ の単体的ホモトピー同値性を証明する。
`representableHomotopyLimitComparison_tower_homotopyEquivalence c x hc` は同じ Hom 図式の
条件と `IsLimit (simplicialHomCone c x)` の下で実際の q_x の同値性を証明する。
正確な型・全前提は README と公開844宣言の監査に記録。
一般の coherent な錐の写像空間との比較は未完了なので、γ3b の完成とは数えない。

両脚が fibration の cospan では、中央の Kan 性から成分ごとの anodyne な自然変換を延長する。
その具体的な延長により、重み付き end の Kan 性と anodyne な制限の trivial Kan fibration 性、
`bousfieldKanLimitComparison_cospan_homotopyEquivalence` および
`representableHomotopyLimitComparison_cospan_homotopyEquivalence` を証明する。
後者には Hom 図式の極限性も必要。正確な型・全前提は README と公開844宣言の監査が正本。
一般の延長性を入力とする `WeightedExtensions` と `BousfieldKanComparison` を使うが、
cospan の結論ではその入力を実際の三成分の持ち上げから構成している。

一脚の fibration 性への準備は `cospanRightCornerMap j` と
`exists_resized_cospan_extension_of_rightCorner`。
右成分と中央が Kan、左脚が fibration の下で、左右の成分と中央の相対境界が anodyne なら延長できる。
中央の境界は A(one) ⨿_{A(right)} B(right) → B(one)。右脚の fibration 性は要求しない。
ホーンとの直積の相対境界の anodyne 性は実装済み。重みの制限と境界の pushout-product の
相対境界は交換同型で元の相対境界に帰着する。元の重みの相対境界と一脚での κ は末尾の実装で証明した。
coherent な錐の写像空間の比較と 𝒮・Sp の ∞ 引き戻しへの適用は未完了。

一脚だけが fibration の cospan の end の Kan 性は
`weightedSections_cospan_leftFibration_kanComplex` と
`bousfieldKanHolim_cospan_leftFibration_kanComplex`。
前提は中央・右端の Kan 性と左脚の Fibration 性で、一般の重み W では右脚の Mono 性も要求する。
`cospanRightCorner_tensor_anodyne` と持ち上げ版は、中央の相対境界を pushout-product と同定する。
`bousfieldKanWeight_map_mono` は添字の単射から重みの遷移の単射性を証明するので、
Bousfield–Kan 重みに追加の未証明条件はない。正確な型は README と公開844宣言の監査に記録。
元の重みの相対境界と一脚での κ の同値性は末尾の実装で証明した。
coherent な錐の写像空間との比較と 𝒮・Sp への適用は未完了。

`cornerTensorIso j f` は重みの相対境界と pushout-product の二つの順序の間の交換同型。
`cornerTensorComparison_fac` は実際の相対境界射との可換性で、交換自体に Kan 性・単射性は不要。
`rightCorner_weightedCorner_anodyne` は元の重みの相対境界が anodyne、f が Mono のとき、
pushout-product の相対境界が anodyne であることを証明する。
これにより `weightedSectionsPre_cospan_leftFibration_trivialKanFibration` は中央と右端が Kan、
左脚が Fibration の cospan に対して、成分と元の中央の相対境界が anodyne な重みの制限を扱う。
`weightedSectionsPre_cospan_leftFibration_homotopyEquivalence` では両重みの右脚の Mono 性も要求する。
正確な型・全前提は README と公開844宣言の監査に記録。
元の重みの相対境界と一脚での κ の同値性は末尾の実装で証明した。
coherent な錐の写像空間との比較と 𝒮・Sp への適用は未完了。

一点重み U → V の相対境界は `bousfieldKanConeWeightPoint_cospan_corner_anodyne` で検証済み。
補助重みは添字の単射に沿って新しい始対象を保つ nerve の単射となるため anodyne で、
定値一点の右脚の同型性から相対境界へ移す。
`bousfieldKanConeWeightPoint_cospan_leftFibration_trivialKanFibration` は中央・右端が Kan、
左脚が Fibration の H に対する一点側の実際の制限を扱う。
`bousfieldKanConeWeightComparison_cospan_leftFibration_homotopyEquivalence H c hc` は
同じ前提と `IsLimit c` の下で strict 極限から補助 end への比較射の同値性を証明する。
頂点の Kan 性は導出し、追加の境界条件や右脚の fibration 性は要求しない。
正確な型・全前提は README と公開844宣言の監査に記録。
元の重み W → V の相対境界とその制限、一脚の場合の κ 全体は末尾の実装で証明した。
coherent な錐の写像空間との比較と 𝒮・Sp の適用は未完了。

元の重みの右脚の遷移は `bousfieldKanWeight_cospan_inr_anodyne` で anodyne と証明済み。
右端の over 圏の恒等射の始対象性と、中央の over 圏の恒等射の終対象性を使い、
終対象を付加する中間圏で left と right の anodyne な単射に分解する。
`joinUnion_pointBoundary_anodyne` は anodyne な部分複体の包含から作る相対的な点の錐を扱い、
`bousfieldKanWeight_cospan_inr_relativeCone_anodyne` は実際の遷移の像に適用した定理。
外側の最後のホーンも含む相対 coslice の Kan fibration 性から証明する。
正確な型・全前提は README と公開844宣言の監査に記録。
この相対錐と標準境界の同定、一脚の場合の κ 全体は末尾の実装で証明した。
coherent な錐の写像空間との比較と 𝒮・Sp の適用は未完了。

WithInitial の nerve と点の join の同定のため、射列の切断と元の圏の後半を構成した。
`initialNerveCut` は始対象を 0、元の対象を 1 に送る単調写像の先頭区間の逆像の頂点数。
`initialNerveCut_precomp` は全ての単体作用素との可換性、`initialNerveCut_map` は関手による保存。
`initialNerveOldFunctor` は全対象が新しい始対象でない部分を元の圏へ戻し、恒等・合成を保つ。
`initialNerveTail` は切断以後の射列、`initialNerveJoinSimplex` は次数ごとの join 型のデータ。
後半が空のときは補った空単体を使い、元の圏の非空性は要求しない。
正確な型・全前提は README と公開844宣言の監査に記録。
全データの単体的自然性と逆関係は下記の同型で証明した。
相対錐と標準境界の同定と一脚での κ は末尾の実装で証明した。
coherent な錐の写像空間との比較と 𝒮・Sp の適用も未完了。

点と nerve の join 型の単体から WithInitial の射列への逆向きの次数ごとの構成を追加した。
`augNerveObj`・`augNerveMap` は補った空単体を含む評価で、恒等・合成・再添字付けを保つ。
零頂点の場合は空の添字で処理し、元の圏の対象を選ばない。
`initialJoinChain` は切断より前を新しい始対象、後を元の射列としてつなぐ。
`initialJoinChain_star_iff` と `initialNerveCut_initialJoinChain` により切断が元に戻る。
C : Type u、[SmallCategory C] のみを仮定し、追加の非空性・忠実性は要求しない。
正確な型・全前提は README と公開844宣言の監査に記録。
単体的自然性と全データの両向きの逆関係、単体集合の同型は下記の三ファイルで証明した。
相対錐と標準境界の同定と一脚での κ は末尾の実装で証明した。
coherent な錐の写像空間との比較、
𝒮・Sp の適用も継続中。

`InitialJoinNaturality`・`InitialJoinRetraction`・`InitialJoinIso` により、
`initialJoinNerveIso (C : Type u) [SmallCategory C] :
join (Δ[0] : SSet.{u}) (nerve C) ≅ nerve (WithInitial C)` を構成した。
任意の単体作用素と可換な射列への復元を作り、切断と後半の全対象・全射を比較して単射性を証明する。
`initialJoinChain_initialNerveJoinSimplex` と `initialNerveJoinSimplex_initialJoinChain` は
全データの両向きの厳密な逆関係。逆射の自然性も導出した。
元の圏の非空性や Kan 性は要求しない。正確な型・全前提は README と公開844宣言の監査に記録。
両端の包含と関手との可換性も末尾の実装で証明した。既存の始対象の錐の射との一致は未完了。
相対錐と標準境界の同定と一脚での κ は末尾の実装で証明した。
coherent な錐の写像空間との比較、
𝒮・Sp の適用も継続中。

`InitialJoinFaces` と `InitialJoinFunctor` で、同型の順方向と両端の包含および任意の関手との
厳密な可換性を証明した。`PointJoinCorner` は像と空 join の同型を使い、相対錐を
`pushout f (joinInr Δ[0] A) → join Δ[0] B` と同型で表示する。
`InitialNerveCorner` はこの結果を始対象の付加の四角形へ移し、元の nerve の写像が
単射かつ anodyne なら相対境界も anodyne であることを証明した。
`CospanSingleFibrationComparison` はこれを実際の W → V に適用し、
`bousfieldKanConeWeightInclusion_cospan_corner_anodyne` を公開する。
この重みの制限の trivial Kan fibration 性と単体的ホモトピー同値性を得て、
一点側の同値と合成し、実際の κ の同値性を
`bousfieldKanLimitComparison_cospan_leftFibration_homotopyEquivalence H` として証明した。
H : AsSmall.{u} WalkingCospan ⥤ SSet.{u} に対し、中央・右端の Kan 性と左脚の Fibration 性だけを要求する。
任意の極限錐 c と IsLimit c に対する版も公開し、極限頂点の Kan 性は導出する。
`representableHomotopyLimitComparison_cospan_leftFibration_homotopyEquivalence c x hc` は
Hom 図式の同じ条件と hc : IsLimit (simplicialHomCone c x) の下で、実際の q_x の同値性を証明する。
右脚の Fibration 性や未証明の境界条件は追加しない。正確な型・全前提は README と公開844宣言の監査が正本。
coherent な錐の pinched Hom と導来ファイバーの主比較、𝒮・Sp の残りの ∞ 極限は未完了。

γ3b の主比較へ向け、重み付き end と weighted nerve の切断空間の対応の順方向を構成した。
`PrefixOverWeight` は射列の各初区間を終点の over 圏へ持ち上げ、終点の後合成および任意の
単体作用素との可換性を証明する。`prefixOverWeight σ` は初区間の重みから Bousfield–Kan 重みへの自然変換。
`WeightedNerveCoefficients` はこの標準単体とパラメータの制限を直積へまとめ、
η : bousfieldKanWeight I ⊗ const A ⟶ H で評価した係数の全ての面・退化との整合性を証明する。
`WeightedNerveSections` の `weightedNerveSectionFromTransform η` は
`nerve I ⊗ A ⟶ weightedNerve H` で、射影との合成は厳密に第一射影に一致する。
`bousfieldKanWeightedNerveEvaluation H` は同じ構成に end の恒等射の uncurry を渡した普遍的な族。
I : Type u、[SmallCategory I] 以外に、係数やパラメータの Kan 性などは要求しない。
正確な型・全前提は README と公開844宣言の監査に記録。
切断から自然変換への逆対応と両逆関係は以下で証明した。切断空間との単体集合の同型も以下で証明した。
coherent な錐の pinched Hom と導来ファイバーの主比較、𝒮・Sp の残りの ∞ 極限は未完了。

`WeightedSectionCoefficients` は切断の族から底を正規化した係数を取り出し、単体的自然性を係数へ移す。
`WeightedSectionOverEvaluation` は over 圏の射列の最後の係数を最後の構造射で後合成し、
終点に関する自然性と、最後の頂点を保たない場合も含む全ての単体作用素との可換性を証明する。
`WeightedSectionTransform s hs : bousfieldKanWeight I ⊗ const A ⟶ H` はこれを束ねた逆構成。
`WeightedSectionTransformRetraction` と `WeightedSectionRoundtrip` で両向きの厳密な逆関係を証明した。
`weightedNerveSectionEquiv H A` は重み付き自然変換と底の nerve を保つ切断の族の全単射。
`bousfieldKanSectionHomEquiv H A` は end の普遍性と合成した
`(A ⟶ bousfieldKanHolim H) ≃ {s : nerve I ⊗ A ⟶ weightedNerve H // s ≫ projection = fst}`。
I : Type u、[SmallCategory I] のみで、係数とパラメータの Kan 性は不要。
正確な型・全前提は README と公開844宣言の監査に記録。
全単射のパラメータ自然性と切断模型との単体集合の同型は以下で証明した。
coherent な錐の pinched Hom と導来ファイバーの主比較、𝒮・Sp の残りの ∞ 極限は未完了。

`WeightedSectionParameter` で任意のパラメータの射による前合成の自然性を証明し、
`bousfieldKanSectionHomEquiv_apply H f` で全単射の順方向を普遍的な評価の前合成と同定した。
`SimplicialSections` は p : E ⟶ K の切断空間を内部 Hom の恒等写像の点上の引き戻しで定義する。
評価・持ち上げ・一意性と切断の族との全単射を公開した。
`BousfieldKanSectionsIso` の `bousfieldKanSectionsIso H` は
`bousfieldKanHolim H ≅ simplicialSections (weightedNerveProjection H)`。
任意の H に対する実際の単体集合の同型であり、両向きの評価式と厳密な逆関係を証明した。
`SectionsKan` の `simplicialSectionsRelativeIso p` は F1 の `relativeFunctorSpace p (𝟙 K)` との同型。
F1 の weighted nerve の射影の left fibration 性と相対関手空間の Kan 性から、
`bousfieldKanHolim_kanComplex H [∀ i, KanComplex (H.obj i)]` を証明した。
添字圏は任意の小さい圏で、遷移の fibration 性も有限性も要求しない。
正確な型・全前提は README と公開844宣言の監査に記録。
比較先の一般の Kan 性までの結果であり、任意の Kan 図式の strict 極限を homotopy 極限とは主張しない。
coherent な錐の pinched Hom と導来ファイバーの主比較、𝒮・Sp の残りの ∞ 極限は未完了。

`SectionsFunctor` で底を保つ全空間の写像 f : E ⟶ E' と f ≫ q = p から
`simplicialSectionsMap f hf` を構成し、評価式と恒等・合成の法則を証明した。
`SectionsDiagramNaturality` は end の uncurry と weighted nerve の係数の後合成の整合性を使い、
`bousfieldKanSectionsMap_naturality η` を証明する。
`bousfieldKanSectionsNatIso I` は
`bousfieldKanHolimFunctor I ≅ weightedNerveFunctor I ⋙ simplicialSectionsFunctor (nerve I)`。
任意の図式と自然変換に対し、F1 の実際の全空間の写像と可換な自然同型である。
`SectionsLifting` の `simplicialSectionsMap_hasLiftingProperty f hf i` は
HasLiftingProperty (K ◁ i) f から切断空間での i の持ち上げ性を得る。
ホーンと境界に適用し、f が Fibration または TrivialKanFibration なら
切断空間の誘導写像もそれぞれ同じ性質を持つことを証明した。
前提は全空間間の写像 f の性質であり、底への射影の left fibration 性だけでは代用しない。
正確な型・全前提は README と公開844宣言の監査に記録。
coherent な錐の切断模型との比較射とその同値性、pinched Hom と導来ファイバーの主比較、
𝒮・Sp の残りの ∞ 極限への適用は未完了。

`CoherentConeSections` は全ての JoinCone p をその頂点の coslice へ curry し、
底の図式を保つこと、逆構成の頂点の保存と厳密な逆関係を証明した。
`fixedVertexConeSectionEquiv p x` は左端を x に固定した錐と coslice への持ち上げの全単射。
`CoherentConeSectionSpace` はこれを相対関手空間に移し、任意の錐 c に
`coherentConeSectionPoint c` という具体的な零単体を割り当てる。
`fixedVertexConeSpaceEquiv p x` は頂点を固定した錐とこの模型の零単体の全単射。
X が quasicategory なら模型は Kan で、K の quasicategory 性は不要。
`PullbackSections` は引き戻しの切断空間と元の射の相対関手空間の同型を証明する。
`CoherentConeLeftFibration` は coslice 射影を図式に沿って引き戻した
`coherentConeProjection p x` を定義し、X が quasicategory なら left fibration であることを示す。
`coherentConeSectionsIso p x` はその切断空間と錐の相対関手模型の同型。
各錐 c はその切断空間の実際の点 `coherentConeSectionVertex c` を与える。
`coherentConeProjectionMappingEquivalence p x k` は各 fiber と右 pinched Hom の同値。
`strictCoherentConeFiberHomEquivalence F x i` は局所 Kan な単体的圏の実際の strict 図式の各 fiber と
宇宙を持ち上げた sHom x (F.obj i) の QCatEquivalence を与える。
正確な型・全前提は README と公開844宣言の監査に記録。
fiber の比較を図式全体へ束ねること、Bousfield–Kan end との切断空間の同値性、
錐の pinched Hom と q_x の導来ファイバーの主比較、𝒮・Sp の残りの ∞ 極限は未完了。

`TransportConeAssembly` は任意の通常の錐 c から simplicial replacement への写像を作り、
strict transport の場合は既存の universal scaffold で元の全空間へ評価する。
`strictTransportConeSections p c` はこの切断の族を切断空間へ持ち上げた射。
`TransportSectionsCone` は逆に切断を各 under 圏へ制限し、strict transport の通常の錐を作る。
`TransportSectionsRetraction` と `TransportSectionsLimit` は under 圏の射列の復元と
錐の可換性から両方向の回収を示す。
`transportSectionsConeIsLimit p : IsLimit (transportSectionsCone p)` と
`transportLimitSectionsIso p : limit (leftStrictTransportDiagram p) ≅ simplicialSections p` を証明した。
ここまでは p : E ⟶ nerve I が任意の小圏上の射影でよく、left fibration 性は不要。
`TransportSectionsComparison` はこの通常の極限錐に Bousfield–Kan 比較を適用する。
`strictTransportSectionsComparison p : simplicialSections p ⟶ bousfieldKanHolim (leftStrictTransportDiagram p)` は
cospan と塔上の left fibration p について実際の単体的ホモトピー同値である。
strict transport の構造射の fibration 性は F1 の薄い圏の制限の定理から導出し、追加仮定を残さない。
離散の場合の同じ比較は p の充填性や添字の有限性なしで厳密な同型。
正確な型・全前提は README と公開844宣言の監査に記録。
切断空間と strict transport の大域的な比較まで進んだが、元の sHom 図式との自然な比較は未完了。
錐の pinched Hom と q_x の導来ファイバーの主比較、𝒮・Sp の残りの ∞ 極限への適用も継続中。

`WeightedTransportCoefficients` と `WeightedTransportUnit` は任意の小圏上の図式 H に対して
`weightedTransportUnit H : H ⟶ leftStrictTransportDiagram (weightedNerveProjection H)` を構成した。
各 H(i) の単体を under 圏全体へ輸送し、相対 curry して得る自然変換であり、Kan 性は不要。
`weightedTransportUnitComponent_evaluate H i` は恒等射での評価との合成を
`weightedNerveFiberMap H i` と厳密に同定する。
`WeightedTransportUnitEquivalence` は全ての H(i) が Kan のとき、
`weightedTransportUnitComponent_isQCatEquivalence H i` と
`weightedTransportUnitComponent_homotopyEquivalence H i` を証明した。
前提は `[∀ i, KanComplex (H.obj i)]` のみであり、図式の構造射の fibration 性は不要。
成分の逆の自然性は要求しない。end 上の同値性は以下で証明した。
正確な型・全前提は README と公開844宣言の監査に記録。
coherent cone の射影の strict transport と元の sHom 図式との自然な比較、
錐の pinched Hom と q_x の導来ファイバーの主比較、𝒮・Sp の残りの適用は継続中。

`WeightedCoefficientPostcomp` は最後の係数評価の後合成自然性を証明し、
`WeightedBoundaryReconstruction` と `WeightedBoundaryLifting` は最後の面と最後の係数から
全ての正次元の境界を復元する。零次元は係数の自明 Kan fibration の切断で持ち上げる。
`weightedNerveMap_trivialKanFibration η` は `[∀ i, TrivialKanFibration (η.app i)]` の下で
実際の全空間の射 `weightedNerveMap η` が自明 Kan fibration であることを示す。
`bousfieldKanMap_trivialKanFibration η` は切断空間との自然同型で同じ結論を
`weightedSectionsMap (bousfieldKanWeight I) η` に移す。ここまでは値の Kan 性は不要。
`DiagramPathReplacement` と `DiagramPathSpan` は成分の可逆 path 置換を自然な図式にし、
射影・終点・切断を自然変換として束ねる。切断と射影の合成は恒等、切断と終点の合成は元の η。
Kan 値図式の成分ごとの同値なら、二射影がともに成分ごとの自明 Kan fibration になる。
これにより `bousfieldKanMap_isQCatEquivalence η hη` と
`bousfieldKanMap_homotopyEquivalence η hη` は任意の小圏上の Kan 値図式の
成分ごとの同値を、実際の end の誘導射の同値へ移す。
添字の有限性、遷移の fibration 性、成分の逆の自然性は要求しない。
`weightedTransportUnit_end_homotopyEquivalence H` は元の Kan 値図式とその weighted nerve の
strict transport の比較が end 全体でもホモトピー同値であることを示す。
正確な型・全前提は README と公開844宣言の監査に記録。
coherent cone の射影の transport と元の sHom 図式との自然な比較、
錐の pinched Hom と q_x の導来ファイバーの主比較、𝒮・Sp の残りの適用は継続中。
対象集約ビルド2265 jobs、公開844宣言の公理監査は標準三公理のみ。
外部リポジトリ依存457件は追跡済みかつ変更なしを確認。

`RelativeFunctorPostcomposition` は底を保つ全空間の実際の射 f から相対関手の後合成を作り、
前合成・頂点での評価・uncurry との可換性を証明した。
`TransportPostcomparison` は `strictTransportPost p q f hf` を strict transport の図式の
自然変換として構成し、`strictTransportPost_evaluate` で各 fiber の誘導射との可換性を示す。
p・q が left fibration なら、fiber の誘導射の同値性から transport の各成分の同値性と
end 全体のホモトピー同値性 `strictTransportPost_end_homotopyEquivalence` を得る。
`TransportSectionsNaturality` は切断の under 圏への制限の自然性を示し、
`strictTransportSectionsComparison_naturality` で標準比較の厳密な可換四角形を証明した。
`SectionsFiberwiseComparison` はその四角形から、cospan・塔・離散圏上の二つの left fibration 間の
fiber ごとの同値が実際の切断の誘導射のホモトピー同値を与えることを示す。
公開名は `simplicialSectionsMap_cospan_homotopyEquivalence`・
`simplicialSectionsMap_tower_homotopyEquivalence`・
`simplicialSectionsMap_discrete_homotopyEquivalence`。
全空間の射 f 自身の fibration 性や自明 Kan fibration 性は要求せず、離散添字の有限性も不要。
実際の底を保つ f と全 fiber の誘導射の同値性を要求し、点ごとに選んだ同値の族だけでは代用しない。
正確な型・全前提は README と公開844宣言の監査に記録。
coherent cone の射影と元の sHom 図式の模型の間の実際の比較、pinched Hom と q_x の導来ファイバーの
主比較、𝒮・Sp の残りの適用は継続中。

`RightConeBoundary` は境界と右の一点の join の right anodyne 性を示し、
`sliceOverPostcomp_trivialKanFibration_of_rightFibration c r` を証明した。
`VertexFiberMapLifting` は持ち上げ性・自明 Kan fibration 性・right fibration 性を
同じ底の頂点 fiber の誘導射へ移す。
`RightFibrationMappingSpan` は right fibration r : E ⟶ B の終点 c と底の始点 x に対して
M := `rightFibrationMappingTotal r c x` を構成し、
`rightFibrationMappingHomProjection r c x : M ⟶ pinchedHom x (r c)` が自明 Kan fibration、
`rightFibrationMappingEvaluation r c x : M ⟶ vertexFiber r x` が Kan fibration になることを示す。
後者と M の Kan 性には `[Quasicategory B]` を使い、E の quasicategory 性は導出する。
`RightFibrationHomComparison` は前者の射影の切断を選び、始点評価への合成による
`rightFibrationHomComparison r c x` を構成した。選んだ切断の自然性は主張しない。
`VertexFiberMapFiber` は任意の同じ底上の射の二重 fiber の厳密な同型を作り、
`rightFibrationMappingEvaluationFiberIso` で M の始点評価の strict fiber を元の pinched Hom と同定する。
`ConeMappingSpan` は任意の coherent な錐 d・c に対して
`conePinchedHom_mappingEvaluationFiberIso d c` を公開した。
これは実際の `pinchedHom (X := sliceOver p) d c` と始点評価の strict fiber の同型であり、
主比較の slice 側を回収する。strict な通常の錐に制限しない。
正確な型・全前提は README と公開844宣言の監査に記録。
始点評価の strict fiber と導来ファイバーの比較は以下で証明した。
錐の頂点 fiber と end の切断模型の比較、既存の sHom からの q_x との比較、
𝒮・Sp の残りの ∞ 極限への適用は未完了。

`KanEquivalencePaths` は Kan 複体の可逆 path の包含の同型性を証明し、
`PointEndpointEvaluation` と `KanRelativePathLifting` は一点の評価と二変数随伴を使って
Kan 複体間の Kan fibration p の `relativeEquivalencePathMapAt p j` が
全ての端点 j について自明 Kan fibration になることを証明した。
既存の `AnodyneIntervalEndpoints.delta_anodyne` を再利用し、そのリポジトリ依存を監査する。
`FibrationDerivedFiberSpan` は共通の path 解像から strict fiber と導来ファイバーへの
二つの実際の自明 Kan fibration を作り、`fibrationStrictDerivedFiberEquivalence p b` を公開した。
前提は `[KanComplex E]`・`[KanComplex B]`・`p : E ⟶ B`・`[Fibration p]`。
`ConeDerivedFiberComparison` は任意の図式 p : K ⟶ X と `[Quasicategory X]` に対し、
全ての coherent な錐 d・c の pinched Hom を始点評価の実際の導来ファイバーと同値にする
`conePinchedHom_mappingEvaluationDerivedFiberEquivalence d c` を証明した。
`ConeSpanLimitCriterion` は c の極限性と全ての x での始点評価のホモトピー同値性の同値を示す。
`ConeRepresentableCriterion` はさらに始域を底の `pinchedHom x c.vertex` とする実際の比較射
`rightFibrationHomComparison (sliceOverProjection p) c x` による同じ極限判定を証明した。
公開名は `isLimitCone_iff_rightFibrationHomComparison_homotopyEquivalence`。
添字 K や図式 p に strict な通常の図式という条件はなく、全ての x を量化する。
比較射には span の自明 Kan fibration の切断の選択が含まれ、その自然性は主張しない。
正確な型・全前提は README と公開844宣言の監査に記録。
錐の頂点 fiber と end の切断模型の比較、既存の豊穣 Hom からの q_x との接続、
𝒮・Sp の残りの ∞ 極限への適用は未完了であり、γ3b・γ3c の完成とは数えない。

`ConeFamilyApex` は `coneFamilyApex p : coneFamily p ⟶ X` と
`fixedApexConeFamily p x := vertexFiber (coneFamilyApex p) x` を定義した。
`sliceConeFamilyMap_apex p` は slice の標準比較が頂点を厳密に保つことを証明し、
`coneVertexFiberFamilyMap p x : vertexFiber (sliceOverProjection p) x ⟶
fixedApexConeFamily p x` を構成する。
`SectionConeFamily` は `joinTensorRight` と coslice の普遍性により切断の族を展開し、
`sectionConeFamilyUncurry_fixed`・`sectionConeFamilyUncurry_curry_fixed` で図式を、
`sectionConeFamilyMap_apex p x` で頂点を全次数で固定することを示した。
その結果 `sectionFixedApexConeFamilyMap p x : coherentConeSectionSpace p x ⟶
fixedApexConeFamily p x` を得た。全て任意の K・X・p・x で、充填性の仮定は不要。
正確な型・全前提は README と公開844宣言の監査に記録。
二つの射の同値性、豊穣 q_x との接続、𝒮・Sp の残りの適用は未完了。
大域的な slice の比較の同値性を strict fiber へ無条件に移してはいない。

`FixedEndpointConeSpace` は join の両端包含への制限の指定図式上の fiber を定義し、
`FixedEndpointConeIso` は `fixedApexEndpointConeSpaceIso p x :
fixedApexConeFamily p x ≅ fixedEndpointConeSpace p x` を構成した。
この厳密な同型は任意の K・X・p・x について、充填性なしで成立する。
`FixedEndpointFatComparison` は両端固定の fat join の模型
`fixedEndpointFatConeSpace p x` とそこへの実際の射を定義した。
`fixedApexFatConeComparison_isQCatEquivalence p x :
IsQCatEquivalence (fixedApexFatConeComparison p x)` は `[Quasicategory X]` だけを仮定する。
F1 の両端固定の fat join 比較の同値性を使い、頂点と図式を全次数で固定したまま比較する。
`joinEndpointInclusion_vertex_surjective` と固定 fiber の Kan 判定により、
同じ前提で `fixedEndpointConeSpace_kanComplex`・`fixedApexConeFamily_kanComplex` も得た。
K の quasicategory 性・非空性や p の fibration 性を追加しない。
正確な型・全前提は README と公開844宣言の監査に記録。
slice と切断空間から固定頂点の模型への二つの射の同値性、豊穣 q_x との接続、
𝒮・Sp の残りの適用は未完了であり、γ3b・γ3c の完成とは数えない。

`FixedFatConeUniversal`・`FixedFatConeCurry` は任意パラメータ A に対して
`fixedFatConeHomEquiv p x A : (A ⟶ fixedEndpointFatConeSpace p x) ≃
{F : fatJoin A K ⟶ X // fatJoinInl A K ≫ F = SSet.const x ∧ fatJoinInr A K ≫ F = p}`
を充填性の仮定なしで証明した。curry と uncurry の両端条件、自然性、単射性、往復則を含む。
`[Quasicategory X]` なら固定した fat join の空間の Kan 性もホモトピー圏の亜群性から得る。
`FixedSliceFatComparison` は既存の射の合成 `fixedSliceFatConeComparison p x :=
coneVertexFiberFamilyMap p x ≫ fixedApexFatConeComparison p x` を定義した。
太い slice への合成の厳密な同定と任意パラメータの uncurry の計算を行い、
`sliceLaxMap_mono`・`fixedSliceFatConeComparison_mono` を充填性なしで証明した。
`fixedSliceFatConeComparison_exists_retraction p x` は `[Quasicategory X]` の下で、
`∃ r : fixedEndpointFatConeSpace p x ⟶ vertexFiber (sliceOverProjection p) x,
fixedSliceFatConeComparison p x ≫ r = 𝟙 _` を証明する。
F1 の相対 join 延長で既存の部分族を固定し、頂点と図式を保って slice へ戻した。
K の quasicategory 性・非空性や p の fibration 性は不要。
正確な型・全前提は README と公開844宣言の監査に記録。
厳密な左逆だけを圏同値性と同一視しない。逆合成のホモトピー、切断空間側の同値、
豊穣 q_x との接続、𝒮・Sp の残りの適用は未完了。

`FatJoinTimeInput`・`FixedFatConeHomotopy` は両端を全時間で固定する fat join 図式の
ホモトピーを、固定頂点の錐の族のホモトピーへ戻す構成を充填性なしで証明した。
`FixedSliceConeEquivalence` は F1 の両端固定の join 比較で任意の族の逆像を
ホモトピーまで回収し、前節の厳密な左逆と合わせて標準比較の圏同値性を証明した。
公開名は `fixedSliceFatConeComparison_isQCatEquivalence`、
`coneVertexFiberFamilyMap_isQCatEquivalence`、`coneVertexFiberFamilyMap_homotopyEquivalence`。
任意の K・p・x に対し `[Quasicategory X]` だけを仮定し、
実際の `coneVertexFiberFamilyMap p x : vertexFiber (sliceOverProjection p) x ⟶
fixedApexConeFamily p x` の同値性を得た。
`FixedApexLimitCriterion` は `fixedApexConeHomComparison c x :
pinchedHom x c.vertex ⟶ fixedApexConeFamily p x` を定義し、
`isLimitCone_iff_fixedApexConeHomComparison_homotopyEquivalence c :
IsLimitCone c ↔ ∀ x, IsSimplicialHomotopyEquivalence (fixedApexConeHomComparison c x)`
を証明した。比較には既存の span の切断の選択が含まれ、その自然性は主張しない。
正確な型・全前提は README と公開844宣言の監査に記録。
切断空間側の比較の同値性、豊穣 q_x との接続、𝒮・Sp の残りの適用は未完了。

`SectionConeUniversal` は任意パラメータ A での切断空間の join 表示
`sectionConeHomEquiv p x A` を充填性なしで証明した。
`FatJoinTensorRight`・`FatJoinTensorRightComparison` は右因子へパラメータを移す射を構成し、
`fatJoinTensorRight_comparison` で通常の `joinTensorRight` との厳密な可換性を証明した。
`RightFatConeDiagram`・`RightFatConeNaturality` は共通模型への族を
`fatJoin Δ[0] (K ⊗ A) ⟶ X` へ展開し、左右の固定条件、元の普遍族への回収、
パラメータへの自然性と単射性を証明した。空のパラメータも扱う。
`SectionFatConeComparison` は既存の射の合成 `sectionFatConeComparison p x :=
sectionFixedApexConeFamilyMap p x ≫ fixedApexFatConeComparison p x` を定義した。
`sectionFatConeComparison_diagram` は任意パラメータの実際の比較の表示を同定し、
`sectionFatConeComparison_mono` はその単射性を充填性なしで証明する。
`sectionFatConeComparison_exists_retraction p x` は `[Quasicategory X]` だけを仮定して、
`∃ r : fixedEndpointFatConeSpace p x ⟶ coherentConeSectionSpace p x,
sectionFatConeComparison p x ≫ r = 𝟙 _` を証明した。
F1 の右因子の相対 join 延長を使い、部分族・頂点・図式を固定して逆射を作った。
正確な型・全前提は README と公開844宣言の監査に記録。
逆合成のホモトピーは未完了で、左逆だけを圏同値性とは数えない。
切断側の比較の同値性、豊穣 q_x との接続、𝒮・Sp の残りの適用を継続する。

`RightFatConeHomotopy` は右パラメータの図式の両端固定のホモトピーを、
共通模型の族のホモトピーへ戻す構成を充填性なしで証明した。
`SectionConeEquivalence` は両端固定の join 比較からホモトピー右逆を回収し、
前節の厳密な左逆と合わせて `sectionFatConeComparison_isQCatEquivalence`、
`sectionFixedApexConeFamilyMap_isQCatEquivalence`、
`sectionFixedApexConeFamilyMap_homotopyEquivalence` を証明した。
任意の K・p・x で `[Quasicategory X]` だけを仮定する。
`coneVertexFiberSectionEquivalence p x : QCatEquivalence
(vertexFiber (sliceOverProjection p) x) (coherentConeSectionSpace p x)` も構成した。
`ConeSectionLimitCriterion` は実際の `coneSectionHomComparison c x` を定義し、
`isLimitCone_iff_coneSectionHomComparison_homotopyEquivalence` を証明した。
`ConeTransportLimitCriterion` はその終域を錐の left fibration の strict transport の
Bousfield–Kan end へ移す。任意の小圏 I でこの end の Kan 性を示した。
cospan・塔・離散図式では追加の比較仮定なしに
`isLimitCone_iff_coneTransportHomComparison_cospan`・`_tower`・`_discrete` を証明した。
いずれも `IsLimitCone c ↔ ∀ x, IsSimplicialHomotopyEquivalence
(coneTransportHomComparison c x)` であり、p の fibration 性や添字の非空性は要求しない。
比較には同値の逆と span の切断の選択を含み、その自然性は主張しない。
正確な型・全前提は README と公開844宣言の監査に記録。
end の係数は表現可能な left fibration の transport であり、元の豊穣 Hom の図式との
自然な比較・実際の豊穣 q_x との整合性、𝒮・Sp の残りの適用は未完了。

`CoherentPathDual` は包含順序の path の順序双対への反転と恒等・合成・二回の双対との
整合性を証明し、`coherentThickeningDual J` を構成した。
`CoherentEnrichedOpposite` は単体的豊穣関手の反対と合成との可換性、および path の双対の
単調写像への自然性を証明した。反対の豊穣圏には Mathlib の構造を使う。
`CoherentReverseThickening` は Fin.rev による頂点の反転と
SimplexCategory.rev による添字の反転の可換性を証明した。
`CoherentOppositeMap` は任意の単体的圏 C で
`coherentNerveOppositeMap C : (SimplicialNerve C).op ⟶ SimplicialNerve Cᵒᵖ` を構成した。
Kan 性の仮定はなく、面・退化への自然性と頂点 x の像が op x である厳密な等式を含む。
`CoherentNervePost` は対象の宇宙が同じ C・D の豊穣関手 F について nerve の後合成を定義し、
`coherentNerveOppositeMap_post F` で反対の標準射との厳密な自然性を証明した。
正確な型・全前提は README と公開844宣言の監査に記録。
この射の逆と往復則、左 coslice の係数図式への接続は未完了。
元の豊穣 Hom の図式・q_x との主比較と、𝒮・Sp の残りの適用を継続する。

`CoherentDoubleOpposite` は二重反対からの標準豊穣関手と豊穣関手への自然性を構成した。
`CoherentReverseInvolution` は標準 thickening の二回の頂点と path の反転の往復則を証明した。
Hom では端点の等式による移送を保持し、部分集合の二回の像を恒等に戻す。
`CoherentOppositeIso` は各 simplex の反転と二重 unop の両方の往復則から、
`coherentNerveOppositeInverse C : SimplicialNerve Cᵒᵖ ⟶ (SimplicialNerve C).op` と
`coherentNerveOppositeIso C : (SimplicialNerve C).op ≅ SimplicialNerve Cᵒᵖ` を構成した。
順方向は既存の標準射で、`coherentNerveOppositeMap_isIso C` も公開する。
任意の単体的圏 C で成立し、Kan 性・quasicategory 性は要求しない。
逆射の面・退化との可換性、頂点 op x の像の厳密な等式、
`coherentNerveOppositeInverse_post F` による豊穣関手への自然性も証明した。
正確な型・全前提は README と公開844宣言の監査に記録。
左 coslice の係数図式への接続、元の豊穣 Hom の図式・q_x との主比較、
𝒮・Sp の残りの適用は引き続き未完了。


### γ3b：反転したホモトピー同値の移送

`OppositeKanHomotopy` に直積・ULift と反転の同型、区間の反転による逆向きのホモトピー、
Kan 複体間のホモトピー同値の反転による保存を実装した。
公開宣言は `oppositeTensorIso`、`oppositeSimplicialHomotopy`、
`oppositeKanHomotopyEquivalence`、`uliftOppositeIso`。
正確な型と前提は README の対応節と公開844宣言の監査に記録。
係数図式の自然比較、元の q_x、𝒮・Sp の残りの適用は未完了。


### γ3b：反転した豊穣 Hom と左 coslice fiber の実際の比較

`CoherentLeftHomComparison` に、反対圏の標準右 Hom 比較を反対 nerve の同型で移し、
さらに反転する射を構成した。始域は `ulift (sHom(x,y).op)`、
終域は x の左 coslice 射影の y 上の fiber。
`coherentCosliceFiberComparison_homotopyEquivalence x y` は局所 Kan 性のみで
実際の比較射の単体的ホモトピー同値性を証明する。
途中の右 Hom と左 Hom の射とその同値性、端点の厳密な同型も公開した。
正確な型・全前提は README と公開844宣言の監査に記録。
係数図式全体への自然比較、元の q_x、𝒮・Sp の残りの適用は未完了。


### γ3b：標準 Hom 比較の豊穣関手による後合成との整合性

`CoherentHomPost` に対象・simplex・標準頂点の後合成の式と端点の同型を構成し、
`coherentHomComparison_post F x y` として単体集合の射の厳密な可換図式を証明した。
前提は二つの単体的圏と豊穣関手のみ。Kan 性を要求しない。
各 Hom の端点を標準対象へ移送し、豊穣単位則と最大元評価の自然性で証明する。
正確な型・全前提は README と公開844宣言の監査に記録。
添字圏の合成作用・高次整合性と左 coslice 側への接続、元の q_x、
𝒮・Sp の残りの適用は未完了。


### γ3b：左 coslice の係数評価の最小点の座標

`CoherentPathMinimum` に零を除いた path の最小点を定義し、包含への反単調性、
正の切断点での合成則、初点固定拡張による任意の添字変換との可換性を証明した。
既存 Core の `prependOrderHom` を再利用し、面・退化を含めて扱う。
`pathFirstMinimumMap j` は反転した初区間の標準単体への実際の射で、
`pathFirstMinimumMap_reindex α j` が重みの初区間の制限との厳密な自然性を与える。
Kan 性を要求しない。正確な型・全前提は README と公開844宣言の監査に記録。
実際の weighted nerve から左 coslice への射の組立てと元の q_x、
𝒮・Sp の残りの適用は未完了。


### γ3b：反転した weighted nerve の係数の評価と豊穣合成

`WeightedCoherentCoefficients` に反転を戻した係数の実際の評価射を構成し、
path の合成を係数図式の作用へ移す厳密な式と全ての面・退化との自然性を証明した。
`WeightedRepresentableCoefficients` で表現可能な係数へ適用し、
`weightedRepresentableCoefficient_comp` により図式の作用を通常の射の定値 simplex との
豊穣合成と同定した。Kan 性や極限性は要求しない。
正確な型・全前提は README と公開844宣言の監査に記録。
cone の全頂点と Hom の豊穣関手への組立て、実際の左 coslice 射、元の q_x、
𝒮・Sp の残りの適用は未完了。


### γ3b：weighted nerve から coherent な錐の全空間への実際の射

`WeightedConeSimplex` に全頂点と Hom の作用、単位則と合成則を備えた cone simplex を構成。
初点が x の標準頂点、初点以外の面が元の strict な図式であること、全ての面・退化との
整合性を証明した。`WeightedCosliceComparison` で join の同型により左 coslice に移し、
`weightedCoherentConeComparison F x` として元の図式の上の実際の射を構成した。
`weightedCoherentConeComparison_over` が底への射影との厳密な可換性を与える。
前提は strict な図式と単体的圏だけ。Kan 性・Hom の逆の選択を要求しない。
正確な型・全前提は README と公開844宣言の監査に記録。
構成した射の fiber の同値性、反転した係数の切断空間の移送と元の q_x、
𝒮・Sp の残りの適用は未完了。


### γ3b：一定の底の fiber 比較と反転した Hom の座標

`ReflectedPathCoordinates` に最小点と反転 path の最大点の厳密な対応を証明し、
一定係数の評価を既存の右 Hom の最大点による評価として表した。
`WeightedConstantFiber` に構成済みの射の一定の底での制限と、終点 F(i) の fiber への
実際の持ち上げを構成し、その元の cone simplex と非定値 Hom の作用を計算した。
`coherentLeftHomComparison_simplex` に既存の左 Hom 比較の simplex の反転による表示を証明。
Kan 性を要求しない。正確な型・全前提は README と公開844宣言の監査に記録。
二つの coherent simplex 全体の一致と実際の fiber 射の同値性、元の q_x と切断空間、
𝒮・Sp の残りの適用は未完了。


### γ3b：一定の底の fiber 射の厳密な同定と同値性

`WeightedConstantSimplex` に `weightedConstantConeSimplex_eq` を証明し、一定の底の
coherent simplex 全体を反対圏の右 Hom の標準 simplex の反転に同定した。
`weightedConstantCosliceFiberMap_eq` は構成済みの実際の射を標準左 Hom 比較に厳密に同定する。
`weightedConstantCosliceFiberMap_homotopyEquivalence` は局所 Kan 性のみでその射の同値性を証明。
比較の同値性の追加仮定や逆射の選び直しはない。
正確な型・全前提は README と公開844宣言の監査に記録。
ULift と引き戻しの fiber の同型を通じた全体比較の各 fiber への移送、切断空間と元の q_x、
𝒮・Sp の残りの適用は未完了。


### γ3b：全体比較が誘導する全ての fiber 射の同値性

`UniverseVertexFiber` に ULift と頂点 fiber の厳密な同型と包含の可換性を構成。
`WeightedConeFiberEquivalence` に始域の持ち上げた weighted nerve の fiber と
終域の引き戻しの fiber の同型を構成し、実際の全体の比較射が誘導する fiber 射の
`weightedCoherentConeFiberMap_factorization` を証明した。
`weightedCoherentConeFiberMap_homotopyEquivalence` は局所 Kan 性のみで全ての底の頂点の
実際の fiber 射が単体的ホモトピー同値であることを証明する。
正確な型・全前提は README と公開844宣言の監査に記録。
切断空間の比較と反転・ULift・底の同型に沿う移送、元の q_x、𝒮・Sp の残りの適用は未完了。


### γ3b：宇宙の持ち上げの left fibration 性と切断比較射

`UniverseLeftFibration` に指定したホーンの相対持ち上げ性の ULift による保存と、
`leftFibration_uliftFunctor_map` を証明した。p の Kan fibration 性や標的の Kan 性は要求しない。
`WeightedConeSections` で持ち上げた反転豊穣係数の射影の left fibration 性と切断空間の Kan 性を証明。
`weightedCoherentConeSectionsComparison` は構成済みの全体の比較射による後合成を使う実際の射。
射の定義には Kan 性・極限性を要求しない。
正確な型・全前提は README と公開844宣言の監査に記録。
切断比較の同値性、底の同型と反転・ULift を通じた end への移送、元の q_x、
𝒮・Sp の残りの適用は未完了。


### γ3b：三形状の実際の切断比較の同値性

`SectionsBaseIso` と `FibersBaseIso` に底の厳密な同型による切断空間・fiber の同型と
実際の比較写像への自然性、同値性の移送を証明した。
`SectionsShapeBaseIso` と `LiftedShapeNerveIso` で離散・cospan・塔の持ち上げた nerve を
標準形へ同型で移し、構成済みの全 fiber の同値性を三形状の切断判定へ渡した。
`WeightedConeSectionEquivalence` の三つの公開定理は実際の
`weightedCoherentConeSectionsComparison` の単体的ホモトピー同値性を局所 Kan 性のみで証明する。
図式の射の fibration 性や離散対象の有限性は要求しない。
正確な型・全前提は README と公開844宣言の監査に記録。
始域の反転・ULift を元の豊穣 Hom の end へ移す比較、元の q_x と cone の射の一致、
𝒮・Sp の残りの適用は未完了。


### γ3b：切断の ULift 同型と反転豊穣 Hom の end の比較

`UniverseSSetMaps` に単体集合の ULift の完全忠実性と直積・標準単体の厳密な同型を構成。
`UniverseSections` に任意の射影 p について `uliftSectionsIso p` を構成し、順方向を
普遍的な評価から作る標準比較射に固定した。小さいパラメータの切断の全単射を標準単体へ
適用して検証し、Kan 性・fibration 性を要求しない。
`ReflectedHomHolimComparison` の実際の射は反転豊穣 Hom の Bousfield–Kan end の ULift から
coherent な錐の切断模型へ写す。三形状では局所 Kan 性のみでホモトピー同値性を証明した。
正確な型・全前提は README と公開844宣言の監査に記録。
係数の反転の移送と元の q_x・strict な錐の比較射との整合性、𝒮・Sp の残りの適用は未完了。


### γ3b：反転した strict Hom 錐の標準比較

`OppositeFibration` に Kan fibration の反転の保存を追加。始域・終域の Kan 性を要求せず、
全ホーンの相対持ち上げ性を反転同型で移した。
`ReflectedRepresentableComparison` は `reflectedSimplicialHomCone c x`、その極限性、
実際の標準比較 `reflectedRepresentableComparison c x : sHom(x,L).op → BKholim(H_x ⋙ op)`、
始対象の射に関する厳密な反変自然性を公開する。
離散図式の比較は同型、中央・右端が Kan で左脚が fibration の cospan の比較と、
零段が Kan で全隣接遷移が fibration の塔の比較は単体的ホモトピー同値。
三形状の `reflectedStrictConeSectionsComparison c x` はこの比較を ULift で写して
反転 end からの切断比較へ合成した実際の射であり、局所 Kan 性と Hom 錐の極限性、
cospan・塔の上記 fibration 条件の下で同値である。
新規12宣言の正確な型・全前提は README と公開856宣言の監査に記録。
既存の `DoldKanComparison.ulift_homotopyEquivalence` を再利用する。
係数の反転の自然な移送、元の q_x と native な strict 錐の比較との整合性、
𝒮・Sp の残りの適用は未完了。新しい切断比較の同値性だけで `IsLimitCone` を結論しない。

検証：`lake build SerrePositivity.InfinityCategories.HomotopyLimits` 成功（4434 jobs）、
`scripts/audit_homotopy_limits.lean` の公開856宣言の `#check @` と公理監査が成功。
標準3公理のみ。新規ファイルに警告・sorry・追加公理はない。
集約から再帰的に辿る他担当の700ソースはすべて追跡済み・コミット済み・変更なし。
検証ログは `/tmp/gamma3-reflected-strict-aggregate.log` と
`/tmp/gamma3-reflected-strict-audit.log`。


### γ3b：strict な錐の全パラメータの評価と各脚の比較

`StrictConeWeightedEvaluation` に任意の strict な単体集合の錐について、標準比較を
weighted nerve と切断空間で評価する式、初区間の全係数の式、底の各対象での評価式を証明。
`ReflectedStrictConeEvaluation` に引き戻し切断同型の評価、weighted nerve の切断比較と
反転 end の比較の評価、反転した strict Hom 錐の合成の全パラメータでの評価を証明した。
非定値係数を初区間の最小点・反転した Hom のパラメータ・実際の錐の脚の後合成へ分解し、
`reflectedStrictConeSectionsComparison_evaluate` により各対象で既存の canonical な
`coherentCosliceFiberComparison x (F.obj i)` と錐の脚の後合成に一致することを示した。
全て定義済みの実際の射に関する等式であり、Kan 性・極限性・同値の逆の選択を要求しない。
新規10宣言の正確な型・全前提は README と公開866宣言の監査に記録。
選択付きの native な錐の Hom 比較との全体の比較、元の q_x と係数の反転の整合性、
𝒮・Sp の残りの適用は未完了。各脚での一致だけから `IsLimitCone` を結論していない。

検証：対象集約 `HomotopyLimits` のビルド成功（4436 jobs）、公開866宣言の `#check @` と
公理監査成功（標準3公理のみ）。新規ファイルの警告・sorry・追加公理はない。
集約の他担当の依存700ソースはすべて追跡済み・コミット済み・変更なし。
検証ログは `/tmp/gamma3-strict-cone-evaluation-aggregate.log` と
`/tmp/gamma3-strict-cone-evaluation-audit.log`。


### γ3b：反復 slice の比較に向けた join の再結合の準備

native な比較 span と錐の図式 `Δ[0]⋆K → X` 上の切断の制限を比較する経路を進める。
反復 slice に現れる `(Δ[n]⋆Δ[0])⋆K` と `Δ[n]⋆(Δ[0]⋆K)` の再結合のため、
`AssociativeJoinSimplex` で空区間を含む単体の長さの和表示、三つの区間への展開、
両逆則、各次数の `joinAssociatorSimplexEquiv` を構成した。
`JoinAssociativityCuts` に二つの切断の引き戻しと左右の区間への制限の計算を証明。
`JoinSumNaturality` は二因子の長さの和表示の全順序写像への自然性と恒等・合成則を証明する。
Core の定義・他担当のファイルは変更していない。
新規14宣言の正確な型・全前提は README と公開880宣言の監査に記録。
三因子の再結合そのものの自然性、単体集合の結合同型、反復 slice への移送は未完了。
したがって native な極限判定との全体の比較、元の q_x の整合性、𝒮・Sp の残りの適用は
引き続き未完了であり、次数ごとの全単射で γ3b の完成とはしない。

検証：対象集約 `HomotopyLimits` のビルド成功（4439 jobs）、公開880宣言の `#check @` と
公理監査成功（標準3公理のみ）。新規ファイルの警告・sorry・追加公理はない。
集約の他担当の依存700ソースはすべて追跡済み・コミット済み・変更なし。
検証ログは `/tmp/gamma3-join-assoc-preparation-aggregate.log` と
`/tmp/gamma3-join-assoc-preparation-audit.log`。


### γ3b：join の結合同型と三因子の射についての自然性

`JoinTripleCoordinates` に中区間の直接の制限と、左右の二重の区間制限の単体作用の HEq、
三因子の和表示の外延性を証明した。
`JoinTripleMaps` に共通表示の単体作用を構成し、両括弧付けからの作用との一致を証明。
`JoinAssociator` は任意の A・B・C について全ての面・退化との可換性を示し、
`joinAssociator A B C : (A⋆B)⋆C ≅ A⋆(B⋆C)` を単体集合の厳密な同型として公開する。
`JoinAssociatorMaps` の `joinAssociator_naturality` は三つの因子の任意の射への自然性。
Kan 性・quasicategory 性・非空性や因子の射への追加の仮定は不要。
新規27宣言の正確な型・全前提は README と公開907宣言の監査に記録。
join の結合同型と自然性は今回で完成。固定面の包含との整合式、反復 slice の同定、
native な錐の比較と切断の制限の比較、元の q_x と反転係数の整合性、𝒮・Sp の残りの適用は
未完了であり、γ3b・γ3c は継続中。

検証：対象集約 `HomotopyLimits` のビルド成功（4443 jobs）、公開907宣言の `#check @` と
公理監査成功（標準3公理のみ）。新規ファイルの警告・sorry・追加公理はない。
集約の他担当の依存700ソースはすべて追跡済み・コミット済み・変更なし。
検証ログは `/tmp/gamma3-join-associator-aggregate.log` と
`/tmp/gamma3-join-associator-audit.log`。


### γ3b：反復 slice の同型と native な判定の slice の制限への移送

`JoinAssociatorInclusions` に固定面と結合同型の可換式を追加し、
`IteratedSliceOverFamilies`・`IteratedSliceOverIso` に任意の p・q とパラメータについての
二方向の族、往復則・自然性、`sliceOver q ≅ sliceOver (sliceOverUncurry q)` を構成した。
X への二重の射影と、元の図式の slice への制限と射影の対応も厳密に証明。
`ConeIteratedSliceIso` は任意の coherent な錐 c に特殊化し、native な比較 span の
中間空間を錐の図式上の slice の頂点 fiber と同型で結び、実際の評価射を制限の fiber 射に同定する。
これらに Kan 性・極限性は不要。
`ConeSliceRestrictionCriterion` は任意の quasicategory X と任意の錐 c について
`IsLimitCone c ↔ ∀ x, IsSimplicialHomotopyEquivalence (coneSliceRestrictionFiberMap c x)`
を証明する。strict な錐や有限の添字に制限せず、追加の fibration 性は不要。
新規53宣言の正確な型・全前提は README と公開960宣言の監査に記録。
slice の頂点 fiber の判定から coslice の切断の制限への移送、豊穣 q′ との可換式、
元の q_x と反転係数の整合性、𝒮・Sp の残りの適用は未完了であり、γ3b・γ3c は継続中。

検証：対象集約 `HomotopyLimits` のビルド成功（4449 jobs）、公開960宣言の `#check @` と
公理監査成功（標準3公理のみ）。新規ファイルの警告・sorry・追加公理はない。
集約の他担当の依存700ソースはすべて追跡済み・コミット済み・変更なし。
検証ログは `/tmp/gamma3-cone-slice-restriction-aggregate.log` と
`/tmp/gamma3-cone-slice-restriction-audit.log`。


### 図式の制限と切断の標準比較の自然性

`ConeDiagramRestriction` に両端固定の錐の制限 `endpointConeRestrict p x f` と
その包含後の値・固定条件、切断の族の `sectionConeUncurry_restrict` を構成した。
`ConeDiagramTensor` は図式の因子の射と join・直積の左右の標準比較の自然性を証明。
`ConeRestrictionComparison` の実際の比較 `sectionEndpointConeComparison` は
`relativeFunctorPre ... p f ≫ sectionEndpointConeComparison (f ≫ p) x =
sectionEndpointConeComparison p x ≫ endpointConeRestrict p x f` を満たす。
ここまでは全て任意の単体集合の図式で成立し、充填性の前提はない。
X が quasicategory ならこの比較は単体的ホモトピー同値であり、
`sectionRestriction_homotopyEquivalence_iff_endpoint` は切断の制限の同値性と
両端固定の錐の制限の同値性を同値にする。全ての単体的パラメータの値を追跡し、
選択した逆同値の自然性は使っていない。原典は HTT 4.2.4.1、Kerodon 7.4.1.6。
新規13宣言の正確な型・全前提は README に記録し、公開973宣言の監査に追加した。
slice 側の制限との可換式、native な極限判定の切断の制限への移送、豊穣 q′ との可換式、
元の q_x と反転係数の整合性、𝒮・Sp の残りの適用、余極限の比較は未完了。
γ3b・γ3c は継続中。

検証：対象集約 `HomotopyLimits` のビルド成功（4452 jobs）、公開973宣言の `#check @` と
公理監査成功（標準3公理のみ）。新規ファイルの警告・sorry・追加公理はない。
他担当の依存700ソースは全て追跡済み・コミット済み・変更なし。
検証ログは `/tmp/gamma3-cone-diagram-restriction-aggregate.log` と
`/tmp/gamma3-cone-diagram-restriction-audit.log`。


### native な極限判定の切断の制限への移送

`SliceEndpointConeComparison` に、任意の図式の射について slice の頂点 fiber から
両端固定の錐への実際の標準比較と制限の可換式を証明した。
全パラメータの uncurry の値と射影との可換式も証明し、X が quasicategory なら
`sliceRestriction_homotopyEquivalence_iff_sections` は slice の制限と切断の制限の
ホモトピー同値性を同値にする。追加の比較同値の仮定や逆同値の自然性は不要。
`ConeSectionRestrictionCriterion` は native な錐の制限を通常の図式の制限へ同定し、
錐の固定条件で正規化した実際の切断の制限 `coneSectionRestriction c x` を構成した。
主定理 `isLimitCone_iff_coneSectionRestriction_homotopyEquivalence` の型は
`IsLimitCone c ↔ ∀ x : X _⦋0⦌,
IsSimplicialHomotopyEquivalence (coneSectionRestriction c x)`。
前提は `[Quasicategory X]` のみで、任意の単体集合 K と任意の coherent な錐 c を扱う。
全パラメータの制限の値 `coneSectionRestriction_uncurry` も公開した。
原典は HTT 4.2.4.1 の双対、Kerodon 7.4.1.6、7.5.4.6。
新規16宣言の正確な型・全前提は README に記録し、公開989宣言の監査に追加。
native な極限判定の切断の制限への移送は証明済みとなったが、strict な豊穣錐の q′ との
可換式、元の q_x と反転係数の整合性、𝒮・Sp の残りの適用、余極限の比較は未完了。
γ3b・γ3c は継続中。

検証：対象集約 `HomotopyLimits` のビルド成功（4454 jobs）、公開989宣言の `#check @` と
公理監査成功（標準3公理のみ）。新規ファイルの警告・sorry・追加公理はない。
他担当の依存700ソースは全て追跡済み・コミット済み・変更なし。
検証ログは `/tmp/gamma3-cone-section-restriction-aggregate.log` と
`/tmp/gamma3-cone-section-restriction-audit.log`。


### 錐の頂点評価と豊穣 Hom を始域とする native な比較

`ConeApexEvaluation` は任意の K の左頂点包含 `joinInl Δ[0] K` の left anodyne 性と、
任意の quasicategory X の錐 c に対する `coneApexSectionEvaluation c x` の
trivial Kan fibration 性・ホモトピー同値性を証明した。包含後の値も通常の頂点評価に同定。
`StrictConeNativeComparison` は strict な錐の頂点評価を c.pt へ正規化し、その厳密な切断を選ぶ。
既存の coslice fiber 比較との合成 `reflectedStrictConeFamilyComparison c x` は
頂点で元の比較に厳密に一致し、局所 Kan 性の下で単体的ホモトピー同値である。
元の図式への制限を合成した `reflectedNativeConeComparison c x` を定義し、主定理
`strictCoherentCone_isLimit_iff_reflectedNativeConeComparison` として
`IsLimitCone (strictCoherentCone c) ↔ ∀ x : C,
IsSimplicialHomotopyEquivalence (reflectedNativeConeComparison c x)` を証明した。
前提は C の局所 Kan 性のみで、I は任意の小圏、c は任意の通常の錐。
Hom 錐の極限性や図式の fibration 性は要求しない。始域は `ULift (sHom(x,c.pt).op)`。
切断の選択を含み、その自然性は主張しない。新規16宣言の正確な型・全前提は README に記録。
原典は HTT 4.2.4.1 の双対、Kerodon 7.4.1.6、7.5.4.6。
q′ の切断比較との整合性はまだ未証明。次は始対象を加えた通常の図式上の weighted な
切断比較を使い、頂点での評価と元の図式への制限を同時に追跡する。
元の q_x と反転係数の整合性、𝒮・Sp の残りの適用、余極限の比較も未完了。
γ3b・γ3c は継続中。

検証：対象集約 `HomotopyLimits` のビルド成功（4456 jobs）、公開1005宣言の `#check @` と
公理監査成功（標準3公理のみ）。新規ファイルの警告・sorry・追加公理はない。
他担当の依存700ソースは全て追跡済み・コミット済み・変更なし。
検証ログは `/tmp/gamma3-native-enriched-apex-aggregate.log` と
`/tmp/gamma3-native-enriched-apex-audit.log`。


### q′ と native な制限の主可換式、三形状の ∞ 極限への移送

`SmallStrictConeParameter` に `WithInitial I` 上の小さい錐の図式と標準射を構成し、
既存の strict な coherent な錐がその引き戻しであること、左右の包含での値を厳密に証明した。
`WeightedStrictConeFamily` は始対象付き図式の標準錐の q′ から錐全体上の実際の族を構成。
頂点評価との合成は標準の coslice fiber 比較に一致し、局所 Kan 性でこの族はホモトピー同値。
頂点評価の切断の選択や、始対象付き図式の q′ 全体の同値性は用いない。
`WeightedConeRestriction` は主可換式
`weightedStrictConeFamilyComparison c x ≫
coneSectionRestriction (strictCoherentCone c) (coherentNerveVertex x) =
reflectedStrictConeSectionsComparison c x` を全パラメータで証明した（Kan 性や極限性は不要）。
局所 Kan 性での主判定
`strictCoherentCone_isLimit_iff_reflectedStrictConeSectionsComparison` の型は
`IsLimitCone (strictCoherentCone c) ↔ ∀ x : C,
IsSimplicialHomotopyEquivalence (reflectedStrictConeSectionsComparison c x)`。
I と c は任意で、追加の比較同値の仮定はない。
`StrictHomotopyLimits` は `strictCoherentCone_isLimit_of_discrete_homLimit`、
`strictCoherentCone_isLimit_of_cospan_homLimit`、`strictCoherentCone_isLimit_of_tower_homLimit`
を公開した。共通の条件は C の局所 Kan 性と全 x での Hom 錐の strict 極限性。
離散図式には有限性を要求せず、cospan は Hom の左脚の fibration 性のみ、
塔は Hom の全隣接遷移の fibration 性を要求する。結論は実際の `IsLimitCone (strictCoherentCone c)`。
原典は HTT 4.2.4.1 の双対の限定形、Kerodon 7.5.3.12、7.5.4.6。
新規27宣言の正確な型・全前提は README に記録し、公開1032宣言の監査へ追加。
q′ と native な制限の接続は証明済みとなった。
元の非反転の end・q_x と反転係数の直接比較、𝒮・Sp の実際の錐と Hom 条件の検証、
余極限の比較は未完了。一般定理のみで γ3c の具体的適用を完了とは数えず、γ3 は継続中。

検証：対象集約 `HomotopyLimits` のビルド成功（4460 jobs）、公開1032宣言の `#check @` と
公理監査成功（標準3公理のみ）。新規ファイルの警告・sorry・追加公理はない。
他担当の依存700ソースは全て追跡済み・コミット済み・変更なし。
検証ログは `/tmp/gamma3-strict-homotopy-limits-aggregate.log` と
`/tmp/gamma3-strict-homotopy-limits-audit.log`。


### γ3c：𝒮 の指定された三形状の実際の極限

`KanConeLimits` は既存の KanObject の豊穣 Hom と内部 Hom の共変作用を厳密に同定した。
台での極限性から通常の Kan 複体の圏と全ての豊穣 Hom の極限性を導き、fibration の
内部 Hom による保存も検証した。一般の台の錐の Kan な頂点を束縛する構成と、
`strictCoherentDiagram F = kanDiagramCoherentNerve F` も公開した。
`SpaceProducts` は `kanProductObject F` と射影の錐を構成し、
`spaceProductCone_isLimitCone (F : Discrete J ⥤ KanObject)` として任意の小さい積を公開。
頂点の台は `limit (F ⋙ kanObjectForget)`。有限性・非空性の仮定はなく、有限積を含む。
`SpacePullbacks` は `p : E ⟶ B`、`q : D ⟶ B` の台の p が Kan fibration の場合に、
台の実際の `pullback p q` を束縛し、`spacePullbackCone_isLimitCone p q` を公開した。
右脚の fibration 性は要求しない。
`SpaceTowers` は `F : AsSmall ℕᵒᵖ ⥤ KanObject` の台の全隣接遷移が Kan fibration なら、
実際の可算塔の `limit (AsSmall.up ⋙ F ⋙ kanObjectForget)` を束縛し、
`spaceTowerCone_isLimitCone F` を公開した。
三形状とも F1 の既存の `kanDiagramCoherentNerve` 上の実際の錐であり、忘却後と通常の
Kan 複体の圏の極限の普遍性、全 Hom の極限性と必要な fibration 性を実装内で証明した。
追加の Hom 条件や比較同値を仮定する界面ではない。
原典は HTT 4.2.4.1 の双対、Kerodon 7.5.3.12、7.5.4.6。
新規31宣言の正確な型・全前提は README に記録し、公開1063宣言の監査へ追加した。
γ3c の 𝒮 の指定された三形状の極限は公開済み。Sp の具体的な三形状の極限、
元の非反転の end・q_x と反転係数の直接比較、余極限の比較は未完了で、γ3 は継続中。

検証：対象集約 `HomotopyLimits` のビルド成功（4467 jobs）、公開1063宣言の `#check @` と
公理監査成功（標準3公理のみ）。新規ファイルの警告・sorry・追加公理はない。
他担当の依存703ソースは全て追跡済み・コミット済み・変更なし。
検証ログは `/tmp/gamma3-space-limits-aggregate.log` と `/tmp/gamma3-space-limits-audit.log`。


### γ3c：Sp の実際の写像空間の段評価と極限の普遍性

L9 の `OmegaSpectrum` の対象条件（各段 Kan、懸垂の構造射が単射、随伴構造射の
全基点の π_* 同型）と、既存の `Sp` がこの局所 Kan な単体的圏の coherent nerve であることを確認。
`SpectrumMappingDiagram` は実際の Hom の後合成と各段評価の厳密な可換式を証明し、
評価を自然変換として束ねた。点つき写像空間の極限保存、前合成・後合成・懸垂の自然性と、
スペクトルの境界比較の後合成に関する自然性も証明した。
`SpectrumHomLimitFamilies` は、任意の小圏 I、`F : I ⥤ OmegaSpectrum`、錐 c について、
`spectrumHomCone_isLimit_of_levelwise (c : Cone F)
(hc : ∀ n, IsLimit (spectrumLevelCone c n)) (X : OmegaSpectrum) :
IsLimit (simplicialHomCone c X)` を公開。
各段の極限性は点つき単体集合の圏で指定し、Hom の極限性を追加の前提にはしない。
任意の Hom 図式上の錐 s の全単体的パラメータの各段の普遍族を構成し、
構造射との整合性から L9 の実際の全写像空間へ持ち上げ、射影則・一意性まで証明した。
L9 の対象・射・豊穣構造の定義は変更せず、別の Sp の模型や追加の比較同値は使わない。
原典は BF 1978 §2、HTT 4.2.4.1、Kerodon 7.5.4.6。
新規21宣言の正確な型・全前提は README に記録し、公開1084宣言の監査へ追加。
Sp の実際の極限対象の Ω 条件と構造射の単射性、必要な Hom の fibration 条件、
三形状の ∞ 極限錐の公開は未完了。この Hom の普遍性の結果だけで Sp の適用を完了とは数えない。
元の非反転の end・q_x と反転係数の直接比較、余極限側も未完了で、γ3 は継続中。

検証：対象集約 `HomotopyLimits` のビルド成功（4528 jobs）、公開1084宣言の `#check @` と
公理監査成功（標準3公理のみ）。新規ファイルの警告・sorry・追加公理はない。
他担当の依存758ソースは全て追跡済み・コミット済み・変更なし。
検証ログは `/tmp/gamma3-spectrum-hom-limits-aggregate.log` と
`/tmp/gamma3-spectrum-hom-limits-audit.log`。


### γ3c：Sp の二項積の Ω 条件の検証

`KanPiProducts` は L9 の全自然数次数のホモトピー類について、全基点で積の二つの射影が
全単射 `kanHomotopyProdMap_bijective` を与えることを証明した。
積の射に関する自然性を使い、`kanPiIsomorphism_tensor` は全基点 π_* 同型の
二項積が再び全基点 π_* 同型となることを証明。零次数も含み、正次数の指定基点だけに弱めていない。
`SpectrumBinaryProductSequence` は loop の右随伴性から `loopProductIso` を作り、
射影と可換すること、および `binaryProductSigma_adjoint` により積の構造射の随伴が
二つの随伴の積に厳密に一致することを証明した。
`binaryProductKanSequence X Y` と厳密な射影二本、任意の二射を組にする普遍射、
射影則と一意性も構成。`binaryProductKanSequence_omega` の型は
`(X Y : KanSequence.{u}) → X.OmegaCondition → Y.OmegaCondition →
(binaryProductKanSequence X Y).OmegaCondition`。
全基点・零次数を含む Ω 条件を二つの成分から検証し、構造射の単射性は仮定しない。
原典は BF 1978 §2、HA §1.4.2、Kerodon §3.2.2、HTT 4.2.4.1。
新規23宣言の正確な型・全前提は README に記録し、公開1107宣言の監査へ追加した。
この対象は単射構造をまだ持たない Kan Ω 列の積であり、L9 の OmegaSpectrum として
束縛する構造射の単射性、Sp の二項積の極限錐、空積と有限積、引き戻し・塔の公開は未完了。
中間の列の Ω 条件と普遍性だけで Sp の有限積を完了とは数えない。
元の非反転の end・q_x と反転係数の直接比較、余極限側も未完了で、γ3 は継続中。

検証：対象集約 `HomotopyLimits` のビルド成功（4587 jobs）、公開1107宣言の `#check @` と
公理監査成功（標準3公理のみ）。新規ファイルの警告・sorry・追加公理はない。
他担当の依存812ソースは全て追跡済み・コミット済み・変更なし。
検証ログは `/tmp/gamma3-spectrum-binary-product-sequence-aggregate.log` と
`/tmp/gamma3-spectrum-binary-product-sequence-audit.log`。


### γ3c：smash の各次数の単射性と Sp の実際の二項積

新規4モジュールで、非基点の組による smash の表示、既存の pushout による smash との
標準同型 `smashSimplexModelIso`、二項積との標準比較 `smashProductComparison` の
基礎単体写像のモノ射性を証明した。比較の単射性には Kan 性の仮定を置かない。
`binaryProductSigma_factor` と `binaryProductSigma_mono` により、二つの単射な
懸垂構造射の積の構造射も単射とした。

前回の Kan Ω 列の積の全基点・全自然数次数の Ω 条件を合わせ、L9 の実際の対象
`spectrumBinaryProduct (X Y : OmegaSpectrum.{u}) : OmegaSpectrum.{u}` を構成した。
各段は点つき通常積、二つの厳密な射影と離散二対象の図式・錐を持つ。
各段の極限性から全ての実際の豊穣 Hom の極限性を得て、

```lean
spectrumBinaryProductInfinityCone_isLimit (X Y : OmegaSpectrum.{u}) :
  IsLimitCone (spectrumBinaryProductInfinityCone X Y)
```

を証明した。追加の条件付き入力はない。底は `Discrete (ULift WalkingPair)` の nerve、
標的は L9 の `Sp` と同じ coherent nerve。主張を Kan 列の中間対象で止めていない。
原典は BF 1978 §2、HA §1.4.2、HTT 4.2.4.1 の双対、Kerodon 7.5.4.6。
新規44宣言の正確な型・全前提は InfinityCategories/README.md の同名節へ記録し、
監査へ追加した。

Sp の空積・一般の有限積への束ね直し、引き戻し、塔は未完了。
元の非反転の end・q_x と反転係数の直接比較、余極限側、E2a 完了後の E2b 適用も未完了。
γ3 は継続中。

検証：対象集約 `HomotopyLimits` のビルド成功（4591 jobs）、公開1151宣言の `#check @` と
公理監査成功（標準3公理のみ）。新規ファイルの警告・sorry・追加公理はない。
他担当の依存812ソースは全て追跡済み・コミット済み・変更なし。
検証ログは `/tmp/gamma3-spectrum-binary-product-aggregate.log` と
`/tmp/gamma3-spectrum-binary-product-audit.log`。


### γ3c：Sp の空積を含む全ての有限積

`SpectrumPoint` で一点の Kan 性と、その懸垂・loop の零対象性を証明し、
構造射とその随伴が同型である実際の `spectrumPoint : OmegaSpectrum.{u}` を構成した。
`SpectrumFiniteProducts` で通常の終対象性と前回の二項積の通常の普遍性を検証し、
Mathlib の終対象・二項積からの有限帰納の構成により `spectrumHasFiniteProducts` を得た。
各段の評価が終対象と二項積を保つことを直接確認し、全ての有限積の保存を証明した。
存在・保存のクラスの公開補題はモジュール内では局所 instance として使う。

任意の有限型 J と実際の図式 F について、通常の極限錐 `spectrumFiniteProductCone F` と
全ての段の極限性、L9 の実際の豊穣 Hom の極限性を得た。主定理は

```lean
spectrumFiniteProductInfinityCone_isLimit {J : Type u} [Finite J]
    (F : Discrete J ⥤ OmegaSpectrum.{u}) :
  IsLimitCone (spectrumFiniteProductInfinityCone F)
```

追加仮定は J の有限性だけ。空積を含み、L9 の対象や写像空間の定義は変更していない。
Sp の有限積の工程は実際の対象と ∞ 極限錐まで完成した。
新規19宣言の正確な型・全前提は InfinityCategories/README.md の同名節に記録し、監査へ追加。
原典は BF 1978 §2、HA §1.4.2、HTT 4.2.4.1 の双対、Kerodon 7.5.4.6。

Sp の引き戻し・塔、元の非反転の end・q_x と反転係数の直接比較、余極限側、
E2a 完了後の E2b 適用は未完了。γ3 は継続中。

検証：対象集約 `HomotopyLimits` のビルド成功（4593 jobs）、公開1170宣言の `#check @` と
公理監査成功（標準3公理のみ）。新規2ファイルの警告・sorry・追加公理はない。
他担当の依存812ソースは全て追跡済み・コミット済み・変更なし。
検証ログは `/tmp/gamma3-spectrum-finite-products-aggregate.log` と
`/tmp/gamma3-spectrum-finite-products-audit.log`。


### γ3c：Sp の引き戻し構造射の単射性と随伴比較

`SmashMonomorphisms` は、基点保存の二つの単射が smash の基礎単体写像でもモノ射を与えると
各次数の具体的表示から証明した。任意の左因子の作用についても公開し、Kan 性は仮定しない。
`SpectrumPullbackMonomorphisms` では点つき引き戻しから通常積への標準射の基礎モノ射性、
引き戻し構造射と二項積の構造射の厳密な可換式を証明した。

```lean
pullbackSigma_mono {E X B : KanSequence.{u}}
    (f : KanSequence.Hom E B) (g : KanSequence.Hom X B)
    (hE : ∀ n, Mono (E.sigma n).right) (hX : ∀ n, Mono (X.sigma n).right) (n : ℕ) :
  Mono (KanSequence.pullbackSigma f g n).right
```

元の二列の構造射の単射性だけを使い、底の列の構造射や f、g の fibration 性は不要。
L9 の実際の OmegaSpectrum の cospan には元の sigma_mono から適用できる。

`SpectrumPullbackAdjoints` は loop と引き戻しの厳密な標準同型と両射影の式を構成した。
実際の比較射 `pullbackAdjointMap f g n` を定義し、引き戻し構造射の随伴が
この同型の下で比較射に等しいことを `pullbackSigma_adjoint` で証明した。
一脚 f が各段で fibration のときの `pullbackSequence_omega_iff` は、
引き戻し列の Ω 条件をこの比較射の全基点・全自然数次数の π_* 同型性へ同値で帰着する。
元の三列の Ω 条件から比較射の π_* 同型性を導く定理、実際のスペクトル錐の束ね直し、
豊穣 Hom の fibration 条件と ∞ 極限性は未完了。この段階を引き戻し全体の完成と数えない。

新規14宣言の正確な型・全前提は InfinityCategories/README.md の同名節へ記録し、監査へ追加。
原典は BF 1978 §2、HA §1.4.2、Goerss–Jardine I §§7–8、HTT 4.2.4.1。
Sp の塔、非反転の比較、余極限側、E2a 完了後の E2b 適用も未完了で、γ3 は継続中。

検証：対象集約 `HomotopyLimits` のビルド成功（4605 jobs）、公開1184宣言の `#check @` と
公理監査成功（標準3公理のみ）。新規3ファイルの警告・sorry・追加公理はない。
他担当の依存821ソースは全て追跡済み・コミット済み・変更なし。
検証ログは `/tmp/gamma3-spectrum-pullback-structure-aggregate.log` と
`/tmp/gamma3-spectrum-pullback-structure-audit.log`。


### E2a-1

```lean
universe u
open CategoryTheory MonoidalCategory
open scoped BigOperators
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.EInfinity

Operad (A : Type u) [CommRing A] : Type (u + 1)
schurFunctor (A : Type u) [CommRing A] (S : SymmetricSequence (Complex A)) :
  Complex A ⥤ Complex A

namespace Operad
variable {A : Type u} [CommRing A]

arity (P : Operad A) (n : ℕ) : Complex A
rightAction (P : Operad A) (n : ℕ) (σ : Equiv.Perm (Fin n)) : P.arity n ⟶ P.arity n
composition (P : Operad A) (n : ℕ) (s : Fin n → ℕ) :
  P.arity n ⊗ tensorFamily n (fun i => P.arity (s i)) ⟶ P.arity (∑ i, s i)
Algebra (P : Operad A) : Type (u + 1)
AlgebraHom {P : Operad A} (X Y : P.Algebra) : Type u

Algebra.instCategory {P : Operad A} : Category.{u} P.Algebra
Algebra.forget (P : Operad A) : P.Algebra ⥤ Complex A
Algebra.forget_faithful (P : Operad A) : (Algebra.forget P).Faithful

schurUnit (P : Operad A) (K : Complex A) : K ⟶ (schurFunctor A P.sequence).obj K
schurUnitNatTrans (P : Operad A) : 𝟭 (Complex A) ⟶ schurFunctor A P.sequence
freeAlgebra (P : Operad A) (K : Complex A) : P.Algebra
freeAlgebraFunctor (P : Operad A) : Complex A ⥤ P.Algebra
freeAlgebraFunctor_forget (P : Operad A) :
  P.freeAlgebraFunctor ⋙ Algebra.forget P = schurFunctor A P.sequence

schurAction_generators (P : Operad A) (K : Complex A) (n : ℕ) :
  (P.arity n ◁ TensorPowers.map (P.schurUnit K) n) ≫ P.schurAction K n =
    schurι A P.sequence K n

namespace Algebra
variable {P : Operad A}

evaluation (X : P.Algebra) : (schurFunctor A P.sequence).obj X.carrier ⟶ X.carrier
evaluation_action (X : P.Algebra) (n : ℕ) :
  P.schurAction X.carrier n ≫ X.evaluation =
    (P.arity n ◁ TensorPowers.map X.evaluation n) ≫ X.action n
evaluationHom (X : P.Algebra) : P.freeAlgebra X.carrier ⟶ X
schurLift {K : Complex A} (X : P.Algebra) (f : K ⟶ X.carrier) :
  (schurFunctor A P.sequence).obj K ⟶ X.carrier
liftHom {K : Complex A} (X : P.Algebra) (f : K ⟶ X.carrier) : P.freeAlgebra K ⟶ X
schurUnit_liftHom {K : Complex A} (X : P.Algebra) (f : K ⟶ X.carrier) :
  P.schurUnit K ≫ (X.liftHom f).hom = f
freeAlgebraHom_ι {K : Complex A} {X : P.Algebra} (f : P.freeAlgebra K ⟶ X) (n : ℕ) :
  schurι A P.sequence K n ≫ f.hom =
    (P.arity n ◁ TensorPowers.map (P.schurUnit K ≫ f.hom) n) ≫ X.action n
freeAlgebraHom_ext {K : Complex A} {X : P.Algebra} {f g : P.freeAlgebra K ⟶ X}
  (h : P.schurUnit K ≫ f.hom = P.schurUnit K ≫ g.hom) : f = g
liftHom_restrict {K : Complex A} {X : P.Algebra} (f : P.freeAlgebra K ⟶ X) :
  X.liftHom (P.schurUnit K ≫ f.hom) = f
evaluationAlgebraNatTrans (P : Operad A) :
  forget P ⋙ P.freeAlgebraFunctor ⟶ 𝟭 P.Algebra

end Algebra

freeAlgebraHomEquiv (P : Operad A) (K : Complex A) (X : P.Algebra) :
  (P.freeAlgebra K ⟶ X) ≃ (K ⟶ X.carrier)
freeAlgebraAdjunction (P : Operad A) : P.freeAlgebraFunctor ⊣ Algebra.forget P
freeAlgebraAdjunction_homEquiv (P : Operad A) (K : Complex A) (X : P.Algebra) :
  P.freeAlgebraAdjunction.homEquiv K X = P.freeAlgebraHomEquiv K X
freeAlgebraAdjunction_unit_app (P : Operad A) (K : Complex A) :
  P.freeAlgebraAdjunction.unit.app K = P.schurUnit K
freeAlgebraAdjunction_counit_app (P : Operad A) (X : P.Algebra) :
  P.freeAlgebraAdjunction.counit.app X = X.evaluationHom

end Operad
end SerrePositivity.EInfinity
```


### γ3c：fibration の fiber・底から全空間の全次数を比較する補題

`GroupPointedFiveLemma` の最後の項が任意の基点付き集合でよい五項補題を、
`FibrationTotalPositive` で長完全列に適用した。底と指定 fiber の π_* 同型から
全空間の全正次数の全単射性を得る。π₁ の次の fiber の π₀ は群とせず、基本群も含めて検証した。

`FibrationComponentTransport` は、指定 fiber に頂点があることを仮定せず、
任意の底の頂点 b に写る全空間の成分をその fiber へ移す補題と完全性を証明した。
`FibrationTotalComponents` は任意の b 上の `fibrationFiberMapBase` を構成し、
全空間の π₀ の単射性と全射性を別々に検証して `fibrationTotal_piIsomorphism` を得た。
前提は底の π_* 同型、各全空間頂点の像の上の fiber の π_* 同型、
および全ての b 上の fiber の成分の全射性。
空の fiber の全基点条件から成分の全射性を推論していない。

`FibrationAllFibers` の `fibrationFiberMapBase_piIsomorphism_of_vertex` は
fiber に頂点がある場合の全次数比較を既存の fiber 比較へ渡す。
`fibrationFiberMapBase_piZero_surjective` は、元の全空間の頂点 e₀ と全空間・底の
π_* 同型から任意の b 上の fiber の成分の全射性を得る。
標的 fiber の成分を全空間で戻してから底の成分の単射性で源の fiber へ移すため、
源の fiber が空の可能性も検査する。L9 の各段では元の基点を e₀ として使える。
新規12宣言の正確な型・全前提は InfinityCategories/README.md の同名節へ記録し、監査へ追加した。
原典は Goerss–Jardine I §§7–8、Kerodon 3.2.6、BF 1978 §2、HTT 4.2.4.1。

引き戻し射影の fiber の標準同型と実際の pullbackAdjointMap への適用は次工程。
Sp の引き戻しの Ω 条件そのもの、実際の錐、豊穣 Hom の fibration 条件と ∞ 極限性は未完了。
Sp の塔、非反転の比較、余極限側、E2a 完了後の E2b 適用も未完了で、γ3 は継続中。

検証：対象集約 `HomotopyLimits` のビルド成功（4627 jobs）、公開1196宣言の `#check @` と
公理監査成功（標準3公理のみ）。新規5ファイルの警告・sorry・追加公理はない。
他担当の依存838ソースは全て追跡済み・コミット済み・変更なし。
検証ログは `/tmp/gamma3-fibration-total-comparison-aggregate.log` と
`/tmp/gamma3-fibration-total-comparison-audit.log`。


### γ3c：Sp の実際の引き戻し対象の Ω 条件と豊穣 Hom の普遍性

任意の引き戻し正方形で第二射影の fiber と元の第一脚の fiber の標準同型を、
底の頂点の等号を明示して構成した。Kan 性・非空性は不要で、比較に対する自然性も証明。
同型による表示の変更の下で π_* 同型と π₀ 全射を移す補題、および fiber の底の移送を整えた。
`pullbackComparison_piIsomorphism` は、三つの比較射が全基点 π_* 同型のとき、
一脚が Kan fibration の引き戻し間の実際の射も全基点 π_* 同型であることを与える。
零次数の検査には元の全空間の頂点を渡し、空の fiber の全射性を省略しない。

これを実際の `pullbackAdjointMap` に適用し、`pullbackAdjointMap_piIsomorphism` と
`pullbackSequence_omega` を証明した。元の三列の Ω 条件と f の段ごとの fibration 性だけを使う。
前回の構造射の単射性と合わせて実際の対象を構成した。

```lean
spectrumPullback {E X B : OmegaSpectrum.{u}} (f : E ⟶ B) (g : X ⟶ B)
    [∀ n, Fibration (f.app n).right] : OmegaSpectrum.{u}
```

各段は点つき通常引き戻しそのもので、置換は行わない。
二本の厳密な射影・合成の一致・小さい cospan の図式・実際の錐を構成した。
各段の極限性から `spectrumPullbackCone_hom_isLimit` で全ての実際の豊穣 Hom の普遍性も得た。
coherent nerve の錐 `spectrumPullbackInfinityCone` はあるが、Hom の左脚の fibration 性は未証明。
したがって Sp の引き戻しを `IsLimitCone` として公開する工程全体は未完了。

新規27宣言の正確な型・全前提は InfinityCategories/README.md の同名節へ記録し、監査へ追加。
原典は Goerss–Jardine I §§7–8、Kerodon 3.2.5–3.2.6、BF 1978 §2、HA §1.4.2、
HTT 4.2.4.1 の双対。Sp の塔、非反転の比較、余極限側、E2a 完了後の E2b 適用も未完了。
γ3 は継続中。

検証：対象集約 `HomotopyLimits` のビルド成功（4633 jobs）、公開1223宣言の `#check @` と
公理監査成功（標準3公理のみ）。新規6ファイルの警告・sorry・追加公理はない。
他担当の依存838ソースは全て追跡済み・コミット済み・変更なし。
検証ログは `/tmp/gamma3-spectrum-pullback-objects-aggregate.log` と
`/tmp/gamma3-spectrum-pullback-objects-audit.log`。


### γ3c：Sp の一脚 fibration の引き戻しの実際の ∞ 極限性

`RelativePointedHomLifting` は、単射な源の制限と標的の Kan fibration に対して、
点つき Hom の既存パラメータ上の族・指定部分・底への合成を同時に保つ相対ホーン充填を証明した。
`SpectrumHomHornFamilies` は、源スペクトルの構造射の単射性を使ってその充填を段ごとに反復し、
構造条件を満たす実際の族を構成した。
`SpectrumHomFibrations` は族を L9 の全切断写像空間へ束ね、任意の X と各段が fibration の
p : Y → Z に対する実際の豊穣 Hom の後合成写像の fibration 性を証明した。
源の単射な構造射は既存の OmegaSpectrum の定義に含まれるものを使う。

前回の錐の全豊穣 Hom の普遍性と合わせ、主定理を得た。

```lean
spectrumPullbackInfinityCone_isLimit {E X B : OmegaSpectrum.{u}}
    (f : E ⟶ B) (g : X ⟶ B) [∀ n, Fibration (f.app n).right] :
  IsLimitCone (spectrumPullbackInfinityCone f g)
```

左脚だけが各段で Kan fibration ならよく、右脚は任意。
実際の対象、単射な構造射、全基点の Ω 条件、各段と豊穣 Hom の普遍性、Hom の左脚の
fibration 性を全て検証した。Sp の指定された引き戻しの工程は ∞ 極限錐まで完成した。
原典は BF 1978 §2、HTT A.3.3、HA §1.4.2、HTT 4.2.4.1 の双対、
Kerodon 7.5.3.12・7.5.4.6。新規6宣言の正確な型・全前提は README の同名節へ記録し、監査へ追加。

Sp の fibration の塔、非反転の比較、余極限側、E2a 完了後の E2b 適用は未完了。
γ3 全体は継続中。

検証：対象集約 `HomotopyLimits` のビルド成功（4636 jobs）、公開1229宣言の `#check @` と
公理監査成功（標準3公理のみ）。新規3ファイルの警告・sorry・追加公理はない。
他担当の依存838ソースは全て追跡済み・コミット済み・変更なし。
検証ログは `/tmp/gamma3-spectrum-pullback-infinity-aggregate.log` と
`/tmp/gamma3-spectrum-pullback-infinity-audit.log`。


### γ3c：塔の相対比較の右持ち上げ性を極限へ移す準備

`TowerMaps` で、厳密に可換な各段の射から L9 の整合族の極限の間の実際の射を構成した。
射影の計算、恒等射・合成の保存を証明し、次段から
`pullback (dY n) (f n)` への相対比較 `towerMatchingMap` を与えた。

`TowerMatchingLifting` は、任意の左射 j に対し、初段と全相対比較の持ち上げ性から
塔の極限の射の持ち上げ性を構成する。次の標的成分と既存の源の前段の充填を
引き戻しへまとめ、ホーン上・底・遷移の三条件を保って帰納する。
`towerMap_rlp` は任意のクラス W への RLP を極限へ移し、
`towerMap_fibration` は初段と相対比較の fibration 性から極限の射の fibration 性を得る。
`towerMap_piIsomorphism_of_matching_rlp` は、両極限の Kan 性と初段・相対比較の全単射 RLP の下で
実際の極限の射の全基点・全自然数次数の π_* 同型を与える。
各段の fibration 性だけや各段の π_* 同型だけへ前提を弱めていない。

`RelativePointedHomLifting` に一般の pushout-product の持ち上げ性からの相対充填と、
anodyne な源・任意の単射パラメータ・Kan fibration の標的の場合の相対充填を追加した。
既存のホーン充填の公開型は保ち、一般の充填へ渡す形へ整理して再検証した。
次にこの補題を mapping path の塔の相対比較へ適用し、元の段ごとの π_* 同型と塔の
fibration 性から必要な全単射 RLP を構成する。Sp の塔の対象と ∞ 極限錐は未完了。
今回の条件付き判定を塔全体の完成とは数えない。

新規12宣言の正確な型・全前提は README の同名節へ記録し、監査へ追加した。
原典は Goerss–Jardine I §§7–8、HTT A.3.3、BF 1978 §2、HTT 4.2.4.1。
非反転の比較、余極限側、E2a 完了後の E2b 適用も未完了で、γ3 は継続中。

検証：対象集約 `HomotopyLimits` のビルド成功（4638 jobs）、公開1241宣言の `#check @` と
公理監査成功（標準3公理のみ）。新規2ファイルと変更した相対充填ファイルの警告・sorry・追加公理はない。
他担当の依存838ソースは全て追跡済み・コミット済み・変更なし。
検証ログは `/tmp/gamma3-tower-relative-lifting-aggregate.log` と
`/tmp/gamma3-tower-relative-lifting-audit.log`。


### γ3c：mapping path の塔の因子分解と源側の RLP・π_* 比較

`MappingPathNaturality` で自由 path の端点・定数 path と mapping path の可換正方形に対する
自然性を証明した。path、源、標的、定数 path の比較を厳密に保持する。
`MappingPathTowers` で中間の塔の遷移と、元の源・標的の極限への射および Unit を構成した。
Unit と Source の合成は恒等射、Unit と Target の合成は元の towerMap に厳密に等しい。

`RelativeFreePathLifting` は指定端点と底の path を保つ単射パラメータ上の相対充填を証明。
`MappingPathSourceLifting` は、標的側の縦射が Kan fibration なら mapping path の源射影の
相対比較が全ての単射への RLP を持つことを、二つの引き戻しの普遍性で証明した。
標的の各段が Kan、遷移が fibration のとき、極限の源射影も全ての単射への RLP を持つ。
源側の縦射と各段の比較射の π_* 同型性はこの RLP の前提には置かない。

両縦射が fibration なら mapping path 間の射も fibration となる。
両塔の各段が Kan、全遷移が fibration のとき中間の塔の極限の Kan 性を検証し、
`mappingPathTowerLimitSource_piIsomorphism` と `mappingPathTowerLimitUnit_piIsomorphism` で
源射影と定数 path の極限の比較が全基点・全自然数次数の π_* 同型であることを得た。

元の各段の比較が π_* 同型の場合の標的側の相対比較の RLP は未証明。
次に Target の極限の比較を検証し、元の塔の極限の射の π_* 同型性へ戻す。
Sp の塔の実際の対象と ∞ 極限錐はまだ未完了であり、今回の源側だけを塔全体の完成と数えない。
新規24宣言の正確な型・全前提は README の同名節へ記録し、監査へ追加した。
原典は Goerss–Jardine I §7、HTT A.3.3、BF 1978 §2、HTT 4.2.4.1。
非反転の比較、余極限側、E2a 完了後の E2b 適用も未完了で、γ3 は継続中。

検証：対象集約 `HomotopyLimits` のビルド成功（4648 jobs）、公開1265宣言の `#check @` と
公理監査成功（標準3公理のみ）。新規4ファイルの警告・sorry・追加公理はない。
他担当の依存844ソースは全て追跡済み・コミット済み・変更なし。
検証ログは `/tmp/gamma3-mapping-path-tower-source-aggregate.log` と
`/tmp/gamma3-mapping-path-tower-source-audit.log`。


### γ3c：mapping path の標的側の相対比較と塔の極限の π_* 同型

`RelativeFreePathBoundary` の `relativeFreePath_boundaryHornLift` は、自由 path の
両端点・底への合成・既存のホーン上の族を同時に保つ充填を構成する。
前提は底の点つき射の fibration 性とパラメータがホーンであることだけであり、
対象の Kan 性は要求しない。境界の Hom の積表示と相対 Hom 充填を用いる。

`MappingPathTargetLifting` で、可換正方形の両縦射が fibration なら
`mappingPathTargetMatchingMap` も fibration となることを証明した。
さらに四対象が Kan で両横射が全基点 π_* 同型なら、この相対比較は全ての単射への RLP を持つ。
前段の標的射影の RLP を引き戻し、次段の標的射影と二対三で比較し、
源の基点を明示して相対 Whitehead を適用する。

`TowerPiComparison` では、この相対比較の RLP を実際の極限の射
`mappingPathTowerLimitTarget` へ移した。前回の定数 path の比較と合成して、
`pointedTowerMap_piIsomorphism` を得た。正確な前提は、両塔の全段が点つき Kan 複体、
全遷移が fibration、比較が厳密可換で、各段の比較が全基点・全自然数次数の π_* 同型であること。
結論も実際の `FibrationTower.limit` 間の射の全基点・全次数の π_* 同型である。
比較射自身の fibration 性や matching map の RLP を追加の前提には置かない。

この定理は Sp の塔の Ω 条件を検証するための入力であり、
Sp の塔の実際の対象・構造射の単射性・Ω 条件・∞ 極限錐への適用は引き続き未完了。
非反転の比較、余極限側、E2a 完了後の E2b 適用も未完了で、γ3 は継続中。
原典：Goerss–Jardine I §§7–8、BF 1978 §2、HTT A.3.3、HTT 4.2.4.1。

新規7宣言の正確な型と全前提は README の同名節へ記録し、全てを
`scripts/audit_homotopy_limits.lean` の `#check @` と公理監査へ追加した。

検証：対象集約 `HomotopyLimits` のビルド成功（4653 jobs）、公開1272宣言の `#check @` と
公理監査成功（標準3公理のみ）。新規3ファイルの警告・sorry・追加公理はない。
他担当の依存846ソースは全て追跡済み・コミット済み・変更なし。
検証ログは `/tmp/gamma3-tower-pi-aggregate.log` と `/tmp/gamma3-tower-pi-audit.log`。


### γ3c：Sp の段ごとに fibration の塔の実際の ∞ 極限錐

`PointedTowers` は `FibrationTower.limit` の整合族の極限に基点を加え、射影・持ち上げ・
外延性と通常の極限錐 `pointedTowerCone_isLimit` を構成する。初段が Kan、遷移が fibration
なら点つき極限も Kan。`LoopTowers` は loop の右随伴性を用いて、極限の loop と loop の塔の
極限の厳密同型 `loopTowerIso` を構成し、各射影との可換式を証明する。

`SpectrumTowerSequence` は元の Kan 列の塔の段ごとの極限へ懸垂構造射を組み立てる。
随伴構造射と `loopTowerIso` の合成は各段の随伴構造射が誘導する実際の塔の極限の射に
厳密に一致する。`SpectrumTowerOmega` は前回の `pointedTowerMap_piIsomorphism` を適用し、
各元の列の Ω 条件から極限の列の全基点・全自然数次数の Ω 条件を証明した。

構造射の単射性には `SmashJointProjections` を使う。右因子の単体を識別する基点保存射の族は、
smash の単体も識別する。非基点の組と基点の具体的表示で基点へ潰れる場合も検査する。
`SpectrumTowerMonomorphisms` は元の全構造射が単射なら極限の構造射も単射であることを証明。
この単射性の証明自体には、遷移の fibration 性や Ω 条件を使わない。

`SpectrumTowers` の `spectrumTower X d` は、各段を置換せず、上の Kan 性・単射性・Ω 条件で
L9 の Ω スペクトルに束ねた実際の極限対象である。射影を通常の錐にまとめ、各スペクトル段で
点つき極限の普遍性を検証し、既存の全切断の族の定理で全ての実際の豊穣 Hom の極限性を得る。
隣接遷移の Hom の fibration 性には既存の `spectrumHomMap_fibration` を適用した。

主要定理 `spectrumTowerInfinityCone_isLimit` の前提は、
`X : ℕ → OmegaSpectrum`、`d : ∀ n, X (n+1) ⟶ X n` と
`[∀ n k, Fibration ((d n).app k).right]` のみ。
結論は `IsLimitCone (spectrumTowerInfinityCone X d)`。
添字は `AsSmall ℕᵒᵖ`、通常図式は `AsSmall.down ⋙ Functor.ofOpSequence d`、
錐の頂点は実際の `spectrumTower X d` である。
Hom の極限性や追加の比較同値・Ω 条件を前提に置かない。

これにより、γ3c で指定された 𝒮 と Sp の有限積・一脚 fibration の引き戻し・fibration の塔は、
いずれも実際の対象と錐について ∞ 極限錐であることが揃った。
γ3 全体は継続中。非反転の元の比較射の導来 fiber と反転比較との直接の橋渡し、
余極限側、E2a 完了後の E2b 適用は引き続き未完了。
原典：Goerss–Jardine I §§7–8、BF 1978 §2、HA §1.4.2、HTT A.3.3、HTT 4.2.4.1 の双対。

新規35宣言の正確な型・全前提を README の同名節へ記録し、
`scripts/audit_homotopy_limits.lean` に `#check @` と `#print axioms` を追加した。

検証：対象集約 `HomotopyLimits` のビルド成功（4660 jobs）、公開1307宣言の `#check @` と
公理監査成功（標準3公理のみ）。新規7ファイルの警告・sorry・追加公理はない。
他担当の依存846ソースは全て追跡済み・コミット済み・変更なし。
検証ログは `/tmp/gamma3-spectrum-towers-aggregate.log` と `/tmp/gamma3-spectrum-towers-audit.log`。


### γ3b：元の q_x と反転比較 q′ の同値判定、および元の比較からの極限性

`ReflectedConeLimitLift` で Kan 複体間のホモトピー同値性が反転で検出されることと、
任意の錐の厳密極限への射が反転の極限保存同型と可換であることを証明した。
錐の厳密極限性は要求しない。二重反転の自然同型で元の射へ戻す。

`ConeComparisonReflection` は任意の錐の比較を
`bousfieldKanConeComparison c = limit.lift H c ≫ bousfieldKanLimitComparison H`
と厳密に分解する。元と反転後の標準比較 κ の同値性を消去し、両極限への射を比較する。
離散 Kan 図式、一脚 fibration の Kan cospan、Kan fibration の塔について、
必要な κ の同値性と厳密極限の Kan 性を検証して、比較の同値性の一致を得た。
反転した end と元の end を同一視することはなく、中間の厳密極限の保存同型を使う。

`RepresentableReflection` の三つの `representableComparison_reflection_*_iff` は、
局所 Kan な単体的圏の実際の Hom 錐にこの判定を適用し、元の
`representableHomotopyLimitComparison c x` が同値であることと、
`reflectedRepresentableComparison c x` が同値であることの同値を証明した。
cospan には Hom の左脚の fibration 性、塔には全隣接遷移の Hom の fibration 性を要求する。
Hom 錐そのものが厳密極限であることは、三形状のいずれの定理にも要求しない。

`RepresentableLimitCriterion` の三つの
`strictCoherentCone_isLimit_of_*_representableComparison` は、元の q_x の同値性を全 x で
仮定して `IsLimitCone (strictCoherentCone c)` を導く共有定理である。
反転比較を ULift し、反転 end から実際の coherent 錐の切断模型への比較と合成して、
既存の native な極限判定へ渡す。局所 Kan 性と形状に応じた Hom の fibration 性は明示する。

これは三形状で元の q_x を入力とする十分条件を証明したもの。
元の q_x の同値性と native な極限性の逆向き、元の比較射の導来 fiber と錐の pinched Hom
との直接比較、一般形状の元と反転 end の直接比較は、引き続き未完了。
余極限側と E2a 完了後の E2b 適用も未完了で、γ3 は継続中。
原典：HTT 4.2.4.1 の限定形、Kerodon 7.5.3.12・7.5.4.6、2.4.5、4.6.7。

新規15宣言の正確な型・全前提を README の同名節へ記録し、
全ての `#check @` と `#print axioms` を監査に追加した。

検証：対象集約 `HomotopyLimits` のビルド成功（4664 jobs）、公開1322宣言の `#check @` と
公理監査成功（標準3公理のみ）。新規4ファイルの警告・sorry・追加公理はない。
他担当の依存846ソースは全て追跡済み・コミット済み・変更なし。
検証ログは `/tmp/gamma3-representable-limit-criterion-aggregate.log` と
`/tmp/gamma3-representable-limit-criterion-audit.log`。


### γ3b：元の q_x の同値性と native な ∞ 極限性の両向きの判定

`UniverseHomotopyReflection` は、持ち上げた二射の実際の単体的ホモトピーを元の宇宙へ戻す
`uliftHomotopyDown` と、持ち上げた射のホモトピー逆を充満性で戻す
`homotopyEquivalence_of_ulift` を構成した。これにより
`ulift_homotopyEquivalence_iff` で、宇宙の持ち上げの前後のホモトピー同値性が同値となる。
この宇宙の移送自体には、元・持ち上げ後のいずれの単体集合にも Kan 性を要求しない。

`RepresentableLimitEquivalence` は、反転 end からの切断比較の後合成を消去し、
ULift の同値検出で反転比較 q′ の同値性へ戻す中間判定を構成した。
一般の添字圏では、反転 end から切断空間への比較の同値性を明示した前提に置く。
三形状では、この前提を既存の実際の比較定理で検証した。

主要定理は `strictCoherentCone_isLimit_iff_discrete_representableComparison`、
`strictCoherentCone_isLimit_iff_cospan_representableComparison`、
`strictCoherentCone_isLimit_iff_tower_representableComparison`。
結論はそれぞれ
`IsLimitCone (strictCoherentCone c) ↔ ∀ x, IsSimplicialHomotopyEquivalence
  (representableHomotopyLimitComparison c x)`。
離散図式では局所 Kan 性のみで、添字の有限性・非空性は要求しない。
cospan では全 x で Hom の左脚が fibration、塔では全 x・全隣接遷移で Hom が fibration
であることを追加する。Hom 錐の厳密極限性、元の q_x の fibration 性、追加の比較同値は
三つの主要定理の前提に置かない。

これで指定三形状について、前回の十分条件の逆向きも証明された。
元の q_x の導来 fiber と錐の pinched Hom の直接比較、および可縮性による判定への
元の q_x を使った直接の接続は引き続き未完了。一般形状の end の直接比較、
余極限側、E2a 完了後の E2b 適用も未完了で、γ3 全体は継続中。
原典：HTT 4.2.4.1 の限定形、Kerodon 7.5.3.12・7.5.4.6、2.4.5、4.6.7。

新規7宣言の `#check @` と `#print axioms` を監査に追加し、正確な型・全前提を
README の同名節に記録した。

検証：対象集約 `HomotopyLimits` のビルド成功（4666 jobs）、公開1329宣言の `#check @` と
公理監査成功（標準3公理のみ）。新規2ファイルの警告・sorry・追加公理はない。
他担当の依存846ソースは全て追跡済み・コミット済み・変更なし。
検証ログは `/tmp/gamma3-representable-limit-equivalence-aggregate.log` と
`/tmp/gamma3-representable-limit-equivalence-audit.log`。


### γ3b：元の q_x の全導来 fiber の可縮性による三形状の両向きの極限判定

`IntervalHomBoundary` は、二つの単位の余積からの内部 Hom の積表示を構成し、
単射な二端点包含への制限が fibration であることから、通常の区間の両端点の同時評価
`intervalHomEndpoints` の Kan fibration 性を証明した。
第一成分は終点一、第二成分は始点零。既存の可逆 path の包含の同型を利用している。

`KanComparisonFibers` の `kanEquivalencePathReplacementMap_fibration` は、
Kan 複体間の任意の射 q の可逆 path 置換の終点射が Kan fibration であることを証明する。
元の始域のホーンを先に充填し、標的の両端点を同時指定して path を充填する。
元の q の fibration 性は不要。既存の `comparisonFiber q b` はその終点射の頂点 fiber
そのものであり、任意の q と b について Kan 性を得た。

`homotopyEquivalence_iff_comparisonFiber_isContractibleKan` は、Kan 複体間の任意の射で
`IsSimplicialHomotopyEquivalence q ↔ ∀ b, IsContractibleKan (comparisonFiber q b)` を証明。
逆向きは path 置換の終点射を右ファイブレーションとして扱い、全頂点 fiber の可縮性から
trivial Kan fibration 性を得て、その同値性を元の射へ戻す。空の始域・標的も除外しない。

`RepresentableFiberCriterion` は任意の通常の小圏について、元の q_x の同値性をその
全導来 fiber の可縮性と同値にした。指定三形状では前回の実際の錐の極限判定と接続し、
`strictCoherentCone_isLimit_iff_discrete_comparisonFiber`、
`strictCoherentCone_isLimit_iff_cospan_comparisonFiber`、
`strictCoherentCone_isLimit_iff_tower_comparisonFiber` を公開した。

三定理の結論は
`IsLimitCone (strictCoherentCone c) ↔ ∀ x b,
  IsContractibleKan (comparisonFiber (representableHomotopyLimitComparison c x) b)`。
b は元の `bousfieldKanHolim (simplicialHomDiagram F x)` の全頂点を走る。
局所 Kan 性に加え、cospan では Hom の左脚の fibration 性、塔では Hom の全隣接遷移の
fibration 性を要求する。離散図式には添字の有限性・非空性を要求しない。
元の q_x の fibration 性、Hom 錐の厳密極限性、追加の比較同値は三定理の前提に置かない。

これにより γ3b の指定三形状について、A3d に基づく native な極限性を元の q_x の導来 fiber
の可縮性へ両向きに帰着できた。ただし、錐の pinched Hom と元の導来 fiber の実際の比較射を
直接構成したわけではない。この直接比較、一般形状の end の直接比較、余極限側、
E2a 完了後の E2b 適用は引き続き未完了で、γ3 全体は継続中。
原典：HTT 4.2.4.1 の限定形、Kerodon 4.5.3.24・7.5.3.12・7.5.4.6、Goerss–Jardine I §7。

新規17宣言の `#check @` と `#print axioms` を監査に追加し、README の γ3 冒頭の現在地も更新。
正確な型・全前提は README の同名節に記録した。

検証：対象集約 `HomotopyLimits` のビルド成功（4669 jobs）、公開1346宣言の `#check @` と
公理監査成功（標準3公理のみ）。新規3ファイルの警告・sorry・追加公理はない。
他担当の依存846ソースは全て追跡済み・コミット済み・変更なし。
検証ログは `/tmp/gamma3-representable-fiber-criterion-aggregate.log` と
`/tmp/gamma3-representable-fiber-criterion-audit.log`。


### γ3b：同じ底上の源の比較が誘導する導来 fiber の実際の射と weighted な錐への適用

`ComparisonFiberSource` は、既存の `comparisonFiber p b` の path 成分と源成分を取り出し、
整合する二成分からの持ち上げと外延性を構成した。標的 B が Kan のとき、
`comparisonFiberSource p b : comparisonFiber p b ⟶ E` が Kan fibration であることを証明。
元の p の fibration 性も、E の Kan 性もこの射影の fibration 性には要求しない。
両端点を指定する区間の内部 Hom の充填を使い、源成分をそのまま保持する。

`ComparisonFiberFunctor` の `comparisonFiberMap p q f hf b` は、同じ底上の可換図式
`f ≫ q = p` が誘導する実際の射。path 成分と固定頂点 b を保持し、源成分にだけ f を適用する。
その源射影との可換正方形は厳密な引き戻しであり、Kan 性なしで普遍性を構成した。
E・D・B が Kan、f がホモトピー同値なら、この実際の fiber 比較射もホモトピー同値。
導来 fiber の源射影の fibration 性に、可逆 path の相対持ち上げを使う既存の同値の
引き戻し定理を適用した。元の p・q の fibration 性は要求しない。

`WeightedConeDerivedFiberComparison` は主可換式
`weightedStrictConeFamilyComparison c x ≫ coneSectionRestriction ... =
  reflectedStrictConeSectionsComparison c x`
へこの構成を適用する。
`weightedStrictConeFamilyFiberComparison c x b` は、反転・ULift 後の切断比較の導来 fiber から、
native な切断の制限の同じ頂点 b 上の導来 fiber への実際の射である。
源成分で weighted な錐全体の比較と厳密に可換であることを記録した。
局所 Kan 性の下で、この実際の射がホモトピー同値であることも証明した。
添字圏 I と通常の錐 c は任意であり、Hom の fibration 性や厳密極限性は要求しない。

この工程の fiber は `reflectedStrictConeSectionsComparison` の fiber である。
元の非反転 q_x の fiber との直接比較、および native な制限の導来 fiber と錐の pinched Hom
の直接比較をすべて閉じたわけではない。これらの残る比較 span、一般形状の end の直接比較、
余極限側、E2a 完了後の E2b 適用は引き続き未完了で、γ3 は継続中。
原典：HTT 4.2.4.1、Kerodon 4.5.3.24・7.4.1.6・7.5.4.6。

新規17宣言の `#check @` と `#print axioms` を監査に追加し、正確な型・全前提を
README の同名節に記録した。γ3 冒頭の現在地もこの実際の fiber 比較まで更新した。

検証：対象集約 `HomotopyLimits` のビルド成功（4672 jobs）、公開1363宣言の `#check @` と
公理監査成功（標準3公理のみ）。新規3ファイルの警告・sorry・追加公理はない。
他担当の依存846ソースは全て追跡済み・コミット済み・変更なし。
検証ログは `/tmp/gamma3-weighted-cone-derived-fiber-aggregate.log` と
`/tmp/gamma3-weighted-cone-derived-fiber-audit.log`。

### γ3b：標的の同値が誘導する実際の導来 fiber の比較


Kan 複体間の `p : E ⟶ B` と `g : B ⟶ D`、頂点 `b : B _⦋0⦌` に対して、
実際の射
`comparisonFiberPost p g b : comparisonFiber p b ⟶ comparisonFiber (p ≫ g) (g.app _ b)`
を構成した。可逆 path を g で後合成し、元の源成分を保持する。
`comparisonFiberPost_source` と `comparisonFiberPost_path` はこの二成分の厳密な等式。

`comparisonFiberPost_homotopyEquivalence` の前提は E・B・D の Kan 性と g の単体的
ホモトピー同値性であり、p の fibration 性や E・fiber の非空性は要求しない。
path 置換の全空間の比較は、元の源への二つの自明 Kan fibration との可換式から、
g の同値性なしでも同値となる。全空間と底が同値な Kan fibration の正方形から
各 fiber の実際の比較の同値性を得て、部分型の頂点 fiber の模型へ厳密な同型で戻した。

空の fiber を含めるため、全基点・全次数の `KanPiIsomorphism` だけで結論せず、
fiber の π₀ の全射性を別に証明する。全空間の π₀ の全射性、底の π₀ の単射性と
fibration の成分持ち上げからこれを得る。源に頂点がある場合は点つき Whitehead を使い、
頂点がない場合は π₀ の全射性から標的も全次数で空であることを確認する。

既存の同じ底上の源の比較 `comparisonFiberMap` と合わせ、導来 fiber の源と標的の
同値による実際の比較が使える。元の非反転 q_x と錐の pinched Hom の直接比較、
一般形状の end の直接比較、余極限側、E2a 完了後の E2b 適用は引き続き未完了。
この補助比較を γ3 全体の完成とは数えない。
原典：HTT 4.2.4.1、Kerodon 7.4.1.6・7.5.4.6、Goerss–Jardine I §§7–8。

新規5ファイル・21宣言を集約と専用監査へ追加した。正確な型・全前提は
README の同名節と `scripts/audit_homotopy_limits.lean` の `#check @` を正本とする。

検証：対象集約 `HomotopyLimits` のビルド成功（4677 jobs）、公開1384宣言の `#check @` と
公理監査成功（標準3公理のみ）。新規5ファイルの警告・sorry・追加公理はない。
他担当の依存846ソースは全て追跡済み・コミット済み・変更なし。
ログ：`/tmp/gamma3-comparison-fiber-post-aggregate.log`、
`/tmp/gamma3-comparison-fiber-post-audit.log`。

### γ3b：任意の coherent な錐の pinched Hom と選んだ切断比較の導来 fiber


`rightFibrationHomDerivedFiberMap r c x d` は、選んだ表現可能な比較
`rightFibrationHomComparison r c x` の導来 fiber から、比較 span の始点評価
`rightFibrationMappingEvaluation r c x` の同じ頂点 d 上の導来 fiber への実際の射である。
span の切断による源成分の作用と、底の可逆 path が保持されることを厳密な等式で記録した。
底 B が quasicategory なら、この実際の射はホモトピー同値である。
r 自体の Kan fibration 性、比較射の同値性、fiber の可縮性・非空性は要求しない。

既存の始点評価の fiber と全空間の pinched Hom の同値と合わせ、
`rightFibrationPinchedHomComparisonDerivedFiberEquivalence r c x d` を得た。
これは `pinchedHom d.val c` と選んだ比較の実際の導来 fiber の圏同値である。
E・B の quasicategory 性と r の right fibration 性を前提とする。

さらに錐の slice 射影へ適用し、頂点 fiber と切断空間の既存の同値で標的を移す。
`coneSectionDerivedFiberMap d c` はこの後合成による実際の fiber の射であり、
源成分を保持し、path は選んだ同値で後合成する。この射もホモトピー同値となる。
最終的に `conePinchedHom_sectionComparisonDerivedFiberEquivalence d c` は

```lean
QCatEquivalence (pinchedHom (X := sliceOver p) d c)
  (comparisonFiber (coneSectionHomComparison c d.vertex) (coneSectionDerivedFiberPoint d))
```

を与える。K、p、d、c は任意で、X の quasicategory 性だけを要求する。
strict な通常の錐、極限錐、可縮な fiber に制限しない。
`coneSectionDerivedFiberPoint d` は d の頂点 fiber の点を
`coneVertexFiberSectionEquivalence p d.vertex` の順射で写した点である。
この同値の逆には選択があるため、標準の切断制限の点との厳密な一致は主張しない。

未完了は、選んだ比較と標準の切断制限の fiber の照合、元の非反転 q_x の fiber への
直接比較、一般形状の end の直接比較、余極限側、E2a 完了後の E2b 適用。
既存の三形状の可縮性判定と、この任意の錐の fiber 比較は区別して保持し、γ3 は継続中。
原典：HTT 4.2.4.1、Kerodon 7.4.1.6・7.5.4.6。

新規2ファイル・12宣言を集約と専用監査へ追加した。README の γ3 冒頭の現在地も更新した。
正確な型・全前提は README の同名節と `scripts/audit_homotopy_limits.lean` の `#check @` に記録。

検証：対象集約 `HomotopyLimits` のビルド成功（4679 jobs）、公開1396宣言の `#check @` と
公理監査成功（標準3公理のみ）。新規2ファイルに警告・sorry・追加公理はない。
他担当の依存846ソースは全て追跡済み・コミット済み・変更なし。
ログ：`/tmp/gamma3-cone-section-derived-aggregate.log`、
`/tmp/gamma3-cone-section-derived-audit.log`。

### γ3b：標準の錐の点を保持する native な切断制限の導来 fiber と pinched Hom


`conePinchedHom_sectionRestrictionDerivedFiberEquivalence d c` を構成した。
X が quasicategory、`p : K ⟶ X`、`d c : JoinCone p` に対し、型は

```lean
QCatEquivalence (pinchedHom (X := sliceOver p) d c)
  (comparisonFiber (coneSectionRestriction c d.vertex) (coherentConeSectionPoint d))
```

である。K・p・d・c は任意。strict な通常の錐への制限、極限性、比較射の同値性、
fiber の可縮性や非空性は前提に要求しない。底の点は選んだ切断比較の像ではなく、
元の d を coslice へ curry した標準の `coherentConeSectionPoint d` そのもの。

証明の第一段では `coneMappingTotalIso c x` が始点評価と native な slice 制限を厳密に
対応させる式から、同じ底上の実際の fiber 射 `coneSliceDerivedFiberMap c x b` を作る。
これは源の厳密な同型から誘導される同値であり、元の点 b を変更しない。
その結果 `conePinchedHom_sliceRestrictionDerivedFiberEquivalence d c` を得る。

第二段では、slice・切断の標準比較を共通の `fixedEndpointConeSpace` へ移す。
図式の固定条件 c.property による移送を正規化した自然性を証明し、
`coneSliceEndpointComparison_restrict` と `coneSectionEndpointComparison_restrict` により、
両制限が同じ `coneEndpointRestriction c x` と厳密に可換であることを確認した。
それぞれから共通模型の導来 fiber への実際の射
`coneSliceEndpointDerivedFiberMap` と `coneSectionEndpointDerivedFiberMap` を構成し、
源と標的の標準比較の同値性から、両方がホモトピー同値であることを証明した。

最後に `coneEndpointComparison_point_eq d` で固定点を厳密に照合する。
標準の slice の点と標準の切断の点の共通模型での像は等しい。
零単体の普遍族を uncurry すると両方とも
`fst (join Δ[0] K) Δ[0] ≫ d.val` となるためである。
この照合自体には X の quasicategory 性や同値の逆の選択は不要。
共通模型上で同じ底の点を持つ二つの fiber の同値を合成して主定理を得た。

これで、任意の coherent な錐の pinched Hom と標準の切断制限の実際の導来 fiber の
直接比較は完了した。反転・ULift 後の切断比較からこの標準制限の fiber への実際の同値は
既存の `weightedStrictConeFamilyFiberComparison_homotopyEquivalence` にある。
元の非反転 q_x の fiber までの直接比較、一般形状の end の直接比較、余極限側、
E2a 完了後の E2b 適用は引き続き未完了。γ3 全体は継続中。
原典：HTT 4.2.4.1、Kerodon 7.4.1.6・7.5.4.6。

新規4ファイル・19宣言を集約と専用監査へ追加した。README の γ3 冒頭の現在地も更新した。
全公開宣言の正確な型・全前提は README の同名節と専用監査の `#check @` に記録。

検証：対象集約 `HomotopyLimits` のビルド成功（4683 jobs）、公開1415宣言の `#check @` と
公理監査成功（標準3公理のみ）。新規4ファイルに警告・sorry・追加公理はない。
他担当の依存846ソースは全て追跡済み・コミット済み・変更なし。
ログ：`/tmp/gamma3-native-restriction-derived-aggregate.log`、
`/tmp/gamma3-native-restriction-derived-audit.log`。

### γ3b：底の path による固定点の移送と反転・ULift 後の豊穣比較の導来 fiber


任意の添字圏 I と局所 Kan な単体的圏 C、通常の錐 c、同じ strict な図式上の任意の coherent
な錐 d に対して、`strictConePinched_reflectedDerivedFiberEquivalence c d` を構成した。
pinched Hom と `reflectedStrictConeSectionsComparison c (coherentNerveObject d.vertex)` の
導来 fiber の同値であり、点は元の d の標準切断点を頂点の表示の等式で移送した
`strictConeDerivedFiberPoint d` である。厳密極限性や Hom の fibration 性は要求しない。
既存の native な制限の fiber の同値と weighted な錐の実際の fiber 比較を合成する。

さらに end から切断への比較を除き、三形状では ULift 後の反転豊穣比較 q′ 自体の
導来 fiber まで同定した。公開定理は
`strictConePinched_reflectedEnd_discrete_equivalence`、
`strictConePinched_reflectedEnd_cospan_equivalence`、
`strictConePinched_reflectedEnd_tower_equivalence`。
x = `coherentNerveObject d.vertex` とすると、いずれも pinched Hom と

```lean
comparisonFiber ((SSet.uliftFunctor.{v, u}).map (reflectedRepresentableComparison c x))
  (strictConeReflectedEndPoint d hκ)
```

の圏同値を返す。hκ はこの形状の既存の end・切断比較の同値性の証明であり、
利用者に追加の同値性の前提を要求しない。三定理の前提は局所 Kan 性だけで、
離散図式の有限性、Hom の fibration 性、錐 c の厳密極限性は不要。
一般の I で同じ結論を使う補助定理は
`strictConePinched_reflectedEndDerivedFiberEquivalence c d hκ` であり、こちらは hκ を明示する。

固定点を回収するため、底の path に沿う実際の fiber の比較を追加した。
`kanFiberPathEndpointMap p e j` は、p の path の持ち上げ空間から端点 j 上の fiber への射。
全空間と底が Kan、p が fibration なら、両端点の射は実際のホモトピー同値になる。
これを元の射 p の path 置換へ適用した `comparisonFiberPathEquivalence p e` は、
元の p に fibration 性を要求せず、底の指定した可逆 path の両端の導来 fiber を同値にする。
Kan な底の辺から同じ移送を行う `comparisonFiberEdgeEquivalence p e` も公開した。

`comparisonFiberPostInverseEquivalence p g hg b` は、標的の同値 g の任意の点 b に対し、
選んだ逆による点 g⁻¹(b) 上の p の導来 fiber と、b 上の p≫g の導来 fiber の同値を返す。
b が g の厳密な像であることを要求しない。後合成の実際の fiber 射と、
g⁻¹≫g から恒等射へのホモトピーを b で評価した辺による移送を合成する。
三形状の `strictConeReflectedEndPoint` はこの選んだ逆で標準切断点を回収した点である。
等式による固定点の移送と path による移送を区別し、元の点のデータを保持する。

未完了は ULift を外す移送、反転した係数の q′ と元の非反転 q_x の fiber の直接比較、
一般形状の end の直接比較、余極限側、E2a 完了後の E2b 適用。γ3 全体は継続中。
原典：HTT 4.2.4.1、Kerodon 4.5.3.24・7.4.1.6・7.5.4.6。

新規5ファイル・15宣言を集約と専用監査へ追加した。README の γ3 冒頭の現在地も更新した。
正確な型と全前提は README の同名節と専用監査の `#check @` に記録。

検証：対象集約 `HomotopyLimits` のビルド成功（4688 jobs）、公開1430宣言の `#check @` と
公理監査成功（標準3公理のみ）。新規5ファイルに警告・sorry・追加公理はない。
他担当の依存846ソースは全て追跡済み・コミット済み・変更なし。
ログ：`/tmp/gamma3-reflected-end-derived-aggregate.log`、
`/tmp/gamma3-reflected-end-derived-audit.log`。

型一覧の記録の修正：直近三節の46宣言を括弧の深さを考慮して再抽出し、名前付き引数
`(X := ...)` で途中終了していた8宣言の型の末尾を README に復元した。
Lean ソースと監査は変更なし。4688 jobs・1430宣言の検証結果を保持し、文書の diff 検査も成功。

### γ3b：導来 fiber と ULift の厳密な交換、および元の宇宙の反転比較への移送


`uliftComparisonFiberIso p b` を構成した。型は

```lean
(SSet.uliftFunctor.{v, u}).obj (comparisonFiber p b) ≅
  comparisonFiber ((SSet.uliftFunctor.{v, u}).map p) (ULift.up b)
```

であり、`p : E ⟶ B`、`b : B _⦋0⦌` と B の Kan 性だけを前提に取る。
E の Kan 性、p の fibration 性、fiber の非空性・可縮性は要求しない。
ホモトピー型の存在だけでなく、既存の path 置換で定義した実際の導来 fiber の厳密な同型。

まず `uliftInternalHomComparison` を評価の ULift から curry して定義し、ULift の完全忠実性
でパラメータごとの逆を作る。各標準単体の全単射が実際の比較の成分であることを確認して
`uliftInternalHomIso` を得た。標準区間の宇宙の同型で始域を移した `uliftIntervalHomIso` は、
両端評価と標的への後合成に厳密に可換。Kan 複体の path は全て可逆であることを使い、
`uliftEquivalencePathIso` と、その包含・両端評価・後合成の可換式を得た。

ULift の引き戻し保存を型の極限保存と単体対象の後合成から証明した。
これと可逆 path の始点評価の可換式により `uliftPathReplacementIso p` を作った。
その同型は元の源への射影と終点評価を厳密に保持する。
最後に頂点 fiber と ULift の交換同型を合成して、元の p と b の導来 fiber を復元した。

三形状への適用は `strictConePinched_smallReflectedEnd_discrete_equivalence`、
`strictConePinched_smallReflectedEnd_cospan_equivalence`、
`strictConePinched_smallReflectedEnd_tower_equivalence`。
x = `coherentNerveObject d.vertex` とすると、pinched Hom と

```lean
(SSet.uliftFunctor.{v, u}).obj
  (comparisonFiber (reflectedRepresentableComparison c x)
    (strictConeSmallReflectedEndPoint d hκ))
```

の圏同値である。hκ は各形状の既存の end・切断比較の同値性の証明で、三定理の利用者に
追加の比較仮定は要求しない。局所 Kan 性のみを要求し、c の厳密極限性、Hom の fibration 性、
離散図式の有限性は不要。元の宇宙の点は既存の回収した点の ULift.down で定義する。
一般の添字圏で使う補助定理は `strictConePinched_smallReflectedEndDerivedFiberEquivalence` で、
この一般形には hκ を明示する。

ULift は比較射の内部から fiber 全体の外へ移した。pinched Hom の宇宙が max u v なので、
比較対象の宇宙を揃える ULift 自体は fiber 全体に残す。
係数の反転 q′ と元の非反転 q_x の fiber の直接比較、一般形状の end の直接比較、
余極限側、E2a 完了後の E2b 適用は未完了。γ3 全体は継続中。
原典：HTT 4.2.4.1、Kerodon 4.5.3.24・7.4.1.6・7.5.4.6。

新規6ファイル・30宣言を集約と専用監査へ追加。README の γ3 冒頭の現在地も更新した。
全公開宣言の正確な型と前提は README の同名節と専用監査の `#check @` に記録。
型一覧は括弧の深さを考慮して抽出し、名前付き引数を含む全30署名をソースから復元した。

検証：対象集約 `HomotopyLimits` のビルド成功（4694 jobs）、公開1460宣言の `#check @` と
公理監査成功（標準3公理のみ）。新規6ファイルに警告・sorry・追加公理はない。
他担当の依存846ソースは全て追跡済み・コミット済み・変更なし。
ログ：`/tmp/gamma3-ulift-comparison-fiber-aggregate.log`、
`/tmp/gamma3-ulift-comparison-fiber-audit.log`。

### γ3b：反転した係数から元の非反転 q_x の導来 fiber の反転への直接比較


任意の Kan 複体間の射 p と底の点 b について `oppositeComparisonFiberEquivalence p b` を構成した。

```lean
QCatEquivalence (comparisonFiber p b).op
  (comparisonFiber (SSet.opFunctor.map p) (SSet.opObjEquiv.symm b))
```

p の fibration 性や fiber の非空性・可縮性は要求しない。
頂点 fiber と反転の厳密な同型 `oppositeVertexFiberIso` を作り、元の path 置換の終点射を
反転して共通の fibration 模型とした。元の path 置換への切断はホモトピー同値であり、
反転しても同値となる。この切断が同じ底上で誘導する実際の fiber 射
`oppositeComparisonFiberSectionMap` の同値性を、strict・導来 fiber の比較と合成した。

係数図式 H の錐 c の元の標準比較 q と反転した比較 q′ は、それぞれ厳密極限への射と
極限標準比較 κ・κ′ の合成に分解する。`reflectedConeLimitLift` の厳密な可換式、
標的の同型による `comparisonFiberPostIsoEquivalence`、標的の同値と底の path による移送を
合わせ、反転した比較の fiber を元の比較の fiber の反転へ直接移した。
`bousfieldKanConeFiberReflection_{discrete,cospan,tower}_equivalence` は二つの κ の同値性を
指定形状で検証し、利用者に追加の比較同値の仮定を要求しない。
一般形 `bousfieldKanConeFiberReflectionEquivalence` は κ・κ′ の同値性と極限の Kan 性を明示する。
固定点 `bousfieldKanReflectedFiberPoint H hκ' b` は、κ′ の選んだ逆、反転の極限保存同型の逆、
元の κ の反転の順で回収し、最後に零次の反転の全単射で元の end の点に戻す。

strict な錐への適用は `strictConePinched_originalEnd_discrete_equivalence`、
`strictConePinched_originalEnd_cospan_equivalence`、`strictConePinched_originalEnd_tower_equivalence`。
x = `coherentNerveObject d.vertex` とすると、任意の coherent な錐 d について

```lean
QCatEquivalence (pinchedHom (X := sliceOver (strictCoherentDiagram F)) d (strictCoherentCone c))
  ((SSet.uliftFunctor.{v, u}).obj
    (comparisonFiber (representableHomotopyLimitComparison c x)
      (strictConeOriginalEndPoint d hκ hL')).op)
```

を与える。比較射は元の非反転 q_x そのもの。反転は fiber 全体に作用し、ULift は
pinched Hom の宇宙に揃えるため fiber 全体の外に置く。
離散図式は局所 Kan 性だけを要求し、有限性は不要。cospan は d の頂点が表す x に対する
Hom 図式の左脚の fibration 性、塔は同じ x に対する全隣接遷移の fibration 性を要求する。
錐 c 自体の厳密極限性・∞ 極限性はどの定理の前提にもしない。
一般形 `strictConePinched_originalEndDerivedFiberEquivalence` の追加の比較入力は三形状で検証した。

この結果は fiber 全体の反転を明示した直接比較であり、γ3b 冒頭の反転なしの模型の同定とは
区別する。fiber 全体の反転を外す実際の比較、一般形状の end の直接比較、余極限側、
E2a 完了後の E2b 適用は引き続き未完了。指定三形状の既存の全 fiber の可縮性判定は保持し、
γ3 全体は継続中。
原典：HTT 4.2.4.1、Kerodon 4.5.3.24・7.4.1.6・7.5.4.6。

新規5ファイル・19宣言を集約と専用監査へ追加。README の γ3 冒頭の現在地も更新した。
全宣言の正確な型・全前提は README の同名節と専用監査の `#check @` に記録。
型一覧は括弧の深さを考慮して抽出し、名前付き引数を含む全署名をソースから復元した。

検証：対象集約 `HomotopyLimits` のビルド成功（4699 jobs）、公開1479宣言の `#check @` と
公理監査成功（標準3公理のみ）。新規5ファイルに警告・sorry・追加公理はない。
他担当の依存846ソースは全て追跡済み・コミット済み・変更なし。
ログ：`/tmp/gamma3-original-end-fiber-aggregate.log`、
`/tmp/gamma3-original-end-fiber-audit.log`。

### γ3b：Kan な fiber の反転の除去と元の非反転 q_x の反転なしの直接比較


`kanOppositeComparison K : K.op ⟶ K` とそのホモトピー同値性を、任意の Kan 複体 K に対して
構成した。空の Kan 複体も含み、非空性・可縮性は要求しない。
まず局所 Kan な単体的圏で、反転した豊穣 Hom の ULift を左 pinched Hom へ移し、
左右の pinched 模型の同値を経由して右 pinched Hom へ移し、coherent Hom 比較の逆で
元の豊穣 Hom の ULift に戻す。この実際の射 `coherentHomOppositeComparison x y` は同値。

次に C を KanObject、一点空間から K への Hom として任意の K を実現する。
`pointKanObjectHomIso` の同型で左右を挟み、ULift の充満性で元の宇宙の射 K.op ⟶ K を取る。
ULift 後に逆を持つことをホモトピーの降下で元へ戻し、構成済みの実際の射の同値性を得た。
`kanOppositeEquivalence K` と、任意の宇宙の持ち上げに対する
`uliftKanOppositeEquivalence K` も公開した。
これらは既存の左右の比較の選んだ逆を含む。射についての厳密な自然性や二重反転の厳密な
往復則をこの構成の結論には含めない。

これを元の q_x の導来 fiber に適用し、fiber 全体の反転を外した。
三形状の公開定理は `strictConePinched_originalFiber_discrete_equivalence`、
`strictConePinched_originalFiber_cospan_equivalence`、
`strictConePinched_originalFiber_tower_equivalence`。x = `coherentNerveObject d.vertex` とすると、
型は

```lean
QCatEquivalence (pinchedHom (X := sliceOver (strictCoherentDiagram F)) d (strictCoherentCone c))
  ((SSet.uliftFunctor.{v, u}).obj
    (comparisonFiber (representableHomotopyLimitComparison c x)
      (strictConeOriginalEndPoint d hκ hL')))
```

であり、比較射・fiber のどちらにも反転を残さない。ULift は対象と Hom の宇宙を揃えるため
fiber 全体の外に置く。点 b_d は前工程と同じ `strictConeOriginalEndPoint` であり、元の coherent
な錐 d の標準切断点から、比較同値の逆・極限保存同型で回収した点を保持する。

離散図式は局所 Kan 性だけを要求し、有限性は不要。cospan は x に対する Hom 図式の左脚の
fibration 性、塔は同じ x に対する全隣接遷移の fibration 性を要求する。
通常の錐 c と coherent な錐 d は任意であり、c の厳密極限性・∞ 極限性を前提にしない。
一般形 `strictConePinched_originalFiberEquivalence` の追加の比較入力は三形状で検証している。

これで指定三形状の γ3b の元の q_x と pinched Hom の反転なしの直接比較まで実装済み。
既存の全 x・全 end の頂点 b に対する可縮性の両向きの判定と、𝒮・Sp の指定三形状の適用も
保持する。一般形状の end の直接比較、余極限側、E2a 完了後の E2b 適用は引き続き未完了で、
γ3 全体は継続中。
原典：HTT 4.2.4.1、Kerodon 4.6.5–4.6.7・7.4.1.6・7.5.4.6。

新規2ファイル・10宣言を集約と専用監査へ追加。README の γ3 冒頭の現在地も更新した。
全宣言の正確な型・全前提は README の同名節と専用監査の `#check @` に記録。
型一覧は括弧の深さを考慮して抽出し、名前付き引数を含む全署名をソースから復元した。

検証：対象集約 `HomotopyLimits` のビルド成功（4701 jobs）、公開1489宣言の `#check @` と
公理監査成功（標準3公理のみ）。新規2ファイルに警告・sorry・追加公理はない。
他担当の依存846ソースは全て追跡済み・コミット済み・変更なし。
ログ：`/tmp/gamma3-direct-original-fiber-aggregate.log`、
`/tmp/gamma3-direct-original-fiber-audit.log`。

### γ3 余極限側：着手時の文言と方針

極限側の指定三形状と元の q_x の導来 fiber の直接比較を保持したまま、余極限側へ進む。
既存の `Stable/Cocone.lean` の `JoinCocone`・`IsColimitCone` を native な定義として使い、
新しい余極限性の定義を作らない。通常の余錐 c を反対圏の通常の錐 c.op にし、局所 Kan な
反対の単体的圏の coherent nerve 上で既存の極限定理を適用する。
その錐を `reverseCocone` で反転し、coherent nerve の反対の標準同型と二重反転で元の値域へ戻す。
添字は nerve の反対の標準同型と ULift の反転の同型で元の通常の添字へ戻す。

初段は離散図式の Hom 条件による余極限判定を扱い、空余積を含む 𝒮 の余積へ接続する。
余錐の native な構成、標準の図式との一致、頂点・脚の元の通常の余錐との一致、余極限性の
証明を区別して検証する。双対化した図式上の条件付きの定理だけで 𝒮 の適用の完成とは数えない。
押し出し・逐次 homotopy 余極限では実際の模型と必要な cofibration 条件・Kan 置換も検証する。
一般形状の end の直接比較と、E2a 完了後の E2b 適用も後続に保持する。

再利用候補 `Stable/ConeOpposite.lean`・`ColimitReindex.lean`・`SquareDuality.lean` の依存閉包は
着手時点で他担当307ソース、全て追跡済み・コミット済み・変更なしであることを確認した。
原典：HTT 4.2.4.1、Kerodon 7.1・7.4–7.5、coherent nerve の反対の同型は Kerodon 4.6.7。

### γ3 余極限側：標準図式上の通常の余錐の native な表示と双対化


`strictNativeCocone c : JoinCocone (strictCoherentDiagram F)` を、任意の通常の小圏 I、
単体的圏 C、`F : I ⥤ C`、`c : Cocone F` に対して構成した。
固定図式は既存の `strictCoherentDiagram F` そのものであり、元の C の coherent nerve 内の
既存の native な余錐である。
`strictNativeCocone_vertex c` は頂点が元の c.pt の標準頂点に等しいことを証明する。

手順は次の通り。c.op の strict な錐を `reverseCocone` で反転し、添字を
`strictCoconeIndexIso I : U N(I) ≅ (U N(Iᵒᵖ)).op` で元の I へ戻す。
反対の単体的圏の coherent nerve の反転を `coherentOppositeReturnIso C` で元の値域へ戻す。
この時点の図式 `strictCoherentCoconeDiagram F` が元の標準図式に厳密に等しいことを、
`strictCoherentDiagram_opposite` と `strictCoherentCoconeDiagram_eq` で全単体について検証した。
通常の射列の反転と定値な豊穣 Hom の反対の一致、二重反転の自然性による。
頂点や辺だけの一致ではなく SSet の射の等式として照合している。

最後に固定図式の等式で余錐を正規化する。
`coherentCoconeOfDiagramEq` はこの移送で余錐の射・頂点・余極限性を保持する。
値域の同型による `coherentCoconePost` も native な余極限性を保存し反映する。
これらを既存の極限・余極限の反転の同値へ接続し、

```lean
strictNativeCocone_isColimit_iff (c : Cocone F) :
  IsColimitCone (strictNativeCocone c) ↔ IsLimitCone (strictCoherentCone c.op)
```

を公開した。この形式的な双対化は局所 Kan 性、c の通常の余極限性、図式の特別な形を
要求しない。後続の homotopy 余極限への適用では、局所 Kan 性と Hom 条件を具体的に検証する。
余錐の脚の元の通常の成分との照合、離散 Hom 条件からの余極限性、𝒮 の実際の余積・空余積、
homotopy 押し出し・逐次 homotopy 余極限の模型への適用は、この構成だけでは完成と数えない。
一般形状の end の直接比較と、E2a 完了後の E2b 適用も引き続き後続工程。
原典：HTT 4.2.4.1、Kerodon 4.6.7・7.1・7.4–7.5。

着手時の文言と方針を README に先に記録してから実装した。
新規5ファイル・24宣言を集約と専用監査へ追加。README の γ3 冒頭の現在地も更新した。
全宣言の正確な型・全前提は README の同名節と専用監査の `#check @` に記録。
型一覧は括弧の深さを考慮して抽出し、全署名をソースから復元した。

検証：対象集約 `HomotopyLimits` のビルド成功（4776 jobs）、公開1513宣言の `#check @` と
公理監査成功（標準3公理のみ）。新規5ファイルに警告・sorry・追加公理はない。
既存の Stable 側の双対化 API の再利用で、他担当の依存は916ソースとなり、
全て追跡済み・コミット済み・変更なしを確認した。
ログ：`/tmp/gamma3-native-cocones-aggregate.log`、`/tmp/gamma3-native-cocones-audit.log`。
