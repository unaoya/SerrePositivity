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
| γ3b | 錐の頂点 fiber と切断空間の同値、切断による表現可能な極限判定、三形状の transport の end の極限判定まで実装。反転した係数の weighted nerve から錐の全空間への実際の底上の射を構成。各 fiber の同値性と元の q_x との主比較は未完了 |
| γ3c | 𝒮 の空積は IsLimitCone として実装。SSet の積・fibration 引き戻し・塔の Kan 性を実装。𝒮 の残りと Sp は未完了 |

Sp では raw sHom の局所 Kan 性と極限の cofibrancy を省略せず、必要なら cofibrant-fibrant
置換後の錐を公開する。実装は `InfinityCategories/HomotopyLimits/` と専用監査に置く。

γ3b の部分 API は `HomotopyLimits` 集約と `scripts/audit_homotopy_limits.lean` に置く。
公開776宣言。`representableHomotopyLimitComparison c x` は実際の sHom から end への射、
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
正確な型・全前提は README と公開776宣言の監査に記録。
一般の coherent な錐の写像空間との比較は未完了なので、γ3b の完成とは数えない。

両脚が fibration の cospan では、中央の Kan 性から成分ごとの anodyne な自然変換を延長する。
その具体的な延長により、重み付き end の Kan 性と anodyne な制限の trivial Kan fibration 性、
`bousfieldKanLimitComparison_cospan_homotopyEquivalence` および
`representableHomotopyLimitComparison_cospan_homotopyEquivalence` を証明する。
後者には Hom 図式の極限性も必要。正確な型・全前提は README と公開776宣言の監査が正本。
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
Bousfield–Kan 重みに追加の未証明条件はない。正確な型は README と公開776宣言の監査に記録。
元の重みの相対境界と一脚での κ の同値性は末尾の実装で証明した。
coherent な錐の写像空間との比較と 𝒮・Sp への適用は未完了。

`cornerTensorIso j f` は重みの相対境界と pushout-product の二つの順序の間の交換同型。
`cornerTensorComparison_fac` は実際の相対境界射との可換性で、交換自体に Kan 性・単射性は不要。
`rightCorner_weightedCorner_anodyne` は元の重みの相対境界が anodyne、f が Mono のとき、
pushout-product の相対境界が anodyne であることを証明する。
これにより `weightedSectionsPre_cospan_leftFibration_trivialKanFibration` は中央と右端が Kan、
左脚が Fibration の cospan に対して、成分と元の中央の相対境界が anodyne な重みの制限を扱う。
`weightedSectionsPre_cospan_leftFibration_homotopyEquivalence` では両重みの右脚の Mono 性も要求する。
正確な型・全前提は README と公開776宣言の監査に記録。
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
正確な型・全前提は README と公開776宣言の監査に記録。
元の重み W → V の相対境界とその制限、一脚の場合の κ 全体は末尾の実装で証明した。
coherent な錐の写像空間との比較と 𝒮・Sp の適用は未完了。

元の重みの右脚の遷移は `bousfieldKanWeight_cospan_inr_anodyne` で anodyne と証明済み。
右端の over 圏の恒等射の始対象性と、中央の over 圏の恒等射の終対象性を使い、
終対象を付加する中間圏で left と right の anodyne な単射に分解する。
`joinUnion_pointBoundary_anodyne` は anodyne な部分複体の包含から作る相対的な点の錐を扱い、
`bousfieldKanWeight_cospan_inr_relativeCone_anodyne` は実際の遷移の像に適用した定理。
外側の最後のホーンも含む相対 coslice の Kan fibration 性から証明する。
正確な型・全前提は README と公開776宣言の監査に記録。
この相対錐と標準境界の同定、一脚の場合の κ 全体は末尾の実装で証明した。
coherent な錐の写像空間との比較と 𝒮・Sp の適用は未完了。

WithInitial の nerve と点の join の同定のため、射列の切断と元の圏の後半を構成した。
`initialNerveCut` は始対象を 0、元の対象を 1 に送る単調写像の先頭区間の逆像の頂点数。
`initialNerveCut_precomp` は全ての単体作用素との可換性、`initialNerveCut_map` は関手による保存。
`initialNerveOldFunctor` は全対象が新しい始対象でない部分を元の圏へ戻し、恒等・合成を保つ。
`initialNerveTail` は切断以後の射列、`initialNerveJoinSimplex` は次数ごとの join 型のデータ。
後半が空のときは補った空単体を使い、元の圏の非空性は要求しない。
正確な型・全前提は README と公開776宣言の監査に記録。
全データの単体的自然性と逆関係は下記の同型で証明した。
相対錐と標準境界の同定と一脚での κ は末尾の実装で証明した。
coherent な錐の写像空間との比較と 𝒮・Sp の適用も未完了。

点と nerve の join 型の単体から WithInitial の射列への逆向きの次数ごとの構成を追加した。
`augNerveObj`・`augNerveMap` は補った空単体を含む評価で、恒等・合成・再添字付けを保つ。
零頂点の場合は空の添字で処理し、元の圏の対象を選ばない。
`initialJoinChain` は切断より前を新しい始対象、後を元の射列としてつなぐ。
`initialJoinChain_star_iff` と `initialNerveCut_initialJoinChain` により切断が元に戻る。
C : Type u、[SmallCategory C] のみを仮定し、追加の非空性・忠実性は要求しない。
正確な型・全前提は README と公開776宣言の監査に記録。
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
元の圏の非空性や Kan 性は要求しない。正確な型・全前提は README と公開776宣言の監査に記録。
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
右脚の Fibration 性や未証明の境界条件は追加しない。正確な型・全前提は README と公開776宣言の監査が正本。
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
正確な型・全前提は README と公開776宣言の監査に記録。
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
正確な型・全前提は README と公開776宣言の監査に記録。
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
正確な型・全前提は README と公開776宣言の監査に記録。
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
正確な型・全前提は README と公開776宣言の監査に記録。
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
正確な型・全前提は README と公開776宣言の監査に記録。
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
正確な型・全前提は README と公開776宣言の監査に記録。
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
正確な型・全前提は README と公開776宣言の監査に記録。
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
正確な型・全前提は README と公開776宣言の監査に記録。
coherent cone の射影の transport と元の sHom 図式との自然な比較、
錐の pinched Hom と q_x の導来ファイバーの主比較、𝒮・Sp の残りの適用は継続中。
対象集約ビルド2265 jobs、公開776宣言の公理監査は標準三公理のみ。
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
正確な型・全前提は README と公開776宣言の監査に記録。
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
正確な型・全前提は README と公開776宣言の監査に記録。
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
正確な型・全前提は README と公開776宣言の監査に記録。
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
正確な型・全前提は README と公開776宣言の監査に記録。
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
正確な型・全前提は README と公開776宣言の監査に記録。
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
正確な型・全前提は README と公開776宣言の監査に記録。
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
正確な型・全前提は README と公開776宣言の監査に記録。
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
正確な型・全前提は README と公開776宣言の監査に記録。
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
正確な型・全前提は README と公開776宣言の監査に記録。
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
正確な型・全前提は README と公開776宣言の監査に記録。
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
正確な型・全前提は README と公開776宣言の監査に記録。
左 coslice の係数図式への接続、元の豊穣 Hom の図式・q_x との主比較、
𝒮・Sp の残りの適用は引き続き未完了。


### γ3b：反転したホモトピー同値の移送

`OppositeKanHomotopy` に直積・ULift と反転の同型、区間の反転による逆向きのホモトピー、
Kan 複体間のホモトピー同値の反転による保存を実装した。
公開宣言は `oppositeTensorIso`、`oppositeSimplicialHomotopy`、
`oppositeKanHomotopyEquivalence`、`uliftOppositeIso`。
正確な型と前提は README の対応節と公開776宣言の監査に記録。
係数図式の自然比較、元の q_x、𝒮・Sp の残りの適用は未完了。


### γ3b：反転した豊穣 Hom と左 coslice fiber の実際の比較

`CoherentLeftHomComparison` に、反対圏の標準右 Hom 比較を反対 nerve の同型で移し、
さらに反転する射を構成した。始域は `ulift (sHom(x,y).op)`、
終域は x の左 coslice 射影の y 上の fiber。
`coherentCosliceFiberComparison_homotopyEquivalence x y` は局所 Kan 性のみで
実際の比較射の単体的ホモトピー同値性を証明する。
途中の右 Hom と左 Hom の射とその同値性、端点の厳密な同型も公開した。
正確な型・全前提は README と公開776宣言の監査に記録。
係数図式全体への自然比較、元の q_x、𝒮・Sp の残りの適用は未完了。


### γ3b：標準 Hom 比較の豊穣関手による後合成との整合性

`CoherentHomPost` に対象・simplex・標準頂点の後合成の式と端点の同型を構成し、
`coherentHomComparison_post F x y` として単体集合の射の厳密な可換図式を証明した。
前提は二つの単体的圏と豊穣関手のみ。Kan 性を要求しない。
各 Hom の端点を標準対象へ移送し、豊穣単位則と最大元評価の自然性で証明する。
正確な型・全前提は README と公開776宣言の監査に記録。
添字圏の合成作用・高次整合性と左 coslice 側への接続、元の q_x、
𝒮・Sp の残りの適用は未完了。


### γ3b：左 coslice の係数評価の最小点の座標

`CoherentPathMinimum` に零を除いた path の最小点を定義し、包含への反単調性、
正の切断点での合成則、初点固定拡張による任意の添字変換との可換性を証明した。
既存 Core の `prependOrderHom` を再利用し、面・退化を含めて扱う。
`pathFirstMinimumMap j` は反転した初区間の標準単体への実際の射で、
`pathFirstMinimumMap_reindex α j` が重みの初区間の制限との厳密な自然性を与える。
Kan 性を要求しない。正確な型・全前提は README と公開776宣言の監査に記録。
実際の weighted nerve から左 coslice への射の組立てと元の q_x、
𝒮・Sp の残りの適用は未完了。


### γ3b：反転した weighted nerve の係数の評価と豊穣合成

`WeightedCoherentCoefficients` に反転を戻した係数の実際の評価射を構成し、
path の合成を係数図式の作用へ移す厳密な式と全ての面・退化との自然性を証明した。
`WeightedRepresentableCoefficients` で表現可能な係数へ適用し、
`weightedRepresentableCoefficient_comp` により図式の作用を通常の射の定値 simplex との
豊穣合成と同定した。Kan 性や極限性は要求しない。
正確な型・全前提は README と公開776宣言の監査に記録。
cone の全頂点と Hom の豊穣関手への組立て、実際の左 coslice 射、元の q_x、
𝒮・Sp の残りの適用は未完了。


### γ3b：weighted nerve から coherent な錐の全空間への実際の射

`WeightedConeSimplex` に全頂点と Hom の作用、単位則と合成則を備えた cone simplex を構成。
初点が x の標準頂点、初点以外の面が元の strict な図式であること、全ての面・退化との
整合性を証明した。`WeightedCosliceComparison` で join の同型により左 coslice に移し、
`weightedCoherentConeComparison F x` として元の図式の上の実際の射を構成した。
`weightedCoherentConeComparison_over` が底への射影との厳密な可換性を与える。
前提は strict な図式と単体的圏だけ。Kan 性・Hom の逆の選択を要求しない。
正確な型・全前提は README と公開776宣言の監査に記録。
構成した射の fiber の同値性、反転した係数の切断空間の移送と元の q_x、
𝒮・Sp の残りの適用は未完了。


### γ3b：一定の底の fiber 比較と反転した Hom の座標

`ReflectedPathCoordinates` に最小点と反転 path の最大点の厳密な対応を証明し、
一定係数の評価を既存の右 Hom の最大点による評価として表した。
`WeightedConstantFiber` に構成済みの射の一定の底での制限と、終点 F(i) の fiber への
実際の持ち上げを構成し、その元の cone simplex と非定値 Hom の作用を計算した。
`coherentLeftHomComparison_simplex` に既存の左 Hom 比較の simplex の反転による表示を証明。
Kan 性を要求しない。正確な型・全前提は README と公開776宣言の監査に記録。
二つの coherent simplex 全体の一致と実際の fiber 射の同値性、元の q_x と切断空間、
𝒮・Sp の残りの適用は未完了。
