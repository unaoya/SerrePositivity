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
| γ3b | 検出・導来 fiber・重み付き end・q_x と θκ 分解は実装。coherent な錐との比較、end の Kan 性・同値不変性は未実装 |
| γ3c | 𝒮・Sp の引き戻し、fibration の塔、有限積への適用は未実装。Alg_E は E2a 後 |

Sp では raw sHom の局所 Kan 性と極限の cofibrancy を省略せず、必要なら cofibrant-fibrant
置換後の錐を公開する。実装は `InfinityCategories/HomotopyLimits/` と専用監査に置く。

γ3b の部分 API は `HomotopyLimits` 集約と `scripts/audit_homotopy_limits.lean` に置く。
公開52宣言。`representableHomotopyLimitComparison c x` は実際の sHom から end への射、
`representableHomotopyLimitComparison_factorization c x h` は θκ への厳密な分解、
`representableHomotopyLimitComparison_naturality c f` は始対象に関する厳密な自然性。
重み付き end の普遍性・通常の随伴と極限保存も公開。正確な型と数学は README に置く。
coherent な錐から end の点への対応と pinched Hom の fiber 比較が未完了なので、γ3b は未完了。
