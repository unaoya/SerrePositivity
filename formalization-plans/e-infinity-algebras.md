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

γ1.5a の設計・符号・原典との照合は `InfinityCategories/README.md` に置く。
比較の向きは `N^hc(C_Δ) → N_dg(C)`。小さい線形 Hom の Kan 性、次数の符号、
閉零射と零単体の同値、標準 chain map 方程式の単体的加群との自然同型、
切断 Hom 複体への Mathlib Γ の適用とその正規化、標準模型の正規化の各項の
具体的な核の共通部分との同定まで実装済み。`standardNormalizationIso x y` は
標準模型の実際の Moore 正規化と `connectiveHomComplex x y` の複体の同型。
`standardDoldKanModuleIso x y : standardModule x y ≅ doldKanHomModule x y`、
`homModuleDoldKanIso x y : homModule x y ≅ doldKanHomModule x y` は単体的加群の自然同型。
`doldKanHomSpaceKan x y : SSet.KanComplex (doldKanHomSpace x y)` は N4 の線形充填から従う。
`awDataBilinear x y z n` は AW 成分族の R 双線形演算。
`awData_unit_left`・`awData_unit_right` は dg 単位の定数単体による両側単位則、
`standardUnitMap x : 𝟙_ SSet.{u} ⟶ standardHomSpace x x` は単体的単位写像。
`awData_assoc h g f : awData h (awData g f) = awData (awData h g) f` は成分族上の結合律。
`awData_pullback α g f` は任意の単調写像 α による引き戻しとの可換性で、退化も含む。
`awData_mem_standard g f` は標準方程式の保存を証明する。
`standardAW (g : StandardSimplex R y z n) (f : StandardSimplex R x y n) :
StandardSimplex R x z n` が追加仮定なしの合成。
γ1.5b は完了。`doldKanSimplicialCategory : SimplicialCategory (ClosedCategory R D)`、
`doldKanSimplicialCategory_locallyKan x y : SSet.KanComplex (SimplicialCategory.sHom x y)`、
`doldKanCoherentNerve : SSet.{max u v}` とその quasicategory instance を構成した。
`doldKanSimplicialHomIso` は豊穣 Hom と実際の Mathlib Γ の Hom の自然同型。
通常の圏の恒等射と合成との整合性も証明済み。前提は `[CommRing R] [DGCategory R D]`。
γ1.5c では `cubeEvaluation e φ : GradedHom R x y (-(m : ℤ))` と native Path の
`coherentCubeComponent` を構成し、`cubeFlag_internal_sum_eq_zero` で内部面の相殺を証明した。
`cubeFlag_boundary_sum` は最大旗の全境界を座標1面−座標0面の交代和にする。
`cubeEvaluation_succ_d` は `e : Fin (n+1) ≃ T` と
`φ : Coherent.cube T ⟶ standardHomSpace x y` に対し、
`d (−↑(n+1)) (−↑n) (cubeEvaluation e φ)` が各座標面の評価の差の交代和に等しいと示す。
`cubeEvaluation_zero_closed e φ : differential R (cubeEvaluation e φ) = 0`。
前提は同じく `[CommRing R] [DGCategory R D]`。
`cubeEvaluation_pathFace_zero` は座標0面を一点削除した内部点集合の評価へ移す。
`erasedEnumeration_eq_descending` は降順の向きの保存、`strictAnti_enumeration_card_filter` は係数の点数を与える。
`pathCubeMap_face_one` は座標1面の Path の左右分解、`coherentCube_face_one_apply` は
その豊穣 Hom での像が `standardAW 後半 前半` に等しいことを示す。
前提には `[LinearOrder J]` と実際の豊穣関手 s を用いる。
`standardComponent_nerve_zero_of_not_injOn` は選んだ頂点集合で頂点が重複する成分の消滅、
`cubeEvaluation_restriction_zero` は座標を忘れた正次元の立方体評価の消滅。
`standardTopEval_AW_restriction_zero_of_inversion` は `r<s`、`¬P(e r)`、`P(e s)` の旗を消去し、
`standardTopEval_AW_restriction_eq_term` は `P(e r) ↔ r.val<c.val` の旗の AW を切断点 c の一項にする。
前提は同じ dg 圏と座標立方体からの実際の標準 Hom 写像。残る一項の評価と符号付き和の積への分解は残る。
公開303宣言の正確な型・前提・公理監査は `scripts/audit_dold_kan_comparison.lean`。残りは
比較写像、低次の一致、写像空間の比較。A3e の `qCatEquivalenceOfFullyFaithfulEssentiallySurjective` は実装済み。
比較写像と各 pinched Hom の実際のホモトピー同値を完成させた後に適用する。
