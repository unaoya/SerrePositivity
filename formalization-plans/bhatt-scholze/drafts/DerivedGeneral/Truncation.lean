-- 将来の置き場所：InfinityCategories の Derived の上（調整役が判断。M12 と同じ扱い）。BS 固有ではない一般論。
-- 設計書：formalization-plans/bhatt-scholze/a2-design.md G-A2-2。基準コミット efa846fe8。型検査対象（5∞-0）。
module
public import SerrePositivity.HomologicalAlgebra.DerivedInfinity.VertexPredicates

-- 取り込み時の依存先：drafts/DerivedGeneral/CompletionFunctor.lean。
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.HomotopyModels.DiscreteEmbedding
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.NerveCone
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Loop
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Suspension
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.Homology
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.Stability
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomEvaluation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Triangles.StableLimits

/-!
# D(A) の標準 t 構造と Postnikov 切り捨て（∞ 関手として）

## 概要
導来 ∞ 圏 D(A) = N_dg(Semifree(A)) に標準 t 構造（D^{≤n}、D^{≥n}）を入れ、切り捨て τ^{≤n}・τ^{≥n} を ∞ 関手として与える。
cofiber 列 τ^{≤n−1}X → τ^{≤n}X → H^n(X)[−n]、H^i による検出、有界性。

## 方針
切り捨ては **dg 関手にはならない**（W9-I-28：X = A[0]、Y = A[−1] の間の次数 ±1 の可逆な射で、τ^{≤0} が Hom 複体の合成を保てない）。
∞ 関手としては、(a) 複体と擬同型の相対圏で smart truncation を作り、擬同型を保つことから ∞ 局所化 D(A) へ降ろす、または (b) D(A) の t 構造の
随伴（D^{≤n} ↪ D(A) の右随伴）として作る。t 構造の公理（HA 1.2.1.4）は複体の計算。H^i は基盤の `H i`（`HFunctor`）。

## 規約
cohomological な添字。**名前は原典（BS p.12）に合わせる**：connective ＝ H^{>0} = 0（D^{≤0}）、coconnective ＝ H^{<0} = 0（D^{≥0}）。
`IsConnectiveAt n` := H^i = 0（i > n）、`IsCoconnectiveAt n` := H^i = 0（i < n）（W9-I-28 で入れ替え。以前は逆だった）。
BS の HT filtration では τ^{≤i} Δ̄ を使う。

## 使われ方
A2-3（HT filtration ＝ τ^{≤i} Δ̄_P の Kan 延長、gr^i = H^i[−i]）、A4（Lemma 8.4 の coconnectivity）、A5（Prop 8.5 の連結性の議論）、
導来 Nakayama（G-A1-4）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial Function

namespace SerrePositivity.InfinityCategories.Derived

attribute [local instance] HasDerivedCategory.standard

variable (A : Type u) [CommRing A]

/-! 連結性・p完備性の述語と旧名の略記は、本体の
`HomologicalAlgebra/DerivedInfinity/VertexPredicates` を使う。 -/

/-- 概要：coconnective at n：D^{≥n}、H^i = 0（i < n）な対象（原典の coconnective。Lemma 8.4 は `IsCoconnectiveAt 0`）。 -/
def IsCoconnectiveAt (n : ℤ) (x : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A) _⦋0⦌) : Prop :=
  ∀ i : ℤ, i < n → Subsingleton (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomology A i x)

/-- 概要：切り捨て τ^{≤n} : D(A) → D(A)（∞ 関手）。
方針：相対圏からの ∞ 局所化、または t 構造の随伴（§方針、W9-I-28。dg 関手にはしない）。
規約：τ^{≤n}X → X が H^i（i ≤ n）で同型、τ^{≤n}X ∈ D^{≤n}。
使われ方：HT filtration。 -/
def truncationLE (n : ℤ) : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A ⟶ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A := by
  sorry -- M13：smart truncation を擬同型で局所化して得る ∞ 関手

def truncationGE (n : ℤ) : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A ⟶ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A := by
  sorry -- M13：smart truncation を擬同型で局所化して得る ∞ 関手

/-- 概要：τ^{≤n}X → X の自然変換と、その H^i（i ≤ n）での同型。 -/
def truncationLE_counit (n : ℤ) : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (truncationLE A n) (𝟙 _) := by
  sorry -- D^{≤n} への右随伴の余単位

/-- h Fun の射の成分を表す辺。代表の選択はホモトピー類を変えない。 -/
def componentEdge {F G : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A ⟶ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A}
    (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom F G) (x : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A) _⦋0⦌) :
    SSet.Truncated.Edge (X := (SSet.truncation 2).obj (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A))
      (F.app _ x) (G.app _ x) :=
  Classical.choose (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective _ _ (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate α x))

theorem truncationLE_counit_h (n : ℤ) (x : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A) _⦋0⦌)
    (i : ℤ) (hi : i ≤ n) :
    IsIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomologyMap A i (componentEdge A (truncationLE_counit A n) x)) := by
  sorry -- smart truncation の余単位は i ≤ n のコホモロジーに同型を誘導する

def truncationLE_step (n : ℤ) : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (truncationLE A n) (truncationLE A (n+1)) := by
  sorry -- τ^{≤n}X → X を τ^{≤n+1}X への射に随伴で持ち上げる

theorem truncationLE_step_counit (n : ℤ) :
    truncationLE_step A n ≫ truncationLE_counit A (n+1) = truncationLE_counit A n := by
  sorry -- 随伴による持ち上げを余単位と合成すると元の射に戻る

/-- 概要：τ^{≤n}X ∈ D^{≤n}、すなわち `IsConnectiveAt n`（H^i = 0 for i > n）。W9-III-11 で述語の向きを訂正（以前は `IsCoconnectiveAt` で逆：
非零 A、X = A[1]、n = 0 なら τ^{≤0}X = X は H^{−1} ≠ 0 で coconnective でない）。 -/
theorem truncationLE_isConnective (n : ℤ) (x : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A) _⦋0⦌) :
    IsConnectiveAt A n ((truncationLE A n).app _ x) := by
  sorry -- smart truncation の n より上のコホモロジーは零

/-- 加群を次数零に入れる。D5-02：既存の離散代数の埋め込みの、加群から先の部分。 -/
def discreteModuleEmbedding : nerve (ModuleCat.{u} A) ⟶ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A :=
  nerveMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleSemifreeResolutionFunctor A) ≫ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.closedNerveInclusion A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree A)

/-- Hⁿ(X)[−n]。loop と suspension は hD(A) 上の関手なので、対象に反復して頂点を読む。 -/
def cohomologyLayer (n : ℤ) (x : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A) _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A) _⦋0⦌ := by
  let y : hoFunctor.obj (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A) := HomotopyCategory.mk
    ((discreteModuleEmbedding A).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomology A n x)))
  exact match n with
    | .ofNat m => (SSet.HomotopyCategory.objEquiv (((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopFunctor (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A)).obj^[m]) y))
    | .negSucc m => (SSet.HomotopyCategory.objEquiv (((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionFunctor (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A)).obj^[m+1]) y))

/-- τ^{≤n−1}X → τ^{≤n}X の指定された射の cofiber が Hⁿ(X)[−n]。 -/
theorem truncation_cofiber (n : ℤ) (x : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A) _⦋0⦌) :
    ∃ c : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.CofiberSquare (componentEdge A (show _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (truncationLE A (n-1)) (truncationLE A n) from
        by simpa only [sub_add_cancel] using truncationLE_step A (n-1)) x),
      Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso c.cofiber (cohomologyLayer A n x)) := by
  sorry -- smart truncation の隣接する段の商は Hⁿ(X) を次数 n に置いた複体

/-- t 構造の直交性。ここでの Hom は写像空間の π₀。 -/
theorem tStructure_orthogonal (n : ℤ) (x y : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A) _⦋0⦌)
    (hx : IsConnectiveAt A n x) (hy : IsCoconnectiveAt A (n+1) y) :
    Subsingleton ((HomotopyCategory.mk x : hoFunctor.obj (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A)) ⟶
      HomotopyCategory.mk y) := by
  sorry -- D^{≤n} から D^{≥n+1} への導来圏の射は零

/-- D5-01：Σ = [1] なので Hⁱ(ΣX) = Hⁱ⁺¹(X)。 -/
theorem tStructure_shift (n : ℤ) (x : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A) _⦋0⦌) :
    IsConnectiveAt A n x ↔ IsConnectiveAt A (n-1)
      ((SSet.HomotopyCategory.objEquiv ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionFunctor (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A)).obj (HomotopyCategory.mk x)))) := by
  sorry -- derivedSuspensionShiftObjectIso とコホモロジーのシフト公式

/-- τ^{≤n}X → X → τ^{≥n+1}X は cofiber 列でも fiber 列でもある。 -/
theorem tStructure_decomposition (n : ℤ) (x : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A) _⦋0⦌) :
    ∃ c : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.CofiberSquare (componentEdge A (truncationLE_counit A n) x),
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare c.square ∧ Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso c.cofiber ((truncationGE A (n+1)).app _ x)) ∧
        IsCoconnectiveAt A (n+1) ((truncationGE A (n+1)).app _ x) := by
  sorry -- 余単位の cofiber は上側の smart truncation。安定性で同じ四角形が pullback

/-- 概要：有界な対象では Postnikov 塔は有限で exhaustive（X ∈ D^{[a,b]} ⇒ τ^{≤b}X ≃ X）。
方針：H^i の検出。
規約：—
使われ方：HT filtration が多項式代数で有限段で止まること。 -/
theorem truncationLE_of_isConnective (n : ℤ) (x : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A) _⦋0⦌)
    (hx : IsConnectiveAt A n x) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (componentEdge A (truncationLE_counit A n) x) := by
  sorry -- 余単位が全次数のコホモロジーで同型なので D(A) で可逆

/-- 概要：導来 Nakayama の形：導来 (p,d) 完備な X で X ⊗^L A/(p,d) = 0 ⇒ X = 0（G-A1-4）。
方針：完備化の塔と H^i の検出。
規約：完備性は `IsModuleComplete` の D(A) 版（DerivedGeneral/CompletionFunctor）。
使われ方：Thm 5.2 の η、Construction 6.1 (1)、Cor 4.12、D32。 -/
theorem derived_nakayama (s : Finset A) {r : ℕ} (a : Fin r → A)
    (ha : Set.range a = (s : Set A)) (x : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A) _⦋0⦌)
    (hx : IsDerivedComplete A s x)
    (hKos : ∀ i : ℤ, Limits.IsZero ((koszulComplexOn a
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategoryVertexEquiv A x).val).homology i)) :
    ∀ i : ℤ, Subsingleton (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomology A i x) := by
  sorry -- Kos(a;X) の消滅を各冪の Koszul 複体へ dévissage し、完備な X を塔の極限で回収

end SerrePositivity.InfinityCategories.Derived
