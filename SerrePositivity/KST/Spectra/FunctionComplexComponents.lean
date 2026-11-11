module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FunctionComplexPointedSimplex
public import SerrePositivity.KST.Spectra.PointedMappingComponents
public import SerrePositivity.KST.Spectra.FunctionComplexPost

/-!
概要：Kan 複体の関数複体の連結成分を座標ごとの連結成分で表示する。
方針：Kan 充填で各座標の成分の等式を単一の辺へ戻し、その辺を束ねる。
規約：添字集合の有限性は不要。Kan 性は単射性の証明に使う。
使われ方：Goerss–Jardine I §7、VIII §1。骨格の fiber の零次数の係数表示。
-/

@[expose] public section

universe u
open CategoryTheory SSet
open scoped Simplicial

namespace SerrePositivity.KST.Spectra.SimplicialFunctionComplex

noncomputable section

/-- 概要：関数複体の成分を各座標の成分へ送る。
方針：評価の誘導する π₀ の写像を並べる。
規約：この写像自体には Kan 性は不要。
使われ方：Goerss–Jardine I §7。係数表示の順写像。 -/
def componentMap (S : Type u) (X : SSet.{u}) : π₀ (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialFunctionComplex.obj S X) → (S → π₀ X) :=
  fun a s ↦ mapπ₀ (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialFunctionComplex.eval S X s) a

@[simp]
lemma componentMap_mk (S : Type u) (X : SSet.{u}) (v : S → X _⦋0⦌) :
    componentMap S X (π₀.mk v) = fun s ↦ π₀.mk (v s) := rfl

/-- 概要：Kan 複体の関数複体の成分表示は全単射。
方針：座標ごとの成分の等式から辺を選び、関数値の一単体を構成する。
規約：空集合と無限集合の添字も含む。
使われ方：Goerss–Jardine I §7、VIII §1。無限個のセルの成分の同時比較。 -/
theorem componentMap_bijective (S : Type u) (X : SSet.{u}) [KanComplex X] :
    Function.Bijective (componentMap S X) := by
  constructor
  · intro a b h
    obtain ⟨v, rfl⟩ := π₀.mk_surjective a
    obtain ⟨w, rfl⟩ := π₀.mk_surjective b
    have he (s : S) : Nonempty (X.Edge (v s) (w s)) :=
      nonempty_edge_of_piZero_eq (congrFun h s)
    let e (s : S) := Classical.choice (he s)
    exact π₀.sound (Edge.mk (X := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialFunctionComplex.obj S X) (fun s ↦ (e s).edge)
      (funext fun s ↦ (e s).src_eq) (funext fun s ↦ (e s).tgt_eq))
  · intro a
    choose v hv using fun s ↦ π₀.mk_surjective (a s)
    exact ⟨π₀.mk v, funext hv⟩

/-- 概要：関数複体の π₀ と成分の関数の標準同値。
方針：評価写像の全単射性を使う。
規約：Kan 充填と選択公理による集合の同値。
使われ方：Goerss–Jardine VIII §1。骨格の fiber の係数への接続。 -/
def componentEquiv (S : Type u) (X : SSet.{u}) [KanComplex X] :
    π₀ (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialFunctionComplex.obj S X) ≃ (S → π₀ X) :=
  Equiv.ofBijective _ (componentMap_bijective S X)

@[simp]
lemma componentEquiv_mk (S : Type u) (X : SSet.{u}) [KanComplex X]
    (v : S → X _⦋0⦌) :
    componentEquiv S X (π₀.mk v) = fun s ↦ π₀.mk (v s) := rfl

/-- 概要：成分の座標表示は係数の後合成と可換。
方針：各座標の評価と後合成の可換性を π₀ へ送る。
規約：Kan 性を仮定せずに写像として述べる。
使われ方：Goerss–Jardine VIII §1。成分係数の自然性。 -/
theorem componentMap_natural (S : Type u) {X Y : SSet.{u}} (f : X ⟶ Y)
    (a : π₀ (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialFunctionComplex.obj S X)) :
    componentMap S Y (mapπ₀ (post S f) a) = fun s ↦ mapπ₀ f (componentMap S X a s) := by
  funext s
  change mapπ₀ (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialFunctionComplex.eval S Y s) (mapπ₀ (post S f) a) =
    mapπ₀ f (mapπ₀ (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialFunctionComplex.eval S X s) a)
  rw [← mapπ₀_comp_apply, post_eval, mapπ₀_comp_apply]

end

end SerrePositivity.KST.Spectra.SimplicialFunctionComplex
