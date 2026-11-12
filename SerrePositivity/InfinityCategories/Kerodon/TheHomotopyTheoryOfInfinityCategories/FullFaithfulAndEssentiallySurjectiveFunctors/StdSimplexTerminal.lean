module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithfulBaseChange

/-!
概要：標準単体の最後の頂点の終対象性。
方針：標準単体の pinched 単体は端点で一意であり、最後の頂点への辺が存在する。
規約：標準単体の全次元を扱う。
使われ方：Kerodon Proposition 4.8.4.5（Tag 05AR） の標準単体上の境界充填。

対応節は Kerodon 4.8（Tag 0578）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors

/-- 概要：各次数が高々一点で零単体が存在する単体集合は可縮な Kan 複体。
方針：任意の境界を選んだ頂点への定値射で充填する。
規約：周囲の quasicategory 性を仮定しない。
使われ方：Kerodon §4.8.4（Tag 06SQ） の標準単体の写像空間。 -/
lemma isContractibleKan_of_nonempty_of_degreewise_subsingleton (K : SSet.{u})
    (hne : Nonempty (K _⦋0⦌)) (hs : ∀ n : ℕ, Subsingleton (K _⦋n⦌)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan K := by
  obtain ⟨x⟩ := hne
  intro n b
  refine ⟨SSet.const x, ?_⟩
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro a
  exact (hs d).elim _ _

/-- 概要：標準単体の任意の二頂点間の pinched 写像空間の各次数は高々一点。
方針：元の順序写像の前面と最後の頂点を固定端点で比較する。
規約：辺が存在しない二頂点も許す。
使われ方：Kerodon §4.8.4（Tag 06SQ） の標準単体の離散的な写像空間。 -/
instance pinchedHom_stdSimplex_subsingleton {n : ℕ} (a b : (Δ[n] : SSet.{u}) _⦋0⦌)
    (m : ℕ) : Subsingleton ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom a b) _⦋m⦌) where
  allEq x y := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.Simplex.ext
    apply stdSimplex.ext
    intro i
    induction i using Fin.lastCases with
    | last =>
      exact (congrArg (fun z : (Δ[n] : SSet.{u}) _⦋0⦌ ↦ z 0) x.target).trans
        (congrArg (fun z : (Δ[n] : SSet.{u}) _⦋0⦌ ↦ z 0) y.target).symm
    | cast i =>
      exact (congrArg (fun z : (Δ[n] : SSet.{u}) _⦋m⦌ ↦ z i) x.source).trans
        (congrArg (fun z : (Δ[n] : SSet.{u}) _⦋m⦌ ↦ z i) y.source).symm

/-- 概要：標準単体の任意の頂点から最後の頂点への写像空間は非空。
方針：二頂点を結ぶ標準辺を零単体として取る。
規約：最後の頂点は Fin.last n。
使われ方：Kerodon §4.8.4（Tag 06SQ） の標準単体の終対象。 -/
lemma pinchedHom_stdSimplex_last_nonempty {n : ℕ} (a : (Δ[n] : SSet.{u}) _⦋0⦌) :
    Nonempty ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom a (stdSimplex.obj₀Equiv.symm (Fin.last n))) _⦋0⦌) := by
  refine ⟨⟨stdSimplex.edge.{u} n (stdSimplex.obj₀Equiv a) (Fin.last n) (Fin.le_last _), ?_, ?_⟩⟩
  · apply stdSimplex.ext
    intro i
    fin_cases i
    rfl
  · apply stdSimplex.ext
    intro i
    fin_cases i
    rfl

/-- 概要：標準単体の最後の頂点は終対象。
方針：全ての頂点からの pinched 写像空間は各次数高々一点で非空なので可縮。
規約：全次元の標準単体を扱う。
使われ方：Kerodon Proposition 4.8.4.5（Tag 05AR） の標準単体上の境界の充填。 -/
lemma stdSimplex_last_isTerminalVertex (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (X := (Δ[n] : SSet.{u})) (stdSimplex.obj₀Equiv.symm (Fin.last n)) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.isTerminalVertex_of_pinchedHom_isContractibleKan
  intro a
  exact isContractibleKan_of_nonempty_of_degreewise_subsingleton _
    (pinchedHom_stdSimplex_last_nonempty a) (fun m ↦ inferInstance)

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors
