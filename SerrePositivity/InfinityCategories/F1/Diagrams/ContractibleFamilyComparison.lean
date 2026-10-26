module

public import SerrePositivity.InfinityCategories.Core.TrivialFibrationEquivalence

/-!
概要：可縮 Kan 複体への任意の二つの全族は、全パラメーターで可逆比較できる。
方針：終対象への内部 Hom の同じ fiber に両族を戻し、その可縮性を使う。
規約：頂点ごとの同型の族ではなく、実際の FunctorIso を供給する。
使われ方：Ind-S の読出し・再構成の合成に対する全族比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 任意のパラメーター全体で、可縮 Kan 複体への二つの族を比較する。 -/
def contractibleKanFamilyComparison {A L : SSet.{u}} (hcL : IsContractibleKan L)
    (f g : A ⟶ L) : FunctorIso f g := by
  let p := terminal.from L
  letI : TrivialKanFibration p := (isContractibleKan_iff_trivialKanFibration L).mp hcL
  let q := (ihom A).map p
  let b := functorVertex (terminal.from A)
  let v (h : A ⟶ L) : (vertexFiber q b) _⦋0⦌ := ⟨functorVertex h, by
    rw [pinchedConstant_zero]
    change functorVertex (h ≫ p) = functorVertex (terminal.from A)
    exact congrArg functorVertex (terminal.hom_ext _ _)⟩
  have hc := vertexFiber_isContractibleKan q b
  letI := hc.kanComplex
  exact VertexIso.map (terminalVertexIso (hc.isTerminalVertex (v f))
    (hc.isTerminalVertex (v g))) (vertexFiberι q b)

end SerrePositivity.InfinityCategories
