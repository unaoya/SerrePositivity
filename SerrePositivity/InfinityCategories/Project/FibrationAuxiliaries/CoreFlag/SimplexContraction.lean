module


public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleInitialContraction

/-!
概要：任意次元の標準単体の初頂点への収縮。
方針：頂点の組 (i,t) を t=0 なら 0、それ以外なら i に送る。
規約：元の全単体上のホモトピーを構成する。
使われ方：Sp-8 の可逆な旗の行の評価の同値。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped _root_.Simplicial
namespace SerrePositivity.KST.LocalizingInvariants.CoreFlag
end SerrePositivity.KST.LocalizingInvariants.CoreFlag
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreFlag
open _root_.SerrePositivity.KST.LocalizingInvariants.CoreFlag
open InfinityCategories

/-- 初頂点から恒等写像へ変形する単調写像。 -/
def initialContractionOrder (m : ℕ) : Fin (m + 1) × Fin 2 →o Fin (m + 1) where
  toFun p := if p.2 = 0 then 0 else p.1
  monotone' := by
    intro p q hpq
    dsimp
    by_cases hp : p.2 = 0
    · simp only [hp, ite_true]
      exact Fin.zero_le _
    · have hq : q.2 ≠ 0 := by
        intro hq
        apply hp
        exact le_antisymm (hq ▸ hpq.2) (Fin.zero_le _)
      simpa only [hp, hq, ite_false] using hpq.1

/-- 標準単体の初頂点から恒等写像への指定された収縮。 -/
def initialContraction (m : ℕ) :
    SSet.Homotopy (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin (m + 1))) :
      (Δ[m] : SSet.{u}) ⟶ Δ[m]) (𝟙 _) where
  h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.stdSimplexProductMap (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreFlag.initialContractionOrder m)
  h₀ := by
    apply SSet.hom_ext
    rintro ⟨⟨n⟩⟩
    apply ConcreteCategory.hom_ext
    intro a
    apply stdSimplex.ext
    intro i
    rfl
  h₁ := by
    apply SSet.hom_ext
    rintro ⟨⟨n⟩⟩
    apply ConcreteCategory.hom_ext
    intro a
    apply stdSimplex.ext
    intro i
    rfl
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    exact False.elim s.1.property

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreFlag

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
