module

public import SerrePositivity.HomotopicalAlgebra.Diagram.BousfieldKanFrameAugmentationZero
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.BousfieldKanTerminalWeightNaturality

/-!
概要：既存の終対象によるBK重みの収縮を自然変換に束ねる。
方針：指定頂点と円柱の自然性を使い、両端を元の射と照合する。
使われ方：HTT 4.2.4.4、RR02(a)のframe実現の増大射の比較。
規約：単体集合のモデル構造は仮定しない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe w
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial
open SerrePositivity.InfinityCategories.Project.FilteredExchange
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
namespace SerrePositivity.DiagramModel.FrameWeightRealization
variable {K : Type w} [SmallCategory K] {t : K} (ht : IsTerminal t)

/-- 指定終対象への射の頂点で、零重みへの射を分裂する。 -/
def terminalZeroWeightSection :
    ConstantWeightHom.weight K (SimplexCategory.mk 0) ⟶ bousfieldKanWeight Kᵒᵖ where
  app k := SSet.const (nerveVertex (terminalWeightPoint ht k.unop))
  naturality i j f := by
    change 𝟙 _ ≫ _ = _ ≫ _
    rw [Category.id_comp, SSet.const_comp]
    congr 1
    change nerveVertex (terminalWeightPoint ht j.unop) =
      nerveVertex ((Over.map f).obj (terminalWeightPoint ht i.unop))
    exact congrArg nerveVertex (terminalWeightPoint_map ht f.unop).symm

lemma terminalZeroWeightSection_comp :
    terminalZeroWeightSection ht ≫ bousfieldKanZeroWeight K = 𝟙 _ := by
  apply NatTrans.ext
  funext k
  exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

/-- 既存の収縮の円柱を、重み全体の自然変換として束ねる。 -/
def terminalWeightCylinder :
    (weightedParameterFunctor (bousfieldKanWeight Kᵒᵖ)).obj (Δ[1] : SSet.{w}) ⟶
      bousfieldKanWeight Kᵒᵖ where
  app k := (terminalWeightHomotopy ht k.unop).h
  naturality i j f := terminalWeightHomotopy_naturality ht f.unop

/-- 同じ重みの円柱の指定端点。 -/
def terminalWeightEndpoint (ε : Fin 2) : bousfieldKanWeight Kᵒᵖ ⟶
    (weightedParameterFunctor (bousfieldKanWeight Kᵒᵖ)).obj (Δ[1] : SSet.{w}) where
  app k := if ε = 0 then SSet.ι₀ else SSet.ι₁
  naturality i j f := by
    by_cases h : ε = 0 <;> simp only [h, if_pos, if_neg] <;> rfl

lemma terminalWeightEndpoint_zero :
    terminalWeightEndpoint (K := K) 0 ≫ terminalWeightCylinder ht =
      bousfieldKanZeroWeight K ≫ terminalZeroWeightSection ht := by
  apply NatTrans.ext
  funext k
  change SSet.ι₀ ≫ (terminalWeightHomotopy ht k.unop).h = _
  rw [(terminalWeightHomotopy ht k.unop).h₀]
  simp [terminalZeroWeightSection, SSet.comp_const]

lemma terminalWeightEndpoint_one :
    terminalWeightEndpoint (K := K) 1 ≫ terminalWeightCylinder ht = 𝟙 _ := by
  apply NatTrans.ext
  funext k
  exact (terminalWeightHomotopy ht k.unop).h₁

end SerrePositivity.DiagramModel.FrameWeightRealization
