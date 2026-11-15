module

public import SerrePositivity.HomotopicalAlgebra.Diagram.BousfieldKanTerminalWeightDiagram

/-!
概要：終対象による重み収縮の像を、円柱射影を反転する関手で照合する。
方針：両端の射影との合成を同定し、指定切断を逆射として用いる。
使われ方：HTT 4.2.4.4、RR02(a)のframe実現後の弱同値判定。
規約：ここでは任意の通常の関手に関する収縮の法則だけを述べる。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe w u v
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
namespace SerrePositivity.DiagramModel.FrameWeightRealization
variable {K : Type w} [SmallCategory K] {t : K}

/-- 指定された重みの円柱の第一射影。 -/
def terminalWeightProjection :
    (weightedParameterFunctor (bousfieldKanWeight Kᵒᵖ)).obj (Δ[1] : SSet.{w}) ⟶
      bousfieldKanWeight Kᵒᵖ :=
  fst _ _

lemma terminalWeightEndpoint_projection (ε : Fin 2) :
    terminalWeightEndpoint (K := K) ε ≫ terminalWeightProjection = 𝟙 _ := by
  apply NatTrans.ext
  funext k
  change (if ε = 0 then SSet.ι₀ else SSet.ι₁) ≫ fst _ _ = 𝟙 _
  by_cases h : ε = 0 <;> simp [h]

variable {D : Type u} [Category.{v} D] (F : (Kᵒᵖ ⥤ SSet.{w}) ⥤ D)
  [IsIso (F.map (terminalWeightProjection (K := K)))]

/-- 射影を反転する関手では、同じ円柱の両端は等しい。 -/
lemma terminalWeightEndpoint_map_eq :
    F.map (terminalWeightEndpoint (K := K) 0) =
      F.map (terminalWeightEndpoint (K := K) 1) := by
  apply (cancel_mono (F.map (terminalWeightProjection (K := K)))).mp
  simp only [← F.map_comp, terminalWeightEndpoint_projection]

/-- 指定切断は、射影を反転した後には零重みへの指定射の逆となる。 -/
def terminalZeroWeightMapIso (ht : IsTerminal t) :
    F.obj (bousfieldKanWeight Kᵒᵖ) ≅
      F.obj (ConstantWeightHom.weight K (SimplexCategory.mk 0)) where
  hom := F.map (bousfieldKanZeroWeight K)
  inv := F.map (terminalZeroWeightSection ht)
  hom_inv_id := by
    rw [← F.map_comp, ← terminalWeightEndpoint_zero ht, F.map_comp,
      terminalWeightEndpoint_map_eq F, ← F.map_comp, terminalWeightEndpoint_one ht,
      F.map_id]
  inv_hom_id := by
    rw [← F.map_comp, terminalZeroWeightSection_comp ht, F.map_id]

lemma terminalZeroWeightMapIso_hom (ht : IsTerminal t) :
    (terminalZeroWeightMapIso F ht).hom = F.map (bousfieldKanZeroWeight K) := rfl

end SerrePositivity.DiagramModel.FrameWeightRealization
