module
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.GrothendieckWeightedNerveInverseData

/-!
概要：元のweighted係数から回収した同じ対象と射を、Grothendieckの全射列にする。
方針：元の係数の全自然性でfiber射の合成を合わせ、Grothendieckの合成則を使う。
規約：IS-W2 R03eの逆向きの単体の関手性。元の基底とfiber射を保つ。
使われ方：同じ厳密な比較同型の逆射。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open CategoryTheory
variable {I : Type u} [SmallCategory I] (F : I ⥤ Cat.{u,u})
  {n : ℕ} (s : weightedNerveSimplex (F ⋙ nerveFunctor) n)

/-- 元の同じfiber射から回収したGrothendieck射は恒等射を保つ。 -/
theorem grothWeightedNerveInverseMap_id (i : Fin (n+1)) :
    grothWeightedNerveInverseMap F s (𝟙 i) = 𝟙 (grothWeightedNerveInverseObj F s i) := by
  apply Grothendieck.ext _ _ (s.1.map_id i)
  simp only [Grothendieck.id_fiber, grothWeightedNerveInverseMap, homOfLE_refl,
    CategoryTheory.Functor.map_id, Category.comp_id, eqToHom_trans]

/-- 元の同じfiber射から回収したGrothendieck射は合成を保つ。 -/
theorem grothWeightedNerveInverseMap_comp {i j k : Fin (n+1)} (f : i ⟶ j) (g : j ⟶ k) :
    grothWeightedNerveInverseMap F s (f ≫ g) =
      grothWeightedNerveInverseMap F s f ≫ grothWeightedNerveInverseMap F s g := by
  apply Grothendieck.ext _ _ (s.1.map_comp f g)
  have hc := CategoryTheory.Functor.congr_hom (grothWeightedNerveFiberChain_naturality F s g).symm
    (homOfLE (show grothWeightedNerveInverseIndex f ≤ Fin.last j.val from
      Nat.le_of_lt_succ (grothWeightedNerveInverseIndex f).isLt))
  dsimp only [Functor.comp_map] at hc
  simp only [Grothendieck.comp_fiber, grothWeightedNerveInverseMap,
    Functor.map_comp, eqToHom_map, Category.assoc]
  rw [hc]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
    ← CategoryTheory.Functor.map_comp]
  congr 2

/-- 元のweighted係数から同じGrothendieck射列を回収する。 -/
def grothWeightedNerveInverseSimplex : ComposableArrows (Grothendieck F) n where
  obj := grothWeightedNerveInverseObj F s
  map := grothWeightedNerveInverseMap F s
  map_id := grothWeightedNerveInverseMap_id F s
  map_comp := grothWeightedNerveInverseMap_comp F s

/-- 逆向きの単体は元の同じ底の射列を厳密に回収する。 -/
theorem grothWeightedNerveInverseSimplex_base :
    grothWeightedNerveInverseSimplex F s ⋙ Grothendieck.forget F = s.1 := rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
