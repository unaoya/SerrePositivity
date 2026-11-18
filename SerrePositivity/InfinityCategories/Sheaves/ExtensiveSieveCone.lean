module

public import SerrePositivity.InfinityCategories.Sheaves.ExtensiveSieveIndex
public import SerrePositivity.InfinityCategories.Sheaves.ExtensiveCofanDuality
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConeNaturality

/-!
概要：生成篩の指定全錐を脚と初対象の添字へ制限し、元の fan の脚を回収する。
方針：通常の指定篩錐を whisker し、nerve の両境界と混合辺で制限を照合する。
規約：HTT 6.2.2.6 の extensive 位相の係数・添字移送の法則。
使われ方：S1 の有限積保存の元の指定錐への接続。頂点の同値だけに置き換えない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C] {ι : Type u} {B : ι → C}

/-- 元の篩錐を、脚と初対象を含む同じ添字へ制限した通常の全錐。 -/
abbrev cofanSieveIndexCone [HasInitial C] [Nonempty ι] (c : Cofan B) :=
  (sieveCone (cofanGeneratedSieve c)).whisker (cofanSieveIndex c)

/-- 脚だけへの制限では、係数図式は元の同じ反対の族。 -/
lemma cofanSieveIndex_legs [HasInitial C] [Nonempty ι] (c : Cofan B) :
    WithTerminal.incl ⋙ cofanSieveIndex c ⋙ sieveDiagram (cofanGeneratedSieve c) =
      Discrete.functor (fun i => Opposite.op (B i)) := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  rintro ⟨i⟩ ⟨j⟩ f
  obtain rfl := Discrete.eq_of_hom f
  have hf : f = 𝟙 (Discrete.mk i) := Subsingleton.elim _ _
  subst f
  simp only [CategoryTheory.Functor.map_id, eqToHom_refl, Category.id_comp, Category.comp_id]

/-- 全篩錐を同じ二段の添字で制限すると、元の指定 fan の全射を回収する。 -/
lemma cofanSieveIndexCone_legs_val [HasInitial C] [Nonempty ι] (c : Cofan B) :
    (nerveCone ((cofanSieveIndexCone c).whisker WithTerminal.incl)).val =
      (nerveCone (cofanToOppositeFan c)).val := by
  apply nerve_joinPoint_hom_ext
  · rw [nerveCone_point, nerveCone_point]
    rfl
  · rw [(nerveCone ((cofanSieveIndexCone c).whisker WithTerminal.incl)).property,
      (nerveCone (cofanToOppositeFan c)).property]
    exact congrArg nerveMap (cofanSieveIndex_legs c)
  · intro i
    rw [nerveCone_leg, nerveCone_leg]
    rfl

end SerrePositivity.InfinityCategories.Sheaves
