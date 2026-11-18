module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.NerveConeInitialComparison
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConeUniverseNaturality
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanDiagramCoherentNerve

/-!
概要：小さい通常錐の coherent 表示は、同じ錐を Kan 値関手で送る操作と一致する。
方針：始対象の標準錐と AsSmall の全射の比較を使う。
規約：HTT 4.2.4.1 の指定錐の構成の法則。頂点だけの比較ではない。
使われ方：S8 の離散層条件の元の制限錐の照合。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
variable {I C : Type u} [SmallCategory I] [SmallCategory C] {F : I ⥤ C}

/-- 拡大した指定錐の関手と係数関手の合成は、係数で送った錐の関手。 -/
lemma strictConeFunctor_mapCone (c : Cone F) (G : C ⥤ KanObject.{u}) :
    coneWithInitialFunctor (asSmallCone c) ⋙ AsSmall.down ⋙ G =
      strictConeFunctor (G.mapCone c) := by
  refine CategoryTheory.Functor.ext (by intro i; cases i <;> rfl) ?_
  intro i j f
  cases i <;> cases j <;>
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  · rfl
  · exact (f : PEmpty).elim
  · rfl
  · change G.map (𝟙 c.pt) = 𝟙 (G.obj c.pt)
    exact G.map_id c.pt

/-- 同じ通常錐を係数で送る coherent 表示は、元の nerve 錐の持ち上げへの後合成。 -/
lemma strictCoherentConeMap_mapCone (c : Cone F) (G : C ⥤ KanObject.{u}) :
    strictCoherentConeMap (G.mapCone c) =
      (nerveCone c).ulift.val ≫ kanDiagramCoherentNerve G := by
  let H : AsSmall.{u + 1} C ⥤ KanObject.{u} := AsSmall.down ⋙ G
  have hh : nerveMap (coneWithInitialFunctor (asSmallCone c)) ≫ resizedNerveMap H =
      resizedNerveMap (strictConeFunctor (G.mapCone c)) := by
    rw [resizedNerveMap_precomp, strictConeFunctor_mapCone]
  have hi := uliftNerveCone_asSmall_val c
  calc
    _ = (joinMap (𝟙 Δ[0]) (nerveAsSmallIso.{u, u + 1} I).hom ≫
        (nerveCone (asSmallCone c)).val) ≫ resizedNerveMap H ≫ nerveToCoherent _ := by
      rw [nerveCone_val_initial]
      simp only [Category.assoc]
      rw [← Category.assoc (nerveMap (coneWithInitialFunctor (asSmallCone c))), hh]
      rw [strictCoherentConeMap]
      simp only [← Category.assoc]
      rw [← joinMap_comp, Category.id_comp]
    _ = ((nerveCone c).ulift.val ≫ (nerveAsSmallIso.{u, u + 1} C).hom) ≫
        resizedNerveMap H ≫ nerveToCoherent _ := by rw [hi]
    _ = _ := by
      simp only [Category.assoc]
      rfl

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
