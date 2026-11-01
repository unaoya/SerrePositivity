module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.GeneratorPartition

/-!
# 元の自由圏の二つの生成部分の普遍性

概要：指定生成矢と非指定生成矢からの関手は一意に元の Paths C へ拡張する。
方針：両部分の制限の等式を元の各生成矢に戻し、自由圏の関手の外延性を使う。
規約：対象表示の移送を含む元の関手の等式で普遍性を述べる。
使われ方：Dwyer–Kan 比較補題2.3で使う、同じ対象上の自由積分解。
-/

@[expose] public section
universe u v u' v'
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.SimplicialLocalization.GeneratorPartition
open CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)
  {D : Type u'} [Category.{v'} D]

lemma jointly_ext {F G : Paths C ⥤ D}
    (hm : MarkedGenerators.inclusion W ⋙ F = MarkedGenerators.inclusion W ⋙ G)
    (hu : MarkedGenerators.inclusion (unmarked W) ⋙ F =
      MarkedGenerators.inclusion (unmarked W) ⋙ G) : F = G := by
  classical
  have ho : F.obj = G.obj := funext (fun X => Functor.congr_obj hm X)
  apply Paths.ext_functor (F := F) (G := G) ho
  intro X Y f
  apply eq_of_heq
  simp only [heq_eqToHom_comp_iff, heq_comp_eqToHom_iff]
  by_cases hf : W f
  · exact CategoryTheory.Functor.hcongr_hom hm
      (Quiver.Hom.toPath (show @Quiver.Hom (MarkedGenerators.quiver W) _ X Y from ⟨f, hf⟩))
  · exact CategoryTheory.Functor.hcongr_hom hu
      (Quiver.Hom.toPath (show @Quiver.Hom (MarkedGenerators.quiver (unmarked W)) _ X Y from
        ⟨f, hf⟩))

lemma extend_unique (F : Paths (MarkedGenerators.quiver W) ⥤ D)
    (G : Paths (MarkedGenerators.quiver (unmarked W)) ⥤ D)
    (h : ∀ X : C, F.obj X = G.obj X) (H : Paths C ⥤ D)
    (hm : MarkedGenerators.inclusion W ⋙ H = F)
    (hu : MarkedGenerators.inclusion (unmarked W) ⋙ H = G) :
    H = extendFunctor W F G h :=
  jointly_ext W (hm.trans (marked_fac W F G h).symm)
    (hu.trans (unmarked_fac W F G h).symm)

lemma existsUnique_extension (F : Paths (MarkedGenerators.quiver W) ⥤ D)
    (G : Paths (MarkedGenerators.quiver (unmarked W)) ⥤ D)
    (h : ∀ X : C, F.obj X = G.obj X) :
    ∃! H : Paths C ⥤ D, MarkedGenerators.inclusion W ⋙ H = F ∧
      MarkedGenerators.inclusion (unmarked W) ⋙ H = G := by
  refine ⟨extendFunctor W F G h, ⟨marked_fac W F G h, unmarked_fac W F G h⟩, ?_⟩
  intro H hH
  exact extend_unique W F G h H hH.1 hH.2

end SerrePositivity.EInfinity.SimplicialLocalization.GeneratorPartition
