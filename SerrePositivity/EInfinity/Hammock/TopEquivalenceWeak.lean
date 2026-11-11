module

public import SerrePositivity.EInfinity.Hammock.RelativeNaturalWeakComparison
public import SerrePositivity.EInfinity.Hammock.RelativeFunctorLaws
public import SerrePositivity.EInfinity.Hammock.WeakTwoOfSix

/-!
# 全指定圏の元の圏同値による hammock の弱同値

概要：元の圏同値の関手が誘導する同じ hammock 写像は弱同値。
方針：元の unit と counit の相対自然変換の比較と二対六則を使う。
規約：元の全端点を保持し、圏同値を厳密同型とは仮定しない。
使われ方：自由な指定生成圏から元の指定部分圏への移送。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock
open CategoryTheory SerrePositivity.InfinityCategories

variable {C D : Type u} [Category.{v} C] [Category.{v} D]

def topRelative (F : C ⥤ D) :
    LocalizerMorphism (⊤ : MorphismProperty C) (⊤ : MorphismProperty D) :=
  ⟨F, fun _ _ _ _ => trivial⟩

lemma topRelative_composite_weak (F : C ⥤ D) (G : D ⥤ C)
    (η : F ⋙ G ⟶ 𝟭 C) (X Y : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (Relative.colimitMap ((topRelative F).comp (topRelative G)) X Y) := by
  have hid : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (Relative.colimitMap
      (LocalizerMorphism.id (⊤ : MorphismProperty C)) X Y) := by
    rw [Relative.colimitMap_id]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.isWeakHomotopyEquivalence_id _
  exact (RelativeNatural.weak_iff (F := (topRelative F).comp (topRelative G))
    (G := LocalizerMorphism.id _) η (fun _ => trivial) X Y).mpr hid

lemma topEquivalence_colimitMap_weak (e : C ≌ D) (X Y : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (Relative.colimitMap (topRelative e.functor) X Y) := by
  let F := topRelative e.functor
  let G := topRelative e.inverse
  have hfg : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (Relative.colimitMap F X Y ≫
      Relative.colimitMap G (e.functor.obj X) (e.functor.obj Y)) := by
    exact (Relative.colimitMap_comp F G X Y) ▸
      topRelative_composite_weak e.functor e.inverse e.unitIso.inv X Y
  have hgh : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence
      (Relative.colimitMap G (e.functor.obj X) (e.functor.obj Y) ≫
        Relative.colimitMap F (e.inverse.obj (e.functor.obj X))
          (e.inverse.obj (e.functor.obj Y))) := by
    exact (Relative.colimitMap_comp G F (e.functor.obj X) (e.functor.obj Y)) ▸
      topRelative_composite_weak e.inverse e.functor e.counitIso.hom _ _
  have hg := weak_middle_of_composites (Relative.colimitMap F X Y)
    (Relative.colimitMap G (e.functor.obj X) (e.functor.obj Y))
    (Relative.colimitMap F (e.inverse.obj (e.functor.obj X))
      (e.inverse.obj (e.functor.obj Y))) hfg hgh
  exact hg.cancel_right hfg

end SerrePositivity.EInfinity.Hammock
