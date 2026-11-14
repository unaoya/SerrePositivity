module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.FreeProductFrames
public import Mathlib.CategoryTheory.Functor.Currying

/-!
概要：積パラメータの frame を、積添字上の同じ自由鎖図式へ戻す。
方針：各対象で恒等の同型を使い、射の式を自由鎖の関手性で照合する。
規約：AW・shuffle のホモトピーを同じ成分で運ぶための A02 内部の比較。
使われ方：HA 1.2.4、全余単体・全図式添字の同時比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory MonoidalCategory
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A] {J : Type v} [Category.{w} J]
variable (W : J ⥤ SSet.{u}) (P : SimplexCategory ⥤ (J ⥤ SSet.{u}))

/-- 積添字上の重みは、元の重みを第二添字で評価する。 -/
def frameWeightDiagram : SimplexCategory × J ⥤ SSet.{u} := CategoryTheory.Prod.snd _ _ ⋙ W

/-- 積 frame を uncurry した図式と、元の自由積図式の同じ成分による同型。 -/
def freeProductFrameUncurryIso :
    Functor.uncurry.obj (freeProductFrame A W P) ≅
      freeNegativeChainsDiagram (A := A)
        (frameWeightDiagram W ⊗ Functor.uncurry.obj P) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro x y f
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    change freeNegativeChainsMap (A := A) ((𝟙 (W.obj x.2)) ⊗ₘ ((P.map f.1).app x.2)) ≫
      freeNegativeChainsMap (A := A) ((W.map f.2) ⊗ₘ ((P.obj y.1).map f.2)) =
      freeNegativeChainsMap (A := A)
        ((W.map f.2) ⊗ₘ ((P.map f.1).app x.2 ≫ (P.obj y.1).map f.2))
    simp only [freeNegativeChainsMap, ← HomologicalComplex.extendMap_comp,
      ← CategoryTheory.Functor.map_comp, ← Functor.whiskerRight_comp,
      tensorHom_comp_tensorHom, Category.id_comp])

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
