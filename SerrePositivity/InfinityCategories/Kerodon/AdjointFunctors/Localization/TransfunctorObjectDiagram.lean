module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Transfunctor

/-!
# transfunctor の固定した対象での元の図式

概要：全作用素で対象表示を保つ元の底の図式を固定し、係数の値の図式を得る。
方針：元の表示等式から Grothendieck 圏への切断を構成し、その後に係数関手を合成する。
規約：元の作用素・対象表示・係数自然変換を保持する。
使われ方：DK10.4の各固定対象での弱同値の入力。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory
variable {I : Type v} [Category I] (B : I ⥤ Cat.{u, u})
  (p : (i : I) → B.obj i)
  (hp : ∀ {i j : I} (θ : i ⟶ j), (B.map θ).toFunctor.obj (p i) = p j)

def objectSection : I ⥤ Grothendieck B where
  obj i := ⟨i, p i⟩
  map θ := ⟨θ, eqToHom (hp θ)⟩
  map_id i := by
    refine Grothendieck.ext _ _ rfl ?_
    simp only [Grothendieck.id_fiber, eqToHom_trans]
  map_comp θ φ := by
    refine Grothendieck.ext _ _ rfl ?_
    simp only [Grothendieck.comp_fiber, eqToHom_map, eqToHom_trans]

variable (T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Transfunctor.Covariant B)

def objectDiagram : I ⥤ Cat.{u, u} := objectSection B p hp ⋙ T

def objectDiagramMap {T' : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Transfunctor.Covariant B} (τ : T ⟶ T') :
    objectDiagram B p hp T ⟶ objectDiagram B p hp T' :=
  Functor.whiskerLeft (objectSection B p hp) τ

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
