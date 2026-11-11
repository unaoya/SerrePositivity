module
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
/-!
概要：同じ底を保って引き戻しの二つの入力座標を同型で変更する。
方針：元の二脚へ同型の逆を前合成し、三成分が同型である pullback.map を用いる。
規約：底の条件と二つの全射影を厳密に保持する。
使われ方：正本 lax Hom の矢印座標と元左右入力を同時に輸送する。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits
variable {E F B E' F' : SSet.{u}} (f : E ⟶ B) (g : F ⟶ B) (i : E ≅ E') (j : F ≅ F')

def dgGluingPullbackReindexIso : pullback f g ≅ pullback (i.inv ≫ f) (j.inv ≫ g) :=
  asIso (pullback.map f g (i.inv ≫ f) (j.inv ≫ g) i.hom j.hom (𝟙 B)
    (by simp only [Category.comp_id, Iso.hom_inv_id_assoc])
    (by simp only [Category.comp_id, Iso.hom_inv_id_assoc]))

lemma dgGluingPullbackReindexIso_first :
    (dgGluingPullbackReindexIso f g i j).hom ≫ pullback.fst _ _ =
      pullback.fst f g ≫ i.hom :=
  pullback.lift_fst _ _ _

lemma dgGluingPullbackReindexIso_second :
    (dgGluingPullbackReindexIso f g i j).hom ≫ pullback.snd _ _ =
      pullback.snd f g ≫ j.hom :=
  pullback.lift_snd _ _ _
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
