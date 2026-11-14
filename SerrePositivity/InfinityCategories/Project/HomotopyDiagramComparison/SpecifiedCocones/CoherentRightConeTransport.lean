module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.CoherentRightConeFunctor

/-!
# 元の coherent 錐の端点の正規化

概要：通常射の異種等式を同じ豊穣 Hom の点へ移し、定値な左因子を tensor と比較する。
方針：端点の等号による帰納と Cartesian な積の普遍性を使う。
規約：元の射と元の全 Hom を保持する。
使われ方：native roof の混合時刻の全合成条件。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
open CategoryTheory SSet MonoidalCategory CartesianMonoidalCategory

lemma lift_const_tensor {K T H G : SSet.{u}} (p : 𝟙_ SSet.{u} ⟶ H) (L : T ⟶ G) :
    lift (toUnit (K ⊗ T) ≫ p) (snd _ _ ≫ L) = (toUnit K ≫ p) ⊗ₘ L := by
  rw [← lift_fst_comp_snd_comp]
  simp only [← Category.assoc, comp_toUnit]

lemma unitHom_transport {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {A B A' B' : C} (hA : A = A') (hB : B = B') (f : A ⟶ B) (g : A' ⟶ B')
    (hf : HEq f g) :
    eHomEquiv SSet.{u} f ≫ eqToHom (congrArg₂ SimplicialCategory.sHom hA hB) =
      eHomEquiv SSet.{u} g := by
  cases hA
  cases hB
  have h : f = g := eq_of_heq hf
  subst g
  simp only [eqToHom_refl, Category.comp_id]

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
