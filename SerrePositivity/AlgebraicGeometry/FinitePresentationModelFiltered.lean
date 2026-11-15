module

public import SerrePositivity.AlgebraicGeometry.FinitePresentationModelCocones
public import SerrePositivity.AlgebraicGeometry.FinitePresentationModelCoequalizer
public import Mathlib.CategoryTheory.Filtered.Basic

/-!
概要：有限表示代数の模型の圏は filtered。
方針：二対象にはテンソル積、平行射には有限個の生成元の差を消す商を使う。
規約：同じ宇宙の小さい模型へも filtered 性を移す。元の代数の有限型性は要求しない。
使われ方：整拡大の有限表示模型による近似。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u
variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]

set_option backward.isDefEq.respectTransparency false in
/-- 元の環 B 上で可換な模型の平行射は、ある先の模型で等しくなる。 -/
theorem finitePresentationModelCategory_cocone_maps {X Y : FinitePresentationModelCategory R B}
    (f g : X ⟶ Y) : ∃ (Z : FinitePresentationModelCategory R B) (h : Y ⟶ Z), f ≫ h = g ≫ h := by
  let φ := f.hom.left.hom.hom
  let ψ := g.hom.left.hom.hom
  have hf : Y.obj.hom.hom.comp φ = X.obj.hom.hom :=
    congrArg CommAlgCat.Hom.hom f.hom.w
  have hg : Y.obj.hom.hom.comp ψ = X.obj.hom.hom :=
    congrArg CommAlgCat.Hom.hom g.hom.w
  obtain ⟨Q, _, _, hQfp, q, hq, k, hk, heq⟩ :=
    exists_finitePresentation_coequalizing_quotient φ ψ Y.obj.hom.hom (hf.trans hg.symm)
  let Z := finitePresentationModelObj k
  let h : Y ⟶ Z := finitePresentationModelHomMk q hk
  refine ⟨Z, h, ?_⟩
  apply InducedCategory.hom_ext
  apply CostructuredArrow.hom_ext
  apply InducedCategory.hom_ext
  apply CommAlgCat.hom_ext
  exact heq

instance : IsFiltered (FinitePresentationModelCategory R B) where
  cocone_objs := finitePresentationModelCategory_cocone_objs
  cocone_maps _ _ f g := finitePresentationModelCategory_cocone_maps f g

instance : IsFiltered (FinitePresentationModelIndex R B) :=
  IsFiltered.of_equivalence (equivSmallModel (FinitePresentationModelCategory R B))

end SerrePositivity.AlgebraicGeometry
