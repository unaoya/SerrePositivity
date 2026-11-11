module

public import SerrePositivity.KST.Spectra.PointedParametricPostExchange
public import SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensorCotensor

/-!
概要：テンソルからの curry は、同じ標準 ihomAction による全族後合成と厳密に可換。
方針：族を転置した射への mapping と交換へ表示し、curry・cotensor の整合式を用いる。
規約：族を頂点ごとに照合しない。使われ方：二重 loop の標準族作用への厳密同定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.KST.Spectra.PointedMapping

/-- 同じ二重 curry は、標準の二つの ihomAction による全族後合成と射全体で可換。 -/
lemma parametricPost_tensor (A B : PointedSimplicialSet.{u})
    {P Z Z' : PointedSimplicialSet.{u}} (v : P ⟶ PointedObject.basedHom Z Z') :
    parametricPost (A ⊗ B) v ≫ PointedObject.basedHomMap P (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso A B Z').hom =
      (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso A B Z).hom ≫ parametricPost B (v ≫ ihomAction A Z Z') := by
  rw [parametricPost_exchange (A ⊗ B) v, parametricPost_exchange B (v ≫ ihomAction A Z Z')]
  change ((ihom (A ⊗ B)).map (transpose v) ≫ (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso (A ⊗ B) P Z').hom) ≫
      (ihom P).map (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso A B Z').hom =
    (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso A B Z).hom ≫ (ihom B).map (parametricPost A v) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso B P ((ihom A).obj Z')).hom
  rw [parametricPost_exchange A v]
  change ((ihom (A ⊗ B)).map (transpose v) ≫ (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso (A ⊗ B) P Z').hom) ≫
      (ihom P).map (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso A B Z').hom =
    (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso A B Z).hom ≫
      (ihom B).map ((ihom A).map (transpose v) ≫ (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso A P Z').hom) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso B P ((ihom A).obj Z')).hom
  have h₀ := congrArg (fun m => (ihom (A ⊗ B)).map (transpose v) ≫ m)
    (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.tensor_curry A B P Z')
  have h₁ := congrArg (fun m => m ≫ (ihom B).map (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso A P Z').hom ≫
    (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso B P ((ihom A).obj Z')).hom)
    (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.natural_post A B (transpose v))
  simp only [Category.assoc] at h₀ h₁
  simpa only [Category.assoc, CategoryTheory.Functor.map_comp] using h₀.trans h₁

end SerrePositivity.KST.Spectra.PointedMapping
