module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.CochainModels.Cochains.UnitCochainElement

/-! 単位からの指定 cochain と次数 −1 の射影の合成の零性を、その同じ値へ移す。 -/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex DifferentialGraded
variable {R : Type u} [CommRing R] {K L : Complex R}

/-- 合成 cochain が零なら、単位の 1 の像の同じ射影も零。 -/
lemma dgGluingUnitCochainElement_comp_zero
    (h : Cochain (𝟙_ (Complex R)) K (-1)) (k : Cochain K L (-1))
    (hh : h.comp k (by omega : -1 + -1 = -2) = 0) :
    k.v (-1) (-2) (by omega) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitCochainElement K h) = 0 := by
  have he := Cochain.congr_v hh 0 (-2) (by omega)
  rw [Cochain.comp_v _ _ (by omega : -1 + -1 = -2) 0 (-1) (-2) rfl (by omega),
    Cochain.zero_v] at he
  exact congrArg (fun a => a
    ((singleObjXSelf (ComplexShape.up ℤ) 0 (𝟙_ (ModuleCat R))).inv 1)) he

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
