module
public import SerrePositivity.InfinityCategories.Derived.DGModuleFunctorConeSquareModel
public import SerrePositivity.InfinityCategories.Derived.DGModuleSquareTopMiddleIso
public import SerrePositivity.InfinityCategories.Derived.DGModuleSquareVertices

/-! # cone の押し出し模型の零角を実関手像へ替える

概要：標準零加群の角を F(0) に替えた四角形データは元の標準四角形の実関手像と等しい。
方針：実零加群同型と、cone 同型の二包含の厳密一致を使う。
規約：四辺・対角・二つの Hom end 成分を全て照合。使われ方：標準 cofiber 保存。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
variable (F : DGFunctor A (RightModule A D) (RightModule A E))
variable {M N : ModuleCategory A D}

/-- 零角の実同型と零射は模型の上辺を因子分解する。 -/
lemma dgModuleFunctorConeSquareModel_zero_factorization (f : M ⟶ N) :
    (dgModuleFunctorZeroIso A D E F).hom ≫
      (0 : F.onClosed.obj (moduleZero A D) ⟶ F.onClosed.obj (moduleCone A D f)) =
        (dgModuleFunctorConeSquareModel A D E F f).top := by
  change _ = 0 ≫ _
  rw [comp_zero, zero_comp]

/-- 実関手像の零加群を左上の角とする模型。 -/
def dgModuleFunctorConeSquareZeroModel (f : M ⟶ N) :
    DGModuleSquareData A E (F.onClosed.obj M) (F.onClosed.obj N)
      (F.onClosed.obj (moduleZero A D)) (F.onClosed.obj (moduleCone A D f)) :=
  (dgModuleFunctorConeSquareModel A D E F f).changeTopMiddle
    (dgModuleFunctorZeroIso A D E F).hom 0
    (dgModuleFunctorConeSquareModel_zero_factorization A D E F f)

/-- 零角を替えた模型は全データにおいて元の実四角形の関手像と一致する。 -/
lemma dgModuleFunctorConeSquareZeroModel_eq_map (f : M ⟶ N) :
    dgModuleFunctorConeSquareZeroModel A D E F f = (dgModuleConeSquareData A D f).map F := by
  apply DGModuleSquareData.ext
  · rfl
  · change 0 ≫ _ = F.onClosed.map (0 : M ⟶ moduleZero A D)
    rw [zero_comp, Functor.map_zero]
  · exact dgModuleFunctorConeComparison_inr A D E F f
  · change 0 = F.onClosed.map (0 : moduleZero A D ⟶ moduleCone A D f)
    rw [Functor.map_zero]
  · change 0 ≫ _ = F.onClosed.map (0 : M ⟶ moduleCone A D f)
    rw [zero_comp, Functor.map_zero]
  · exact dgModuleFunctorConeComparison_inl A D E F f
  · change compose A _ 0 (add_zero (-1)) = (F.map _ _).f (-1) 0
    rw [compose_zero, map_zero]

/-- 零角を実関手像へ変更する四角形全体の関手同型。 -/
def dgModuleFunctorConeSquareZeroFunctorIso (f : M ⟶ N) :
    FunctorIso (dgModuleFunctorConeSquareModel A D E F f).square
      ((dgModuleConeSquareData A D f).map F).square := by
  have hs : IsZeroVertex
      (squareVertex (dgModuleFunctorConeSquareModel A D E F f).square 0 1) := by
    rw [DGModuleSquareData.square_vertex01]
    exact dgModuleNerveZeroVertex_isZero A E
  have ht : IsZeroVertex
      (squareVertex (dgModuleFunctorConeSquareZeroModel A D E F f).square 0 1) := by
    rw [DGModuleSquareData.square_vertex01]
    exact dgNerve_isZeroVertex_of_closed_isZero _ (dgModuleFunctor_zero_isZero A D E F)
  have h := (dgModuleFunctorConeSquareModel A D E F f).changeTopMiddleFunctorIso
    (dgModuleFunctorZeroIso A D E F).hom 0
    (dgModuleFunctorConeSquareModel_zero_factorization A D E F f) hs ht
  change FunctorIso _ (dgModuleFunctorConeSquareZeroModel A D E F f).square at h
  rw [dgModuleFunctorConeSquareZeroModel_eq_map] at h
  exact h

end SerrePositivity.InfinityCategories
