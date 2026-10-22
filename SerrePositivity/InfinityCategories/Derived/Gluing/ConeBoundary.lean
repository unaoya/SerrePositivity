module
public import SerrePositivity.InfinityCategories.Derived.Gluing.KernelConeNullhomotopy
public import SerrePositivity.InfinityCategories.Derived.Gluing.ConeRightModuleMap
public import SerrePositivity.DifferentialGraded.Functor.HomIso

/-! 標準円錐の零ホモトピーを native gluing と全 dg 自然な Yoneda 加群へ移す。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits CochainComplex HomComplex DifferentialGraded MonoidalCategory

/-- 閉零圏の零射を単位からの Hom 鎖写像として読むと、同じ零鎖写像。 -/
lemma dgGluingClosedHomTo_zero {R : Type u} [CommRing R] {E : Type v} [DGCategory R E]
    (x y : ClosedCategory R E) :
    ForgetEnrichment.homTo (Complex R) (0 : x ⟶ y) =
      (0 : 𝟙_ (Complex R) ⟶ homObject R E x y) := rfl

variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (Y Z : DGGluingObject R C D M)
  (f : ForgetEnrichment.of (Complex R) Y ⟶ ForgetEnrichment.of (Complex R) Z)
local notation "F" => Morita.kernelTensor R D C M
local notation "E" => DGFunctorCommaObject R (RightModule R D) (RightModule R C)
  (Morita.kernelTensor R D C M)
local notation "KY" => dgGluingKernelObject R C D M Y
local notation "L" => dgGluingKernelConeObject R C D M Y Z f
local notation "ki" => dgGluingKernelConeInr R C D M Y Z f
local notation "kf" => CategoryTheory.Functor.map
  (DGFunctor.onClosed (dgGluingToKernelComma R C D M)) f

/-- 標準 kernel 円錐の包含との合成は、同じ Hom 円錐の左包含による境界。 -/
lemma dgGluingKernelConeInr_boundary : boundaryRelation R E (kf ≫ ki) 0 := by
  apply (unit_homotopy_iff (homObject R E KY L)
    (ForgetEnrichment.homTo (Complex R) (kf ≫ ki))
    (ForgetEnrichment.homTo (Complex R) 0)).2
  refine ⟨dgGluingKernelConeNullCochain R C D M Y Z f, ?_⟩
  rw [dgGluingClosedHomTo_zero, Cochain.ofHom_zero,
    dgGluingKernelConeNullCochain_boundary, add_zero]

variable
  (p : DGGluingConeRepresentative R C Y.left Z.left (dgGluingConeLeftArrow R C D M Y Z f))
  (q : DGGluingConeRepresentative R D Y.right Z.right
    ((dgYoneda R D).onClosed.map (dgGluingConeRightArrow R C D M Y Z f)))
local notation "W" => dgGluingConeObjectFromRepresentatives R C D M Y Z f p q
local notation "i" => dgGluingConeInr R C D M Y Z f p q
local notation "a" => dgGluingKernelConeRepresentativeMap R C D M Y Z f p q

/-- native gluing の元の射と選んだ円錐包含の合成も、全 Hom の同じ境界で零。 -/
lemma dgGluingConeInr_boundary : boundaryRelation R (DGGluingObject R C D M) (f ≫ i) 0 := by
  apply ((dgGluingToKernelComma R C D M).boundary_iff_of_homIso
    (fun x y => by rw [dgGluingToKernelComma_map]; infer_instance) (f ≫ i) 0).1
  rw [CategoryTheory.Functor.map_comp, dgGluingConeInr_kernel,
    CategoryTheory.Functor.map_zero]
  apply (toHomotopy_map_eq_iff R E _ _).1
  rw [← Category.assoc, CategoryTheory.Functor.map_comp,
    (toHomotopy_map_eq_iff R E _ _).2 (dgGluingKernelConeInr_boundary R C D M Y Z f)]
  simp only [CategoryTheory.Functor.map_zero, zero_comp]

/-- Yoneda 加群の同じ二射の合成は、全 dg 自然な加群ホモトピーで零。 -/
lemma dgGluingConeInrModuleMap_boundary :
    Nonempty (ModuleHomotopy R (DGGluingObject R C D M)
      ((dgYoneda R (DGGluingObject R C D M)).onClosed.map f ≫
        dgGluingConeInrModuleMap R C D M Y Z f p q) 0) := by
  apply (moduleHomotopy_nonempty_iff R (DGGluingObject R C D M) _ _).2
  have he := (dgYoneda R (DGGluingObject R C D M)).preserves_boundary
    (f ≫ i) 0 (dgGluingConeInr_boundary R C D M Y Z f p q)
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_zero] at he
  exact he

end SerrePositivity.InfinityCategories
