module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.HomComplexes.Models.HomConeRightTensor
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.Kernels.KernelHomEvaluation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.StableStructure.KernelConeEvaluation

/-! 右 Hom 円錐の tensor 作用を評価し、元の双加群作用で両包含を表示する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory CochainComplex HomComplex
open DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (X Y Z : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
  (f : ForgetEnrichment.of (Complex R) Y ⟶ ForgetEnrichment.of (Complex R) Z)
local notation "rf" => CategoryTheory.Functor.map
  (SerrePositivity.DifferentialGraded.DGFunctor.onClosed (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRight R C D M)) f
local notation "yf" => CategoryTheory.Functor.map
  (SerrePositivity.DifferentialGraded.DGFunctor.onClosed (dgYoneda R D)) rf
local notation "K" => ForgetEnrichment.to (Complex R) (moduleCone R D yf)
local notation "F" => Morita.kernelTensor R D C M
local notation "r" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeRightArrow R C D M X Y Z f
local notation "A" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeRightTensorAction R C D M X Y Z f
local notation "E" => moduleEvaluation R C X.left
local notation "μ" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightAction R C D M X Y
local notation "ν" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightAction R C D M X Z

/-- 評価した右包含は、元の右作用と tensor の実閉包含で与えられる。 -/
lemma dgGluingHomConeRightTensorAction_inr_eval :
    mappingCone.inr r ≫ A ≫ (dgYonedaIso R X.left ((F).obj K)).hom =
    ν ≫ (E).map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelColumnIso R C D M (ForgetEnrichment.of (Complex R) Z.right)).inv ≫
      (E).map ((F).onClosed.map (moduleConeInr R D yf)) := by
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeRightTensorAction_inr]
  have hn := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingYoneda_postcompose R C X.left
    ((F).onClosed.map (moduleConeInr R D yf))
  simp only [Category.assoc]
  erw [hn]
  have he := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelHomAction_evaluate R C D M X Z
  erw [← Category.assoc, ← Category.assoc, he, Category.assoc]

/-- 評価した左包含も、元の右作用と tensor の同じ次数 −1 の包含で与えられる。 -/
lemma dgGluingHomConeRightTensorAction_inl_eval :
    (mappingCone.inl r).comp
      (Cochain.ofHom (A ≫ (dgYonedaIso R X.left ((F).obj K)).hom)) (add_zero (-1)) =
    (Cochain.ofHom (μ ≫ (E).map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelColumnIso R C D M (ForgetEnrichment.of (Complex R) Y.right)).inv)).comp
      (DGFunctor.moduleConeImageInl R D ((F).comp (moduleEvaluationDG R C X.left)) yf)
      (zero_add (-1)) := by
  have ht := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeRightTensorAction_inl R C D M X Y Z f
  have hp := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingYonedaPostAction R C ((F).obj (representable R Y.right)) ((F).obj K)
    (-1) X.left (dgModuleFunctorConeInl R D C F yf)
  have he := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelHomAction_evaluate R C D M X Y
  apply Cochain.ext
  intro q n hn
  have htq := Cochain.congr_v ht q n hn
  have hpq := Cochain.congr_v hp q n hn
  have heq := congrArg (fun a => a.f q) he
  simp only [Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v,
    Cochain.ofHom_v, HomologicalComplex.comp_f] at htq hpq heq ⊢
  erw [← Category.assoc, htq, Category.assoc, hpq, ← Category.assoc, heq]
  rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
