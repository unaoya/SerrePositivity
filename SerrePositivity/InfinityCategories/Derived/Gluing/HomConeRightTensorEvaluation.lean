module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomConeRightTensor
public import SerrePositivity.InfinityCategories.Derived.Gluing.KernelHomEvaluation
public import SerrePositivity.InfinityCategories.Derived.Gluing.KernelConeEvaluation

/-! 右 Hom 円錐の tensor 作用を評価し、元の双加群作用で両包含を表示する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory CochainComplex HomComplex
open DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (X Y Z : DGGluingObject R C D M)
  (f : ForgetEnrichment.of (Complex R) Y ⟶ ForgetEnrichment.of (Complex R) Z)
local notation "rf" => CategoryTheory.Functor.map
  (SerrePositivity.DifferentialGraded.DGFunctor.onClosed (dgGluingRight R C D M)) f
local notation "yf" => CategoryTheory.Functor.map
  (SerrePositivity.DifferentialGraded.DGFunctor.onClosed (dgYoneda R D)) rf
local notation "K" => ForgetEnrichment.to (Complex R) (moduleCone R D yf)
local notation "F" => Morita.kernelTensor R D C M
local notation "r" => dgGluingHomConeRightArrow R C D M X Y Z f
local notation "A" => dgGluingHomConeRightTensorAction R C D M X Y Z f
local notation "E" => moduleEvaluation R C X.left
local notation "μ" => dgGluingRightAction R C D M X Y
local notation "ν" => dgGluingRightAction R C D M X Z

/-- 評価した右包含は、元の右作用と tensor の実閉包含で与えられる。 -/
lemma dgGluingHomConeRightTensorAction_inr_eval :
    mappingCone.inr r ≫ A ≫ (dgYonedaIso R X.left ((F).obj K)).hom =
    ν ≫ (E).map
      (dgGluingKernelColumnIso R C D M (ForgetEnrichment.of (Complex R) Z.right)).inv ≫
      (E).map ((F).onClosed.map (moduleConeInr R D yf)) := by
  rw [← Category.assoc, dgGluingHomConeRightTensorAction_inr]
  have hn := dgGluingYoneda_postcompose R C X.left
    ((F).onClosed.map (moduleConeInr R D yf))
  simp only [Category.assoc]
  erw [hn]
  have he := dgGluingKernelHomAction_evaluate R C D M X Z
  erw [← Category.assoc, ← Category.assoc, he, Category.assoc]

/-- 評価した左包含も、元の右作用と tensor の同じ次数 −1 の包含で与えられる。 -/
lemma dgGluingHomConeRightTensorAction_inl_eval :
    (mappingCone.inl r).comp
      (Cochain.ofHom (A ≫ (dgYonedaIso R X.left ((F).obj K)).hom)) (add_zero (-1)) =
    (Cochain.ofHom (μ ≫ (E).map
      (dgGluingKernelColumnIso R C D M (ForgetEnrichment.of (Complex R) Y.right)).inv)).comp
      (DGFunctor.moduleConeImageInl R D ((F).comp (moduleEvaluationDG R C X.left)) yf)
      (zero_add (-1)) := by
  have ht := dgGluingHomConeRightTensorAction_inl R C D M X Y Z f
  have hp := dgGluingYonedaPostAction R C ((F).obj (representable R Y.right)) ((F).obj K)
    (-1) X.left (dgModuleFunctorConeInl R D C F yf)
  have he := dgGluingKernelHomAction_evaluate R C D M X Y
  apply Cochain.ext
  intro q n hn
  have htq := Cochain.congr_v ht q n hn
  have hpq := Cochain.congr_v hp q n hn
  have heq := congrArg (fun a => a.f q) he
  simp only [Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v,
    Cochain.ofHom_v, HomologicalComplex.comp_f] at htq hpq heq ⊢
  erw [← Category.assoc, htq, Category.assoc, hpq, ← Category.assoc, heq]
  rfl

end SerrePositivity.InfinityCategories
