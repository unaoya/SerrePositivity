module
public import SerrePositivity.InfinityCategories.Derived.Gluing.NormalizationProjectionInputs
public import SerrePositivity.InfinityCategories.Derived.Gluing.SlicePrismTrianglePostcomp
public import SerrePositivity.InfinityCategories.Derived.DGPinchedCompositionClosedFamilyNaturality

/-! # coherent 標準合成面の六つの射影自然性

概要：正規化の前後・終側の全標準面について、二射影の自然性を実例化する。
方針：D の Small 不要の coherent prism 自然性を、同じ三角形表示へ移す。
規約：Direct 版へ面を変更せず、固定標的の等式輸送も保持する。
使われ方：相対貼り合わせの六つの補助入力を、無仮定の実データで置き換える。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded MonoidalCategory DGNerve SSet
open scoped Simplicial

lemma dgGluingDGCompositionTriangleFamily_naturality
    (R : Type u) [CommRing R] (A B : Type v) [DGCategory R A] [DGCategory R B]
    (F : DGFunctor R A B) {K : SSet.{max u v}} {x y z : A}
    (f : K ⟶ DGNerve.pinchedHom R A x y) (g : K ⟶ DGNerve.pinchedHom R A y z) :
    dgGluingDGCompositionTriangleFamily R A f g ≫ dgNerve.map F =
      dgGluingDGCompositionTriangleFamily R B
        (f ≫ pinchedHomChainMap (F.map x y))
        (g ≫ pinchedHomChainMap (F.map y z)) := by
  have h := dgPinchedCompositionFamilyPrism_naturality R A B F f g
    (dgPinchedCompositionTargetPoint_naturality R A B F z)
  rw [← Category.assoc] at h
  have ht := congrArg (fun V => dgGluingSlicePrismTriangle V) h
  rw [dgGluingSlicePrismTriangle_transport (dgPinchedCompositionTargetPoint_naturality R A B F z),
    dgGluingSlicePrismTriangle_postcomp] at ht
  exact ht

variable (R : Type u) [CommRing R] (E : Type (max u v)) [DGCategory R E]
  (X Y : DGFunctorCommaObject R E E (DGFunctor.id E))
  {K : SSet.{max u v}} (f : K ⟶ DGNerve.pinchedHom R
    (DGFunctorCommaObject R E E (DGFunctor.id E)) X Y)
local notation "Q" => DGFunctorCommaObject R E E (DGFunctor.id E)
local notation "NX" => dgGluingIdentityCommaObject R E X.replacement

lemma dgGluingPreNormalizeProjectionInput_naturality
    {Z : Type (max u v)} [DGCategory R Z] (F : DGFunctor R Q Z) :
    DGGluingPreNormalizeProjectionInput R E X Y f F := by
  have h := dgPinchedCompositionFamilyPrism_closed_first_naturality R Q Z F
    (dgGluingIdentityCommaNormalizationClosedIn R E X) f
    (dgPinchedCompositionTargetPoint_naturality R Q Z F Y)
  rw [← Category.assoc] at h
  have ht := congrArg (fun V => dgGluingSlicePrismTriangle V) h
  rw [dgGluingSlicePrismTriangle_transport (dgPinchedCompositionTargetPoint_naturality R Q Z F Y),
    dgGluingSlicePrismTriangle_postcomp] at ht
  exact ht

lemma dgGluingPostNormalizeProjectionInput_naturality
    {Z : Type (max u v)} [DGCategory R Z] (F : DGFunctor R Q Z) :
    DGGluingPostNormalizeProjectionInput R E X Y f F := by
  have h := dgPinchedCompositionFamilyPrism_closed_second_naturality R Q Z F
    (f ≫ pinchedHomChainMap (D := Q) (E := Q)
      (dgGluingIdentityCommaPreNormalizeHom R E X Y))
    (dgGluingIdentityCommaNormalizationClosedOut R E Y)
    (dgPinchedCompositionTargetPoint_naturality R Q Z F
      (dgGluingIdentityCommaObject R E Y.source))
  rw [← Category.assoc] at h
  have ht := congrArg (fun V => dgGluingSlicePrismTriangle V) h
  rw [dgGluingSlicePrismTriangle_transport (dgPinchedCompositionTargetPoint_naturality R Q Z F
      (dgGluingIdentityCommaObject R E Y.source)),
    dgGluingSlicePrismTriangle_postcomp] at ht
  exact ht

lemma dgGluingExitProjectionInput_naturality
    {Z : Type (max u v)} [DGCategory R Z] (F : DGFunctor R Q Z) :
    DGGluingExitProjectionInput R E X Y f F := by
  have h := dgPinchedCompositionFamilyPrism_closed_second_naturality R Q Z F f
    (dgGluingIdentityCommaNormalizationClosedOut R E Y)
    (dgPinchedCompositionTargetPoint_naturality R Q Z F
      (dgGluingIdentityCommaObject R E Y.source))
  rw [← Category.assoc] at h
  have ht := congrArg (fun V => dgGluingSlicePrismTriangle V) h
  rw [dgGluingSlicePrismTriangle_transport (dgPinchedCompositionTargetPoint_naturality R Q Z F
      (dgGluingIdentityCommaObject R E Y.source)),
    dgGluingSlicePrismTriangle_postcomp] at ht
  exact ht

lemma dgGluingNormalizationProjectionInput_naturality :
    DGGluingNormalizationProjectionInput R E X Y f where
  preReplacement := dgGluingPreNormalizeProjectionInput_naturality R E X Y f _
  preSource := dgGluingPreNormalizeProjectionInput_naturality R E X Y f _
  postReplacement := dgGluingPostNormalizeProjectionInput_naturality R E X Y f _
  postSource := dgGluingPostNormalizeProjectionInput_naturality R E X Y f _
  exitReplacement := dgGluingExitProjectionInput_naturality R E X Y f _
  exitSource := dgGluingExitProjectionInput_naturality R E X Y f _

end SerrePositivity.InfinityCategories
