module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.NormalizationProjectionInputs
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.SlicePrismTrianglePostcomp
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGPinchedCompositionClosedFamilyNaturality

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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded MonoidalCategory SSet
open scoped _root_.Simplicial

lemma dgGluingDGCompositionTriangleFamily_naturality
    (R : Type u) [CommRing R] (A B : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R A] [_root_.SerrePositivity.DifferentialGraded.DGCategory R B]
    (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R A B) {K : SSet.{max u v}} {x y z : A}
    (f : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R A x y) (g : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R A y z) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDGCompositionTriangleFamily R A f g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDGCompositionTriangleFamily R B
        (f ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (F.map x y))
        (g ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (F.map y z)) := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedCompositionFamilyPrism_naturality R A B F f g
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedCompositionTargetPoint_naturality R A B F z)
  rw [← Category.assoc] at h
  have ht := congrArg (fun V => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingSlicePrismTriangle V) h
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingSlicePrismTriangle_transport (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedCompositionTargetPoint_naturality R A B F z),
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingSlicePrismTriangle_postcomp] at ht
  exact ht

variable (R : Type u) [CommRing R] (E : Type (max u v)) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E]
  (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R E E (DGFunctor.id E))
  {K : SSet.{max u v}} (f : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R E E (DGFunctor.id E)) X Y)
local notation "Q" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R E E (DGFunctor.id E)
local notation "NX" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E X.replacement

lemma dgGluingPreNormalizeProjectionInput_naturality
    {Z : Type (max u v)} [_root_.SerrePositivity.DifferentialGraded.DGCategory R Z] (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R Q Z) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingPreNormalizeProjectionInput R E X Y f F := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedCompositionFamilyPrism_closed_first_naturality R Q Z F
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaNormalizationClosedIn R E X) f
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedCompositionTargetPoint_naturality R Q Z F Y)
  rw [← Category.assoc] at h
  have ht := congrArg (fun V => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingSlicePrismTriangle V) h
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingSlicePrismTriangle_transport (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedCompositionTargetPoint_naturality R Q Z F Y),
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingSlicePrismTriangle_postcomp] at ht
  exact ht

lemma dgGluingPostNormalizeProjectionInput_naturality
    {Z : Type (max u v)} [_root_.SerrePositivity.DifferentialGraded.DGCategory R Z] (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R Q Z) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingPostNormalizeProjectionInput R E X Y f F := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedCompositionFamilyPrism_closed_second_naturality R Q Z F
    (f ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (D := Q) (E := Q)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaPreNormalizeHom R E X Y))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaNormalizationClosedOut R E Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedCompositionTargetPoint_naturality R Q Z F
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E Y.source))
  rw [← Category.assoc] at h
  have ht := congrArg (fun V => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingSlicePrismTriangle V) h
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingSlicePrismTriangle_transport (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedCompositionTargetPoint_naturality R Q Z F
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E Y.source)),
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingSlicePrismTriangle_postcomp] at ht
  exact ht

lemma dgGluingExitProjectionInput_naturality
    {Z : Type (max u v)} [_root_.SerrePositivity.DifferentialGraded.DGCategory R Z] (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R Q Z) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingExitProjectionInput R E X Y f F := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedCompositionFamilyPrism_closed_second_naturality R Q Z F f
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaNormalizationClosedOut R E Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedCompositionTargetPoint_naturality R Q Z F
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E Y.source))
  rw [← Category.assoc] at h
  have ht := congrArg (fun V => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingSlicePrismTriangle V) h
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingSlicePrismTriangle_transport (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedCompositionTargetPoint_naturality R Q Z F
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E Y.source)),
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingSlicePrismTriangle_postcomp] at ht
  exact ht

lemma dgGluingNormalizationProjectionInput_naturality :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingNormalizationProjectionInput R E X Y f where
  preReplacement := dgGluingPreNormalizeProjectionInput_naturality R E X Y f _
  preSource := dgGluingPreNormalizeProjectionInput_naturality R E X Y f _
  postReplacement := dgGluingPostNormalizeProjectionInput_naturality R E X Y f _
  postSource := dgGluingPostNormalizeProjectionInput_naturality R E X Y f _
  exitReplacement := dgGluingExitProjectionInput_naturality R E X Y f _
  exitSource := dgGluingExitProjectionInput_naturality R E X Y f _

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
