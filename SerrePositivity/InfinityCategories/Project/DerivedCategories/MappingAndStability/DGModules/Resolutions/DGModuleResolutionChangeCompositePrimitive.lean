module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Resolutions.DGModuleResolutionChangeCompositionMaps
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.ComplexTensorCochainSquare
/-!
概要：分解変更は、実合成を比較する二つの全 cochain を同じ終点後合成へ送る。
方針：左右 tensor の全次数四角形と、同じ二つの実合成作用の可換式を接続する。
規約：二つの比較項と全パラメータを保持する。使われ方：実 dg 合成の保存。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded MonoidalCategory CochainComplex HomComplex
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
  (E : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
  {F G : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C (_root_.SerrePositivity.DifferentialGraded.RightModule R E)}
  (a : ∀ x, ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (F.obj x) ⟶
    ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (G.obj x))
  (hs : ∀ x, _root_.SerrePositivity.DifferentialGraded.moduleDegreewiseSurjective R E (a x))
  (hq : ∀ x, _root_.SerrePositivity.DifferentialGraded.moduleQuasiIso R E (a x))
variable (ha : ∀ x y, F.map x y ≫
    eHomWhiskerLeft (_root_.SerrePositivity.DifferentialGraded.Complex R) (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (F.obj x)) (a y) =
  G.map x y ≫ eHomWhiskerRight (_root_.SerrePositivity.DifferentialGraded.Complex R) (a x)
    (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (G.obj y)))
variable (X Y Z : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R C E F)
/-- 実合成の第一比較 cochain は、同じ tensor 鎖写像と終点後合成で可換。 -/
lemma dgModuleResolutionChange_firstPrimitive :
    (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeHom R C E a hs hq ha X Y ⊗ₘ
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeHom R C E a hs hq ha Y Z)).comp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionFirstCompositePrimitive R C E G
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeObject R C E a hs hq X)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeObject R C E a hs hq Y)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeObject R C E a hs hq Z)) (zero_add (-1)) =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionFirstCompositePrimitive R C E F X Y Z).comp
      (Cochain.ofHom (_root_.SerrePositivity.DifferentialGraded.moduleHomPostcompose R E X.replacement.val
        (F.obj Z.source) (G.obj Z.source) (a Z.source))) (add_zero (-1)) := by
  let X' := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeObject R C E a hs hq X
  let Y' := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeObject R C E a hs hq Y
  let Z' := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeObject R C E a hs hq Z
  let f := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeHom R C E a hs hq ha X Y
  let g := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeHom R C E a hs hq ha Y Z
  let b := _root_.SerrePositivity.DifferentialGraded.moduleHomPostcompose R E X.replacement.val
    (F.obj Y.source) (G.obj Y.source) (a Y.source)
  let c := _root_.SerrePositivity.DifferentialGraded.moduleHomPostcompose R E X.replacement.val
    (F.obj Z.source) (G.obj Z.source) (a Z.source)
  have hp : (Cochain.ofHom f).comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionPrimitive R C E G X' Y')
      (zero_add (-1)) =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionPrimitive R C E F X Y).comp (Cochain.ofHom b) (add_zero (-1)) :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeHom_comparison R C E a hs hq ha X Y
  have ht := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.tensorRight_cochain_square (-1) f g b
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionPrimitive R C E F X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionPrimitive R C E G X' Y') hp
  have H := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cochain_postcompose_square (-1) (f ⊗ₘ g) (b ⊗ₘ g) c
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionFirstCompositionMap R C E F X Y Z)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionFirstCompositionMap R C E G X' Y' Z') _ _ ht
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChange_firstCompositionMap R C E a hs hq ha X Y Z)
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionFirstCompositePrimitive] using! H
/-- 実合成の第二比較 cochain も、同じ tensor 鎖写像と終点後合成で可換。 -/
lemma dgModuleResolutionChange_secondPrimitive :
    (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeHom R C E a hs hq ha X Y ⊗ₘ
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeHom R C E a hs hq ha Y Z)).comp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSecondCompositePrimitive R C E G
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeObject R C E a hs hq X)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeObject R C E a hs hq Y)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeObject R C E a hs hq Z)) (zero_add (-1)) =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSecondCompositePrimitive R C E F X Y Z).comp
      (Cochain.ofHom (_root_.SerrePositivity.DifferentialGraded.moduleHomPostcompose R E X.replacement.val
        (F.obj Z.source) (G.obj Z.source) (a Z.source))) (add_zero (-1)) := by
  let X' := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeObject R C E a hs hq X
  let Y' := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeObject R C E a hs hq Y
  let Z' := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeObject R C E a hs hq Z
  let f := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeHom R C E a hs hq ha X Y
  let g := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeHom R C E a hs hq ha Y Z
  let b := _root_.SerrePositivity.DifferentialGraded.moduleHomPostcompose R E Y.replacement.val
    (F.obj Z.source) (G.obj Z.source) (a Z.source)
  let c := _root_.SerrePositivity.DifferentialGraded.moduleHomPostcompose R E X.replacement.val
    (F.obj Z.source) (G.obj Z.source) (a Z.source)
  have hp : (Cochain.ofHom g).comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionPrimitive R C E G Y' Z')
      (zero_add (-1)) =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionPrimitive R C E F Y Z).comp (Cochain.ofHom b) (add_zero (-1)) :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeHom_comparison R C E a hs hq ha Y Z
  have ht := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.tensorLeft_cochain_square (-1) f g b
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionPrimitive R C E F Y Z)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionPrimitive R C E G Y' Z') hp
  have H := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cochain_postcompose_square (-1) (f ⊗ₘ g) (f ⊗ₘ b) c
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSecondCompositionMap R C E F X Y Z)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSecondCompositionMap R C E G X' Y' Z') _ _ ht
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChange_secondCompositionMap R C E a hs hq ha X Y Z)
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSecondCompositePrimitive] using! H
end SerrePositivity.InfinityCategories.Project.DerivedCategories
