module
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolutionChangeCompositionMaps
public import SerrePositivity.InfinityCategories.Derived.ComplexTensorCochainSquare
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve MonoidalCategory CochainComplex HomComplex
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] [Small.{u} E]
  {F G : DGFunctor R C (RightModule R E)}
  (a : ∀ x, ForgetEnrichment.of (Complex R) (F.obj x) ⟶
    ForgetEnrichment.of (Complex R) (G.obj x))
  (hs : ∀ x, moduleDegreewiseSurjective R E (a x))
  (hq : ∀ x, moduleQuasiIso R E (a x))
variable (ha : ∀ x y, F.map x y ≫
    eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) (F.obj x)) (a y) =
  G.map x y ≫ eHomWhiskerRight (Complex R) (a x)
    (ForgetEnrichment.of (Complex R) (G.obj y)))
variable (X Y Z : DGModuleFunctorResolutionObject R C E F)
/-- 実合成の第一比較 cochain は、同じ tensor 鎖写像と終点後合成で可換。 -/
lemma dgModuleResolutionChange_firstPrimitive :
    (Cochain.ofHom (dgModuleResolutionChangeHom R C E a hs hq ha X Y ⊗ₘ
      dgModuleResolutionChangeHom R C E a hs hq ha Y Z)).comp
      (dgModuleFunctorResolutionFirstCompositePrimitive R C E G
        (dgModuleResolutionChangeObject R C E a hs hq X)
        (dgModuleResolutionChangeObject R C E a hs hq Y)
        (dgModuleResolutionChangeObject R C E a hs hq Z)) (zero_add (-1)) =
    (dgModuleFunctorResolutionFirstCompositePrimitive R C E F X Y Z).comp
      (Cochain.ofHom (moduleHomPostcompose R E X.replacement.val
        (F.obj Z.source) (G.obj Z.source) (a Z.source))) (add_zero (-1)) := by
  let X' := dgModuleResolutionChangeObject R C E a hs hq X
  let Y' := dgModuleResolutionChangeObject R C E a hs hq Y
  let Z' := dgModuleResolutionChangeObject R C E a hs hq Z
  let f := dgModuleResolutionChangeHom R C E a hs hq ha X Y
  let g := dgModuleResolutionChangeHom R C E a hs hq ha Y Z
  let b := moduleHomPostcompose R E X.replacement.val
    (F.obj Y.source) (G.obj Y.source) (a Y.source)
  let c := moduleHomPostcompose R E X.replacement.val
    (F.obj Z.source) (G.obj Z.source) (a Z.source)
  have hp : (Cochain.ofHom f).comp (dgModuleFunctorResolutionPrimitive R C E G X' Y')
      (zero_add (-1)) =
    (dgModuleFunctorResolutionPrimitive R C E F X Y).comp (Cochain.ofHom b) (add_zero (-1)) :=
    dgModuleResolutionChangeHom_comparison R C E a hs hq ha X Y
  have ht := tensorRight_cochain_square (-1) f g b
    (dgModuleFunctorResolutionPrimitive R C E F X Y)
    (dgModuleFunctorResolutionPrimitive R C E G X' Y') hp
  have H := cochain_postcompose_square (-1) (f ⊗ₘ g) (b ⊗ₘ g) c
    (dgModuleFunctorResolutionFirstCompositionMap R C E F X Y Z)
    (dgModuleFunctorResolutionFirstCompositionMap R C E G X' Y' Z') _ _ ht
    (dgModuleResolutionChange_firstCompositionMap R C E a hs hq ha X Y Z)
  simpa only [dgModuleFunctorResolutionFirstCompositePrimitive] using! H
/-- 実合成の第二比較 cochain も、同じ tensor 鎖写像と終点後合成で可換。 -/
lemma dgModuleResolutionChange_secondPrimitive :
    (Cochain.ofHom (dgModuleResolutionChangeHom R C E a hs hq ha X Y ⊗ₘ
      dgModuleResolutionChangeHom R C E a hs hq ha Y Z)).comp
      (dgModuleFunctorResolutionSecondCompositePrimitive R C E G
        (dgModuleResolutionChangeObject R C E a hs hq X)
        (dgModuleResolutionChangeObject R C E a hs hq Y)
        (dgModuleResolutionChangeObject R C E a hs hq Z)) (zero_add (-1)) =
    (dgModuleFunctorResolutionSecondCompositePrimitive R C E F X Y Z).comp
      (Cochain.ofHom (moduleHomPostcompose R E X.replacement.val
        (F.obj Z.source) (G.obj Z.source) (a Z.source))) (add_zero (-1)) := by
  let X' := dgModuleResolutionChangeObject R C E a hs hq X
  let Y' := dgModuleResolutionChangeObject R C E a hs hq Y
  let Z' := dgModuleResolutionChangeObject R C E a hs hq Z
  let f := dgModuleResolutionChangeHom R C E a hs hq ha X Y
  let g := dgModuleResolutionChangeHom R C E a hs hq ha Y Z
  let b := moduleHomPostcompose R E Y.replacement.val
    (F.obj Z.source) (G.obj Z.source) (a Z.source)
  let c := moduleHomPostcompose R E X.replacement.val
    (F.obj Z.source) (G.obj Z.source) (a Z.source)
  have hp : (Cochain.ofHom g).comp (dgModuleFunctorResolutionPrimitive R C E G Y' Z')
      (zero_add (-1)) =
    (dgModuleFunctorResolutionPrimitive R C E F Y Z).comp (Cochain.ofHom b) (add_zero (-1)) :=
    dgModuleResolutionChangeHom_comparison R C E a hs hq ha Y Z
  have ht := tensorLeft_cochain_square (-1) f g b
    (dgModuleFunctorResolutionPrimitive R C E F Y Z)
    (dgModuleFunctorResolutionPrimitive R C E G Y' Z') hp
  have H := cochain_postcompose_square (-1) (f ⊗ₘ g) (f ⊗ₘ b) c
    (dgModuleFunctorResolutionSecondCompositionMap R C E F X Y Z)
    (dgModuleFunctorResolutionSecondCompositionMap R C E G X' Y' Z') _ _ ht
    (dgModuleResolutionChange_secondCompositionMap R C E a hs hq ha X Y Z)
  simpa only [dgModuleFunctorResolutionSecondCompositePrimitive] using! H
end SerrePositivity.InfinityCategories
