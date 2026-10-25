module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetProjectionComposition
/-!
概要：元終域への comma 比較の実 Hom 鎖写像は全豊穣合成を保存する。
方針：三成分の全次数評価を tensor の生成元で評価し、comma Hom の一意性を適用する。
規約：元の二射影と第三 cochain を同時に保持する。
使われ方：元二脚を持つ実 dg comma 比較関手の合成欄を供給する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
open DifferentialGraded KST.SConstruction
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (E : Type z) [DGCategory R E] [Small.{u} E]
  (p : DGFunctor R C E) (q : DGFunctor R D E)
  (X Y Z : DGGluingObject R C D (dgHomGluingBimodule R C D E p q))
set_option maxRecDepth 1024 in
lemma dgGluingHomTargetCommaHomMap_composition :
    eComp (Complex R) X Y Z ≫ dgGluingHomTargetCommaHomMap R C D E p q X Z =
    (dgGluingHomTargetCommaHomMap R C D E p q X Y ⊗ₘ
      dgGluingHomTargetCommaHomMap R C D E p q Y Z) ≫
      eComp (Complex R) (dgGluingHomTargetCommaObject R C D E p q X)
        (dgGluingHomTargetCommaObject R C D E p q Y)
        (dgGluingHomTargetCommaObject R C D E p q Z) := by
  apply dgFunctorCommaHom_ext R D E q
    (dgGluingHomTargetCommaObject R C D E p q X)
    (dgGluingHomTargetCommaObject R C D E p q Z) _
  · rw [Category.assoc, dgGluingHomTargetCommaHomMap_source R C D E p q X Z]
    have hc := (dgFunctorCommaSource R D E q).map_comp
      (dgGluingHomTargetCommaObject R C D E p q X)
      (dgGluingHomTargetCommaObject R C D E p q Y)
      (dgGluingHomTargetCommaObject R C D E p q Z)
    dsimp only [dgFunctorCommaSource] at hc
    change eComp (Complex R)
      (dgGluingHomTargetCommaObject R C D E p q X)
      (dgGluingHomTargetCommaObject R C D E p q Y)
      (dgGluingHomTargetCommaObject R C D E p q Z) ≫
      dgFunctorCommaSourceHomMap R D E q
        (dgGluingHomTargetCommaObject R C D E p q X)
        (dgGluingHomTargetCommaObject R C D E p q Z) = _ at hc
    rw [Category.assoc, hc, tensorHom_comp_tensorHom_assoc]
    erw [dgGluingHomTargetCommaHomMap_source R C D E p q X Y,
      dgGluingHomTargetCommaHomMap_source R C D E p q Y Z]
    exact dgGluingComposition_right R C D (dgHomGluingBimodule R C D E p q) X Y Z
  · rw [Category.assoc, dgGluingHomTargetCommaHomMap_replacement R C D E p q X Z]
    have hc := (dgFunctorCommaReplacement R D E q).map_comp
      (dgGluingHomTargetCommaObject R C D E p q X)
      (dgGluingHomTargetCommaObject R C D E p q Y)
      (dgGluingHomTargetCommaObject R C D E p q Z)
    dsimp only [dgFunctorCommaReplacement] at hc
    change eComp (Complex R)
      (dgGluingHomTargetCommaObject R C D E p q X)
      (dgGluingHomTargetCommaObject R C D E p q Y)
      (dgGluingHomTargetCommaObject R C D E p q Z) ≫
      dgFunctorCommaReplacementHomMap R D E q
        (dgGluingHomTargetCommaObject R C D E p q X)
        (dgGluingHomTargetCommaObject R C D E p q Z) = _ at hc
    rw [Category.assoc, hc, tensorHom_comp_tensorHom_assoc]
    erw [dgGluingHomTargetCommaHomMap_replacement R C D E p q X Y,
      dgGluingHomTargetCommaHomMap_replacement R C D E p q Y Z]
    rw [← tensorHom_comp_tensorHom_assoc]
    erw [← p.map_comp X.left Y.left Z.left]
    change dgGluingComposition R C D (dgHomGluingBimodule R C D E p q) X Y Z ≫
      (dgGluingLeftHomMap R C D (dgHomGluingBimodule R C D E p q) X Z ≫
        p.map X.left Z.left) = _
    rw [← Category.assoc, dgGluingComposition_left, Category.assoc]
  · apply Cochain.ext
    intro n k hk
    apply mapBifunctor.hom_ext
    intro i j hij
    change i + j = n at hij
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro a b
    simp only [dgFunctorCommaHomComparison, Cochain.zero_cochain_comp_v,
      Cochain.ofHom_v, HomologicalComplex.comp_f]
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
    erw [tensorMap_apply]
    have he : k = n - 1 := by omega
    subst k
    cases hij
    have h := dgGluingHomTargetCommaHomMap_forward_primitive R C D E p q X Y Z (r := i) (s := j) a b
    simp only [forward, dgFunctorCommaPrimitive, ιTensorObj, ModuleCat.Hom.hom] at h ⊢
    exact h
end SerrePositivity.InfinityCategories
