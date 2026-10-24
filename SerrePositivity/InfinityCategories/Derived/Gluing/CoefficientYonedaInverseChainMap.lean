module
public import SerrePositivity.InfinityCategories.Derived.Gluing.CoefficientYonedaSpaceIso
public import SerrePositivity.InfinityCategories.Derived.Gluing.ComplexPinchedUnitModel

/-! # Yoneda 係数空間同型の実逆射

概要：Yoneda 係数空間同型の逆を、同じ Yoneda 鎖射の pinched 作用で表す。
方針：同型合成の逆を有限展開し、単位 Hom の自然性と鎖写像の関手則を使う。
規約：元の対象宇宙と端点を保持し、heartbeat 上限は変更しない。
使われ方：正規化 prism の係数写像を canonical 始域同型の逆へ照合する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded MonoidalCategory
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (c : C) (N : RightModule R C)

lemma dgGluingCoefficientYonedaSpaceIso_inv_chainMap :
    (dgGluingCoefficientYonedaSpaceIso R C c N).inv =
      pinchedHomChainMap (D := RightModule R C)
        (E := DGComplexPinchedModel.{u, max (u + 1) v} (N.obj (Opposite.op c)))
        (x := representable R c) (y := N)
        (x' := complexPinchedSource _) (y' := complexPinchedTarget _)
        ((dgYonedaIso R c N).hom ≫ (complexUnitHomIso (N.obj (Opposite.op c))).hom) := by
  dsimp only [dgGluingCoefficientYonedaSpaceIso, Iso.trans_inv, Iso.symm_inv,
    dgGluingComplexPinchedMapIso]
  let K := homObject R (RightModule R C) (representable R c) N
  let L := N.obj (Opposite.op c)
  have hcomp := pinchedHomChainMap_comp
    (D := RightModule R C) (E := DGComplexPinchedModel.{u, max (u + 1) v} K)
    (T := DGComplexPinchedModel.{u, max (u + 1) v} L)
    (x := representable R c) (y := N)
    (x' := complexPinchedSource K) (y' := complexPinchedTarget K)
    (x'' := complexPinchedSource L) (y'' := complexPinchedTarget L)
    (complexUnitHomIso K).hom (homPostcompose (𝟙_ (Complex R)) (dgYonedaIso R c N).hom)
  rw [dgGluingPinchedComplexModelIso_hom, complexPinchedMap, ← hcomp]
  exact congrArg (fun q : K ⟶ homComplex R (𝟙_ (Complex R)) L =>
    pinchedHomChainMap (D := RightModule R C)
      (E := DGComplexPinchedModel.{u, max (u + 1) v} L)
      (x := representable R c) (y := N)
      (x' := complexPinchedSource L) (y' := complexPinchedTarget L) q)
    (complexUnitHomIso_naturality (dgYonedaIso R c N).hom)

end SerrePositivity.InfinityCategories
