module
public import SerrePositivity.DifferentialGraded.Tensor.PentagonShortElements
public import SerrePositivity.DifferentialGraded.Tensor.PentagonLongElements
public import SerrePositivity.DifferentialGraded.Tensor.QuadCochainExt
public import SerrePositivity.DifferentialGraded.Tensor.BimoduleValueHom
public import SerrePositivity.DifferentialGraded.Tensor.BimoduleFunctor
public import SerrePositivity.DifferentialGraded.Bimodule.ValueExt

/-! # 全Hom自然なbimodule合成の五角coherence -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t x
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  (F : Type t) (G : Type x)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F] [DGCategory A G]
  [Small.{u} B] [Small.{u} C] [Small.{u} E] [Small.{u} F]
variable (P : Bimodule A B C) (Q : Bimodule A C E) (R : Bimodule A E F) (S : Bimodule A F G)

/-- 固定成分による値のchain mapとしての五角。 -/
lemma pentagonValueHom (b : B) (g : G) :
    associatorValueHom A B E F G (compose A B C E P Q) R S b g ≫
      associatorValueHom A B C E G P Q (compose A E F G R S) b g =
    composeValueHom A B F G (associatorIso A B C E F P Q R).hom
      (𝟙 (BimoduleCategory.of A F G S)) b g ≫
      associatorValueHom A B C F G P (compose A C E F Q R) S b g ≫
      composeValueHom A B C G (𝟙 (BimoduleCategory.of A B C P))
        (associatorIso A C E F G Q R S).hom b g := by
  apply Cochain.ofHom_injective
  apply quadLeft_cochain_element_ext A B C E F G P Q R S b g
  intro c e f a k r s i m n t hi hm hn ht σ τ q v
  simp only [add_zero] at ht
  cases ht
  simp only [Cochain.ofHom_v]
  change associatorValueComponent A B C E G P Q (compose A E F G R S) b g n
    (associatorValueComponent A B E F G (compose A B C E P Q) R S b g n
      (quadLeftElement A B C E F G P Q R S b c e f g σ τ q v hi hm hn)) =
    composeMapComponent A B C G (𝟙 (BimoduleCategory.of A B C P))
      (associatorIso A C E F G Q R S).hom b g n
      (associatorValueComponent A B C F G P (compose A C E F Q R) S b g n
        (composeMapComponent A B F G (associatorIso A B C E F P Q R).hom
          (𝟙 (BimoduleCategory.of A F G S)) b g n
          (quadLeftElement A B C E F G P Q R S b c e f g σ τ q v hi hm hn)))
  exact (pentagonShort_component_element A B C E F G P Q R S b c e f g
    (l := a + k) (j := a + k + r) σ τ q v hi hm hn rfl rfl).trans
    (pentagonLong_component_element A B C E F G P Q R S b c e f g
      (l := a + k) (j := a + k + r) σ τ q v hi hm hn rfl rfl).symm

/-- 元の値の結合同型と合成mapに対する五角。 -/
lemma pentagonValue (b : B) (g : G) :
    (associatorValueIso A B E F G (compose A B C E P Q) R S b g).hom ≫
      (associatorValueIso A B C E G P Q (compose A E F G R S) b g).hom =
    composeValueMap A B F G (associatorIso A B C E F P Q R).hom
      (𝟙 (BimoduleCategory.of A F G S)) b g ≫
      (associatorValueIso A B C F G P (compose A C E F Q R) S b g).hom ≫
      composeValueMap A B C G (𝟙 (BimoduleCategory.of A B C P))
        (associatorIso A C E F G Q R S).hom b g := by
  simpa only [associatorValueHom_eq, composeValueHom_eq] using
    pentagonValueHom A B C E F G P Q R S b g

/-- 実際の閉零bimodule射としての結合同型の五角。 -/
lemma pentagon :
    (associatorIso A B E F G (compose A B C E P Q) R S).hom ≫
      (associatorIso A B C E G P Q (compose A E F G R S)).hom =
    composeMap A B F G (associatorIso A B C E F P Q R).hom
      (𝟙 (BimoduleCategory.of A F G S)) ≫
      (associatorIso A B C F G P (compose A C E F Q R) S).hom ≫
      composeMap A B C G (𝟙 (BimoduleCategory.of A B C P))
        (associatorIso A C E F G Q R S).hom := by
  apply BimoduleCategory.value_hom_ext A B G
  intro b g
  simp only [CategoryTheory.Functor.map_comp, composeMap_value_eval,
    associatorIso_hom_value_eval]
  exact pentagonValue A B C E F G P Q R S b g

end SerrePositivity.DifferentialGraded.BimoduleTensor
