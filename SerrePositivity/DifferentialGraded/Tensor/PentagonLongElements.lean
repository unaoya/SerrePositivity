module
public import SerrePositivity.DifferentialGraded.Tensor.QuadElements
public import SerrePositivity.DifferentialGraded.Tensor.AssociatorIsoElements
public import SerrePositivity.DifferentialGraded.Tensor.BimoduleMapElementValues
public import SerrePositivity.DifferentialGraded.Bimodule.ValueIdentity

/-! # 五角の三辺からなる経路の四重生成元上の評価 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t x
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  (F : Type t) (G : Type x)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F] [DGCategory A G]
  [Small.{u} B] [Small.{u} C] [Small.{u} E] [Small.{u} F]
variable (P : Bimodule A B C) (Q : Bimodule A C E) (R : Bimodule A E F) (S : Bimodule A F G)

lemma pentagonLongFirst_element (b : B) (c : C) (e : E) (f : F) (g : G)
    {a k r s i m z n : ℤ} (σ : (S.value f g).X a) (τ : (R.value e f).X k)
    (q : (Q.value c e).X r) (v : (P.value b c).X s)
    (hi : r + s = i) (hm : k + i = m) (hn : a + m = n) (hz : k + r = z) :
    composeMapComponent A B F G (associatorIso A B C E F P Q R).hom
      (𝟙 (BimoduleCategory.of A F G S)) b g n
      (quadLeftElement A B C E F G P Q R S b c e f g σ τ q v hi hm hn) =
    associatorLeftElement A B C F G P (compose A C E F Q R) S b c f g σ
      (BalancedTensor.element A E (R.rightAt f) (Q.leftAt c) e τ q hz) v (by omega) hn := by
  exact composeMapComponent_element_of_values A B F G
    (associatorIso A B C E F P Q R).hom (𝟙 (BimoduleCategory.of A F G S)) b f g
    σ (associatorLeftElement A B C E F P Q R b c e f τ q v hi hm)
    σ (associatorRightElement A B C E F P Q R b c e f
      (l := z) (n := m) τ q v hz (by omega)) hn
    (BimoduleCategory.valueMap_id_apply A F G (BimoduleCategory.of A F G S) f g a σ)
    (associatorIso_hom_value_element A B C E F P Q R b c e f τ q v hi hz hm)

lemma pentagonLongThird_element (b : B) (c : C) (e : E) (f : F) (g : G)
    {a k r s z j l n : ℤ} (σ : (S.value f g).X a) (τ : (R.value e f).X k)
    (q : (Q.value c e).X r) (v : (P.value b c).X s)
    (hz : k + r = z) (hj : a + z = j) (hl : a + k = l) (hn : j + s = n) :
    composeMapComponent A B C G (𝟙 (BimoduleCategory.of A B C P))
      (associatorIso A C E F G Q R S).hom b g n
      (quadMiddleElement A B C E F G P Q R S b c e f g σ τ q v hz hj hn) =
    quadRightElement A B C E F G P Q R S b c e f g σ τ q v hl (by omega) hn := by
  exact composeMapComponent_element_of_values A B C G
    (𝟙 (BimoduleCategory.of A B C P)) (associatorIso A C E F G Q R S).hom b c g
    (associatorLeftElement A C E F G Q R S c e f g σ τ q hz hj) v
    (associatorRightElement A C E F G Q R S c e f g
      (l := l) (n := j) σ τ q hl (by omega)) v hn
    (associatorIso_hom_value_element A C E F G Q R S c e f g σ τ q hz hl hj)
    (BimoduleCategory.valueMap_id_apply A B C (BimoduleCategory.of A B C P) b c s v)

lemma pentagonLong_component_element (b : B) (c : C) (e : E) (f : F) (g : G)
    {a k r s i m l j n : ℤ} (σ : (S.value f g).X a) (τ : (R.value e f).X k)
    (q : (Q.value c e).X r) (v : (P.value b c).X s)
    (hi : r + s = i) (hm : k + i = m) (hn : a + m = n)
    (hl : a + k = l) (hj : l + r = j) :
    composeMapComponent A B C G (𝟙 (BimoduleCategory.of A B C P))
      (associatorIso A C E F G Q R S).hom b g n
      (associatorValueComponent A B C F G P (compose A C E F Q R) S b g n
        (composeMapComponent A B F G (associatorIso A B C E F P Q R).hom
          (𝟙 (BimoduleCategory.of A F G S)) b g n
          (quadLeftElement A B C E F G P Q R S b c e f g σ τ q v hi hm hn))) =
    quadRightElement A B C E F G P Q R S b c e f g σ τ q v hl hj (by omega) := by
  have h₁ := pentagonLongFirst_element A B C E F G P Q R S b c e f g
    (z := k + r) σ τ q v hi hm hn rfl
  have h₂ := associatorValueComponent_element A B C F G P (compose A C E F Q R) S b c f g
    (k := a) (r := k + r) (s := s) (i := m) (l := j) (n := n) σ
    (BalancedTensor.element A E (R.rightAt f) (Q.leftAt c) e τ q rfl) v
    (by omega) (by omega) hn
  have h₁₂ := (congrArg
    (associatorValueComponent A B C F G P (compose A C E F Q R) S b g n) h₁).trans h₂
  have h₃ := pentagonLongThird_element A B C E F G P Q R S b c e f g
    (z := k + r) (j := j) (l := l) (n := n) σ τ q v rfl (by omega) hl (by omega)
  exact (congrArg (composeMapComponent A B C G (𝟙 (BimoduleCategory.of A B C P))
    (associatorIso A C E F G Q R S).hom b g n) h₁₂).trans h₃

end SerrePositivity.DifferentialGraded.BimoduleTensor
