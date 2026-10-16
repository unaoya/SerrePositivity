module
public import SerrePositivity.DifferentialGraded.Tensor.AssociatorComponentCompatibility
public import SerrePositivity.DifferentialGraded.Tensor.AssociatorValueHom

/-! # 結合比較の左端のdg作用との整合性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z) (F : Type t)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F]
  [Small.{u} B] [Small.{u} C] [Small.{u} E]

/-- 左F作用と結合比較の三重生成元上での可換式。 -/
lemma associatorValueHom_leftAction_compatibility (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (b : B) (c : C) (e : E) (f f' : F) {p k r s i m n : ℤ}
    (hi : r + s = i) (hm : k + i = m) (hn : m + p = n) (g : GradedHom A f f' p)
    (t : (R.value e f).X k) (q : (Q.value c e).X r) (v : (P.value b c).X s) :
    (associatorValueHom A B C E F P Q R b f').f n
      (SerrePositivity.DifferentialGraded.leftAction A
        ((compose A B E F (compose A B C E P Q) R).leftAt b) g
        (associatorLeftElement A B C E F P Q R b c e f (n := m) t q v hi hm) hn) =
    SerrePositivity.DifferentialGraded.leftAction A
      ((compose A B C F P (compose A C E F Q R)).leftAt b) g
      ((associatorValueHom A B C E F P Q R b f).f m
        (associatorLeftElement A B C E F P Q R b c e f (n := m) t q v hi hm)) hn := by
  have hLC := associatorLeftCochain_apply A B C E F P Q R b f f' g
    (associatorLeftElement A B C E F P Q R b c e f (n := m) t q v hi hm) hn
  have hRC := associatorRightCochain_apply A B C E F P Q R b f f' g
    ((associatorValueHom A B C E F P Q R b f).f m
      (associatorLeftElement A B C E F P Q R b c e f (n := m) t q v hi hm)) hn
  have hc := associatorComponent_leftCochain_compatibility A B C E F P Q R b c e f f'
    hi hm hn g t q v
  simp only [associatorValueHom_apply] at hLC hRC ⊢
  exact (congrArg (fun z =>
    associatorValueComponent A B C E F P Q R b f' n z) hLC.symm).trans (hc.trans hRC)

/-- 結合比較は左F作用の主Hom写像と全次数で可換。 -/
lemma associatorValueHom_left_naturality (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (b : B) (f f' : F) :
    associatorLeftMap A B C E F P Q R b f f' ≫
      homPostcompose ((compose A B E F (compose A B C E P Q) R).value b f)
        (associatorValueHom A B C E F P Q R b f') =
    associatorRightMap A B C E F P Q R b f f' ≫
      homPrecompose (associatorValueHom A B C E F P Q R b f)
        ((compose A B C F P (compose A C E F Q R)).value b f') := by
  apply hom_naturality_of_apply
  intro p g
  rw [associatorLeftMap_apply, associatorRightMap_apply]
  apply associatorLeft_cochain_element_ext A B C E F P Q R b f
  intro c e k r s i m n hi hm hn t q v
  have hL := cochain_comp_ofHom_apply
    (associatorLeftCochain A B C E F P Q R b f f' p g)
    (associatorValueHom A B C E F P Q R b f') hn
    (associatorLeftElement A B C E F P Q R b c e f (n := m) t q v hi hm)
  have hR := cochain_ofHom_comp_apply
    (associatorValueHom A B C E F P Q R b f)
    (associatorRightCochain A B C E F P Q R b f f' p g) hn
    (associatorLeftElement A B C E F P Q R b c e f (n := m) t q v hi hm)
  have hc := associatorComponent_leftCochain_compatibility A B C E F P Q R b c e f f'
    hi hm hn g t q v
  simp only [associatorValueHom_apply] at hL hR
  exact hL.trans (hc.trans hR.symm)

end SerrePositivity.DifferentialGraded.BimoduleTensor
