module
public import SerrePositivity.KST.SConstruction.DGCoherenceInverses
public import SerrePositivity.DifferentialGraded.Tensor.Pentagon
public import SerrePositivity.DifferentialGraded.Tensor.AssociatorNaturality

/-! # 元の tensor 結合同型の逆向きの五角と自然性
概要：実延長で使う逆結合同型の式を、元の順向きの coherence から導く。
方針：元の合成双関手で同型を運び、抽象的な同型の逆経路の判定を使う。
規約：元の tensor 射を保つ。使われ方：実 graph 延長の三重合成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t s
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  [DGCategory A B] [Small.{u} B] [DGCategory A C] [Small.{u} C] [DGCategory A E]

/-- 元の合成双関手による、二つの閉零双加群同型の tensor。 -/
def dgBimoduleTensorMapIso {P P' : BimoduleCategory A B C}
    {Q Q' : BimoduleCategory A C E} (e : P ≅ P') (f : Q ≅ Q') :
    (BimoduleTensor.composeFunctor A B C E).obj (P, Q) ≅
      (BimoduleTensor.composeFunctor A B C E).obj (P', Q') :=
  (BimoduleTensor.composeFunctor A B C E).mapIso (e.prod f)

/-- 同型の tensor の順射は元の同じ tensor 射。 -/
lemma dgBimoduleTensorMapIso_hom {P P' : BimoduleCategory A B C}
    {Q Q' : BimoduleCategory A C E} (e : P ≅ P') (f : Q ≅ Q') :
    (dgBimoduleTensorMapIso A B C E e f).hom = BimoduleTensor.composeMap A B C E e.hom f.hom :=
  rfl

/-- 同型の tensor の逆射は元の逆射の tensor。 -/
lemma dgBimoduleTensorMapIso_inv {P P' : BimoduleCategory A B C}
    {Q Q' : BimoduleCategory A C E} (e : P ≅ P') (f : Q ≅ Q') :
    (dgBimoduleTensorMapIso A B C E e f).inv = BimoduleTensor.composeMap A B C E e.inv f.inv :=
  rfl

/-- 後因子の元の射の合成は、同じ前因子を固定した tensor の合成となる。 -/
lemma dgBimoduleTensor_second_comp (P : BimoduleCategory A B C)
    {Q Q' Q'' : BimoduleCategory A C E} (f : Q ⟶ Q') (g : Q' ⟶ Q'') :
    BimoduleTensor.composeMap A B C E (𝟙 P) (f ≫ g) =
      BimoduleTensor.composeMap A B C E (𝟙 P) f ≫
        BimoduleTensor.composeMap A B C E (𝟙 P) g := by
  simpa only [Category.id_comp] using
    BimoduleTensor.composeMap_comp A B C E (𝟙 P) (𝟙 P) f g

section Pentagon
variable [Small.{u} E] (F : Type t) [DGCategory A F] [Small.{u} F]
  (G : Type s) [DGCategory A G]
  (P : Bimodule A B C) (Q : Bimodule A C E) (R : Bimodule A E F) (S : Bimodule A F G)

/-- 元の逆結合同型と元の tensor 射が満たす逆向きの五角。 -/
lemma dgTensor_associator_inv_pentagon :
    BimoduleTensor.composeMap A B C G (𝟙 (BimoduleCategory.of A B C P))
        (BimoduleTensor.associatorIso A C E F G Q R S).inv ≫
      (BimoduleTensor.associatorIso A B C F G P (BimoduleTensor.compose A C E F Q R) S).inv ≫
      BimoduleTensor.composeMap A B F G (BimoduleTensor.associatorIso A B C E F P Q R).inv
        (𝟙 (BimoduleCategory.of A F G S)) =
    (BimoduleTensor.associatorIso A B C E G P Q (BimoduleTensor.compose A E F G R S)).inv ≫
      (BimoduleTensor.associatorIso A B E F G (BimoduleTensor.compose A B C E P Q) R S).inv := by
  have h := dgIso_inverse_pentagon
    (dgBimoduleTensorMapIso A B C G (Iso.refl (BimoduleCategory.of A B C P))
      (BimoduleTensor.associatorIso A C E F G Q R S).symm)
    (BimoduleTensor.associatorIso A B C F G P (BimoduleTensor.compose A C E F Q R) S).symm
    (dgBimoduleTensorMapIso A B F G
      (BimoduleTensor.associatorIso A B C E F P Q R).symm
      (Iso.refl (BimoduleCategory.of A F G S)))
    (BimoduleTensor.associatorIso A B E F G (BimoduleTensor.compose A B C E P Q) R S).symm
    (BimoduleTensor.associatorIso A B C E G P Q (BimoduleTensor.compose A E F G R S)).symm
    (by
      simpa only [dgBimoduleTensorMapIso_inv, Iso.symm_inv, Iso.refl_inv] using
        BimoduleTensor.pentagon A B C E F G P Q R S)
  simpa only [dgBimoduleTensorMapIso_hom, Iso.symm_hom, Iso.refl_hom] using h

end Pentagon

section Naturality
variable [Small.{u} E] (F : Type t) [DGCategory A F]
  {P P' : BimoduleCategory A B C} {Q Q' : BimoduleCategory A C E}
  {R R' : BimoduleCategory A E F}

/-- 元の三変数自然性は、同じ逆結合同型についても成り立つ。 -/
lemma dgTensor_associator_inv_naturality (f : P ⟶ P') (g : Q ⟶ Q') (h : R ⟶ R') :
    BimoduleTensor.composeMap A B C F f (BimoduleTensor.composeMap A C E F g h) ≫
        (BimoduleTensor.associatorIso A B C E F
          (BimoduleCategory.underlying A B C P') (BimoduleCategory.underlying A C E Q')
          (BimoduleCategory.underlying A E F R')).inv =
      (BimoduleTensor.associatorIso A B C E F
        (BimoduleCategory.underlying A B C P) (BimoduleCategory.underlying A C E Q)
        (BimoduleCategory.underlying A E F R)).inv ≫
        BimoduleTensor.composeMap A B E F (BimoduleTensor.composeMap A B C E f g) h :=
  dgIso_inverse_naturality _ _ _ _ (BimoduleTensor.associatorIso_naturality A B C E F f g h)

end Naturality
end SerrePositivity.KST.SConstruction
