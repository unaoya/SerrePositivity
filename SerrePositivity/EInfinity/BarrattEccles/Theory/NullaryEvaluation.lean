module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.HopfNullaryUnitMap
public import SerrePositivity.EInfinity.BarrattEccles.Theory.FreeHopfComparison
public import SerrePositivity.EInfinity.Operad.AlgebraEvaluationAll
public import SerrePositivity.EInfinity.Operad.TensorFamilyUnitSeparation

/-!
# 零入力の族を代入する作用の照合

HA 3.2.4.7。指定単位射を有限入力族へ移し、BE の零入力消去を代数の作用へ接続する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers
open scoped BigOperators
attribute [local implicit_reducible] tensorFamily TensorPowers.power
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct
variable {A : Type u} [CommRing A]

/-- 零乗だけの族を連結する同型は、指定単位族の縮約である。 -/
lemma tensorPowerFamilyIso_zero (K : Complex A) (n : ℕ) :
    (tensorPowerFamilyIso K n (fun _ => 0)).hom ≫
      eqToHom (congrArg (power K) (by simp : (∑ _ : Fin n, 0) = 0)) =
        (tensorUnitFamilyIso A n).hom := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [tensorPowerFamilyIso, Iso.trans_hom, whiskerLeftIso_hom, eqToIso.hom,
      appendIso_zero_left, tensorUnitFamilyIso_succ_head, Category.assoc, eqToHom_trans]
    change (𝟙_ (Complex A) ◁ (tensorPowerFamilyIso K n (fun _ => 0)).hom) ≫
      (λ_ (power K (∑ _ : Fin n, 0))).hom ≫
        eqToHom (congrArg (power K) (by simp : (∑ _ : Fin n, 0) = 0)) = _
    rw [← leftUnitor_naturality, ← whiskerLeft_comp_assoc, ih]
    rfl

/-- 右側の単位を因子ごとに挿入して分離すると、単位族の逆を挿入する射になる。 -/
lemma tensorFamilyTensorIso_insert_right (n : ℕ) (V : Fin n → Complex A) :
    tensorFamilyMap n (fun j => (ρ_ (V j)).inv) ≫
      (tensorFamilyTensorIso n V (fun _ => 𝟙_ (Complex A))).hom =
    (ρ_ (tensorFamily n V)).inv ≫
      (𝟙 (tensorFamily n V) ⊗ₘ (tensorUnitFamilyIso A n).inv) := by
  apply (cancel_mono ((𝟙 (tensorFamily n V) ⊗ₘ (tensorUnitFamilyIso A n).hom) ≫
    (ρ_ (tensorFamily n V)).hom)).1
  simp only [Category.assoc]
  rw [tensorFamilyTensorIso_unit_right n V, ← tensorFamilyMap_comp]
  simp only [Iso.inv_hom_id, tensorFamilyMap_id, tensorHom_comp_tensorHom_assoc,
    Category.comp_id, tensorHom_id, id_whiskerRight, Category.id_comp]

namespace BarrattEccles
variable (R : Type u) [CommRing R] (K : Complex R) (m n : ℕ)

/-- 零入力の指定係数を前半の入力へ入れる、実際の反復作用の始域の射。 -/
def nullarySourceInsert :
    (operad R).arity (m + n) ⊗ power K n ⟶
      (operad R).arity (m + n) ⊗
        (tensorFamily m (fun _ => (operad R).arity 0 ⊗ power K 0) ⊗ power K n) :=
  (operad R).arity (m + n) ◁ ((λ_ (power K n)).inv ≫
    ((nullaryInputFamily R m ≫
      tensorFamilyMap m (fun _ => (ρ_ ((operad R).arity 0)).inv)) ▷ power K n))

/-- 指定係数の零入力代入は、係数消去の同じ射を入力冪とテンソルした射である。 -/
lemma nullarySourceInsert_operation :
    nullarySourceInsert R K m n ≫
      (operad R).iteratedOperationTensor K m n (fun _ => 0) ≫
        eqToHom (congrArg (fun j => (operad R).arity j ⊗ power K j)
          (by simp : (∑ _ : Fin m, 0) + n = n)) =
      nullaryPrefixDelete R m n ▷ power K n := by
  let e := eqToHom (congrArg (power K) (by simp : (∑ _ : Fin m, 0) = 0))
  have hp : (tensorPowerFamilyIso K m (fun _ => 0)).hom =
      (tensorUnitFamilyIso R m).hom ≫ inv e := by
    apply (cancel_mono e).1
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    exact tensorPowerFamilyIso_zero K m
  have hs := congrArg (fun f => (operad R).arity (m + n) ◁ (f ▷ power K n))
    (tensorFamilyTensorIso_insert_right m (fun _ => (operad R).arity 0))
  simp only [comp_whiskerRight, whiskerLeft_comp] at hs
  let C := (operad R).arity (m + n)
  let F := tensorFamily m (fun _ => (operad R).arity 0)
  let U := tensorFamily m (fun _ => 𝟙_ (Complex R))
  let T := power K n
  let u := (tensorUnitFamilyIso R m).inv
  have hm :
      (C ◁ ((𝟙 F ⊗ₘ u) ▷ T)) ≫ (C ◁ (α_ F U T).hom) ≫
        (α_ C F (U ⊗ T)).inv =
      (C ◁ (α_ F (𝟙_ (Complex R)) T).hom) ≫
        (α_ C F (𝟙_ (Complex R) ⊗ T)).inv ≫ (𝟙 (C ⊗ F) ⊗ₘ (u ▷ T)) := by
    simp only [tensorHom_def, whiskerLeft_comp, comp_whiskerRight, Category.assoc]
    monoidal
  have hc (l : ℕ) (hl : l = 0) :
      ((operad R).arity (l + n) ◁ ((λ_ T).inv ≫
        (inv (eqToHom (congrArg (power K) hl)) ▷ T) ≫ (appendIso K l n).hom)) ≫
        eqToHom (congrArg (fun j => (operad R).arity j ⊗ power K j)
          ((congrArg (fun j => j + n) hl).trans (Nat.zero_add n))) =
      eqToHom (congrArg (operad R).arity
        ((congrArg (fun j => j + n) hl).trans (Nat.zero_add n))) ▷ T := by
    subst l
    dsimp only [T, TensorPowers.power]
    simp only [eqToHom_refl, IsIso.inv_id, id_whiskerRight, Category.id_comp,
      appendIso_zero_left, Iso.inv_hom_id_assoc,
      whiskerLeft_eqToHom, eqToHom_whiskerRight, eqToHom_trans]
  dsimp only [nullarySourceInsert, Operad.iteratedOperationTensor, nullaryPrefixDelete,
    coefficientUnitInsert]
  simp only [whiskerLeft_comp, comp_whiskerRight, Category.assoc]
  dsimp only [TensorPowers.power]
  rw [reassoc_of% hs, hp]
  rw [reassoc_of% hm, tensorHom_comp_tensorHom_assoc, Category.id_comp]
  simp only [comp_whiskerRight, Category.assoc]
  rw [← comp_whiskerRight_assoc, Iso.inv_hom_id]
  simp only [id_whiskerRight, Category.id_comp]
  calc
    _ = ((coefficientUnitInsert C F (nullaryInputFamily R m) ≫
        (operad R).composeFirstInputs m n (fun _ => 0)) ▷ T) ≫
      ((operad R).arity ((∑ _ : Fin m, 0) + n) ◁
        ((λ_ T).inv ≫ (inv e ▷ T) ≫ (appendIso K (∑ _ : Fin m, 0) n).hom)) ≫
      eqToHom (congrArg (fun j => (operad R).arity j ⊗ power K j)
        (by simp : (∑ _ : Fin m, 0) + n = n)) := by
          dsimp only [coefficientUnitInsert]
          simp only [tensorHom_def, whiskerLeft_comp, comp_whiskerRight, Category.assoc]
          monoidal
    _ = _ := by
      rw [hc (∑ _ : Fin m, 0) (by simp)]
      simp only [coefficientUnitInsert, comp_whiskerRight, Category.assoc, C, T]

/-- 零入力係数を各入力で評価して得る、指定された単位入力の有限族。 -/
def nullaryUnitPower (Y : (operad R).Algebra) (a : ℕ) :
    𝟙_ (Complex R) ⟶ power Y.carrier a :=
  (tensorUnitFamilyIso R a).inv ≫ tensorFamilyMap a (fun _ =>
    (nullaryCoefficientIso R).inv ≫ (ρ_ ((operad R).arity 0)).inv ≫ Y.action 0) ≫
    eqToHom (tensorFamily_const Y.carrier a)

/-- 係数消去を実際の代数の作用へ移すと、前半の入力への指定単位族の代入となる。 -/
lemma nullaryPrefixDelete_action (Y : (operad R).Algebra) (a b : ℕ) :
    (nullaryPrefixDelete R a b ▷ power Y.carrier b) ≫ Y.action b =
      ((operad R).arity (a + b) ◁ ((λ_ (power Y.carrier b)).inv ≫
        (nullaryUnitPower R Y a ▷ power Y.carrier b) ≫
          (appendIso Y.carrier a b).hom)) ≫ Y.action (a + b) := by
  have ht (i j : ℕ) (h : i = j) :
      eqToHom (congrArg (fun k => (operad R).arity k ⊗ power Y.carrier k) h) ≫
        Y.action j = Y.action i := by cases h; exact Category.id_comp _
  have hv : (nullaryInputFamily R a ≫
      tensorFamilyMap a (fun _ => (ρ_ ((operad R).arity 0)).inv)) ≫
      tensorFamilyGenerator Y.carrier (fun j => (operad R).arity j ⊗ power Y.carrier j)
        Y.action a (fun _ => 0) = nullaryUnitPower R Y a := by
    simp only [nullaryUnitPower, nullaryInputFamily, tensorFamilyGenerator_asMap,
      tensorFamilyMap_comp, Category.assoc]
  calc
    _ = nullarySourceInsert R Y.carrier a b ≫
        (operad R).iteratedOperationTensor Y.carrier a b (fun _ => 0) ≫
        eqToHom (congrArg (fun j => (operad R).arity j ⊗ power Y.carrier j)
          (by simp : (∑ _ : Fin a, 0) + b = b)) ≫ Y.action b := by
      simpa only [Category.assoc] using
        (congrArg (fun q => q ≫ Y.action b)
          (nullarySourceInsert_operation R Y.carrier a b)).symm
    _ = _ := by
      rw [ht ((∑ _ : Fin a, 0) + b) b (by simp), Y.iteratedOperationTensor_action]
      have h := congrArg (fun f => (operad R).arity (a + b) ◁ (f ▷ power Y.carrier b)) hv
      simp only [comp_whiskerRight, whiskerLeft_comp] at h
      simp only [nullarySourceInsert, tensorHom_id, whiskerLeft_comp, comp_whiskerRight,
        Category.assoc]
      rw [reassoc_of% h]

/-- 指定単位射の同じ有限族として、零入力族を読む。 -/
lemma nullaryUnitPower_eq (Y : (operad R).Algebra) (a : ℕ)
    (h0 : IsIso ((hopf R).counit.map.app (FiniteBijection.of 0))) :
    nullaryUnitPower R Y a = (tensorUnitFamilyIso R a).inv ≫
      tensorFamilyMap a (fun _ => (hopfTensorUnitMap (hopf R) h0 Y).hom) ≫
        eqToHom (tensorFamily_const Y.carrier a) := by
  rw [nullaryUnitPower, barrattEcclesTensorUnitMap_nullary R h0 Y]

end BarrattEccles
end SerrePositivity.EInfinity
