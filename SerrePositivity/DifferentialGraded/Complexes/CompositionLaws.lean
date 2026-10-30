module
public import SerrePositivity.HomologicalAlgebra.CochainTensorTriple
public import SerrePositivity.DifferentialGraded.Complexes.Composition
public import SerrePositivity.DifferentialGraded.Complexes.HomComplex
public import SerrePositivity.HomologicalAlgebra.CochainTensorLinear
public import SerrePositivity.DifferentialGraded.Complexes.Unit

/-! # dg 合成の単位と結合 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A]

/-- 恒等 chain map に対応する閉次数零単位。 -/
def identity (X : Complex A) : 𝟙_ (Complex A) ⟶ homComplex A X X :=
  unitFromCycle _ ⟨Cochain.ofHom (𝟙 X), δ_ofHom _⟩

/-- 豊穣合成を純粋斉次 tensor で評価する。 -/
lemma enrichedComposition_apply (X Y Z : Complex A) (p q n : ℤ) (h : p + q = n)
    (f : Homogeneous X Y p) (g : Homogeneous Y Z q) :
    (enrichedComposition X Y Z).f n
      (ιTensorObj (homComplex A X Y) (homComplex A Y Z) p q n h (f ⊗ₜ[A] g)) =
      (p * q).negOnePow • f.comp g h := by
  have hc := enrichedComposition_component X Y Z p q n h
  have he := congr($(hc).hom (f ⊗ₜ[A] g))
  change (enrichedComposition X Y Z).f n
    (ιTensorObj (homComplex A X Y) (homComplex A Y Z) p q n h (f ⊗ₜ[A] g)) =
      (p * q).negOnePow • compositionComponent X Y Z q p n (by omega) (g ⊗ₜ[A] f) at he
  exact he

/-- 二重 tensor の射の等式を三重斉次 tensor へ帰着する。 -/
lemma triple_ext {P Q T S : Complex A} {f g : (P ⊗ Q) ⊗ T ⟶ S}
    (h : ∀ (i j k n : ℤ) (hn : i + j + k = n),
      (ιTensorObj P Q i j (i + j) rfl ▷ T.X k) ≫
        ιTensorObj (P ⊗ Q) T (i + j) k n hn ≫ f.f n =
      (ιTensorObj P Q i j (i + j) rfl ▷ T.X k) ≫
        ιTensorObj (P ⊗ Q) T (i + j) k n hn ≫ g.f n) : f = g := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact SerrePositivity.cochainTensorTriple_hom_ext P Q T n
    (fun i j k hn => h i j k n hn)

/-- associator の三重斉次成分公式。 -/
@[reassoc]
lemma ι_associator (P Q T : Complex A) (i j k n : ℤ) (hn : i + j + k = n) :
    (ιTensorObj P Q i j (i + j) rfl ▷ T.X k) ≫
      ιTensorObj (P ⊗ Q) T (i + j) k n hn ≫ (α_ P Q T).hom.f n =
    (α_ (P.X i) (Q.X j) (T.X k)).hom ≫
      (P.X i ◁ ιTensorObj Q T j k (j + k) rfl) ≫
        ιTensorObj P (Q ⊗ T) i (j + k) n (by omega) :=
  SerrePositivity.ιTensorObj_cochainTensorAssociator_hom P Q T i j k n hn

/-- 豊穣順の合成の結合則。符号の等式は p q+p r+q r の二つの展開。 -/
lemma enrichedComposition_assoc (W X Y Z : Complex A) :
    enrichedComposition W X Y ▷ homComplex A Y Z ≫ enrichedComposition W Y Z =
    (α_ _ _ _).hom ≫ homComplex A W X ◁ enrichedComposition X Y Z ≫
      enrichedComposition W X Z := by
  apply triple_ext
  intro p q r n hn
  simp only [HomologicalComplex.comp_f]
  rw [ι_whiskerRight_assoc, ι_associator_assoc, ι_whiskerLeft_assoc]
  apply ModuleCat.hom_ext
  apply TensorProduct.ext_threefold
  intro f g h
  change (enrichedComposition W Y Z).f n
    (ιTensorObj (homComplex A W Y) (homComplex A Y Z) (p + q) r n hn
      ((enrichedComposition W X Y).f (p + q)
        (ιTensorObj (homComplex A W X) (homComplex A X Y) p q (p + q) rfl
          (f ⊗ₜ[A] g)) ⊗ₜ[A] h)) =
    (enrichedComposition W X Z).f n
      (ιTensorObj (homComplex A W X) (homComplex A X Z) p (q + r) n (by omega)
        (f ⊗ₜ[A] (enrichedComposition X Y Z).f (q + r)
          (ιTensorObj (homComplex A X Y) (homComplex A Y Z) q r (q + r) rfl
            (g ⊗ₜ[A] h))))
  rw [enrichedComposition_apply, enrichedComposition_apply]
  rw [enrichedComposition_apply, enrichedComposition_apply]
  simp only [Cochain.units_smul_comp, Cochain.comp_units_smul, smul_smul,
    ← Int.negOnePow_add]
  rw [Cochain.comp_assoc _ _ _ rfl rfl hn]
  congr 1
  congr 1
  ring
/-- 豊穣順の閉単位の左単位則。 -/
lemma identity_comp (X Y : Complex A) :
    (λ_ (homComplex A X Y)).inv ≫ identity X ▷ _ ≫ enrichedComposition X X Y = 𝟙 _ := by
  apply HomologicalComplex.Hom.ext
  funext n
  change (leftUnitor' (homComplex A X Y)).inv n ≫
    (identity X ▷ homComplex A X Y).f n ≫ (enrichedComposition X X Y).f n = 𝟙 _
  rw [leftUnitor'_inv, Category.assoc, Category.assoc, ι_whiskerRight_assoc]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  change (enrichedComposition X X Y).f n
    (ιTensorObj (homComplex A X X) (homComplex A X Y) 0 n n (zero_add n)
      ((identity X).f 0 ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv 1) ⊗ₜ[A] f)) = f
  rw [enrichedComposition_apply]
  change (0 * n).negOnePow •
    (cycleFromUnit _ (identity X)).val.comp f (zero_add n) = f
  rw [identity, cycleFromUnit_unitFromCycle]
  simp

/-- 豊穣順の閉単位の右単位則。 -/
lemma comp_identity (X Y : Complex A) :
    (ρ_ (homComplex A X Y)).inv ≫ _ ◁ identity Y ≫ enrichedComposition X Y Y = 𝟙 _ := by
  apply HomologicalComplex.Hom.ext
  funext n
  change (rightUnitor' (homComplex A X Y)).inv n ≫
    (homComplex A X Y ◁ identity Y).f n ≫ (enrichedComposition X Y Y).f n = 𝟙 _
  rw [rightUnitor'_inv, Category.assoc, Category.assoc, ι_whiskerLeft_assoc]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  change (enrichedComposition X Y Y).f n
    (ιTensorObj (homComplex A X Y) (homComplex A Y Y) n 0 n (add_zero n)
      (f ⊗ₜ[A] (identity Y).f 0 ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv 1))) = f
  rw [enrichedComposition_apply]
  change (n * 0).negOnePow •
    f.comp (cycleFromUnit _ (identity Y)).val (add_zero n) = f
  rw [identity, cycleFromUnit_unitFromCycle]
  simp

/-- tensor の chain map から双次数成分を取り出すと tensorLift の微分条件を満たす。 -/
lemma tensorComponent_d {P Q T : Complex A} (c : P ⊗ Q ⟶ T) (i j : ℤ) :
    (ιTensorObj P Q i j (i + j) rfl ≫ c.f (i + j)) ≫ T.d (i + j) (i + j + 1) =
      (P.d i (i + 1) ▷ Q.X j) ≫
        (ιTensorObj P Q (i + 1) j (i + j + 1) (by omega) ≫ c.f (i + j + 1)) +
      i.negOnePow • ((P.X i ◁ Q.d j (j + 1)) ≫
        (ιTensorObj P Q i (j + 1) (i + j + 1) (by omega) ≫ c.f (i + j + 1))) := by
  have hd := SerrePositivity.cochainTensorι_d P Q i j
  change ιTensorObj P Q i j (i + j) rfl ≫ (P ⊗ Q).d (i + j) (i + j + 1) = _ at hd
  rw [Category.assoc, c.comm, ← Category.assoc, hd,
    Preadditive.add_comp, Linear.units_smul_comp, Category.assoc, Category.assoc]

/-- 成分 accessor と tensorLift constructor の chain map の往復。 -/
lemma tensorLift_recover {P Q T : Complex A} (c : P ⊗ Q ⟶ T) :
    tensorLift (fun i j n h => ιTensorObj P Q i j n h ≫ c.f n) (tensorComponent_d c) = c := by
  apply tensorHom_ext
  intro i j n h
  rw [ι_tensorLift]
end SerrePositivity.DifferentialGraded
