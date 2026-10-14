module
public import SerrePositivity.DifferentialGraded.Complexes.HomComplex
public import SerrePositivity.PerfectComplex.TensorSymmetry

/-! # 通常順の dg 合成と豊穣順の符号比較 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A]

/-- 双次数の射が tensor 微分と両立すれば、非有界全 tensor から chain map を作る。
直和の普遍性を用いるので有限支持・有界性を仮定しない。 -/
def tensorLift {P Q T : Complex A}
    (b : ∀ (i j n : ℤ), i + j = n → (P.X i ⊗ Q.X j ⟶ T.X n))
    (db : ∀ (i j : ℤ),
      b i j (i + j) rfl ≫ T.d (i + j) (i + j + 1) =
        (P.d i (i + 1) ▷ Q.X j) ≫ b (i + 1) j (i + j + 1) (by omega) +
        i.negOnePow • ((P.X i ◁ Q.d j (j + 1)) ≫
          b i (j + 1) (i + j + 1) (by omega))) : P ⊗ Q ⟶ T where
  f n := mapBifunctorDesc (fun i j h => b i j n h)
  comm' n m h := by
    obtain rfl : m = n + 1 := h.symm
    apply mapBifunctor.hom_ext
    intro i j hij
    subst n
    rw [ι_mapBifunctorDesc_assoc]
    change b i j (i + j) rfl ≫ T.d (i + j) (i + j + 1) =
      (ιTensorObj P Q i j (i + j) rfl ≫ (P ⊗ Q).d (i + j) (i + j + 1)) ≫
        mapBifunctorDesc (fun i j h => b i j (_ + 1) h)
    have hd := SerrePositivity.cochainTensorι_d P Q i j
    change ιTensorObj P Q i j (i + j) rfl ≫ (P ⊗ Q).d (i + j) (i + j + 1) = _ at hd
    rw [hd, Preadditive.add_comp,
      Linear.units_smul_comp, Category.assoc, Category.assoc,
      ι_mapBifunctorDesc, ι_mapBifunctorDesc]
    exact db i j

/-- tensorLift の斉次成分。 -/
@[reassoc (attr := simp)]
lemma ι_tensorLift {P Q T : Complex A}
    (b : ∀ (i j n : ℤ), i + j = n → (P.X i ⊗ Q.X j ⟶ T.X n)) (db)
    (i j n : ℤ) (h : i + j = n) :
    ιTensorObj P Q i j n h ≫ (tensorLift b db).f n = b i j n h :=
  by
    dsimp only [tensorLift]
    exact ι_mapBifunctorDesc _ i j h

/-- g⊗f を f.comp g へ送る A 線形射。通常の dg 合成の順序。 -/
def compositionComponent (X Y Z : Complex A) (q p n : ℤ) (h : q + p = n) :
    (homComplex A Y Z).X q ⊗ (homComplex A X Y).X p ⟶ (homComplex A X Z).X n :=
  ModuleCat.ofHom (TensorProduct.lift
    { toFun g :=
        { toFun f := f.comp g (by omega)
          map_add' f f' := Cochain.add_comp f f' g _
          map_smul' a f := Cochain.smul_comp a f g _ }
      map_add' g g' := by apply LinearMap.ext; intro f; exact Cochain.comp_add f g g' (by omega)
      map_smul' a g := by apply LinearMap.ext; intro f; exact Cochain.comp_smul f a g (by omega) })

/-- 純粋 tensor における通常順合成。 -/
@[simp]
lemma compositionComponent_apply (X Y Z : Complex A) (q p n : ℤ) (h : q + p = n)
    (g : Homogeneous Y Z q) (f : Homogeneous X Y p) :
    compositionComponent X Y Z q p n h (g ⊗ₜ[A] f) = f.comp g (by omega) := rfl

/-- 通常順合成の chain map。Leibniz の符号が tensor の第一因子 q と一致する。 -/
def composition (X Y Z : Complex A) :
    homComplex A Y Z ⊗ homComplex A X Y ⟶ homComplex A X Z :=
  tensorLift (compositionComponent X Y Z) (by
    intro q p
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    apply LinearMap.ext
    intro g
    apply LinearMap.ext
    intro f
    change δ (q + p) (q + p + 1) (f.comp g (by omega)) =
      f.comp (δ q (q + 1) g) (by omega) +
      q.negOnePow • (δ p (p + 1) f).comp g (by omega)
    exact differential_comp f g (by omega))

/-- 豊穣順 f⊗g の合成は signed braiding の後に通常順合成する。 -/
def enrichedComposition (X Y Z : Complex A) :
    homComplex A X Y ⊗ homComplex A Y Z ⟶ homComplex A X Z :=
  (SerrePositivity.cochainTensorSymmetry _ _).hom ≫ composition X Y Z

/-- 豊穣順と通常順の Koszul 比較。交換同型の既存成分公式を用いる。 -/
lemma enrichedComposition_component (X Y Z : Complex A) (p q n : ℤ) (h : p + q = n) :
    ιTensorObj (homComplex A X Y) (homComplex A Y Z) p q n h ≫
      (enrichedComposition X Y Z).f n =
    (p * q).negOnePow • ((β_ ((homComplex A X Y).X p) ((homComplex A Y Z).X q)).hom ≫
      compositionComponent X Y Z q p n (by omega)) := by
  dsimp only [enrichedComposition, HomologicalComplex.comp_f]
  rw [← Category.assoc, SerrePositivity.ιTensorObj_cochainTensorSymmetry,
    Linear.units_smul_comp, Category.assoc]
  dsimp only [composition]
  rw [ι_tensorLift]

/-- 閉次数零では豊穣順の合成に符号は付かない。 -/
lemma enrichedComposition_zero (X Y Z : Complex A) :
    ιTensorObj (homComplex A X Y) (homComplex A Y Z) 0 0 0 rfl ≫
      (enrichedComposition X Y Z).f 0 =
    (β_ ((homComplex A X Y).X 0) ((homComplex A Y Z).X 0)).hom ≫
      compositionComponent X Y Z 0 0 0 rfl := by
  simpa using enrichedComposition_component X Y Z 0 0 0 rfl
end SerrePositivity.DifferentialGraded
