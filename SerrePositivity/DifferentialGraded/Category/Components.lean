module
public import SerrePositivity.DifferentialGraded.Category.Basic
public import SerrePositivity.DifferentialGraded.Complexes.CompositionLaws
public import SerrePositivity.DifferentialGraded.Complexes.UnitTensor

/-! # dg 圏の斉次成分と通常順合成 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits MonoidalCategory HomologicalComplex
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- dg Hom の次数 n の元。Hom 加群の宇宙は u。 -/
abbrev GradedHom (x y : D) (n : ℤ) := (x ⟶[Complex A] y).X n

/-- 微分はコチェイン次数 +1。 -/
abbrev differential {x y : D} {n : ℤ} (f : GradedHom A x y n) : GradedHom A x y (n + 1) :=
  (x ⟶[Complex A] y).d n (n + 1) f

/-- 豊穣順の斉次成分。第一引数が先に作用する f。 -/
def forward {x y z : D} {p q n : ℤ} (f : GradedHom A x y p) (g : GradedHom A y z q)
    (h : p + q = n) : GradedHom A x z n :=
  (eComp (Complex A) x y z).f n
    (ιTensorObj (x ⟶[Complex A] y) (y ⟶[Complex A] z) p q n h (f ⊗ₜ[A] g))

/-- 通常順 μ(g,f)=g∘f。豊穣順へ Koszul 符号を掛けて定義する。 -/
def compose {x y z : D} {p q n : ℤ} (g : GradedHom A y z q) (f : GradedHom A x y p)
    (h : p + q = n) : GradedHom A x z n := (p * q).negOnePow • forward A f g h

/-- 豊穣順と通常順の Koszul 比較。二度の交換の符号は消える。 -/
lemma forward_eq_signed_compose {x y z : D} {p q n : ℤ}
    (f : GradedHom A x y p) (g : GradedHom A y z q) (h : p + q = n) :
    forward A f g h = (p * q).negOnePow • compose A g f h := by
  simp [compose, smul_smul]

/-- 豊穣順の微分は tensor 第一因子 p による Leibniz 則。 -/
lemma differential_forward {x y z : D} {p q n : ℤ}
    (f : GradedHom A x y p) (g : GradedHom A y z q) (h : p + q = n) :
    differential A (forward A f g h) =
      forward A (differential A f) g (by omega) +
      p.negOnePow • forward A f (differential A g) (by omega) := by
  subst n
  have hd := SerrePositivity.cochainTensorι_d (x ⟶[Complex A] y) (y ⟶[Complex A] z) p q
  have hc := (eComp (Complex A) x y z).comm (p + q) (p + q + 1)
  change (eComp (Complex A) x y z).f (p + q) ≫ (x ⟶[Complex A] z).d _ _ =
    (SerrePositivity.cochainTensor (x ⟶[Complex A] y) (y ⟶[Complex A] z)).d _ _ ≫
      (eComp (Complex A) x y z).f (p + q + 1) at hc
  have he := congrArg (fun l => l ≫ (eComp (Complex A) x y z).f (p + q + 1)) hd
  rw [Category.assoc, ← hc] at he
  rw [Preadditive.add_comp, Linear.units_smul_comp] at he
  apply_fun (fun l => l.hom (f ⊗ₜ[A] g)) at he
  change differential A (forward A f g rfl) = _ at he
  change differential A (forward A f g rfl) =
    forward A (n := p + q + 1) (differential A f) g (by omega) +
    p.negOnePow • forward A (n := p + q + 1) f (differential A g) (by omega) at he
  exact he

/-- 通常順の微分。符号は g の次数 q。
整数の符号等式から得られ、標数二の環でも同じ証明が使える。 -/
lemma differential_compose {x y z : D} {p q n : ℤ}
    (g : GradedHom A y z q) (f : GradedHom A x y p) (h : p + q = n) :
    differential A (compose A g f h) =
      compose A (differential A g) f (by omega) +
      q.negOnePow • compose A g (differential A f) (by omega) := by
  unfold compose
  change (x ⟶[Complex A] z).d n (n + 1) ((p * q).negOnePow • forward A f g h) = _
  simp only [Units.smul_def, map_zsmul]
  change (p * q).negOnePow • differential A (forward A f g h) =
    (p * (q + 1)).negOnePow • forward A f (differential A g) (by omega) +
    q.negOnePow • ((p + 1) * q).negOnePow • forward A (differential A f) g (by omega)
  rw [differential_forward]
  simp only [smul_add, smul_smul, ← Int.negOnePow_add]
  have h₁ : p * q + p = p * (q + 1) := by ring
  have h₂ : p * q = q + (p + 1) * q - 2 * q := by ring
  rw [h₁, h₂]
  simp only [Int.negOnePow_sub, Int.negOnePow_two_mul, mul_one]
  abel

/-- 豊穣合成の結合則を斉次元へ降ろす。 -/
lemma forward_assoc {w x y z : D} {p q r n : ℤ}
    (f : GradedHom A w x p) (g : GradedHom A x y q) (h : GradedHom A y z r)
    (hn : p + q + r = n) :
    forward A (forward A f g rfl) h hn =
      forward A f (forward A g h rfl) (by omega) := by
  have he := e_assoc' (Complex A) w x y z
  have he' := congrArg (fun l => l.f n) he
  have hi := congrArg (fun l =>
    (ιTensorObj (w ⟶[Complex A] x) (x ⟶[Complex A] y) p q (p + q) rfl ▷
        (y ⟶[Complex A] z).X r) ≫
      ιTensorObj ((w ⟶[Complex A] x) ⊗ (x ⟶[Complex A] y))
        (y ⟶[Complex A] z) (p + q) r n hn ≫ l) he'
  simp only [HomologicalComplex.comp_f] at hi
  rw [ι_associator_assoc, ι_whiskerLeft_assoc, ι_whiskerRight_assoc] at hi
  have hv := congrArg (fun l => l.hom (f ⊗ₜ[A] g ⊗ₜ[A] h)) hi
  exact hv.symm

/-- 通常順の結合則。Koszul 符号の指数は両側で同じ。 -/
lemma compose_assoc {w x y z : D} {p q r n : ℤ}
    (f : GradedHom A w x p) (g : GradedHom A x y q) (h : GradedHom A y z r)
    (hn : p + q + r = n) :
    compose A h (compose A g f rfl) hn =
      compose A (compose A h g rfl) f (by omega) := by
  unfold compose forward
  simp only [Units.smul_def, TensorProduct.smul_tmul, TensorProduct.tmul_smul, map_zsmul, smul_smul]
  change (((p + q) * r).negOnePow * (p * q).negOnePow) •
    forward A (forward A f g rfl) h hn =
    ((p * (q + r)).negOnePow * (q * r).negOnePow) •
      forward A f (forward A g h rfl) (by omega)
  rw [forward_assoc]
  simp only [← Int.negOnePow_add]
  congr 1
  congr 1
  ring
/-- dg 単位の閉次数零元。 -/
def unitElement (x : D) : zeroCycles (x ⟶[Complex A] x) :=
  cycleFromUnit _ (eId (Complex A) x)

/-- dg 単位は閉じている。 -/
lemma differential_unit (x : D) : differential A (unitElement A x).val = 0 :=
  (unitElement A x).property

/-- 斉次成分上の左単位則。 -/
lemma forward_unit {x y : D} {n : ℤ} (f : GradedHom A x y n) :
    forward A (unitElement A x).val f (zero_add n) = f := by
  have he := e_id_comp (Complex A) x y
  have he' := congrArg (fun l => l.f n) he
  change (leftUnitor' (x ⟶[Complex A] y)).inv n ≫
    (eId (Complex A) x ▷ (x ⟶[Complex A] y)).f n ≫ (eComp (Complex A) x x y).f n = 𝟙 _ at he'
  rw [leftUnitor'_inv, Category.assoc, Category.assoc, ι_whiskerRight_assoc] at he'
  exact congr($(he').hom f)

/-- 斉次成分上の右単位則。 -/
lemma unit_forward {x y : D} {n : ℤ} (f : GradedHom A x y n) :
    forward A f (unitElement A y).val (add_zero n) = f := by
  have he := e_comp_id (Complex A) x y
  have he' := congrArg (fun l => l.f n) he
  change (rightUnitor' (x ⟶[Complex A] y)).inv n ≫
    ((x ⟶[Complex A] y) ◁ eId (Complex A) y).f n ≫ (eComp (Complex A) x y y).f n = 𝟙 _ at he'
  rw [rightUnitor'_inv, Category.assoc, Category.assoc, ι_whiskerLeft_assoc] at he'
  exact congr($(he').hom f)

/-- 通常順の左単位則。 -/
lemma compose_unit {x y : D} {n : ℤ} (f : GradedHom A x y n) :
    compose A f (unitElement A x).val (zero_add n) = f := by
  simp [compose, forward_unit]

/-- 通常順の右単位則。 -/
lemma unit_compose {x y : D} {n : ℤ} (f : GradedHom A x y n) :
    compose A (unitElement A y).val f (add_zero n) = f := by
  simp [compose, unit_forward]
end SerrePositivity.DifferentialGraded
