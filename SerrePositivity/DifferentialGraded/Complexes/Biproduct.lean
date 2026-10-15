module
public import SerrePositivity.DifferentialGraded.Complexes.Zero
public import SerrePositivity.PerfectComplex.CochainBiproduct
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Preadditive.Biproducts

/-! # 二項直和の全次数対角 Hom -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A] {K P Q R S : Complex A}

/-- 二つの Hom chain map を対角作用として二項直和へ移す。 -/
def biprodHomMap (a : K ⟶ homComplex A P R) (b : K ⟶ homComplex A Q S) :
    K ⟶ homComplex A (P ⊞ Q) (R ⊞ S) :=
  a ≫ homPrecompose biprod.fst R ≫ homPostcompose (P ⊞ Q) biprod.inl +
    b ≫ homPrecompose biprod.snd S ≫ homPostcompose (P ⊞ Q) biprod.inr

/-- 共通パラメータの前合成は対角 Hom と可換。 -/
lemma biprodHomMap_precomp {L : Complex A} (f : L ⟶ K)
    (a : K ⟶ homComplex A P R) (b : K ⟶ homComplex A Q S) :
    f ≫ biprodHomMap a b = biprodHomMap (f ≫ a) (f ≫ b) := by
  simp only [biprodHomMap, Preadditive.comp_add, Category.assoc]

/-- 対角 Hom の全斉次成分。 -/
lemma biprodHomMap_v (a : K ⟶ homComplex A P R) (b : K ⟶ homComplex A Q S)
    (p i j : ℤ) (hij : i + p = j) (t : K.X p) :
    ((biprodHomMap a b).f p t).v i j hij =
      (biprod.fst : P ⊞ Q ⟶ P).f i ≫ (a.f p t).v i j hij ≫ (biprod.inl : R ⟶ R ⊞ S).f j +
        (biprod.snd : P ⊞ Q ⟶ Q).f i ≫ (b.f p t).v i j hij ≫ (biprod.inr : S ⟶ R ⊞ S).f j := by
  simp only [biprodHomMap, HomologicalComplex.add_f_apply, HomologicalComplex.comp_f,
    homPrecompose, homPostcompose]
  change (((Cochain.ofHom biprod.fst).comp (a.f p t) (zero_add p)).comp
    (Cochain.ofHom biprod.inl) (add_zero p) +
    ((Cochain.ofHom biprod.snd).comp (b.f p t) (zero_add p)).comp
      (Cochain.ofHom biprod.inr) (add_zero p)).v i j hij = _
  simp only [Cochain.add_v, Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v,
    Cochain.ofHom_v, Category.assoc]

/-- 直和へ向かう全次数 Hom は二つの射影後の成分で判定できる。 -/
lemma homComplex_biprod_ext {f g : K ⟶ homComplex A P (Q ⊞ R)}
    (hf : f ≫ homPostcompose P biprod.fst = g ≫ homPostcompose P biprod.fst)
    (hg : f ≫ homPostcompose P biprod.snd = g ≫ homPostcompose P biprod.snd) : f = g := by
  apply HomologicalComplex.Hom.ext
  funext p
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro t
  apply Cochain.ext
  intro i j hij
  have hf' := congrArg (fun l => (l.f p t).v i j hij) hf
  have hg' := congrArg (fun l => (l.f p t).v i j hij) hg
  change ((f.f p t).comp (Cochain.ofHom biprod.fst) (add_zero p)).v i j hij =
    ((g.f p t).comp (Cochain.ofHom biprod.fst) (add_zero p)).v i j hij at hf'
  change ((f.f p t).comp (Cochain.ofHom biprod.snd) (add_zero p)).v i j hij =
    ((g.f p t).comp (Cochain.ofHom biprod.snd) (add_zero p)).v i j hij at hg'
  simp only [Cochain.comp_zero_cochain_v, Cochain.ofHom_v] at hf' hg'
  have ht := congrArg (fun l : Q ⊞ R ⟶ Q ⊞ R => l.f j) (biprod.total (X := Q) (Y := R))
  simp only [HomologicalComplex.add_f_apply, HomologicalComplex.comp_f,
    HomologicalComplex.id_f] at ht
  calc
    _ = (f.f p t).v i j hij ≫ ((biprod.fst : Q ⊞ R ⟶ Q).f j ≫ (biprod.inl : Q ⟶ Q ⊞ R).f j +
        (biprod.snd : Q ⊞ R ⟶ R).f j ≫ (biprod.inr : R ⟶ Q ⊞ R).f j) := by rw [ht, Category.comp_id]
    _ = (g.f p t).v i j hij ≫ ((biprod.fst : Q ⊞ R ⟶ Q).f j ≫ (biprod.inl : Q ⟶ Q ⊞ R).f j +
        (biprod.snd : Q ⊞ R ⟶ R).f j ≫ (biprod.inr : R ⟶ Q ⊞ R).f j) := by
      simp only [Preadditive.comp_add, ← Category.assoc]
      rw [hf', hg']
    _ = _ := by rw [ht, Category.comp_id]

/-- 対角 Hom は閉単位を保存する。 -/
lemma biprodHomMap_identity (P Q : Complex A) :
    biprodHomMap (identity P) (identity Q) = identity (P ⊞ Q) := by
  apply (unitCycleEquiv _).injective
  apply Subtype.ext
  change (cycleFromUnit _ (biprodHomMap (identity P) (identity Q))).val =
    (cycleFromUnit _ (identity (P ⊞ Q))).val
  have hP : (cycleFromUnit _ (identity P)).val = Cochain.ofHom (𝟙 P) := by
    simp only [identity, cycleFromUnit_unitFromCycle]
  have hQ : (cycleFromUnit _ (identity Q)).val = Cochain.ofHom (𝟙 Q) := by
    simp only [identity, cycleFromUnit_unitFromCycle]
  have hPQ : (cycleFromUnit _ (identity (P ⊞ Q))).val = Cochain.ofHom (𝟙 (P ⊞ Q)) := by
    simp only [identity, cycleFromUnit_unitFromCycle]
  rw [hPQ]
  apply Cochain.ext₀
  intro i
  change ((biprodHomMap (identity P) (identity Q)).f 0 _).v i i (add_zero i) = _
  rw [biprodHomMap_v]
  change (biprod.fst : P ⊞ Q ⟶ P).f i ≫
      (cycleFromUnit _ (identity P)).val.v i i (add_zero i) ≫
        (biprod.inl : P ⟶ P ⊞ Q).f i +
    (biprod.snd : P ⊞ Q ⟶ Q).f i ≫
      (cycleFromUnit _ (identity Q)).val.v i i (add_zero i) ≫
        (biprod.inr : Q ⟶ P ⊞ Q).f i = _
  rw [hP, hQ]
  simp only [Cochain.ofHom_v, HomologicalComplex.id_f, Category.id_comp]
  exact congrArg (fun l : P ⊞ Q ⟶ P ⊞ Q => l.f i) (biprod.total (X := P) (Y := Q))

/-- 対角 Hom の射影後の全次数成分。 -/
lemma biprodHomMap_fst (a : K ⟶ homComplex A P R) (b : K ⟶ homComplex A Q S) :
    biprodHomMap a b ≫ homPostcompose (P ⊞ Q) biprod.fst =
      a ≫ homPrecompose biprod.fst R := by
  apply HomologicalComplex.Hom.ext
  funext p
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro t
  apply Cochain.ext
  intro i j hij
  change (((biprodHomMap a b).f p t).comp (Cochain.ofHom biprod.fst)
    (add_zero p)).v i j hij =
      ((Cochain.ofHom biprod.fst).comp (a.f p t) (zero_add p)).v i j hij
  rw [Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v,
    Cochain.ofHom_v, Cochain.ofHom_v]
  change ((biprodHomMap a b).f p t).v i j hij ≫
    (biprod.fst : R ⊞ S ⟶ R).f j =
      (biprod.fst : P ⊞ Q ⟶ P).f i ≫ (a.f p t).v i j hij
  rw [biprodHomMap_v, Preadditive.add_comp]
  have h₁ := congrArg (fun l : R ⟶ R => l.f j) (biprod.inl_fst (X := R) (Y := S))
  have h₂ := congrArg (fun l : S ⟶ R => l.f j) (biprod.inr_fst (X := R) (Y := S))
  simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f,
    HomologicalComplex.zero_f] at h₁ h₂
  simp only [Category.assoc, h₁, h₂, Category.comp_id, comp_zero, add_zero]

/-- 対角 Hom の第二射影後の全次数成分。 -/
lemma biprodHomMap_snd (a : K ⟶ homComplex A P R) (b : K ⟶ homComplex A Q S) :
    biprodHomMap a b ≫ homPostcompose (P ⊞ Q) biprod.snd =
      b ≫ homPrecompose biprod.snd S := by
  apply HomologicalComplex.Hom.ext
  funext p
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro t
  apply Cochain.ext
  intro i j hij
  change (((biprodHomMap a b).f p t).comp (Cochain.ofHom biprod.snd)
    (add_zero p)).v i j hij =
      ((Cochain.ofHom biprod.snd).comp (b.f p t) (zero_add p)).v i j hij
  rw [Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v,
    Cochain.ofHom_v, Cochain.ofHom_v]
  change ((biprodHomMap a b).f p t).v i j hij ≫
    (biprod.snd : R ⊞ S ⟶ S).f j =
      (biprod.snd : P ⊞ Q ⟶ Q).f i ≫ (b.f p t).v i j hij
  rw [biprodHomMap_v, Preadditive.add_comp]
  have h₁ := congrArg (fun l : R ⟶ S => l.f j) (biprod.inl_snd (X := R) (Y := S))
  have h₂ := congrArg (fun l : S ⟶ S => l.f j) (biprod.inr_snd (X := R) (Y := S))
  simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f,
    HomologicalComplex.zero_f] at h₁ h₂
  simp only [Category.assoc, h₁, h₂, Category.comp_id, comp_zero, zero_add]

/-- 第一包含前の対角 Hom は第一成分だけになる。 -/
lemma biprodHomMap_inl (a : K ⟶ homComplex A P R) (b : K ⟶ homComplex A Q S) :
    biprodHomMap a b ≫ homPrecompose biprod.inl (R ⊞ S) =
      a ≫ homPostcompose P biprod.inl := by
  apply HomologicalComplex.Hom.ext
  funext p
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro t
  apply Cochain.ext
  intro i j hij
  change ((Cochain.ofHom biprod.inl).comp ((biprodHomMap a b).f p t)
    (zero_add p)).v i j hij =
      ((a.f p t).comp (Cochain.ofHom biprod.inl) (add_zero p)).v i j hij
  rw [Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v,
    Cochain.ofHom_v, Cochain.ofHom_v, biprodHomMap_v]
  have h₁ := congrArg (fun l : P ⟶ P => l.f i) (biprod.inl_fst (X := P) (Y := Q))
  have h₂ := congrArg (fun l : P ⟶ Q => l.f i) (biprod.inl_snd (X := P) (Y := Q))
  simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f,
    HomologicalComplex.zero_f] at h₁ h₂
  simp only [Preadditive.comp_add, ← Category.assoc, h₁, h₂,
    Category.id_comp, zero_comp, add_zero]

/-- 第二包含前の対角 Hom は第二成分だけになる。 -/
lemma biprodHomMap_inr (a : K ⟶ homComplex A P R) (b : K ⟶ homComplex A Q S) :
    biprodHomMap a b ≫ homPrecompose biprod.inr (R ⊞ S) =
      b ≫ homPostcompose Q biprod.inr := by
  apply HomologicalComplex.Hom.ext
  funext p
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro t
  apply Cochain.ext
  intro i j hij
  change ((Cochain.ofHom biprod.inr).comp ((biprodHomMap a b).f p t)
    (zero_add p)).v i j hij =
      ((b.f p t).comp (Cochain.ofHom biprod.inr) (add_zero p)).v i j hij
  rw [Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v,
    Cochain.ofHom_v, Cochain.ofHom_v, biprodHomMap_v]
  have h₁ := congrArg (fun l : Q ⟶ P => l.f i) (biprod.inr_fst (X := P) (Y := Q))
  have h₂ := congrArg (fun l : Q ⟶ Q => l.f i) (biprod.inr_snd (X := P) (Y := Q))
  simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f,
    HomologicalComplex.zero_f] at h₁ h₂
  simp only [Preadditive.comp_add, ← Category.assoc, h₁, h₂,
    Category.id_comp, zero_comp, zero_add]

/-- 対角 Hom は Koszul 符号付き豊穣合成を保存する。 -/
lemma biprodHomMap_comp {L T U : Complex A}
    (a : K ⟶ homComplex A P R) (b : K ⟶ homComplex A Q S)
    (c : L ⟶ homComplex A R T) (d : L ⟶ homComplex A S U) :
    (biprodHomMap a b ⊗ₘ biprodHomMap c d) ≫ enrichedComposition _ _ _ =
      biprodHomMap ((a ⊗ₘ c) ≫ enrichedComposition _ _ _)
        ((b ⊗ₘ d) ≫ enrichedComposition _ _ _) := by
  apply tensorHom_ext
  intro p q n hn
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro t v
  change (enrichedComposition _ _ _).f n
    (((biprodHomMap a b) ⊗ₘ (biprodHomMap c d)).f n
      (ιTensorObj K L p q n hn (t ⊗ₜ[A] v))) = _
  rw [tensorMap_apply, enrichedComposition_apply]
  apply Cochain.ext
  intro i j hij
  rw [Cochain.units_smul_v,
    Cochain.comp_v _ _ hn i (i + p) j rfl (by omega), biprodHomMap_v,
    biprodHomMap_v]
  conv_rhs =>
    change ((biprodHomMap ((a ⊗ₘ c) ≫ enrichedComposition P R T)
      ((b ⊗ₘ d) ≫ enrichedComposition Q S U)).f n
        (ιTensorObj K L p q n hn (t ⊗ₜ[A] v))).v i j hij
  rw [biprodHomMap_v]
  change (p * q).negOnePow •
    (((biprod.fst : P ⊞ Q ⟶ P).f i ≫ (a.f p t).v i (i + p) rfl ≫
        (biprod.inl : R ⟶ R ⊞ S).f (i + p) +
      (biprod.snd : P ⊞ Q ⟶ Q).f i ≫ (b.f p t).v i (i + p) rfl ≫
        (biprod.inr : S ⟶ R ⊞ S).f (i + p)) ≫
      ((biprod.fst : R ⊞ S ⟶ R).f (i + p) ≫ (c.f q v).v (i + p) j (by omega) ≫
          (biprod.inl : T ⟶ T ⊞ U).f j +
        (biprod.snd : R ⊞ S ⟶ S).f (i + p) ≫ (d.f q v).v (i + p) j (by omega) ≫
          (biprod.inr : U ⟶ T ⊞ U).f j)) =
    (biprod.fst : P ⊞ Q ⟶ P).f i ≫
      ((enrichedComposition P R T).f n
        ((a ⊗ₘ c).f n (ιTensorObj K L p q n hn (t ⊗ₜ[A] v)))).v i j hij ≫
        (biprod.inl : T ⟶ T ⊞ U).f j +
      (biprod.snd : P ⊞ Q ⟶ Q).f i ≫
        ((enrichedComposition Q S U).f n
          ((b ⊗ₘ d).f n (ιTensorObj K L p q n hn (t ⊗ₜ[A] v)))).v i j hij ≫
          (biprod.inr : U ⟶ T ⊞ U).f j
  rw [tensorMap_apply, tensorMap_apply, enrichedComposition_apply,
    enrichedComposition_apply]
  rw [Cochain.units_smul_v, Cochain.units_smul_v,
    Cochain.comp_v _ _ hn i (i + p) j rfl (by omega),
    Cochain.comp_v _ _ hn i (i + p) j rfl (by omega)]
  have h₁ := congrArg (fun l : R ⟶ R => l.f (i + p)) (biprod.inl_fst (X := R) (Y := S))
  have h₂ := congrArg (fun l : R ⟶ S => l.f (i + p)) (biprod.inl_snd (X := R) (Y := S))
  have h₃ := congrArg (fun l : S ⟶ R => l.f (i + p)) (biprod.inr_fst (X := R) (Y := S))
  have h₄ := congrArg (fun l : S ⟶ S => l.f (i + p)) (biprod.inr_snd (X := R) (Y := S))
  simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f,
    HomologicalComplex.zero_f] at h₁ h₂ h₃ h₄
  simp only [Preadditive.add_comp, Preadditive.comp_add, Category.assoc]
  simp only [← Category.assoc, h₁, h₂, h₃, h₄, Category.comp_id, comp_zero, zero_comp,
    add_zero, zero_add]
  simp only [smul_add, Units.smul_def, Preadditive.zsmul_comp, Preadditive.comp_zsmul,
    Category.assoc]
end SerrePositivity.DifferentialGraded
