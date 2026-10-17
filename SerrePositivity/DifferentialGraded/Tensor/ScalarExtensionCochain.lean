module
public import SerrePositivity.DifferentialGraded.Tensor.ScalarExtensionHom
public import SerrePositivity.DifferentialGraded.Complexes.TensorRightHom

/-! # 係数変更と閉性を仮定しない斉次 cochain

path の ε 消去には次数 +1 の cochain が必要なため、chain map に限定しない。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded.ScalarExtension
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')

/-- 各斉次成分での係数変更の可換四角形。 -/
def CochainSquare {P Q : Complex A} {P' Q' : Complex A'} {p : ℤ}
    (a : (extension φ).obj P ⟶ P') (b : (extension φ).obj Q ⟶ Q')
    (f : Cochain P Q p) (g : Cochain P' Q' p) : Prop :=
  ∀ i j (h : i + p = j), (ModuleCat.extendScalars φ).map (f.v i j h) ≫ b.f j =
    a.f i ≫ g.v i j h

lemma cochainSquare_ofHom {P Q : Complex A} {P' Q' : Complex A'}
    (a : (extension φ).obj P ⟶ P') (b : (extension φ).obj Q ⟶ Q')
    (f : P ⟶ Q) (g : P' ⟶ Q') (h : (extension φ).map f ≫ b = a ≫ g) :
    CochainSquare φ a b (Cochain.ofHom f) (Cochain.ofHom g) := by
  intro i j hij
  have hj : j = i := by omega
  cases hj
  rw [Cochain.ofHom_v, Cochain.ofHom_v]
  convert congrArg (fun z => z.f i) h using 1 <;> rfl

lemma cochainSquare_comp {P Q R : Complex A} {P' Q' R' : Complex A'}
    {a : (extension φ).obj P ⟶ P'} {b : (extension φ).obj Q ⟶ Q'}
    {c : (extension φ).obj R ⟶ R'} {p q n : ℤ}
    {f : Cochain P Q p} {g : Cochain Q R q} {f' : Cochain P' Q' p} {g' : Cochain Q' R' q}
    (hf : CochainSquare φ a b f f') (hg : CochainSquare φ b c g g') (hn : p + q = n) :
    CochainSquare φ a c (f.comp g hn) (f'.comp g' hn) := by
  intro i j hij
  rw [Cochain.comp_v f g hn i (i + p) j rfl (by omega),
    Cochain.comp_v f' g' hn i (i + p) j rfl (by omega),
    CategoryTheory.Functor.map_comp, Category.assoc, hg, ← Category.assoc, hf, Category.assoc]

set_option maxHeartbeats 800000 in
-- 係数拡大した二重 tensor の全次数生成元で Koszul 符号を照合する。
lemma cochainSquare_tensorLeft {K P Q : Complex A} {K' P' Q' : Complex A'}
    (k : (extension φ).obj K ⟶ K')
    {a : (extension φ).obj P ⟶ P'} {b : (extension φ).obj Q ⟶ Q'} {p : ℤ}
    {f : Cochain P Q p} {g : Cochain P' Q' p} (hf : CochainSquare φ a b f g) :
    CochainSquare φ ((tensorIso φ K P).hom ≫ (k ⊗ₘ a))
      ((tensorIso φ K Q).hom ≫ (k ⊗ₘ b))
      ((tensorLeftHom K P Q).f p f) ((tensorLeftHom K' P' Q').f p g) := by
  let := φ.toAlgebra
  intro s n hsn
  apply cochainTensorBaseChange_hom_ext φ K P
  intro i j hij
  apply ((ModuleCat.extendRestrictScalarsAdj φ).homEquiv _ _).injective
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x y
  change (k ⊗ₘ b).f n ((tensorIso φ K Q).hom.f n
    ((ModuleCat.extendScalars φ).map (((tensorLeftHom K P Q).f p f).v s n hsn)
      ((1 : A') ⊗ₜ[A] ιTensorObj K P i j s hij (x ⊗ₜ[A] y)))) =
    ((tensorLeftHom K' P' Q').f p g).v s n hsn
      ((k ⊗ₘ a).f s ((tensorIso φ K P).hom.f s
        ((1 : A') ⊗ₜ[A] ιTensorObj K P i j s hij (x ⊗ₜ[A] y))))
  erw [ModuleCat.ExtendScalars.map_tmul φ, tensorLeftHom_apply]
  simp only [Units.smul_def, TensorProduct.tmul_smul, map_zsmul]
  erw [cochainTensorBaseChangeIso_apply_ι φ K Q i (j + p) n (by omega)]
  erw [cochainTensorBaseChangeIso_apply_ι φ K P i j s hij]
  erw [tensorMap_apply, tensorMap_apply, tensorLeftHom_apply]
  have hh := congrArg (fun z => z ((1 : A') ⊗ₜ[A] y)) (hf j (j + p) rfl)
  change b.f (j + p) ((1 : A') ⊗ₜ[A] f.v j (j + p) rfl y) =
    g.v j (j + p) rfl (a.f j ((1 : A') ⊗ₜ[A] y)) at hh
  rw [hh]
  rfl

set_option maxHeartbeats 800000 in
-- 右 tensor には追加の符号がなく、同じ純粋生成元で照合できる。
lemma cochainSquare_tensorRight {K P Q : Complex A} {K' P' Q' : Complex A'}
    (k : (extension φ).obj K ⟶ K')
    {a : (extension φ).obj P ⟶ P'} {b : (extension φ).obj Q ⟶ Q'} {p : ℤ}
    {f : Cochain P Q p} {g : Cochain P' Q' p} (hf : CochainSquare φ a b f g) :
    CochainSquare φ ((tensorIso φ P K).hom ≫ (a ⊗ₘ k))
      ((tensorIso φ Q K).hom ≫ (b ⊗ₘ k))
      ((tensorRightHom K P Q).f p f) ((tensorRightHom K' P' Q').f p g) := by
  let := φ.toAlgebra
  intro s n hsn
  apply cochainTensorBaseChange_hom_ext φ P K
  intro i j hij
  apply ((ModuleCat.extendRestrictScalarsAdj φ).homEquiv _ _).injective
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x y
  change (b ⊗ₘ k).f n ((tensorIso φ Q K).hom.f n
    ((ModuleCat.extendScalars φ).map (((tensorRightHom K P Q).f p f).v s n hsn)
      ((1 : A') ⊗ₜ[A] ιTensorObj P K i j s hij (x ⊗ₜ[A] y)))) =
    ((tensorRightHom K' P' Q').f p g).v s n hsn
      ((a ⊗ₘ k).f s ((tensorIso φ P K).hom.f s
        ((1 : A') ⊗ₜ[A] ιTensorObj P K i j s hij (x ⊗ₜ[A] y))))
  erw [ModuleCat.ExtendScalars.map_tmul φ, tensorRightHom_apply]
  erw [cochainTensorBaseChangeIso_apply_ι φ Q K (i + p) j n (by omega)]
  erw [cochainTensorBaseChangeIso_apply_ι φ P K i j s hij]
  erw [tensorMap_apply, tensorMap_apply, tensorRightHom_apply]
  have hh := congrArg (fun z => z ((1 : A') ⊗ₜ[A] x)) (hf i (i + p) rfl)
  change b.f (i + p) ((1 : A') ⊗ₜ[A] f.v i (i + p) rfl x) =
    g.v i (i + p) rfl (a.f i ((1 : A') ⊗ₜ[A] x)) at hh
  rw [hh]

lemma cochainSquare_zero {P Q : Complex A} {P' Q' : Complex A'} {p : ℤ}
    (a : (extension φ).obj P ⟶ P') (b : (extension φ).obj Q ⟶ Q') :
    CochainSquare φ a b (0 : Cochain P Q p) 0 := by
  intro i j h
  simp only [Cochain.zero_v, Functor.map_zero, Limits.zero_comp, Limits.comp_zero]

lemma cochainSquare_add {P Q : Complex A} {P' Q' : Complex A'} {p : ℤ}
    {a : (extension φ).obj P ⟶ P'} {b : (extension φ).obj Q ⟶ Q'}
    {f g : Cochain P Q p} {f' g' : Cochain P' Q' p}
    (hf : CochainSquare φ a b f f') (hg : CochainSquare φ a b g g') :
    CochainSquare φ a b (f + g) (f' + g') := by
  intro i j h
  simp only [Cochain.add_v, Functor.map_add, Preadditive.add_comp, Preadditive.comp_add,
    hf i j h, hg i j h]

end SerrePositivity.DifferentialGraded.ScalarExtension
