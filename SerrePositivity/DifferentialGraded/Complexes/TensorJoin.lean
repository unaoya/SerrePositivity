module

public import SerrePositivity.DifferentialGraded.Complexes.Cone
public import SerrePositivity.DifferentialGraded.Complexes.TensorZeroCochain
public import SerrePositivity.DifferentialGraded.Complexes.TensorCoproduct
public import SerrePositivity.DifferentialGraded.Category.Basic
public import Mathlib.Tactic.CategoryTheory.Monoidal.Basic

/-!
# Complexes.TensorJoin

## 概要
22 本の同主題の構成と比較をまとめる。

## 方針
依存順に連結し、宣言と証明を保存する。

## 規約
元ごとの section で variable と option を保持する。private 名の変更は private_renames で明示する。

## 使われ方
DG の土台とその下流から import する。
-/

/-! ## HomogeneousTransport（旧 SerrePositivity/DifferentialGraded/Complexes/HomogeneousTransport.lean） -/

/-! # 斉次写像の始域次数の逆輸送 -/

@[expose] public section HomogeneousTransport
universe u

noncomputable section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A]

lemma homogeneous_XIsoOfEq_inv_comp {P Q : Complex A} {p i i' j : ℤ}
    (f : Homogeneous P Q p) (hi : i = i') (hij : i + p = j) :
    (P.XIsoOfEq hi).inv ≫ f.v i j hij = f.v i' j (by omega) := by
  subst i'
  simp only [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_inv, Category.id_comp]

end SerrePositivity.DifferentialGraded
end

end HomogeneousTransport

/-! ## UnitorCochainNaturality（旧 SerrePositivity/DifferentialGraded/Complexes/UnitorCochainNaturality.lean） -/

/-! # 左unitorと全整数次数cochainの整合性

閉零射の自然性を任意次数のcochainへ拡張する。逆unitorを純tensorで評価して証明する。
-/

@[expose] public section UnitorCochainNaturality
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A]

/-- 逆左unitorは単位の標準生成元を左に置く。 -/
lemma complexLeftUnitor_inv_apply (P : Complex A) (i : ℤ) (x : P.X i) :
    (λ_ P).inv.f i x = ιTensorObj (𝟙_ (Complex A)) P 0 i i (zero_add i)
      ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat.{u} A))).inv (1 : A) ⊗ₜ[A] x) := by
  change (leftUnitor' P).inv i x = _
  rw [leftUnitor'_inv]
  rfl

/-- 左unitorは標準単位生成元を除く。 -/
lemma leftUnitor_hom_generator (P : Complex A) (i : ℤ) (x : P.X i) :
    (λ_ P).hom.f i (ιTensorObj (𝟙_ (Complex A)) P 0 i i (zero_add i)
      ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat.{u} A))).inv (1 : A) ⊗ₜ[A] x)) = x := by
  rw [← complexLeftUnitor_inv_apply]
  change ((λ_ P).inv ≫ (λ_ P).hom).f i x = x
  rw [Iso.inv_hom_id]
  rfl

/-- 逆左unitorは全次数cochainに関して自然。 -/
lemma leftUnitor_inv_cochain (P Q : Complex A) (p : ℤ) (f : Cochain P Q p) :
    (Cochain.ofHom (λ_ P).inv).comp ((tensorLeftHom (𝟙_ (Complex A)) P Q).f p f)
      (zero_add p) = f.comp (Cochain.ofHom (λ_ Q).inv) (add_zero p) := by
  apply Cochain.ext
  intro i n hn
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rw [cochain_ofHom_comp_apply, cochain_comp_ofHom_apply, complexLeftUnitor_inv_apply,
    tensorLeftHom_apply_of_sum (𝟙_ (Complex A)) P Q p 0 i i n n (zero_add i) hn hn,
    complexLeftUnitor_inv_apply]
  simp only [mul_zero, Int.negOnePow_zero, one_smul]

/-- 左unitorは全次数cochainに関して自然。 -/
lemma leftUnitor_hom_cochain (P Q : Complex A) (p : ℤ) (f : Cochain P Q p) :
    ((tensorLeftHom (𝟙_ (Complex A)) P Q).f p f).comp (Cochain.ofHom (λ_ Q).hom)
      (add_zero p) = (Cochain.ofHom (λ_ P).hom).comp f (zero_add p) := by
  apply Cochain.ext
  intro i n hn
  apply (cancel_epi ((λ_ P).inv.f i)).1
  have h := congrArg (fun z : Cochain P (𝟙_ (Complex A) ⊗ Q) p => z.v i n hn)
    (leftUnitor_inv_cochain P Q p f)
  simp only [Cochain.zero_cochain_comp_v, Cochain.comp_zero_cochain_v, Cochain.ofHom_v] at h ⊢
  have hP : (λ_ P).inv.f i ≫ (λ_ P).hom.f i = 𝟙 _ := by
    rw [← HomologicalComplex.comp_f, Iso.inv_hom_id, HomologicalComplex.id_f]
  have hQ : (λ_ Q).inv.f n ≫ (λ_ Q).hom.f n = 𝟙 _ := by
    rw [← HomologicalComplex.comp_f, Iso.inv_hom_id, HomologicalComplex.id_f]
  rw [← Category.assoc, h, Category.assoc, hQ, Category.comp_id,
    ← Category.assoc, hP, Category.id_comp]

/-- 任意の前方因子を置いた左unitorも全次数cochainと可換する。 -/
lemma leftUnitor_hom_cochain_tensor (K P Q : Complex A) (p : ℤ) (f : Cochain P Q p) :
    ((tensorLeftHom K (𝟙_ (Complex A) ⊗ P) (𝟙_ (Complex A) ⊗ Q)).f p
      ((tensorLeftHom (𝟙_ (Complex A)) P Q).f p f)).comp
      (Cochain.ofHom (K ◁ (λ_ Q).hom)) (add_zero p) =
    (Cochain.ofHom (K ◁ (λ_ P).hom)).comp
      ((tensorLeftHom K P Q).f p f) (zero_add p) := by
  rw [← tensorLeftHom_ofHom K _ _ (λ_ Q).hom,
    ← tensorLeftHom_ofHom K _ _ (λ_ P).hom,
    ← tensorLeftHom_cochain_comp, ← tensorLeftHom_cochain_comp, leftUnitor_hom_cochain]

end SerrePositivity.DifferentialGraded
end

end UnitorCochainNaturality

/-! ## RightUnitorEvaluation（旧 SerrePositivity/DifferentialGraded/Complexes/RightUnitorEvaluation.lean） -/

/-! # 右unitorの単位生成元上の成分 -/

@[expose] public section RightUnitorEvaluation
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A]

lemma complexRightUnitor_inv_apply (P : Complex A) (i : ℤ) (x : P.X i) :
    (ρ_ P).inv.f i x = ιTensorObj P (𝟙_ (Complex A)) i 0 i (add_zero i)
      (x ⊗ₜ[A] (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat.{u} A))).inv (1 : A)) := by
  change (rightUnitor' P).inv i x = _
  rw [rightUnitor'_inv]
  rfl

lemma rightUnitor_hom_generator (P : Complex A) (i : ℤ) (x : P.X i) :
    (ρ_ P).hom.f i (ιTensorObj P (𝟙_ (Complex A)) i 0 i (add_zero i)
      (x ⊗ₜ[A] (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat.{u} A))).inv (1 : A))) = x := by
  rw [← complexRightUnitor_inv_apply]
  change ((ρ_ P).inv ≫ (ρ_ P).hom).f i x = x
  rw [Iso.inv_hom_id]
  rfl

end SerrePositivity.DifferentialGraded
end

end RightUnitorEvaluation

/-! ## UnitSandwichEvaluation（旧 SerrePositivity/DifferentialGraded/Complexes/UnitSandwichEvaluation.lean） -/

/-! # 両側に閉単位射を挿入する操作の純tensor表示 -/

@[expose] public section UnitSandwichEvaluation
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex
variable {A : Type u} [CommRing A]

lemma unitSandwich_apply (H E : Complex A) (e : 𝟙_ (Complex A) ⟶ H)
    (i : ℤ) (x : E.X i) :
    ((λ_ E).inv ≫ (e ⊗ₘ ((ρ_ E).inv ≫ (𝟙 E ⊗ₘ e)))).f i x =
    ιTensorObj H (E ⊗ H) 0 i i (zero_add i)
      (e.f 0 ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat.{u} A))).inv (1 : A)) ⊗ₜ[A]
        ιTensorObj E H i 0 i (add_zero i)
          (x ⊗ₜ[A] e.f 0 ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat.{u} A))).inv (1 : A)))) := by
  rw [chain_comp_apply, complexLeftUnitor_inv_apply, tensorMap_apply,
    chain_comp_apply, complexRightUnitor_inv_apply, tensorMap_apply]
  rfl

end SerrePositivity.DifferentialGraded
end

end UnitSandwichEvaluation

/-! ## CoproductHomologySupport（旧 SerrePositivity/DifferentialGraded/Complexes/CoproductHomologySupport.lean） -/

/-! # 余積の次数零ホモロジー類の有限support表示 -/

@[expose] public section CoproductHomologySupport
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits HomologicalComplex
variable (A : Type u) [CommRing A]

def complexZeroHomologyClassLinearMap (K : Complex A) : zeroCycles K →ₗ[A] K.homology 0 :=
  (complexZeroHomologyQuotientIso A K).hom.hom.comp (Submodule.mkQ _)

lemma complexZeroHomologyClass_surjective (K : Complex A) :
    Function.Surjective (complexZeroHomologyClass A K) := by
  intro z
  obtain ⟨c, hc⟩ := Quotient.exists_rep ((complexZeroHomologyQuotientIso A K).inv z)
  refine ⟨c, ?_⟩
  change (complexZeroHomologyQuotientIso A K).hom (Quotient.mk _ c) = z
  rw [hc, ← ModuleCat.comp_apply, Iso.inv_hom_id, ModuleCat.id_apply]

lemma complexZeroHomologyClass_sum {J : Type*} (K : Complex A) (t : Finset J)
    (c : J → zeroCycles K) :
    complexZeroHomologyClass A K (∑ j ∈ t, c j) = ∑ j ∈ t, complexZeroHomologyClass A K (c j) :=
  map_sum (complexZeroHomologyClassLinearMap A K) c t

/-- 任意の非有界複体族の余積のH⁰は、有限個の成分H⁰の像の和で生成される。 -/
lemma complexCofan_zeroHomology_rep {J : Type u} (F : J → Complex A) (s : Cofan F)
    (hs : IsColimit s) (z : s.pt.homology 0) :
    ∃ (t : Finset J) (c : ∀ j, (F j).homology 0),
      ∑ j ∈ t, homologyMap (s.inj j) 0 (c j) = z := by
  classical
  obtain ⟨a, rfl⟩ := complexZeroHomologyClass_surjective A s.pt z
  obtain ⟨t, c, hc⟩ := complexCofan_cycle_rep A F s hs 0 a
  have h : ∑ j ∈ t, complexMapZeroCycle A (s.inj j) (c j) = a := by
    apply Subtype.ext
    change (zeroCycles s.pt).subtype (∑ j ∈ t, complexMapZeroCycle A (s.inj j) (c j)) = a.val
    rw [map_sum]
    exact hc
  refine ⟨t, fun j => complexZeroHomologyClass A (F j) (c j), ?_⟩
  simp only [complexZeroHomologyClass_naturality]
  rw [← complexZeroHomologyClass_sum, h]

end SerrePositivity.DifferentialGraded
end

end CoproductHomologySupport

/-! ## PrefixTensorCochainPrecomp（旧 SerrePositivity/DifferentialGraded/Complexes/PrefixTensorCochainPrecomp.lean） -/

/-! # 前方二因子を保つcochain持ち上げとchain mapによる前合成

## 概要
前方二因子を保つcochain持ち上げとchain mapによる前合成。

## 方針
既存の全dg自然なHom・作用・chain mapと局所化の計算を再利用する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。dg加群の導来作用・準同値比較の基盤。任意可換環上のMorita・K理論のモデル比較に再利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section PrefixTensorCochainPrecomp
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A]

lemma prefixTensor_cochain_precomp (K E P Q T U V : Complex A) (p : ℤ)
    (m : P ⊗ Q ⟶ T) (f : Cochain T U p) (post : K ⊗ (E ⊗ U) ⟶ V) :
    (Cochain.ofHom (((α_ K (E ⊗ P) Q).hom ≫ K ◁ (α_ E P Q).hom) ≫
      K ◁ (E ◁ m))).comp
      (((tensorLeftHom K (E ⊗ T) (E ⊗ U)).f p ((tensorLeftHom E T U).f p f)).comp
        (Cochain.ofHom post) (add_zero p)) (zero_add p) =
    ((Cochain.ofHom ((α_ K (E ⊗ P) Q).hom ≫ K ◁ (α_ E P Q).hom)).comp
      ((tensorLeftHom K (E ⊗ (P ⊗ Q)) (E ⊗ U)).f p
        ((tensorLeftHom E (P ⊗ Q) U).f p
          ((Cochain.ofHom m).comp f (zero_add p)))) (zero_add p)).comp
      (Cochain.ofHom post) (add_zero p) := by
  rw [tensorLeftHom_cochain_comp, tensorLeftHom_ofHom,
    tensorLeftHom_cochain_comp, tensorLeftHom_ofHom]
  simp only [Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain]

end SerrePositivity.DifferentialGraded
end

end PrefixTensorCochainPrecomp

/-! ## AssociatorCochainNaturality（旧 SerrePositivity/DifferentialGraded/Complexes/AssociatorCochainNaturality.lean） -/

/-! # associatorの第三因子に関する全次数自然性

閉零chain mapに限らず、任意整数次数のcochainについてtensorの括弧変更と可換する。
-/

@[expose] public section AssociatorCochainNaturality
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A]

/-- associatorは第三因子の任意次数cochainと可換する。 -/
lemma associator_hom_cochain_right (P Q R S : Complex A) (p : ℤ) (f : Cochain R S p) :
    ((tensorLeftHom (P ⊗ Q) R S).f p f).comp
      (Cochain.ofHom (α_ P Q S).hom) (add_zero p) =
    (Cochain.ofHom (α_ P Q R).hom).comp
      ((tensorLeftHom P (Q ⊗ R) (Q ⊗ S)).f p
        ((tensorLeftHom Q R S).f p f)) (zero_add p) := by
  apply Cochain.ext
  intro a n hn
  apply SerrePositivity.cochainTensorTriple_hom_ext P Q R a
  intro i j k ha
  apply ModuleCat.hom_ext
  apply TensorProduct.ext_threefold
  intro x y z
  change
    (((tensorLeftHom (P ⊗ Q) R S).f p f).comp
      (Cochain.ofHom (α_ P Q S).hom) (add_zero p)).v a n hn
      (ιTensorObj (P ⊗ Q) R (i + j) k a ha
        (ιTensorObj P Q i j (i + j) rfl (x ⊗ₜ[A] y) ⊗ₜ[A] z)) =
    ((Cochain.ofHom (α_ P Q R).hom).comp
      ((tensorLeftHom P (Q ⊗ R) (Q ⊗ S)).f p
        ((tensorLeftHom Q R S).f p f)) (zero_add p)).v a n hn
      (ιTensorObj (P ⊗ Q) R (i + j) k a ha
        (ιTensorObj P Q i j (i + j) rfl (x ⊗ₜ[A] y) ⊗ₜ[A] z))
  rw [cochain_comp_ofHom_apply, cochain_ofHom_comp_apply,
    tensorLeftHom_apply_of_sum (P ⊗ Q) R S p (i + j) k a (k + p) n ha rfl hn,
    chain_units_smul, associator_apply, associator_apply,
    tensorLeftHom_apply_of_sum P (Q ⊗ R) (Q ⊗ S) p i (j + k) a (j + (k + p)) n
      (by omega) (by omega) hn,
    tensorLeftHom_apply_of_sum Q R S p j k (j + k) (k + p) (j + (k + p))
      rfl rfl (by omega)]
  simp only [Units.smul_def, TensorProduct.tmul_smul, map_zsmul, smul_smul]
  congr 2
  rw [mul_add, Int.negOnePow_add]
  rfl

/-- 逆associatorも第三因子の任意次数cochainと可換する。 -/
lemma associator_inv_cochain_right (P Q R S : Complex A) (p : ℤ) (f : Cochain R S p) :
    ((tensorLeftHom P (Q ⊗ R) (Q ⊗ S)).f p
      ((tensorLeftHom Q R S).f p f)).comp
      (Cochain.ofHom (α_ P Q S).inv) (add_zero p) =
    (Cochain.ofHom (α_ P Q R).inv).comp
      ((tensorLeftHom (P ⊗ Q) R S).f p f) (zero_add p) := by
  apply Cochain.ext
  intro i n hn
  apply (cancel_epi ((α_ P Q R).hom.f i)).1
  have h := congrArg (fun z : Cochain ((P ⊗ Q) ⊗ R) (P ⊗ (Q ⊗ S)) p => z.v i n hn)
    (associator_hom_cochain_right P Q R S p f)
  simp only [Cochain.zero_cochain_comp_v, Cochain.comp_zero_cochain_v, Cochain.ofHom_v] at h ⊢
  have hR : (α_ P Q R).hom.f i ≫ (α_ P Q R).inv.f i = 𝟙 _ := by
    rw [← HomologicalComplex.comp_f, Iso.hom_inv_id, HomologicalComplex.id_f]
  have hS : (α_ P Q S).hom.f n ≫ (α_ P Q S).inv.f n = 𝟙 _ := by
    rw [← HomologicalComplex.comp_f, Iso.hom_inv_id, HomologicalComplex.id_f]
  rw [← Category.assoc, ← h, Category.assoc, hS, Category.comp_id,
    ← Category.assoc, hR, Category.id_comp]

/-- 左因子のchain mapに対するtensorの自然性を、任意次数のcochainに取り出す。 -/
lemma tensorLeftHom_cochain_naturality {K L : Complex A} (c : K ⟶ L)
    (P Q : Complex A) (p : ℤ) (f : Cochain P Q p) :
    ((tensorLeftHom K P Q).f p f).comp (Cochain.ofHom (c ▷ Q)) (add_zero p) =
    (Cochain.ofHom (c ▷ P)).comp ((tensorLeftHom L P Q).f p f) (zero_add p) := by
  have h := congrArg (fun t : homComplex A P Q ⟶ homComplex A (K ⊗ P) (L ⊗ Q) => t.f p f)
    (tensorLeftHom_naturality c P Q)
  change (((tensorLeftHom K P Q).f p f).comp
    (Cochain.ofHom (c ⊗ₘ 𝟙 Q)) (add_zero p)) =
    (Cochain.ofHom (c ⊗ₘ 𝟙 P)).comp ((tensorLeftHom L P Q).f p f) (zero_add p) at h
  simpa only [tensorHom_id] using h

/-- 前方の二因子の合成と括弧変更は、残る右因子の任意次数cochainと可換する。 -/
lemma tensorJoin_cochain_naturality (U V W P Q : Complex A) (c : U ⊗ V ⟶ W)
    (p : ℤ) (f : Cochain P Q p) :
    (Cochain.ofHom ((α_ U V P).inv ≫ (c ▷ P))).comp
      ((tensorLeftHom W P Q).f p f) (zero_add p) =
    ((tensorLeftHom U (V ⊗ P) (V ⊗ Q)).f p
      ((tensorLeftHom V P Q).f p f)).comp
      (Cochain.ofHom ((α_ U V Q).inv ≫ (c ▷ Q))) (add_zero p) := by
  rw [Cochain.ofHom_comp, Cochain.ofHom_comp,
    Cochain.comp_assoc_of_first_is_zero_cochain,
    ← tensorLeftHom_cochain_naturality,
    ← Cochain.comp_assoc_of_third_is_zero_cochain,
    ← associator_inv_cochain_right, Cochain.comp_assoc_of_third_is_zero_cochain]

end SerrePositivity.DifferentialGraded
end

end AssociatorCochainNaturality

/-! ## AssociatorCochainFactors（旧 SerrePositivity/DifferentialGraded/Complexes/AssociatorCochainFactors.lean） -/

/-! # associatorの左・中間因子の全次数cochain自然性 -/

@[expose] public section AssociatorCochainFactors
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A]

/-- 左括弧の三重tensor上の任意次数cochainは純tensorで判定できる。 -/
lemma leftTripleCochain_ext {P Q R T : Complex A} {p : ℤ}
    (f g : Cochain ((P ⊗ Q) ⊗ R) T p)
    (h : ∀ (i j k a n : ℤ) (ha : i + j + k = a) (hn : a + p = n)
      (x : P.X i) (y : Q.X j) (z : R.X k),
      f.v a n hn (ιTensorObj (P ⊗ Q) R (i + j) k a ha
        (ιTensorObj P Q i j (i + j) rfl (x ⊗ₜ[A] y) ⊗ₜ[A] z)) =
      g.v a n hn (ιTensorObj (P ⊗ Q) R (i + j) k a ha
        (ιTensorObj P Q i j (i + j) rfl (x ⊗ₜ[A] y) ⊗ₜ[A] z))) : f = g := by
  apply Cochain.ext
  intro a n hn
  apply SerrePositivity.cochainTensorTriple_hom_ext P Q R a
  intro i j k ha
  apply ModuleCat.hom_ext
  apply TensorProduct.ext_threefold
  intro x y z
  exact h i j k a n ha hn x y z

lemma associator_hom_cochain_left (P P' Q R : Complex A) (p : ℤ) (f : Cochain P P' p) :
    ((tensorRightHom R (P ⊗ Q) (P' ⊗ Q)).f p
      ((tensorRightHom Q P P').f p f)).comp (Cochain.ofHom (α_ P' Q R).hom) (add_zero p) =
    (Cochain.ofHom (α_ P Q R).hom).comp
      ((tensorRightHom (Q ⊗ R) P P').f p f) (zero_add p) := by
  apply leftTripleCochain_ext
  intro i j k a n ha hn x y z
  rw [cochain_comp_ofHom_apply, cochain_ofHom_comp_apply, tensorRightHom_apply,
    tensorRightHom_apply_of_sum Q P P' p i j (i + j) (i + p) (i + j + p) rfl rfl rfl,
    associator_apply_of_sum P' Q R (i + p) j k (i + j + p) n (by omega) (by omega),
    associator_apply, tensorRightHom_apply]

lemma associator_hom_cochain_middle (K P P' R : Complex A) (p : ℤ) (f : Cochain P P' p) :
    ((tensorRightHom R (K ⊗ P) (K ⊗ P')).f p
      ((tensorLeftHom K P P').f p f)).comp (Cochain.ofHom (α_ K P' R).hom) (add_zero p) =
    (Cochain.ofHom (α_ K P R).hom).comp
      ((tensorLeftHom K (P ⊗ R) (P' ⊗ R)).f p
        ((tensorRightHom R P P').f p f)) (zero_add p) := by
  apply leftTripleCochain_ext
  intro i j k a n ha hn x y z
  rw [cochain_comp_ofHom_apply, cochain_ofHom_comp_apply, tensorRightHom_apply,
    tensorLeftHom_apply_of_sum K P P' p i j (i + j) (j + p) (i + j + p) rfl rfl rfl,
    associator_apply]
  simp only [Units.smul_def, TensorProduct.smul_tmul]
  rw [associator_apply_of_sum K P' R i (j + p) k (i + j + p) n (by omega) (by omega),
    tensorLeftHom_apply_of_sum K (P ⊗ R) (P' ⊗ R) p i (j + k) a (j + p + k) n
      (by omega) (by omega) hn,
    tensorRightHom_apply]
  simp only [Units.smul_def, TensorProduct.tmul_smul, map_zsmul]

end SerrePositivity.DifferentialGraded
end

end AssociatorCochainFactors

/-! ## TensorCarryCochain（旧 SerrePositivity/DifferentialGraded/Complexes/TensorCarryCochain.lean） -/

/-! # 結合的な先頭作用の下での任意次数cochainの連結への輸送

## 概要
結合的な先頭作用の下での任意次数cochainの連結への輸送。

## 方針
既存の全dg自然なHom・作用・chain mapと局所化の計算を再利用する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。dg加群の導来作用・準同値比較の基盤。任意可換環上のMorita・K理論のモデル比較に再利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section TensorCarryCochain
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A]

lemma tensorRight_cochain_chain_naturality (P P' Q Q' : Complex A) (p : ℤ)
    (f : Cochain P P' p) (g : Q ⟶ Q') :
    (Cochain.ofHom (P ◁ g)).comp ((tensorRightHom Q' P P').f p f) (zero_add p) =
    ((tensorRightHom Q P P').f p f).comp (Cochain.ofHom (P' ◁ g)) (add_zero p) := by
  have h := tensorCochain_interchange P P' Q Q' p 0 p (add_zero p) (zero_add p)
    f (Cochain.ofHom g)
  simp only [mul_zero, Int.negOnePow_zero, one_smul, tensorLeftHom_ofHom] at h
  exact h.symm

lemma tensorCarry_cochain (K P P' Q T T' R S : Complex A) (p : ℤ)
    (f : Cochain P P' p) (g : Cochain T T' p)
    (m : P ⊗ Q ⟶ T) (n : P' ⊗ Q ⟶ T') (r : K ⊗ P' ⟶ R)
    (s : K ⊗ T' ⟶ S) (t : R ⊗ Q ⟶ S)
    (hm : (Cochain.ofHom m).comp g (zero_add p) =
      ((tensorRightHom Q P P').f p f).comp (Cochain.ofHom n) (add_zero p))
    (ha : (r ▷ Q) ≫ t = (α_ K P' Q).hom ≫ K ◁ n ≫ s) :
    (Cochain.ofHom ((α_ K P Q).hom ≫ K ◁ m)).comp
      (((tensorLeftHom K T T').f p g).comp (Cochain.ofHom s) (add_zero p)) (zero_add p) =
    ((tensorRightHom Q (K ⊗ P) R).f p
      (((tensorLeftHom K P P').f p f).comp (Cochain.ofHom r) (add_zero p))).comp
      (Cochain.ofHom t) (add_zero p) := by
  rw [Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain,
    ← Cochain.comp_assoc_of_first_is_zero_cochain
      (Cochain.ofHom (K ◁ m)), ← tensorLeftHom_ofHom,
    ← tensorLeftHom_cochain_comp, hm, tensorLeftHom_cochain_comp, tensorLeftHom_ofHom,
    ← Cochain.comp_assoc_of_first_is_zero_cochain,
    ← Cochain.comp_assoc_of_first_is_zero_cochain,
    ← associator_hom_cochain_middle,
    Cochain.comp_assoc_of_third_is_zero_cochain,
    Cochain.comp_assoc_of_third_is_zero_cochain, ← Cochain.ofHom_comp, ← Cochain.ofHom_comp]
  rw [tensorRightHom_cochain_comp, tensorRightHom_ofHom,
    Cochain.comp_assoc_of_third_is_zero_cochain, ← Cochain.ofHom_comp, ha]

lemma tensorRight_action_cochain (E H P Q T R S : Complex A) (p : ℤ)
    (f : Cochain E H p) (m : P ⊗ Q ⟶ T) (n : H ⊗ P ⟶ R)
    (r : R ⊗ Q ⟶ S) (s : H ⊗ T ⟶ S)
    (ha : (n ▷ Q) ≫ r = (α_ H P Q).hom ≫ H ◁ m ≫ s) :
    (Cochain.ofHom ((α_ E P Q).hom ≫ E ◁ m)).comp
      (((tensorRightHom T E H).f p f).comp (Cochain.ofHom s) (add_zero p)) (zero_add p) =
    ((tensorRightHom Q (E ⊗ P) R).f p
      (((tensorRightHom P E H).f p f).comp (Cochain.ofHom n) (add_zero p))).comp
      (Cochain.ofHom r) (add_zero p) := by
  rw [Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain,
    ← Cochain.comp_assoc_of_first_is_zero_cochain (Cochain.ofHom (E ◁ m)),
    tensorRight_cochain_chain_naturality,
    ← Cochain.comp_assoc_of_first_is_zero_cochain,
    ← Cochain.comp_assoc_of_first_is_zero_cochain,
    ← associator_hom_cochain_left,
    Cochain.comp_assoc_of_third_is_zero_cochain,
    Cochain.comp_assoc_of_third_is_zero_cochain, ← Cochain.ofHom_comp, ← Cochain.ofHom_comp]
  rw [tensorRightHom_cochain_comp, tensorRightHom_ofHom,
    Cochain.comp_assoc_of_third_is_zero_cochain, ← Cochain.ofHom_comp, ha]

end SerrePositivity.DifferentialGraded
end

end TensorCarryCochain

/-! ## TensorZeroCochainLaws（旧 SerrePositivity/DifferentialGraded/Complexes/TensorZeroCochainLaws.lean） -/

/-! # 閉性を仮定しない次数0 tensorの合成・括弧変更 -/

@[expose] public section TensorZeroCochainLaws
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A]

lemma tensorZeroCochain_comp {P P' P'' Q Q' Q'' : Complex A}
    (f : Cochain P P' 0) (g : Cochain Q Q' 0)
    (f' : Cochain P' P'' 0) (g' : Cochain Q' Q'' 0) :
    (tensorZeroCochain f g).comp (tensorZeroCochain f' g') (zero_add 0) =
      tensorZeroCochain (f.comp f' (zero_add 0)) (g.comp g' (zero_add 0)) := by
  have h := tensorCochain_interchange P' P'' Q Q' 0 0 0 (zero_add 0) (zero_add 0) f' g
  simp only [mul_zero, Int.negOnePow_zero, one_smul] at h
  have hh := congrArg (fun t : Cochain (P' ⊗ Q) (P'' ⊗ Q') 0 =>
    ((tensorRightHom Q P P').f 0 f).comp
      (t.comp ((tensorLeftHom P'' Q' Q'').f 0 g') (zero_add 0)) (zero_add 0)) h.symm
  simpa only [tensorZeroCochain, tensorRightHom_cochain_comp, tensorLeftHom_cochain_comp,
    Cochain.comp_assoc_of_first_is_zero_cochain] using hh

lemma tensorZeroCochain_assoc {P P' Q Q' R R' : Complex A}
    (f : Cochain P P' 0) (g : Cochain Q Q' 0) (h : Cochain R R' 0) :
    (tensorZeroCochain (tensorZeroCochain f g) h).comp
      (Cochain.ofHom (α_ P' Q' R').hom) (zero_add 0) =
    (Cochain.ofHom (α_ P Q R).hom).comp
      (tensorZeroCochain f (tensorZeroCochain g h)) (zero_add 0) := by
  apply Cochain.ext₀
  intro n
  apply SerrePositivity.cochainTensorTriple_hom_ext P Q R n
  intro i j k hn
  apply ModuleCat.hom_ext
  apply TensorProduct.ext_threefold
  intro x y z
  change ((tensorZeroCochain (tensorZeroCochain f g) h).comp
      (Cochain.ofHom (α_ P' Q' R').hom) (zero_add 0)).v n n (add_zero n)
      (ιTensorObj (P ⊗ Q) R (i + j) k n hn
        (ιTensorObj P Q i j (i + j) rfl (x ⊗ₜ[A] y) ⊗ₜ[A] z)) =
    ((Cochain.ofHom (α_ P Q R).hom).comp (tensorZeroCochain f (tensorZeroCochain g h))
      (zero_add 0)).v n n (add_zero n)
      (ιTensorObj (P ⊗ Q) R (i + j) k n hn
        (ιTensorObj P Q i j (i + j) rfl (x ⊗ₜ[A] y) ⊗ₜ[A] z))
  simp only [cochain_comp_ofHom_apply, cochain_ofHom_comp_apply, tensorZeroCochain_apply,
    associator_apply]

lemma tensorZeroCochain_id_left {P Q Q' : Complex A} (g : Cochain Q Q' 0) :
    tensorZeroCochain (Cochain.ofHom (𝟙 P)) g = (tensorLeftHom P Q Q').f 0 g := by
  rw [tensorZeroCochain, tensorRightHom_ofHom, id_whiskerRight, Cochain.id_comp]

lemma tensorZeroCochain_id_right {P P' Q : Complex A} (f : Cochain P P' 0) :
    tensorZeroCochain f (Cochain.ofHom (𝟙 Q)) = (tensorRightHom Q P P').f 0 f := by
  rw [tensorZeroCochain, tensorLeftHom_ofHom, whiskerLeft_id, Cochain.comp_id]

end SerrePositivity.DifferentialGraded
end

end TensorZeroCochainLaws

/-! ## TensorZeroCochainLeftMap（旧 SerrePositivity/DifferentialGraded/Complexes/TensorZeroCochainLeftMap.lean） -/

/-! # 左の閉零写像を後で作用させる次数0 tensor表示 -/

@[expose] public section TensorZeroCochainLeftMap
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A]

lemma tensorZeroCochain_ofHom_left {P P' Q Q' : Complex A}
    (F : P ⟶ P') (g : Cochain Q Q' 0) :
    tensorZeroCochain (Cochain.ofHom F) g =
      ((tensorLeftHom P Q Q').f 0 g).comp (Cochain.ofHom (F ▷ Q')) (zero_add 0) := by
  rw [tensorZeroCochain, tensorRightHom_ofHom]
  exact (tensorLeftHom_cochain_naturality F Q Q' 0 g).symm

end SerrePositivity.DifferentialGraded
end

end TensorZeroCochainLeftMap

/-! ## TensorZeroCochainEvaluation（旧 SerrePositivity/DifferentialGraded/Complexes/TensorZeroCochainEvaluation.lean） -/

/-! # 次数0 cochainのtensor評価と結合的作用の持ち上げ -/

@[expose] public section TensorZeroCochainEvaluation
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A]

lemma tensorZeroCochain_postcomp_left {P P' Q Q' T : Complex A}
    (f : Cochain P P' 0) (g : Cochain Q Q' 0) (c : P' ⟶ T) :
    tensorZeroCochain (f.comp (Cochain.ofHom c) (zero_add 0)) g =
      (tensorZeroCochain f g).comp (Cochain.ofHom (c ▷ Q')) (zero_add 0) := by
  simpa only [tensorZeroCochain_ofHom, tensorHom_id, Cochain.comp_id] using
    (tensorZeroCochain_comp f g (Cochain.ofHom c) (Cochain.ofHom (𝟙 Q'))).symm

lemma tensorZeroCochain_postcomp_right {P P' Q Q' T : Complex A}
    (f : Cochain P P' 0) (g : Cochain Q Q' 0) (c : Q' ⟶ T) :
    tensorZeroCochain f (g.comp (Cochain.ofHom c) (zero_add 0)) =
      (tensorZeroCochain f g).comp (Cochain.ofHom (P' ◁ c)) (zero_add 0) := by
  simpa only [tensorZeroCochain_ofHom, id_tensorHom, Cochain.comp_id] using
    (tensorZeroCochain_comp f g (Cochain.ofHom (𝟙 P')) (Cochain.ofHom c)).symm

lemma tensorZeroCochain_precomp {P P' P'' Q Q' Q'' : Complex A}
    (c : P ⟶ P') (d : Q ⟶ Q') (f : Cochain P' P'' 0) (g : Cochain Q' Q'' 0) :
    (Cochain.ofHom (c ⊗ₘ d)).comp (tensorZeroCochain f g) (zero_add 0) =
      tensorZeroCochain ((Cochain.ofHom c).comp f (zero_add 0))
        ((Cochain.ofHom d).comp g (zero_add 0)) := by
  simpa only [tensorZeroCochain_ofHom] using
    tensorZeroCochain_comp (Cochain.ofHom c) (Cochain.ofHom d) f g

lemma tensorZeroCochain_multiply_assoc {P P' Q Q' R R' U V W : Complex A}
    (f : Cochain P P' 0) (g : Cochain Q Q' 0) (h : Cochain R R' 0)
    (c : P' ⊗ Q' ⟶ U) (d : U ⊗ R' ⟶ W) (e : Q' ⊗ R' ⟶ V) (k : P' ⊗ V ⟶ W)
    (ha : (c ▷ R') ≫ d = (α_ P' Q' R').hom ≫ P' ◁ e ≫ k) :
    (tensorZeroCochain ((tensorZeroCochain f g).comp (Cochain.ofHom c) (zero_add 0)) h).comp
      (Cochain.ofHom d) (zero_add 0) =
    (Cochain.ofHom (α_ P Q R).hom).comp
      ((tensorZeroCochain f ((tensorZeroCochain g h).comp (Cochain.ofHom e) (zero_add 0))).comp
        (Cochain.ofHom k) (zero_add 0)) (zero_add 0) := by
  have hh := congrArg (fun t : Cochain ((P ⊗ Q) ⊗ R) (P' ⊗ (Q' ⊗ R')) 0 =>
    t.comp (Cochain.ofHom (P' ◁ e ≫ k)) (zero_add 0)) (tensorZeroCochain_assoc f g h)
  rw [tensorZeroCochain_postcomp_left, tensorZeroCochain_postcomp_right]
  simp only [Cochain.comp_assoc_of_first_is_zero_cochain]
  rw [← Cochain.ofHom_comp, ha]
  simpa only [Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain] using hh

lemma tensorCarry_evaluation {K K' P P' Q Q' T T' U V : Complex A}
    (r : Cochain K K' 0) (a : Cochain P P' 0) (b : Cochain Q Q' 0) (c : Cochain T T' 0)
    (m : P ⊗ Q ⟶ T) (n : P' ⊗ Q' ⟶ T')
    (e : K' ⊗ P' ⟶ U) (e' : K' ⊗ T' ⟶ V) (n' : U ⊗ Q' ⟶ V)
    (hm : (Cochain.ofHom m).comp c (zero_add 0) =
      (tensorZeroCochain a b).comp (Cochain.ofHom n) (zero_add 0))
    (ha : (e ▷ Q') ≫ n' = (α_ K' P' Q').hom ≫ K' ◁ n ≫ e') :
    (Cochain.ofHom ((α_ K P Q).hom ≫ K ◁ m)).comp
      ((tensorZeroCochain r c).comp (Cochain.ofHom e') (zero_add 0)) (zero_add 0) =
    (tensorZeroCochain ((tensorZeroCochain r a).comp (Cochain.ofHom e) (zero_add 0)) b).comp
      (Cochain.ofHom n') (zero_add 0) := by
  have hc : (Cochain.ofHom (K ◁ m)).comp (tensorZeroCochain r c) (zero_add 0) =
      tensorZeroCochain r ((Cochain.ofHom m).comp c (zero_add 0)) := by
    simpa only [id_tensorHom, Cochain.id_comp] using
      tensorZeroCochain_precomp (𝟙 K) m r c
  have hp := congrArg (fun z : Cochain (K ⊗ (P ⊗ Q)) (K' ⊗ T') 0 =>
    (Cochain.ofHom (α_ K P Q).hom).comp
      (z.comp (Cochain.ofHom e') (zero_add 0)) (zero_add 0)) hc
  calc
    _ = (Cochain.ofHom (α_ K P Q).hom).comp
        ((tensorZeroCochain r ((Cochain.ofHom m).comp c (zero_add 0))).comp
          (Cochain.ofHom e') (zero_add 0)) (zero_add 0) := by
      simpa only [Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain] using hp
    _ = _ := by
      rw [hm]
      exact (tensorZeroCochain_multiply_assoc r a b e n' n e' ha).symm

end SerrePositivity.DifferentialGraded
end

end TensorZeroCochainEvaluation

/-! ## TensorJoinHomNaturality（旧 SerrePositivity/DifferentialGraded/Complexes/TensorJoinHomNaturality.lean） -/

/-! # 前方二因子の合成に関する全Hom写像の自然性 -/

@[expose] public section TensorJoinHomNaturality
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A]

lemma tensorJoin_hom_naturality (U V W P Q : Complex A) (c : U ⊗ V ⟶ W) :
    (tensorLeftHom V P Q ≫ tensorLeftHom U (V ⊗ P) (V ⊗ Q)) ≫
      homPostcompose (U ⊗ (V ⊗ P)) ((α_ U V Q).inv ≫ c ▷ Q) =
    tensorLeftHom W P Q ≫
      homPrecompose ((α_ U V P).inv ≫ c ▷ P) (W ⊗ Q) := by
  apply hom_naturality_of_apply
  intro p f
  exact (tensorJoin_cochain_naturality U V W P Q c p f).symm

end SerrePositivity.DifferentialGraded
end

end TensorJoinHomNaturality

/-! ## TensorJoinAssociativity（旧 SerrePositivity/DifferentialGraded/Complexes/TensorJoinAssociativity.lean） -/

/-! # 前方tensor因子の合成と残る右因子の結合則 -/

@[expose] public section TensorJoinAssociativity
universe u

noncomputable section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory
variable {A : Type u} [CommRing A]

/-- 結合的な前方合成に右因子を残す操作も結合則を保つ。 -/
lemma tensorJoin_assoc (U V T W X Z R : Complex A)
    (f : U ⊗ V ⟶ W) (g : V ⊗ T ⟶ X) (h : W ⊗ T ⟶ Z) (k : U ⊗ X ⟶ Z)
    (ha : (f ▷ T) ≫ h = (α_ U V T).hom ≫ U ◁ g ≫ k) :
    (f ▷ (T ⊗ R)) ≫ (α_ W T R).inv ≫ h ▷ R =
    (α_ U V (T ⊗ R)).hom ≫ U ◁ ((α_ V T R).inv ≫ g ▷ R) ≫
      (α_ U X R).inv ≫ k ▷ R := by
  have hα : (α_ (U ⊗ V) T R).inv ≫ (α_ U V T).hom ▷ R =
      (α_ U V (T ⊗ R)).hom ≫ U ◁ (α_ V T R).inv ≫ (α_ U (V ⊗ T) R).inv := by
    monoidal
  rw [associator_inv_naturality_left_assoc, ← comp_whiskerRight, ha]
  simp only [comp_whiskerRight, whiskerLeft_comp, Category.assoc]
  simp only [associator_inv_naturality_middle_assoc]
  simpa only [Category.assoc] using
    congrArg (fun t => t ≫ (U ◁ g) ▷ R ≫ k ▷ R) hα

end SerrePositivity.DifferentialGraded
end

end TensorJoinAssociativity

/-! ## TensorCarryAssociativity（旧 SerrePositivity/DifferentialGraded/Complexes/TensorCarryAssociativity.lean） -/

/-! # 固定左tensor因子を伴う右作用の結合則 -/

@[expose] public section TensorCarryAssociativity
universe u

noncomputable section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory
variable {A : Type u} [CommRing A]

/-- 右作用の結合図式は固定左tensor因子を追加しても保たれる。 -/
lemma tensorCarry_assoc (K P Q R T U V : Complex A)
    (f : P ⊗ Q ⟶ T) (g : T ⊗ R ⟶ U) (h : Q ⊗ R ⟶ V) (k : P ⊗ V ⟶ U)
    (ha : (f ▷ R) ≫ g = (α_ P Q R).hom ≫ P ◁ h ≫ k) :
    (((α_ K P Q).hom ≫ K ◁ f) ▷ R) ≫ (α_ K T R).hom ≫ K ◁ g =
    (α_ (K ⊗ P) Q R).hom ≫ (K ⊗ P) ◁ h ≫ (α_ K P V).hom ≫ K ◁ k := by
  simp only [comp_whiskerRight, Category.assoc]
  rw [associator_naturality_middle_assoc, ← whiskerLeft_comp, ha]
  simp only [whiskerLeft_comp]
  rw [pentagon_assoc, associator_naturality_right_assoc]

end SerrePositivity.DifferentialGraded
end

end TensorCarryAssociativity

/-! ## TensorJoinUnit（旧 SerrePositivity/DifferentialGraded/Complexes/TensorJoinUnit.lean） -/

/-! # 右因子を残す前方合成の左単位則 -/

@[expose] public section TensorJoinUnit
universe u

noncomputable section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory
variable {A : Type u} [CommRing A]

lemma tensorJoin_left_unit (E V R : Complex A) (e : 𝟙_ (Complex A) ⟶ E)
    (c : E ⊗ V ⟶ V) (hu : (λ_ V).inv ≫ e ▷ V ≫ c = 𝟙 V) :
    (λ_ (V ⊗ R)).inv ≫ e ▷ (V ⊗ R) ≫ (α_ E V R).inv ≫ c ▷ R = 𝟙 (V ⊗ R) := by
  have hunitTensor : (λ_ (V ⊗ R)).inv ≫ (α_ (𝟙_ (Complex A)) V R).inv = (λ_ V).inv ▷ R := by
    monoidal
  rw [associator_inv_naturality_left_assoc]
  calc
    _ = (λ_ V).inv ▷ R ≫ (e ▷ V) ▷ R ≫ c ▷ R := by
      simpa only [Category.assoc] using congrArg (fun t => t ≫ (e ▷ V) ▷ R ≫ c ▷ R) hunitTensor
    _ = ((λ_ V).inv ≫ e ▷ V ≫ c) ▷ R := by simp only [comp_whiskerRight]
    _ = 𝟙 _ := by rw [hu, id_whiskerRight]

end SerrePositivity.DifferentialGraded
end

end TensorJoinUnit

/-! ## TensorCarryUnit（旧 SerrePositivity/DifferentialGraded/Complexes/TensorCarryUnit.lean） -/

/-! # 右作用の単位と固定左tensor因子の整合性 -/

@[expose] public section TensorCarryUnit
universe u

noncomputable section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory
variable {A : Type u} [CommRing A]

/-- 右単位を固定左因子の内側へ移す構造式。 -/
lemma tensorCarry_right_unit (K P H T : Complex A) (e : 𝟙_ (Complex A) ⟶ H)
    (f : P ⊗ H ⟶ T) :
    (ρ_ (K ⊗ P)).inv ≫ (K ⊗ P) ◁ e ≫ (α_ K P H).hom ≫ K ◁ f =
      K ◁ ((ρ_ P).inv ≫ P ◁ e ≫ f) := by
  rw [associator_naturality_right_assoc, rightUnitor_tensor_inv]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, whiskerLeft_comp]

end SerrePositivity.DifferentialGraded
end

end TensorCarryUnit

/-! ## TensorUnitInsertion（旧 SerrePositivity/DifferentialGraded/Complexes/TensorUnitInsertion.lean） -/

/-! # 中間の単位挿入と前方合成の単位律 -/

@[expose] public section TensorUnitInsertion
universe u

noncomputable section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory
variable {A : Type u} [CommRing A]

lemma tensorMiddle_left_unit (E H P : Complex A) (e : 𝟙_ (Complex A) ⟶ H)
    (f : H ⊗ P ⟶ P) (hu : (λ_ P).inv ≫ e ▷ P ≫ f = 𝟙 P) :
    (((ρ_ E).inv ≫ E ◁ e) ▷ P) ≫ (α_ E H P).hom ≫ E ◁ f = 𝟙 (E ⊗ P) := by
  have hunit : (ρ_ E).inv ▷ P ≫ (α_ E (𝟙_ (Complex A)) P).hom = E ◁ (λ_ P).inv := by
    monoidal
  rw [comp_whiskerRight, Category.assoc, associator_naturality_middle_assoc]
  calc
    _ = E ◁ (λ_ P).inv ≫ E ◁ (e ▷ P) ≫ E ◁ f := by
      simpa only [Category.assoc] using congrArg (fun t => t ≫ E ◁ (e ▷ P) ≫ E ◁ f) hunit
    _ = E ◁ ((λ_ P).inv ≫ e ▷ P ≫ f) := by simp only [whiskerLeft_comp]
    _ = 𝟙 _ := by rw [hu, whiskerLeft_id]

lemma tensorSandwich_append (E H P : Complex A) (e : 𝟙_ (Complex A) ⟶ H)
    (f : H ⊗ P ⟶ P) (hu : (λ_ P).inv ≫ e ▷ P ≫ f = 𝟙 P) :
    (((λ_ E).inv ≫ (e ⊗ₘ ((ρ_ E).inv ≫ (𝟙 E ⊗ₘ e)))) ▷ P) ≫
      (α_ H (E ⊗ H) P).hom ≫ H ◁ ((α_ E H P).hom ≫ E ◁ f) =
    (λ_ (E ⊗ P)).inv ≫ e ▷ (E ⊗ P) := by
  have hunit : (λ_ E).inv ▷ P ≫ (α_ (𝟙_ (Complex A)) E P).hom = (λ_ (E ⊗ P)).inv := by
    monoidal
  simp only [tensorHom_def, comp_whiskerRight, id_whiskerRight, Category.id_comp, Category.assoc]
  rw [associator_naturality_middle_assoc, associator_naturality_left_assoc]
  rw [← whiskerLeft_comp, tensorMiddle_left_unit E H P e f hu, whiskerLeft_id, Category.comp_id]
  simpa only [Category.assoc] using congrArg (fun t => t ≫ e ▷ (E ⊗ P)) hunit

lemma tensorJoin_right_unit (V H R : Complex A) (e : 𝟙_ (Complex A) ⟶ H)
    (c : V ⊗ H ⟶ V) (hu : (ρ_ V).inv ≫ V ◁ e ≫ c = 𝟙 V) :
    V ◁ ((λ_ R).inv ≫ e ▷ R) ≫ (α_ V H R).inv ≫ c ▷ R = 𝟙 (V ⊗ R) := by
  have hunit : V ◁ (λ_ R).inv ≫ (α_ V (𝟙_ (Complex A)) R).inv = (ρ_ V).inv ▷ R := by
    monoidal
  simp only [whiskerLeft_comp, Category.assoc]
  rw [associator_inv_naturality_middle_assoc]
  calc
    _ = (ρ_ V).inv ▷ R ≫ (V ◁ e) ▷ R ≫ c ▷ R := by
      simpa only [Category.assoc] using congrArg (fun t => t ≫ (V ◁ e) ▷ R ≫ c ▷ R) hunit
    _ = ((ρ_ V).inv ≫ V ◁ e ≫ c) ▷ R := by simp only [comp_whiskerRight]
    _ = 𝟙 _ := by rw [hu, id_whiskerRight]

end SerrePositivity.DifferentialGraded
end

end TensorUnitInsertion

/-! ## TensorJoinRightAction（旧 SerrePositivity/DifferentialGraded/Complexes/TensorJoinRightAction.lean） -/

/-! # 前方二因子の合成と後方二因子への作用の交換 -/

@[expose] public section TensorJoinRightAction
universe u

noncomputable section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory
variable {A : Type u} [CommRing A]

lemma tensorJoin_right_action (U V W T R S : Complex A) (c : U ⊗ V ⟶ W) (r : T ⊗ R ⟶ S) :
    ((α_ U V T).inv ≫ c ▷ T) ▷ R ≫ (α_ W T R).hom ≫ W ◁ r =
    (α_ U (V ⊗ T) R).hom ≫ U ◁ ((α_ V T R).hom ≫ V ◁ r) ≫
      (α_ U V S).inv ≫ c ▷ S := by
  have hα : (α_ U V T).inv ▷ R ≫ (α_ (U ⊗ V) T R).hom =
      (α_ U (V ⊗ T) R).hom ≫ U ◁ (α_ V T R).hom ≫ (α_ U V (T ⊗ R)).inv := by
    monoidal
  rw [comp_whiskerRight, Category.assoc, associator_naturality_left_assoc,
    ← whisker_exchange]
  simp only [whiskerLeft_comp, Category.assoc, associator_inv_naturality_right_assoc]
  simpa only [Category.assoc] using congrArg (fun f => f ≫ (U ⊗ V) ◁ r ≫ c ▷ S) hα

end SerrePositivity.DifferentialGraded
end

end TensorJoinRightAction

/-! ## TensorJoinActionNaturality（旧 SerrePositivity/DifferentialGraded/Complexes/TensorJoinActionNaturality.lean） -/

/-! # 先頭二因子の合成と結合的作用に対する任意次数cochainの自然性

## 概要
先頭二因子の合成と結合的作用に対する任意次数cochainの自然性。

## 方針
既存の全dg自然なHom・作用・chain mapと局所化の計算を再利用する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。dg加群の導来作用・準同値比較の基盤。任意可換環上のMorita・K理論のモデル比較に再利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section TensorJoinActionNaturality
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A]

lemma tensorJoin_action_cochain (U V W P Q R T : Complex A) (p : ℤ)
    (f : Cochain P Q p) (c : U ⊗ V ⟶ W) (r : W ⊗ Q ⟶ T)
    (s : V ⊗ Q ⟶ R) (t : U ⊗ R ⟶ T)
    (hc : (α_ U V Q).inv ≫ (c ▷ Q) ≫ r = (U ◁ s) ≫ t) :
    (Cochain.ofHom ((α_ U V P).inv ≫ c ▷ P)).comp
      (((tensorLeftHom W P Q).f p f).comp (Cochain.ofHom r) (add_zero p)) (zero_add p) =
    ((tensorLeftHom U (V ⊗ P) R).f p
      (((tensorLeftHom V P Q).f p f).comp (Cochain.ofHom s) (add_zero p))).comp
      (Cochain.ofHom t) (add_zero p) := by
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, tensorJoin_cochain_naturality,
    tensorLeftHom_cochain_comp, tensorLeftHom_ofHom,
    Cochain.comp_assoc_of_third_is_zero_cochain,
    Cochain.comp_assoc_of_third_is_zero_cochain, ← Cochain.ofHom_comp, ← Cochain.ofHom_comp,
    Category.assoc, hc]

end SerrePositivity.DifferentialGraded
end

end TensorJoinActionNaturality

/-! ## TensorTwoUnitInsertion（旧 SerrePositivity/DifferentialGraded/Complexes/TensorTwoUnitInsertion.lean） -/

/-! # 異なる左右単位を挿入したtensorと後方作用

## 概要
異なる左右単位を挿入したtensorと後方作用。

## 方針
既存の全dg自然なHom・作用・chain mapと局所化の計算を再利用する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。dg加群の導来作用・準同値比較の基盤。任意可換環上のMorita・K理論のモデル比較に再利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section TensorTwoUnitInsertion
universe u

noncomputable section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory
variable {A : Type u} [CommRing A]

lemma tensorSandwich_append_distinct (E H₁ H₂ P : Complex A)
    (e₁ : 𝟙_ (Complex A) ⟶ H₁) (e₂ : 𝟙_ (Complex A) ⟶ H₂)
    (f : H₂ ⊗ P ⟶ P) (hu : (λ_ P).inv ≫ e₂ ▷ P ≫ f = 𝟙 P) :
    (((λ_ E).inv ≫ (e₁ ⊗ₘ ((ρ_ E).inv ≫ (𝟙 E ⊗ₘ e₂)))) ▷ P) ≫
      (α_ H₁ (E ⊗ H₂) P).hom ≫ H₁ ◁ ((α_ E H₂ P).hom ≫ E ◁ f) =
    (λ_ (E ⊗ P)).inv ≫ e₁ ▷ (E ⊗ P) := by
  have hunit : (λ_ E).inv ▷ P ≫ (α_ (𝟙_ (Complex A)) E P).hom = (λ_ (E ⊗ P)).inv := by
    monoidal
  simp only [tensorHom_def, comp_whiskerRight, id_whiskerRight, Category.id_comp, Category.assoc]
  rw [associator_naturality_middle_assoc, associator_naturality_left_assoc]
  rw [← whiskerLeft_comp, tensorMiddle_left_unit E H₂ P e₂ f hu,
    whiskerLeft_id, Category.comp_id]
  simpa only [Category.assoc] using congrArg (fun t => t ≫ e₁ ▷ (E ⊗ P)) hunit

end SerrePositivity.DifferentialGraded
end

end TensorTwoUnitInsertion

/-! ## TensorCompositionAssociativity（旧 SerrePositivity/DifferentialGraded/Complexes/TensorCompositionAssociativity.lean） -/

/-! # tensor合成の結合図式と純tensor成分式の往復 -/

@[expose] public section TensorCompositionAssociativity
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex
variable {A : Type u} [CommRing A]

lemma tensorComposition_assoc_apply (P Q R U V W : Complex A)
    (f : P ⊗ Q ⟶ U) (g : U ⊗ R ⟶ W) (h : Q ⊗ R ⟶ V) (k : P ⊗ V ⟶ W)
    (ha : (f ▷ R) ≫ g = (α_ P Q R).hom ≫ P ◁ h ≫ k)
    (p q r n : ℤ) (hn : p + q + r = n) (a : P.X p) (b : Q.X q) (c : R.X r) :
    g.f n (ιTensorObj U R (p + q) r n hn
      (f.f (p + q) (ιTensorObj P Q p q (p + q) rfl (a ⊗ₜ[A] b)) ⊗ₜ[A] c)) =
    k.f n (ιTensorObj P V p (q + r) n (by omega)
      (a ⊗ₜ[A] h.f (q + r) (ιTensorObj Q R q r (q + r) rfl (b ⊗ₜ[A] c)))) := by
  have hh := congrArg (fun F : (P ⊗ Q) ⊗ R ⟶ W =>
    F.f n (ιTensorObj (P ⊗ Q) R (p + q) r n hn
      (ιTensorObj P Q p q (p + q) rfl (a ⊗ₜ[A] b) ⊗ₜ[A] c))) ha
  simpa only [chain_comp_apply, whiskerRight_apply, associator_apply, whiskerLeft_apply] using hh

lemma tensorComposition_assoc_of_apply (P Q R U V W : Complex A)
    (f : P ⊗ Q ⟶ U) (g : U ⊗ R ⟶ W) (h : Q ⊗ R ⟶ V) (k : P ⊗ V ⟶ W)
    (ha : ∀ (p q r n : ℤ) (hn : p + q + r = n) (a : P.X p) (b : Q.X q) (c : R.X r),
      g.f n (ιTensorObj U R (p + q) r n hn
        (f.f (p + q) (ιTensorObj P Q p q (p + q) rfl (a ⊗ₜ[A] b)) ⊗ₜ[A] c)) =
      k.f n (ιTensorObj P V p (q + r) n (by omega)
        (a ⊗ₜ[A] h.f (q + r) (ιTensorObj Q R q r (q + r) rfl (b ⊗ₜ[A] c))))) :
    (f ▷ R) ≫ g = (α_ P Q R).hom ≫ P ◁ h ≫ k := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply SerrePositivity.cochainTensorTriple_hom_ext P Q R n
  intro p q r hn
  apply ModuleCat.hom_ext
  apply TensorProduct.ext_threefold
  intro a b c
  change g.f n ((f ▷ R).f n (ιTensorObj (P ⊗ Q) R (p + q) r n hn
      (ιTensorObj P Q p q (p + q) rfl (a ⊗ₜ[A] b) ⊗ₜ[A] c))) =
    k.f n ((P ◁ h).f n ((α_ P Q R).hom.f n (ιTensorObj (P ⊗ Q) R (p + q) r n hn
      (ιTensorObj P Q p q (p + q) rfl (a ⊗ₜ[A] b) ⊗ₜ[A] c))))
  rw [whiskerRight_apply, associator_apply, whiskerLeft_apply]
  exact ha p q r n hn a b c

end SerrePositivity.DifferentialGraded
end

end TensorCompositionAssociativity
