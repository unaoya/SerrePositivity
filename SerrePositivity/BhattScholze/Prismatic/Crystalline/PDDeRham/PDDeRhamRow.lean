module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDCompletedCech
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import SerrePositivity.HomologicalAlgebra.Cosimplicial.SplitCechConerve
import Mathlib.Algebra.Category.ModuleCat.Colimits
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDCompletedCech
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDPolynomialCech
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.CompletionFunctor

/-!
# pd de Rham 形式の余単体的な行

## 概要
各頂点の座標微分を基底とする分冪微分形式を余単体的加群にまとめる。

## 方針
係数の pd Čech 構造射と、頂点写像が外冪に誘導する写像をテンソルする。

## 規約
余面と余退化は頂点添字を移し、外冪の次数を保つ。

## 使われ方
pd de Rham 双複体と正の形式次数の行の収縮。
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open SerrePositivity.DerivedCompletion SerrePositivity.Cosimplicial
open scoped ZeroObject
open scoped TensorProduct

universe u

namespace SerrePositivity.BhattScholze.Prismatic

variable (p : ℕ) (k : Type u) [CommRing k] (r : ℕ)

private abbrev CopyModule (n : SimplexCategory) := (Fin r × Fin (n.len + 1)) →₀ k

private def copyIndex {m n : SimplexCategory} (θ : m ⟶ n) :
    Fin r × Fin (m.len + 1) → Fin r × Fin (n.len + 1) :=
  fun ji => (ji.1, θ.toOrderHom ji.2)

private def copyModuleMap {m n : SimplexCategory} (θ : m ⟶ n) :
    CopyModule k r m →ₗ[k] CopyModule k r n :=
  Finsupp.lmapDomain k k (copyIndex r θ)

private theorem copyModuleMap_id (n : SimplexCategory) :
    copyModuleMap k r (𝟙 n) = LinearMap.id := by
  have h : copyIndex r (𝟙 n) = id := by funext ⟨a,b⟩; rfl
  rw [copyModuleMap, h, Finsupp.lmapDomain_id]

private theorem copyModuleMap_comp {l m n : SimplexCategory} (θ : l ⟶ m) (ψ : m ⟶ n) :
    copyModuleMap k r (θ ≫ ψ) = copyModuleMap k r ψ ∘ₗ copyModuleMap k r θ := by
  have h : copyIndex r (θ ≫ ψ) = copyIndex r ψ ∘ copyIndex r θ := by
    funext ⟨a,b⟩
    rfl
  simpa only [copyModuleMap, h] using Finsupp.lmapDomain_comp k k (copyIndex r θ) (copyIndex r ψ)

private def rawTermMap {m n : SimplexCategory} (θ : m ⟶ n) :
    CommRingCat.of (pdRaw k r m.len) ⟶ CommRingCat.of (pdRaw k r n.len) :=
  CommRingCat.ofHom (pdRawMap k r θ).toRingHom

private def pdTermMap {m n : SimplexCategory} (θ : m ⟶ n) :
    pdTerm p k r m.len →ₗ[k] pdTerm p k r n.len :=
  let f := ringCatMap p (rawTermMap k r θ)
  { toFun := f.hom
    map_add' := f.hom.map_add
    map_smul' := fun c x => by
      change f.hom (c • x) = c • f.hom x
      rw [Algebra.smul_def, Algebra.smul_def, map_mul]
      congr 1
      let jM := principalCompletionRingCatUnit p (CommRingCat.of (pdRaw k r m.len))
      let jN := principalCompletionRingCatUnit p (CommRingCat.of (pdRaw k r n.len))
      change f (jM (algebraMap k (pdRaw k r m.len) c)) =
        jN (algebraMap k (pdRaw k r n.len) c)
      exact (ConcreteCategory.congr_hom (ringCatMap_comp_unit p (rawTermMap k r θ)) _).trans
        (congrArg jN ((pdRawMap k r θ).commutes c)) }

private theorem pdTermMap_id (n : SimplexCategory) :
    pdTermMap p k r (𝟙 n) = LinearMap.id := by
  have h : rawTermMap k r (𝟙 n) = 𝟙 _ := by rw [rawTermMap, pdRawMap_id]; rfl
  apply LinearMap.ext
  intro x
  have e : ringCatMap p (rawTermMap k r (𝟙 n)) = 𝟙 (pdTerm p k r n.len) :=
    (congrArg (principalCompletionRingFunctor p).map h).trans
      ((principalCompletionRingFunctor p).map_id _)
  exact ConcreteCategory.congr_hom e x

private theorem pdTermMap_comp {l m n : SimplexCategory} (θ : l ⟶ m) (ψ : m ⟶ n) :
    pdTermMap p k r (θ ≫ ψ) = pdTermMap p k r ψ ∘ₗ pdTermMap p k r θ := by
  have h : rawTermMap k r (θ ≫ ψ) = rawTermMap k r θ ≫ rawTermMap k r ψ := by
    rw [rawTermMap, pdRawMap_comp]
    rfl
  apply LinearMap.ext
  intro x
  change (principalCompletionRingFunctor p).map (rawTermMap k r (θ ≫ ψ)) x =
    (principalCompletionRingFunctor p).map (rawTermMap k r ψ)
      ((principalCompletionRingFunctor p).map (rawTermMap k r θ) x)
  rw [h, Functor.map_comp]
  rfl

private def copyModules : CosimplicialObject (ModuleCat.{u} k) where
  obj n := ModuleCat.of k (CopyModule k r n)
  map θ := ModuleCat.ofHom (copyModuleMap k r θ)
  map_id n := ModuleCat.hom_ext (copyModuleMap_id k r n)
  map_comp θ ψ := ModuleCat.hom_ext (copyModuleMap_comp k r θ ψ)

private def pdCoefficients : CosimplicialObject (ModuleCat.{u} k) where
  obj n := ModuleCat.of k (pdTerm p k r n.len)
  map θ := ModuleCat.ofHom (pdTermMap p k r θ)
  map_id n := ModuleCat.hom_ext (pdTermMap_id p k r n)
  map_comp θ ψ := ModuleCat.hom_ext (pdTermMap_comp p k r θ ψ)

private def tensorExterior (j : ℕ) : ModuleCat.{u} k × ModuleCat.{u} k ⥤ ModuleCat.{u} k where
  obj X := ModuleCat.of k (X.1 ⊗[k] (⋀[k]^j X.2))
  map f := ModuleCat.ofHom (TensorProduct.map f.1.hom (exteriorPower.map j f.2.hom))
  map_id X := by
    apply ModuleCat.hom_ext
    change TensorProduct.map LinearMap.id (exteriorPower.map j LinearMap.id) = LinearMap.id
    rw [exteriorPower.map_id, TensorProduct.map_id]
  map_comp f g := by
    apply ModuleCat.hom_ext
    change TensorProduct.map (_ ∘ₗ _) (exteriorPower.map j (_ ∘ₗ _)) =
      TensorProduct.map _ _ ∘ₗ TensorProduct.map _ _
    rw [exteriorPower.map_comp, TensorProduct.map_comp]
    rfl

/-- 形式次数を固定した pd de Rham 形式の余単体的加群。 -/
def pdRow (j : ℕ) : CosimplicialObject (ModuleCat.{u} k) :=
  (pdCoefficients p k r).prod' (copyModules k r) ⋙ tensorExterior k j

private def zeroArrow : Arrow (ModuleCat.{u} k) :=
  Arrow.mk (0 : 0 ⟶ ModuleCat.of k (Fin r →₀ k))

private def copyInsert (n : SimplexCategory) (i : Fin (n.len + 1)) :
    (zeroArrow k r).right ⟶ (copyModules k r).obj n :=
  ModuleCat.ofHom (Finsupp.lmapDomain k k (fun j => (j,i)))

private theorem zeroArrow_left_zero : IsZero (zeroArrow k r).left :=
  isZero_zero _

set_option backward.isDefEq.respectTransparency false in
private def fromCech :
    (zeroArrow k r).cechConerve ⟶ copyModules k r where
  app n := WidePushout.desc 0 (copyInsert k r n)
    (fun _ => (zeroArrow_left_zero k r).eq_of_src _ _)
  naturality m n θ := by
    apply WidePushout.hom_ext
    · intro i
      simp only [Arrow.cechConerve_map, WidePushout.ι_desc_assoc, WidePushout.ι_desc]
      apply ModuleCat.hom_ext
      change Finsupp.lmapDomain k k _ =
        (copyModuleMap k r θ).comp (Finsupp.lmapDomain k k _)
      rw [copyModuleMap, ← Finsupp.lmapDomain_comp]
      rfl
    · exact (zeroArrow_left_zero k r).eq_of_src _ _

set_option backward.isDefEq.respectTransparency false in
private def toCechApp (n : SimplexCategory) :
    (copyModules k r).obj n ⟶ (zeroArrow k r).cechConerve.obj n :=
  ModuleCat.ofHom (Finsupp.linearCombination k fun ji =>
    (WidePushout.ι (fun _ => (zeroArrow k r).hom) ji.2 :
      (zeroArrow k r).right ⟶ (zeroArrow k r).cechConerve.obj n) (Finsupp.single ji.1 1))

set_option backward.isDefEq.respectTransparency false in
private theorem copyInsert_toCechApp (n : SimplexCategory) (i : Fin (n.len + 1)) :
    copyInsert k r n i ≫ toCechApp k r n = WidePushout.ι (fun _ => (zeroArrow k r).hom) i := by
  apply ModuleCat.hom_ext
  apply (Finsupp.basisSingleOne (R := k)).ext
  intro j
  change (Finsupp.linearCombination k _)
    (Finsupp.mapDomain (fun a : Fin r => (a,i)) (Finsupp.single j 1)) = _
  rw [Finsupp.mapDomain_single, Finsupp.linearCombination_single, one_smul]
  rfl

set_option backward.isDefEq.respectTransparency false in
private def copyIsoApp (n : SimplexCategory) :
    (zeroArrow k r).cechConerve.obj n ≅ (copyModules k r).obj n where
  hom := (fromCech k r).app n
  inv := toCechApp k r n
  hom_inv_id := by
    apply WidePushout.hom_ext
    · intro i
      change WidePushout.ι _ i ≫ WidePushout.desc 0 (copyInsert k r n) _ ≫ _ = _
      rw [WidePushout.ι_desc_assoc, copyInsert_toCechApp]
      exact (Category.comp_id (WidePushout.ι (fun _ => (zeroArrow k r).hom) i)).symm
    · exact (zeroArrow_left_zero k r).eq_of_src _ _
  inv_hom_id := by
    apply ModuleCat.hom_ext
    apply (Finsupp.basisSingleOne (R := k)).ext
    rintro ⟨j,i⟩
    change (fromCech k r).app n ((Finsupp.linearCombination k _) (Finsupp.single (j,i) 1)) =
      Finsupp.single (j,i) 1
    rw [Finsupp.linearCombination_single, one_smul]
    have h := ConcreteCategory.congr_hom
      (WidePushout.ι_desc (fun _ : Fin (n.len + 1) => (zeroArrow k r).hom)
        (0 : (zeroArrow k r).left ⟶ (copyModules k r).obj n)
        (copyInsert k r n) (fun _ => (zeroArrow_left_zero k r).eq_of_src _ _) i)
      (Finsupp.single j 1)
    exact h.trans (Finsupp.mapDomain_single)

private def copyIso : (zeroArrow k r).cechConerve ≅ copyModules k r :=
  NatIso.ofComponents (copyIsoApp k r) (fun θ => (fromCech k r).naturality θ)

private theorem exteriorPower_map_zero {M N : Type u} [AddCommGroup M] [Module k M]
    [AddCommGroup N] [Module k N] (j : ℕ) (hj : 0 < j) :
    exteriorPower.map j (0 : M →ₗ[k] N) = 0 := by
  apply exteriorPower.linearMap_ext
  ext x
  simp only [exteriorPower.map_comp_ιMulti, AlternatingMap.compLinearMap_apply,
    LinearMap.zero_apply, LinearMap.compAlternatingMap_apply]
  exact congrArg Subtype.val ((exteriorPower.ιMulti k j).map_coord_zero
    (m := fun _ => (0 : N)) ⟨0, hj⟩ rfl)

/-- 正次数の pd de Rham 行の交代余面複体は収縮可能。 -/
theorem pdRow_contractible (j : ℕ) (hj : 0 < j) :
    let K := (alternatingCofaceMapComplex _).obj (pdRow p k r j)
    Nonempty (Homotopy (𝟙 K) 0) := by
  let f := zeroArrow k r
  let R := pdCoefficients p k r
  let F := tensorExterior k j
  have h₀ : f.hom ≫ (0 : f.right ⟶ f.left) = 𝟙 f.left := by
    exact (isZero_zero _).eq_of_src _ _
  let e : f.cechConerve ⟶ f.cechConerve := cechRetraction f 0 h₀ ≫ f.augmentedCechConerve.hom
  have he : e = 0 := by
    apply NatTrans.ext
    funext n
    change (cechRetraction f 0 h₀).app n ≫ f.augmentedCechConerve.hom.app n = 0
    let a : f.left ⟶ f.cechConerve.obj n := f.augmentedCechConerve.hom.app n
    change (cechRetraction f 0 h₀).app n ≫ a = 0
    rw [(zeroArrow_left_zero k r).eq_zero_of_tgt ((cechRetraction f 0 h₀).app n), zero_comp]
  let h := ((CosimplicialHomotopy.refl (𝟙 R)).prod'
    (cechSplitHomotopy f 0 h₀)).whiskerRight F
  let G := alternatingCofaceMapComplex (ModuleCat.{u} k)
  let a : R.prod' f.cechConerve ⋙ F ≅ pdRow p k r j :=
    Functor.isoWhiskerRight (NatIso.ofComponents (fun n =>
      { hom := (𝟙 _, (copyIso k r).hom.app n)
        inv := (𝟙 _, (copyIso k r).inv.app n)
        hom_inv_id := by
          apply Prod.ext
          · change (𝟙 (R.obj n)) ≫ 𝟙 (R.obj n) = 𝟙 (R.obj n)
            exact Category.id_comp _
          · exact ((copyIso k r).app n).hom_inv_id
        inv_hom_id := by
          apply Prod.ext
          · change (𝟙 (R.obj n)) ≫ 𝟙 (R.obj n) = 𝟙 (R.obj n)
            exact Category.id_comp _
          · exact ((copyIso k r).app n).inv_hom_id }) (fun θ => by
      apply Prod.ext
      · change R.map θ ≫ 𝟙 _ = 𝟙 _ ≫ R.map θ
        simp
      · exact (copyIso k r).hom.naturality θ)) F
  let b := G.mapIso a
  have h₁ : G.map (Functor.whiskerRight (NatTrans.prod' (𝟙 R) (𝟙 f.cechConerve)) F) =
      𝟙 _ := by
    rw [show NatTrans.prod' (𝟙 R) (𝟙 f.cechConerve) = 𝟙 (R.prod' f.cechConerve) from rfl]
    simp
  have h₂ : G.map (Functor.whiskerRight (NatTrans.prod' (𝟙 R) e) F) = 0 := by
    ext n : 1
    apply ModuleCat.hom_ext
    change TensorProduct.map _ (exteriorPower.map j (e.app _).hom) = 0
    rw [he]
    change TensorProduct.map _ (exteriorPower.map j 0) = 0
    rw [exteriorPower_map_zero k j hj]
    ext
    simp
  have H : Homotopy (𝟙 _) (0 : G.obj (R.prod' f.cechConerve ⋙ F) ⟶ _) := by
    have H := h.toCochainHomotopy
    change Homotopy (G.map _) (G.map (Functor.whiskerRight (NatTrans.prod' (𝟙 R) e) F)) at H
    exact (Homotopy.ofEq h₁.symm).trans (H.trans (Homotopy.ofEq h₂))
  exact ⟨by simpa using ((H.compLeft b.inv).compRight b.hom)⟩

end SerrePositivity.BhattScholze.Prismatic
