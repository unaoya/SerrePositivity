module
public import SerrePositivity.DifferentialGraded.Tensor.ScalarExtension
public import SerrePositivity.DifferentialGraded.Complexes.Closed
public import SerrePositivity.DifferentialGraded.Category.Examples

/-! # 係数変更と全次数 Hom の比較

全次数 Hom の係数変更から、係数変更した複体間の Hom への射。
これが同型であるという有限性条件は仮定しない。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity.DifferentialGraded.ScalarExtension
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')

/-- 評価の係数変更を転置した全次数 Hom 比較。 -/
def homComparison (K L : Complex A) :
    (extension φ).obj (homComplex A K L) ⟶
      homComplex A' ((extension φ).obj K) ((extension φ).obj L) :=
  curryRight ((tensorIso φ (homComplex A K L) K).inv ≫
    (extension φ).map (uncurryRight (𝟙 (homComplex A K L))))

set_option maxHeartbeats 800000 in
-- total tensor の同型の逆を純粋生成元上で計算する。
lemma tensorIso_inv_apply (K L : Complex A) (i j n : ℤ) (h : i + j = n)
    (x : K.X i) (y : L.X j) :
    let := φ.toAlgebra
    (tensorIso φ K L).inv.f n
      (ιTensorObj ((extension φ).obj K) ((extension φ).obj L) i j n h
        (((1 : A') ⊗ₜ[A] x) ⊗ₜ[A'] ((1 : A') ⊗ₜ[A] y))) =
      (1 : A') ⊗ₜ[A] ιTensorObj K L i j n h (x ⊗ₜ[A] y) := by
  let := φ.toAlgebra
  have he := cochainTensorBaseChangeIso_apply_ι φ K L i j n h x y
  have hi := congrArg (fun z => (tensorIso φ K L).inv.f n z) he
  have hc := congrArg (fun f => f.f n
    ((1 : A') ⊗ₜ[A] ιTensorObj K L i j n h (x ⊗ₜ[A] y))) (tensorIso φ K L).hom_inv_id
  exact hi.symm.trans hc

set_option maxHeartbeats 800000 in
-- 係数制限の加群表示を展開して純粋生成元上で評価する。
lemma homComparison_apply (K L : Complex A) (p i n : ℤ) (h : i + p = n)
    (f : Homogeneous K L p) (x : K.X i) :
    let := φ.toAlgebra
    ((homComparison φ K L).f p ((1 : A') ⊗ₜ[A] f)).v i n h
      ((1 : A') ⊗ₜ[A] x) = (1 : A') ⊗ₜ[A] f.v i n h x := by
  let := φ.toAlgebra
  change ((extension φ).map (uncurryRight (𝟙 (homComplex A K L)))).f n
    ((tensorIso φ (homComplex A K L) K).inv.f n
      (ιTensorObj ((extension φ).obj (homComplex A K L)) ((extension φ).obj K) p i n (by omega)
        (((1 : A') ⊗ₜ[A] f) ⊗ₜ[A'] ((1 : A') ⊗ₜ[A] x)))) = _
  erw [tensorIso_inv_apply φ (homComplex A K L) K p i n (by omega) f x]
  erw [ModuleCat.ExtendScalars.map_tmul φ, uncurryRight_apply]
  rfl

lemma sphereIso_inv_one (n : ℤ) :
    let := φ.toAlgebra
    (sphereIso φ n).inv.f n
      ((singleObjXSelf (.up ℤ) n (𝟙_ (ModuleCat A'))).inv (1 : A')) =
        (1 : A') ⊗ₜ[A] (singleObjXSelf (.up ℤ) n (𝟙_ (ModuleCat A))).inv (1 : A) := by
  let := φ.toAlgebra
  have hi := congrArg (fun z => (sphereIso φ n).inv.f n z) (sphereIso_one φ n)
  have hc := congrArg (fun f => f.f n
    ((1 : A') ⊗ₜ[A] (singleObjXSelf (.up ℤ) n (𝟙_ (ModuleCat A))).inv (1 : A)))
    (sphereIso φ n).hom_inv_id
  exact hi.symm.trans hc

set_option maxHeartbeats 800000 in
-- Hom 比較の全次数成分を評価して単位を照合する。
lemma homComparison_identity (K : Complex A) :
    (unitIso φ).inv ≫ (extension φ).map (identity K) ≫ homComparison φ K K =
      identity ((extension φ).obj K) := by
  let := φ.toAlgebra
  apply (unitCycleEquiv _).injective
  apply Subtype.ext
  change (homComparison φ K K).f 0
    ((ModuleCat.extendScalars φ).map ((identity K).f 0)
      ((unitIso φ).inv.f 0 ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A'))).inv (1 : A')))) = _
  erw [sphereIso_inv_one φ 0, ModuleCat.ExtendScalars.map_tmul φ]
  have hid : (identity K).f 0
      ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A)) = Cochain.ofHom (𝟙 K) := by
    exact congrArg Subtype.val (cycleFromUnit_unitFromCycle _ _)
  rw [hid]
  change (homComparison φ K K).f 0 ((1 : A') ⊗ₜ[A] Cochain.ofHom (𝟙 K)) =
    (cycleFromUnit _ (identity ((extension φ).obj K))).val
  rw [identity, cycleFromUnit_unitFromCycle]
  apply Cochain.ext₀
  intro i
  apply ((ModuleCat.extendRestrictScalarsAdj φ).homEquiv _ _).injective
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change ((homComparison φ K K).f 0 ((1 : A') ⊗ₜ[A] Cochain.ofHom (𝟙 K))).v i i (add_zero i)
    ((1 : A') ⊗ₜ[A] x) = (1 : A') ⊗ₜ[A] x
  erw [homComparison_apply φ K K 0 i i (add_zero i)]
  rfl

set_option maxHeartbeats 1600000 in
-- 二つの斉次 Hom と値の純粋生成元上で合成を比較する。
lemma homComparison_composition (K L M : Complex A) :
    (tensorIso φ (homComplex A K L) (homComplex A L M)).inv ≫
        (extension φ).map (enrichedComposition K L M) ≫ homComparison φ K M =
      (homComparison φ K L ⊗ₘ homComparison φ L M) ≫
        enrichedComposition ((extension φ).obj K) ((extension φ).obj L) ((extension φ).obj M) := by
  let := φ.toAlgebra
  apply (cancel_epi (tensorIso φ (homComplex A K L) (homComplex A L M)).hom).1
  rw [Iso.hom_inv_id_assoc]
  apply HomologicalComplex.hom_ext
  intro n
  apply cochainTensorBaseChange_hom_ext φ (homComplex A K L) (homComplex A L M)
  intro p q hpq
  apply ((ModuleCat.extendRestrictScalarsAdj φ).homEquiv _ _).injective
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro f g
  change (homComparison φ K M).f n
    ((ModuleCat.extendScalars φ).map ((enrichedComposition K L M).f n)
      ((1 : A') ⊗ₜ[A] ιTensorObj (homComplex A K L) (homComplex A L M) p q n hpq
        (f ⊗ₜ[A] g))) =
    (enrichedComposition _ _ _).f n
      ((homComparison φ K L ⊗ₘ homComparison φ L M).f n
        ((tensorIso φ (homComplex A K L) (homComplex A L M)).hom.f n
          ((1 : A') ⊗ₜ[A] ιTensorObj (homComplex A K L) (homComplex A L M) p q n hpq
            (f ⊗ₜ[A] g))))
  erw [ModuleCat.ExtendScalars.map_tmul φ, enrichedComposition_apply]
  erw [cochainTensorBaseChangeIso_apply_ι φ (homComplex A K L) (homComplex A L M)]
  erw [tensorMap_apply, enrichedComposition_apply]
  apply Cochain.ext
  intro i j hij
  apply ((ModuleCat.extendRestrictScalarsAdj φ).homEquiv _ _).injective
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change ((homComparison φ K M).f n ((1 : A') ⊗ₜ[A] ((p * q).negOnePow • f.comp g hpq))).v
    i j hij ((1 : A') ⊗ₜ[A] x) =
      ((p * q).negOnePow •
        ((homComparison φ K L).f p ((1 : A') ⊗ₜ[A] f)).comp
          ((homComparison φ L M).f q ((1 : A') ⊗ₜ[A] g)) hpq).v i j hij ((1 : A') ⊗ₜ[A] x)
  erw [homComparison_apply φ K M n i j hij]
  rw [Cochain.units_smul_v, Cochain.units_smul_v]
  rw [Cochain.comp_v f g hpq i (i + p) j rfl (by omega),
    Cochain.comp_v _ _ hpq i (i + p) j rfl (by omega)]
  change (1 : A') ⊗ₜ[A] ((p * q).negOnePow •
    g.v (i + p) j (by omega) (f.v i (i + p) rfl x)) =
      (p * q).negOnePow •
        ((homComparison φ L M).f q ((1 : A') ⊗ₜ[A] g)).v (i + p) j (by omega)
          (((homComparison φ K L).f p ((1 : A') ⊗ₜ[A] f)).v i (i + p) rfl ((1 : A') ⊗ₜ[A] x))
  erw [homComparison_apply φ K L p i (i + p) rfl,
    homComparison_apply φ L M q (i + p) j (by omega)]
  simp only [Units.smul_def, TensorProduct.tmul_smul]
  rfl

/-- 複体の係数変更を、移送した自己豊穣構造からの dg 関手として読む。 -/
def complexDGFunctor : DGFunctor A' (DGBaseChange φ (Complex A)) (Complex A') where
  obj := (extension φ).obj
  map K L := homComparison φ K L
  map_id K := homComparison_identity φ K
  map_comp K L M := homComparison_composition φ K L M

end SerrePositivity.DifferentialGraded.ScalarExtension
