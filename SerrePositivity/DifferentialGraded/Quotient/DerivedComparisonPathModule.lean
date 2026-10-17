module
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonPathFlatness
public import SerrePositivity.DifferentialGraded.Quotient.PathComposition
public import SerrePositivity.DifferentialGraded.Module.Free
public import SerrePositivity.DifferentialGraded.Complexes.TensorRightComposition
public import SerrePositivity.DifferentialGraded.Complexes.RightTripleCochainExt
public import SerrePositivity.DifferentialGraded.Module.ActionChain

/-! # 内部 path 項の右 dg 加群構造

正の path は代表加群への右 tensor として構成する。最終微分の ε 消去は含めない。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex Opposite
variable {A : Type u} [CommRing A]

/-- 右 tensor の豊穣関手。 -/
def pathTensorRightDG (K : Complex A) : DGFunctor A (Complex A) (Complex A) where
  obj P := P ⊗ K
  map P Q := tensorRightHom K P Q
  map_id P := by
    apply (unitCycleEquiv _).injective
    apply Subtype.ext
    change (cycleFromUnit _ (identity P ≫ tensorRightHom K P P)).val =
      (cycleFromUnit _ (identity (P ⊗ K))).val
    rw [cycleFromUnit_postcomp, identity, identity, cycleFromUnit_unitFromCycle,
      cycleFromUnit_unitFromCycle]
    change (tensorRightHom K P P).f 0 (Cochain.ofHom (𝟙 P)) =
      Cochain.ofHom (𝟙 (P ⊗ K))
    rw [tensorRightHom_ofHom, id_whiskerRight]
  map_comp P Q T := by
    apply tensorHom_ext
    intro p q m hm
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro f g
    change (tensorRightHom K P T).f m
      ((enrichedComposition P Q T).f m
        (ιTensorObj (homComplex A P Q) (homComplex A Q T) p q m hm (f ⊗ₜ[A] g))) =
      (enrichedComposition _ _ _).f m
        ((tensorRightHom K P Q ⊗ₘ tensorRightHom K Q T).f m
          (ιTensorObj (homComplex A P Q) (homComplex A Q T) p q m hm (f ⊗ₜ[A] g)))
    rw [tensorMap_apply, enrichedComposition_apply, enrichedComposition_apply,
      chain_units_smul, tensorRightHom_cochain_comp]

/-- 全次数の右 tensor 作用の tensor 転置。 -/
lemma pathTensorRight_uncurry {H P Q : Complex A} (K : Complex A)
    (f : H ⟶ homComplex A P Q) :
    uncurryRight (f ≫ tensorRightHom K P Q) =
      (α_ H P K).inv ≫ (uncurryRight f ▷ K) := by
  apply rightTriple_ext
  intro i j k n hn
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro a t
  induction t using TensorProduct.inductionOn with
  | tmul b c =>
    change (uncurryRight (f ≫ tensorRightHom K P Q)).f n
      (ιTensorObj H (P ⊗ K) i (j + k) n hn
        (a ⊗ₜ[A] ιTensorObj P K j k (j + k) rfl (b ⊗ₜ[A] c))) = _
    rw [uncurryRight_apply]
    change ((tensorRightHom K P Q).f i (f.f i a)).v (j + k) n (by omega)
      (ιTensorObj P K j k (j + k) rfl (b ⊗ₜ[A] c)) = _
    rw [tensorRightHom_apply_of_sum K P Q i j k (j + k) (i + j) n rfl (by omega) (by omega)]
    change _ = (uncurryRight f ▷ K).f n ((α_ H P K).inv.f n
      (ιTensorObj H (P ⊗ K) i (j + k) n hn
        (a ⊗ₜ[A] ιTensorObj P K j k (j + k) rfl (b ⊗ₜ[A] c))))
    rw [associator_inv_apply, whiskerRight_apply, uncurryRight_apply]
  | add t t' ht ht' =>
    simpa only [TensorProduct.tmul_add, map_add] using congrArg₂ (· + ·) ht ht'

lemma pathTensorRight_swap (K P Q : Complex A) :
    tensorRightHom K P Q ≫ homPostcompose (P ⊗ K) (signedSwap Q K).hom =
      tensorLeftHom K P Q ≫ homPrecompose (signedSwap P K).hom (K ⊗ Q) := by
  have hs : (signedSwap K Q).hom ≫ (signedSwap Q K).hom = 𝟙 (K ⊗ Q) :=
    SymmetricCategory.symmetry K Q
  change (tensorLeftHom K P Q ≫ homPrecompose (signedSwap P K).hom (K ⊗ Q) ≫
    (homFunctor (P ⊗ K)).map (signedSwap K Q).hom) ≫
      (homFunctor (P ⊗ K)).map (signedSwap Q K).hom = _
  rw [Category.assoc, Category.assoc, ← CategoryTheory.Functor.map_comp, hs,
    CategoryTheory.Functor.map_id]
  change tensorLeftHom K P Q ≫ homPrecompose (signedSwap P K).hom (K ⊗ Q) ≫
    𝟙 (homComplex A (P ⊗ K) (K ⊗ Q)) = _
  rw [Category.comp_id]

variable (A) (D : Type v) [DGCategory A D]

/-- 元の圏を始点方向に動かす内部 path 項の右 dg 加群。 -/
def pathModule {S : Set D} (w : Word S) (z : D) : RightModule A D :=
  match w with
  | [] => representable A z
  | b :: w => (representable A b.val).toFunctor.comp
      (pathTensorRightDG (pathSuffixWeight A D w b z))

/-- 加群の値と元の path 項の明示的な複体同型。 -/
def pathModuleValueIso {S : Set D} (w : Word S) (z : D) (x : Dᵒᵖ) :
    (pathModule A D w z).obj x ≅ term A D w x.unop z := by
  cases w <;> exact Iso.refl _

/-- path 加群の作用は、指定した先頭 Hom の合成そのものである。 -/
lemma pathModule_action {S : Set D} (w : Word S) (z : D) (x y : Dᵒᵖ) :
    ((x ⟶[Complex A] y) ◁ (pathModuleValueIso A D w z x).inv) ≫
      moduleActionChain A (pathModule A D w z) x y ≫
        (pathModuleValueIso A D w z y).hom =
      prependMap A D w y.unop x.unop z := by
  cases w with
  | nil =>
    change (homObject A D y.unop x.unop ◁ 𝟙 (homObject A D x.unop z)) ≫
      uncurryRight (curryRight (eComp (Complex A) y.unop x.unop z)) ≫
        𝟙 (homObject A D y.unop z) = _
    rw [whiskerLeft_id, Category.id_comp, Category.comp_id, uncurryRight_curryRight]
    rfl
  | cons b w =>
    change (homObject A D y.unop x.unop ◁
      𝟙 (homObject A D x.unop b.val ⊗ pathSuffixWeight A D w b z)) ≫
      uncurryRight (representableMap A b.val x y ≫
      tensorRightHom (pathSuffixWeight A D w b z)
        (homObject A D x.unop b.val) (homObject A D y.unop b.val)) ≫
          𝟙 (homObject A D y.unop b.val ⊗ pathSuffixWeight A D w b z) = _
    rw [whiskerLeft_id, Category.id_comp, Category.comp_id]
    rw [pathTensorRight_uncurry]
    change (α_ _ _ _).inv ≫ (uncurryRight (curryRight
      (eComp (Complex A) y.unop x.unop b.val)) ▷ _) = _
    rw [uncurryRight_curryRight]
    rfl

lemma pathModule_action_value {S : Set D} (w : Word S) (z : D) (x y : Dᵒᵖ) :
    moduleActionChain A (pathModule A D w z) x y ≫ (pathModuleValueIso A D w z y).hom =
      ((x ⟶[Complex A] y) ◁ (pathModuleValueIso A D w z x).hom) ≫
        prependMap A D w y.unop x.unop z := by
  have h := congrArg (fun f => ((x ⟶[Complex A] y) ◁
    (pathModuleValueIso A D w z x).hom) ≫ f) (pathModule_action A D w z x y)
  simpa only [← Category.assoc, ← MonoidalCategory.whiskerLeft_comp,
    Iso.hom_inv_id, whiskerLeft_id, Category.id_comp] using h

variable [Small.{u} D]

/-- 正の path は、先頭の殺す対象における自由右加群と同型。 -/
def pathModuleFreeIso {S : Set D} (b : S) (w : Word S) (z : D) :
    ForgetEnrichment.of (Complex A) (pathModule A D (b :: w) z) ≅
      (freeAt b.val).obj (pathSuffixWeight A D w b z) :=
  moduleIsoMk A D
    (fun x => signedSwap (homObject A D x.unop b.val) (pathSuffixWeight A D w b z)) (by
      intro x y
      change (representableMap A b.val x y ≫ tensorRightHom _ _ _) ≫
        homPostcompose _ (signedSwap _ _).hom =
          (representableMap A b.val x y ≫ tensorLeftHom _ _ _) ≫
            homPrecompose (signedSwap _ _).hom _
      rw [Category.assoc, pathTensorRight_swap, Category.assoc])

end SerrePositivity.DifferentialGraded.DGQuotient
