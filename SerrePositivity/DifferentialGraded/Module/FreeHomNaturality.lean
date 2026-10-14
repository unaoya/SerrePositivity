module
public import SerrePositivity.DifferentialGraded.Module.FreeHom
public import SerrePositivity.DifferentialGraded.Module.HomFunctor

/-! # 自由加群の全次数 Hom 同型の自然性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 自由 Hom 複体同型は値域の加群射に対して自然。 -/
lemma freeHomIso_naturality_target (x : D) (K : Complex A) {M N : ModuleCategory A D}
    (f : M ⟶ N) :
    eHomWhiskerLeft (Complex A) ((freeAt x).obj K) f ≫
      (freeHomIso A D x K (ForgetEnrichment.to (Complex A) N)).hom =
    (freeHomIso A D x K (ForgetEnrichment.to (Complex A) M)).hom ≫
      homPostcompose K ((moduleEvaluation A D x).map f) := by
  have hp := moduleHomWhiskerLeft_π A D (M := (freeAt x).obj K) f x
  have ht := congrArg (fun q :
      moduleHom A D (freeModule x K) (ForgetEnrichment.to (Complex A) M) ⟶
        homComplex A (K ⊗ (x ⟶[Complex A] x)) ((ForgetEnrichment.to (Complex A) N).obj (op x)) =>
    q ≫ homPrecompose (freeUnitInsert A x K) ((ForgetEnrichment.to (Complex A) N).obj (op x))) hp
  calc
    _ = (eHomWhiskerLeft (Complex A) ((freeAt x).obj K) f ≫
        moduleHomπ A D (freeModule x K) (ForgetEnrichment.to (Complex A) N) x) ≫
        homPrecompose (freeUnitInsert A x K) ((ForgetEnrichment.to (Complex A) N).obj (op x)) :=
      (Category.assoc _ _ _).symm
    _ = (moduleHomπ A D (freeModule x K) (ForgetEnrichment.to (Complex A) M) x ≫
        homPostcompose (K ⊗ (x ⟶[Complex A] x)) ((moduleEvaluation A D x).map f)) ≫
        homPrecompose (freeUnitInsert A x K) ((ForgetEnrichment.to (Complex A) N).obj (op x)) := ht
    _ = _ := by
      have hc := homPostcompose_precompose A (freeUnitInsert A x K)
        ((moduleEvaluation A D x).map f)
      have he := congrArg (fun q :
          homComplex A (K ⊗ (x ⟶[Complex A] x)) ((ForgetEnrichment.to (Complex A) M).obj (op x)) ⟶
            homComplex A K ((ForgetEnrichment.to (Complex A) N).obj (op x)) =>
        moduleHomπ A D (freeModule x K) (ForgetEnrichment.to (Complex A) M) x ≫ q) hc
      exact (Category.assoc _ _ _).trans (he.trans (Category.assoc _ _ _).symm)

omit [Small.{u} D] in
/-- 自由生成元の単位挿入は生成する複体の chain map に対して自然。 -/
lemma freeUnitInsert_naturality (x : D) {K L : Complex A} (g : L ⟶ K) :
    freeUnitInsert A x L ≫ (g ⊗ₘ 𝟙 (x ⟶[Complex A] x)) = g ≫ freeUnitInsert A x K := by
  dsimp only [freeUnitInsert]
  rw [Category.assoc, tensorHom_comp_tensorHom]
  simp only [Category.id_comp, Category.comp_id]
  rw [rightUnitor_inv_comp_tensorHom]
  simp only [id_tensorHom]

/-- 自由 Hom 複体同型は生成する複体の chain map に対して反変に自然。 -/
lemma freeHomIso_naturality_source (x : D) {K L : Complex A} (g : L ⟶ K)
    (M : ModuleCategory A D) :
    eHomWhiskerRight (Complex A) ((freeAt x).map g) M ≫
      (freeHomIso A D x L (ForgetEnrichment.to (Complex A) M)).hom =
    (freeHomIso A D x K (ForgetEnrichment.to (Complex A) M)).hom ≫
      homPrecompose g ((moduleEvaluation A D x).obj M) := by
  have hp := moduleHomWhiskerRight_π A D ((freeAt x).map g) (P := M) x
  have ht := congrArg (fun q :
      moduleHom A D (freeModule x K) (ForgetEnrichment.to (Complex A) M) ⟶
        homComplex A (L ⊗ (x ⟶[Complex A] x)) ((ForgetEnrichment.to (Complex A) M).obj (op x)) =>
    q ≫ homPrecompose (freeUnitInsert A x L) ((ForgetEnrichment.to (Complex A) M).obj (op x))) hp
  have hg : (moduleEvaluation A D x).map ((freeAt x).map g) =
      g ⊗ₘ 𝟙 (x ⟶[Complex A] x) := tensorModuleMap_eval g (representable A x) x
  have hi : freeUnitInsert A x L ≫ (moduleEvaluation A D x).map ((freeAt x).map g) =
      g ≫ freeUnitInsert A x K := by
    rw [hg]
    exact freeUnitInsert_naturality A D x g
  calc
    _ = (eHomWhiskerRight (Complex A) ((freeAt x).map g) M ≫
        moduleHomπ A D (freeModule x L) (ForgetEnrichment.to (Complex A) M) x) ≫
        homPrecompose (freeUnitInsert A x L) ((ForgetEnrichment.to (Complex A) M).obj (op x)) :=
      (Category.assoc _ _ _).symm
    _ = (moduleHomπ A D (freeModule x K) (ForgetEnrichment.to (Complex A) M) x ≫
        homPrecompose ((moduleEvaluation A D x).map ((freeAt x).map g))
          ((ForgetEnrichment.to (Complex A) M).obj (op x))) ≫
        homPrecompose (freeUnitInsert A x L) ((ForgetEnrichment.to (Complex A) M).obj (op x)) := ht
    _ = _ := by
      rw [Category.assoc, ← homPrecompose_comp, hi, homPrecompose_comp]
      rfl
/-- 全次数 Hom 複体同型の閉零制限は通常の自由評価随伴の Hom 同値と一致する。 -/
lemma freeHomIso_closed_zero (x : D) (K : Complex A) (M : ModuleCategory A D)
    (f : (freeAt x).obj K ⟶ M) :
    mapFromUnit A K ((ForgetEnrichment.to (Complex A) M).obj (op x))
      (ForgetEnrichment.homTo (Complex A) (C := RightModule A D)
          (X := (freeAt x).obj K) (Y := M) f ≫
        (freeHomIso A D x K (ForgetEnrichment.to (Complex A) M)).hom) =
      freeHomEquiv A D x K M f := by
  apply Cochain.ofHom_injective
  rw [mapFromUnit_cochain, cycleFromUnit_postcomp]
  apply Cochain.ext₀
  intro k
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro t
  change ((freeHomEvaluation A D x K (ForgetEnrichment.to (Complex A) M)).f 0
    (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) (C := RightModule A D) f)).val).v
      k k (add_zero k) t = _
  rw [freeHomEvaluation_apply]
  have he := moduleEvaluation_cochain A D x f
  have hv := congrArg (fun z : Homogeneous (K ⊗ (x ⟶[Complex A] x))
      ((ForgetEnrichment.to (Complex A) M).obj (op x)) 0 =>
    z.v k k (add_zero k)
      (ιTensorObj K (x ⟶[Complex A] x) k 0 k (add_zero k)
        (t ⊗ₜ[A] (unitElement A x).val))) he
  calc
    _ = ((moduleEvaluation A D x).map f).f k
        (ιTensorObj K (x ⟶[Complex A] x) k 0 k (add_zero k)
          (t ⊗ₜ[A] (unitElement A x).val)) := hv.symm
    _ = (Cochain.ofHom (freeHomEquiv A D x K M f)).v k k (add_zero k) t := by
      rw [Cochain.ofHom_v, freeHomEquiv_apply]
end SerrePositivity.DifferentialGraded
