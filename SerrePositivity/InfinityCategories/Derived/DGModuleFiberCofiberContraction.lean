module
public import SerrePositivity.InfinityCategories.Derived.DGModuleFiberCofiberSectionFirst
public import SerrePositivity.InfinityCategories.Derived.DGModuleFiberNullHomotopy

/-! # 双対比較の収縮の次数零成分

概要：M→fiber(f) の次数零成分 T と、その微分・射影成分を計算する。
方針：shift の閉斉次単位を cone の左包含へ合成する。
規約：dT は逆射の第一成分と f の合成。使われ方：β3 の双対比較の原始元。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable {M N : ModuleCategory A D}

/-- 全 Hom end の合成は右因子の負号を保つ。 -/
lemma dgModuleCompose_neg_right {X Y Z : RightModule A D} {p q r : ℤ}
    (g : GradedHom A Y Z q) (z : GradedHom A X Y p) (h : p + q = r) :
    compose A g (-z) h = -compose A g z h := by
  have he := compose_sub_right (A := A) g (0 : GradedHom A X Y p) z h
  simpa only [zero_sub, compose_zero] using he

/-- 収縮の M→fiber(f) の次数零成分。 -/
def dgModuleFiberCofiberContractionT (f : M ⟶ N) :
    GradedHom A (ForgetEnrichment.to (Complex A) M) (dgModuleFiber A D f) 0 :=
  (dgModuleNegativeShiftTargetHomEquiv A D (ForgetEnrichment.to (Complex A) M)
    (ForgetEnrichment.to (Complex A) (moduleCone A D f)) (-1)).symm
      (moduleConeInlElement A D f)

/-- T の標準射影は M の単位。 -/
lemma dgModuleFiberCofiberContractionT_projection (f : M ⟶ N) :
    compose A (dgModuleFiberProjectionElement A D f)
      (dgModuleFiberCofiberContractionT A D f) (zero_add 0) =
      (unitElement A (ForgetEnrichment.to (Complex A) M)).val := by
  rw [dgModuleFiberProjection_compose A D f (-1), dgModuleFiberCofiberContractionT,
    LinearEquiv.apply_symm_apply, moduleCone_inl_fst]

/-- T の零ホモトピー成分は零。 -/
lemma dgModuleFiberCofiberContractionT_nullHomotopy (f : M ⟶ N) :
    compose A (dgModuleFiberNullHomotopy A D f)
      (dgModuleFiberCofiberContractionT A D f) (zero_add (-1)) = 0 := by
  rw [dgModuleFiberNullHomotopy_compose A D f (-1), dgModuleFiberCofiberContractionT,
    LinearEquiv.apply_symm_apply, moduleCone_inl_snd, neg_zero]

/-- T の微分は逆射の第一成分と元の射の合成。 -/
lemma dgModuleFiberCofiberContractionT_differential (f : M ⟶ N) :
    (moduleHom A D (ForgetEnrichment.to (Complex A) M) (dgModuleFiber A D f)).d 0 1
      (dgModuleFiberCofiberContractionT A D f) =
      compose A (dgModuleFiberCofiberSectionFirst A D f)
        (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) f)).val (zero_add 1) := by
  have hd := dgModuleNegativeShiftTargetHomEquiv_symm_differential A D
    (ForgetEnrichment.to (Complex A) M)
    (ForgetEnrichment.to (Complex A) (moduleCone A D f)) (-1) (moduleConeInlElement A D f)
  have hi : differential (D := RightModule A D) A (moduleConeInlElement A D f) =
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) (f ≫ moduleConeInr A D f))).val :=
    moduleConeInlElement_d A D f
  rw [hi, dgModuleClosedCycle_comp] at hd
  change (moduleHom A D (ForgetEnrichment.to (Complex A) M) (dgModuleFiber A D f)).d 0 1
    (dgModuleFiberCofiberContractionT A D f) =
    -compose A
      (moduleShiftInElement A D (-1) (ForgetEnrichment.to (Complex A) (moduleCone A D f)))
      (compose A (moduleConeInrElement A D f)
        (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) f)).val (zero_add 0))
      (zero_add 1) at hd
  rw [hd, dgModuleFiberCofiberSectionFirst, dgModuleCompose_neg_left]
  exact congrArg Neg.neg (compose_assoc_of_sum (A := A)
    (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) f)).val (moduleConeInrElement A D f)
    (moduleShiftInElement A D (-1) (ForgetEnrichment.to (Complex A) (moduleCone A D f)))
    (zero_add 0) (zero_add 1) (zero_add 1))

end SerrePositivity.InfinityCategories
