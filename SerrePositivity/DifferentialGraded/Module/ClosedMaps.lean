module
public import SerrePositivity.DifferentialGraded.Module.Underlying
public import SerrePositivity.DifferentialGraded.Complexes.ClosedMaps

/-! # 全次数自然な chain map 族から閉零加群射を構成する -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 閉零射族の全豊穣自然性は Hom chain map の可換式で検証できる。 -/
lemma closedFamily_naturality {M N : RightModule A D}
    (a : ∀ x : Dᵒᵖ, M.obj x ⟶ N.obj x)
    (h : ∀ x y : Dᵒᵖ, M.map x y ≫ homPostcompose (M.obj x) (a y) =
      N.map x y ≫ homPrecompose (a x) (N.obj y)) (x y : Dᵒᵖ) :
    (β_ (𝟙_ (Complex A)) (x ⟶[Complex A] y)).hom ≫
      (M.map x y ⊗ₘ closedMap A (a y)) ≫ enrichedComposition _ _ _ =
      (closedMap A (a x) ⊗ₘ N.map x y) ≫ enrichedComposition _ _ _ := by
  apply (cancel_epi (λ_ (x ⟶[Complex A] y)).inv).1
  rw [braiding_tensorUnit_left]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [rightUnitor_inv_comp_tensorHom_assoc, leftUnitor_inv_comp_tensorHom_assoc]
  rw [← homPostcompose_closedMap, ← homPrecompose_closedMap]
  exact h x y

/-- 全次数自然な通常 chain map 族を単位パラメータの豊穣自然変換にする。 -/
def closedFamilyTrans {M N : RightModule A D}
    (a : ∀ x : Dᵒᵖ, M.obj x ⟶ N.obj x)
    (h : ∀ x y : Dᵒᵖ, M.map x y ≫ homPostcompose (M.obj x) (a y) =
      N.map x y ≫ homPrecompose (a x) (N.obj y)) :
    ModuleParamTrans A D (𝟙_ (Complex A)) M N where
  app x := closedMap A (a x)
  naturality := closedFamily_naturality A (M := M) (N := N) a h

variable (D) [Small.{u} D]
/-- 全次数自然な chain map 族を主 Hom end の閉零加群射へ持ち上げる。 -/
def moduleMorphismMk {M N : RightModule A D}
    (a : ∀ x : Dᵒᵖ, M.obj x ⟶ N.obj x)
    (h : ∀ x y : Dᵒᵖ, M.map x y ≫ homPostcompose (M.obj x) (a y) =
      N.map x y ≫ homPrecompose (a x) (N.obj y)) :
    ForgetEnrichment.of (Complex A) M ⟶ ForgetEnrichment.of (Complex A) N :=
  ForgetEnrichment.homOf (Complex A) (C := RightModule A D) (X := M) (Y := N)
    ((moduleHomEquiv A D (𝟙_ (Complex A)) M N).symm
      (closedFamilyTrans A (M := M) (N := N) a h))

/-- 構成した加群射を評価すると元の chain map 成分に戻る。 -/
@[simp]
lemma moduleMorphismMk_eval {M N : RightModule A D}
    (a : ∀ x : Dᵒᵖ, M.obj x ⟶ N.obj x)
    (h : ∀ x y : Dᵒᵖ, M.map x y ≫ homPostcompose (M.obj x) (a y) =
      N.map x y ≫ homPrecompose (a x) (N.obj y)) (x : D) :
    (moduleEvaluation A D x).map (moduleMorphismMk A D (M := M) (N := N) a h) = a (op x) := by
  let c := closedFamilyTrans A (M := M) (N := N) a h
  have hp := moduleHomEquiv_symm_π A D (𝟙_ (Complex A)) M N c x
  have he := congrArg (fun t : 𝟙_ (Complex A) ⟶ homComplex A (M.obj (op x)) (N.obj (op x)) =>
    complexClosedHomEquiv A (M.obj (op x)) (N.obj (op x))
      (ForgetEnrichment.homOf (Complex A) (C := Complex A)
        (X := M.obj (op x)) (Y := N.obj (op x)) t)) hp
  calc
    _ = complexClosedHomEquiv A (M.obj (op x)) (N.obj (op x))
        (ForgetEnrichment.homOf (Complex A) (C := Complex A)
          (X := M.obj (op x)) (Y := N.obj (op x))
          ((moduleHomEquiv A D (𝟙_ (Complex A)) M N).symm c ≫
            moduleHomπ A D M N x)) := rfl
    _ = complexClosedHomEquiv A (M.obj (op x)) (N.obj (op x))
        (ForgetEnrichment.homOf (Complex A) (C := Complex A)
          (X := M.obj (op x)) (Y := N.obj (op x)) (c.app (op x))) := he
    _ = a (op x) := Equiv.apply_symm_apply (complexClosedHomEquiv A _ _) _
end SerrePositivity.DifferentialGraded
