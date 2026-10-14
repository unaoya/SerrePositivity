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
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
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

/-- 全豊穣自然性から Hom chain map の可換式を復元する。 -/
lemma closedFamily_naturality_converse {M N : RightModule A D}
    (a : ∀ x : Dᵒᵖ, M.obj x ⟶ N.obj x)
    (h : ∀ x y : Dᵒᵖ,
      (β_ (𝟙_ (Complex A)) (x ⟶[Complex A] y)).hom ≫
        (M.map x y ⊗ₘ closedMap A (a y)) ≫ enrichedComposition _ _ _ =
        (closedMap A (a x) ⊗ₘ N.map x y) ≫ enrichedComposition _ _ _) (x y : Dᵒᵖ) :
    M.map x y ≫ homPostcompose (M.obj x) (a y) =
      N.map x y ≫ homPrecompose (a x) (N.obj y) := by
  have hh := congrArg (fun f => (λ_ (x ⟶[Complex A] y)).inv ≫ f) (h x y)
  rw [braiding_tensorUnit_left] at hh
  simp only [Category.assoc, Iso.inv_hom_id_assoc] at hh
  rw [rightUnitor_inv_comp_tensorHom_assoc, leftUnitor_inv_comp_tensorHom_assoc,
    ← homPostcompose_closedMap, ← homPrecompose_closedMap] at hh
  exact hh

/-- 単位パラメータの全次数自然変換の通常 chain map 成分。 -/
abbrev closedTransApp {M N : RightModule A D}
    (τ : ModuleParamTrans A D (𝟙_ (Complex A)) M N) (x : Dᵒᵖ) : M.obj x ⟶ N.obj x :=
  mapFromUnit A (M.obj x) (N.obj x) (τ.app x)

/-- 通常 chain map として読んだ成分も全次数 Hom に関して自然。 -/
lemma closedTransApp_naturality {M N : RightModule A D}
    (τ : ModuleParamTrans A D (𝟙_ (Complex A)) M N) (x y : Dᵒᵖ) :
    M.map x y ≫ homPostcompose (M.obj x) (closedTransApp A τ y) =
      N.map x y ≫ homPrecompose (closedTransApp A τ x) (N.obj y) := by
  apply closedFamily_naturality_converse A (M := M) (N := N)
    (closedTransApp A τ) (fun x y => ?_) x y
  have hx := closedMap_mapFromUnit A (M.obj x) (N.obj x) (τ.app x)
  have hy := closedMap_mapFromUnit A (M.obj y) (N.obj y) (τ.app y)
  change closedMap A (closedTransApp A τ x) = τ.app x at hx
  change closedMap A (closedTransApp A τ y) = τ.app y at hy
  rw [hx, hy]
  exact τ.naturality x y

/-- 全次数自然な通常 chain map 族を単位パラメータの豊穣自然変換にする。 -/
def closedFamilyTrans {M N : RightModule A D}
    (a : ∀ x : Dᵒᵖ, M.obj x ⟶ N.obj x)
    (h : ∀ x y : Dᵒᵖ, M.map x y ≫ homPostcompose (M.obj x) (a y) =
      N.map x y ≫ homPrecompose (a x) (N.obj y)) :
    ModuleParamTrans A D (𝟙_ (Complex A)) M N where
  app x := closedMap A (a x)
  naturality := closedFamily_naturality A (M := M) (N := N) a h

/-- Hom chain map の全次数可換式を作用上で評価する。 -/
lemma closedFamily_action {M N : RightModule A D}
    (a : ∀ x : Dᵒᵖ, M.obj x ⟶ N.obj x)
    (h : ∀ x y : Dᵒᵖ, M.map x y ≫ homPostcompose (M.obj x) (a y) =
      N.map x y ≫ homPrecompose (a x) (N.obj y))
    (x y : Dᵒᵖ) (p r n : ℤ) (hn : r + p = n)
    (f : GradedHom A x y p) (v : (M.obj x).X r) :
    (a y).f n (moduleAction A M f v hn) =
      moduleAction A N f ((a x).f r v) hn := by
  have hh := congrArg (fun t => t.f p f) (h x y)
  change (((M.map x y).f p f).comp (Cochain.ofHom (a y)) (add_zero p)) =
    (Cochain.ofHom (a x)).comp ((N.map x y).f p f) (zero_add p) at hh
  have hv := congrArg (fun c => c.v r n hn v) hh
  rw [Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v,
    Cochain.ofHom_v, Cochain.ofHom_v] at hv
  exact hv

/-- 全次数作用の可換式から Hom chain map の可換式を復元する。 -/
lemma closedFamily_of_action {M N : RightModule A D}
    (a : ∀ x : Dᵒᵖ, M.obj x ⟶ N.obj x)
    (h : ∀ (x y : Dᵒᵖ) (p r n : ℤ) (hn : r + p = n)
      (f : GradedHom A x y p) (v : (M.obj x).X r),
      (a y).f n (moduleAction A M f v hn) =
        moduleAction A N f ((a x).f r v) hn) (x y : Dᵒᵖ) :
    M.map x y ≫ homPostcompose (M.obj x) (a y) =
      N.map x y ≫ homPrecompose (a x) (N.obj y) := by
  apply HomologicalComplex.Hom.ext
  funext p
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  change (((M.map x y).f p f).comp (Cochain.ofHom (a y)) (add_zero p)) =
    (Cochain.ofHom (a x)).comp ((N.map x y).f p f) (zero_add p)
  apply Cochain.ext
  intro r n hn
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro v
  rw [Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v,
    Cochain.ofHom_v, Cochain.ofHom_v]
  exact h x y p r n hn f v

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
/-- 全次数の Hom 可換式を持つ通常 chain map 族。 -/
abbrev ModuleMapFamily (M N : RightModule A D) :=
  { a : ∀ x : Dᵒᵖ, M.obj x ⟶ N.obj x //
    ∀ x y : Dᵒᵖ, M.map x y ≫ homPostcompose (M.obj x) (a y) =
      N.map x y ≫ homPrecompose (a x) (N.obj y) }

/-- 閉零自然変換として読んだ加群射の成分は評価関手の射。 -/
lemma moduleClosedHomEquiv_app {M N : ModuleCategory A D} (f : M ⟶ N) (x : D) :
    closedTransApp A (moduleClosedHomEquiv A D M N f) (op x) =
      (moduleEvaluation A D x).map f := rfl

/-- 主 end の閉零射と全次数自然な chain map 族の同値。 -/
def moduleMapFamilyEquiv (M N : ModuleCategory A D) :
    (M ⟶ N) ≃ ModuleMapFamily A D (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) N) where
  toFun f := ⟨closedTransApp A (moduleClosedHomEquiv A D M N f),
    closedTransApp_naturality A (moduleClosedHomEquiv A D M N f)⟩
  invFun a := moduleMorphismMk A D a.val a.property
  left_inv f := by
    apply moduleMorphism_ext
    intro x
    rw [moduleMorphismMk_eval]
    exact moduleClosedHomEquiv_app A D f x
  right_inv a := by
    apply Subtype.ext
    funext x
    change closedTransApp A (moduleClosedHomEquiv A D M N
      (moduleMorphismMk A D a.val a.property)) x = a.val x
    rw [moduleClosedHomEquiv_app A D _ x.unop, moduleMorphismMk_eval]
end SerrePositivity.DifferentialGraded
