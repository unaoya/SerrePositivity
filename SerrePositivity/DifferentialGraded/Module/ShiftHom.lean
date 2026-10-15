module
public import SerrePositivity.DifferentialGraded.Module.Shift
public import SerrePositivity.DifferentialGraded.Module.HomFunctor

/-! # 整数 shift の全次数加群 Hom chain map -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 全次数自然変換を shift の dg 関手で後合成する。パラメータは動かさない。 -/
def shiftModuleParamTrans (s : ℤ) {K : Complex A} {M N : RightModule A D}
    (τ : ModuleParamTrans A D K M N) :
    ModuleParamTrans A D K (shiftModule s M) (shiftModule s N) where
  app x := τ.app x ≫ shiftHom s (M.obj x) (N.obj x)
  naturality x y := by
    let a : ∀ z : Dᵒᵖ, K ⟶ homComplex A (M.obj z) (N.obj z) := fun z => τ.app z
    have ha : (β_ K (x ⟶[Complex A] y)).hom ≫
        (M.map x y ⊗ₘ a y) ≫ enrichedComposition _ _ _ =
        (a x ⊗ₘ N.map x y) ≫ enrichedComposition _ _ _ := τ.naturality x y
    change (β_ K (x ⟶[Complex A] y)).hom ≫
      ((M.map x y ≫ shiftHom s _ _) ⊗ₘ (a y ≫ shiftHom s _ _)) ≫
        enrichedComposition _ _ _ =
      ((a x ≫ shiftHom s _ _) ⊗ₘ (N.map x y ≫ shiftHom s _ _)) ≫
        enrichedComposition _ _ _
    rw [← tensorHom_comp_tensorHom_assoc, ← tensorHom_comp_tensorHom_assoc,
      ← shiftHom_comp, ← shiftHom_comp]
    simpa only [Category.assoc] using congrArg (fun f => f ≫ shiftHom s (M.obj x) (N.obj y)) ha

/-- Hom end の整数 shift。成分は次数 p で (-1)^(sp) を掛ける chain map。 -/
def moduleShiftHom (s : ℤ) (M N : RightModule A D) :
    moduleHom A D M N ⟶ moduleHom A D (shiftModule s M) (shiftModule s N) :=
  (moduleHomEquiv A D _ _ _).symm
    (shiftModuleParamTrans A D s (moduleHomEquiv A D _ M N (𝟙 _)))

@[reassoc]
lemma moduleShiftHom_π (s : ℤ) (M N : RightModule A D) (x : D) :
    moduleShiftHom A D s M N ≫ moduleHomπ A D (shiftModule s M) (shiftModule s N) x =
      moduleHomπ A D M N x ≫ shiftHom s (M.obj (op x)) (N.obj (op x)) := by
  rw [moduleShiftHom, moduleHomEquiv_symm_π]
  change (𝟙 _ ≫ moduleHomπ A D M N x) ≫ shiftHom s _ _ = _
  rw [Category.id_comp]

/-- 全次数 end の shift の成分。特に次数 −1 でも Koszul 符号を保持する。 -/
lemma moduleShiftHom_π_v (s : ℤ) (M N : RightModule A D) (x : D)
    (p i j : ℤ) (hij : i + p = j) (h : (moduleHom A D M N).X p) :
    ((moduleHomπ A D (shiftModule s M) (shiftModule s N) x).f p
      ((moduleShiftHom A D s M N).f p h)).v i j hij =
      (s * p).negOnePow • ((moduleHomπ A D M N x).f p h).v
        (i + s) (j + s) (by omega) := by
  have he := congrArg (fun f => f.f p h) (moduleShiftHom_π A D s M N x)
  change (moduleHomπ A D (shiftModule s M) (shiftModule s N) x).f p
      ((moduleShiftHom A D s M N).f p h) =
    (shiftHom s (M.obj (op x)) (N.obj (op x))).f p ((moduleHomπ A D M N x).f p h) at he
  rw [he, shiftHom_v]

lemma moduleShiftHom_identity (s : ℤ) (M : RightModule A D) :
    moduleIdentity A D M ≫ moduleShiftHom A D s M M =
      moduleIdentity A D (shiftModule s M) := by
  apply moduleHom_ext
  intro x
  rw [Category.assoc, moduleShiftHom_π, moduleIdentity_π,
    ← Category.assoc, moduleIdentity_π, shiftHom_identity]

lemma moduleShiftHom_comp (s : ℤ) (M N P : RightModule A D) :
    moduleComposition A D M N P ≫ moduleShiftHom A D s M P =
      (moduleShiftHom A D s M N ⊗ₘ moduleShiftHom A D s N P) ≫
        moduleComposition A D (shiftModule s M) (shiftModule s N) (shiftModule s P) := by
  apply moduleHom_ext
  intro x
  simp only [Category.assoc, moduleShiftHom_π, moduleComposition_π,
    moduleComposition_π_assoc]
  rw [shiftHom_comp]
  rw [tensorHom_comp_tensorHom_assoc (moduleShiftHom A D s M N)
    (moduleShiftHom A D s N P), moduleShiftHom_π, moduleShiftHom_π,
    tensorHom_comp_tensorHom_assoc]

/-- 整数 shift は加群圏の主モデルでも真の dg 関手。 -/
def moduleShiftDG (s : ℤ) : DGFunctor A (RightModule A D) (RightModule A D) where
  obj := shiftModule s
  map := moduleShiftHom A D s
  map_id := moduleShiftHom_identity A D s
  map_comp := moduleShiftHom_comp A D s

/-- 複体の閉零射の shift は全次数 Hom shift の次数零制限。 -/
lemma shiftHom_closedMap (s : ℤ) {P Q : Complex A} (f : P ⟶ Q) :
    closedMap A f ≫ shiftHom s P Q = closedMap A (f⟦s⟧') := by
  apply (unitCycleEquiv _).injective
  apply Subtype.ext
  change (cycleFromUnit _ (closedMap A f ≫ shiftHom s P Q)).val =
    (cycleFromUnit _ (closedMap A (f⟦s⟧'))).val
  rw [cycleFromUnit_postcomp, closedMap_cycle, shiftHom_ofHom, closedMap_cycle]

/-- 主 dg shift の閉零射の評価は、既存の複体 shift。 -/
lemma moduleShiftDG_map_eval (s : ℤ) {M N : ModuleCategory A D} (f : M ⟶ N) (x : D) :
    (moduleEvaluation A D x).map ((moduleShiftDG A D s).onClosed.map f) =
      ((moduleEvaluation A D x).map f)⟦s⟧' := by
  apply (complexClosedHomEquiv A _ _).symm.injective
  change closedMap A ((moduleEvaluation A D x).map ((moduleShiftDG A D s).onClosed.map f)) =
    closedMap A (((moduleEvaluation A D x).map f)⟦s⟧')
  rw [moduleEvaluation_closedMap]
  change (ForgetEnrichment.homTo (Complex A) (C := RightModule A D) (X := M) (Y := N) f ≫
    moduleShiftHom A D s (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) N)) ≫
    moduleHomπ A D (shiftModule s (ForgetEnrichment.to (Complex A) M))
      (shiftModule s (ForgetEnrichment.to (Complex A) N)) x = _
  rw [Category.assoc, moduleShiftHom_π, ← Category.assoc,
    ← moduleEvaluation_closedMap, shiftHom_closedMap]
  rfl

/-- 全次数 dg shift の閉零制限と U7 の具体的 shift は同じ射を持つ。 -/
lemma moduleShiftDG_map_eq (s : ℤ) {M N : ModuleCategory A D} (f : M ⟶ N) :
    (moduleShiftDG A D s).onClosed.map f = moduleShiftMap A D s f := by
  apply moduleMorphism_ext
  intro x
  rw [moduleShiftDG_map_eval, moduleShiftMap_eval]

lemma moduleShiftDG_onClosed_eq (s : ℤ) :
    (moduleShiftDG A D s).onClosed = moduleShiftFunctor A D s := by
  apply CategoryTheory.Functor.ext
  swap
  · intro M
    rfl
  · intro M N f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    change (moduleShiftDG A D s).onClosed.map f = moduleShiftMap A D s f
    exact moduleShiftDG_map_eq A D s f

end SerrePositivity.DifferentialGraded
