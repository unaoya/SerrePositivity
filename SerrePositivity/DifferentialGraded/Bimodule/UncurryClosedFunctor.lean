module
public import SerrePositivity.DifferentialGraded.Bimodule.TensorModuleFull
public import SerrePositivity.DifferentialGraded.Bimodule.UncurryRestriction
public import SerrePositivity.DifferentialGraded.Bimodule.Isomorphism
public import SerrePositivity.DifferentialGraded.Module.Isomorphism

/-! # 全Hom自然な閉零bimodule射の明示的なuncurry関手 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.BimoduleTensorModule
open CategoryTheory Opposite
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]

/-- 既存のuncurryHom自然性を主Hom endの閉零射へ束ねる。 -/
def uncurryMap {M N : BimoduleCategory A B C} (f : M ⟶ N) :
    objectPreimage A B C M ⟶ objectPreimage A B C N :=
  leftModuleMorphismMk A (DGTensorCategory A Bᵒᵖ C)
    (M := (BimoduleCategory.underlying A B C M).toTensorFunctor)
    (N := (BimoduleCategory.underlying A B C N).toTensorFunctor)
    (fun x => (BimoduleCategory.valueEvaluation A B C x.1.unop x.2).map f)
    (BimoduleCategory.valueMap_uncurry_naturality A B C f)

@[simp]
lemma uncurryMap_eval {M N : BimoduleCategory A B C} (f : M ⟶ N)
    (x : DGTensorCategory A Bᵒᵖ C) :
    (leftModuleEvaluation A (DGTensorCategory A Bᵒᵖ C) x).map (uncurryMap A B C f) =
      (BimoduleCategory.valueEvaluation A B C x.1.unop x.2).map f :=
  leftModuleMorphismMk_eval A (DGTensorCategory A Bᵒᵖ C) _ _ x

/-- 選択された逆関手を使わない、値と両作用を保持するuncurry。 -/
def uncurryFunctor : BimoduleCategory A B C ⥤ BimoduleTensorModuleCategory A B C where
  obj := objectPreimage A B C
  map := uncurryMap A B C
  map_id M := by
    apply leftModuleMorphism_ext
    intro x
    rw [uncurryMap_eval, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
    rfl
  map_comp f g := by
    apply leftModuleMorphism_ext
    intro x
    rw [uncurryMap_eval, CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
      uncurryMap_eval, uncurryMap_eval]

/-- uncurryの戻りを、各値で恒等の右加群同型として比較する。 -/
def uncurryRightCounitIso (M : BimoduleCategory A B C) (c : C) :
    (BimoduleCategory.evaluation A B C c).obj ((functor A B C).obj (objectPreimage A B C M)) ≅
      (BimoduleCategory.evaluation A B C c).obj M :=
  moduleIsoMk A B (fun _ => Iso.refl _) (by
    intro x y
    apply hom_naturality_of_apply
    intro p f
    simp only [Iso.refl_hom, CochainComplex.HomComplex.Cochain.comp_id,
      CochainComplex.HomComplex.Cochain.id_comp]
    exact congrArg (fun k => k.f p f)
      ((BimoduleCategory.underlying A B C M).uncurryHom_first c x y))

@[simp]
lemma uncurryRightCounitIso_hom_eval (M : BimoduleCategory A B C) (b : B) (c : C) :
    (moduleEvaluation A B b).map (uncurryRightCounitIso A B C M c).hom = 𝟙 _ :=
  moduleIsoMk_hom_eval A B _ _ b

lemma uncurryRightCounitIso_naturality (M : BimoduleCategory A B C) (c c' : C) :
    (BimoduleCategory.underlying A B C ((functor A B C).obj (objectPreimage A B C M))).map c c' ≫
      moduleHomPostcompose A B
        ((BimoduleCategory.underlying A B C M).toTensorFunctor.toBimodule.rightAt c)
        ((BimoduleCategory.underlying A B C M).toTensorFunctor.toBimodule.rightAt c')
        ((BimoduleCategory.underlying A B C M).rightAt c')
        (uncurryRightCounitIso A B C M c').hom =
    (BimoduleCategory.underlying A B C M).map c c' ≫
      moduleHomPrecompose A B
        ((BimoduleCategory.underlying A B C M).toTensorFunctor.toBimodule.rightAt c)
        ((BimoduleCategory.underlying A B C M).rightAt c)
        ((BimoduleCategory.underlying A B C M).rightAt c')
        (uncurryRightCounitIso A B C M c).hom := by
  apply moduleHom_ext
  intro b
  simp only [Category.assoc]
  rw [moduleHomPostcompose_π, moduleHomPrecompose_π]
  simp only [moduleMorphismComponent, uncurryRightCounitIso_hom_eval]
  have h := (BimoduleCategory.underlying A B C M).toTensorFunctor.toBimodule_map_π c c' b
  have hh := h.trans ((BimoduleCategory.underlying A B C M).uncurryHom_second b c c')
  have hn :
      ((BimoduleCategory.underlying A B C ((functor A B C).obj
          (objectPreimage A B C M))).leftAt b).map c c' ≫ homPostcompose _ (𝟙 _) =
      ((BimoduleCategory.underlying A B C M).leftAt b).map c c' ≫ homPrecompose (𝟙 _) _ := by
    apply hom_naturality_of_apply
    intro p f
    refine (CochainComplex.HomComplex.Cochain.comp_id _).trans ?_
    exact (congrArg (fun k => k.f p f) hh).trans
      (CochainComplex.HomComplex.Cochain.id_comp _).symm
  change (_ ≫ moduleHomπ A B _ _ b) ≫ _ = (_ ≫ moduleHomπ A B _ _ b) ≫ _ at hn
  exact (Category.assoc _ _ _).symm.trans (hn.trans (Category.assoc _ _ _))

def uncurryObjectCounitIso (M : BimoduleCategory A B C) :
    (functor A B C).obj (objectPreimage A B C M) ≅ M :=
  BimoduleCategory.isoOfFamily A B C (uncurryRightCounitIso A B C M)
    (uncurryRightCounitIso_naturality A B C M)

@[simp]
lemma uncurryObjectCounitIso_hom_value (M : BimoduleCategory A B C) (b : B) (c : C) :
    (BimoduleCategory.valueEvaluation A B C b c).map (uncurryObjectCounitIso A B C M).hom = 𝟙 _ :=
  uncurryRightCounitIso_hom_eval A B C M b c

/-- 明示的uncurryから主bimoduleへの戻りは恒等関手と自然同型。 -/
def uncurryCounitIso : uncurryFunctor A B C ⋙ functor A B C ≅ 𝟭 (BimoduleCategory A B C) :=
  NatIso.ofComponents (uncurryObjectCounitIso A B C) (by
    intro M N f
    apply BimoduleCategory.value_hom_ext A B C
    intro b c
    simp only [Functor.comp_map, Functor.id_map, CategoryTheory.Functor.map_comp,
      functor_map_value, uncurryFunctor, uncurryMap_eval]
    rw [uncurryObjectCounitIso_hom_value A B C N b c,
      uncurryObjectCounitIso_hom_value A B C M b c]
    exact (Category.comp_id _).trans (Category.id_comp _).symm)

end SerrePositivity.DifferentialGraded.BimoduleTensorModule
