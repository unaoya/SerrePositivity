module
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.IntegralPerfectoid
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.Comparisons
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.RingCategories
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.RingCompletion


/-!
# 導来完備化 H⁰ の通常の環の関手

完備な標的への延長と、その標的圏の同値。
-/

universe u



@[expose] public noncomputable section Completion

namespace SerrePositivity.BhattScholze.PerfectoidizationInterface
open _root_.CategoryTheory
open _root_.SerrePositivity.DerivedCompletion
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (p : ℕ)

/-- 完備化 H⁰ の環自身も導来 p 完備である。 -/
theorem completionRing_complete (S : CommRingCat.{u}) :
    IsModuleComplete (completionRing p S) (p : completionRing p S)
      (ModuleCat.of (completionRing p S) (completionRing p S)) := by
  letI := (completionUnit p S).hom.toAlgebra
  have h : IsModuleComplete S (p : S) (ModuleCat.of S (completionRing p S)) :=
    principalCompletion_isModuleComplete_unit (p : S)
  have h' := (isModuleComplete_algebraMap_iff S (completionRing p S)
    (p : S) (completionRing p S)).mpr h
  simpa only [map_natCast] using h'

/-- 選んだ延長は元の単位との図式を満たす。 -/
@[simp] theorem completionLift_comp {S T : CommRingCat.{u}} (f : S ⟶ T)
    (hT : IsModuleComplete T (p : T) (ModuleCat.of T T)) :
    completionUnit p S ≫ completionLift p f hT = f :=
  (completion_existsUnique p f hT).choose_spec.1

/-- 環の射が誘導する H⁰ 完備化の射。 -/
def completionMap {S T : CommRingCat.{u}} (f : S ⟶ T) :
    completionRing p S ⟶ completionRing p T :=
  completionLift p (f ≫ completionUnit p T) (completionRing_complete p T)

/-- 誘導射は元の二つの単位と両立する。 -/
@[simp] theorem completionMap_comp {S T : CommRingCat.{u}} (f : S ⟶ T) :
    completionUnit p S ≫ completionMap p f = f ≫ completionUnit p T :=
  completionLift_comp p _ _

/-- 完備化の射は恒等射を保つ。 -/
@[simp] theorem completionMap_id (S : CommRingCat.{u}) : completionMap p (𝟙 S) = 𝟙 _ := by
  apply completion_hom_ext p (completionRing_complete p S)
  simp

/-- 完備化の射は合成を保つ。 -/
@[simp] theorem completionMap_comp_map {S T U : CommRingCat.{u}} (f : S ⟶ T) (g : T ⟶ U) :
    completionMap p (f ≫ g) = completionMap p f ≫ completionMap p g := by
  apply completion_hom_ext p (completionRing_complete p U)
  rw [completionMap_comp, ← Category.assoc, completionMap_comp,
    Category.assoc, Category.assoc, completionMap_comp]

/-- 通常の可換環上の導来完備化 H⁰ 関手。 -/
def ringCompletionFunctor : CommRingCat.{u} ⥤ CommRingCat.{u} where
  obj := completionRing p
  map := completionMap p
  map_id := completionMap_id p
  map_comp := completionMap_comp_map p

/-- 元の環が既に導来 p 完備なら、指定された単位は同型。 -/
def completionUnitIso (S : CommRingCat.{u})
    (hS : IsModuleComplete S (p : S) (ModuleCat.of S S)) : S ≅ completionRing p S where
  hom := completionUnit p S
  inv := completionLift p (𝟙 S) hS
  hom_inv_id := completionLift_comp p _ hS
  inv_hom_id := by
    apply completion_hom_ext p (completionRing_complete p S)
    simp [← Category.assoc]

/-- R 作用を元の構造射と完備化単位の合成に固定した H⁰ 完備化関手。 -/
def completionFunctor (R : Type u) [CommRing R] : A_R R ⥤ A_R R where
  obj S := Under.mk (S.hom ≫ completionUnit p S.right)
  map f := Under.homMk (completionMap p f.right) (by
    dsimp only [Under.mk_hom]
    rw [Category.assoc, completionMap_comp, ← Category.assoc, Under.w])
  map_id S := by ext1; exact completionMap_id p S.right
  map_comp f g := by ext1; exact completionMap_comp_map p f.right g.right

/-- 代数の H⁰ 完備化単位は、元の R 作用を保持する自然変換。 -/
def completionAlgebraUnit (R : Type u) [CommRing R] : 𝟭 (A_R R) ⟶ completionFunctor p R where
  app S := Under.homMk (completionUnit p S.right) rfl
  naturality := by intro S T f; ext1; exact (completionMap_comp p f.right).symm

/-- 完備代数上では、指定した代数の単位も同型になる。 -/
def completionAlgebraUnitIso (R : Type u) [CommRing R] (S : C_R R p) :
    S.obj ≅ (completionFunctor p R).obj S.obj :=
  Under.isoMk (completionUnitIso p S.obj.right S.property) rfl

variable [Fact p.Prime]

/-- 完備化の単位で前合成する、perfectoid 標的の制限関手。 -/
def targetRestriction (S : CommRingCat.{u}) :
    PerfUnder_u p (completionRing p S) ⥤ PerfUnder_u p S where
  obj T := ⟨(Under.map (completionUnit p S)).obj T.obj, T.property⟩
  map f := ObjectProperty.homMk ((Under.map (completionUnit p S)).map f.hom)

/-- perfectoid 標的への単位付き一意延長で作る逆向きの関手。 -/
def targetExtension (S : CommRingCat.{u}) :
    PerfUnder_u p S ⥤ PerfUnder_u p (completionRing p S) where
  obj T := ⟨Under.mk (completionLift p T.obj.hom (T.property.isModuleComplete T.obj.right p)),
    T.property⟩
  map {T U} f := ObjectProperty.homMk (Under.homMk f.hom.right (by
    dsimp only [Under.mk_hom]
    apply completion_hom_ext p (U.property.isModuleComplete U.obj.right p)
    rw [← Category.assoc, completionLift_comp, completionLift_comp]
    exact Under.w f.hom))
  map_id T := by ext1; ext1; rfl
  map_comp f g := by ext1; ext1; rfl

/-- Type u の全 perfectoid 標的の圏は H⁰ 完備化で変わらない。 -/
def completionTargetEquivalence (S : CommRingCat.{u}) :
    PerfUnder_u p (completionRing p S) ≌ PerfUnder_u p S where
  functor := targetRestriction p S
  inverse := targetExtension p S
  unitIso := NatIso.ofComponents (fun T => ObjectProperty.isoMk _
    (Under.isoMk (Iso.refl _) (by
      change T.obj.hom ≫ 𝟙 _ =
        completionLift p (completionUnit p S ≫ T.obj.hom)
          (T.property.isModuleComplete T.obj.right p)
      rw [Category.comp_id]
      apply completion_hom_ext p (T.property.isModuleComplete T.obj.right p)
      exact (completionLift_comp p (completionUnit p S ≫ T.obj.hom)
        (T.property.isModuleComplete T.obj.right p)).symm))) (by
          intro T U f
          ext1; ext1
          change f.hom.right ≫ 𝟙 _ = 𝟙 _ ≫ f.hom.right
          simp)
  counitIso := NatIso.ofComponents (fun T => ObjectProperty.isoMk _
    (Under.isoMk (Iso.refl _) (by
      change (completionUnit p S ≫ completionLift p T.obj.hom
        (T.property.isModuleComplete T.obj.right p)) ≫ 𝟙 _ = T.obj.hom
      rw [Category.comp_id, completionLift_comp]))) (by
        intro T U f
        ext1; ext1
        change f.hom.right ≫ 𝟙 _ = 𝟙 _ ≫ f.hom.right
        simp)
  functor_unitIso_comp := by
    intro T
    ext1; ext1
    change 𝟙 _ ≫ 𝟙 _ = 𝟙 _
    simp

/-- 制限関手で運んだ標的の R 作用は、完備化側で指定した作用と同じ。 -/
theorem targetRestriction_algebra (R : Type u) [CommRing R] (S : A_R R) :
    targetRestriction p S.right ⋙ targetAlgebra R p S =
      targetAlgebra R p ((completionFunctor p R).obj S) := by
  rfl

/-- 延長関手は完備化単位の図式により、元の標的の R 作用も保つ。 -/
theorem targetExtension_algebra (R : Type u) [CommRing R] (S : A_R R) :
    targetExtension p S.right ⋙ targetAlgebra R p ((completionFunctor p R).obj S) =
      targetAlgebra R p S := by
  refine CategoryTheory.Functor.ext (fun T => ?_) ?_
  · change Under.mk ((S.hom ≫ completionUnit p S.right) ≫ completionLift p T.obj.hom
        (T.property.isModuleComplete T.obj.right p)) = Under.mk (S.hom ≫ T.obj.hom)
    congr 1
    rw [Category.assoc, completionLift_comp]
  · intro T U f
    ext1
    simp [Under.eqToHom_right, targetExtension, targetAlgebra]

end SerrePositivity.BhattScholze.PerfectoidizationInterface

end Completion

/-! ## H⁰ の環構造と単位付き導来極限錐のデータ

概要：底の導来対象と無関係な環構造を許さず、辺と射影の乗法整合性を記録する。
方針：通常の R 代数の関手と加群の比較同型を持ち、実際の join 錐の脚を照合する。
規約：単位との両立は図式上の slice の辺として保持する。
使われ方：E3 界面の h0 と limitCone の型。
-/

