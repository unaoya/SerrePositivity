module

public import SerrePositivity.BhattScholze.PerfectoidizationInterface.Derived
public import SerrePositivity.CommutativeAlgebra.PerfectoidDerivedComplete
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PrincipalCompletionFunctor
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PrincipalCompletionDerivedComparison
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletionH0AlgebraUniversal
public import SerrePositivity.InfinityCategories.Core.TerminalMap

/-! # 通常の代数への導来完備化 H⁰ の包装

概要：実際の一変数 Koszul 完備化 H⁰ を環の関手にする。
方針：既存の単位と完備標的への環準同型の一意延長を用いる。
規約：通常の完備化との一致や有界 p 冪ねじれを仮定しない。
使われ方：非完備な始域の拡張と perfectoid 標的の添字圏の同値。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.PerfectoidizationInterface
open CategoryTheory
open SerrePositivity.DerivedCompletion
open SerrePositivity.InfinityCategories
open scoped Simplicial
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (p : ℕ)

/-- S の実際の導来 p 完備化の H⁰ 環。 -/
def completionRing (S : CommRingCat.{u}) : CommRingCat.{u} := by
  letI := principalCompletionCommRing S (p : S)
  exact CommRingCat.of (PrincipalCompletionH0 S (p : S))

/-- 元の Koszul 完備化単位を環の射として保持する。 -/
def completionUnit (S : CommRingCat.{u}) : S ⟶ completionRing p S := by
  letI := principalCompletionCommRing S (p : S)
  exact CommRingCat.ofHom (principalCompletionUnitRingHom S (p : S))

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

/-- 離散標的の完備性を、指定された元の環準同型に沿って制限する。 -/
theorem complete_along_map {S T : CommRingCat.{u}} (f : S ⟶ T)
    (hT : IsModuleComplete T (p : T) (ModuleCat.of T T)) :
    letI := f.hom.toAlgebra; IsModuleComplete S (p : S) (ModuleCat.of S T) := by
  letI := f.hom.toAlgebra
  apply (isModuleComplete_algebraMap_iff S T (p : S) T).mp
  simpa only [map_natCast] using hT

/-- 完備な離散環への射は、指定された H⁰ 完備化単位に沿って一意に延長する。 -/
theorem completion_existsUnique {S T : CommRingCat.{u}} (f : S ⟶ T)
    (hT : IsModuleComplete T (p : T) (ModuleCat.of T T)) :
    ∃! g : completionRing p S ⟶ T, completionUnit p S ≫ g = f := by
  letI := principalCompletionCommRing S (p : S)
  obtain ⟨g, hg, hu⟩ := principalCompletion_existsUnique_ringHom S (p : S) T f.hom
    (complete_along_map p f hT)
  refine ⟨CommRingCat.ofHom g, ?_, ?_⟩
  · exact CommRingCat.hom_ext hg
  · intro k hk
    apply CommRingCat.hom_ext
    apply hu k.hom
    exact congrArg (fun (q : S ⟶ T) => q.hom) hk

/-- 完備標的への延長を選ぶ。 -/
def completionLift {S T : CommRingCat.{u}} (f : S ⟶ T)
    (hT : IsModuleComplete T (p : T) (ModuleCat.of T T)) : completionRing p S ⟶ T :=
  (completion_existsUnique p f hT).choose

/-- 選んだ延長は元の単位との図式を満たす。 -/
@[simp] theorem completionLift_comp {S T : CommRingCat.{u}} (f : S ⟶ T)
    (hT : IsModuleComplete T (p : T) (ModuleCat.of T T)) :
    completionUnit p S ≫ completionLift p f hT = f :=
  (completion_existsUnique p f hT).choose_spec.1

/-- 完備標的への二射は、元の単位との合成で検出できる。 -/
theorem completion_hom_ext {S T : CommRingCat.{u}}
    (hT : IsModuleComplete T (p : T) (ModuleCat.of T T))
    {f g : completionRing p S ⟶ T}
    (h : completionUnit p S ≫ f = completionUnit p S ≫ g) : f = g :=
  (completion_existsUnique p (completionUnit p S ≫ f) hT).unique rfl h.symm

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

/-- 添字の射に沿って join 錐を制限する。極限性を仮定しない。 -/
def restrictCone {K L X : SSet.{u + 1}} {F : K ⟶ X}
    (c : JoinCone F) (f : L ⟶ K) : JoinCone (f ≫ F) :=
  ⟨joinMap (𝟙 Δ[0]) f ≫ c.val, by
    rw [← Category.assoc, joinInr_joinMap, Category.assoc, c.property]⟩

/-- 添字を制限しても錐の指定頂点を保つ。 -/
theorem restrictCone_vertex {K L X : SSet.{u + 1}} {F : K ⟶ X}
    (c : JoinCone F) (f : L ⟶ K) : (restrictCone c f).vertex = c.vertex := by
  simp only [JoinCone.vertex_eq, restrictCone, ← Category.assoc, joinInl_joinMap,
    Category.id_comp]

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

/-- 完備化側の図式は、元の図式の標的制限と一致する。 -/
theorem targetDiagram_restriction (R : Type u) [CommRing R] (S : A_R R) :
    nerveMap (targetRestriction p S.right) ≫ targetDiagram R p S =
      targetDiagram R p ((completionFunctor p R).obj S) := by
  have h := nerveFunctor.map_comp (targetRestriction p S.right).toCatHom
    (targetAlgebra R p S).toCatHom
  change nerveMap (targetRestriction p S.right ⋙ targetAlgebra R p S) =
    nerveMap (targetRestriction p S.right) ≫ nerveMap (targetAlgebra R p S) at h
  rw [targetDiagram, ← Category.assoc, ← h, targetRestriction_algebra]
  rfl

/-- 元の図式は、完備化側の図式の標的延長による制限と一致する。 -/
theorem targetDiagram_extension (R : Type u) [CommRing R] (S : A_R R) :
    nerveMap (targetExtension p S.right) ≫
        targetDiagram R p ((completionFunctor p R).obj S) = targetDiagram R p S := by
  have h := nerveFunctor.map_comp (targetExtension p S.right).toCatHom
    (targetAlgebra R p ((completionFunctor p R).obj S)).toCatHom
  change nerveMap (targetExtension p S.right ⋙
      targetAlgebra R p ((completionFunctor p R).obj S)) =
    nerveMap (targetExtension p S.right) ≫
      nerveMap (targetAlgebra R p ((completionFunctor p R).obj S)) at h
  rw [targetDiagram, ← Category.assoc, ← h, targetExtension_algebra]
  rfl

/-- 元の標的図式の指定錐を、完備化側の標的図式へ運ぶ。 -/
def completionRestrictCone (R : Type u) [CommRing R] (S : A_R R)
    (c : JoinCone (targetDiagram R p S)) :
    JoinCone (targetDiagram R p ((completionFunctor p R).obj S)) :=
  (restrictCone c (nerveMap (targetRestriction p S.right))).cast (targetDiagram_restriction p R S)

/-- 完備化側の標的図式の指定錐を、元の標的図式へ運ぶ。 -/
def completionExtendCone (R : Type u) [CommRing R] (S : A_R R)
    (c : JoinCone (targetDiagram R p ((completionFunctor p R).obj S))) :
    JoinCone (targetDiagram R p S) :=
  (restrictCone c (nerveMap (targetExtension p S.right))).cast (targetDiagram_extension p R S)

/-- 完備化側へ運んだ錐の頂点は元の頂点と同じ。 -/
theorem completionRestrictCone_vertex (R : Type u) [CommRing R] (S : A_R R)
    (c : JoinCone (targetDiagram R p S)) : (completionRestrictCone p R S c).vertex = c.vertex := by
  rw [completionRestrictCone, JoinCone.vertex_cast, restrictCone_vertex]

/-- 元の側へ運んだ錐の頂点も元の頂点と同じ。 -/
theorem completionExtendCone_vertex (R : Type u) [CommRing R] (S : A_R R)
    (c : JoinCone (targetDiagram R p ((completionFunctor p R).obj S))) :
    (completionExtendCone p R S c).vertex = c.vertex := by
  rw [completionExtendCone, JoinCone.vertex_cast, restrictCone_vertex]

end SerrePositivity.BhattScholze.PerfectoidizationInterface
