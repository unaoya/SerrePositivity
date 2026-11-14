module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Filtered
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-!
概要：filtered 図式の部分加群と、その余極限の具体的な像を比較する。
方針：各段の像は有向族であり、代表元を一つの段で取れることを使う。
規約：各段の遷移は指定された部分加群を保つ。
使われ方：Proj 次数の成分と近似の filtered 余極限の交換。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
universe u
variable {R : Type u} [CommRing R] {J : Type u} [SmallCategory J] [IsFiltered J]
variable (M : J ⥤ ModuleCat.{u} R) (V : ∀ j, Submodule R (M.obj j))
variable (hV : ∀ {i j} (f : i ⟶ j) (m : M.obj i), m ∈ V i → (M.map f).hom m ∈ V j)

/-- 余極限内の指定部分は、各段の部分加群の像の上限。 -/
def projectiveFilteredSubmodule : Submodule R (colimit M : ModuleCat.{u} R) :=
  ⨆ j, (V j).map (colimit.ι M j).hom

include hV

/-- 遷移で保たれる部分加群の像は、有向族をなす。 -/
theorem projectiveFilteredSubmodule_directed :
    Directed (· ≤ ·) (fun j ↦ (V j).map (colimit.ι M j).hom) := by
  intro i j
  refine ⟨IsFiltered.max i j, ?_, ?_⟩
  · rintro x ⟨m, hm, rfl⟩
    refine ⟨(M.map (IsFiltered.leftToMax i j)).hom m,
      hV (IsFiltered.leftToMax i j) m hm, ?_⟩
    exact congrArg (fun f ↦ f.hom m) (colimit.w M (IsFiltered.leftToMax i j))
  · rintro x ⟨m, hm, rfl⟩
    refine ⟨(M.map (IsFiltered.rightToMax i j)).hom m,
      hV (IsFiltered.rightToMax i j) m hm, ?_⟩
    exact congrArg (fun f ↦ f.hom m) (colimit.w M (IsFiltered.rightToMax i j))

/-- 余極限の指定部分の元は、一段の指定部分の代表元を持つ。 -/
theorem mem_projectiveFilteredSubmodule_iff (x : (colimit M : ModuleCat.{u} R)) :
    x ∈ projectiveFilteredSubmodule M V ↔
      ∃ (j : J) (m : M.obj j), m ∈ V j ∧ (colimit.ι M j).hom m = x := by
  have : Nonempty J := IsFiltered.nonempty
  rw [projectiveFilteredSubmodule,
    Submodule.mem_iSup_of_directed _ (projectiveFilteredSubmodule_directed M V hV)]
  rfl

/-- 各段の指定部分加群自身がなす filtered 図式。 -/
def projectiveFilteredSubmoduleDiagram : J ⥤ ModuleCat.{u} R where
  obj j := ModuleCat.of R (V j)
  map {i j} f := ModuleCat.ofHom
    { toFun := fun m ↦ ⟨(M.map f).hom m.val, hV f m.val m.property⟩
      map_add' := fun _ _ ↦ Subtype.ext ((M.map f).hom.map_add _ _)
      map_smul' := fun _ _ ↦ Subtype.ext ((M.map f).hom.map_smul _ _) }
  map_id j := by
    ext m
    exact congrArg (fun f ↦ f.hom m.val) (M.map_id j)
  map_comp f g := by
    ext m
    exact congrArg (fun f ↦ f.hom m.val) (M.map_comp f g)

/-- 指定部分加群の包含を、図式の包含とする。 -/
def projectiveFilteredSubmoduleInclusion : projectiveFilteredSubmoduleDiagram M V hV ⟶ M where
  app j := ModuleCat.ofHom (V j).subtype
  naturality _ _ _ := by ext m; rfl

/-- 指定部分加群の図式の包含は mono。 -/
instance projectiveFilteredSubmoduleInclusionMono :
    Mono (projectiveFilteredSubmoduleInclusion M V hV) := by
  have : ∀ j, Mono ((projectiveFilteredSubmoduleInclusion M V hV).app j) := fun j ↦
    (ModuleCat.mono_iff_injective _).mpr Subtype.val_injective
  exact NatTrans.mono_of_mono_app _

/-- filtered 余極限の完全性により、指定部分加群の余極限からの包含は単射。 -/
theorem projectiveFilteredSubmoduleColimit_injective :
    Function.Injective (colim.map (projectiveFilteredSubmoduleInclusion M V hV)).hom := by
  have : Mono (colim.map (projectiveFilteredSubmoduleInclusion M V hV)) := inferInstance
  exact (ModuleCat.mono_iff_injective _).mp this

/-- 部分加群の余極限の像は、各有限段の像の有向上限そのもの。 -/
theorem projectiveFilteredSubmoduleColimit_range :
    LinearMap.range (colim.map (projectiveFilteredSubmoduleInclusion M V hV)).hom =
      projectiveFilteredSubmodule M V := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨j, v, rfl⟩ := Concrete.colimit_exists_rep
      (projectiveFilteredSubmoduleDiagram M V hV) a
    apply (mem_projectiveFilteredSubmodule_iff M V hV _).mpr
    refine ⟨j, v.val, v.property, ?_⟩
    exact (congrArg (fun f ↦ f.hom v)
      (colimit.ι_map (projectiveFilteredSubmoduleInclusion M V hV) j)).symm
  · intro hx
    obtain ⟨j, m, hm, rfl⟩ := (mem_projectiveFilteredSubmodule_iff M V hV x).mp hx
    refine ⟨(colimit.ι (projectiveFilteredSubmoduleDiagram M V hV) j).hom ⟨m, hm⟩, ?_⟩
    exact congrArg (fun f ↦ f.hom ⟨m, hm⟩)
      (colimit.ι_map (projectiveFilteredSubmoduleInclusion M V hV) j)

/-- 指定部分加群の余極限を、余極限の中の具体的な部分加群と同定する。 -/
def projectiveFilteredSubmoduleColimitEquiv :
    (colimit (projectiveFilteredSubmoduleDiagram M V hV) : ModuleCat.{u} R) ≃ₗ[R]
      projectiveFilteredSubmodule M V :=
  (LinearEquiv.ofInjective (colim.map (projectiveFilteredSubmoduleInclusion M V hV)).hom
    (projectiveFilteredSubmoduleColimit_injective M V hV)).trans
      (LinearEquiv.ofEq _ _ (projectiveFilteredSubmoduleColimit_range M V hV))

/-- 部分加群の比較は、余極限内の同じ元を対応させる。 -/
theorem projectiveFilteredSubmoduleColimitEquiv_val
    (x : (colimit (projectiveFilteredSubmoduleDiagram M V hV) : ModuleCat.{u} R)) :
    (projectiveFilteredSubmoduleColimitEquiv M V hV x).val =
      (colim.map (projectiveFilteredSubmoduleInclusion M V hV)).hom x := rfl

end SerrePositivity.AlgebraicGeometry
