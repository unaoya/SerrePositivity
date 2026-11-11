module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleSubcategoryYonedaCone
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGPretriangulatedRepresentableOperations
/-!
概要：零・shift・cone で閉じる実加群代表系の前三角性。
方針：同じ代表系の Yoneda 模型の実演算を検証する。
規約：κ-compact 性や全頂点の被覆を仮定しない。
使われ方：K-7 の選択された全 Hom dg 模型への一般供給。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
section
open CategoryTheory Limits DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

lemma dgModuleSubcategory_zeroRepresentable_isZero
    (S : Set (ModuleCategory R D)) [Small.{u} {M // S M}] (h0 : S (moduleZero R D)) :
    IsZero (ForgetEnrichment.of (Complex R)
      (representable R (⟨moduleZero R D, h0⟩ : {M // S M}))) := by
  apply (module_isZero_iff R {M // S M} _).2
  intro M
  exact moduleHom_isZero_tgt R D (ForgetEnrichment.to (Complex R) M.val)
    (zeroModule R D) (fun _ ↦ isZero_zero (Complex R))

lemma dgModuleSubcategoryRepresentables_containsZero
    (S : Set (ModuleCategory R D)) [Small.{u} {M // S M}] (h0 : S (moduleZero R D)) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableHomotopyProperty R {M // S M}).ContainsZero := by
  let Z : {M // S M} := ⟨moduleZero R D, h0⟩
  refine ⟨⟨(moduleToHomotopy R {M // S M}).obj
    (ForgetEnrichment.of (Complex R) (representable R Z)), ?_, ?_⟩⟩
  · exact (moduleToHomotopy R {M // S M}).map_isZero
      (dgModuleSubcategory_zeroRepresentable_isZero R D S h0)
  · exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableHomotopyProperty_representable R {M // S M} Z

end

section
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
    (S : Set (ModuleCategory R D)) [Small.{u} {M // S M}]

lemma dgModuleSubcategory_isDGPretriangulated
    (hzero : S (moduleZero R D))
    (hshift : ∀ M, S M → ∀ n : ℤ, S (M⟦n⟧))
    (hcone : ∀ M N, S M → S N → ∀ f : M ⟶ N, S (moduleCone R D f)) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R {M // S M} := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.isDGPretriangulated_of_representable_operations R {M // S M}
  · exact dgModuleSubcategoryRepresentables_containsZero R D S hzero
  · intro X n
    apply (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableHomotopyProperty_iff R {M // S M} _).2
    exact ⟨⟨X.val⟦n⟧, hshift X.val X.property n⟩,
      ⟨(moduleToHomotopy R {M // S M}).mapIso
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleSubcategoryShiftIso R D S hshift X n)⟩⟩
  · intro X Y f
    apply (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableHomotopyProperty_iff R {M // S M} _).2
    exact ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleSubcategoryConeObject R D S hcone f,
      ⟨(moduleToHomotopy R {M // S M}).mapIso
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleSubcategoryYonedaConeIso R D S hcone f)⟩⟩
end

end SerrePositivity.InfinityCategories.Project.DerivedCategories
