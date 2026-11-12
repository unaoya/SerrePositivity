module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedPrimitives
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGRepresentableDerivedMaps
public import SerrePositivity.DifferentialGraded.Derived.Projective

/-! # 代表加群を始域とする導来零射の実 Hom end の原始元

概要：主導来圏で零の閉加群射は、元の全 Hom end で実際の境界になる。
方針：代表加群のホモトピー射影性で H⁰ の零射へ反映し、商の境界関係を展開する。
規約：標的は任意の加群でシフトも許す。使われ方：全次数の分母零化から原始元を回収。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- ホモトピー射影的な始域からの導来零射は、元の Hom end で境界になる。 -/
lemma dgModuleProjectiveDerived_zero_iff_primitive {M N : ModuleCategory A D}
    (hM : moduleHomotopicallyProjective A D M) (f : M ⟶ N) :
    (moduleToDerived A D).map f = 0 ↔
      ∃ h : (homObject A (RightModule A D) M N).X (-1),
        (homObject A (RightModule A D) M N).d (-1) 0 h =
          (closedHomEquiv A (RightModule A D) M N f).val := by
  have he : (moduleToDerived A D).map f = 0 ↔
      (moduleToHomotopy A D).map f = (moduleToHomotopy A D).map (0 : M ⟶ N) := by
    constructor
    · intro h
      apply (moduleProjectiveDerivedHomEquiv A D hM N).injective
      rw [moduleProjectiveDerivedHomEquiv_map A D hM f,
        moduleProjectiveDerivedHomEquiv_map A D hM (0 : M ⟶ N)]
      simpa only [Functor.map_zero] using h
    · intro h
      have h' := congrArg (moduleProjectiveDerivedHomEquiv A D hM N) h
      rw [moduleProjectiveDerivedHomEquiv_map A D hM f,
        moduleProjectiveDerivedHomEquiv_map A D hM (0 : M ⟶ N)] at h'
      simpa only [Functor.map_zero] using h'
  exact he.trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosed_zero_iff_primitive A (RightModule A D) f)


end SerrePositivity.InfinityCategories.Project.DerivedCategories
