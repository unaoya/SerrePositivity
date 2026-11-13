module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Actions.DGModuleExtensionYonedaStrict
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.Nerves.DGModuleNerveEdges
public import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence

/-! # 代表加群延長同型の閉射に対する自然性

概要：全 Hom 上の延長–Yoneda 比較を、元の閉 dg 射の可換四角形へ戻す。
方針：厳密 dg 自然変換の次数零式と、閉加群射の合成の閉零成分を照合する。
規約：各対象の同型だけで自然性を済ませない。使われ方：導来随伴の代表同型の正規化。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
  (E : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory A E] [Small.{u} E] (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor A D E)

/-- 代表加群の延長同型は元の閉 dg 射について通常の意味でも自然。 -/
lemma dgExtensionRepresentableIso_closed_naturality {x y : _root_.SerrePositivity.DifferentialGraded.ClosedCategory A D}
    (f : x ⟶ y) :
    (_root_.SerrePositivity.DifferentialGraded.dgModuleExtension A D E F).onClosed.map ((_root_.SerrePositivity.DifferentialGraded.dgYoneda A D).onClosed.map f) ≫
      (_root_.SerrePositivity.DifferentialGraded.dgModuleExtensionRepresentableIso A D E F y).hom =
    (_root_.SerrePositivity.DifferentialGraded.dgModuleExtensionRepresentableIso A D E F x).hom ≫
      (_root_.SerrePositivity.DifferentialGraded.dgYoneda A E).onClosed.map (F.onClosed.map f) := by
  let L := (_root_.SerrePositivity.DifferentialGraded.dgYoneda A D).comp (_root_.SerrePositivity.DifferentialGraded.dgModuleExtension A D E F)
  let R := F.comp (_root_.SerrePositivity.DifferentialGraded.dgYoneda A E)
  have h := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleExtensionYonedaStrict A D E F).naturality
    (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv A D x y f).val
  have hL := congrArg Subtype.val (L.closedHomEquiv_map f)
  have hR := congrArg Subtype.val (R.closedHomEquiv_map f)
  change (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv A (_root_.SerrePositivity.DifferentialGraded.RightModule A E) _ _ (L.onClosed.map f)).val =
    (L.map x y).f 0 (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv A D x y f).val at hL
  change (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv A (_root_.SerrePositivity.DifferentialGraded.RightModule A E) _ _ (R.onClosed.map f)).val =
    (R.map x y).f 0 (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv A D x y f).val at hR
  rw [← hL, ← hR] at h
  apply (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv A (_root_.SerrePositivity.DifferentialGraded.RightModule A E) _ _).injective
  apply Subtype.ext
  change (_root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex A) (_ ≫ _))).val =
    (_root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex A) (_ ≫ _))).val
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleClosedCycle_comp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleClosedCycle_comp]
  exact h

end SerrePositivity.InfinityCategories.Project.DerivedCategories
