module
public import SerrePositivity.InfinityCategories.Derived.DGModuleExtensionYonedaStrict
public import SerrePositivity.InfinityCategories.Derived.DGModuleNerveEdges
public import SerrePositivity.DifferentialGraded.Functor.QuasiIsoHomology

/-! # 代表加群延長同型の閉射に対する自然性

概要：全 Hom 上の延長–Yoneda 比較を、元の閉 dg 射の可換四角形へ戻す。
方針：厳密 dg 自然変換の次数零式と、閉加群射の合成の閉零成分を照合する。
規約：各対象の同型だけで自然性を済ませない。使われ方：導来随伴の代表同型の正規化。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

/-- 代表加群の延長同型は元の閉 dg 射について通常の意味でも自然。 -/
lemma dgExtensionRepresentableIso_closed_naturality {x y : ClosedCategory A D}
    (f : x ⟶ y) :
    (dgModuleExtension A D E F).onClosed.map ((dgYoneda A D).onClosed.map f) ≫
      (dgModuleExtensionRepresentableIso A D E F y).hom =
    (dgModuleExtensionRepresentableIso A D E F x).hom ≫
      (dgYoneda A E).onClosed.map (F.onClosed.map f) := by
  let L := (dgYoneda A D).comp (dgModuleExtension A D E F)
  let R := F.comp (dgYoneda A E)
  have h := (dgModuleExtensionYonedaStrict A D E F).naturality
    (closedHomEquiv A D x y f).val
  have hL := congrArg Subtype.val (L.closedHomEquiv_map f)
  have hR := congrArg Subtype.val (R.closedHomEquiv_map f)
  change (closedHomEquiv A (RightModule A E) _ _ (L.onClosed.map f)).val =
    (L.map x y).f 0 (closedHomEquiv A D x y f).val at hL
  change (closedHomEquiv A (RightModule A E) _ _ (R.onClosed.map f)).val =
    (R.map x y).f 0 (closedHomEquiv A D x y f).val at hR
  rw [← hL, ← hR] at h
  apply (closedHomEquiv A (RightModule A E) _ _).injective
  apply Subtype.ext
  change (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) (_ ≫ _))).val =
    (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) (_ ≫ _))).val
  rw [dgModuleClosedCycle_comp, dgModuleClosedCycle_comp]
  exact h

end SerrePositivity.InfinityCategories
