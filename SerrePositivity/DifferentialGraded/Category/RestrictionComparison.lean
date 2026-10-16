module
public import SerrePositivity.DifferentialGraded.Category.Restriction
public import SerrePositivity.DifferentialGraded.Category.QuotientComparison

/-! # 充満dg部分圏の関手制限に対するH⁰比較の評価 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 制限後に包含するH⁰関手と元のH⁰関手の比較から、指定した終域関手への自然同型を作る。 -/
def restrictHomotopyComparisonIso (F : DGFunctor A D D) (P : D → Prop)
    (hP : ∀ X, P X → P (F.obj X)) (G : HomotopyCategory A D ⥤ HomotopyCategory A D)
    (e : F.onHomotopy ≅ G) :
    (F.restrict P P hP).onHomotopy ⋙ (dgFullSubcategoryInclusion A D P).onHomotopy ≅
      (dgFullSubcategoryInclusion A D P).onHomotopy ⋙ G :=
  eqToIso ((DGFunctor.onHomotopy_comp _ _).symm.trans
    ((congrArg (fun H : DGFunctor A (DGFullSubcategory D P) D => H.onHomotopy)
      (F.restrict_comp_inclusion P P hP)).trans (DGFunctor.onHomotopy_comp _ _))) ≪≫
    Functor.isoWhiskerLeft (dgFullSubcategoryInclusion A D P).onHomotopy e

/-- 対象の性質を保つdg関手のH⁰比較は、制限して包含した対象で元の比較の成分を返す。 -/
lemma restrictHomotopyComparison_hom_app (F : DGFunctor A D D) (P : D → Prop)
    (hP : ∀ X, P X → P (F.obj X)) (G : HomotopyCategory A D ⥤ HomotopyCategory A D)
    (e : F.onHomotopy ≅ G) (X : HomotopyCategory A (DGFullSubcategory D P)) :
    (restrictHomotopyComparisonIso F P hP G e).hom.app X =
      e.hom.app ((dgFullSubcategoryInclusion A D P).onHomotopy.obj X) := by
  have h := comparisonWhiskerLeft_hom_app
    ((F.restrict P P hP).onHomotopy ⋙ (dgFullSubcategoryInclusion A D P).onHomotopy)
    (dgFullSubcategoryInclusion A D P).onHomotopy F.onHomotopy G
    ((DGFunctor.onHomotopy_comp _ _).symm.trans
      ((congrArg (fun H : DGFunctor A (DGFullSubcategory D P) D => H.onHomotopy)
        (F.restrict_comp_inclusion P P hP)).trans (DGFunctor.onHomotopy_comp _ _))) e X
  exact h.trans (Category.id_comp _)

end SerrePositivity.DifferentialGraded
