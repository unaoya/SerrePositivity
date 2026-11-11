module
public import SerrePositivity.DifferentialGraded.Functor.ModuleValued

/-! # dg 関手と閉零射の実 cycle

概要：閉零射の dg 関手による像は、Hom 複体の chain map による実 cycle の像。
方針：閉零射を単位複体からの射として読み、cycle の後合成を使う。
規約：任意の dg 圏を扱う。使われ方：実 cone 比較とその二単体成分の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable {A : Type u} [CommRing A] {D : Type v} {E : Type w}
  [DGCategory A D] [DGCategory A E]

/-- dg 関手の閉零射への作用と実次数零 cycle への作用は同じ。 -/
lemma dgFunctor_mapClosedCycle (F : DGFunctor A D E) {M N : ClosedCategory A D} (f : M ⟶ N) :
    (F.map (ForgetEnrichment.to (Complex A) M) (ForgetEnrichment.to (Complex A) N)).f 0
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) f)).val =
        (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) (F.onClosed.map f))).val := by
  change _ = (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) f ≫ F.map _ _)).val
  rw [cycleFromUnit_postcomp]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
