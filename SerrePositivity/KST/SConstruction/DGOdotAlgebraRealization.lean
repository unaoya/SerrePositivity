module
public import SerrePositivity.KST.SConstruction.DGOdotAlgebra
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGQuasiEquivalenceNerve

/-! # 元の商 End 代数の右加群用一対象圏と元の End の比較
概要：構成した dg 代数の右加群用圏から、同じ元の商 End への全 Hom 恒等射を構成する。
方針：二回の Koszul 交換を対称性で消し、一対象の H⁰ 本質的全射性を使う。
規約：元の全 Hom・単位・積を保持。使われ方：具体的 ⊙ の Perf と元の商の比較。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory HomologicalComplex DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "Q" => DGOdotQuotientEnd R d
local notation "K" => homObject R (Q) EndomorphismObject.point EndomorphismObject.point

/-- 右加群用の反転 End 代数の圏から元の対象への、全 Hom 恒等の実 dg 射。 -/
def dgOdotEndAlgebraOppositeInclusion (D : Type v) [DGCategory R D] (x : D) :
    DGFunctor R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R
      (LocalizingInvariants.dgEndAlgebra R Dᵒᵖ (Opposite.op x))) D where
  obj _ := x
  map _ _ := 𝟙 _
  map_id _ := by
    change eId (Complex R) x ≫ 𝟙 _ = _
    exact Category.comp_id _
  map_comp _ _ _ := by
    change ((β_ (homObject R D x x) (homObject R D x x)).hom ≫
      (β_ (homObject R D x x) (homObject R D x x)).hom ≫
        eComp (Complex R) x x x) ≫ 𝟙 _ =
      (𝟙 _ ⊗ₘ 𝟙 _) ≫ eComp (Complex R) x x x
    rw [id_tensorHom_id, Category.comp_id, Category.id_comp, SymmetricCategory.symmetry_assoc]

/-- 右加群の向きへ揃えた実代数の圏は、元の商 End を同じ全 Hom で回収する。 -/
def dgOdotAlgebraToEnd : DGFunctor R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R (dgOdotAlgebra R d)) (Q) :=
  dgOdotEndAlgebraOppositeInclusion R (Q) EndomorphismObject.point

/-- 同じ代数の右加群用圏から元の商 End への実射は準同値。 -/
lemma dgOdotAlgebraToEnd_quasiEquivalence : QuasiEquivalence (dgOdotAlgebraToEnd R d) := by
  refine ⟨?_, ⟨?_⟩⟩
  · intro x y
    change QuasiIso (𝟙 _)
    constructor
    intro n
    exact quasiIsoAt_of_isIso (𝟙 _) n
  · intro y
    refine ⟨(toHomotopy R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R (dgOdotAlgebra R d))).obj
      (ForgetEnrichment.of (Complex R) (Opposite.op _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint.star)), ⟨?_⟩⟩
    obtain ⟨y⟩ := y
    cases y using EndomorphismObject.rec
    exact Iso.refl _

/-- 同じ実代数の右加群用圏と元の商 End の native nerve の実同値。 -/
def dgOdotAlgebraEndNerveEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R (dgOdotAlgebra R d))) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (Q)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuasiEquivalenceNerveEquivalence (dgOdotAlgebraToEnd R d)
    (dgOdotAlgebraToEnd_quasiEquivalence R d)

end SerrePositivity.KST.SConstruction
