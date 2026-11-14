module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.DGClosedRoofDiagramFillers
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.DGClosedRoofRefinements

/-! # 閉実分母上の一般有限対の実屋根充填

概要：一つの閉実分母上の一般有限係数正方形に、実屋根内の境界整合的充填を供給する。
方針：有限相対係数充填の合成閉分母で元の実分母を細分し、一般図式の二輸送で戻す。
規約：指定部分の元・商ホモトピーを全時刻で整合させる。使われ方：共通 fiber 還元後。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded DGQuotient SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]
variable (P : Set D) (x y : D) (s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedVerdierDenominators A D P x)
variable {L K : SSet.{max u v}} (i : L ⟶ K) [Mono i] [K.Finite]
variable (b : L ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D (ForgetEnrichment.to (Complex A) s.obj.left) y)
variable (g : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A (QuotientObject D P)
  ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) s.obj.left))
  ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y))

/-- 閉実分母上の任意の有限係数対は、実屋根内の全境界付き相対充填を持つ。 -/
theorem dgClosedRoofFinitePairs_nonempty (hP : _root_.SerrePositivity.DifferentialGraded.DGQuotient.localKFlat A D P)
    (hb : b ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap ((inclusion A D P).map
      (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) s.obj.left) y) = i ≫ g) :
    Nonempty (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.RoofHomotopyRelativeFiller i (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceMap A D P x y)
      (b ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofHomInclusion A D P x y s)
      (g ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientClosedRoofHomInclusion A D P x y s)) := by
  obtain ⟨C⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoefficientFinitePairs_nonempty A D P i
    (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) s.obj.left) y b g hP hb
  let s' := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofRefine A D P x s C.denominator C.denominator_mem
  let R : s' ⟶ s := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofRefineHom A D P x s C.denominator C.denominator_mem
  let t : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D (ForgetEnrichment.to (Complex A) s'.obj.left) y :=
    C.filler
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofDiagramFiller_nonempty A D P x y R i b g t hP hb C.boundary
    C.comparison C.fixed

end SerrePositivity.InfinityCategories.Project.DerivedCategories
