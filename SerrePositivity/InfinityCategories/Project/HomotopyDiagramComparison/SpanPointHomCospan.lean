module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.CosliceEdgeSectionFiber
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.PartialColimitHomEnd
public import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits

/-!
概要：二辺の span の固定終点余錐空間を、各終点からの点図式の Hom の cospan と比較する。
方針：辺全体への固定終点の切断を二枝で束ね、前合成の厳密な等式で自然性を証明する。
規約：span は Λ[2,0]、右枝を cospan の左枝とする。使われ方：native な span の余錐空間の表示。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
variable {X : SSet.{u}} [Quasicategory X] (p : (horn 2 0 : SSet.{u}) ⟶ X) (y : X _⦋0⦌)

/-- 二辺の終点側から共通の始点側へ、実際の辺で前合成する点図式の Hom の cospan。 -/
def spanPointHomWalkingCospan : WalkingCospan ⥤ SSet.{u} :=
  cospan
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEdgeFiberPrecomposition (horn₂₀.ι₀₂ ≫ p)
      (stdSimplex.δ (1 : Fin 2) ≫ (horn₂₀.ι₀₁ ≫ p))
      (stdSimplex.δ (0 : Fin 2) ≫ (horn₂₀.ι₀₂ ≫ p))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq horn₂₀.isPushout p) rfl y)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEdgeFiberPrecomposition (horn₂₀.ι₀₁ ≫ p)
      (stdSimplex.δ (1 : Fin 2) ≫ (horn₂₀.ι₀₁ ≫ p))
      (stdSimplex.δ (0 : Fin 2) ≫ (horn₂₀.ι₀₁ ≫ p)) rfl rfl y)

/-- 点図式の Hom の cospan を宇宙 u の小さい添字へ持ち上げる。 -/
def spanPointHomCospan : AsSmall.{u} WalkingCospan ⥤ SSet.{u} :=
  AsSmall.down ⋙ spanPointHomWalkingCospan p y

/-- 二つの辺全体の余錐空間から共通始点への制限の cospan。 -/
def spanEdgeCoconeWalkingCospan : WalkingCospan ⥤ SSet.{u} :=
  cospan
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber (horn₂₀.ι₀₂ ≫ p) (stdSimplex.δ (1 : Fin 2))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq horn₂₀.isPushout p) y)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap (horn₂₀.ι₀₁ ≫ p) (stdSimplex.δ (1 : Fin 2)) y)

/-- 辺全体の余錐空間の cospan を宇宙 u の小さい添字へ持ち上げる。 -/
def spanEdgeCoconeCospan : AsSmall.{u} WalkingCospan ⥤ SSet.{u} :=
  AsSmall.down ⋙ spanEdgeCoconeWalkingCospan p y

/-- 二枝の終点制限の切断は、点 Hom の cospan から辺全体の cospan への厳密な自然変換。 -/
def spanPointHomToEdgeCocones : spanPointHomCospan p y ⟶ spanEdgeCoconeCospan p y :=
  Functor.whiskerLeft AsSmall.down (cospanHomMk
    (F := spanPointHomWalkingCospan p y) (G := spanEdgeCoconeWalkingCospan p y) (𝟙 _)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEdgeSectionFiber (horn₂₀.ι₀₂ ≫ p) y)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEdgeSectionFiber (horn₂₀.ι₀₁ ≫ p) y)
    (by
      change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEdgeFiberPrecomposition (horn₂₀.ι₀₂ ≫ p)
        (stdSimplex.δ (1 : Fin 2) ≫ (horn₂₀.ι₀₁ ≫ p))
        (stdSimplex.δ (0 : Fin 2) ≫ (horn₂₀.ι₀₂ ≫ p))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq horn₂₀.isPushout p) rfl y ≫ 𝟙 _ = _
      rw [Category.comp_id]
      exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEdgeSectionFiber_source (horn₂₀.ι₀₂ ≫ p) _
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq horn₂₀.isPushout p) y).symm)
    (by
      change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEdgeFiberPrecomposition (horn₂₀.ι₀₁ ≫ p)
          (stdSimplex.δ (1 : Fin 2) ≫ (horn₂₀.ι₀₁ ≫ p))
          (stdSimplex.δ (0 : Fin 2) ≫ (horn₂₀.ι₀₁ ≫ p)) rfl rfl y ≫ 𝟙 _ =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEdgeSectionFiber (horn₂₀.ι₀₁ ≫ p) y ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap (horn₂₀.ι₀₁ ≫ p) (stdSimplex.δ (1 : Fin 2)) y
      rw [Category.comp_id]
      simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber_eq, eqToHom_refl, Category.comp_id] using
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEdgeSectionFiber_source (horn₂₀.ι₀₁ ≫ p) _ rfl y).symm))

/-- 二枝の切断による自然変換は、共通始点と両側の点 Hom の全成分で同値。 -/
lemma spanPointHomToEdgeCocones_app_homotopyEquivalence (k : AsSmall.{u} WalkingCospan) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence ((spanPointHomToEdgeCocones p y).app k) := by
  rcases k with ⟨k⟩
  cases k with
  | none => exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.homotopyEquivalence_of_isIso (𝟙 _)
  | some k =>
    cases k with
    | left => exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEdgeSectionFiber_homotopyEquivalence _ _
    | right => exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEdgeSectionFiber_homotopyEquivalence _ _

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
