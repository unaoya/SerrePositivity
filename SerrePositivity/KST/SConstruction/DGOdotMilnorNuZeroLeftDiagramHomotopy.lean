module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNuZeroArrowBoundary

/-!
概要：元零角Left辺比較の端点固定ホモトピーを元実／絶対四角形の零角Left辺面に戻す。
方針：元四辺の厳密回収で同じホモトピーと同じ関手同型を同時に輸送する。
規約：元零角Left辺比較の類・全経路を保持。使われ方：元上下比較 prism の零角Left辺境界。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial

private lemma zeroLeftTransportHomotopy_h {A X : SSet.{u}}
    {f g f' g' : A ⟶ X} (hf : f = f') (hg : g = g') (H : SSet.Homotopy f g) :
    (Eq.mp (congrArg₂ (fun a b => SSet.Homotopy a b) hf hg) H).h = H.h := by
  subst f' g'
  rfl

private lemma zeroLeftTransportComparison {A X : SSet.{u}} [Quasicategory X]
    {f g f' g' : A ⟶ X} (hf : f = f') (hg : g = g') (H : SSet.Homotopy f g)
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g)
    (he : SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H) = e.hom) :
    SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (Eq.mp (congrArg₂ (fun a b => SSet.Homotopy a b) hf hg) H)) =
      (Eq.mp (congrArg₂ (fun a b => _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso a b) hf hg) e).hom := by
  subst f' g'
  exact he

variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "A" => dgKInputStableValue R (dgOdotMilnorFlatKernelInput R d)
local notation "B" => dgKInputStableValue R (dgOdotMilnorResolvedInput R d)
local notation "Z" => dgKInputStableValue R
  (dgFixedNullInput R (dgOdotMilnorFlatKernelInput R d))

variable (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d)

/-- 概要：同じ元零角Left辺辺全体を結ぶ指定端点経路付きの実ホモトピー。
方針：元全辺の等号で同じ元ホモトピーを輸送する。
規約：新しい辺や充填を選ばない。使われ方：元下比較 prism の実零角Left辺面。 -/
def dgOdotMilnorNuZeroLeftDiagramHomotopy : SSet.Homotopy
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ dgOdotMilnorPerfectNullSquare R d ≫ dgKInputNu R)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ perfectVerdierRawSquare (dgOdotMilnorNuPerfectSequence R d h)) :=
  Eq.mp (congrArg₂ (fun f g : (Δ[1] : SSet.{u + 2}) ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1} =>
    SSet.Homotopy f g) (dgOdotMilnorNuZeroLeftMap_diagram R d)
      (dgOdotMilnorNuZeroAbsoluteLeftMap_diagram R d h))
        (dgOdotMilnorNuZeroLeftArrowHomotopy R d)

/-- 概要：元零角Left辺面への輸送は同じ元ホモトピーの全単体を厳密回収する。
方針：端点等号だけの輸送で内部の射を変えないことを使う。
規約：元の全パラメータ。使われ方：元端点経路の保持。 -/
lemma dgOdotMilnorNuZeroLeftDiagramHomotopy_h :
    (dgOdotMilnorNuZeroLeftDiagramHomotopy R d h).h =
      (dgOdotMilnorNuZeroLeftArrowHomotopy R d).h :=
  zeroLeftTransportHomotopy_h (dgOdotMilnorNuZeroLeftMap_diagram R d)
    (dgOdotMilnorNuZeroAbsoluteLeftMap_diagram R d h)
    (dgOdotMilnorNuZeroLeftArrowHomotopy R d)

/-- 概要：元零角Left辺面の実ホモトピーが与える全比較は同じ元零角Left辺比較。
方針：同じ元ホモトピーと関手同型を同じ二端点等号で輸送する。
規約：元比較の射の等号。使われ方：元上下共有境界の保持。 -/
lemma dgOdotMilnorNuZeroLeftDiagramHomotopy_comparison :
    SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (dgOdotMilnorNuZeroLeftDiagramHomotopy R d h)) =
      (dgOdotMilnorNuZeroLeftDiagramComparison R d h).hom :=
  zeroLeftTransportComparison (dgOdotMilnorNuZeroLeftMap_diagram R d)
    (dgOdotMilnorNuZeroAbsoluteLeftMap_diagram R d h)
    (dgOdotMilnorNuZeroLeftArrowHomotopy R d)
    (dgOdotMilnorNuZeroLeftArrowComparison R d)
    (show SSet.Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (dgOdotMilnorNuZeroLeftArrowHomotopy R d)) =
        (dgOdotMilnorNuZeroLeftArrowComparison R d).hom from rfl)

/-- 概要：元零角Left辺面の実ホモトピーは同じ可逆な全零角Left辺比較を与える。
方針：同じ指定比較の射への等号で可逆性を戻す。
規約：元指定比較を保持。使われ方：元全比較 prism の実零角Left辺面。 -/
lemma dgOdotMilnorNuZeroLeftDiagramHomotopy_isInvertible :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (dgOdotMilnorNuZeroLeftDiagramHomotopy R d h)) := by
  change IsIso (SSet.Truncated.HomotopyCategory.homMk
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (dgOdotMilnorNuZeroLeftDiagramHomotopy R d h)))
  exact Eq.mp (congrArg (fun f => IsIso f)
    (dgOdotMilnorNuZeroLeftDiagramHomotopy_comparison R d h)).symm
      (inferInstance : IsIso (dgOdotMilnorNuZeroLeftDiagramComparison R d h).hom)

/-- 概要：元零角Left辺面ホモトピーの両端点は元の同じ指定端点経路。
方針：元ホモトピーの全回収式と同じ二端点経路を合成する。
規約：全一単体の厳密等号。使われ方：元二比較面の貼り合わせ。 -/
lemma dgOdotMilnorNuZeroLeftDiagramHomotopy_paths :
    (stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u + 2})) ≫
        (dgOdotMilnorNuZeroLeftDiagramHomotopy R d h).h =
      snd Δ[0] Δ[1] ≫ SSet.yonedaEquiv.symm
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (𝟙 (A : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}))).edge ∧
      (stdSimplex.δ (0 : Fin 2) ▷ (Δ[1] : SSet.{u + 2})) ≫
        (dgOdotMilnorNuZeroLeftDiagramHomotopy R d h).h =
      snd Δ[0] Δ[1] ≫ SSet.yonedaEquiv.symm
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.toZeroCategory (Z))).edge :=
  ⟨(congrArg (fun f => (stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u + 2})) ≫ f)
      (dgOdotMilnorNuZeroLeftDiagramHomotopy_h R d h)).trans
        (dgOdotMilnorNuZeroLeftArrowHomotopy_paths R d).1,
    (congrArg (fun f => (stdSimplex.δ (0 : Fin 2) ▷ (Δ[1] : SSet.{u + 2})) ≫ f)
      (dgOdotMilnorNuZeroLeftDiagramHomotopy_h R d h)).trans
        (dgOdotMilnorNuZeroLeftArrowHomotopy_paths R d).2⟩

end SerrePositivity.KST.SConstruction
