module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNuProjectionHomotopy

/-!
概要：元指定商比較の端点固定ホモトピーを元実／絶対四角形の右面に戻す。
方針：元四辺の厳密回収で同じホモトピーと同じ関手同型を同時に輸送する。
規約：元比較の類・全経路を保持。使われ方：元下比較 prism の指定右境界。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial

private lemma projectionTransportHomotopy_h {A X : SSet.{u}}
    {f g f' g' : A ⟶ X} (hf : f = f') (hg : g = g') (H : SSet.Homotopy f g) :
    (Eq.mp (congrArg₂ (fun a b => SSet.Homotopy a b) hf hg) H).h = H.h := by
  subst f' g'
  rfl

private lemma projectionTransportComparison {A X : SSet.{u}} [Quasicategory X]
    {f g f' g' : A ⟶ X} (hf : f = f') (hg : g = g') (H : SSet.Homotopy f g)
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g)
    (he : SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H) = e.hom) :
    SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (Eq.mp (congrArg₂ (fun a b => SSet.Homotopy a b) hf hg) H)) =
      (Eq.mp (congrArg₂ (fun a b => _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso a b) hf hg) e).hom := by
  subst f' g'
  exact he

variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "A" => dgKInputStableValue R (dgOdotMilnorCellInput R d)
local notation "B" => dgKInputStableValue R (dgOdotMilnorResolvedInput R d)

/-- 概要：元実商完全射の全辺は元実四角形の同じ右辺。
方針：元右辺と元 ν の全一単体の回収を使う。
規約：元辺の等号。使われ方：元実右境界への厳密復元。 -/
lemma dgOdotMilnorNuProjectionMap_diagram :
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (dgOdotMilnorCellProjectionExactMap R d)).edge =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ dgOdotMilnorPerfectNullSquare R d ≫ dgKInputNu R := by
  symm
  rw [← Category.assoc, (dgOdotMilnorPerfectNullSquare_edges R d).2.1]
  change SSet.yonedaEquiv.symm ((dgKInputNu R).app _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgOdotMilnorCellProjectionInputMap R d)).edge) = _
  exact congrArg SSet.yonedaEquiv.symm
    (dgKInputNu_edge R (dgOdotMilnorCellProjectionInputMap R d))

variable (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d)

/-- 概要：同じ元完備化後射影の全辺は同じ絶対四角形の元右辺。
方針：元絶対提示の四辺回収を使う。
規約：同じ射影・同じ四角形。使われ方：元絶対右境界への厳密復元。 -/
lemma dgOdotMilnorNuAbsoluteProjectionMap_diagram :
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (dgOdotMilnorNuPerfectSequence R d h).projection).edge =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ perfectVerdierRawSquare (dgOdotMilnorNuPerfectSequence R d h) :=
  (perfectVerdierRawSquare_edges (dgOdotMilnorNuPerfectSequence R d h)).2.2.2.symm

/-- 概要：元実／絶対四角形の右辺を同じ既公開商比較で結ぶ。
方針：元二辺の等号で同じ全関手同型を輸送する。
規約：元指定商比較を変更しない。使われ方：元下比較 prism の右境界。 -/
def dgOdotMilnorNuProjectionDiagramComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ dgOdotMilnorPerfectNullSquare R d ≫ dgKInputNu R)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ perfectVerdierRawSquare (dgOdotMilnorNuPerfectSequence R d h)) :=
  Eq.mp (congrArg₂ (fun f g : (Δ[1] : SSet.{u + 2}) ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1} => _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g)
    (dgOdotMilnorNuProjectionMap_diagram R d) (dgOdotMilnorNuAbsoluteProjectionMap_diagram R d h))
      (dgOdotMilnorNuProjectionArrowComparison R d h)

/-- 概要：同じ元右辺全体を結ぶ指定端点経路付きの実ホモトピー。
方針：元全辺の等号で同じ元ホモトピーを輸送する。
規約：新しい辺や充填を選ばない。使われ方：元下比較 prism の実右面。 -/
def dgOdotMilnorNuProjectionDiagramHomotopy : SSet.Homotopy
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ dgOdotMilnorPerfectNullSquare R d ≫ dgKInputNu R)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ perfectVerdierRawSquare (dgOdotMilnorNuPerfectSequence R d h)) :=
  Eq.mp (congrArg₂ (fun f g : (Δ[1] : SSet.{u + 2}) ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1} =>
    SSet.Homotopy f g) (dgOdotMilnorNuProjectionMap_diagram R d)
      (dgOdotMilnorNuAbsoluteProjectionMap_diagram R d h))
        (dgOdotMilnorNuProjectionArrowHomotopy R d h)

/-- 概要：元右面への輸送は同じ元ホモトピーの全単体を厳密回収する。
方針：端点等号だけの輸送で内部の射を変えないことを使う。
規約：元の全パラメータ。使われ方：元端点経路の保持。 -/
lemma dgOdotMilnorNuProjectionDiagramHomotopy_h :
    (dgOdotMilnorNuProjectionDiagramHomotopy R d h).h =
      (dgOdotMilnorNuProjectionArrowHomotopy R d h).h :=
  projectionTransportHomotopy_h (dgOdotMilnorNuProjectionMap_diagram R d)
    (dgOdotMilnorNuAbsoluteProjectionMap_diagram R d h)
    (dgOdotMilnorNuProjectionArrowHomotopy R d h)

/-- 概要：元右面の実ホモトピーが与える全比較は同じ元指定商比較。
方針：同じ元ホモトピーと関手同型を同じ二端点等号で輸送する。
規約：元比較の射の等号。使われ方：Sp の指定商境界の保持。 -/
lemma dgOdotMilnorNuProjectionDiagramHomotopy_comparison :
    SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (dgOdotMilnorNuProjectionDiagramHomotopy R d h)) =
      (dgOdotMilnorNuProjectionDiagramComparison R d h).hom :=
  projectionTransportComparison (dgOdotMilnorNuProjectionMap_diagram R d)
    (dgOdotMilnorNuAbsoluteProjectionMap_diagram R d h)
    (dgOdotMilnorNuProjectionArrowHomotopy R d h) (dgOdotMilnorNuProjectionArrowComparison R d h)
    (dgOdotMilnorNuProjectionArrowHomotopy_comparison R d h)

/-- 概要：元右面の実ホモトピーは同じ可逆な全商比較を与える。
方針：同じ指定比較の射への等号で可逆性を戻す。
規約：元指定比較を保持。使われ方：元全比較 prism の実右面。 -/
lemma dgOdotMilnorNuProjectionDiagramHomotopy_isInvertible :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (dgOdotMilnorNuProjectionDiagramHomotopy R d h)) := by
  change IsIso (SSet.Truncated.HomotopyCategory.homMk
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (dgOdotMilnorNuProjectionDiagramHomotopy R d h)))
  exact Eq.mp (congrArg (fun f => IsIso f)
    (dgOdotMilnorNuProjectionDiagramHomotopy_comparison R d h)).symm
      (inferInstance : IsIso (dgOdotMilnorNuProjectionDiagramComparison R d h).hom)

/-- 概要：元右面ホモトピーの両端点は元中間圏・元商の同じ恒等経路。
方針：元ホモトピーの全回収式と同じ二端点経路を合成する。
規約：全一単体の厳密等号。使われ方：元二比較面の貼り合わせ。 -/
lemma dgOdotMilnorNuProjectionDiagramHomotopy_paths :
    (stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u + 2})) ≫
        (dgOdotMilnorNuProjectionDiagramHomotopy R d h).h =
      snd Δ[0] Δ[1] ≫ SSet.yonedaEquiv.symm
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (𝟙 (A : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}))).edge ∧
      (stdSimplex.δ (0 : Fin 2) ▷ (Δ[1] : SSet.{u + 2})) ≫
        (dgOdotMilnorNuProjectionDiagramHomotopy R d h).h =
      snd Δ[0] Δ[1] ≫ SSet.yonedaEquiv.symm
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (𝟙 (B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}))).edge :=
  ⟨(congrArg (fun f => (stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u + 2})) ≫ f)
      (dgOdotMilnorNuProjectionDiagramHomotopy_h R d h)).trans
        (dgOdotMilnorNuProjectionArrowHomotopy_paths R d h).1,
    (congrArg (fun f => (stdSimplex.δ (0 : Fin 2) ▷ (Δ[1] : SSet.{u + 2})) ≫ f)
      (dgOdotMilnorNuProjectionDiagramHomotopy_h R d h)).trans
        (dgOdotMilnorNuProjectionArrowHomotopy_paths R d h).2⟩

end SerrePositivity.KST.SConstruction
