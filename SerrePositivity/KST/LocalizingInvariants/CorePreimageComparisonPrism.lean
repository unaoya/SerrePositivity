module

public import SerrePositivity.KST.LocalizingInvariants.IntervalMarkedEdges
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FunctorEdgePointwise
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.SuspensionDiagramArrows
public import Mathlib.AlgebraicTopology.SimplicialSet.HoFunctorMonoidal

/-!
概要：商後の比較が可逆な実 prism を、元の core の厳密逆像内へ戻す。
方針：水平・垂直・斜辺を実合成二単体で検査し、同じ全 prism を部分複体へ持ち上げる。
規約：比較の一次単体と両端を変えず、経路の類による代用はしない。
使われ方：c5 の分母精密化を元の相対図式内の実比較として回収する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

/-- 水平辺と垂直辺を反転する同じ prism は、斜辺も全て反転する。 -/
lemma prism_invertsAllEdges {K Y : SSet.{u}} (H : K ⊗ (Δ[1] : SSet.{u}) ⟶ Y)
    (horizontal : ∀ (e : K _⦋1⦌) (v : (Δ[1] : SSet.{u}) _⦋0⦌),
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (H.app _ (e, (Δ[1] : SSet.{u}).σ 0 v))))
    (vertical : ∀ (k : K _⦋0⦌) (a : (Δ[1] : SSet.{u}) _⦋1⦌),
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (H.app _ (K.σ 0 k, a)))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges H Set.univ := by
  intro s _
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex s.1
  let a := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex s.2
  let c := ((Truncated.Edge.CompStruct.compId e).tensor
    (Truncated.Edge.CompStruct.idComp a)).map ((truncation 2).map H)
  have h₀ := horizontal s.1 ((Δ[1] : SSet.{u}).δ 1 s.2)
  have h₁ := vertical (K.δ 0 s.1) s.2
  have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge ((e.tensor a).map ((truncation 2).map H)) := by
    change IsIso (Truncated.HomotopyCategory.homMk _)
    rw [← Truncated.HomotopyCategory.homMk_comp_homMk c]
    have : IsIso (Truncated.HomotopyCategory.homMk
      ((e.tensor (Truncated.Edge.id (X := (truncation 2).obj (Δ[1] : SSet.{u}))
        ((Δ[1] : SSet.{u}).δ 1 s.2))).map
        ((truncation 2).map H))) :=
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex
        (H.app _ (s.1, (Δ[1] : SSet.{u}).σ 0 ((Δ[1] : SSet.{u}).δ 1 s.2))))
        (f := (e.tensor (Truncated.Edge.id
          (X := (truncation 2).obj (Δ[1] : SSet.{u}))
          ((Δ[1] : SSet.{u}).δ 1 s.2))).map ((truncation 2).map H)) rfl).mp h₀
    have : IsIso (Truncated.HomotopyCategory.homMk
      (((Truncated.Edge.id (X := (truncation 2).obj K) (K.δ 0 s.1)).tensor a).map
        ((truncation 2).map H))) :=
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (H.app _ (K.σ 0 (K.δ 0 s.1), s.2)))
        (f := ((Truncated.Edge.id (X := (truncation 2).obj K) (K.δ 0 s.1)).tensor a).map
          ((truncation 2).map H)) rfl).mp h₁
    infer_instance
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e := (e.tensor a).map ((truncation 2).map H))
    (f := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex s).map ((truncation 2).map H)) rfl).mp hc

/-- 商後に全辺を反転する実図式を、同じ core の厳密逆像へ持ち上げる。 -/
def corePreimageLift {T X Y : SSet.{u}} (p : X ⟶ Y) (F : T ⟶ X)
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges (F ≫ p) Set.univ) :
    T ⟶ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore Y).preimage p : SSet.{u}) :=
  Subcomplex.lift F (by
    rintro n _ ⟨s, rfl⟩
    intro α
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex
      (Y.map α.op ((F ≫ p).app n s)))
    rw [← (F ≫ p).naturality_apply]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (T.map α.op s)).map
      ((truncation 2).map (F ≫ p))) (f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex
        ((F ≫ p).app (Opposite.op ⦋1⦌) (T.map α.op s))) rfl).mp
          (hF (Set.mem_univ _)))

lemma corePreimageLift_ι {T X Y : SSet.{u}} (p : X ⟶ Y) (F : T ⟶ X)
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges (F ≫ p) Set.univ) :
    corePreimageLift p F hF ≫ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore Y).preimage p).ι = F := rfl

/-- 可逆な比較辺の prism は、両端が全辺を反転すれば全ての辺を反転する。 -/
lemma functorEdgePrism_invertsAllEdges {K Y : SSet.{u}} [Quasicategory Y]
    {F G : K ⟶ Y}
    (t : Truncated.Edge (X := (truncation 2).obj ((ihom K).obj Y))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G))
    (ht : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := (ihom K).obj Y) t)
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges F Set.univ) (hG : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges G Set.univ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge t).h Set.univ := by
  let H := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge t
  apply prism_invertsAllEdges H.h
  · intro e v
    obtain ⟨j, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective v
    fin_cases j
    · have he := congrArg (fun f => f.app (Opposite.op ⦋1⦌) e) H.h₀
      change H.h.app _ (e, (Δ[1] : SSet.{u}).σ 0 (stdSimplex.obj₀Equiv.symm 0)) =
        F.app _ e at he
      have hi := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex e).map ((truncation 2).map F))
        (f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (F.app (Opposite.op ⦋1⦌) e)) rfl).mp (hF (Set.mem_univ e))
      exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr he).mpr hi
    · have he := congrArg (fun f => f.app (Opposite.op ⦋1⦌) e) H.h₁
      change H.h.app _ (e, (Δ[1] : SSet.{u}).σ 0 (stdSimplex.obj₀Equiv.symm 1)) =
        G.app _ e at he
      have hi := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex e).map ((truncation 2).map G))
        (f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (G.app (Opposite.op ⦋1⦌) e)) rfl).mp (hG (Set.mem_univ e))
      exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr he).mpr hi
  · intro k a
    let v := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := Y) k).app (Opposite.op ⦋1⦌) t.edge
    have hv : v ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertedEdges (𝟙 Y) := by
      exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr
        (e := t.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := Y) k)))
        (f := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex v).map ((truncation 2).map (𝟙 Y))) rfl).mp
          (ht.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := Y) k))
    have hi := intervalMap_edges_mem (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertedEdges (𝟙 Y))
      (invertedEdges_constant (𝟙 Y)) v hv a
    have hc : SSet.yonedaEquiv.symm v =
        lift (SSet.const k) (𝟙 (Δ[1] : SSet.{u})) ≫ H.h := by
      rw [← SSet.yonedaEquiv_symm_comp]
      change SSet.yonedaEquiv.symm t.edge ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt k = _
      rw [← curry_uncurry (SSet.yonedaEquiv.symm t.edge), _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.curry_evaluateFunctorAt_vertex]
      rfl
    have he := congrArg (fun f => f.app (Opposite.op ⦋1⦌) a) hc
    change (SSet.yonedaEquiv.symm v).app (Opposite.op ⦋1⦌) a =
      H.h.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant k 1, a) at he
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one] at he
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr
      (e := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex ((SSet.yonedaEquiv.symm v).app _ a)).map
        ((truncation 2).map (𝟙 Y)))
      (f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (H.h.app _ (K.σ 0 k, a))) he).mp hi

/-- 元の比較 prism の商後合成は、商側で同じ比較辺を uncurry したもの。 -/
lemma functorEdgePrism_postcomp {K X Y : SSet.{u}} (p : X ⟶ Y) {F G : K ⟶ X}
    (t : Truncated.Edge (X := (truncation 2).obj ((ihom K).obj X))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge t).h ≫ p =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge (f := F ≫ p) (g := G ≫ p)
        (t.map ((truncation 2).map ((ihom K).map p)))).h := by
  change uncurry (SSet.yonedaEquiv.symm t.edge) ≫ p =
    uncurry (SSet.yonedaEquiv.symm (((ihom K).map p).app (Opposite.op ⦋1⦌) t.edge))
  rw [← SSet.yonedaEquiv_symm_comp, uncurry_natural_right]
  rfl

/-- 全辺反転は、元の実図式の前合成で保たれる。 -/
lemma invertsAllEdges_precomp {A X Y : SSet.{u}} (j : A ⟶ X) (F : X ⟶ Y)
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges F Set.univ) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges (j ≫ F) Set.univ := by
  intro s _
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr
    (e := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (j.app (Opposite.op ⦋1⦌) s)).map ((truncation 2).map F))
    (f := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex s).map ((truncation 2).map (j ≫ F))) rfl).mp
      (hF (Set.mem_univ _))

/-- 比較辺の全 prism は、その一次単体を変えず元の core 逆像内に入る。 -/
def corePreimageComparisonHomotopy {K X Y : SSet.{u}} [Quasicategory Y]
    (p : X ⟶ Y) {F G : K ⟶ X}
    (t : Truncated.Edge (X := (truncation 2).obj ((ihom K).obj X))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G))
    (ht : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := (ihom K).obj Y)
      (t.map ((truncation 2).map ((ihom K).map p))))
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges (F ≫ p) Set.univ) (hG : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges (G ≫ p) Set.univ) :
    SSet.Homotopy (corePreimageLift p F hF) (corePreimageLift p G hG) := by
  let H := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge t
  have hH : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges (H.h ≫ p) Set.univ := by
    rw [functorEdgePrism_postcomp]
    exact functorEdgePrism_invertsAllEdges _ ht hF hG
  let L := corePreimageLift p H.h hH
  refine { h := L, h₀ := ?_, h₁ := ?_, rel := ?_ }
  · apply (cancel_mono ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore Y).preimage p).ι).mp
    rw [Category.assoc, corePreimageLift_ι, H.h₀]
    rfl
  · apply (cancel_mono ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore Y).preimage p).ι).mp
    rw [Category.assoc, corePreimageLift_ι, H.h₁]
    rfl
  · apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    exact False.elim s.1.property

/-- 元の比較 prism を、同じ全単体写像として厳密回収する。 -/
lemma corePreimageComparisonHomotopy_ι {K X Y : SSet.{u}} [Quasicategory Y]
    (p : X ⟶ Y) {F G : K ⟶ X}
    (t : Truncated.Edge (X := (truncation 2).obj ((ihom K).obj X))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G))
    (ht : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := (ihom K).obj Y)
      (t.map ((truncation 2).map ((ihom K).map p))))
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges (F ≫ p) Set.univ) (hG : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges (G ≫ p) Set.univ) :
    (corePreimageComparisonHomotopy p t ht hF hG).h ≫
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore Y).preimage p).ι = (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge t).h := rfl

/-- 全辺反転する元の全図式の、同じ core への持ち上げ。 -/
def allEdgesCoreLift {K Y : SSet.{u}} (F : K ⟶ Y) (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges F Set.univ) :
    K ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore Y : SSet.{u}) :=
  corePreimageLift (𝟙 Y) F (by simpa only [Category.comp_id] using hF)

lemma allEdgesCoreLift_ι {K Y : SSet.{u}} (F : K ⟶ Y) (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges F Set.univ) :
    allEdgesCoreLift F hF ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore Y).ι = F := rfl

/-- 両端が core 内にある実可逆比較を、その全 prism のまま core 内へ戻す。 -/
def allEdgesCoreComparisonHomotopy {K Y : SSet.{u}} [Quasicategory Y]
    {F G : K ⟶ Y}
    (t : Truncated.Edge (X := (truncation 2).obj ((ihom K).obj Y))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G))
    (ht : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := (ihom K).obj Y) t)
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges F Set.univ) (hG : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges G Set.univ) :
    SSet.Homotopy (allEdgesCoreLift F hF) (allEdgesCoreLift G hG) :=
  corePreimageComparisonHomotopy (𝟙 Y) t (ht.map ((ihom K).map (𝟙 Y)))
    (by simpa only [Category.comp_id] using hF)
    (by simpa only [Category.comp_id] using hG)

lemma allEdgesCoreComparisonHomotopy_ι {K Y : SSet.{u}} [Quasicategory Y]
    {F G : K ⟶ Y}
    (t : Truncated.Edge (X := (truncation 2).obj ((ihom K).obj Y))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G))
    (ht : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := (ihom K).obj Y) t)
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges F Set.univ) (hG : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges G Set.univ) :
    (allEdgesCoreComparisonHomotopy t ht hF hG).h ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore Y).ι =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge t).h := rfl

end SerrePositivity.KST.LocalizingInvariants
