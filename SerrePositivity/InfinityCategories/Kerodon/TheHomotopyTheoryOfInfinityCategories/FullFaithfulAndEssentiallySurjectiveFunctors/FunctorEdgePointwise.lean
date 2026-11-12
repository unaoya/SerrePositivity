module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorComposition
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：関手単体集合の辺の可逆性の点ごとの判定。
方針：可逆 path の普遍ホモトピーを、定値 path の切断による前合成で検出する。
規約：同じ両端を結ぶ別の同型の存在ではなく、指定された辺の可逆性を扱う。
使われ方：Kerodon §4.5.1（Tag 01DQ）、§4.6.2（Tag 01HM）、§7.1.8（Tag 02X8） の比較のホモトピー。

対応節は Kerodon 4.8（Tag 0578）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors

/-- 概要：充満忠実な関手は辺の可逆性を反映する。
方針：ホモトピー圏の充満忠実な関手が同型を反映することを使う。
規約：両端の単体集合は quasicategory。
使われ方：Kerodon §4.8.3（Tag 05AW） の可逆性の検出。 -/
@[kerodon 01JN]
lemma IsFullyFaithful.reflects_isInvertibleEdge {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {f : X ⟶ Y} (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful f)
    {x y : X _⦋0⦌} (e : SSet.Truncated.Edge (X := (truncation 2).obj X) x y)
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (e.map ((truncation 2).map f))) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge e := by
  let F := (hoFunctor.map f).toFunctor
  haveI : F.Full := hf.toHoFullyFaithful.full
  haveI : F.Faithful := hf.toHoFullyFaithful.faithful
  haveI : IsIso (F.map (SSet.Truncated.HomotopyCategory.homMk e)) := he
  exact isIso_of_reflects_iso _ F

/-- 概要：定値 path を可逆 path へ含めると第二射影の curry となる。
方針：全部分複体への持ち上げの包含の等式を使う。
規約：標的に quasicategory 性は不要。
使われ方：Kerodon §4.5.3（Tag 032Y） の定値 path の普遍ホモトピーの計算。 -/
lemma equivalencePathRefl_ι (Y : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathRefl Y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι Y = curry (snd (Δ[1] : SSet.{u}) Y) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _

/-- 概要：可逆 path の始点評価と終点評価を結ぶ普遍ホモトピー。
方針：可逆 path の包含を uncurry し、二因子を交換する。
規約：ホモトピーの区間は第二因子。
使われ方：Kerodon §4.5.1（Tag 01DQ） の指定された関手の辺の可逆性。 -/
noncomputable def equivalencePathHomotopy (Y : SSet.{u}) :
    SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint Y 0) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint Y 1) where
  h := (β_ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePath Y) (Δ[1] : SSet.{u})).hom ≫ uncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι Y)
  h₀ := by
    change SSet.ι₀ ≫ (β_ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePath Y) (Δ[1] : SSet.{u})).hom ≫
      uncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι Y) = _
    rw [← Category.assoc]
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePath Y) ≫ uncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι Y) = _
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval, curry_uncurry]
    rfl
  h₁ := by
    change SSet.ι₁ ≫ (β_ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePath Y) (Δ[1] : SSet.{u})).hom ≫
      uncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι Y) = _
    rw [← Category.assoc]
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePath Y) ≫ uncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι Y) = _
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval, curry_uncurry]
    rfl
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    exact False.elim s.1.property

/-- 概要：普遍ホモトピーを定値 path に制限すると第二因子の区間を忘れる。
方針：定値 path の包含の等式を uncurry する。
規約：結果は Y×Δ[1]→Y の第一射影。
使われ方：Kerodon §4.5.1（Tag 01DQ） の前合成による可逆性の検出。 -/
lemma equivalencePathHomotopy_refl (Y : SSet.{u}) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathRefl Y ▷ (Δ[1] : SSet.{u})) ≫ (equivalencePathHomotopy Y).h =
      fst Y (Δ[1] : SSet.{u}) := by
  let R := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathRefl Y
  have hswap : (R ▷ (Δ[1] : SSet.{u})) ≫ (β_ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePath Y) (Δ[1] : SSet.{u})).hom =
      (β_ Y (Δ[1] : SSet.{u})).hom ≫ (Δ[1] ◁ R) := rfl
  change (R ▷ (Δ[1] : SSet.{u})) ≫ (β_ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePath Y) (Δ[1] : SSet.{u})).hom ≫
      uncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι Y) = _
  rw [← Category.assoc, hswap, Category.assoc, ← uncurry_natural_left,
    equivalencePathRefl_ι, uncurry_curry]
  rfl

/-- 概要：可逆 path の普遍ホモトピーが定める関手単体集合の辺は可逆。
方針：定値 path の切断による前合成が同値であり、制限後の辺が恒等であることを使う。
規約：標的 Y は quasicategory。
使われ方：Kerodon §4.5.1（Tag 01DQ） の点ごとの可逆性から指定された辺の可逆性へ。 -/
lemma equivalencePathHomotopy_edge_isInvertible (Y : SSet.{u}) [Quasicategory Y] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (equivalencePathHomotopy Y)) := by
  let R := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathRefl Y
  let q := (pre R).app Y
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (equivalencePathHomotopy Y)
  have hq₀ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint Y 0)
  have hR : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence R := hq₀.cancel_right (by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathRefl Y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint Y 0)
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathRefl_endpoint]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence.refl Y).isQCatEquivalence)
  have hq : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful q := (hR.precompose Y).isFullyFaithful
  apply hq.reflects_isInvertibleEdge e
  have he : (e.map ((truncation 2).map q)).edge =
      (SSet.Truncated.Edge.id (X := (truncation 2).obj ((ihom Y).obj Y))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (𝟙 Y))).edge := by
    change q.app (Opposite.op ⦋1⦌)
      (SSet.yonedaEquiv (curry (equivalencePathHomotopy Y).h)) = _
    rw [← SSet.yonedaEquiv_comp]
    change SSet.yonedaEquiv (curry (equivalencePathHomotopy Y).h ≫ (pre R).app Y) = _
    rw [curry_pre_app, equivalencePathHomotopy_refl]
    change SSet.yonedaEquiv (curry (fst Y (Δ[1] : SSet.{u}))) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (𝟙 Y)) 1
    apply CategoryTheory.Functor.functorHom_ext
    intro d α
    apply ConcreteCategory.hom_ext
    intro y
    rfl
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr he).mpr
  change IsIso (SSet.Truncated.HomotopyCategory.homMk (SSet.Truncated.Edge.id _))
  rw [SSet.Truncated.HomotopyCategory.homMk_id]
  infer_instance

/-- 概要：全ての頂点で可逆な辺を持つホモトピーは、指定された関手の辺自体を可逆にする。
方針：ホモトピーを可逆 path の普遍ホモトピーの前合成として表す。
規約：標的 X は quasicategory、始域 K は任意。
使われ方：Kerodon §4.5.1（Tag 01DQ）、§4.6.2（Tag 01HM） の点ごとの可逆性の判定。 -/
lemma functorEdgeOfSimplicialHomotopy_isInvertible_of_pointwise {K X : SSet.{u}}
    [Quasicategory X] {f g : K ⟶ X} (H : SSet.Homotopy f g)
    (hH : ∀ k : K _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H k).toTruncated) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H) := by
  let H' := (β_ (Δ[1] : SSet.{u}) K).hom ≫ H.h
  have hv : ∀ k, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsEquivalencePathVertex ((curry H').app (Opposite.op ⦋0⦌) k) := by
    intro k
    unfold _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsEquivalencePathVertex
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge_curry]
    have he : H'.app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant k 1) =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H k).edge := by
      change H.h.app (Opposite.op ⦋1⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant k 1, SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u}))) =
        H.h.app (Opposite.op ⦋1⦌)
          ((SSet.Truncated.Edge.id (X := (truncation 2).obj K) k).edge, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge)
      have hi : SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge := by
        apply stdSimplex.ext
        intro i
        fin_cases i <;> rfl
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one, hi]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr he).mpr (hH k)
  let a : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePath X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsEquivalencePathVertex (curry H') hv
  have ha : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι X = curry H' := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _
  have hpre : (a ▷ (Δ[1] : SSet.{u})) ≫ (equivalencePathHomotopy X).h = H.h := by
    have hswap : (a ▷ (Δ[1] : SSet.{u})) ≫
        (β_ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePath X) (Δ[1] : SSet.{u})).hom =
          (β_ K (Δ[1] : SSet.{u})).hom ≫ (Δ[1] ◁ a) := rfl
    change (a ▷ (Δ[1] : SSet.{u})) ≫ (β_ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePath X) (Δ[1] : SSet.{u})).hom ≫
      uncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι X) = _
    rw [← Category.assoc, hswap, Category.assoc, ← uncurry_natural_left, ha, uncurry_curry]
    rfl
  have hm := (equivalencePathHomotopy_edge_isInvertible X).map ((pre a).app X)
  have he : ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (equivalencePathHomotopy X)).map
      ((truncation 2).map ((pre a).app X))).edge = (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H).edge := by
    change ((pre a).app X).app (Opposite.op ⦋1⦌)
      (SSet.yonedaEquiv (curry (equivalencePathHomotopy X).h)) = SSet.yonedaEquiv (curry H.h)
    rw [← SSet.yonedaEquiv_comp, curry_pre_app, hpre]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr he).mp hm

/-- 概要：関手単体集合の指定された辺は、全ての評価で可逆であることと可逆であることが同値。
方針：順方向は評価で写し、逆方向はその辺の uncurry の点ごとの可逆性を使う。
規約：標的 X は quasicategory、パラメーター K は任意。
使われ方：Kerodon §4.5.1（Tag 01DQ） の可逆な自然変換の点ごとの判定。 -/
@[kerodon 01DK]
lemma isInvertibleEdge_iff_evaluateFunctorAt {K X : SSet.{u}} [Quasicategory X]
    {f g : K ⟶ X} (e : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom K).obj X))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex g)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge e ↔ ∀ k : K _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (e.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) k))) := by
  constructor
  · intro he k
    exact he.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt k)
  · intro he
    let H := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge e
    have hH : ∀ k : K _⦋0⦌,
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H k).toTruncated := by
      intro k
      exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_edge e k)).mpr (he k)
    have h := functorEdgeOfSimplicialHomotopy_isInvertible_of_pointwise H hH
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H) (f := e) ?_).mp h
    change SSet.yonedaEquiv (curry (uncurry (SSet.yonedaEquiv.symm e.edge))) = e.edge
    rw [curry_uncurry, Equiv.apply_symm_apply]

/-- 概要：点ごとに可逆なホモトピーから、その指定された辺を順方向の射とする関手の同型。
方針：指定された関手の辺の可逆性を使ってホモトピー圏で asIso を取る。
規約：同型の順方向の射はこのホモトピーの辺の類。
使われ方：Kerodon §4.5.1（Tag 01DQ）、§4.6.2（Tag 01HM） の実際のホモトピーによる比較。 -/
@[kerodon 01DK]
noncomputable def functorIsoOfPointwiseInvertibleHomotopy {K X : SSet.{u}}
    [Quasicategory X] {f g : K ⟶ X} (H : SSet.Homotopy f g)
    (hH : ∀ k : K _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H k).toTruncated) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g := by
  haveI := functorEdgeOfSimplicialHomotopy_isInvertible_of_pointwise H hH
  exact asIso (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H))

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors
