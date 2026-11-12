module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FunctorEdgePointwise

/-!
概要：内部 Hom の前合成作用を関手の頂点で評価する計算。
方針：評価をモノイダル単位からの射で表し、閉構造の合成の単位則を使う。
規約：前合成のパラメーターとなる射を固定する。
使われ方：Kerodon §4.6.2（Tag 01HM） の比較のホモトピーの前合成作用。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed BraidedCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：頂点での評価は、単位からの射を補って閉構造で評価する射。
方針：単位からの射を頂点で表し直し、各次数で計算する。
規約：単体集合 D,E に前提は不要。
使われ方：Kerodon §4.5.1（Tag 01DQ）、§4.6.2（Tag 01HM） の評価の整合。 -/
lemma evaluateFunctorAt_unitHomEquiv {D E : SSet.{u}} (v : 𝟙_ SSet ⟶ D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := E) (SSet.unitHomEquiv D v) =
      (λ_ ((ihom D).obj E)).inv ≫ (v ▷ ((ihom D).obj E)) ≫ (ihom.ev D).app E := by
  obtain ⟨d, rfl⟩ := (SSet.unitHomEquiv D).symm.surjective v
  rw [Equiv.apply_symm_apply]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro F
  rfl

/-- 概要：curry した射を単位からの頂点で評価すると、元の射のその頂点での制限。
方針：評価の単位表示と curry・評価の恒等式を使う。
規約：パラメーター A と標的 X は任意。
使われ方：Kerodon §4.6.2（Tag 01HM） の前合成ホモトピーの評価。 -/
lemma curry_evaluateFunctorAt_unitHomEquiv {D A X : SSet.{u}}
    (H : D ⊗ A ⟶ X) (v : 𝟙_ SSet ⟶ D) :
    curry H ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) (SSet.unitHomEquiv D v) =
      (λ_ A).inv ≫ (v ▷ A) ≫ H := by
  rw [evaluateFunctorAt_unitHomEquiv, ← Category.assoc, leftUnitor_inv_naturality]
  simp only [Category.assoc]
  rw [← Category.assoc (𝟙_ SSet ◁ curry H), whisker_exchange]
  simp only [Category.assoc]
  rw [whiskerLeft_curry_ihom_ev_app]

/-- 概要：前合成作用を関手 u で評価すると u による後合成。
方針：合成の単位則と二つのテンソル因子の交換を使う。
規約：全ての単体集合に quasicategory 性は不要。
使われ方：Kerodon §4.6.2（Tag 01HM） の比較写像の前合成作用の可逆性。 -/
lemma functorPrecompositionMap_evaluate {A B Z : SSet.{u}} (u : B ⟶ Z) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorPrecompositionMap A B Z ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex u) = (ihom A).map u := by
  change curry ((β_ ((ihom B).obj Z) ((ihom A).obj B)).hom ≫ MonoidalClosed.comp A B Z) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (SSet.unitHomEquiv _ (curry' u)) = _
  rw [curry_evaluateFunctorAt_unitHomEquiv]
  rw [← Category.assoc (curry' u ▷ ((ihom A).obj B)), BraidedCategory.braiding_naturality_left]
  simp only [Category.assoc]
  rw [whiskerLeft_curry'_comp, ← Category.assoc (β_ (𝟙_ SSet) ((ihom A).obj B)).hom,
    braiding_rightUnitor, Iso.inv_hom_id_assoc]

/-- 概要：点ごとに可逆なホモトピーは、任意の quasicategory への前合成作用の同型を与える。
方針：前合成の辺を各関手で評価すると後合成されたホモトピーの辺となることを使う。
規約：元の単体集合 A,B には quasicategory 性を仮定しない。
使われ方：Kerodon §4.6.2（Tag 01HM） の fat join の比較のホモトピー。 -/
noncomputable def functorIsoPrecompositionOfHomotopy {A B : SSet.{u}}
    {f g : A ⟶ B} (H : SSet.Homotopy f g)
    (hH : ∀ a : A _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H a).toTruncated)
    (Z : SSet.{u}) [Quasicategory Z] : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((pre f).app Z) ((pre g).app Z) := by
  let q := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorPrecompositionMap A B Z
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H
  let m : SSet.Truncated.Edge
      (X := (truncation 2).obj ((ihom ((ihom B).obj Z)).obj ((ihom A).obj Z)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((pre f).app Z)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((pre g).app Z)) :=
    { edge := q.app (Opposite.op ⦋1⦌) e.edge
      src_eq := (e.map ((truncation 2).map q)).src_eq.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorPrecompositionMap_vertex f)
      tgt_eq := (e.map ((truncation 2).map q)).tgt_eq.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorPrecompositionMap_vertex g) }
  have hm : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge m := by
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.isInvertibleEdge_iff_evaluateFunctorAt m).mpr
    intro v
    obtain ⟨u, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv B Z).surjective v
    let H' : SSet.Homotopy (f ≫ u) (g ≫ u) :=
      { h := H.h ≫ u
        h₀ := by rw [← Category.assoc, H.h₀]; rfl
        h₁ := by rw [← Category.assoc, H.h₁]; rfl
        rel := by
          apply SSet.hom_ext
          intro n
          apply ConcreteCategory.hom_ext
          intro s
          exact False.elim s.1.property }
    have hH' : ∀ a : A _⦋0⦌,
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H' a).toTruncated := by
      intro a
      exact (hH a).map u
    have hinv := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.functorEdgeOfSimplicialHomotopy_isInvertible_of_pointwise H' hH'
    have he : (m.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := (ihom A).obj Z)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex u)))).edge = (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H').edge := by
      have hq := ConcreteCategory.congr_hom
        (NatTrans.congr_app (functorPrecompositionMap_evaluate (A := A) u) (Opposite.op ⦋1⦌)) e.edge
      change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := (ihom A).obj Z) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex u)).app (Opposite.op ⦋1⦌)
        (q.app (Opposite.op ⦋1⦌) e.edge) = ((ihom A).map u).app (Opposite.op ⦋1⦌) e.edge at hq
      change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := (ihom A).obj Z) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex u)).app (Opposite.op ⦋1⦌)
        (q.app (Opposite.op ⦋1⦌) e.edge) = _
      rw [hq]
      change ((ihom A).map u).app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv (curry H.h)) =
        SSet.yonedaEquiv (curry (H.h ≫ u))
      rw [← SSet.yonedaEquiv_comp, curry_natural_right]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr he).mpr hinv
  haveI := hm
  exact asIso (SSet.Truncated.HomotopyCategory.homMk m)

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
