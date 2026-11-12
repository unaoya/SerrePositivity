module
public import SerrePositivity.KST.SConstruction.CoherentInsertionEndpointEdges

/-! # 二点挿入の実二単体の四辺と豊穣合成の照合
概要：同じ二単体の下辺を元の比較辺へ、上辺を固定因子との実豊穣合成へ照合する。
方針：元の全一単体の等号に豊穣作用を適用し、その全次数の合成則を使う。
規約：Kan 性や類の等式を使わず、元の全辺と同じ二単体を保持する。
使われ方：三入力 BF 四面体からの二経路を、元の合成面と実合成へ復号する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SimplicialThickening MonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable {J : Type u} [LinearOrder J] {a b c d : J}

/-- Path の合成の全次数の豊穣作用は、元の二つの全作用を実合成した値。 -/
lemma coherentEnrichedPathComposite_app {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (s : EnrichedFunctor SSet.{u} (SimplicialThickening J) C) (a b c : J) (n : ℕ)
    (p : (nerve (Path a b)) _⦋n⦌) (q : (nerve (Path b c)) _⦋n⦌) :
    (s.map (.mk a) (.mk c)).app (Opposite.op ⦋n⦌)
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCompMap a b c).app (Opposite.op ⦋n⦌) (p, q)) =
      (eComp SSet (s.obj (.mk a)) (s.obj (.mk b)) (s.obj (.mk c))).app (Opposite.op ⦋n⦌)
        ((s.map (.mk a) (.mk b)).app (Opposite.op ⦋n⦌) p,
          (s.map (.mk b) (.mk c)).app (Opposite.op ⦋n⦌) q) := by
  have hm : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCompMap a b c ≫ s.map (.mk a) (.mk c) =
      (s.map (.mk a) (.mk b) ⊗ₘ s.map (.mk b) (.mk c)) ≫
        eComp SSet (s.obj (.mk a)) (s.obj (.mk b)) (s.obj (.mk c)) :=
    s.map_comp (.mk a) (.mk b) (.mk c)
  have h := ConcreteCategory.congr_hom (NatTrans.congr_app hm (Opposite.op ⦋n⦌))
    (show ((nerve (Path a b)) ⊗ (nerve (Path b c))).obj (Opposite.op ⦋n⦌) from (p, q))
  simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at h
  have hpair : ((s.map (.mk a) (.mk b) ⊗ₘ s.map (.mk b) (.mk c)).app
      (Opposite.op ⦋n⦌)) (p, q) =
      ((s.map (.mk a) (.mk b)).app (Opposite.op ⦋n⦌) p,
        (s.map (.mk b) (.mk c)).app (Opposite.op ⦋n⦌) q) := by rfl
  exact h.trans (congrArg
    ((eComp SSet (s.obj (.mk a)) (s.obj (.mk b)) (s.obj (.mk c))).app
      (Opposite.op ⦋n⦌)) hpair)

/-- 第一挿入経路の下辺は、元の長辺から第一切断の合成への全比較辺。 -/
lemma coherentDoubleInsertMappedFirstLower {E : SSet.{u}}
    (m : nerve (Path a c) ⟶ E) (hab : a ≤ b) (hbc : b ≤ c)
    (had : a ≤ d) (hdc : d ≤ c) :
    E.δ 2 (coherentDoubleInsertMappedFirstTriangle m hab hbc had hdc
      (coherentEndpointPath (hab.trans hbc))).simplex =
      ((nerve.edgeMk (coherentEndpointPathToComposite hab hbc)).map m).edge := by
  refine (coherentDoubleInsertMappedFirstTriangle m hab hbc had hdc
    (coherentEndpointPath (hab.trans hbc))).d₂.trans ?_
  exact congrArg (m.app (Opposite.op ⦋1⦌)) (coherentInsertEndpoint_edge hab hbc)

/-- 第二挿入経路の下辺は、元の長辺から第二切断の合成への全比較辺。 -/
lemma coherentDoubleInsertMappedSecondLower {E : SSet.{u}}
    (m : nerve (Path a c) ⟶ E) (hab : a ≤ b) (hbc : b ≤ c)
    (had : a ≤ d) (hdc : d ≤ c) :
    E.δ 2 (coherentDoubleInsertMappedSecondTriangle m hab hbc had hdc
      (coherentEndpointPath (had.trans hdc))).simplex =
      ((nerve.edgeMk (coherentEndpointPathToComposite had hdc)).map m).edge := by
  refine (coherentDoubleInsertMappedSecondTriangle m hab hbc had hdc
    (coherentEndpointPath (had.trans hdc))).d₂.trans ?_
  exact congrArg (m.app (Opposite.op ⦋1⦌)) (coherentInsertEndpoint_edge had hdc)

/-- 第一経路の上辺は、固定前半と後半の元の比較辺の実豊穣合成そのもの。 -/
lemma coherentDoubleInsertMappedFirstUpper
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (s : EnrichedFunctor SSet.{u} (SimplicialThickening J) C)
    (hab : a ≤ b) (hbd : b ≤ d) (hdc : d ≤ c) :
    (SimplicialCategory.sHom (s.obj (.mk a)) (s.obj (.mk c))).δ 0
        (coherentDoubleInsertMappedFirstTriangle (s.map (.mk a) (.mk c))
          hab (hbd.trans hdc) (hab.trans hbd) hdc
          (coherentEndpointPath ((hab.trans hbd).trans hdc))).simplex =
      (eComp SSet (s.obj (.mk a)) (s.obj (.mk b)) (s.obj (.mk c))).app (Opposite.op ⦋1⦌)
        (((nerve.edgeMk (𝟙 (coherentEndpointPath hab))).map (s.map (.mk a) (.mk b))).edge,
          ((nerve.edgeMk (coherentEndpointPathToComposite hbd hdc)).map
            (s.map (.mk b) (.mk c))).edge) := by
  refine (coherentDoubleInsertMappedFirstTriangle (s.map (.mk a) (.mk c))
    hab (hbd.trans hdc) (hab.trans hbd) hdc
    (coherentEndpointPath ((hab.trans hbd).trans hdc))).d₀.trans ?_
  exact (congrArg ((s.map (.mk a) (.mk c)).app (Opposite.op ⦋1⦌))
    (coherentDoubleInsertFirstUpper_edge hab hbd hdc)).trans
      (coherentEnrichedPathComposite_app s a b c 1 _ _)

/-- 第二経路の上辺は、前半の元の比較辺と固定後半の実豊穣合成そのもの。 -/
lemma coherentDoubleInsertMappedSecondUpper
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (s : EnrichedFunctor SSet.{u} (SimplicialThickening J) C)
    (hab : a ≤ b) (hbd : b ≤ d) (hdc : d ≤ c) :
    (SimplicialCategory.sHom (s.obj (.mk a)) (s.obj (.mk c))).δ 0
        (coherentDoubleInsertMappedSecondTriangle (s.map (.mk a) (.mk c))
          hab (hbd.trans hdc) (hab.trans hbd) hdc
          (coherentEndpointPath ((hab.trans hbd).trans hdc))).simplex =
      (eComp SSet (s.obj (.mk a)) (s.obj (.mk d)) (s.obj (.mk c))).app (Opposite.op ⦋1⦌)
        (((nerve.edgeMk (coherentEndpointPathToComposite hab hbd)).map
            (s.map (.mk a) (.mk d))).edge,
          ((nerve.edgeMk (𝟙 (coherentEndpointPath hdc))).map (s.map (.mk d) (.mk c))).edge) := by
  refine (coherentDoubleInsertMappedSecondTriangle (s.map (.mk a) (.mk c))
    hab (hbd.trans hdc) (hab.trans hbd) hdc
    (coherentEndpointPath ((hab.trans hbd).trans hdc))).d₀.trans ?_
  exact (congrArg ((s.map (.mk a) (.mk c)).app (Opposite.op ⦋1⦌))
    (coherentDoubleInsertSecondUpper_edge hab hbd hdc)).trans
      (coherentEnrichedPathComposite_app s a d c 1 _ _)

end SerrePositivity.KST.SConstruction
