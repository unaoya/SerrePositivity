module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentLeftHomComparison

/-!
概要：標準の豊穣 Hom 比較と豊穣関手による後合成の整合性。
方針：各 Hom の simplex の最大元評価と豊穣関手の単位則を直接比較する。
規約：対象の宇宙は共通とし、Hom の宇宙は異なってよい。
使われ方：Kerodon §4.6.7（Tag 01LA）、HTT 4.2.4.1 の係数比較の自然性。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory SSet SimplicialThickening
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：Hom 比較の頂点の作用は豊穣関手の対象の作用と可換。
方針：最後の頂点か否かで場合分けする。
規約：頂点数は n+2。
使われ方：Kerodon §4.6.7（Tag 01LA） の後合成による二端点の同定。 -/
lemma coherentHomComparisonObj_post {C D : Type v} [Category.{u} C] [Category.{u} D]
    [SimplicialCategory C] [SimplicialCategory D] (F : EnrichedFunctor SSet C D)
    (x y : C) {n : ℕ} (i : Fin (n + 2)) :
    F.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj x y i) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj (F.obj x) (F.obj y) i := by
  induction i using Fin.lastCases <;>
    simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj, Fin.lastCases_last, Fin.lastCases_castSucc]

/-- 概要：Hom の simplex の比較は豊穣関手の後合成と可換。
方針：二端点の分岐ごとに恒等の保存と最大元評価の自然性を使う。
規約：Kan 性を仮定しない、全ての次数での厳密な等式。
使われ方：Kerodon §4.6.7（Tag 01LA）、係数図式の実際の射の自然性。 -/
lemma coherentHomComparisonSimplex_post {C D : Type v} [Category.{u} C] [Category.{u} D]
    [SimplicialCategory C] [SimplicialCategory D] (F : EnrichedFunctor SSet C D)
    {x y : C} {n : ℕ} (σ : (SimplicialCategory.sHom x y) _⦋n⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonSimplex σ).comp SSet F =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonSimplex ((F.map x y).app (Opposite.op ⦋n⦌) σ) := by
  have hmap {a b a' b' : C} (ha : a = a') (hb : b = b') :
      F.map a b ≫ eqToHom (congrArg₂ SimplicialCategory.sHom
        (congrArg F.obj ha) (congrArg F.obj hb)) =
      eqToHom (congrArg₂ SimplicialCategory.sHom ha hb) ≫ F.map a' b' := by
    subst a'
    subst b'
    simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
  refine EnrichedFunctor.ext SSet
    (fun i ↦ coherentHomComparisonObj_post F x y i.as.down) (fun i j ↦ ?_)
  rcases i with ⟨⟨i⟩⟩
  rcases j with ⟨⟨j⟩⟩
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonHom σ i j ≫
    F.map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj x y i) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj x y j)) ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom
        (coherentHomComparisonObj_post F x y i)
        (coherentHomComparisonObj_post F x y j)) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonHom ((F.map x y).app (Opposite.op ⦋n⦌) σ) i j
  induction i using Fin.lastCases (n := n + 1) <;>
    induction j using Fin.lastCases (n := n + 1)
  case last.last  =>
    apply (cancel_mono (eqToHom (congrArg₂ SimplicialCategory.sHom
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_last (F.obj x) (F.obj y) n)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_last (F.obj x) (F.obj y) n)))).1
    rw [Category.assoc, eqToHom_trans]
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonHom σ (Fin.last (n + 1)) (Fin.last (n + 1)) ≫
      F.map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj x y (Fin.last (n + 1)))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj x y (Fin.last (n + 1)))) ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom
        (congrArg F.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_last x y n))
        (congrArg F.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_last x y n))) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonHom ((F.map x y).app (Opposite.op ⦋n⦌) σ)
        (Fin.last (n + 1)) (Fin.last (n + 1)) ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_last (F.obj x) (F.obj y) n)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_last (F.obj x) (F.obj y) n))
    rw [Category.assoc,
      hmap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_last x y n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_last x y n),
      ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparisonHom_last_last,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparisonHom_last_last]
    simp only [Category.assoc, F.map_id]
  case cast.last i =>
    apply (cancel_mono (eqToHom (congrArg₂ SimplicialCategory.sHom
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_cast (F.obj x) (F.obj y) i)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_last (F.obj x) (F.obj y) n)))).1
    rw [Category.assoc, eqToHom_trans]
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonHom σ (i.castSucc) (Fin.last (n + 1)) ≫
      F.map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj x y (i.castSucc))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj x y (Fin.last (n + 1)))) ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom
        (congrArg F.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_cast x y i))
        (congrArg F.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_last x y n))) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonHom ((F.map x y).app (Opposite.op ⦋n⦌) σ)
        (i.castSucc) (Fin.last (n + 1)) ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_cast (F.obj x) (F.obj y) i)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_last (F.obj x) (F.obj y) n))
    rw [Category.assoc,
      hmap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_cast x y i) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_last x y n),
      ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparisonHom_cast_last,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparisonHom_cast_last]
    rw [Category.assoc, SSet.yonedaEquiv_symm_comp]
  case cast.cast i j =>
    apply (cancel_mono (eqToHom (congrArg₂ SimplicialCategory.sHom
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_cast (F.obj x) (F.obj y) i)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_cast (F.obj x) (F.obj y) j)))).1
    rw [Category.assoc, eqToHom_trans]
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonHom σ (i.castSucc) (j.castSucc) ≫
      F.map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj x y (i.castSucc))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj x y (j.castSucc))) ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom
        (congrArg F.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_cast x y i))
        (congrArg F.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_cast x y j))) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonHom ((F.map x y).app (Opposite.op ⦋n⦌) σ)
        (i.castSucc) (j.castSucc) ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_cast (F.obj x) (F.obj y) i)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_cast (F.obj x) (F.obj y) j))
    rw [Category.assoc,
      hmap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_cast x y i) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_cast x y j),
      ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparisonHom_cast_cast,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparisonHom_cast_cast]
    simp only [Category.assoc, F.map_id]
  case last.cast j =>
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro P
    have h := Path.le (P.obj 0)
    change n + 1 ≤ j.val at h
    have := j.isLt
    omega


/-- 概要：coherent nerve の後合成は対象の標準頂点を対応する標準頂点へ送る。
方針：零単体の全 Hom が恒等であることと豊穣関手の単位則を使う。
規約：Kan 性なしでの厳密な等式。
使われ方：Kerodon §4.6.7（Tag 01LA） の pinched Hom の端点の同定。 -/
lemma coherentNervePost_vertex {C D : Type v} [Category.{u} C] [Category.{u} D]
    [SimplicialCategory C] [SimplicialCategory D] (F : EnrichedFunctor SSet C D) (x : C) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentNervePost F).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex x) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (F.obj x) := by
  refine EnrichedFunctor.ext SSet (fun _ ↦ rfl) (fun i j ↦ ?_)
  change ((SemiCartesianMonoidalCategory.toUnit _ ≫ eId SSet x) ≫ F.map x x) ≫
    eqToHom (rfl : SimplicialCategory.sHom (F.obj x) (F.obj x) = _) =
      SemiCartesianMonoidalCategory.toUnit _ ≫ eId SSet (F.obj x)
  simp only [eqToHom_refl, Category.comp_id, Category.assoc, F.map_id]

/-- 概要：pinched Hom の端点の等号による移送は元の単体を変えない。
方針：二つの端点の等号を消去する。
規約：固定条件の証明だけを移送し、元の n+1 単体はそのまま。
使われ方：Kerodon §4.6.7（Tag 01LA） の標準比較の厳密な自然性。 -/
lemma pinchedHom_endpointTransport_val {X : SSet.{u}} {x y x' y' : X _⦋0⦌}
    (hx : x = x') (hy : y = y') {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.Simplex x y n) :
    ((eqToHom (congrArg₂ (fun a b ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (X := X) a b) hx hy)).app
      (Opposite.op ⦋n⦌) s).val = s.val := by
  subst x'
  subst y'
  rfl

/-- 概要：豊穣関手の nerve による Hom の像の端点を標準頂点へそろえる同型。
方針：二端点に後合成の頂点の式を適用する。
規約：順方向は像の端点から標準頂点への移送。
使われ方：Kerodon §4.6.7（Tag 01LA） の豊穣関手への自然性の余域。 -/
noncomputable def coherentHomPostEndpointIso {C D : Type v}
    [Category.{u} C] [Category.{u} D] [SimplicialCategory C] [SimplicialCategory D]
    (F : EnrichedFunctor SSet C D) (x y : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentNervePost F).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex x))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentNervePost F).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex y)) ≅
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (F.obj x)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (F.obj y)) :=
  eqToIso (congrArg₂ (fun a b ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (X := SimplicialNerve D) a b)
    (coherentNervePost_vertex F x) (coherentNervePost_vertex F y))

/-- 概要：標準の Hom 比較は豊穣関手による後合成と厳密に可換。
方針：各次数で pinched 単体の値を比較し、端点移送を消して simplex の比較を使う。
規約：対象の宇宙は共通 v、Hom の宇宙は u。Kan 性を仮定しない。
使われ方：Kerodon §4.6.7（Tag 01LA）、HTT 4.2.4.1 の係数図式の自然比較。 -/
lemma coherentHomComparison_post {C D : Type v} [Category.{u} C] [Category.{u} D]
    [SimplicialCategory C] [SimplicialCategory D] (F : EnrichedFunctor SSet C D) (x y : C) :
    (SSet.uliftFunctor.{v, u}).map (F.map x y) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparison (F.obj x) (F.obj y) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparison x y ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentNervePost F) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex y) ≫
        (coherentHomPostEndpointIso F x y).hom := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro σ
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.Simplex.ext
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonSimplex ((F.map x y).app (Opposite.op ⦋n⦌) σ.down) =
    ((eqToHom (congrArg₂ (fun a b ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (X := SimplicialNerve D) a b)
      (coherentNervePost_vertex F x) (coherentNervePost_vertex F y))).app
        (Opposite.op ⦋n⦌)
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentNervePost F) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex x)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex y)).app (Opposite.op ⦋n⦌)
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparison x y).app (Opposite.op ⦋n⦌) σ))).val
  rw [pinchedHom_endpointTransport_val
    (coherentNervePost_vertex F x) (coherentNervePost_vertex F y)]
  exact (coherentHomComparisonSimplex_post F σ.down).symm

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
