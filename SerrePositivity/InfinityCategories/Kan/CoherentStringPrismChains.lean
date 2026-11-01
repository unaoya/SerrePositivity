module
public import SerrePositivity.InfinityCategories.Kan.CoherentArrowStrings
public import SerrePositivity.InfinityCategories.Kan.CoherentStringPrismOrders

/-! # 元の合成列からの上下の prism 列
概要：元の射の各合成列に縦辺を加え、同じ積圏の射の合成列を構成する。
方針：入力添字と時刻の二つの順序写像で列を定め、長辺を厳密に回収する。
規約：元の合成列の全射を保持し、長さ零と退化を含める。
使われ方：元の K prism の同じ native Hom へ二つの列を評価する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open scoped Simplicial
variable {I : Type u} [SmallCategory I] {x y : I}

/-- 入力と時刻の二つの再添字で指定した、元の積圏の列。 -/
def coherentStringPrismChain {f : x ⟶ y} (s : CoherentArrowString f) {n : ℕ}
    (p : ⦋n⦌ ⟶ ⦋s.length⦌) (q : ⦋n⦌ ⟶ ⦋1⦌) :
    (nerve (I × ULift.{u} (Fin 2))) _⦋n⦌ :=
  (p.toOrderHom.monotone.functor ⋙ s.chain).prod'
    (q.toOrderHom.monotone.functor ⋙
      (ULift.orderIso : ULift.{u} (Fin 2) ≃o Fin 2).symm.monotone.functor)

/-- 列全体の再添字は、元の入力と時刻の再添字そのもの。 -/
lemma coherentStringPrismChain_reindex {f : x ⟶ y} (s : CoherentArrowString f)
    {m n : ℕ} (p : ⦋n⦌ ⟶ ⦋s.length⦌) (q : ⦋n⦌ ⟶ ⦋1⦌) (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    (nerve (I × ULift.{u} (Fin 2))).map θ.op (coherentStringPrismChain s p q) =
      coherentStringPrismChain s (θ ≫ p) (θ ≫ q) := rfl

/-- 積圏の長辺は、指定した元の射と元の縦辺そのもの。 -/
lemma coherentStringPrismChain_longEdge {f : x ⟶ y} (s : CoherentArrowString f)
    {n : ℕ} (p : ⦋n⦌ ⟶ ⦋s.length⦌) (q : ⦋n⦌ ⟶ ⦋1⦌)
    (hp : coherentStringEndpointMap n ≫ p = coherentStringEndpointMap s.length)
    (hq : coherentStringEndpointMap n ≫ q = 𝟙 ⦋1⦌) :
    (nerve (I × ULift.{u} (Fin 2))).map (coherentStringEndpointMap n).op
      (coherentStringPrismChain s p q) =
      (nerve.edgeMk ((f, homOfLE (by change (0 : Fin 2) ≤ 1; decide)) :
        (x, ULift.up (0 : Fin 2)) ⟶ (y, ULift.up (1 : Fin 2)))).edge := by
  rw [coherentStringPrismChain_reindex, hp, hq]
  change ((nerve I).map (coherentStringEndpointMap s.length).op s.chain).prod' _ = _
  rw [s.long_edge]
  refine ComposableArrows.ext₁ (F := _) (G := _) ?_ ?_ ?_
  · rfl
  · rfl
  · simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    apply Prod.ext
    · rfl
    · exact Subsingleton.elim _ _


/-- 元の列の精密化に沿う、積圏の列全体の厳密な一致。 -/
lemma coherentStringPrismChain_refinement {f : x ⟶ y} {s t : CoherentArrowString f}
    (a : s ⟶ t) {n : ℕ} (p : ⦋n⦌ ⟶ ⦋s.length⦌) (q : ⦋n⦌ ⟶ ⦋1⦌) :
    coherentStringPrismChain t (p ≫ a.map) q = coherentStringPrismChain s p q := by
  have ha : a.map.toOrderHom.monotone.functor ⋙ t.chain = s.chain := a.comm
  change (p.toOrderHom.monotone.functor ⋙ (a.map.toOrderHom.monotone.functor ⋙
    t.chain)).prod' _ = _
  rw [ha]
  rfl

/-- 元の列に下側の縦辺を加えた、同じ積圏の長辺の合成列。 -/
def coherentLowerPrismString {f : x ⟶ y} (s : CoherentArrowString f) :
    CoherentArrowString (I := I × ULift.{u} (Fin 2)) ((f, homOfLE (by change (0 : Fin 2) ≤ 1; decide)) :
      (x, ULift.up (0 : Fin 2)) ⟶ (y, ULift.up (1 : Fin 2))) where
  length := s.length + 1
  chain := coherentStringPrismChain s (coherentLowerStringIndex _) (coherentLowerStringTime _)
  long_edge := coherentStringPrismChain_longEdge s _ _
    (coherentStringEndpointMap_comp _ (coherentLowerStringIndex_first _)
      (coherentLowerStringIndex_last _)) (by
      refine SimplexCategory.Hom.ext_one_left _ _ ?_ ?_
      · change (coherentLowerStringTime s.length).toOrderHom
          ((coherentStringEndpointMap (s.length + 1)).toOrderHom 0) = 0
        rw [coherentStringEndpointMap_first, coherentLowerStringTime_first]
      · change (coherentLowerStringTime s.length).toOrderHom
          ((coherentStringEndpointMap (s.length + 1)).toOrderHom 1) = 1
        rw [coherentStringEndpointMap_last, coherentLowerStringTime_last])

/-- 下側の列への精密化は、元の列と時刻を全射で保持する。 -/
def coherentLowerPrismStringMap {f : x ⟶ y} {s t : CoherentArrowString f}
    (a : s ⟶ t) : coherentLowerPrismString s ⟶ coherentLowerPrismString t where
  map := coherentLowerStringExtend a.map
  first := coherentLowerStringExtend_first a.map a.first
  last := coherentLowerStringExtend_last a.map
  comm := by
    change (nerve (I × ULift.{u} (Fin 2))).map (coherentLowerStringExtend a.map).op
      (coherentStringPrismChain t (coherentLowerStringIndex _) (coherentLowerStringTime _)) = _
    rw [coherentStringPrismChain_reindex, coherentLowerStringExtend_index _ a.last,
      coherentLowerStringExtend_time, coherentStringPrismChain_refinement]
    rfl

/-- 元の射の全合成列を、下側の全因子分解列へ送る関手。 -/
def coherentLowerPrismStringFunctor (f : x ⟶ y) :
    CoherentArrowString f ⥤ CoherentArrowString (I := I × ULift.{u} (Fin 2)) ((f, homOfLE (by change (0 : Fin 2) ≤ 1; decide)) :
      (x, ULift.up (0 : Fin 2)) ⟶ (y, ULift.up (1 : Fin 2))) where
  obj := coherentLowerPrismString
  map := coherentLowerPrismStringMap
  map_id _ := CoherentArrowStringHom.ext (coherentLowerStringExtend_id _)
  map_comp _ _ := CoherentArrowStringHom.ext (coherentLowerStringExtend_comp _ _)

/-- 元の列に上側の縦辺を加えた、同じ積圏の長辺の合成列。 -/
def coherentUpperPrismString {f : x ⟶ y} (s : CoherentArrowString f) :
    CoherentArrowString (I := I × ULift.{u} (Fin 2)) ((f, homOfLE (by change (0 : Fin 2) ≤ 1; decide)) :
      (x, ULift.up (0 : Fin 2)) ⟶ (y, ULift.up (1 : Fin 2))) where
  length := s.length + 1
  chain := coherentStringPrismChain s (coherentUpperStringIndex _) (coherentUpperStringTime _)
  long_edge := coherentStringPrismChain_longEdge s _ _
    (coherentStringEndpointMap_comp _ (coherentUpperStringIndex_first _)
      (coherentUpperStringIndex_last _)) (by
      refine SimplexCategory.Hom.ext_one_left _ _ ?_ ?_
      · change (coherentUpperStringTime s.length).toOrderHom
          ((coherentStringEndpointMap (s.length + 1)).toOrderHom 0) = 0
        rw [coherentStringEndpointMap_first, coherentUpperStringTime_first]
      · change (coherentUpperStringTime s.length).toOrderHom
          ((coherentStringEndpointMap (s.length + 1)).toOrderHom 1) = 1
        rw [coherentStringEndpointMap_last, coherentUpperStringTime_last])

/-- 上側の列への精密化は、元の列と時刻を全射で保持する。 -/
def coherentUpperPrismStringMap {f : x ⟶ y} {s t : CoherentArrowString f}
    (a : s ⟶ t) : coherentUpperPrismString s ⟶ coherentUpperPrismString t where
  map := coherentUpperStringExtend a.map
  first := coherentUpperStringExtend_zero a.map
  last := coherentUpperStringExtend_last a.map a.last
  comm := by
    change (nerve (I × ULift.{u} (Fin 2))).map (coherentUpperStringExtend a.map).op
      (coherentStringPrismChain t (coherentUpperStringIndex _) (coherentUpperStringTime _)) = _
    rw [coherentStringPrismChain_reindex, coherentUpperStringExtend_index _ a.first,
      coherentUpperStringExtend_time, coherentStringPrismChain_refinement]
    rfl

/-- 元の射の全合成列を、上側の全因子分解列へ送る関手。 -/
def coherentUpperPrismStringFunctor (f : x ⟶ y) :
    CoherentArrowString f ⥤ CoherentArrowString (I := I × ULift.{u} (Fin 2)) ((f, homOfLE (by change (0 : Fin 2) ≤ 1; decide)) :
      (x, ULift.up (0 : Fin 2)) ⟶ (y, ULift.up (1 : Fin 2))) where
  obj := coherentUpperPrismString
  map := coherentUpperPrismStringMap
  map_id _ := CoherentArrowStringHom.ext (coherentUpperStringExtend_id _)
  map_comp _ _ := CoherentArrowStringHom.ext (coherentUpperStringExtend_comp _ _)

end SerrePositivity.KST.SConstruction
