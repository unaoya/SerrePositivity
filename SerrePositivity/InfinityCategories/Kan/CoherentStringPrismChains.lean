module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
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
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Kan
open SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open scoped _root_.Simplicial
variable {I : Type u} [SmallCategory I] {x y : I}

/-- 入力と時刻の二つの再添字で指定した、元の積圏の列。 -/
def coherentStringPrismChain {f : x ⟶ y} (s : _root_.SerrePositivity.InfinityCategories.Kan.CoherentArrowString f) {n : ℕ}
    (p : ⦋n⦌ ⟶ ⦋s.length⦌) (q : ⦋n⦌ ⟶ ⦋1⦌) :
    (nerve (I × ULift.{u} (Fin 2))) _⦋n⦌ :=
  (p.toOrderHom.monotone.functor ⋙ s.chain).prod'
    (q.toOrderHom.monotone.functor ⋙
      (ULift.orderIso : ULift.{u} (Fin 2) ≃o Fin 2).symm.monotone.functor)

/-- 列全体の再添字は、元の入力と時刻の再添字そのもの。 -/
lemma coherentStringPrismChain_reindex {f : x ⟶ y} (s : _root_.SerrePositivity.InfinityCategories.Kan.CoherentArrowString f)
    {m n : ℕ} (p : ⦋n⦌ ⟶ ⦋s.length⦌) (q : ⦋n⦌ ⟶ ⦋1⦌) (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    (nerve (I × ULift.{u} (Fin 2))).map θ.op (_root_.SerrePositivity.InfinityCategories.Kan.coherentStringPrismChain s p q) =
      _root_.SerrePositivity.InfinityCategories.Kan.coherentStringPrismChain s (θ ≫ p) (θ ≫ q) := rfl

/-- 積圏の長辺は、指定した元の射と元の縦辺そのもの。 -/
lemma coherentStringPrismChain_longEdge {f : x ⟶ y} (s : _root_.SerrePositivity.InfinityCategories.Kan.CoherentArrowString f)
    {n : ℕ} (p : ⦋n⦌ ⟶ ⦋s.length⦌) (q : ⦋n⦌ ⟶ ⦋1⦌)
    (hp : _root_.SerrePositivity.InfinityCategories.Kan.coherentStringEndpointMap n ≫ p = _root_.SerrePositivity.InfinityCategories.Kan.coherentStringEndpointMap s.length)
    (hq : _root_.SerrePositivity.InfinityCategories.Kan.coherentStringEndpointMap n ≫ q = 𝟙 ⦋1⦌) :
    (nerve (I × ULift.{u} (Fin 2))).map (_root_.SerrePositivity.InfinityCategories.Kan.coherentStringEndpointMap n).op
      (_root_.SerrePositivity.InfinityCategories.Kan.coherentStringPrismChain s p q) =
      (nerve.edgeMk ((f, homOfLE (by change (0 : Fin 2) ≤ 1; decide)) :
        (x, ULift.up (0 : Fin 2)) ⟶ (y, ULift.up (1 : Fin 2)))).edge := by
  rw [_root_.SerrePositivity.InfinityCategories.Kan.coherentStringPrismChain_reindex, hp, hq]
  change ((nerve I).map (_root_.SerrePositivity.InfinityCategories.Kan.coherentStringEndpointMap s.length).op s.chain).prod' _ = _
  rw [s.long_edge]
  refine ComposableArrows.ext₁ (F := _) (G := _) ?_ ?_ ?_
  · rfl
  · rfl
  · simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    apply Prod.ext
    · rfl
    · exact Subsingleton.elim _ _


/-- 元の列の精密化に沿う、積圏の列全体の厳密な一致。 -/
lemma coherentStringPrismChain_refinement {f : x ⟶ y} {s t : _root_.SerrePositivity.InfinityCategories.Kan.CoherentArrowString f}
    (a : s ⟶ t) {n : ℕ} (p : ⦋n⦌ ⟶ ⦋s.length⦌) (q : ⦋n⦌ ⟶ ⦋1⦌) :
    _root_.SerrePositivity.InfinityCategories.Kan.coherentStringPrismChain t (p ≫ a.map) q = _root_.SerrePositivity.InfinityCategories.Kan.coherentStringPrismChain s p q := by
  have ha : a.map.toOrderHom.monotone.functor ⋙ t.chain = s.chain := a.comm
  change (p.toOrderHom.monotone.functor ⋙ (a.map.toOrderHom.monotone.functor ⋙
    t.chain)).prod' _ = _
  rw [ha]
  rfl

/-- 元の列に下側の縦辺を加えた、同じ積圏の長辺の合成列。 -/
def coherentLowerPrismString {f : x ⟶ y} (s : _root_.SerrePositivity.InfinityCategories.Kan.CoherentArrowString f) :
    _root_.SerrePositivity.InfinityCategories.Kan.CoherentArrowString (I := I × ULift.{u} (Fin 2)) ((f, homOfLE (by change (0 : Fin 2) ≤ 1; decide)) :
      (x, ULift.up (0 : Fin 2)) ⟶ (y, ULift.up (1 : Fin 2))) where
  length := s.length + 1
  chain := _root_.SerrePositivity.InfinityCategories.Kan.coherentStringPrismChain s (_root_.SerrePositivity.InfinityCategories.Kan.coherentLowerStringIndex _) (_root_.SerrePositivity.InfinityCategories.Kan.coherentLowerStringTime _)
  long_edge := _root_.SerrePositivity.InfinityCategories.Kan.coherentStringPrismChain_longEdge s _ _
    (_root_.SerrePositivity.InfinityCategories.Kan.coherentStringEndpointMap_comp _ (_root_.SerrePositivity.InfinityCategories.Kan.coherentLowerStringIndex_first _)
      (_root_.SerrePositivity.InfinityCategories.Kan.coherentLowerStringIndex_last _)) (by
      refine SimplexCategory.Hom.ext_one_left _ _ ?_ ?_
      · change (_root_.SerrePositivity.InfinityCategories.Kan.coherentLowerStringTime s.length).toOrderHom
          ((_root_.SerrePositivity.InfinityCategories.Kan.coherentStringEndpointMap (s.length + 1)).toOrderHom 0) = 0
        rw [_root_.SerrePositivity.InfinityCategories.Kan.coherentStringEndpointMap_first, _root_.SerrePositivity.InfinityCategories.Kan.coherentLowerStringTime_first]
      · change (_root_.SerrePositivity.InfinityCategories.Kan.coherentLowerStringTime s.length).toOrderHom
          ((_root_.SerrePositivity.InfinityCategories.Kan.coherentStringEndpointMap (s.length + 1)).toOrderHom 1) = 1
        rw [_root_.SerrePositivity.InfinityCategories.Kan.coherentStringEndpointMap_last, _root_.SerrePositivity.InfinityCategories.Kan.coherentLowerStringTime_last])

/-- 下側の列への精密化は、元の列と時刻を全射で保持する。 -/
def coherentLowerPrismStringMap {f : x ⟶ y} {s t : _root_.SerrePositivity.InfinityCategories.Kan.CoherentArrowString f}
    (a : s ⟶ t) : _root_.SerrePositivity.InfinityCategories.Kan.coherentLowerPrismString s ⟶ _root_.SerrePositivity.InfinityCategories.Kan.coherentLowerPrismString t where
  map := _root_.SerrePositivity.InfinityCategories.Kan.coherentLowerStringExtend a.map
  first := _root_.SerrePositivity.InfinityCategories.Kan.coherentLowerStringExtend_first a.map a.first
  last := _root_.SerrePositivity.InfinityCategories.Kan.coherentLowerStringExtend_last a.map
  comm := by
    change (nerve (I × ULift.{u} (Fin 2))).map (_root_.SerrePositivity.InfinityCategories.Kan.coherentLowerStringExtend a.map).op
      (_root_.SerrePositivity.InfinityCategories.Kan.coherentStringPrismChain t (_root_.SerrePositivity.InfinityCategories.Kan.coherentLowerStringIndex _) (_root_.SerrePositivity.InfinityCategories.Kan.coherentLowerStringTime _)) = _
    rw [_root_.SerrePositivity.InfinityCategories.Kan.coherentStringPrismChain_reindex, _root_.SerrePositivity.InfinityCategories.Kan.coherentLowerStringExtend_index _ a.last,
      _root_.SerrePositivity.InfinityCategories.Kan.coherentLowerStringExtend_time, _root_.SerrePositivity.InfinityCategories.Kan.coherentStringPrismChain_refinement]
    rfl

/-- 元の射の全合成列を、下側の全因子分解列へ送る関手。 -/
def coherentLowerPrismStringFunctor (f : x ⟶ y) :
    _root_.SerrePositivity.InfinityCategories.Kan.CoherentArrowString f ⥤ _root_.SerrePositivity.InfinityCategories.Kan.CoherentArrowString (I := I × ULift.{u} (Fin 2)) ((f, homOfLE (by change (0 : Fin 2) ≤ 1; decide)) :
      (x, ULift.up (0 : Fin 2)) ⟶ (y, ULift.up (1 : Fin 2))) where
  obj := _root_.SerrePositivity.InfinityCategories.Kan.coherentLowerPrismString
  map := _root_.SerrePositivity.InfinityCategories.Kan.coherentLowerPrismStringMap
  map_id _ := _root_.SerrePositivity.InfinityCategories.Kan.CoherentArrowStringHom.ext (_root_.SerrePositivity.InfinityCategories.Kan.coherentLowerStringExtend_id _)
  map_comp _ _ := _root_.SerrePositivity.InfinityCategories.Kan.CoherentArrowStringHom.ext (_root_.SerrePositivity.InfinityCategories.Kan.coherentLowerStringExtend_comp _ _)

/-- 元の列に上側の縦辺を加えた、同じ積圏の長辺の合成列。 -/
def coherentUpperPrismString {f : x ⟶ y} (s : _root_.SerrePositivity.InfinityCategories.Kan.CoherentArrowString f) :
    _root_.SerrePositivity.InfinityCategories.Kan.CoherentArrowString (I := I × ULift.{u} (Fin 2)) ((f, homOfLE (by change (0 : Fin 2) ≤ 1; decide)) :
      (x, ULift.up (0 : Fin 2)) ⟶ (y, ULift.up (1 : Fin 2))) where
  length := s.length + 1
  chain := _root_.SerrePositivity.InfinityCategories.Kan.coherentStringPrismChain s (_root_.SerrePositivity.InfinityCategories.Kan.coherentUpperStringIndex _) (_root_.SerrePositivity.InfinityCategories.Kan.coherentUpperStringTime _)
  long_edge := _root_.SerrePositivity.InfinityCategories.Kan.coherentStringPrismChain_longEdge s _ _
    (_root_.SerrePositivity.InfinityCategories.Kan.coherentStringEndpointMap_comp _ (_root_.SerrePositivity.InfinityCategories.Kan.coherentUpperStringIndex_first _)
      (_root_.SerrePositivity.InfinityCategories.Kan.coherentUpperStringIndex_last _)) (by
      refine SimplexCategory.Hom.ext_one_left _ _ ?_ ?_
      · change (_root_.SerrePositivity.InfinityCategories.Kan.coherentUpperStringTime s.length).toOrderHom
          ((_root_.SerrePositivity.InfinityCategories.Kan.coherentStringEndpointMap (s.length + 1)).toOrderHom 0) = 0
        rw [_root_.SerrePositivity.InfinityCategories.Kan.coherentStringEndpointMap_first, _root_.SerrePositivity.InfinityCategories.Kan.coherentUpperStringTime_first]
      · change (_root_.SerrePositivity.InfinityCategories.Kan.coherentUpperStringTime s.length).toOrderHom
          ((_root_.SerrePositivity.InfinityCategories.Kan.coherentStringEndpointMap (s.length + 1)).toOrderHom 1) = 1
        rw [_root_.SerrePositivity.InfinityCategories.Kan.coherentStringEndpointMap_last, _root_.SerrePositivity.InfinityCategories.Kan.coherentUpperStringTime_last])

/-- 上側の列への精密化は、元の列と時刻を全射で保持する。 -/
def coherentUpperPrismStringMap {f : x ⟶ y} {s t : _root_.SerrePositivity.InfinityCategories.Kan.CoherentArrowString f}
    (a : s ⟶ t) : _root_.SerrePositivity.InfinityCategories.Kan.coherentUpperPrismString s ⟶ _root_.SerrePositivity.InfinityCategories.Kan.coherentUpperPrismString t where
  map := _root_.SerrePositivity.InfinityCategories.Kan.coherentUpperStringExtend a.map
  first := _root_.SerrePositivity.InfinityCategories.Kan.coherentUpperStringExtend_zero a.map
  last := _root_.SerrePositivity.InfinityCategories.Kan.coherentUpperStringExtend_last a.map a.last
  comm := by
    change (nerve (I × ULift.{u} (Fin 2))).map (_root_.SerrePositivity.InfinityCategories.Kan.coherentUpperStringExtend a.map).op
      (_root_.SerrePositivity.InfinityCategories.Kan.coherentStringPrismChain t (_root_.SerrePositivity.InfinityCategories.Kan.coherentUpperStringIndex _) (_root_.SerrePositivity.InfinityCategories.Kan.coherentUpperStringTime _)) = _
    rw [_root_.SerrePositivity.InfinityCategories.Kan.coherentStringPrismChain_reindex, _root_.SerrePositivity.InfinityCategories.Kan.coherentUpperStringExtend_index _ a.first,
      _root_.SerrePositivity.InfinityCategories.Kan.coherentUpperStringExtend_time, _root_.SerrePositivity.InfinityCategories.Kan.coherentStringPrismChain_refinement]
    rfl

/-- 元の射の全合成列を、上側の全因子分解列へ送る関手。 -/
def coherentUpperPrismStringFunctor (f : x ⟶ y) :
    _root_.SerrePositivity.InfinityCategories.Kan.CoherentArrowString f ⥤ _root_.SerrePositivity.InfinityCategories.Kan.CoherentArrowString (I := I × ULift.{u} (Fin 2)) ((f, homOfLE (by change (0 : Fin 2) ≤ 1; decide)) :
      (x, ULift.up (0 : Fin 2)) ⟶ (y, ULift.up (1 : Fin 2))) where
  obj := _root_.SerrePositivity.InfinityCategories.Kan.coherentUpperPrismString
  map := _root_.SerrePositivity.InfinityCategories.Kan.coherentUpperPrismStringMap
  map_id _ := _root_.SerrePositivity.InfinityCategories.Kan.CoherentArrowStringHom.ext (_root_.SerrePositivity.InfinityCategories.Kan.coherentUpperStringExtend_id _)
  map_comp _ _ := _root_.SerrePositivity.InfinityCategories.Kan.CoherentArrowStringHom.ext (_root_.SerrePositivity.InfinityCategories.Kan.coherentUpperStringExtend_comp _ _)

end SerrePositivity.InfinityCategories.Kan

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.coherentLowerPrismString (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentLowerPrismString := _root_.SerrePositivity.InfinityCategories.Kan.coherentLowerPrismString

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.coherentLowerPrismStringFunctor (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentLowerPrismStringFunctor := _root_.SerrePositivity.InfinityCategories.Kan.coherentLowerPrismStringFunctor

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.coherentLowerPrismStringMap (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentLowerPrismStringMap := _root_.SerrePositivity.InfinityCategories.Kan.coherentLowerPrismStringMap

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.coherentStringPrismChain (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentStringPrismChain := _root_.SerrePositivity.InfinityCategories.Kan.coherentStringPrismChain

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentStringPrismChain_longEdge := _root_.SerrePositivity.InfinityCategories.Kan.coherentStringPrismChain_longEdge

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentStringPrismChain_refinement := _root_.SerrePositivity.InfinityCategories.Kan.coherentStringPrismChain_refinement

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentStringPrismChain_reindex := _root_.SerrePositivity.InfinityCategories.Kan.coherentStringPrismChain_reindex

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.coherentUpperPrismString (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentUpperPrismString := _root_.SerrePositivity.InfinityCategories.Kan.coherentUpperPrismString

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.coherentUpperPrismStringFunctor (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentUpperPrismStringFunctor := _root_.SerrePositivity.InfinityCategories.Kan.coherentUpperPrismStringFunctor

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.coherentUpperPrismStringMap (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentUpperPrismStringMap := _root_.SerrePositivity.InfinityCategories.Kan.coherentUpperPrismStringMap

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentLowerPrismString._proof_1 := _root_.SerrePositivity.InfinityCategories.Kan.coherentLowerPrismString._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentLowerPrismString._proof_2 := _root_.SerrePositivity.InfinityCategories.Kan.coherentLowerPrismString._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentLowerPrismString._proof_3 := _root_.SerrePositivity.InfinityCategories.Kan.coherentLowerPrismString._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentLowerPrismStringFunctor._proof_1 := _root_.SerrePositivity.InfinityCategories.Kan.coherentLowerPrismStringFunctor._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentLowerPrismStringFunctor._proof_2 := _root_.SerrePositivity.InfinityCategories.Kan.coherentLowerPrismStringFunctor._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentLowerPrismStringMap._proof_1 := _root_.SerrePositivity.InfinityCategories.Kan.coherentLowerPrismStringMap._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentLowerPrismStringMap._proof_2 := _root_.SerrePositivity.InfinityCategories.Kan.coherentLowerPrismStringMap._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentLowerPrismStringMap._proof_3 := _root_.SerrePositivity.InfinityCategories.Kan.coherentLowerPrismStringMap._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentLowerPrismStringMap._proof_4 := _root_.SerrePositivity.InfinityCategories.Kan.coherentLowerPrismStringMap._proof_4

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentStringPrismChain._proof_1 := _root_.SerrePositivity.InfinityCategories.Kan.coherentStringPrismChain._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentStringPrismChain._proof_2 := _root_.SerrePositivity.InfinityCategories.Kan.coherentStringPrismChain._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentStringPrismChain._proof_3 := _root_.SerrePositivity.InfinityCategories.Kan.coherentStringPrismChain._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentStringPrismChain_longEdge._proof_1 := _root_.SerrePositivity.InfinityCategories.Kan.coherentStringPrismChain_longEdge._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentUpperPrismString._proof_1 := _root_.SerrePositivity.InfinityCategories.Kan.coherentUpperPrismString._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentUpperPrismString._proof_2 := _root_.SerrePositivity.InfinityCategories.Kan.coherentUpperPrismString._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentUpperPrismStringFunctor._proof_1 := _root_.SerrePositivity.InfinityCategories.Kan.coherentUpperPrismStringFunctor._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentUpperPrismStringFunctor._proof_2 := _root_.SerrePositivity.InfinityCategories.Kan.coherentUpperPrismStringFunctor._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentUpperPrismStringMap._proof_1 := _root_.SerrePositivity.InfinityCategories.Kan.coherentUpperPrismStringMap._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentUpperPrismStringMap._proof_2 := _root_.SerrePositivity.InfinityCategories.Kan.coherentUpperPrismStringMap._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentUpperPrismStringMap._proof_3 := _root_.SerrePositivity.InfinityCategories.Kan.coherentUpperPrismStringMap._proof_3
