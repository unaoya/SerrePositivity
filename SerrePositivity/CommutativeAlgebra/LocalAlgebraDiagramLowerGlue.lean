module

public import SerrePositivity.CommutativeAlgebra.LocalAlgebraPoint

/-! # 下方に閉じた添字集合上の局所代数図式の貼り合わせ

開初期部分と全添字集合で同じ処理を使う。対角段から環を取り出し、
構造を含む制限一致に沿って写像を移す。剰余体や平坦性には依存しない。
-/

@[expose] public section
namespace SerrePositivity
universe u
variable {B K ι : Type u} [CommRing B] [CommRing K] [Algebra B K] [LinearOrder ι]

/-- 閉初期部分の履歴を、より小さい閉初期部分へ制限する。 -/
def localAlgebraHistoryRestrict (j i : ι) (h : j < i)
    (D : LocalAlgebraDiagram B K {k : ι // k ≤ i}) :
    LocalAlgebraDiagram B K {k : ι // k ≤ j} :=
  D.reindex (fun k ↦ ⟨k.val, k.property.trans h.le⟩) (fun _ _ hk ↦ hk)

variable (U : ι → Prop)
variable (p : ∀ j, U j → LocalAlgebraDiagram B K {k : ι // k ≤ j})
variable (hc : ∀ j k (hj : U j) (hk : U k) (hjk : j < k),
  localAlgebraHistoryRestrict j k hjk (p k hk) = p j hj)
include hc

/-- 対角段の台だけでなく構造と指定終域も、大きい履歴の同じ段と一致する。 -/
theorem localAlgebraLowerGlue_point_eq (j l : ι) (hj : U j) (hl : U l) (hjl : j ≤ l) :
    (p j hj).point ⟨j, le_rfl⟩ = (p l hl).point ⟨j, hjl⟩ := by
  by_cases h : j = l
  · subst l
    rfl
  · have hlt : j < l := lt_of_le_of_ne hjl h
    exact (congrArg (fun D : LocalAlgebraDiagram B K {k : ι // k ≤ j} ↦
      D.point ⟨j, le_rfl⟩) (hc j l hj hl hlt)).symm

/-- 先行履歴から、実際の環と写像を持つ添字集合上の図式を構成する。 -/
def localAlgebraLowerGlue : LocalAlgebraDiagram B K {j : ι // U j} where
  obj j := (p j.val j.property).obj ⟨j.val, le_rfl⟩
  ring j := (p j.val j.property).ring ⟨j.val, le_rfl⟩
  localRing j := (p j.val j.property).localRing ⟨j.val, le_rfl⟩
  algebra j := (p j.val j.property).algebra ⟨j.val, le_rfl⟩
  baseLocal j := (p j.val j.property).baseLocal ⟨j.val, le_rfl⟩
  map j k h := LocalAlgebraPoint.castMap
    (C := (p k.val k.property).point ⟨k.val, le_rfl⟩)
    (localAlgebraLowerGlue_point_eq U p hc j.val k.val j.property k.property h).symm rfl
    ((p k.val k.property).map ⟨j.val, h⟩ ⟨k.val, le_rfl⟩ h)
  target j := (p j.val j.property).target ⟨j.val, le_rfl⟩

/-- 開図式の写像は、任意の先行履歴内の写像と型・構造を含めて一致する。 -/
theorem localAlgebraLowerGlue_map_heq
    (j k : {j : ι // U j}) (h : j ≤ k) (l : ι) (hl : U l) (hkl : k.val ≤ l) :
    HEq ((localAlgebraLowerGlue U p hc).map j k h)
      ((p l hl).map ⟨j.val, (show j.val ≤ k.val from h).trans hkl⟩ ⟨k.val, hkl⟩ h) := by
  have he := LocalAlgebraPoint.castMap_heq
    (C := (p k.val k.property).point ⟨k.val, le_rfl⟩)
    (localAlgebraLowerGlue_point_eq U p hc j.val k.val j.property k.property h).symm rfl
    ((p k.val k.property).map ⟨j.val, h⟩ ⟨k.val, le_rfl⟩ h)
  by_cases hEq : k.val = l
  · subst l
    exact he
  · have hlt : k.val < l := lt_of_le_of_ne hkl hEq
    exact he.trans ((LocalAlgebraDiagram.map_heq_of_reindex_eq
      (p l hl) (p k.val k.property)
      (fun a : {a : ι // a ≤ k.val} ↦ ⟨a.val, a.property.trans hlt.le⟩)
      (fun _ _ ha ↦ ha) (hc k.val l k.property hl hlt)
      ⟨j.val, h⟩ ⟨k.val, le_rfl⟩ h).symm)

variable (hU : ∀ {j l : ι}, j ≤ l → U l → U j)

/-- 各先行閉初期部分へ制限すると、元の図式全体に等しい。 -/
theorem localAlgebraLowerGlue_restrict (l : ι) (hl : U l) :
    (localAlgebraLowerGlue U p hc).reindex
      (fun j : {j : ι // j ≤ l} ↦ ⟨j.val, hU j.property hl⟩)
      (fun _ _ h ↦ h) = p l hl := by
  apply LocalAlgebraDiagram.ext_point
  · intro j
    exact localAlgebraLowerGlue_point_eq U p hc j.val l
      (hU j.property hl) hl j.property
  · intro j k h
    exact localAlgebraLowerGlue_map_heq U p hc
      ⟨j.val, hU j.property hl⟩
      ⟨k.val, hU k.property hl⟩ h l hl k.property


section All
variable (q : ∀ j : ι, LocalAlgebraDiagram B K {k : ι // k ≤ j})
variable (hq : ∀ j k (hjk : j < k), localAlgebraHistoryRestrict j k hjk (q k) = q j)

/-- 全添字集合にも、開初期部分と同じ貼り合わせを適用する。 -/
def localAlgebraGlueAll : LocalAlgebraDiagram B K ι :=
  (localAlgebraLowerGlue (fun _ : ι ↦ True) (fun j _ ↦ q j)
    (fun j k _ _ hjk ↦ hq j k hjk)).reindex (fun j ↦ ⟨j, trivial⟩) (fun _ _ h ↦ h)

omit hc in
/-- 全体図式から任意の閉初期部分へ戻ると、その履歴全体に等しい。 -/
theorem localAlgebraGlueAll_restrict (l : ι) :
    (localAlgebraGlueAll q hq).reindex (fun j : {j : ι // j ≤ l} ↦ j.val)
      (fun _ _ h ↦ h) = q l := by
  exact (LocalAlgebraDiagram.reindex_comp
    (localAlgebraLowerGlue (fun _ : ι ↦ True) (fun j _ ↦ q j)
      (fun j k _ _ hjk ↦ hq j k hjk))
    (fun j ↦ ⟨j, trivial⟩) (fun _ _ h ↦ h)
    (fun j : {j : ι // j ≤ l} ↦ j.val) (fun _ _ h ↦ h)).trans
    (localAlgebraLowerGlue_restrict (fun _ : ι ↦ True) (fun j _ ↦ q j)
      (fun j k _ _ hjk ↦ hq j k hjk) (fun _ _ ↦ trivial) l trivial)
end All

end SerrePositivity
