module

public import SerrePositivity.CommutativeAlgebra.ResidueFieldExtension.AlgebraSystem
public import Mathlib.Logic.Function.Basic

/-! # 局所代数の図式と下方に閉じた添字集合での貼り合わせ

## 概要

局所環 `B` 上の局所代数と、指定体 `K` への写像からなる図式を構造体 `LocalAlgebraDiagram` にまとめ、
添字の引き戻し（`reindex`）、一段の取り出し（`LocalAlgebraPoint`、`point`）、
下方に閉じた添字集合上での貼り合わせ（`localAlgebraLowerGlue`、`localAlgebraGlueAll`）を与える。

## 方針

貼り合わせでは、各添字 `j` までの閉初期部分の図式から対角の段 `j` を取り出して環とし、
制限の一致（`localAlgebraHistoryRestrict`）から得られる段の等式に沿って遷移写像を移す。
移送は環・代数の構造も含めた等式（`LocalAlgebraPoint` の等式）で行い、台の型だけの等式は使わない。

## 規約

有向図式の法則・平坦性・剰余体の像は構造体に入れず、別に検証する。
関数の組による図式（`ResidueFieldExtension/AlgebraSystem`）との一本化は、剰余体拡大の構成を
書き直すときに行う。

## 使われ方

剰余体拡大の構成の図式としての延長と貼り合わせ（`ResidueFieldDiagramExtension`、
`ResidueFieldDiagramGlue`、`ResidueFieldHistory*`）。
-/

@[expose] public section

namespace SerrePositivity

section Diagram

open IsLocalRing
universe u v
variable (B K : Type u) [CommRing B] [IsLocalRing B] [CommRing K] [Algebra B K]

/-- 局所B代数の族、遷移写像、指定終域への写像。 -/
structure LocalAlgebraDiagram (ι : Type v) [Preorder ι] where
  obj : ι → Type u
  [ring : ∀ i, CommRing (obj i)]
  [localRing : ∀ i, IsLocalRing (obj i)]
  [algebra : ∀ i, Algebra B (obj i)]
  [baseLocal : ∀ i, IsLocalHom (algebraMap B (obj i))]
  map : ∀ i j, i ≤ j → obj i →ₐ[B] obj j
  target : ∀ i, obj i →ₐ[B] K

attribute [instance] LocalAlgebraDiagram.ring LocalAlgebraDiagram.localRing
  LocalAlgebraDiagram.algebra LocalAlgebraDiagram.baseLocal

variable {B K} {ι κ : Type v} [Preorder ι] [Preorder κ]

omit [IsLocalRing B] in
/-- 図式の一致には、環の台だけでなく環・代数の構造と写像の一致が必要。
局所性と基底写像の局所性は命題なので証明無関係性で一致する。 -/
theorem LocalAlgebraDiagram.ext (D E : LocalAlgebraDiagram B K ι)
    (hobj : D.obj = E.obj) (hring : HEq D.ring E.ring)
    (halg : HEq D.algebra E.algebra) (hmap : HEq D.map E.map)
    (htarget : HEq D.target E.target) : D = E := by
  cases D
  cases E
  cases hobj
  cases hring
  cases halg
  cases hmap
  cases htarget
  rfl

/-- 単調な添字写像で環の構造と写像を同時に制限する。 -/
def LocalAlgebraDiagram.reindex (D : LocalAlgebraDiagram B K ι)
    (r : κ → ι) (hr : Monotone r) : LocalAlgebraDiagram B K κ where
  obj j := D.obj (r j)
  map := algebraSystemReindexMap D.obj D.map r hr
  target j := D.target (r j)

omit [IsLocalRing B] in
@[simp] theorem LocalAlgebraDiagram.reindex_id (D : LocalAlgebraDiagram B K ι) :
    D.reindex id monotone_id = D := rfl

omit [IsLocalRing B] in
theorem LocalAlgebraDiagram.reindex_comp {J : Type v} [Preorder J]
    (D : LocalAlgebraDiagram B K ι) (r : κ → ι) (hr : Monotone r)
    (s : J → κ) (hs : Monotone s) :
    (D.reindex r hr).reindex s hs = D.reindex (r ∘ s) (hr.comp hs) := rfl

/-- 再帰の全域化の既定値。正しい剰余体の像や平坦性の主張は含めない。 -/
def LocalAlgebraDiagram.constant : LocalAlgebraDiagram B K ι where
  obj _ := B
  baseLocal _ := by
    change IsLocalHom (RingHom.id B)
    infer_instance
  map _ _ _ := AlgHom.id B B
  target _ := Algebra.ofId B K

instance : Nonempty (LocalAlgebraDiagram B K ι) := ⟨LocalAlgebraDiagram.constant⟩

end Diagram

section Point

universe u v
variable {B K : Type u} [CommRing B] [CommRing K] [Algebra B K]

/-- 指定終域への写像を持つ局所B代数の一段。 -/
structure LocalAlgebraPoint where
  carrier : Type u
  [ring : CommRing carrier]
  [localRing : IsLocalRing carrier]
  [algebra : Algebra B carrier]
  [baseLocal : IsLocalHom (algebraMap B carrier)]
  target : carrier →ₐ[B] K

attribute [instance] LocalAlgebraPoint.ring LocalAlgebraPoint.localRing
  LocalAlgebraPoint.algebra LocalAlgebraPoint.baseLocal

/-- 図式から構造と指定終域を含む一段を取り出す。 -/
def LocalAlgebraDiagram.point {ι : Type v} [Preorder ι]
    (D : LocalAlgebraDiagram B K ι) (i : ι) : LocalAlgebraPoint (B := B) (K := K) where
  carrier := D.obj i
  target := D.target i

/-- 制限した図式の等式は、遷移写像の型と構造を含む一致を与える。 -/
theorem LocalAlgebraDiagram.map_heq_of_reindex_eq {ι κ : Type v} [Preorder ι] [Preorder κ]
    (D : LocalAlgebraDiagram B K ι) (E : LocalAlgebraDiagram B K κ)
    (r : κ → ι) (hr : Monotone r) (hDE : D.reindex r hr = E)
    (j k : κ) (h : j ≤ k) : HEq (D.map (r j) (r k) (hr h)) (E.map j k h) := by
  cases hDE
  rfl

/-- 源と終域の段の等式に沿って代数写像を移す。 -/
def LocalAlgebraPoint.castMap {A A' C C' : LocalAlgebraPoint (B := B) (K := K)}
    (hA : A = A') (hC : C = C') (f : A.carrier →ₐ[B] C.carrier) :
    A'.carrier →ₐ[B] C'.carrier := by
  cases hA
  cases hC
  exact f

theorem LocalAlgebraPoint.castMap_heq {A A' C C' : LocalAlgebraPoint (B := B) (K := K)}
    (hA : A = A') (hC : C = C') (f : A.carrier →ₐ[B] C.carrier) :
    HEq (LocalAlgebraPoint.castMap hA hC f) f := by
  cases hA
  cases hC
  rfl

theorem LocalAlgebraPoint.ring_heq {A C : LocalAlgebraPoint (B := B) (K := K)}
    (h : A = C) : HEq A.ring C.ring := by cases h; rfl

theorem LocalAlgebraPoint.algebra_heq {A C : LocalAlgebraPoint (B := B) (K := K)}
    (h : A = C) : HEq A.algebra C.algebra := by cases h; rfl

theorem LocalAlgebraPoint.target_heq {A C : LocalAlgebraPoint (B := B) (K := K)}
    (h : A = C) : HEq A.target C.target := by cases h; rfl

/-- 一段ごとの一致と遷移の一致から、図式全体の等式を得る。 -/
theorem LocalAlgebraDiagram.ext_point {ι : Type v} [Preorder ι]
    (D E : LocalAlgebraDiagram B K ι)
    (hp : ∀ i, D.point i = E.point i)
    (hm : ∀ j k h, HEq (D.map j k h) (E.map j k h)) : D = E := by
  apply LocalAlgebraDiagram.ext
  · funext i
    exact congrArg LocalAlgebraPoint.carrier (hp i)
  · apply Function.hfunext rfl
    intro i j hij
    cases eq_of_heq hij
    exact LocalAlgebraPoint.ring_heq (hp i)
  · apply Function.hfunext rfl
    intro i j hij
    cases eq_of_heq hij
    exact LocalAlgebraPoint.algebra_heq (hp i)
  · apply Function.hfunext rfl
    intro j j' hj
    cases eq_of_heq hj
    apply Function.hfunext rfl
    intro k k' hk
    cases eq_of_heq hk
    apply Function.hfunext rfl
    intro h h' hh
    exact hm j k h
  · apply Function.hfunext rfl
    intro i j hij
    cases eq_of_heq hij
    exact LocalAlgebraPoint.target_heq (hp i)

end Point

section LowerGlue

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

end All

end LowerGlue

end SerrePositivity
