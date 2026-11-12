module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.PathDeformationEnriched

/-!
概要：順序集合の射を最大の区間 path に送る通常の関手。
方針：全区間を path の台とし、接合点での区間の和集合の式で合成を証明する。
規約：通常の射の向きは変えず、全ての中間の頂点を path に含める。
使われ方：Kerodon §5.6（Tag 027M）、coherent な単体の最大化を通常の射列で表示する。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SimplicialThickening SSet
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

/-- 概要：二端点間の全区間を台とする最大の path。
方針：順序区間の所属から path の二つの上下界を得る。
規約：h は端点の順序。
使われ方：Kerodon §2.4.3（Tag 00KM）、coherent な単体の strict な射列の各射。 -/
def coherentMaximalPath {J : Type u} [LinearOrder J] {i j : J} (h : i ≤ j) : Path i j where
  I := Set.Icc i j
  left := ⟨le_rfl, h⟩
  right := ⟨h, le_rfl⟩
  left_le _ hz := hz.1
  le_right _ hz := hz.2

/-- 概要：順序集合は各射を最大の区間 path に送る通常の関手を持つ。
方針：二つの連続した区間の和集合が全区間となることを使う。
規約：対象写像は恒等。
使われ方：Kerodon §5.6（Tag 027M）、coherent な単体から通常の射列を取り出す入力。 -/
def coherentMaximalPathFunctor (J : Type u) [LinearOrder J] : J ⥤ SimplicialThickening J where
  obj i := ⟨i⟩
  map f := coherentMaximalPath (leOfHom f)
  map_id i := by
    apply SimplicialThickening.Path.ext
    ext z
    change (i ≤ z ∧ z ≤ i) ↔ z = i
    exact ⟨fun h ↦ le_antisymm h.2 h.1, fun h ↦ by subst z; exact ⟨le_rfl, le_rfl⟩⟩
  map_comp {i j k} f g := by
    apply SimplicialThickening.Path.ext
    ext z
    change (i ≤ z ∧ z ≤ k) ↔ ((i ≤ z ∧ z ≤ j) ∨ (j ≤ z ∧ z ≤ k))
    constructor
    · rintro ⟨hiz, hzk⟩
      rcases le_total z j with hzj | hjz
      · exact Or.inl ⟨hiz, hzj⟩
      · exact Or.inr ⟨hjz, hzk⟩
    · rintro (⟨hiz, hzj⟩ | ⟨hjz, hzk⟩)
      · exact ⟨hiz, hzj.trans (leOfHom g)⟩
      · exact ⟨(leOfHom f).trans hjz, hzk⟩

/-- 概要：時刻一の path の変形は最大の区間 path に一致する。
方針：既存の台の区間の等式を path の等式へ移す。
規約：端点の順序は元の path から得る。
使われ方：Kerodon §5.6（Tag 027M）、豊穣な変形の終点を通常の射の表示に戻す。 -/
lemma coherentPathDeformation_one_eq_maximal {J K : Type u} [LinearOrder J] [LinearOrder K]
    (A : J →o K) {i j : J} (P : Path i j) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPathDeformation A (OrderHom.const J 1) P =
      coherentMaximalPath (A.monotone P.le) := by
  apply SimplicialThickening.Path.ext
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPathDeformation_one A P

/-- 概要：時刻一の変形は最大の path の通常の順序図式の豊穣表示。
方針：Hom の各単体を、最大の path に定値な図式と比較する。
規約：対象写像は元の単調写像 A。
使われ方：Kerodon §5.6（Tag 027M）、変形の終点が通常の射列であることの厳密な同定。 -/
lemma coherentPathDeformationEnriched_one {J K : Type u} [LinearOrder J] [LinearOrder K]
    (A : J →o K) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPathDeformationEnriched A (OrderHom.const J 1) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.enrichedFunctorOfOrderDiagram (A.toFunctor ⋙ coherentMaximalPathFunctor K) := by
  refine EnrichedFunctor.ext SSet (fun _ ↦ rfl) ?_
  intro i j
  simp only [eqToHom_refl, Category.comp_id]
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro P
  apply CategoryTheory.Functor.ext (fun z ↦ coherentPathDeformation_one_eq_maximal A (P.obj z))

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
