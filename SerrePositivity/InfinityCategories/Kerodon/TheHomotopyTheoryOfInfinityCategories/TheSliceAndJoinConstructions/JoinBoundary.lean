module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：境界同士の pushout-join と標準単体の境界の比較。
方針：標準単体の join の同型で、連結写像が頂点を取り逃す条件を左右に分ける。
規約：零次元の境界と空区間も含める。
使われ方：HTT §1.2.12、Kerodon Corollary 4.7.3.12（Tag 06R2） の終対象の充填条件。

対応節は Kerodon 4.3（Tag 015M）。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Limits SSet
open scoped Simplicial

namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
namespace Join

/-- 概要：連結写像が頂点を取り逃す条件は、左右どちらかが頂点を取り逃す条件。
方針：欠落した頂点を連結先の左右の区間に分ける。
規約：始域・終域の空区間も許す。
使われ方：HTT §1.2.12、Kerodon Corollary 4.7.3.12（Tag 06R2） の境界の比較。 -/
lemma missing_concat_boundary_iff {p q r : ℕ} (ℓ : ℕ) (hℓ : ℓ ≤ r)
    (f : Fin ℓ →o Fin p) (g : Fin (r - ℓ) →o Fin q) :
    (∃ v : Fin (p + q), v ∉ Set.range (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.concat ℓ hℓ f g)) ↔
      (∃ v : Fin p, v ∉ Set.range f) ∨ (∃ v : Fin q, v ∉ Set.range g) := by
  constructor
  · rintro ⟨v, hm⟩
    by_cases h : v.val < p
    · let a : Fin p := ⟨v.val, h⟩
      have ha : a.castAdd q = v := Fin.ext rfl
      exact Or.inl ⟨a, by rwa [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.Join.mem_range_concat_left ℓ hℓ f g, ha]⟩
    · let b : Fin q := ⟨v.val - p, by have := v.isLt; omega⟩
      have hb : b.natAdd p = v := Fin.ext (by dsimp [b]; omega)
      exact Or.inr ⟨b, by rwa [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.Join.mem_range_concat_right ℓ hℓ f g, hb]⟩
  · rintro (⟨v, hm⟩ | ⟨v, hm⟩)
    · exact ⟨v.castAdd q, by rwa [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.Join.mem_range_concat_left ℓ hℓ f g]⟩
    · exact ⟨v.natAdd p, by rwa [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.Join.mem_range_concat_right ℓ hℓ f g]⟩

/-- 概要：有限集合の大きさを移送しても写像に欠落頂点がある条件は変わらない。
方針：大きさの等式で置換する。
規約：空集合も許す。
使われ方：HTT §1.2.12、Kerodon Corollary 4.7.3.12（Tag 06R2） の標準単体の比較。 -/
lemma missing_cast_boundary_iff {p q r : ℕ} (h : p = q) (f : Fin r → Fin p) :
    (∃ v : Fin q, v ∉ Set.range (fun a ↦ Fin.cast h (f a))) ↔
      ∃ v : Fin p, v ∉ Set.range f := by
  subst q
  rfl

/-- 概要：境界同士の pushout-join は標準単体の境界の逆像。
方針：標準単体の同型の下で頂点の欠落を左右に分解する。
規約：p と q はともに零も許す。
使われ方：HTT §1.2.12、Kerodon Corollary 4.7.3.12（Tag 06R2） の境界充填。 -/
@[kerodon 02BU]
lemma boundary_boundary_preimage (p q : ℕ) :
    (boundary (p + q + 1)).preimage (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso.{u} p q).hom =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnion (boundary p) (boundary q) := by
  ext ⟨⟨n⟩⟩ s
  change ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso p q).hom.app (Opposite.op ⦋n⦌) s ∈
    (boundary (p + q + 1)).obj _) ↔ _
  rw [mem_boundary_iff_notMem_range, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.Join.mem_joinUnion, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.Join.augMem_boundary_iff, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.Join.augMem_boundary_iff]
  change (∃ v : Fin (p + q + 1 + 1), v ∉ Set.range
    (fun a ↦ Fin.cast (by omega) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.stdEncode p q n s a))) ↔ _
  rw [missing_cast_boundary_iff, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.stdEncode, missing_concat_boundary_iff]

end Join

/-- 概要：境界同士の pushout-join は標準単体の境界と同型。
方針：境界が標準単体の join の同型に沿う逆像であることを使う。
規約：同型は和の部分複体から標準単体の境界へ向かう。
使われ方：HTT §1.2.12、Kerodon Corollary 4.7.3.12（Tag 06R2） の終対象の特徴づけ。 -/
@[kerodon 02BU]
def boundaryJoinIso (p q : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnion (boundary p) (boundary q) : SSet.{u}) ≅ (boundary (p + q + 1) : SSet.{u}) :=
  Subcomplex.eqToIso (Join.boundary_boundary_preimage p q).symm ≪≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.subcomplexPreimageIso (boundary (p + q + 1)) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso p q)

/-- 概要：境界の join の同型は周囲の標準単体への包含と可換。
方針：逆像の同型と等式による同型の構成を計算する。
規約：合成の標的は Δ[p+q+1]。
使われ方：HTT §1.2.12、Kerodon Corollary 4.7.3.12（Tag 06R2） の境界の貼り合わせ。 -/
lemma boundaryJoinIso_hom_ι (p q : ℕ) :
    (boundaryJoinIso p q).hom ≫ (boundary (p + q + 1)).ι =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnion (boundary p) (boundary q)).ι ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso.{u} p q).hom := by
  change (Subcomplex.homOfLE (Join.boundary_boundary_preimage p q).symm.le ≫
    (boundary (p + q + 1)).fromPreimage (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso p q).hom) ≫ _ = _
  rw [Category.assoc, Subcomplex.fromPreimage_ι, ← Category.assoc, Subcomplex.homOfLE_ι]

/-- 概要：join の右頂点は、標準単体の同型の下で最後の頂点になる。
方針：Yoneda と頂点での連結写像の値を計算する。
規約：右因子は Δ[0]。
使われ方：HTT Definition 1.2.12.3 の最後の頂点の固定。 -/
lemma joinStdSimplexIso_inr_vertex (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[n] : SSet.{u}) Δ[0] ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).hom =
      SSet.yonedaEquiv.symm (stdSimplex.obj₀Equiv.symm (Fin.last (n + 1))) := by
  apply SSet.yonedaEquiv.injective
  rw [Equiv.apply_symm_apply]
  apply stdSimplex.ext
  intro i
  fin_cases i
  apply Fin.ext
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.concat (p := n + 1) (q := 1) (r := 1) 0 (by omega)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.stdAugEquiv.{u} n 0 PUnit.unit)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.stdAugEquiv.{u} 0 1 (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})))) (0 : Fin 1)).val = n + 1
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.concat_of_ge _ _ _ _ _ (by omega)]
  rfl

/-- 概要：正次元の標準単体の任意の頂点は境界に属する。
方針：頂点と異なる別の頂点は定数写像の像に属さない。
規約：標準単体の次元は n+1。
使われ方：HTT Definition 1.2.12.3、終対象の境界充填条件の端点。 -/
lemma vertex_mem_boundary (n : ℕ) (i : Fin (n + 2)) :
    stdSimplex.obj₀Equiv.symm i ∈ (boundary.{u} (n + 1)).obj (Opposite.op ⦋0⦌) := by
  rw [mem_boundary_iff_notMem_range]
  have hv : ∃ v : Fin (n + 2), v ≠ i := by
    by_cases hi : i = 0
    · exact ⟨Fin.last (n + 1), by intro h; have := congrArg Fin.val (h.trans hi); simp at this⟩
    · exact ⟨0, Ne.symm hi⟩
  obtain ⟨v, hv⟩ := hv
  refine ⟨v, ?_⟩
  rintro ⟨a, ha⟩
  apply hv
  exact ha.symm

/-- 概要：標準単体の指定頂点を境界への射として表す。
方針：境界の零単体を Yoneda で射にする。
規約：次元 n+1 は正。
使われ方：HTT Definition 1.2.12.3、始対象・終対象の端点固定条件。 -/
def boundaryVertex (n : ℕ) (i : Fin (n + 2)) : (Δ[0] : SSet.{u}) ⟶ (boundary (n + 1) : SSet.{u}) :=
  SSet.yonedaEquiv.symm ⟨stdSimplex.obj₀Equiv.symm i, vertex_mem_boundary n i⟩

/-- 概要：境界の指定頂点を周囲へ含めると、標準単体の同じ頂点になる。
方針：Yoneda の同値の後合成への自然性を使う。
規約：頂点の番号は変えない。
使われ方：HTT Definition 1.2.12.3 の端点の比較。 -/
lemma boundaryVertex_ι (n : ℕ) (i : Fin (n + 2)) :
    boundaryVertex n i ≫ (boundary (n + 1)).ι =
      SSet.yonedaEquiv.symm (stdSimplex.obj₀Equiv.symm i) :=
  SSet.yonedaEquiv_symm_comp _ _

/-- 概要：境界の join の右頂点は境界の最後の頂点になる。
方針：周囲への包含を打ち消し、標準単体の join の頂点の式を使う。
規約：左は任意の境界 ∂Δ[n]、右は Δ[0]。
使われ方：HTT Definition 1.2.12.3、Kerodon Corollary 4.7.3.12（Tag 06R2） の端点条件。 -/
lemma boundaryJoinIso_inr_vertex (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (boundary n : SSet.{u}) Δ[0] ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnionLeft (boundary n) (boundary 0) ≫
      (boundaryJoinIso n 0).hom = boundaryVertex n (Fin.last (n + 1)) := by
  apply (cancel_mono (boundary (n + 1)).ι).1
  simp only [Category.assoc, boundaryJoinIso_hom_ι, boundaryVertex_ι]
  rw [← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnionLeft (boundary n) (boundary 0)), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnionLeft_ι,
    ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap, Category.id_comp]
  exact joinStdSimplexIso_inr_vertex n

/-- 概要：join の左頂点は標準単体の同型の下で最初の頂点になる。
方針：連結写像の左区間の値を計算する。
規約：左因子は Δ[0]、右因子は Δ[n]。
使われ方：HTT Definition 1.2.12.3 の双対の最初の頂点の固定。 -/
lemma joinStdSimplexIso_inl_vertex (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u}) Δ[n] ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 n).hom =
      SSet.yonedaEquiv.symm (stdSimplex.obj₀Equiv.symm (0 : Fin (0 + n + 1 + 1))) := by
  apply SSet.yonedaEquiv.injective
  rw [Equiv.apply_symm_apply]
  apply stdSimplex.ext
  intro i
  fin_cases i
  apply Fin.ext
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.concat (p := 1) (q := n + 1) (r := 1) 1 (by omega)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.stdAugEquiv.{u} 0 1 (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u}))))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.stdAugEquiv.{u} n (1 - 1) (by simp only [Nat.sub_self, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj]; exact PUnit.unit))
    (0 : Fin 1)).val = 0
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.concat_of_lt _ _ _ _ _ (by decide)]
  rfl

/-- 概要：境界の join の左頂点は境界の最初の頂点になる。
方針：周囲への包含を打ち消し、標準単体の join の頂点の式を使う。
規約：左因子は Δ[0]、右因子は ∂Δ[n]。
使われ方：HTT Definition 1.2.12.3 の双対、Kerodon Corollary 4.7.3.12（Tag 06R2） の始対象。 -/
lemma boundaryJoinIso_inl_vertex (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u}) (boundary n : SSet.{u}) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnionRight (boundary 0) (boundary n) ≫ (boundaryJoinIso 0 n).hom =
        boundaryVertex (0 + n) 0 := by
  apply (cancel_mono (boundary (0 + n + 1)).ι).1
  simp only [Category.assoc, boundaryJoinIso_hom_ι, boundaryVertex_ι]
  rw [← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnionRight (boundary 0) (boundary n)), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnionRight_ι,
    ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap, Category.id_comp]
  exact joinStdSimplexIso_inl_vertex n

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
