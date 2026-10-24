module

public import SerrePositivity.InfinityCategories.F1B.MappingSpaces.IntervalFamilySquare
public import SerrePositivity.InfinityCategories.F1B.MappingSpaces.MappingTranspose

/-!
概要：両側辺を固定した関手正方形を区間写像空間の族のホモトピーへ戻す。
方針：正方形を写像空間の path に curry し、パラメータと時間を転置する。
規約：入力の正方形そのものを使い、h Fun の射の等式から再選択しない。
使われ方：B1 の合成三角形の相対比較を、実際の族のホモトピーへ移す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：関手の辺から戻した族は元のホモトピー代表を回収する。
方針：区間の交換を二度適用し、curry の両逆を使う。
規約：端点は定値関手、quasicategory 性は不要。
使われ方：元の正方形の対角辺を写像空間の族と厳密に同一視する。 -/
lemma intervalFamilyOfEdge_homotopy {A X : SSet.{u}} {x y : X _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom A).obj X))
      (functorVertex (SSet.const x)) (functorVertex (SSet.const y))) :
    intervalFamilyHomotopy (intervalFamilyOfEdge e) = simplicialHomotopyOfFunctorEdge e := by
  apply RelativeMorphism.Homotopy.ext
  change (β_ A (Δ[1] : SSet.{u})).hom ≫ intervalMappingUncurry (intervalFamilyOfEdge e) = _
  rw [intervalFamilyOfEdge, intervalFamilyUncurry_curry]
  simp only [← Category.assoc, SymmetricCategory.symmetry, Category.id_comp]

/-- 概要：端点固定の関手正方形から元の写像空間の族のホモトピーを作る。
方針：区間写像空間の普遍性と族の転置を使い、横辺を厳密に回収する。
規約：標的の quasicategory 性は不要。
使われ方：coherence を保った comma 比較の経路。 -/
noncomputable def intervalFamilyHomotopyOfSquare {A X : SSet.{u}} {x y : X _⦋0⦌}
    {f g : A ⟶ intervalMappingSpace x y}
    (Q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (ihom A).obj X)
    (hb : SSet.ι₀ ≫ Q = curry (intervalFamilyHomotopy f).h)
    (ht : SSet.ι₁ ≫ Q = curry (intervalFamilyHomotopy g).h)
    (hl : prismEndpoint 0 (Δ[1] : SSet.{u}) ≫ Q =
      SSet.const (functorVertex (SSet.const x : A ⟶ X)))
    (hr : prismEndpoint 1 (Δ[1] : SSet.{u}) ≫ Q =
      SSet.const (functorVertex (SSet.const y : A ⟶ X))) : SSet.Homotopy f g where
  h := intervalFamilyTranspose (intervalFamilyCurry Q hl hr)
  h₀ := by
    apply intervalMappingUncurry_injective x y
    rw [intervalMappingUncurry_precomp, intervalFamilyTranspose_uncurry]
    unfold intervalTransposeUncurry
    rw [intervalFamilyUncurry_curry, ← Category.assoc, intervalParameterSwap_time_zero,
      Category.assoc, ← uncurry_natural_left, hb, uncurry_curry]
    change (β_ (Δ[1] : SSet.{u}) A).hom ≫ (β_ A (Δ[1] : SSet.{u})).hom ≫
      intervalMappingUncurry f = _
    rw [← Category.assoc, SymmetricCategory.symmetry, Category.id_comp]
    rfl
  h₁ := by
    apply intervalMappingUncurry_injective x y
    rw [intervalMappingUncurry_precomp, intervalFamilyTranspose_uncurry]
    unfold intervalTransposeUncurry
    rw [intervalFamilyUncurry_curry, ← Category.assoc, intervalParameterSwap_time_one,
      Category.assoc, ← uncurry_natural_left, ht, uncurry_curry]
    change (β_ (Δ[1] : SSet.{u}) A).hom ≫ (β_ A (Δ[1] : SSet.{u})).hom ≫
      intervalMappingUncurry g = _
    rw [← Category.assoc, SymmetricCategory.symmetry, Category.id_comp]
    rfl
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro a
    exact False.elim a.1.property

/-- 概要：正方形から戻したホモトピーの正方形表示は入力図式そのもの。
方針：転置・uncurry の公式と区間の並べ替えの往復を計算する。
規約：ホモトピー類だけでなく二変数の図式を回収する。
使われ方：比較で元の coherence が失われていないことの検証。 -/
lemma intervalFamilyHomotopyOfSquare_square {A X : SSet.{u}} {x y : X _⦋0⦌}
    {f g : A ⟶ intervalMappingSpace x y}
    (Q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (ihom A).obj X)
    (hb : SSet.ι₀ ≫ Q = curry (intervalFamilyHomotopy f).h)
    (ht : SSet.ι₁ ≫ Q = curry (intervalFamilyHomotopy g).h)
    (hl : prismEndpoint 0 (Δ[1] : SSet.{u}) ≫ Q =
      SSet.const (functorVertex (SSet.const x : A ⟶ X)))
    (hr : prismEndpoint 1 (Δ[1] : SSet.{u}) ≫ Q =
      SSet.const (functorVertex (SSet.const y : A ⟶ X))) :
    intervalFamilySquare (intervalFamilyHomotopyOfSquare Q hb ht hl hr) = Q := by
  apply uncurry_injective
  change uncurry (curry (intervalFamilySquareReorder A ≫
    intervalMappingUncurry (intervalFamilyTranspose (intervalFamilyCurry Q hl hr)))) = _
  rw [uncurry_curry, intervalFamilyTranspose_uncurry]
  unfold intervalTransposeUncurry
  rw [intervalFamilyUncurry_curry, ← Category.assoc]
  have h : intervalFamilySquareReorder A ≫ intervalParameterSwap A Δ[1] =
      𝟙 (A ⊗ ((Δ[1] : SSet.{u}) ⊗ Δ[1])) := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro a
    rfl
  rw [h, Category.id_comp]

end SerrePositivity.InfinityCategories
