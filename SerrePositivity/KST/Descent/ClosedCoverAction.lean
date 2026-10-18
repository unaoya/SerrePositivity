module

public import SerrePositivity.KST.Descent.ClosedCoverPullback
public import SerrePositivity.KST.Descent.ThickeningDescent
public import SerrePositivity.KST.Descent.EquivariantSquareComparison

/-!
# 閉和の比較立方体の同変性

## 概要
始域へ引き戻した閉被覆の四頂点に作用を構成し、元の閉被覆への立方体を同変にする。

## 方針
二つの閉部分に引き戻し作用を使い、交わりの作用は再び引き戻す。
比較先の引き戻しの普遍性から、交わりへの射の不変性を導く。

## 規約
元の閉被覆には自明に作用し、始域上では指定された作用を保持する。

## 使われ方
論文 補題 3.3・定理 3.1 の閉和に関する有理不変部分の列の比較。
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace SerrePositivity.KST.Descent

/-- 概要：引き戻し正方形への三頂点の不変な射から同変な立方体（論文 補題 3.3）。
方針：残る頂点の不変性を二つの射影で検査する。
規約：比較先の四頂点の作用は自明。
使われ方：閉和の交わりへの指定された比較射の同変性。 -/
theorem squareMapToTrivial_equivariant_of_isPullback {C : Type u} [Category.{v} C]
    {sq tq : Square C} {G : Type*} [Group G] (a : SquareAction sq G)
    (cartesian : IsPullback tq.f₁₂ tq.f₁₃ tq.f₂₄ tq.f₃₄) (f : sq ⟶ tq)
    (invariant2 : ∀ g, (a.on2 g).asIso.hom ≫ f.τ₂ = f.τ₂)
    (invariant3 : ∀ g, (a.on3 g).asIso.hom ≫ f.τ₃ = f.τ₃)
    (invariant4 : ∀ g, (a.on4 g).asIso.hom ≫ f.τ₄ = f.τ₄) :
    EquivariantSquareMap a (SquareAction.trivial tq G) f where
  equivariant1 g := by
    change (a.on1 g).asIso.hom ≫ f.τ₁ = f.τ₁ ≫ 𝟙 _
    rw [Category.comp_id]
    apply cartesian.hom_ext
    · rw [Category.assoc, ← f.comm₁₂, ← Category.assoc, a.equivariant12,
        Category.assoc, invariant2, f.comm₁₂]
    · rw [Category.assoc, ← f.comm₁₃, ← Category.assoc, a.equivariant13,
        Category.assoc, invariant3, f.comm₁₃]
  equivariant2 g := by
    change (a.on2 g).asIso.hom ≫ f.τ₂ = f.τ₂ ≫ 𝟙 _
    exact (invariant2 g).trans (Category.comp_id _).symm
  equivariant3 g := by
    change (a.on3 g).asIso.hom ≫ f.τ₃ = f.τ₃ ≫ 𝟙 _
    exact (invariant3 g).trans (Category.comp_id _).symm
  equivariant4 g := by
    change (a.on4 g).asIso.hom ≫ f.τ₄ = f.τ₄ ≫ 𝟙 _
    exact (invariant4 g).trans (Category.comp_id _).symm

variable {S : Scheme.{u}} {B V Y Z : FiniteTypeSchemes S}
variable (f : V ⟶ B) (i : Y ⟶ B) (j : Z ⟶ B)
variable [IsClosedImmersion i.hom.left] [IsClosedImmersion j.hom.left]
variable {G : Type u} [Group G] (action : G →* Aut V)
variable (over_base : ∀ g, (action g).asIso.hom ≫ f = f)

/-- 概要：引き戻した閉被覆の四頂点への群作用（論文 補題 3.3）。
方針：二つの閉部分の引き戻し作用を用い、その交わりへ作用を移す。
規約：右下の作用は元の action そのもの。
使われ方：始域の閉和の列に対する作用と有理不変部分。 -/
noncomputable def closedCoverPullbackSquareAction :
    SquareAction (closedCoverPullbackSquare f i j) G := by
  exact @closedImmersionSquareAction S V (closedImmersionPullback f i)
    (closedImmersionPullback f j) G inferInstance
    (closedImmersionSquare f i).f₁₂ (closedImmersionSquare f j).f₁₂
    (closedImmersionSquare_first_isClosedImmersion f j)
    (closedBaseChangeAction f i action over_base)
    (closedBaseChangeAction f j action over_base) action
    (closedPullbackAction_fst f i action 1 1
      (fun g ↦ by simpa using over_base g) (fun _ ↦ by simp))
    (closedPullbackAction_fst f j action 1 1
      (fun g ↦ by simpa using over_base g) (fun _ ↦ by simp))

/-- 概要：閉被覆への実際の比較立方体は同変（論文 補題 3.3）。
方針：二つの第二射影の不変性と f の不変性を、比較先の引き戻しの普遍性へ入力する。
規約：交わりの比較の不変性を追加仮定にしない。
使われ方：自然な全次数の列を有理不変部分で比較する。 -/
theorem closedCoverPullbackCube_equivariant :
    EquivariantSquareMap (closedCoverPullbackSquareAction f i j action over_base)
      (SquareAction.trivial (closedImmersionSquare i j) G) (closedCoverPullbackCube f i j) :=
  squareMapToTrivial_equivariant_of_isPullback _ (closedImmersionSquare_isPullback i j) _
    (closedBaseChangeAction_over_base f i action over_base)
    (closedBaseChangeAction_over_base f j action over_base) over_base

end SerrePositivity.KST.Descent
