module

public import SerrePositivity.InfinityCategories.F1B.Fibrations.FiberwiseFunctorPrecomposition
public import SerrePositivity.InfinityCategories.F1B.FunctorCategories.RelativeInitialExtension

/-!
概要：fiber ごとの図式の持ち上げと実際の大域図式の持ち上げを同定し、相対骨格で組み立てる。
方針：族の普遍性で持ち上げ問題を移し、相対始点境界充填を骨格全体へ適用する。
規約：境界充填の仮定を明示する。fiber ごとの余極限性からの導出は別に必要。
使われ方：Kerodon Lemma 7.3.4.5 の組み立ての一般部分。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：大域図式の制限の持ち上げ問題と、fiber ごとの関手の族の持ち上げ問題は同値。
方針：curry の制限との両立、全射性・単射性を使う。
規約：全空間の図式は底の射も含めた依存和で指定する。
使われ方：骨格で作った族を、境界と元の図式を保つ実際の延長へ戻す。 -/
lemma fiberwiseFunctor_lift_iff {B A A₀ D : SSet.{u}} {F G : Over B ⥤ SSet.{u}}
    (α : F ⟶ G) (i : A₀ ⟶ A)
    [PreservesColimitsOfShape A.Elementsᵒᵖ F] [PreservesColimitsOfShape A.Elementsᵒᵖ G]
    [PreservesColimitsOfShape A₀.Elementsᵒᵖ G]
    (s₀ : SerrePositivity.InfinityCategories.FiberwiseFunctorSimplex G D A₀) (t : SerrePositivity.InfinityCategories.FiberwiseFunctorSimplex F D A) :
    (∃ s : SerrePositivity.InfinityCategories.FiberwiseFunctorSimplex G D A,
      SerrePositivity.InfinityCategories.fiberwiseFunctorRestrict G D i s = s₀ ∧ SerrePositivity.InfinityCategories.fiberwiseFunctorPreSimplex α s = t) ↔
    ∃ f : A ⟶ SerrePositivity.InfinityCategories.fiberwiseFunctor G D,
      i ≫ f = SerrePositivity.InfinityCategories.fiberwiseFunctorCurry G s₀ ∧
        f ≫ SerrePositivity.InfinityCategories.fiberwiseFunctorPre α = SerrePositivity.InfinityCategories.fiberwiseFunctorCurry F t := by
  constructor
  · rintro ⟨s, hs₀, ht⟩
    refine ⟨SerrePositivity.InfinityCategories.fiberwiseFunctorCurry G s, ?_, ?_⟩
    · rw [← SerrePositivity.InfinityCategories.fiberwiseFunctorCurry_precomp, hs₀]
    · rw [← SerrePositivity.InfinityCategories.fiberwiseFunctorCurry_pre, ht]
  · rintro ⟨f, hf₀, hft⟩
    let s := (SerrePositivity.InfinityCategories.fiberwiseFunctorHomEquiv G).symm f
    have hs : SerrePositivity.InfinityCategories.fiberwiseFunctorCurry G s = f :=
      (SerrePositivity.InfinityCategories.fiberwiseFunctorHomEquiv G).apply_symm_apply f
    refine ⟨s, ?_, ?_⟩
    · apply SerrePositivity.InfinityCategories.fiberwiseFunctorCurry_injective G
      rw [SerrePositivity.InfinityCategories.fiberwiseFunctorCurry_precomp, hs, hf₀]
    · apply SerrePositivity.InfinityCategories.fiberwiseFunctorCurry_injective F
      rw [SerrePositivity.InfinityCategories.fiberwiseFunctorCurry_pre, hs, hft]

/-- 概要：族の制限に対する相対始点境界充填から大域図式の延長を組み立てる。
方針：全頂点を含む部分の相対骨格で族を持ち上げ、実際の図式へ戻す。
規約：充填性は V の境界条件として明示し、普遍余錐性から導出したとは主張しない。
使われ方：fiber ごとの余極限からの Kan 拡張の存在定理へ接続する組み立ての核。 -/
lemma exists_kanFiberwise_extension_of_initialBoundary
    {B A D : SSet.{u}} {F G : Over B ⥤ SSet.{u}} (α : F ⟶ G)
    (A₀ : A.Subcomplex) (hA₀ : ∀ v : A _⦋0⦌, v ∈ A₀.obj (Opposite.op ⦋0⦌))
    [PreservesColimitsOfShape A.Elementsᵒᵖ F] [PreservesColimitsOfShape A.Elementsᵒᵖ G]
    [PreservesColimitsOfShape (A₀ : SSet.{u}).Elementsᵒᵖ G]
    (s₀ : SerrePositivity.InfinityCategories.FiberwiseFunctorSimplex G D (A₀ : SSet.{u}))
    (t : SerrePositivity.InfinityCategories.FiberwiseFunctorSimplex F D A)
    (hw : SerrePositivity.InfinityCategories.fiberwiseFunctorPreSimplex α s₀ = SerrePositivity.InfinityCategories.fiberwiseFunctorRestrict F D A₀.ι t)
    (hinit : ∀ (n : ℕ) (σ : A _⦋n + 1⦌), σ ∉ A₀.obj (Opposite.op ⦋n + 1⦌) →
      InitialBoundaryLifting (SerrePositivity.InfinityCategories.fiberwiseFunctorPre (D := D) α)
        ((SerrePositivity.InfinityCategories.fiberwiseFunctorCurry G s₀).app (Opposite.op ⦋0⦌)
          ⟨simplexFirstVertex σ, hA₀ _⟩)) :
    ∃ s : SerrePositivity.InfinityCategories.FiberwiseFunctorSimplex G D A,
      SerrePositivity.InfinityCategories.fiberwiseFunctorRestrict G D A₀.ι s = s₀ ∧ SerrePositivity.InfinityCategories.fiberwiseFunctorPreSimplex α s = t := by
  apply (fiberwiseFunctor_lift_iff α A₀.ι s₀ t).2
  apply exists_lift_of_initial_first_vertices A₀ hA₀ (SerrePositivity.InfinityCategories.fiberwiseFunctorPre α)
    (SerrePositivity.InfinityCategories.fiberwiseFunctorCurry G s₀) (SerrePositivity.InfinityCategories.fiberwiseFunctorCurry F t) _ hinit
  rw [← SerrePositivity.InfinityCategories.fiberwiseFunctorCurry_pre, hw, SerrePositivity.InfinityCategories.fiberwiseFunctorCurry_precomp]

end SerrePositivity.InfinityCategories
