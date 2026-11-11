module
public import SerrePositivity.KST.SConstruction.DGGluingAxesDerivedTriangle
public import SerrePositivity.DifferentialGraded.Perfect.Basic

/-! # 元の二軸による実 gluing の Perfect 生成性
概要：元の全右軸・全左軸の代表加群は、同じ gluing の全 Perfect 対象を生成する。
方針：元の実二軸三角形で各代表を戻し、D の既存 Perfect 生成判定を使う。
規約：商の生成性を仮定しない。使われ方：具体的対角と右端 End の Morita 比較。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits Pretriangulated DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (zc : C) (hc : IsZero (ForgetEnrichment.of (Complex R) zc))
  (zd : D) (hd : IsZero (ForgetEnrichment.of (Complex R) zd))
local notation "G" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M
local notation "Q" => moduleToDerived R G

/-- 元の実左右軸の対象だけからなる、同じ gluing 内の指定生成集合。 -/
def dgGluingAxisObjects : Set G :=
  Set.range (dgGluingRightAxisObject R C D M zc) ∪
    Set.range (dgGluingLeftAxisObject R C D M zd)

include hc hd in
/-- 同じ二軸代表を含む三角的な条件は、元の全対象の代表を含む。 -/
lemma dgGluingAxes_representable_mem
    (P : ObjectProperty (DerivedModuleCategory R G))
    [P.IsTriangulatedClosed₂] [P.IsClosedUnderIsomorphisms]
    (hR : ∀ d : D, P ((Q).obj (ForgetEnrichment.of (Complex R)
      (representable R (dgGluingRightAxisObject R C D M zc d)))))
    (hL : ∀ c : C, P ((Q).obj (ForgetEnrichment.of (Complex R)
      (representable R (dgGluingLeftAxisObject R C D M zd c))))) (X : G) :
    P ((Q).obj (ForgetEnrichment.of (Complex R) (representable R X))) := by
  have h := P.ext_of_isTriangulatedClosed₂'
    (dgGluingAxesDerivedTriangle R C D M zc hc zd hd X)
    (dgGluingAxesDerivedTriangle_distinguished R C D M zc hc zd hd X)
    (hR X.right) (hL X.left)
  rw [ObjectProperty.isoClosure_eq_self] at h
  exact h

include hc hd in
/-- 元の gluing の Perfect 対象を含むことは、同じ二軸代表だけで判定できる。 -/
lemma dgGluingPerfect_le_iff_axes
    (P : ObjectProperty (DerivedModuleCategory R G)) [P.IsTriangulated]
    [P.IsClosedUnderIsomorphisms] [P.IsStableUnderRetracts] :
    modulePerfect R G ≤ P ↔
      (∀ d : D, P ((Q).obj (ForgetEnrichment.of (Complex R)
        (representable R (dgGluingRightAxisObject R C D M zc d))))) ∧
      (∀ c : C, P ((Q).obj (ForgetEnrichment.of (Complex R)
        (representable R (dgGluingLeftAxisObject R C D M zd c))))) := by
  rw [modulePerfect_le_iff_generators R G P]
  constructor
  · intro h
    exact ⟨fun d => h _, fun c => h _⟩
  · rintro ⟨hR, hL⟩
    exact dgGluingAxes_representable_mem R C D M zc hc zd hd P hR hL

include hc hd in
/-- 指定二軸の同じ生成集合から作る Perf は、元の gluing の全 Perf に等しい。 -/
lemma dgGluingPerfectOver_axes_eq :
    modulePerfectOver R G (dgGluingAxisObjects R C D M zc zd) = modulePerfect R G := by
  apply le_antisymm
  · exact modulePerfectOver_mono R G (Set.subset_univ _)
  · apply (dgGluingPerfect_le_iff_axes R C D M zc hc zd hd
      (modulePerfectOver R G (dgGluingAxisObjects R C D M zc zd))).mpr
    constructor
    · intro d
      exact modulePerfectOver_representable R G _ (Or.inl ⟨d, rfl⟩)
    · intro c
      exact modulePerfectOver_representable R G _ (Or.inr ⟨c, rfl⟩)

end SerrePositivity.KST.SConstruction
