module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.RightFibrationReflection
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.LeftFibrationEquivalenceLifting
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.InitialUniqueness

/-!
概要：指定右分数三角形を coslice の同じ実三角形へ持ち上げる。
方針：可逆な最初の辺を終点指定で持ち上げ、隣接二辺を固定した内ホーンを充填する。
規約：標的二単体と指定された後辺を選び直さず、始点の逆像も厳密に保持する。
使われ方：有限図式の前段正規化で、隣接二辺の比較を同じ右分数へ接続する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions
open _root_.SerrePositivity.KST.LocalizingInvariants

/-- 内ファイブレーションは、指定した隣接二辺と標的二単体を厳密に保って合成を持ち上げる。 -/
lemma innerFibration_liftCompStruct {X Y : SSet.{u}} (q : X ⟶ Y) [InnerFibration q]
    {x₀ x₁ x₂ : X _⦋0⦌}
    (f : Truncated.Edge (X := (truncation 2).obj X) x₀ x₁)
    (g : Truncated.Edge (X := (truncation 2).obj X) x₁ x₂)
    (h : Truncated.Edge (X := (truncation 2).obj Y)
      (q.app (Opposite.op ⦋0⦌) x₀) (q.app (Opposite.op ⦋0⦌) x₂))
    (t : Truncated.Edge.CompStruct (f.map ((truncation 2).map q))
      (g.map ((truncation 2).map q)) h) :
    Nonempty (Σ h' : Truncated.Edge (X := (truncation 2).obj X) x₀ x₂,
      {t' : Truncated.Edge.CompStruct f g h' //
        q.app (Opposite.op ⦋2⦌) t'.simplex = t.simplex}) := by
  obtain ⟨a, ha₂, ha₀⟩ := horn₂₁.isPushout.exists_desc
    (SSet.yonedaEquiv.symm f.edge) (SSet.yonedaEquiv.symm g.edge) (by
      rw [stdSimplex.δ_comp_yonedaEquiv_symm, stdSimplex.δ_comp_yonedaEquiv_symm]
      exact congrArg SSet.yonedaEquiv.symm (f.tgt_eq.trans g.src_eq.symm))
  have := InnerFibration.mem (q := q) _
    (innerHornInclusions.intro (1 : Fin 3) (by decide) (by decide))
  have sq : CommSq a (horn 2 1).ι q (SSet.yonedaEquiv.symm t.simplex) := by
    constructor
    apply horn₂₁.isPushout.hom_ext
    · simp only [← Category.assoc, ha₂, horn.ι_ι]
      apply SSet.yonedaEquiv.injective
      rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply,
        stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply]
      exact t.d₂.symm
    · simp only [← Category.assoc, ha₀, horn.ι_ι]
      apply SSet.yonedaEquiv.injective
      rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply,
        stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply]
      exact t.d₀.symm
  let F := sq.lift
  have hF₂ : stdSimplex.δ 2 ≫ F = SSet.yonedaEquiv.symm f.edge := by
    rw [← horn.ι_ι_assoc 1 2 (by decide), sq.fac_left, ha₂]
    rfl
  have hF₀ : stdSimplex.δ 0 ≫ F = SSet.yonedaEquiv.symm g.edge := by
    rw [← horn.ι_ι_assoc 1 0 (by decide), sq.fac_left, ha₀]
    rfl
  let s := SSet.yonedaEquiv F
  have h₂ : X.δ 2 s = f.edge := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, hF₂]
    exact SSet.yonedaEquiv.apply_symm_apply f.edge
  have h₀ : X.δ 0 s = g.edge := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, hF₀]
    exact SSet.yonedaEquiv.apply_symm_apply g.edge
  have hsrc : X.δ (1 : Fin 2) (X.δ (1 : Fin 3) s) = x₀ := by
    have he : X.δ (1 : Fin 2) (X.δ (1 : Fin 3) s) =
        X.δ (1 : Fin 2) (X.δ (2 : Fin 3) s) := by
      simp only [SimplicialObject.δ, ← CategoryTheory.Functor.map_comp_apply, ← op_comp]
      apply congrArg (fun α : ⦋0⦌ ⟶ ⦋2⦌ ↦ X.map α.op s)
      decide
    rw [he, h₂]
    exact f.src_eq
  have htgt : X.δ (0 : Fin 2) (X.δ (1 : Fin 3) s) = x₂ := by
    have he : X.δ (0 : Fin 2) (X.δ (1 : Fin 3) s) =
        X.δ (0 : Fin 2) (X.δ (0 : Fin 3) s) := by
      simp only [SimplicialObject.δ, ← CategoryTheory.Functor.map_comp_apply, ← op_comp]
      apply congrArg (fun α : ⦋0⦌ ⟶ ⦋2⦌ ↦ X.map α.op s)
      decide
    rw [he, h₀]
    exact g.tgt_eq
  let h' : Truncated.Edge (X := (truncation 2).obj X) x₀ x₂ :=
    ⟨X.δ 1 s, hsrc, htgt⟩
  refine ⟨h', ⟨⟨s, h₂, h₀, rfl⟩, ?_⟩⟩
  change q.app (Opposite.op ⦋2⦌) (SSet.yonedaEquiv sq.lift) = _
  rw [← SSet.yonedaEquiv_comp, sq.fac_right, Equiv.apply_symm_apply]

/-- 同じ右分数三角形と指定後辺を保持する、左ファイブレーション内の実持ち上げ。 -/
structure LeftFractionTriangleLift {X Y : SSet.{u}} (q : X ⟶ Y)
    {x₁ x₂ : X _⦋0⦌} {b₀ : Y _⦋0⦌}
    (g : Truncated.Edge (X := (truncation 2).obj X) x₁ x₂)
    (f : Truncated.Edge (X := (truncation 2).obj Y) b₀
      (q.app (Opposite.op ⦋0⦌) x₁))
    (h : Truncated.Edge (X := (truncation 2).obj Y) b₀
      (q.app (Opposite.op ⦋0⦌) x₂))
    (t : Truncated.Edge.CompStruct f (g.map ((truncation 2).map q)) h) where
  source : X _⦋0⦌
  source_eq : q.app (Opposite.op ⦋0⦌) source = b₀
  first : Truncated.Edge (X := (truncation 2).obj X) source x₁
  diagonal : Truncated.Edge (X := (truncation 2).obj X) source x₂
  first_image : (first.map ((truncation 2).map q)).edge = f.edge
  diagonal_image : (diagonal.map ((truncation 2).map q)).edge = h.edge
  triangle : Truncated.Edge.CompStruct first g diagonal
  triangle_image : q.app (Opposite.op ⦋2⦌) triangle.simplex = t.simplex
  first_isInvertible : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := X) first

/-- 可逆な最初の辺を持つ指定三角形は、同じ指定後辺を保って全三角形として持ち上がる。 -/
lemma exists_leftFractionTriangleLift {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    (q : X ⟶ Y) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q] {x₁ x₂ : X _⦋0⦌} {b₀ : Y _⦋0⦌}
    (g : Truncated.Edge (X := (truncation 2).obj X) x₁ x₂)
    (f : Truncated.Edge (X := (truncation 2).obj Y) b₀
      (q.app (Opposite.op ⦋0⦌) x₁))
    (h : Truncated.Edge (X := (truncation 2).obj Y) b₀
      (q.app (Opposite.op ⦋0⦌) x₂))
    (t : Truncated.Edge.CompStruct f (g.map ((truncation 2).map q)) h)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := Y) f) : Nonempty (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.LeftFractionTriangleLift q g f h t) := by
  obtain ⟨F, hF₁, hFq⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.leftFibration_liftInvertibleEdge_target q x₁ f hf
  let σ := SSet.yonedaEquiv F
  let x₀ := X.δ 1 σ
  have hσ : X.δ 0 σ = x₁ := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, hF₁, Equiv.apply_symm_apply]
  let u : Truncated.Edge (X := (truncation 2).obj X) x₀ x₁ := ⟨σ, rfl, hσ⟩
  have hu : (u.map ((truncation 2).map q)).edge = f.edge := by
    change q.app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv F) = _
    rw [← SSet.yonedaEquiv_comp, hFq]
    exact SSet.yonedaEquiv.apply_symm_apply f.edge
  have hx : q.app (Opposite.op ⦋0⦌) x₀ = b₀ := by
    have hn := q.naturality_apply (SimplexCategory.δ (1 : Fin 2)).op σ
    have he := congrArg (fun z => Y.δ 1 z) hu
    exact hn.trans (he.trans f.src_eq)
  let v : Truncated.Edge (X := (truncation 2).obj Y)
      (q.app (Opposite.op ⦋0⦌) x₀) (q.app (Opposite.op ⦋0⦌) x₂) :=
    ⟨h.edge, h.src_eq.trans hx.symm, h.tgt_eq⟩
  let T : Truncated.Edge.CompStruct (u.map ((truncation 2).map q))
      (g.map ((truncation 2).map q)) v :=
    ⟨t.simplex, t.d₂.trans hu.symm, t.d₀, t.d₁⟩
  obtain ⟨w, Tw, hw⟩ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.innerFibration_liftCompStruct q u g v T
  have hw₁ : (w.map ((truncation 2).map q)).edge = h.edge := by
    calc
      _ = q.app (Opposite.op ⦋1⦌) (X.δ 1 Tw.simplex) :=
        congrArg (q.app (Opposite.op ⦋1⦌)) Tw.d₁.symm
      _ = Y.δ 1 (q.app (Opposite.op ⦋2⦌) Tw.simplex) :=
        q.naturality_apply (SimplexCategory.δ (1 : Fin 3)).op Tw.simplex
      _ = h.edge := by rw [hw]; exact t.d₁
  have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := X) u := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.leftFibration_reflects_invertibleEdge q u
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr hu).mpr hf)
  exact ⟨⟨x₀, hx, u, w, hu, hw₁, Tw, hw, hi⟩⟩

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.LeftFractionTriangleLift (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LeftFractionTriangleLift := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.LeftFractionTriangleLift

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.exists_leftFractionTriangleLift := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.exists_leftFractionTriangleLift

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.innerFibration_liftCompStruct := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.innerFibration_liftCompStruct

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.LeftFractionTriangleLift._sizeOf_1 (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LeftFractionTriangleLift._sizeOf_1 := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.LeftFractionTriangleLift._sizeOf_1

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.LeftFractionTriangleLift._sizeOf_inst (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LeftFractionTriangleLift._sizeOf_inst := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.LeftFractionTriangleLift._sizeOf_inst

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.LeftFractionTriangleLift.casesOn (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LeftFractionTriangleLift.casesOn := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.LeftFractionTriangleLift.casesOn

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.LeftFractionTriangleLift.ctorIdx (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LeftFractionTriangleLift.ctorIdx := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.LeftFractionTriangleLift.ctorIdx

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.LeftFractionTriangleLift.diagonal (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LeftFractionTriangleLift.diagonal := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.LeftFractionTriangleLift.diagonal

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LeftFractionTriangleLift.diagonal_image := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.LeftFractionTriangleLift.diagonal_image

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.LeftFractionTriangleLift.first (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LeftFractionTriangleLift.first := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.LeftFractionTriangleLift.first

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LeftFractionTriangleLift.first_image := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.LeftFractionTriangleLift.first_image

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LeftFractionTriangleLift.first_isInvertible := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.LeftFractionTriangleLift.first_isInvertible

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.LeftFractionTriangleLift.mk (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LeftFractionTriangleLift.mk := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.LeftFractionTriangleLift.mk

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.LeftFractionTriangleLift.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LeftFractionTriangleLift.noConfusion := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.LeftFractionTriangleLift.noConfusion

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.LeftFractionTriangleLift.noConfusionType (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LeftFractionTriangleLift.noConfusionType := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.LeftFractionTriangleLift.noConfusionType

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.LeftFractionTriangleLift.rec (since := "2026-11-05"), elab_as_elim]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LeftFractionTriangleLift.rec := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.LeftFractionTriangleLift.rec

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.LeftFractionTriangleLift.recOn (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LeftFractionTriangleLift.recOn := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.LeftFractionTriangleLift.recOn

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.LeftFractionTriangleLift.source (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LeftFractionTriangleLift.source := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.LeftFractionTriangleLift.source

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LeftFractionTriangleLift.source_eq := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.LeftFractionTriangleLift.source_eq

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.LeftFractionTriangleLift.triangle (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LeftFractionTriangleLift.triangle := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.LeftFractionTriangleLift.triangle

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LeftFractionTriangleLift.triangle_image := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.LeftFractionTriangleLift.triangle_image

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.LeftFractionTriangleLift.mk._flat_ctor (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LeftFractionTriangleLift.mk._flat_ctor := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.LeftFractionTriangleLift.mk._flat_ctor

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LeftFractionTriangleLift.mk.inj := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.LeftFractionTriangleLift.mk.inj

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LeftFractionTriangleLift.mk.injEq := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.LeftFractionTriangleLift.mk.injEq

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.LeftFractionTriangleLift.mk.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LeftFractionTriangleLift.mk.noConfusion := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.LeftFractionTriangleLift.mk.noConfusion

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LeftFractionTriangleLift.mk.sizeOf_spec := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.LeftFractionTriangleLift.mk.sizeOf_spec
