module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.CosliceHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.Shapes
public import SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetElements

/-!
概要：同じ底の点にある二つの右 Kan 頂点が同じ coslice の辺の類を表せば、要素圏の頂点として一致する。
方針：coslice fiber の辺を取り出し、元の要素圏の恒等射上の辺を読む。
使われ方：R06.2 の指定始点の比較。
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories

namespace SerrePositivity.InfinityCategories.Sheaves

private theorem nerve_vertices_eq_of_vertical_edge {C D : Type u} [SmallCategory C] [SmallCategory D]
    (p : C ⥤ D)
    (hd : ∀ {x y : C} (f : x ⟶ y),
      Arrow.mk (p.map f) = Arrow.mk (𝟙 (p.obj x)) → x = y)
    {a b : (nerve C) _⦋0⦌} (e : (nerve C).Edge a b)
    (h : (e.map (nerveMap p)).edge = (SSet.Edge.id ((nerveMap p).app _ a)).edge) :
    a = b := by
  obtain ⟨x, rfl⟩ := nerveEquiv.symm.surjective a
  obtain ⟨y, rfl⟩ := nerveEquiv.symm.surjective b
  obtain ⟨f, rfl⟩ := (nerve.edgeMk_surjective (x := x) (y := y)) e
  change (nerveMap p).app (Opposite.op ⦋1⦌) (ComposableArrows.mk₁ f) =
    (SSet.Edge.id ((nerveMap p).app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ x))).edge at h
  rw [nerveMap_app_mk₁, nerveMap_app_mk₀] at h
  have hi := congrArg SSet.Edge.edge (nerve.edgeMk_id (p.obj x))
  change ComposableArrows.mk₁ (𝟙 (p.obj x)) =
    (SSet.Edge.id (X := nerve D) (ComposableArrows.mk₀ (p.obj x))).edge at hi
  rw [← hi] at h
  have hx := congrArg (ComposableArrows.arrowEquiv (C := D)) h
  exact congrArg nerveEquiv.symm (hd f hx)

private theorem elements_eq_of_projection_arrow_id {D : Type u} [SmallCategory D]
    (P : D ⥤ Type u) {a b : P.Elements} (f : a ⟶ b)
    (h : Arrow.mk ((Functor.Elements.π P).map f) =
      Arrow.mk (𝟙 ((Functor.Elements.π P).obj a))) : a = b := by
  obtain ⟨hl, hr, hArrow⟩ := (Arrow.mk_eq_mk_iff _ _).mp h
  change a.obj = a.obj at hl
  change b.obj = a.obj at hr
  change f.hom = eqToHom hl ≫ 𝟙 a.obj ≫ eqToHom hr.symm at hArrow
  have hf : f.hom = eqToHom hr.symm := by
    simpa only [eqToHom_refl, Category.id_comp] using hArrow
  exact Functor.Elements.ext a b hr.symm (hf ▸ f.map_val)

private theorem rightKanReadout_localLabels_of_cosliceHomMk_eq
    {K X : SSet.{u}} [Quasicategory X]
    {A D : Type u} [SmallCategory A] [SmallCategory D]
    (p : A ⥤ D)
    (hd : ∀ {x y : A} (f : x ⟶ y),
      Arrow.mk (p.map f) = Arrow.mk (𝟙 (p.obj x)) → x = y)
    (δ : K ⟶ X) (v : X _⦋0⦌)
    (i : rightKanShape δ v ⟶ nerve A)
    (b : K ⟶ nerve D) (hi : i ≫ nerveMap p = rightKanProjection δ v ≫ b)
    {k : K _⦋0⦌}
    (s t : (vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm v))
      (δ.app _ k)) _⦋0⦌)
    (h : Truncated.HomotopyCategory.homMk (cosliceFiberEdge _ _ s) =
      Truncated.HomotopyCategory.homMk (cosliceFiberEdge _ _ t)) :
    let q := sliceUnderProjection (SSet.yonedaEquiv.symm v)
    let l : vertexFiber q (δ.app _ k) ⟶ rightKanShape δ v :=
      pullback.lift (vertexFiberι q _) (SSet.const k)
        (by rw [vertexFiberι_comp, SSet.const_comp])
    (l ≫ i).app _ s = (l ≫ i).app _ t := by
  intro q l
  have hp : l ≫ rightKanProjection δ v = SSet.const k := pullback.lift_snd _ _ _
  have hc : (l ≫ i) ≫ nerveMap p = SSet.const (b.app _ k) := by
    rw [Category.assoc, hi, ← Category.assoc l, hp, SSet.const_comp]
  let a := SSet.yonedaEquiv.symm v
  let y := δ.app (Opposite.op ⦋0⦌) k
  have h₂ : Truncated.HomotopyCategory₂.homMk (cosliceFiberEdge a y s) =
      Truncated.HomotopyCategory₂.homMk (cosliceFiberEdge a y t) := by
    have hh := congrArg (fun m => (pathToEdgeHomotopyCategory ((truncation 2).obj X)).map m) h
    simpa only [pathToEdgeHomotopyCategory, Truncated.HomotopyCategory.lift_map_homMk] using hh
  obtain ⟨e₀⟩ := cosliceFiber_nonempty_edge_of_homotopicL a y s t (Quotient.exact h₂)
  let e := SSet.Edge.ofTruncated (X := vertexFiber q y) e₀
  let e' := e.map (l ≫ i)
  have h₁ : ((l ≫ i) ≫ nerveMap p).app _ e.edge = (SSet.Edge.id (X := nerve D) (b.app _ k)).edge := by
    rw [hc]
    exact (pinchedConstant_one (b.app _ k))
  have hk : (nerveMap p).app _ ((l ≫ i).app _ s) = b.app _ k := by
    have hh := ConcreteCategory.congr_hom (NatTrans.congr_app hc (Opposite.op ⦋0⦌)) s
    exact hh.trans (pinchedConstant_zero (b.app _ k))
  exact nerve_vertices_eq_of_vertical_edge p hd e'
    (h₁.trans (congrArg (fun z => (SSet.Edge.id (X := nerve D) z).edge) hk).symm)

private theorem asSmall_elements_eq_of_projection_arrow_id {D : Type u} [SmallCategory D]
    (P : D ⥤ Type u) :
    let p : AsSmall.{u + 1} P.Elements ⥤ AsSmall.{u + 1} D :=
      AsSmall.down ⋙ Functor.Elements.π P ⋙ AsSmall.up
    ∀ {x y : AsSmall.{u + 1} P.Elements} (f : x ⟶ y),
      Arrow.mk (p.map f) = Arrow.mk (𝟙 (p.obj x)) → x = y := by
  intro p x y f h
  let d : AsSmall.{u + 1} D ⥤ D := AsSmall.down
  have hr := congrArg d.mapArrow.obj h
  change Arrow.mk ((Functor.Elements.π P).map f.down) =
    Arrow.mk (𝟙 ((Functor.Elements.π P).obj ((AsSmall.down : AsSmall.{u + 1} P.Elements ⥤ P.Elements).obj x))) at hr
  exact ULift.ext (elements_eq_of_projection_arrow_id P f.down hr)

private theorem pullback_vertices_eq
    {A C B : SSet.{u}} (p : A ⟶ B) (q : C ⟶ B) {s t : (pullback p q) _⦋0⦌}
    (h₀ : (pullback.fst p q).app _ s = (pullback.fst p q).app _ t)
    (h₁ : (pullback.snd p q).app _ s = (pullback.snd p q).app _ t) : s = t := by
  apply SSet.yonedaEquiv.symm.injective
  apply pullback.hom_ext
  · rw [SSet.yonedaEquiv_symm_comp, SSet.yonedaEquiv_symm_comp, h₀]
  · rw [SSet.yonedaEquiv_symm_comp, SSet.yonedaEquiv_symm_comp, h₁]

/-- 同じ底の点にある二つの右 Kan 頂点が同じ coslice の辺の類を表せば、要素圏の頂点として一致する。
HTT 1.2.2・3.3.2、Kerodon §4.6.5（Tag 01KW）の固定終点の写像空間。 -/
lemma rightKanReadout_elements_vertices_eq_of_cosliceHomMk_eq
    {K X : SSet.{u + 1}} [Quasicategory X]
    {D : Type u} [SmallCategory D] (P : D ⥤ Type u)
    (δ : K ⟶ X) (v : X _⦋0⦌) :
    let p : AsSmall.{u + 1} P.Elements ⥤ AsSmall.{u + 1} D :=
      AsSmall.down ⋙ Functor.Elements.π P ⋙ AsSmall.up
    ∀ (i : rightKanShape δ v ⟶ nerve (AsSmall.{u + 1} P.Elements))
      (b : K ⟶ nerve (AsSmall.{u + 1} D)),
    i ≫ nerveMap p = rightKanProjection δ v ≫ b →
    ∀ (x y : (rightKanShape δ v) _⦋0⦌)
      (hxy : (rightKanProjection δ v).app _ x = (rightKanProjection δ v).app _ y),
    let q := sliceUnderProjection (SSet.yonedaEquiv.symm v)
    let k := (rightKanProjection δ v).app _ x
    let s : (vertexFiber q (δ.app _ k)) _⦋0⦌ :=
      ⟨(pullback.fst q δ).app _ x, by
        rw [pinchedConstant_zero]
        have hc : pullback.fst q δ ≫ q = pullback.snd q δ ≫ δ := pullback.condition
        exact ConcreteCategory.congr_hom (NatTrans.congr_app hc _) x⟩
    let t : (vertexFiber q (δ.app _ k)) _⦋0⦌ :=
      ⟨(pullback.fst q δ).app _ y, by
        rw [pinchedConstant_zero]
        have hc : pullback.fst q δ ≫ q = pullback.snd q δ ≫ δ := pullback.condition
        exact (ConcreteCategory.congr_hom (NatTrans.congr_app hc _) y).trans
          (congrArg (fun z => δ.app (Opposite.op ⦋0⦌) z) hxy.symm)⟩
    Truncated.HomotopyCategory.homMk (cosliceFiberEdge _ _ s) =
      Truncated.HomotopyCategory.homMk (cosliceFiberEdge _ _ t) →
    i.app _ x = i.app _ y := by
  intro p i b hi x y hxy q k s t h
  let l : vertexFiber q (δ.app _ k) ⟶ rightKanShape δ v :=
    pullback.lift (vertexFiberι q _) (SSet.const k)
      (by rw [vertexFiberι_comp, SSet.const_comp])
  have h₀ : l ≫ pullback.fst q δ = vertexFiberι q (δ.app _ k) :=
    pullback.lift_fst _ _ _
  have h₁ : l ≫ pullback.snd q δ = SSet.const k := pullback.lift_snd _ _ _
  have hx : l.app _ s = x := by
    apply pullback_vertices_eq q δ
    · exact ConcreteCategory.congr_hom (NatTrans.congr_app h₀ _) s
    · exact (ConcreteCategory.congr_hom (NatTrans.congr_app h₁ _) s).trans
        (pinchedConstant_zero k)
  have hy : l.app _ t = y := by
    apply pullback_vertices_eq q δ
    · exact ConcreteCategory.congr_hom (NatTrans.congr_app h₀ _) t
    · exact (ConcreteCategory.congr_hom (NatTrans.congr_app h₁ _) t).trans
        ((pinchedConstant_zero k).trans hxy)
  have he := rightKanReadout_localLabels_of_cosliceHomMk_eq p
    (asSmall_elements_eq_of_projection_arrow_id P) δ v i b hi s t h
  change i.app _ (l.app _ s) = i.app _ (l.app _ t) at he
  rwa [hx, hy] at he

end SerrePositivity.InfinityCategories.Sheaves
