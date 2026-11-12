module
public import SerrePositivity.KST.SConstruction.CoherentTetrahedronWhiskerTraces

/-! # 三辺を指定した元の三角形の前後合成を三単体から回収する
概要：Hom 正方形の合成面を、指定した通常射と既存の復号辺の前後合成へ同定する。
方針：元の辺・面の等式で四頂点の表示を合わせ、同じ実区間を回収する。
規約：局所 Kan 性や比較辺の新しい選択を要求しない。
使われ方：K 合成 prism の残る四辺の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SimplicialThickening MonoidalCategory CartesianMonoidalCategory SSet
open Spectra.CoherentPathCoordinates SerrePositivity.InfinityCategories
open scoped Simplicial
variable {C : Type v} [Category.{u} C] [SimplicialCategory C]

/-- 元の三番面の最初の辺は、同じ三単体の最初の辺。 -/
lemma tetrahedronFirstEdge_of_face {s : (SimplicialNerve C) _⦋3⦌}
    {t : (SimplicialNerve C) _⦋2⦌} (h : (SimplicialNerve C).δ 3 s = t) :
    (SimplicialNerve C).map tetrahedronFirstEdgeMap.op s = (SimplicialNerve C).δ 2 t := by
  rw [tetrahedronFirstEdgeMap, op_comp, CategoryTheory.Functor.map_comp_apply]
  change (SimplicialNerve C).δ 2 ((SimplicialNerve C).δ 3 s) = (SimplicialNerve C).δ 2 t
  exact congrArg ((SimplicialNerve C).δ 2) h

/-- 元の零番面の最後の辺は、同じ三単体の最後の辺。 -/
lemma tetrahedronLastEdge_of_face {s : (SimplicialNerve C) _⦋3⦌}
    {t : (SimplicialNerve C) _⦋2⦌} (h : (SimplicialNerve C).δ 0 s = t) :
    (SimplicialNerve C).map tetrahedronLastEdgeMap.op s = (SimplicialNerve C).δ 0 t := by
  rw [tetrahedronLastEdgeMap, op_comp, CategoryTheory.Functor.map_comp_apply]
  change (SimplicialNerve C).δ 0 ((SimplicialNerve C).δ 0 s) = (SimplicialNerve C).δ 0 t
  exact congrArg ((SimplicialNerve C).δ 0) h

/-- 第一座標一の辺は、指定した零番面の同じ復号辺を最初の元の射で前合成する。 -/
lemma tetrahedronTrace_include_first_specified {X₀ X₁ X₂ X₃ : C}
    (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (k : X₂ ⟶ X₃) (d : X₁ ⟶ X₃)
    (T : SSet.Edge.CompStruct (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge g) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge k) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge d))
    (s : (SimplicialNerve C) _⦋3⦌)
    (hf : (SimplicialNerve C).map tetrahedronFirstEdgeMap.op s = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).edge)
    (hT : (SimplicialNerve C).δ 0 s = T.simplex)
    (e : SimplicialCategory.sHom (s.obj (.mk (ULift.up 0)))
      (s.obj (.mk (ULift.up 3))) = SimplicialCategory.sHom X₀ X₃) :
    lift (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) (𝟙 (Δ[1] : SSet.{u})) ≫
        tetrahedronTrace s ≫ eqToHom e =
      SSet.yonedaEquiv.symm (coherentTriangleMappingEdge g k d T).edge ≫
        eHomWhiskerRight SSet f X₃ := by
  have hx₀ : s.obj (.mk (ULift.up 0)) = X₀ :=
    congrArg (fun q => (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveArrowData q).1) hf
  have hx₁ : s.obj (.mk (ULift.up 1)) = X₁ :=
    congrArg (fun q => (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveArrowData q).2.1) hf
  have hx₂ : s.obj (.mk (ULift.up 2)) = X₂ :=
    (congrArg (fun q : (SimplicialNerve C) _⦋2⦌ => q.obj (.mk (ULift.up 1))) hT).trans
      (congrArg (fun q => (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveArrowData q).2.1) T.d₂)
  have hx₃ : s.obj (.mk (ULift.up 3)) = X₃ :=
    (congrArg (fun q : (SimplicialNerve C) _⦋2⦌ => q.obj (.mk (ULift.up 2))) hT).trans
      (congrArg (fun q => (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveArrowData q).2.1) T.d₀)
  subst X₀
  subst X₁
  subst X₂
  subst X₃
  have hfirst : coherentSimplexArrow s 0 1 (by decide) = f :=
    coherentSimplexArrow_of_edge_face s tetrahedronFirstEdgeMap f hf
  have ht := coherentTriangleTrace_specified_face g k d T hT rfl
  simp only [eqToHom_refl, Category.comp_id] at ht ⊢
  calc
    _ = triangleTrace ((SimplicialNerve C).δ 0 s) ≫
        eHomWhiskerRight SSet (coherentSimplexArrow s 0 1 (by decide))
          (s.obj (.mk (ULift.up 3))) := tetrahedronTrace_include_first_whisker s
    _ = _ := by rw [hfirst, ht]

/-- 第二座標一の辺は、指定した三番面の同じ復号辺を最後の元の射で後合成する。 -/
lemma tetrahedronTrace_include_second_specified {X₀ X₁ X₂ X₃ : C}
    (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (d : X₀ ⟶ X₂) (k : X₂ ⟶ X₃)
    (T : SSet.Edge.CompStruct (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge g) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge d))
    (s : (SimplicialNerve C) _⦋3⦌)
    (hT : (SimplicialNerve C).δ 3 s = T.simplex)
    (hk : (SimplicialNerve C).map tetrahedronLastEdgeMap.op s = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge k).edge)
    (e : SimplicialCategory.sHom (s.obj (.mk (ULift.up 0)))
      (s.obj (.mk (ULift.up 3))) = SimplicialCategory.sHom X₀ X₃) :
    lift (𝟙 (Δ[1] : SSet.{u})) (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) ≫
        tetrahedronTrace s ≫ eqToHom e =
      SSet.yonedaEquiv.symm (coherentTriangleMappingEdge f g d T).edge ≫
        eHomWhiskerLeft SSet X₀ k := by
  have hx₀ : s.obj (.mk (ULift.up 0)) = X₀ :=
    (congrArg (fun q : (SimplicialNerve C) _⦋2⦌ => q.obj (.mk (ULift.up 0))) hT).trans
      (congrArg (fun q => (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveArrowData q).1) T.d₂)
  have hx₁ : s.obj (.mk (ULift.up 1)) = X₁ :=
    (congrArg (fun q : (SimplicialNerve C) _⦋2⦌ => q.obj (.mk (ULift.up 1))) hT).trans
      (congrArg (fun q => (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveArrowData q).2.1) T.d₂)
  have hx₂ : s.obj (.mk (ULift.up 2)) = X₂ :=
    congrArg (fun q => (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveArrowData q).1) hk
  have hx₃ : s.obj (.mk (ULift.up 3)) = X₃ :=
    congrArg (fun q => (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveArrowData q).2.1) hk
  subst X₀
  subst X₁
  subst X₂
  subst X₃
  have hlast : coherentSimplexArrow s 2 3 (by decide) = k :=
    coherentSimplexArrow_of_edge_face s tetrahedronLastEdgeMap k hk
  have ht := coherentTriangleTrace_specified_face f g d T hT rfl
  simp only [eqToHom_refl, Category.comp_id] at ht ⊢
  calc
    _ = triangleTrace ((SimplicialNerve C).δ 3 s) ≫
        eHomWhiskerLeft SSet (s.obj (.mk (ULift.up 0)))
          (coherentSimplexArrow s 2 3 (by decide)) := tetrahedronTrace_include_second_whisker s
    _ = _ := by rw [hlast, ht]

end SerrePositivity.KST.SConstruction
