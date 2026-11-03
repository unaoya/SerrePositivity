module
public import SerrePositivity.InfinityCategories.Derived.SuspensionAction.EpsilonCellRigidity
public import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence
public import SerrePositivity.InfinityCategories.Derived.DGStableHomotopyEquivalence
public import SerrePositivity.InfinityCategories.F1.Categories.QuasicategoryCore

/-!
概要：固定 ε 関手圏の null 対象での評価は、境界を厳密に零へ送る。
方針：次数 −1 成分の消滅を chain map の可換性に適用し H⁰ を経由させる。
規約：native map の存在・不存在はこの葉だけでは結論しない。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory CategoryTheory.Limits DifferentialGraded HomologicalComplex KST.SConstruction
open DGCategoryCellResolution
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D]
  (S : Set C) (T : Set (Source R D))

/-- null 対象での評価は固定 ε 関手圏の境界関係を厳密な等号へ送る。 -/
lemma quotientEpsilonCellEvaluation_boundary (b : S)
    {F G : ClosedCategory R (NullPreservingFunctorsε R C (Source R D) S T)}
    (f g : F ⟶ G)
    (h : boundaryRelation R (NullPreservingFunctorsε R C (Source R D) S T) f g) :
    (((nullPreservingFunctorsεForget R C (Source R D) S T).comp
      (dgFunctorEvaluationDG R C (Source R D) b.val)).onClosed).map f =
    (((nullPreservingFunctorsεForget R C (Source R D) S T).comp
      (dgFunctorEvaluationDG R C (Source R D) b.val)).onClosed).map g := by
  let E := (nullPreservingFunctorsεForget R C (Source R D) S T).comp
    (dgFunctorEvaluationDG R C (Source R D) b.val)
  obtain ⟨t, ht⟩ := (toHomotopy_map_eq_iff_boundary R _ f g).1
    ((toHomotopy_map_eq_iff R _ f g).2 h)
  have hz : (E.map F G).f (-1) t = 0 :=
    quotientEpsilonCellHom_component_zero_of_degree_ne_zero R C D S T F G b (-1) (by omega) t
  apply (closedHomEquiv R (Source R D) _ _).injective
  rw [E.closedHomEquiv_map, E.closedHomEquiv_map]
  apply Subtype.ext
  have hd := (ConcreteCategory.congr_hom ((E.map F G).comm (-1) 0) t).symm
  change (E.map F G).f 0 ((homObject R _ F G).d (-1) 0 t) =
    (homObject R (Source R D) _ _).d (-1) 0 ((E.map F G).f (-1) t) at hd
  rw [ht, hz, map_zero, map_sub] at hd
  exact sub_eq_zero.mp hd

/-- 固定 ε 関手圏の H⁰ から、null 対象上の厳密な閉射への評価。 -/
def quotientEpsilonCellHomotopyEvaluation (b : S) :
    DifferentialGraded.HomotopyCategory R
      (NullPreservingFunctorsε R C (Source R D) S T) ⥤ ClosedCategory R (Source R D) :=
  CategoryTheory.Quotient.lift _
    (((nullPreservingFunctorsεForget R C (Source R D) S T).comp
      (dgFunctorEvaluationDG R C (Source R D) b.val)).onClosed)
    (fun _ _ f g h => quotientEpsilonCellEvaluation_boundary R C D S T b f g h)

/-- 異なる null 像を結ぶ閉射は、同じ評価で零になる。 -/
lemma quotientEpsilonCellEvaluation_zero_of_obj_ne (b : S)
    {F G : ClosedCategory R (NullPreservingFunctorsε R C (Source R D) S T)}
    (f : F ⟶ G) (h : F.val.obj b.val ≠ G.val.obj b.val) :
    (((nullPreservingFunctorsεForget R C (Source R D) S T).comp
      (dgFunctorEvaluationDG R C (Source R D) b.val)).onClosed).map f = 0 := by
  let E := (nullPreservingFunctorsεForget R C (Source R D) S T).comp
    (dgFunctorEvaluationDG R C (Source R D) b.val)
  apply (closedHomEquiv R (Source R D) _ _).injective
  rw [E.closedHomEquiv_map]
  apply Subtype.ext
  change ((E.map F G).f 0) (closedHomEquiv R _ F G f).val = 0
  have hε := quotientEpsilonHomι_compatible R C (Source R D) S T F G
    (𝟙 (quotientEpsilonHom R C (Source R D) S T F G))
  rw [Category.id_comp] at hε
  exact quotientEpsilonCellParameter_component_zero R C D S T F G _ hε b 0
    (closedHomEquiv R _ F G f).val (Or.inr h)

/-- ε 関手圏で H⁰ 同型な対象は、各 null 対象で実際に同じ cell 対象を持つ。 -/
lemma quotientEpsilonCell_obj_eq_of_homotopyIso [Nontrivial R] (b : S)
    (F G : NullPreservingFunctorsε R C (Source R D) S T)
    (e : (toHomotopy R _).obj (ForgetEnrichment.of (Complex R) F) ≅
      (toHomotopy R _).obj (ForgetEnrichment.of (Complex R) G)) :
    F.val.obj b.val = G.val.obj b.val := by
  by_contra h
  let E := quotientEpsilonCellHomotopyEvaluation R C D S T b
  let i := E.mapIso e
  obtain ⟨f, hf⟩ := (toHomotopy R _).map_surjective e.hom
  have hi : i.hom = 0 := by
    change E.map e.hom = 0
    rw [← hf]
    exact quotientEpsilonCellEvaluation_zero_of_obj_ne R C D S T b f h
  have hz : (𝟙 (E.obj ((toHomotopy R _).obj (ForgetEnrichment.of (Complex R) F)))) = 0 := by
    rw [← i.hom_inv_id, hi, zero_comp]
  have hu : (unitElement R (F.val.obj b.val)).val = 0 := by
    have he := congrArg (fun f => (closedHomEquiv R (Source R D) _ _ f).val) hz
    exact he
  exact dgCellResolution_unit_ne_zero R D (F.val.obj b.val) hu

/-- dg nerve 内の可逆比較も、null 対象の像を実際の対象として固定する。 -/
lemma quotientEpsilonCell_obj_eq_of_vertexIso [Nontrivial R] (b : S)
    (F G : NullPreservingFunctorsε R C (Source R D) S T)
    (e : VertexIso (X := dgNerve R (NullPreservingFunctorsε R C (Source R D) S T))
      (DGNerve.Simplex.vertex F) (DGNerve.Simplex.vertex G)) :
    F.val.obj b.val = G.val.obj b.val :=
  quotientEpsilonCell_obj_eq_of_homotopyIso R C D S T b F G (dgH0IsoOfVertexIso R _ e)

/-- native core 内の可逆比較は、各 null 対象で同じ実 cell 対象を要求する。 -/
lemma quotientEpsilonCell_obj_eq_of_coreVertexIso [Nontrivial R] (b : S)
    (F G : NullPreservingFunctorsε R C (Source R D) S T)
    (e : VertexIso
      (X := (quasicategoryCore (dgNerve R
        (NullPreservingFunctorsε R C (Source R D) S T)) : SSet))
      ⟨DGNerve.Simplex.vertex F, quasicategoryCore_vertex _⟩
      ⟨DGNerve.Simplex.vertex G, quasicategoryCore_vertex _⟩) :
    F.val.obj b.val = G.val.obj b.val :=
  quotientEpsilonCell_obj_eq_of_vertexIso R C D S T b F G
    (e.map (quasicategoryCore _).ι)

/-- ε core への全単体射は、入力の可逆比較の両端で null 像対象を変えられない。
頂点一致を等号でなく ε core 内の指定同型に弱めても、この条件は必要。 -/
lemma quotientEpsilonCell_nativeMap_obj_eq [Nontrivial R] (b : S)
    {X : SSet.{max u v w}} {x y : X.obj (Opposite.op ⦋0⦌)}
    (H : X ⟶ (quasicategoryCore (dgNerve R
      (NullPreservingFunctorsε R C (Source R D) S T)) : SSet))
    (F G : NullPreservingFunctorsε R C (Source R D) S T)
    (e : VertexIso (X := X) x y)
    (hF : VertexIso
      (H.app (Opposite.op ⦋0⦌) x)
      (⟨DGNerve.Simplex.vertex F, quasicategoryCore_vertex _⟩ :
        (quasicategoryCore (dgNerve R
          (NullPreservingFunctorsε R C (Source R D) S T)) : SSet).obj (Opposite.op ⦋0⦌)))
    (hG : VertexIso
      (H.app (Opposite.op ⦋0⦌) y)
      (⟨DGNerve.Simplex.vertex G, quasicategoryCore_vertex _⟩ :
        (quasicategoryCore (dgNerve R
          (NullPreservingFunctorsε R C (Source R D) S T)) : SSet).obj (Opposite.op ⦋0⦌))) :
    F.val.obj b.val = G.val.obj b.val :=
  quotientEpsilonCell_obj_eq_of_coreVertexIso R C D S T b F G
    (hF.symm ≪≫ e.map H ≪≫ hG)

end SerrePositivity.InfinityCategories
