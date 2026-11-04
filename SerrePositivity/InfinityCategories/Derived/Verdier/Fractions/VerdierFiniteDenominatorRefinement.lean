module

public import SerrePositivity.KST.LocalizingInvariants.ExactFiniteLimitPreservation
public import SerrePositivity.KST.LocalizingInvariants.VerdierSimplexDenominators
public import SerrePositivity.InfinityCategories.F1B.Cones.CoconeShapeAdjunction
public import SerrePositivity.InfinityCategories.HomotopyLimits.JoinVertexSummands
public import SerrePositivity.InfinityCategories.Derived.EvaluationLimitCone
public import SerrePositivity.InfinityCategories.F1B.FunctorIsoConstantEdges
public import SerrePositivity.InfinityCategories.Core.CatInfinity.NativeConeLeg
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.MappingSpacePrismPoint
public import SerrePositivity.InfinityCategories.F1B.Homotopy.WeakReverseHomotopy
public import SerrePositivity.InfinityCategories.F1B.HomotopyPrecompVertex
public import SerrePositivity.InfinityCategories.HomotopyLimits.CoconeVertexTriangles
public import SerrePositivity.KST.LocalizingInvariants.FixedSpanApexDenominators
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.FiniteJoin

/-!
概要：共通終点へ向かう実分母の有限図式を、全図式を保持して共通精密化する。
方針：終点を含む有限拡大図式の実極限を取り、その同じ各脚の分母性を商で反映する。
規約：有限頂点族だけへの弱化や、図式の高次整合性の追加入力を使わない。
使われ方：完成分数族からの実分母族の回収に必要な有限同時精密化。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.Fibration
namespace SerrePositivity.KST.LocalizingInvariants

private lemma coconeShapeContraction_left (K : SSet.{u}) :
    (joinInl K (Δ[0] : SSet.{u}) ▷ (Δ[1] : SSet.{u})) ≫
      (F1B.coconeShapeContraction K).h =
        (β_ K (Δ[1] : SSet.{u})).hom ≫ rightMappingSpacePrism K := by
  have h : (joinInl K (Δ[0] : SSet.{u}) ▷ (Δ[1] : SSet.{u})) ≫
      (β_ (join K (Δ[0] : SSet.{u})) (Δ[1] : SSet.{u})).hom =
        (β_ K (Δ[1] : SSet.{u})).hom ≫ (Δ[1] ◁ joinInl K Δ[0]) := rfl
  change _ ≫ (_ ≫ (joinTensorLeft Δ[1] K Δ[0] ≫ F1B.coneContractionCore K)) = _
  rw [← Category.assoc, h, Category.assoc, ← Category.assoc (Δ[1] ◁ _),
    joinTensorLeft_inl, F1B.coneContractionCore_inl]

private lemma coconeShape_isWeaklyContractible (K : SSet.{u}) :
    IsWeaklyContractible (join K (Δ[0] : SSet.{u})) := by
  let z := (joinInr K (Δ[0] : SSet.{u})).app (Opposite.op ⦋0⦌)
    (stdSimplex.obj₀Equiv.symm (0 : Fin 1))
  let g : (⊤_ SSet.{u}) ⟶ join K Δ[0] := SSet.const z
  change IsWeakHomotopyEquivalence (terminal.from (join K (Δ[0] : SSet.{u})))
  apply isWeakHomotopyEquivalence_of_reverseHomotopyInverse.{u}
    (terminal.from (join K (Δ[0] : SSet.{u}))) g
  · have he : terminal.from (join K (Δ[0] : SSet.{u})) ≫ g =
        stdSimplex.isTerminalObj₀.from (join K Δ[0]) ≫ joinInr K Δ[0] := by
      dsimp only [g]
      rw [SSet.comp_const]
      change SSet.const z = SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) ≫ _
      rw [SSet.const_comp]
    rw [he]
    exact F1B.coconeShapeContraction K
  · have he : g ≫ terminal.from (join K (Δ[0] : SSet.{u})) = 𝟙 _ :=
      terminal.hom_ext _ _
    rw [he]
    exact SSet.RelativeMorphism.Homotopy.refl (SSet.RelativeMorphism.botEquiv.symm (𝟙 _))

private def augmentedCoconeHomotopy {K X : SSet.{u}} {p : K ⟶ X}
    (t : JoinCocone p) : SSet.Homotopy t.val (SSet.const t.vertex) :=
  stableHomotopyRetarget (functorHomotopyPostcomp (F1B.coconeShapeContraction K) t.val)
    (Category.id_comp _) (by
      change (stdSimplex.isTerminalObj₀.from (join K Δ[0]) ≫ joinInr K Δ[0]) ≫
        t.val = SSet.const t.vertex
      rw [Category.assoc]
      change SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) ≫
        (joinInr K Δ[0] ≫ t.val) = SSet.const t.vertex
      have he : joinInr K Δ[0] ≫ t.val = SSet.yonedaEquiv.symm t.vertex :=
        (SSet.yonedaEquiv.symm_apply_apply _).symm
      rw [he]
      exact const_point_comp_yoneda _)

private lemma augmentedCoconeHomotopy_left_edge {K X : SSet.{u}} {p : K ⟶ X}
    (t : JoinCocone p) (a : K _⦋0⦌) :
    (simplicialHomotopyVertexEdge (augmentedCoconeHomotopy t)
      ((joinInl K Δ[0]).app (Opposite.op ⦋0⦌) a)).edge =
        (t.leg (SSet.yonedaEquiv.symm a)).edge := by
  let j : (Δ[1] : SSet.{u}) ⟶ K ⊗ Δ[1] := lift (SSet.const a) (𝟙 _)
  have h : (joinInl K (Δ[0] : SSet.{u}) ▷ (Δ[1] : SSet.{u})) ≫
      (augmentedCoconeHomotopy t).h =
        (β_ K (Δ[1] : SSet.{u})).hom ≫ rightMappingSpacePrism K ≫ t.val := by
    change _ ≫ ((F1B.coconeShapeContraction K).h ≫ t.val) = _
    rw [← Category.assoc, coconeShapeContraction_left, Category.assoc]
  have hj : j ≫ (β_ K (Δ[1] : SSet.{u})).hom =
      pointTensorSection (Δ[1] : SSet.{u}) ≫ (Δ[1] ◁ SSet.yonedaEquiv.symm a) := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    rfl
  have hh := congrArg (fun f => SSet.yonedaEquiv (j ≫ f)) h
  rw [← Category.assoc j (β_ K (Δ[1] : SSet.{u})).hom
      (rightMappingSpacePrism K ≫ t.val), hj, Category.assoc,
    ← Category.assoc (Δ[1] ◁ _), rightMappingSpacePrism_naturality,
    rightMappingSpacePrism_point] at hh
  have hs : pointTensorSection (Δ[1] : SSet.{u}) ≫ fst Δ[1] Δ[0] = 𝟙 _ := rfl
  simp only [Category.assoc] at hh
  rw [← Category.assoc (pointTensorSection _), hs, Category.id_comp] at hh
  have hi : SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})) = homotopyIntervalEdge.edge := by
    apply SSet.stdSimplex.ext
    intro k
    fin_cases k <;> rfl
  change (augmentedCoconeHomotopy t).h.app (Opposite.op ⦋1⦌)
    ((joinInl K Δ[0]).app (Opposite.op ⦋1⦌) (PinchedHom.constant a 1),
      SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u}))) = _ at hh
  rw [hi] at hh
  have hid := congrArg Truncated.Edge.edge
    (Truncated.Edge.map_id a ((truncation 2).map (joinInl K (Δ[0] : SSet.{u}))))
  change (joinInl K (Δ[0] : SSet.{u})).app (Opposite.op ⦋1⦌)
    (Truncated.Edge.id (X := (truncation 2).obj K) a).edge =
      (Truncated.Edge.id (X := (truncation 2).obj (join K (Δ[0] : SSet.{u})))
        ((joinInl K Δ[0]).app (Opposite.op ⦋0⦌) a)).edge at hid
  rw [pinchedConstant_one, hid] at hh
  exact hh

private lemma augmentedCoconeHomotopy_invertible {K X : SSet.{u}} [Quasicategory X]
    {p : K ⟶ X} (t : JoinCocone p)
    (ht : ∀ a : K _⦋0⦌, IsInvertibleEdge (t.leg (SSet.yonedaEquiv.symm a)))
    (v : (join K (Δ[0] : SSet.{u})) _⦋0⦌) :
    IsInvertibleEdge (simplicialHomotopyVertexEdge (augmentedCoconeHomotopy t) v).toTruncated := by
  rcases HomotopyLimits.joinVertexSummands v with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · exact (isInvertibleEdge_congr (augmentedCoconeHomotopy_left_edge t a)).mpr (ht a)
  · let H := augmentedCoconeHomotopy t
    have hp : (joinInr K (Δ[0] : SSet.{u})) ≫ t.val = SSet.const t.vertex := by
      have he : joinInr K Δ[0] ≫ t.val = SSet.yonedaEquiv.symm t.vertex :=
        (SSet.yonedaEquiv.symm_apply_apply _).symm
      rw [he, SSet.yonedaEquiv_symm_zero]
    have hh : (functorHomotopyPrecomp H (joinInr K (Δ[0] : SSet.{u}))).h =
        SSet.const t.vertex := by
      change (joinInr K (Δ[0] : SSet.{u}) ▷ (Δ[1] : SSet.{u})) ≫
        ((F1B.coconeShapeContraction K).h ≫ t.val) = _
      rw [← Category.assoc, F1B.coconeShapeContraction_right, Category.assoc,
        hp, SSet.comp_const]
    let s : ((Δ[0] : SSet.{u}) ⊗ Δ[1]) _⦋1⦌ :=
      ((Truncated.Edge.id (X := (truncation 2).obj (Δ[0] : SSet.{u})) b).edge,
        homotopyIntervalEdge.edge)
    have hi := invertsEdges_const ((Δ[0] : SSet.{u}) ⊗ Δ[1]) X t.vertex Set.univ
      (a := s) (Set.mem_univ s)
    have he : (simplicialHomotopyVertexEdge H
        ((joinInr K Δ[0]).app (Opposite.op ⦋0⦌) b)).edge =
        ((edgeOfSimplex s).map ((truncation 2).map (SSet.const t.vertex :
          ((Δ[0] : SSet.{u}) ⊗ Δ[1]) ⟶ X))).edge := by
      rw [← simplicialHomotopyVertexEdge_precomp_edge]
      exact congrArg (fun f : ((Δ[0] : SSet.{u}) ⊗ Δ[1]) ⟶ X =>
        f.app (Opposite.op ⦋1⦌) s) hh
    exact (isInvertibleEdge_congr he).mpr hi

/-- 可逆な有限分母余錐を終点まで含めて極限にすると、同じ全脚が再び実分母になる。 -/
lemma exists_verdierFiniteDenominatorRefinement
    {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}
    (h : IsVerdierSequence i q) {K : SSet.{u}} [K.Finite]
    {p : K ⟶ B.obj} (t : JoinCocone p)
    (ht : ∀ a : K _⦋0⦌, (t.leg (SSet.yonedaEquiv.symm a)).edge ∈ weakEquivalences i) :
    ∃ c : JoinCone t.val, IsLimitCone c ∧ InvertsEdges (c.val ≫ q.hom) Set.univ ∧
      ∀ k : (join K (Δ[0] : SSet.{u})) _⦋0⦌,
        (F2.nativeConeLeg c k).edge ∈ weakEquivalences i := by
  let : HasFiniteLimits B.obj := hasFiniteLimits_of_isStable B.obj
  obtain ⟨c, hc⟩ := HasFiniteLimits.hasLimit t.val
  let tq := F1B.kanPostcomposeCocone q.hom t
  have hq : ∀ a : K _⦋0⦌, IsInvertibleEdge (tq.leg (SSet.yonedaEquiv.symm a)) := by
    intro a
    have hi := (mem_weakEquivalences_iff_invertible h
      (t.leg (SSet.yonedaEquiv.symm a))).mp (ht a)
    apply (isInvertibleEdge_congr (e := (t.leg (SSet.yonedaEquiv.symm a)).map
      ((truncation 2).map q.hom)) (f := tq.leg (SSet.yonedaEquiv.symm a)) ?_).mp hi
    change q.hom.app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv _) = SSet.yonedaEquiv _
    rw [← SSet.yonedaEquiv_comp]
    rfl
  let H := augmentedCoconeHomotopy tq
  let r := evaluationLimitConeTransport (coconeShape_isWeaklyContractible K)
    tq.vertex H (augmentedCoconeHomotopy_invertible tq hq)
  have hqc := exactMap_map_isLimit_finite q c hc
  have e : FunctorIso (mapJoinCone q.hom c).val (SSet.const tq.vertex) :=
    coneFunctorIsoOfVertexIso _ r.cone (limitConeIso _ _ hqc r.isLimit) ≪≫
      functorIsoOfPointwiseInvertibleHomotopy r.homotopy r.vertical_isInvertible
  refine ⟨c, hc, (invertsEdges_functorIso_iff e Set.univ).mpr
    (invertsEdges_const _ _ _ Set.univ), ?_⟩
  intro k
  apply (mem_weakEquivalences_iff_invertible h (F2.nativeConeLeg c k)).mpr
  exact (isInvertibleEdge_congr (e := (F2.nativeConeLeg c k).map
    ((truncation 2).map q.hom)) (f := (F2.coneDomainLeg k).map
      ((truncation 2).map (mapJoinCone q.hom c).val)) rfl).mpr
        (functorIso_const_map_isInvertible tq.vertex e (F2.coneDomainLeg k))

end SerrePositivity.KST.LocalizingInvariants
