module

public import SerrePositivity.InfinityCategories.Stable.Quasicategory.CoconeFamilyTranspose
public import SerrePositivity.KST.LocalizingInvariants.CoconeFamilyTranspose
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierSimplexCommonDenominatorFamily
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierSpanFamilyComposition

/-!
概要：元の共通分母による前段精密化と実次辺族を、商の全余錐族へ指定経路付きで比較する。
方針：終端脚を回収実辺へ照合し、証明済みの分数合成整合で共有経路付き貼合せを実適用する。
規約：合成整合も共有経路も新たな入力にせず、元の前段比較の一次単体を保持する。
使われ方：c5 の全次数の第一行単体商比較に向けた全パラメータの比較構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Fibration
namespace SerrePositivity.KST.LocalizingInvariants

private lemma spanParametricCompArrowCongr {T : Type*} [Category* T] {a b c a' b' c' : T}
    {f : a ⟶ b} {g : b ⟶ c} {f' : a' ⟶ b'} {g' : b' ⟶ c'}
    (hf : Arrow.mk f = Arrow.mk f') (hg : Arrow.mk g = Arrow.mk g') :
    Arrow.mk (f ≫ g) = Arrow.mk (f' ≫ g') := by
  obtain ⟨rfl, rfl, hf⟩ := (Arrow.mk_eq_mk_iff _ _).mp hf
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hf
  subst f'
  obtain ⟨_, rfl, hg⟩ := (Arrow.mk_eq_mk_iff _ _).mp hg
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hg
  subst g'
  rfl

/-- 元の共通実分母の前段比較を保ち、商の全余錐族への全比較を構成する。 -/
lemma exists_verdierSimplexParametricComparison
    {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}
    (h : IsVerdierSequence i q) {n : ℕ} (D D' : (Δ[n] : SSet.{u}) ⟶ B.obj)
    (z : B.obj _⦋0⦌)
    (t : Truncated.Edge (X := (truncation 2).obj ((ihom (Δ[n] : SSet.{u})).obj B.obj))
      (functorVertex D') (functorVertex D))
    (ht : t.edge ∈ (relativeFirstRowSimplex q n).obj (Opposite.op ⦋1⦌))
    (d : (verdierDenominatorOver i
      (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) : SSet.{u}) _⦋0⦌)
    (hlast : (evaluateFunctorAt (Y := B.obj)
      (stdSimplex.obj₀Equiv.symm (Fin.last n))).app (Opposite.op ⦋1⦌) t.edge =
      (roofPointSliceVertexEdge (SSet.yonedaEquiv.symm
        (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n)))) d.val).edge)
    {K : SSet.{u}}
    (g : K ⟶ vertexFiber (verdierDenominatorSpanProjection i
      (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z) d)
    (F : K ⟶ (ihom (join (Δ[n] : SSet.{u}) Δ[0])).obj B.obj)
    (hF : F ≫ (pre (joinInl (Δ[n] : SSet.{u}) Δ[0])).app B.obj =
      SSet.const (functorVertex D'))
    (hFe : F ≫ (pre (joinMap (simplexLastPoint n) (𝟙 Δ[0]))).app B.obj =
      g ≫ verdierDenominatorSpanFiberArrow i
        (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z d ≫
        (pre (joinStdSimplexIso 0 0).hom).app B.obj)
    (G : K ⟶ (ihom (join (Δ[n] : SSet.{u}) Δ[0])).obj C.obj)
    (hG : G ≫ (pre (joinInl (Δ[n] : SSet.{u}) Δ[0])).app C.obj =
      SSet.const (functorVertex (D ≫ q.hom)))
    (f : K ⟶ intervalMappingSpace
      (q.hom.app (Opposite.op ⦋0⦌)
        (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))))
      (q.hom.app (Opposite.op ⦋0⦌) z))
    (hGe : G ≫ (pre (joinMap (simplexLastPoint n) (𝟙 Δ[0]))).app C.obj =
      f ≫ vertexFiberι ((pre (boundary 1).ι).app C.obj)
        (functorVertex (intervalMappingBoundary
          (q.hom.app (Opposite.op ⦋0⦌)
            (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))))
          (q.hom.app (Opposite.op ⦋0⦌) z))) ≫
      (pre (joinStdSimplexIso 0 0).hom).app C.obj)
    (e : FunctorIso (verdierSpanEvaluatedMapping h
      (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z d g) f) :
    ∃ l : Truncated.Edge
        (X := (truncation 2).obj ((ihom (join (Δ[n] : SSet.{u}) Δ[0])).obj ((ihom K).obj C.obj)))
        (functorVertex (internalHomFlipHomEquiv K (join (Δ[n] : SSet.{u}) Δ[0]) C.obj
          (F ≫ (ihom (join (Δ[n] : SSet.{u}) Δ[0])).map q.hom)))
        (functorVertex (internalHomFlipHomEquiv K (join (Δ[n] : SSet.{u}) Δ[0]) C.obj G)),
      IsInvertibleEdge l ∧
      ((pre (joinInl (Δ[n] : SSet.{u}) Δ[0])).app ((ihom K).obj C.obj)).app
        (Opposite.op ⦋1⦌) l.edge = (spanConstantPrefixEdge K q.hom t).edge ∧
      SSet.yonedaEquiv.symm l.edge ≫ (pre (joinInr (Δ[n] : SSet.{u}) Δ[0])).app
        ((ihom K).obj C.obj) = curry (snd (Δ[0] : SSet.{u}) Δ[1] ≫
          SSet.const (functorVertex (SSet.const (q.hom.app (Opposite.op ⦋0⦌) z) : K ⟶ C.obj))) ∧
      Nonempty (FunctorIso (F ≫ (ihom (join (Δ[n] : SSet.{u}) Δ[0])).map q.hom) G) := by
  let x := D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))
  let FQ := F ≫ (ihom (join (Δ[n] : SSet.{u}) Δ[0])).map q.hom
  have hFQ : FQ ≫ (pre (joinInl (Δ[n] : SSet.{u}) Δ[0])).app C.obj =
      SSet.const (functorVertex (D' ≫ q.hom)) := by
    dsimp only [FQ]
    rw [Category.assoc, (pre (joinInl (Δ[n] : SSet.{u}) Δ[0])).naturality q.hom,
      ← Category.assoc, hF, SSet.const_comp]
    rfl
  have hFQe : FQ ≫ (pre (joinMap (simplexLastPoint n) (𝟙 Δ[0]))).app C.obj =
      verdierSpanMappedNumeratorFamily i q x z d g ≫
        (pre (joinStdSimplexIso 0 0).hom).app C.obj := by
    dsimp only [FQ]
    rw [Category.assoc, (pre (joinMap (simplexLastPoint n) (𝟙 Δ[0]))).naturality q.hom,
      ← Category.assoc, hFe]
    simp only [Category.assoc]
    rw [← (pre (joinStdSimplexIso 0 0).hom).naturality q.hom]
    rfl
  let c := spanCoconeFamilyTranspose (D' ≫ q.hom) FQ hFQ
  let b := spanCoconeFamilyTranspose (D ≫ q.hom) G hG
  let k := SSet.yonedaEquiv (simplexLastPoint.{u} n)
  let cL := HomotopyLimits.coconeVertexLeg c k
  let bL := HomotopyLimits.coconeVertexLeg b k
  have hcL : cL.edge = (verdierSpanMappedNumeratorEdge i q x z d g).edge := by
    exact (spanCoconeFamilyTranspose_last_edge (D' ≫ q.hom) FQ hFQ _ hFQe).trans
      (verdierSpanMappedNumeratorEdge_edge i q x z d g).symm
  have hbL : bL.edge = (intervalMappingFamilyEdge f).edge := by
    exact spanCoconeFamilyTranspose_last_interval_edge (D ≫ q.hom) G hG f hGe
  let a := spanConstantPrefixEdge K q.hom t
  have hai : IsInvertibleEdge a.toTruncated := by
    apply spanConstantPrefixEdge_isInvertible
    change IsIso (simplexDenominatorImageIso q t ht).hom
    infer_instance
  have haL : (functorEdgeAt a k).edge = (verdierSpanMappedDenominatorEdge i q x d K).edge := by
    have he := spanConstantPrefixEdge_component K q.hom t k
    have hk : k = stdSimplex.obj₀Equiv.symm (Fin.last n) := Equiv.apply_symm_apply _ _
    rw [hk, hlast] at he
    have hd : SSet.yonedaEquiv (verdierSpanDenominatorDiagram i q x d) =
        (verdierSpanMappedDenominator i q x d).edge :=
      (congrArg SSet.yonedaEquiv (verdierSpanMappedDenominator_diagram i q x d)).symm.trans
        (Equiv.apply_symm_apply _ _)
    have hden := verdierSpanMappedDenominatorEdge_edge i q x d K
    rw [SSet.yonedaEquiv_comp, hd] at hden
    exact he.trans hden.symm
  let v := functorVertex (SSet.const (q.hom.app (Opposite.op ⦋0⦌) z) : K ⟶ C.obj)
  have hcv : c.vertex = v := by
    rw [← cL.tgt_eq, hcL]
    exact (verdierSpanMappedNumeratorEdge i q x z d g).tgt_eq
  have hbv : b.vertex = v := by
    rw [← bL.tgt_eq, hbL]
    exact (intervalMappingFamilyEdge f).tgt_eq
  let w := (SSet.Edge.id v).ofEq hcv.symm hbv.symm
  have hwi : IsInvertibleEdge w.toTruncated := by
    have hi : IsInvertibleEdge (Truncated.Edge.id
        (X := (truncation 2).obj ((ihom K).obj C.obj)) v) := by
      dsimp only [IsInvertibleEdge]
      rw [Truncated.HomotopyCategory.homMk_id]
      infer_instance
    exact (isInvertibleEdge_congr (e := w.toTruncated)
      (f := Truncated.Edge.id (X := (truncation 2).obj ((ihom K).obj C.obj)) v) rfl).mpr hi
  have hw := Truncated.HomotopyCategory.congr_arrowMk_homMk w.toTruncated
    (Truncated.Edge.id (X := (truncation 2).obj ((ihom K).obj C.obj)) v) rfl
  rw [Truncated.HomotopyCategory.homMk_id] at hw
  have hnum := Truncated.HomotopyCategory.congr_arrowMk_homMk _ _ hcL
  have htarget := Truncated.HomotopyCategory.congr_arrowMk_homMk _ _ hbL
  have hden := Truncated.HomotopyCategory.congr_arrowMk_homMk _ _ haL
  have hcomm : Truncated.HomotopyCategory.homMk cL.toTruncated ≫
      Truncated.HomotopyCategory.homMk w.toTruncated =
      Truncated.HomotopyCategory.homMk (functorEdgeAt a k).toTruncated ≫
        Truncated.HomotopyCategory.homMk bL.toTruncated := by
    apply (Arrow.mk_inj _ _).mp
    calc
      _ = Arrow.mk (Truncated.HomotopyCategory.homMk
          (verdierSpanMappedNumeratorEdge i q x z d g).toTruncated ≫ 𝟙 _) :=
        spanParametricCompArrowCongr hnum hw
      _ = Arrow.mk (Truncated.HomotopyCategory.homMk
          (verdierSpanMappedNumeratorEdge i q x z d g).toTruncated) := by rw [Category.comp_id]
      _ = Arrow.mk (Truncated.HomotopyCategory.homMk
          (verdierSpanMappedDenominatorEdge i q x d K).toTruncated ≫
          Truncated.HomotopyCategory.homMk (intervalMappingFamilyEdge f).toTruncated) :=
        congrArg Arrow.mk (verdierSpanRecoveredArrows_comp_of_comparison h x z d g f e)
      _ = _ := (spanParametricCompArrowCongr hden htarget).symm
  obtain ⟨l, hi, hp, hv⟩ := exists_simplexCoconeComparison c b a w hai hwi hcomm
  have ei : FunctorIso c.val b.val := by
    have := hi
    exact asIso (Truncated.HomotopyCategory.homMk l)
  have hwdiag : SSet.yonedaEquiv.symm w.edge = (SSet.const v : (Δ[1] : SSet.{u}) ⟶ _) := by
    apply SSet.yonedaEquiv.injective
    rw [Equiv.apply_symm_apply]
    exact (pinchedConstant_one v).symm
  rw [hwdiag] at hv
  exact ⟨l, hi, hp, hv, ⟨spanFunctorIsoUnflip ei⟩⟩

end SerrePositivity.KST.LocalizingInvariants
