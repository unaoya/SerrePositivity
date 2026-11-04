module

public import SerrePositivity.InfinityCategories.Stable.Quasicategory.CoconeFamilyTranspose
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierRecoveredInitialComparison
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierUniformCoconeImage

/-!
概要：同じ実前段分母と次辺族を保持し、元の商余錐への全図式比較を構成する。
方針：終端一次単体から共有経路を証明し、既存の全 attachment 比較を実適用する。
規約：共有経路を追加入力にせず、比較辺の前段・次辺制限を元の一次単体で保持する。
使われ方：完成境界回収の全余錐を元の商全族へ接続する。
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
variable {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}
  {h : IsVerdierSequence i q} {n : ℕ} {D : (Δ[n] : SSet.{u}) ⟶ B.obj}
  {z : B.obj _⦋0⦌} {K : SSet.{u}}
  {d : (verdierDenominatorOver i
    (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) : SSet.{u}) _⦋0⦌}
  {g : K ⟶ vertexFiber (verdierDenominatorSpanProjection i
    (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z) d}
  {f : K ⟶ intervalMappingSpace
    (q.hom.app (Opposite.op ⦋0⦌)
      (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))))
    (q.hom.app (Opposite.op ⦋0⦌) z)}


lemma verdierUniformCocone_source_prefix
    (W : K ⟶ (ihom (join (Δ[n] : SSet.{u}) Δ[0])).obj B.obj)
    {D' : (Δ[n] : SSet.{u}) ⟶ B.obj}
    (hWp : W ≫ (pre (joinInl (Δ[n] : SSet.{u}) Δ[0])).app B.obj =
      SSet.const (functorVertex D')) :
    (W ≫ (ihom (join (Δ[n] : SSet.{u}) Δ[0])).map q.hom) ≫
      (pre (joinInl (Δ[n] : SSet.{u}) Δ[0])).app C.obj =
      SSet.const (functorVertex (D' ≫ q.hom)) := by
  rw [Category.assoc, (pre (joinInl (Δ[n] : SSet.{u}) Δ[0])).naturality q.hom,
    ← Category.assoc, hWp, SSet.const_comp]
  rfl

/-- 保存済み K 全族の次辺は、同じ始端分数二胞体の下辺に厳密に一致する。 -/
lemma verdierUniformCocone_source_last
    (W : K ⟶ (ihom (join (Δ[n] : SSet.{u}) Δ[0])).obj B.obj)
    (hWn : W ≫ (pre (joinMap (simplexLastPoint n) (𝟙 Δ[0]))).app B.obj =
      verdierSpanFamilyNumeratorArrow i
        (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z
        (g ≫ vertexFiberι (verdierDenominatorSpanProjection i
          (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z) d) ≫
        (pre (joinStdSimplexIso 0 0).hom).app B.obj) :
    (W ≫ (ihom (join (Δ[n] : SSet.{u}) Δ[0])).map q.hom) ≫
      (pre (joinMap (simplexLastPoint n) (𝟙 Δ[0]))).app C.obj =
      (g ≫ vertexFiberι (verdierDenominatorSpanProjection i
        (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z) d ≫
        verdierSpanEvaluationSquare h
          (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z ≫
        (pre squareBottomEdge).app C.obj) ≫ (pre (joinStdSimplexIso 0 0).hom).app C.obj := by
  rw [Category.assoc, (pre (joinMap (simplexLastPoint n) (𝟙 Δ[0]))).naturality q.hom,
    ← Category.assoc, hWn]
  have he := congrArg (fun v => g ≫ vertexFiberι (verdierDenominatorSpanProjection i
      (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z) d ≫
      v ≫ (pre (joinStdSimplexIso 0 0).hom).app C.obj)
    (verdierSpanEvaluationSquare_bottom h
      (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z)
  simp only [Category.assoc] at he ⊢
  rw [he]
  simp only [verdierSpanFamilyNumeratorArrow, Category.assoc]
  rw [(pre (joinStdSimplexIso 0 0).hom).naturality q.hom]

variable {L : SSet.Homotopy
    (g ≫ vertexFiberι (verdierDenominatorSpanProjection i
      (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z) d ≫
      verdierDenominatorSpanCanonicalComparison i
        (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z ≫
      fixedFractionEvaluation q.hom (weakEquivalences i) h.inverts
        (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z) f}
  {G : K ⟶ (ihom (join (Δ[n] : SSet.{u}) Δ[0])).obj C.obj}


local notation "J" => join (Δ[n] : SSet) Δ[0]

/-- 指定された実前段辺と次辺比較を、同じ共有経路から全図式の実可逆辺へ貼る。 -/
lemma exists_verdierUniformCoconeInitialComparison
    {D' : (Δ[n] : SSet.{u}) ⟶ B.obj}
    (t : Truncated.Edge (X := (truncation 2).obj ((ihom Δ[n]).obj B.obj))
      (functorVertex D') (functorVertex D))
    (ht : t.edge ∈ (relativeFirstRowSimplex q n).obj (Opposite.op ⦋1⦌))
    (hlast : (evaluateFunctorAt (Y := B.obj)
      (stdSimplex.obj₀Equiv.symm (Fin.last n))).app (Opposite.op ⦋1⦌) t.edge =
        (roofPointSliceVertexEdge (SSet.yonedaEquiv.symm
          (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n)))) d.val).edge)
    (W : K ⟶ (ihom J).obj B.obj)
    (hWp : W ≫ (pre (joinInl (Δ[n] : SSet.{u}) Δ[0])).app B.obj =
      SSet.const (functorVertex D'))
    (hWn : W ≫ (pre (joinMap (simplexLastPoint n) (𝟙 Δ[0]))).app B.obj =
      verdierSpanFamilyNumeratorArrow i
        (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z
        (g ≫ vertexFiberι (verdierDenominatorSpanProjection i
          (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z) d) ≫
        (pre (joinStdSimplexIso 0 0).hom).app B.obj)
    (U : VerdierUniformCoconeImage (h := h) L G) :
    ∃ l : Truncated.Edge (X := (truncation 2).obj ((ihom J).obj ((ihom K).obj C.obj)))
        (functorVertex (internalHomFlipHomEquiv K J C.obj (W ≫ (ihom J).map q.hom)))
        (functorVertex (internalHomFlipHomEquiv K J C.obj U.initialFamily)),
      IsInvertibleEdge (X := (ihom J).obj ((ihom K).obj C.obj)) l ∧
      ((pre (joinInl (Δ[n] : SSet.{u}) Δ[0])).app ((ihom K).obj C.obj)).app
        (Opposite.op ⦋1⦌) l.edge = (spanConstantPrefixEdge K q.hom t).edge ∧
      ((pre (joinMap (simplexLastPoint n) (𝟙 Δ[0]))).app ((ihom K).obj C.obj)).app
        (Opposite.op ⦋1⦌) l.edge =
      (((functorEdgeOfSimplicialHomotopy (verdierUniformSpanFractionHomotopy h
        (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z d g)).map
          ((truncation 2).map ((pre (joinStdSimplexIso 0 0).hom).app
            ((ihom K).obj C.obj)))).edge) := by
  have hai : IsInvertibleEdge (X := (ihom (Δ[n] : SSet.{u})).obj ((ihom K).obj C.obj))
      (spanConstantPrefixEdge K q.hom t).toTruncated := by
    apply spanConstantPrefixEdge_isInvertible
    change IsIso (simplexDenominatorImageIso q t ht).hom
    infer_instance
  have hshared := verdierUniformSpanPrefixPath h
    (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z d g t hlast
  let F := internalHomFlipHomEquiv K J C.obj (W ≫ (ihom J).map q.hom)
  let T := internalHomFlipHomEquiv K J C.obj U.initialFamily
  let A₀ := spanConstantPrefixEdge K q.hom t
  let B₀ := (functorEdgeOfSimplicialHomotopy (verdierUniformSpanFractionHomotopy h
    (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z d g)).map
    ((truncation 2).map ((pre (joinStdSimplexIso 0 0).hom).app ((ihom K).obj C.obj)))
  have hFp : joinInl (Δ[n] : SSet.{u}) Δ[0] ≫ F =
      (D' ≫ q.hom) ≫
        constantFunctorMap K C.obj := by
    dsimp only [F]
    rw [← internalHomFlipHomEquiv_pre_app,
      verdierUniformCocone_source_prefix (q := q) W hWp, spanInternalHomFlip_const]
    rfl
  have hTp : joinInl (Δ[n] : SSet.{u}) Δ[0] ≫ T =
      (D ≫ q.hom) ≫ constantFunctorMap K C.obj := by
    dsimp only [T]
    rw [← internalHomFlipHomEquiv_pre_app, U.initialFamily_prefix, spanInternalHomFlip_const]
    rfl
  let A' := A₀.ofEq (congrArg functorVertex hFp).symm (congrArg functorVertex hTp).symm
  let V := g ≫ vertexFiberι (verdierDenominatorSpanProjection i
    (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z) d ≫
    verdierSpanEvaluationSquare h
      (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z
  have hFB : joinMap (simplexLastPoint n) (𝟙 Δ[0]) ≫ F =
      (joinStdSimplexIso 0 0).hom ≫
        internalHomFlipHomEquiv K Δ[1] C.obj (V ≫ (pre squareBottomEdge).app C.obj) := by
    dsimp only [F]
    rw [← internalHomFlipHomEquiv_pre_app,
      verdierUniformCocone_source_last (h := h) (D := D) (d := d) (g := g) W hWn,
      internalHomFlipHomEquiv_pre_app]
    simp only [V, Category.assoc]
  have hTB : joinMap (simplexLastPoint n) (𝟙 Δ[0]) ≫ T =
      (joinStdSimplexIso 0 0).hom ≫
        internalHomFlipHomEquiv K Δ[1] C.obj (V ≫ (pre squareTopEdge).app C.obj) := by
    dsimp only [T]
    rw [← internalHomFlipHomEquiv_pre_app, U.initialFamily_last,
      internalHomFlipHomEquiv_pre_app]
    simp only [V, Category.assoc]
  have hBs : functorVertex ((joinStdSimplexIso 0 0).hom ≫
      internalHomFlipHomEquiv K Δ[1] C.obj (V ≫ (pre squareBottomEdge).app C.obj)) =
      functorVertex (joinMap (simplexLastPoint n) (𝟙 Δ[0]) ≫ F) := by rw [hFB]
  have hBt : functorVertex ((joinStdSimplexIso 0 0).hom ≫
      internalHomFlipHomEquiv K Δ[1] C.obj (V ≫ (pre squareTopEdge).app C.obj)) =
      functorVertex (joinMap (simplexLastPoint n) (𝟙 Δ[0]) ≫ T) := by rw [hTB]
  let B' := (SSet.Edge.ofTruncated B₀).ofEq hBs hBt
  have hab : SSet.yonedaEquiv.symm A'.edge ≫
      (pre (simplexLastPoint n)).app ((ihom K).obj C.obj) =
      SSet.yonedaEquiv.symm B'.edge ≫
        (pre (joinInl (Δ[0] : SSet.{u}) Δ[0])).app ((ihom K).obj C.obj) := by
    change SSet.yonedaEquiv.symm A₀.edge ≫
      (pre (simplexLastPoint n)).app ((ihom K).obj C.obj) =
      SSet.yonedaEquiv.symm (((pre (joinStdSimplexIso 0 0).hom).app ((ihom K).obj C.obj)).app
        (Opposite.op ⦋1⦌) (functorEdgeOfSimplicialHomotopy (verdierUniformSpanFractionHomotopy h
    (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z d g)).edge) ≫
        (pre (joinInl (Δ[0] : SSet.{u}) Δ[0])).app ((ihom K).obj C.obj)
    rw [← SSet.yonedaEquiv_symm_comp, Category.assoc, ← NatTrans.comp_app,
      ← pre_map, joinStdSimplexIso_zero_inl]
    exact hshared.symm
  have hb₀ : IsInvertibleEdge (functorEdgeOfSimplicialHomotopy (verdierUniformSpanFractionHomotopy h
    (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z d g)) := by
    have hi := fractionFamilyComparison_isInvertible q.hom (weakEquivalences i) h.inverts
      (g ≫ vertexFiberι (verdierDenominatorSpanProjection i
        (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z) d ≫
        verdierDenominatorSpanCanonicalComparison i
          (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z ≫
        fixedMarkedSpanInclusion B.obj (weakEquivalences i)
          (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z)
    apply (isInvertibleEdge_congr (e := functorEdgeOfSimplicialHomotopy
      (verdierUniformSpanFractionHomotopy h
    (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z d g))
      (f := functorEdgeOfSimplicialHomotopy (spanSquareFamilyHomotopy
        ((g ≫ vertexFiberι (verdierDenominatorSpanProjection i
          (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z) d ≫
          verdierDenominatorSpanCanonicalComparison i
            (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z ≫
          fixedMarkedSpanInclusion B.obj (weakEquivalences i)
            (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z) ≫
          fractionEvaluationSquare q.hom (weakEquivalences i) h.inverts))) rfl).mpr hi
  obtain ⟨l, hlp, hln⟩ := exists_simplexAttachmentComparison n F T A'.toTruncated
    B'.toTruncated hab
  have hai' : IsInvertibleEdge (X := (ihom (Δ[n] : SSet.{u})).obj ((ihom K).obj C.obj))
      A'.toTruncated :=
    (isInvertibleEdge_congr (e := A₀.toTruncated) (f := A'.toTruncated) rfl).mp hai
  have hbi : IsInvertibleEdge
      (X := (ihom (join (Δ[0] : SSet.{u}) Δ[0])).obj ((ihom K).obj C.obj)) B'.toTruncated :=
    (isInvertibleEdge_congr (e := B₀) (f := B'.toTruncated) rfl).mp
      (hb₀.map ((pre (joinStdSimplexIso 0 0).hom).app ((ihom K).obj C.obj)))
  have hli := simplexAttachmentComparison_isInvertible n l
    ((isInvertibleEdge_congr hlp).mpr hai') ((isInvertibleEdge_congr hln).mpr hbi)
  exact ⟨l, hli, hlp, hln⟩

end SerrePositivity.KST.LocalizingInvariants
