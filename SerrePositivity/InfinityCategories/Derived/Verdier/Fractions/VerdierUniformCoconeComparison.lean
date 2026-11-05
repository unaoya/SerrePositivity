module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

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
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Fibration
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.InfinityCategories.Derived.Verdier.Fractions
open SerrePositivity.KST.LocalizingInvariants
variable {A B C : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap B C}
  {h : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.IsVerdierSequence i q} {n : ℕ} {D : (Δ[n] : SSet.{u}) ⟶ B.obj}
  {z : B.obj _⦋0⦌} {K : SSet.{u}}
  {d : (verdierDenominatorOver i
    (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) : SSet.{u}) _⦋0⦌}
  {g : K ⟶ vertexFiber (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanProjection i
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
    (hWn : W ≫ (pre (joinMap (_root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.simplexLastPoint n) (𝟙 Δ[0]))).app B.obj =
      _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanFamilyNumeratorArrow i
        (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z
        (g ≫ vertexFiberι (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanProjection i
          (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z) d) ≫
        (pre (joinStdSimplexIso 0 0).hom).app B.obj) :
    (W ≫ (ihom (join (Δ[n] : SSet.{u}) Δ[0])).map q.hom) ≫
      (pre (joinMap (_root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.simplexLastPoint n) (𝟙 Δ[0]))).app C.obj =
      (g ≫ vertexFiberι (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanProjection i
        (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z) d ≫
        _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanEvaluationSquare h
          (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z ≫
        (pre squareBottomEdge).app C.obj) ≫ (pre (joinStdSimplexIso 0 0).hom).app C.obj := by
  rw [Category.assoc, (pre (joinMap (_root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.simplexLastPoint n) (𝟙 Δ[0]))).naturality q.hom,
    ← Category.assoc, hWn]
  have he := congrArg (fun v => g ≫ vertexFiberι (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanProjection i
      (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z) d ≫
      v ≫ (pre (joinStdSimplexIso 0 0).hom).app C.obj)
    (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanEvaluationSquare_bottom h
      (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z)
  simp only [Category.assoc] at he ⊢
  rw [he]
  simp only [_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanFamilyNumeratorArrow, Category.assoc]
  rw [(pre (joinStdSimplexIso 0 0).hom).naturality q.hom]

variable {L : SSet.Homotopy
    (g ≫ vertexFiberι (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanProjection i
      (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z) d ≫
      _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanCanonicalComparison i
        (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z ≫
      fixedFractionEvaluation q.hom (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i) h.inverts
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
    (hWn : W ≫ (pre (joinMap (_root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.simplexLastPoint n) (𝟙 Δ[0]))).app B.obj =
      _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanFamilyNumeratorArrow i
        (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z
        (g ≫ vertexFiberι (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanProjection i
          (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z) d) ≫
        (pre (joinStdSimplexIso 0 0).hom).app B.obj)
    (U : _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierUniformCoconeImage (h := h) L G) :
    ∃ l : Truncated.Edge (X := (truncation 2).obj ((ihom J).obj ((ihom K).obj C.obj)))
        (functorVertex (internalHomFlipHomEquiv K J C.obj (W ≫ (ihom J).map q.hom)))
        (functorVertex (internalHomFlipHomEquiv K J C.obj U.initialFamily)),
      IsInvertibleEdge (X := (ihom J).obj ((ihom K).obj C.obj)) l ∧
      ((pre (joinInl (Δ[n] : SSet.{u}) Δ[0])).app ((ihom K).obj C.obj)).app
        (Opposite.op ⦋1⦌) l.edge = (_root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.spanConstantPrefixEdge K q.hom t).edge ∧
      ((pre (joinMap (_root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.simplexLastPoint n) (𝟙 Δ[0]))).app ((ihom K).obj C.obj)).app
        (Opposite.op ⦋1⦌) l.edge =
      (((functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierUniformSpanFractionHomotopy h
        (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z d g)).map
          ((truncation 2).map ((pre (joinStdSimplexIso 0 0).hom).app
            ((ihom K).obj C.obj)))).edge) := by
  have hai : IsInvertibleEdge (X := (ihom (Δ[n] : SSet.{u})).obj ((ihom K).obj C.obj))
      (_root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.spanConstantPrefixEdge K q.hom t).toTruncated := by
    apply _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.spanConstantPrefixEdge_isInvertible
    change IsIso (simplexDenominatorImageIso q t ht).hom
    infer_instance
  have hshared := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierUniformSpanPrefixPath h
    (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z d g t hlast
  let F := internalHomFlipHomEquiv K J C.obj (W ≫ (ihom J).map q.hom)
  let T := internalHomFlipHomEquiv K J C.obj U.initialFamily
  let A₀ := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.spanConstantPrefixEdge K q.hom t
  let B₀ := (functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierUniformSpanFractionHomotopy h
    (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z d g)).map
    ((truncation 2).map ((pre (joinStdSimplexIso 0 0).hom).app ((ihom K).obj C.obj)))
  have hFp : joinInl (Δ[n] : SSet.{u}) Δ[0] ≫ F =
      (D' ≫ q.hom) ≫
        constantFunctorMap K C.obj := by
    dsimp only [F]
    rw [← internalHomFlipHomEquiv_pre_app,
      _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierUniformCocone_source_prefix (q := q) W hWp, spanInternalHomFlip_const]
    rfl
  have hTp : joinInl (Δ[n] : SSet.{u}) Δ[0] ≫ T =
      (D ≫ q.hom) ≫ constantFunctorMap K C.obj := by
    dsimp only [T]
    rw [← internalHomFlipHomEquiv_pre_app, U.initialFamily_prefix, spanInternalHomFlip_const]
    rfl
  let A' := A₀.ofEq (congrArg functorVertex hFp).symm (congrArg functorVertex hTp).symm
  let V := g ≫ vertexFiberι (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanProjection i
    (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z) d ≫
    _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanEvaluationSquare h
      (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z
  have hFB : joinMap (_root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.simplexLastPoint n) (𝟙 Δ[0]) ≫ F =
      (joinStdSimplexIso 0 0).hom ≫
        internalHomFlipHomEquiv K Δ[1] C.obj (V ≫ (pre squareBottomEdge).app C.obj) := by
    dsimp only [F]
    rw [← internalHomFlipHomEquiv_pre_app,
      _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierUniformCocone_source_last (h := h) (D := D) (d := d) (g := g) W hWn,
      internalHomFlipHomEquiv_pre_app]
    simp only [V, Category.assoc]
  have hTB : joinMap (_root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.simplexLastPoint n) (𝟙 Δ[0]) ≫ T =
      (joinStdSimplexIso 0 0).hom ≫
        internalHomFlipHomEquiv K Δ[1] C.obj (V ≫ (pre squareTopEdge).app C.obj) := by
    dsimp only [T]
    rw [← internalHomFlipHomEquiv_pre_app, U.initialFamily_last,
      internalHomFlipHomEquiv_pre_app]
    simp only [V, Category.assoc]
  have hBs : functorVertex ((joinStdSimplexIso 0 0).hom ≫
      internalHomFlipHomEquiv K Δ[1] C.obj (V ≫ (pre squareBottomEdge).app C.obj)) =
      functorVertex (joinMap (_root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.simplexLastPoint n) (𝟙 Δ[0]) ≫ F) := by rw [hFB]
  have hBt : functorVertex ((joinStdSimplexIso 0 0).hom ≫
      internalHomFlipHomEquiv K Δ[1] C.obj (V ≫ (pre squareTopEdge).app C.obj)) =
      functorVertex (joinMap (_root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.simplexLastPoint n) (𝟙 Δ[0]) ≫ T) := by rw [hTB]
  let B' := (SSet.Edge.ofTruncated B₀).ofEq hBs hBt
  have hab : SSet.yonedaEquiv.symm A'.edge ≫
      (pre (_root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.simplexLastPoint n)).app ((ihom K).obj C.obj) =
      SSet.yonedaEquiv.symm B'.edge ≫
        (pre (joinInl (Δ[0] : SSet.{u}) Δ[0])).app ((ihom K).obj C.obj) := by
    change SSet.yonedaEquiv.symm A₀.edge ≫
      (pre (_root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.simplexLastPoint n)).app ((ihom K).obj C.obj) =
      SSet.yonedaEquiv.symm (((pre (joinStdSimplexIso 0 0).hom).app ((ihom K).obj C.obj)).app
        (Opposite.op ⦋1⦌) (functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierUniformSpanFractionHomotopy h
    (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z d g)).edge) ≫
        (pre (joinInl (Δ[0] : SSet.{u}) Δ[0])).app ((ihom K).obj C.obj)
    rw [← SSet.yonedaEquiv_symm_comp, Category.assoc, ← NatTrans.comp_app,
      ← pre_map, joinStdSimplexIso_zero_inl]
    exact hshared.symm
  have hb₀ : IsInvertibleEdge (functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierUniformSpanFractionHomotopy h
    (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z d g)) := by
    have hi := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionFamilyComparison_isInvertible q.hom (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i) h.inverts
      (g ≫ vertexFiberι (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanProjection i
        (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z) d ≫
        _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanCanonicalComparison i
          (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z ≫
        fixedMarkedSpanInclusion B.obj (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i)
          (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z)
    apply (isInvertibleEdge_congr (e := functorEdgeOfSimplicialHomotopy
      (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierUniformSpanFractionHomotopy h
    (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z d g))
      (f := functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.spanSquareFamilyHomotopy
        ((g ≫ vertexFiberι (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanProjection i
          (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z) d ≫
          _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanCanonicalComparison i
            (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z ≫
          fixedMarkedSpanInclusion B.obj (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i)
            (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z) ≫
          fractionEvaluationSquare q.hom (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i) h.inverts))) rfl).mpr hi
  obtain ⟨l, hlp, hln⟩ := _root_.SerrePositivity.InfinityCategories.Derived.Localization.exists_simplexAttachmentComparison n F T A'.toTruncated
    B'.toTruncated hab
  have hai' : IsInvertibleEdge (X := (ihom (Δ[n] : SSet.{u})).obj ((ihom K).obj C.obj))
      A'.toTruncated :=
    (isInvertibleEdge_congr (e := A₀.toTruncated) (f := A'.toTruncated) rfl).mp hai
  have hbi : IsInvertibleEdge
      (X := (ihom (join (Δ[0] : SSet.{u}) Δ[0])).obj ((ihom K).obj C.obj)) B'.toTruncated :=
    (isInvertibleEdge_congr (e := B₀) (f := B'.toTruncated) rfl).mp
      (hb₀.map ((pre (joinStdSimplexIso 0 0).hom).app ((ihom K).obj C.obj)))
  have hli := _root_.SerrePositivity.InfinityCategories.Derived.Localization.simplexAttachmentComparison_isInvertible n l
    ((isInvertibleEdge_congr hlp).mpr hai') ((isInvertibleEdge_congr hln).mpr hbi)
  exact ⟨l, hli, hlp, hln⟩

end SerrePositivity.InfinityCategories.Derived.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.exists_verdierUniformCoconeInitialComparison := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.exists_verdierUniformCoconeInitialComparison

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierUniformCocone_source_last := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierUniformCocone_source_last

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierUniformCocone_source_prefix := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierUniformCocone_source_prefix
