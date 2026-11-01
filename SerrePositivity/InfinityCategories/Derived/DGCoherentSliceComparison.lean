module
public import SerrePositivity.InfinityCategories.DoldKanComparison.CoherentHomRetraction
public import SerrePositivity.InfinityCategories.DoldKanComparison.CoherentHomSection
public import SerrePositivity.InfinityCategories.Core.Roof.RoofPinchedSlicePostcomp
public import SerrePositivity.InfinityCategories.F1B.Roof.RoofTargetFunctor

/-! # Dold–Kan 比較による実 Hom の slice 表示の厳密一致

概要：標準 Hom の片側逆を、元の実 slice と区間族の比較へ接続する。
方針：既存の全次数の等式を同じ写像のまま接続する。
規約：有限性・前三角性を仮定しない。使われ方：実屋根の四三角形の高次の族。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory CartesianMonoidalCategory DifferentialGraded
open DGNerve DoldKanComparison SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

/-- coherent 標準終点の点図式は、実 dg 頂点の点図式へ厳密に移る。 -/
lemma dgCoherentTargetPoint (y : D) :
    SSet.yonedaEquiv.symm (coherentNerveVertex (ForgetEnrichment.of (Complex A) y)) ≫
      coherentComparison (R := A) (D := D) =
        (SSet.yonedaEquiv (X := dgNerve A D)).symm (Simplex.vertex y) := by
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  rw [coherentNerveVertex_eq_vertex]
  exact coherentComparison_vertex (R := A) (D := D) y
/-- 比較関手による標準 coherent 終点の slice から実 dg slice への写像。 -/
def dgCoherentTargetSliceMap (y : D) :
    sliceOver (SSet.yonedaEquiv.symm (coherentNerveVertex (ForgetEnrichment.of (Complex A) y))) ⟶
      sliceOver ((SSet.yonedaEquiv (X := dgNerve A D)).symm (Simplex.vertex y)) :=
  sliceOverPostcomp _ (coherentComparison (R := A) (D := D)) ≫
    (eqToIso (congrArg sliceOver (dgCoherentTargetPoint A D y))).hom
/-- 標準 Hom の coherent 表示を比較で戻すと、元の実 pinched 同型に厳密に一致。 -/
lemma dgStandardHomToCoherentPinched_comp (x y : ClosedCategory A D) :
    standardHomToCoherentPinched (R := A) (D := D) x y ≫
      coherentPinchedComparison (R := A) (D := D) x y =
        (standardHomPinchedIso (R := A) (D := D) x y).hom := by
  have h := standardHomToCoherentPinched_comp (R := A) (D := D) x y
  have ht := congrArg (fun k => k ≫ (standardHomPinchedIso (R := A) (D := D) x y).hom) h
  rw [Category.assoc, coherentPinchedStandardComparison_comp (R := A) (D := D) x y,
    Category.id_comp] at ht
  exact ht
/-- 指定二対象の実 pinched Hom の標準実 target slice への包含。 -/
def dgPinchedHomSlice (x y : D) : DGNerve.pinchedHom A D x y ⟶
    sliceOver ((SSet.yonedaEquiv (X := dgNerve A D)).symm (Simplex.vertex y)) :=
  (pinchedHomSliceFiberIso (X := dgNerve A D)
    (Simplex.vertex (A := A) x) (Simplex.vertex (A := A) y)).hom ≫
    vertexFiberι (sliceOverProjection
      ((SSet.yonedaEquiv (X := dgNerve A D)).symm (Simplex.vertex y))) (Simplex.vertex x)
/-- 実 slice 比較は台の join 写像の後合成である。 -/
lemma dgCoherentTargetSliceMap_val (y : D) {n : SimplexCategoryᵒᵖ}
    (s : (sliceOver (SSet.yonedaEquiv.symm
      (coherentNerveVertex (ForgetEnrichment.of (Complex A) y)))).obj n) :
    ((dgCoherentTargetSliceMap A D y).app n s).val =
      s.val ≫ coherentComparison (R := A) (D := D) :=
  roofSliceTransport_val (dgCoherentTargetPoint A D y) _
/-- 標準 Hom の coherent slice 表示は、比較後に同じ実 Hom の slice 表示となる。 -/
lemma dgCoherentHomComparison_slice (x y : ClosedCategory A D) :
    coherentHomComparison x y ≫ pinchedHomToSliceFiber _ _ ≫ vertexFiberι _ _ ≫
      dgCoherentTargetSliceMap A D (ForgetEnrichment.to (Complex A) y) =
        (standardHomPinchedIso (R := A) (D := D) x y).hom ≫
          dgPinchedHomSlice A D x y := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro σ
  apply Subtype.ext
  change ((dgCoherentTargetSliceMap A D y).app _
    (((coherentHomComparison x y ≫ pinchedHomToSliceFiber _ _ ≫ vertexFiberι _ _).app _) σ)).val = _
  rw [dgCoherentTargetSliceMap_val]
  change ((joinStdSimplexIso n 0).hom ≫ SSet.yonedaEquiv.symm
      ((coherentHomComparison x y).app _ σ).val) ≫ coherentComparison (R := A) (D := D) =
    (joinStdSimplexIso n 0).hom ≫ SSet.yonedaEquiv.symm
      (((standardHomPinchedIso (R := A) (D := D) x y).hom.app _ σ).val)
  rw [Category.assoc, SSet.yonedaEquiv_symm_comp]
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app (dgStandardHomToCoherentPinched_comp A D x y) (Opposite.op ⦋n⦌)) σ
  have hv := congrArg (fun a : (DGNerve.pinchedHom A D x y) _⦋n⦌ => a.val) h
  exact congrArg (fun a => (joinStdSimplexIso n 0).hom ≫ SSet.yonedaEquiv.symm a) hv

end SerrePositivity.InfinityCategories
