module
public import SerrePositivity.InfinityCategories.Derived.DGNerveOppositeIso
public import SerrePositivity.DifferentialGraded.Functor.Closed
public import SerrePositivity.InfinityCategories.DGNerve.Functor
/-!
概要：実反対圏比較と、任意の dg 関手の全単体作用との厳密な自然性。
方針：全 Hom の鎖写像が反転符号と可換なことを全成分へ適用する。
規約：対象別の同型ではなく実 ∞ 関手の等式。使われ方：反変 Hom の模型変更。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerveOppositeData
/-- 符号付き実反転は、dg 関手の全実成分への作用と厳密に可換。 -/
lemma dgOppositeData_map {R : Type u} [CommRing R] {D : Type v} {E : Type w}
    [DGCategory R D] [DGCategory R E] {n : ℕ}
    (s : SimplexData R D n) (F : DGFunctor R D E) :
    DGNerveOppositeData.op (s.map F) = (DGNerveOppositeData.op s).map F.op := by
  apply SimplexData.ext
  · rfl
  · apply heq_of_eq
    funext I a b k hI ha hb hk
    simp only [DGNerveOppositeData.op, SimplexData.map, DGFunctor.op, id_eq,
      Units.smul_def, map_zsmul]
    rfl
/-- 同じ実 dg 関手の nerve に関して、反対圏比較の全四角形は厳密に可換。 -/
lemma dgNerveOppositeIso_naturality {R : Type u} [CommRing R] {D E : Type v}
    [DGCategory R D] [DGCategory R E] (F : DGFunctor R D E) :
    SSet.opFunctor.map (dgNerve.map F) ≫ (dgNerveOppositeIso R E).hom =
      (dgNerveOppositeIso R D).hom ≫ dgNerve.map F.op := by
  ext n s
  change opSimplex ((SSet.opObjEquiv s).map F) = (opSimplex (SSet.opObjEquiv s)).map F.op
  apply Simplex.ext
  exact dgOppositeData_map (SSet.opObjEquiv s).toSimplexData F
end SerrePositivity.InfinityCategories
