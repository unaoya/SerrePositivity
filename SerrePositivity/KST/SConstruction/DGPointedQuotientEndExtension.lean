module
public import SerrePositivity.KST.SConstruction.DGPointedQuotientEnd

/-! # 指定収縮を保つ実 dg 商 End からの射
概要：元の対角像の収縮を指定した実 dg 関手を、同じ商の指定対象 End から延長する。
方針：全 path と指定 ε を保つ商の普遍性を、同じ対象の End へ制限する。
規約：収縮を選び直さない。使われ方：dg ⊙ から比較先の代数への実射。
-/
@[expose] public section
noncomputable section
universe u v w t
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded
variable (R : Type u) [CommRing R] {P : Type v} {G : Type w}
  [DGCategory R P] [DGCategory R G] [Small.{u} G] (i : DGFunctor R P G)
  {T : Type t} [DGCategory R T]
  (H : DGQuotient.ContractedFunctor R G (dgQuotientImage R i) T)

/-- 元の指定収縮から、同じ商の指定対象 End への実 dg 射を構成する。 -/
def pointedDGQuotientEndExtension (b : G) :
    DGFunctor R (PointedDGQuotientEndObject R i b)
      (EndomorphismObject (H.toDGFunctor.obj b)) :=
  endomorphismMap R (DGQuotient.extension R H) (pointedDGQuotientVertex R i b)

/-- 同じ End 射の全 Hom 鎖写像は、元の全 path と指定 ε による評価。 -/
lemma pointedDGQuotientEndExtension_map (b : G)
    (x y : PointedDGQuotientEndObject R i b) :
    (pointedDGQuotientEndExtension R i H b).map x y =
      DGQuotient.quotientEvaluation R H b b := rfl

/-- 元の End の射は、同じ商の End を経由して全 Hom 上で厳密に回収される。 -/
lemma pointedDGQuotientEndExtension_unitMap (b : G) :
    (pointedDGQuotientEndUnitMap R i b).comp (pointedDGQuotientEndExtension R i H b) =
      endomorphismMap R H.toDGFunctor b := by
  apply EnrichedFunctor.ext (Complex R)
    (F := (pointedDGQuotientEndUnitMap R i b).comp (pointedDGQuotientEndExtension R i H b))
    (G := endomorphismMap R H.toDGFunctor b) (fun _ => rfl)
  intro x y
  change (DGQuotient.originalHomInclusion R G (dgQuotientImage R i) b b ≫
    DGQuotient.quotientEvaluation R H b b) ≫ eqToHom (by rfl) = H.toDGFunctor.map b b
  rw [eqToHom_refl, Category.comp_id, DGQuotient.quotientEvaluation_original]

/-- 指定対象が対角像なら、同じ End の射は元の指定 ε を指定収縮そのものへ送る。 -/
lemma pointedDGQuotientEndExtension_epsilon (a : P)
    (x y : PointedDGQuotientEndObject R i (i.obj a)) :
    ((pointedDGQuotientEndExtension R i H (i.obj a)).map x y).f (-1)
        (pointedDGQuotientDiagonalEpsilon R i a) = H.homotopy ⟨i.obj a, ⟨a, rfl⟩⟩ :=
  DGQuotient.restrict_extension_homotopy R H ⟨i.obj a, ⟨a, rfl⟩⟩

omit [Small.{u} G] in
/-- 元の指定収縮の像の微分も、同じ対象の恒等を厳密に回収する。 -/
lemma pointedDGQuotientEndExtension_epsilon_d (a : P) :
    (homObject R T (H.toDGFunctor.obj (i.obj a)) (H.toDGFunctor.obj (i.obj a))).d (-1) 0
      (H.homotopy ⟨i.obj a, ⟨a, rfl⟩⟩) =
    (unitElement R (H.toDGFunctor.obj (i.obj a))).val := H.d_homotopy ⟨i.obj a, ⟨a, rfl⟩⟩

end SerrePositivity.KST.SConstruction
