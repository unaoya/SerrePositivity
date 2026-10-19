module

public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapExceptionalBaseMap

/-!
概要：KST v4 Lemma 3.6（pp.11–14）の例外因子の基底への射を係数図式に装備する。
方針：共通 Koszul 表示への基底係数射の自然性を証明し、指定図式同型で元の表示へ移す。
規約：係数代数の自然変換であり、層レベルの射や導来直像との比較は別工程。
使われ方：例外因子の q* と blowup への局所射の係数計算。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory DifferentialGraded

variable (R : Type u) [CommRing R] {I : Type} [DecidableEq I]

set_option maxHeartbeats 2000000 in
-- 二つの局所化環の係数変更と共通基底環上の Hom を照合するために必要。
set_option synthInstance.maxHeartbeats 100000 in
-- 局所化環上の複体のモノイダル構造を照合するために必要。
/-- 概要：基底 Koszul dg 代数から共通表示への射は全有限重なり遷移と可換。
方針：総外積上で二段の係数変更を合成し、実際の環射の基底係数保存を使う。
規約：KST Lemma 3.6。使われ方：基底からの係数自然変換の自然性。 -/
theorem finiteOverlapExceptionalProductBaseMap_natural (a : I → R) (i k : I)
    {T U : Finset I} (h : T ⊆ U) (hi : i ∈ T) :
    finiteOverlapExceptionalProductBaseMap R a i T ≫
        finiteOverlapExceptionalProductMap R a i k h hi =
      finiteOverlapExceptionalProductBaseMap R a k U := by
  apply Mon.Hom.ext
  apply HomologicalComplex.Hom.ext
  funext q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply exteriorCochainInclusion_injective
    (Finsupp.linearCombination (FiniteOverlapRing R k U)
      (fun j => algebraMap R (FiniteOverlapRing R k U) (a j))) q
  change exteriorCochainInclusion (Finsupp.linearCombination (FiniteOverlapRing R k U)
      (fun j => algebraMap R (FiniteOverlapRing R k U) (a j))) q
      (((finiteOverlapExceptionalProductMap R a i k h hi).hom.f q)
        (((finiteOverlapExceptionalProductBaseMap R a i T).hom.f q) z)) =
    exteriorCochainInclusion (Finsupp.linearCombination (FiniteOverlapRing R k U)
      (fun j => algebraMap R (FiniteOverlapRing R k U) (a j))) q
      (((finiteOverlapExceptionalProductBaseMap R a k U).hom.f q) z)
  rw [finiteOverlapExceptionalProductMap_inclusion,
    finiteOverlapExceptionalProductBaseMap_inclusion,
    finiteOverlapExceptionalProductBaseMap_inclusion, freeExteriorScalarMap_comp,
    baseRestrictionRingHom_comp]

/-- 概要：基底 Ko(A;a) の定数図式から共通 Koszul 表示の係数図式への指定自然変換。
方針：各重なり環への標準係数射を成分とし、証明済みの自然性を使う。
規約：KST Lemma 3.6、幾何の射と反変の向き。
使われ方：例外因子の射影を dg 加群の係数射として扱う。 -/
def finiteOverlapExceptionalProductBaseNatTrans (a : I → R) :
    (Functor.const (FiniteOverlapIndex I)).obj (baseKoszulDGAlgebra R a) ⟶
      finiteOverlapExceptionalProductDiagram R a where
  app T := finiteOverlapExceptionalProductBaseMap R a (finiteOverlapIndexPivot T) T.val
  naturality {T U} f := by
    change 𝟙 _ ≫ finiteOverlapExceptionalProductBaseMap R a (finiteOverlapIndexPivot U) U.val =
      finiteOverlapExceptionalProductBaseMap R a (finiteOverlapIndexPivot T) T.val ≫
        finiteOverlapExceptionalProductMap R a (finiteOverlapIndexPivot T)
          (finiteOverlapIndexPivot U) (leOfHom f) (finiteOverlapIndexPivot_mem T)
    rw [Category.id_comp]
    exact (finiteOverlapExceptionalProductBaseMap_natural R a _ _ _ _).symm

/-- 概要：基底 Ko(A;a) から元の例外因子係数図式への指定自然変換。
方針：共通表示への基底係数射に指定図式同型の逆を合成する。
規約：KST Lemma 3.6、元の例外因子模型を保持する。
使われ方：元の cartesian dg 加群模型で q* を構成する入力。 -/
def finiteOverlapExceptionalBaseNatTrans (a : I → R) :
    (Functor.const (FiniteOverlapIndex I)).obj (baseKoszulDGAlgebra R a) ⟶
      finiteOverlapExceptionalDGAlgebraDiagram R a :=
  finiteOverlapExceptionalProductBaseNatTrans R a ≫
    (finiteOverlapExceptionalProductDiagramIso R a).inv

/-- 概要：元の例外因子への基底係数射は指定図式比較を通して標準係数射に一致する。
方針：図式同型の逆と順射を消去する。
規約：KST Lemma 3.6。使われ方：二つの表示で同じ射影を使うことの整合性。 -/
theorem finiteOverlapExceptionalBaseNatTrans_comparison (a : I → R) :
    finiteOverlapExceptionalBaseNatTrans R a ≫ (finiteOverlapExceptionalProductDiagramIso R a).hom =
      finiteOverlapExceptionalProductBaseNatTrans R a := by
  simp only [finiteOverlapExceptionalBaseNatTrans, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

end SerrePositivity.KST.DerivedBlowup
