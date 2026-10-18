module

public import SerrePositivity.KST.DerivedGeometry.LinearShiftNaturality

/-!
概要：複体から代表 dg 加群への関手が整数 shift と可換であることを証明する。
方針：具体的な右 shift の自然同型と零・加法の整合性を束ねる。
規約：Mathlib と既存 dg 加群の標準 shift をそのまま使う。
使われ方：Drinfeld §2.4、KST D4・§10-7 の標準三角形の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.DerivedGeometry.LinearComplex
variable (A : Type u) [CommRing A] {C : Type v} [Category.{u} C] [Preadditive C] [Linear A C]
attribute [local instance] enrichment
variable [Small.{u} (CochainComplex C ℤ)]

set_option maxHeartbeats 1000000 in
-- 豊穣な加群圏の shift 比較の型の展開と評価の比較に必要。
/--
概要：代表加群への具体的な関手は整合的に全整数 shift と可換。
方針：各評価で、証明済みの写像複体の零・加法 shift の式へ戻す。
規約：比較同型は既に構成した代表加群の shift 同型の逆とする。
使われ方：Drinfeld §2.4、KST D4 の三角構造と導来局所化の比較。
-/
instance complexYoneda_commShift : (complexYoneda (C := C) A).CommShift ℤ where
  commShiftIso s := (complexYonedaShiftIso A s).symm
  commShiftIso_zero := by
    apply Iso.ext_inv
    apply NatTrans.ext
    funext X
    rw [CategoryTheory.Functor.CommShift.isoZero_inv_app]
    have hc : (representableShiftIso A X 0).hom ≫ (complexYoneda A).map
        ((shiftFunctorZero (CochainComplex C ℤ) ℤ).hom.app X) =
        (shiftFunctorZero (ModuleCategory A (CochainComplex C ℤ)) ℤ).hom.app
          ((complexYoneda A).obj X) := by
      apply moduleMorphism_ext
      intro T
      simp only [CategoryTheory.Functor.map_comp, moduleShiftZero_eq,
        moduleShiftZeroIso_hom_eval, representableShiftIso_hom_eval]
      change mappingShiftMap A T X 0 ≫
        (moduleEvaluation A (CochainComplex C ℤ) T).map (representablePostcompose A
          ((shiftFunctorZero (CochainComplex C ℤ) ℤ).hom.app X)) = _
      rw [representablePostcompose_eval]
      exact mappingShiftMap_zero A T X
    have he := congrArg (fun z => z ≫ (complexYoneda A).map
      ((shiftFunctorZero (CochainComplex C ℤ) ℤ).inv.app X)) hc
    simp only [Category.assoc, ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id_app,
      CategoryTheory.Functor.map_id] at he
    exact (Category.comp_id (representableShiftIso A X 0).hom).symm.trans he
  commShiftIso_add s t := by
    apply Iso.ext_inv
    apply NatTrans.ext
    funext X
    rw [CategoryTheory.Functor.CommShift.isoAdd_inv_app]
    have hc : (representableShiftIso A X (s + t)).hom ≫ (complexYoneda A).map
        ((shiftFunctorAdd (CochainComplex C ℤ) s t).hom.app X) =
      (shiftFunctorAdd (ModuleCategory A (CochainComplex C ℤ)) s t).hom.app
        ((complexYoneda A).obj X) ≫
      (representableShiftIso A X s).hom⟦t⟧' ≫
      (representableShiftIso A (X⟦s⟧) t).hom := by
      apply moduleMorphism_ext
      intro T
      simp only [CategoryTheory.Functor.map_comp, moduleShiftAdd_eq,
        moduleShiftAddIso_hom_eval, moduleShiftFunctor_eq, moduleShiftFunctor_map_eval,
        representableShiftIso_hom_eval]
      change mappingShiftMap A T X (s + t) ≫
        (moduleEvaluation A (CochainComplex C ℤ) T).map (representablePostcompose A
          ((shiftFunctorAdd (CochainComplex C ℤ) s t).hom.app X)) =
        (shiftFunctorAdd (Complex A) s t).hom.app (mappingComplex A T X) ≫
          (mappingShiftMap A T X s)⟦t⟧' ≫ mappingShiftMap A T (X⟦s⟧) t
      rw [representablePostcompose_eval]
      exact mappingShiftMap_add A T X s t
    have he := congrArg (fun z => z ≫ (complexYoneda A).map
      ((shiftFunctorAdd (CochainComplex C ℤ) s t).inv.app X)) hc
    simp only [Category.assoc, ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id_app,
      CategoryTheory.Functor.map_id] at he
    exact (Category.comp_id (representableShiftIso A X (s + t)).hom).symm.trans he

/--
概要：代表加群関手の shift 可換性の成分は具体的な shift 同型の逆。
方針：構成した可換性構造の同型成分を読む。
規約：三角形の比較で可換性の証明全体を展開しない。
使われ方：Drinfeld §2.4、KST D4 の標準三角形の第三射。
-/
theorem complexYoneda_commShiftIso_hom_app (X : CochainComplex C ℤ) (s : ℤ) :
    ((complexYoneda A).commShiftIso s).hom.app X = (representableShiftIso A X s).inv := rfl

/--
概要：具体的な代表加群関手の射は構成した後合成射。
方針：関手の射成分の定義を使う。
規約：三角形の比較で関手全体を展開しない。
使われ方：Drinfeld §2.4、KST D4 の標準三角形。
-/
theorem complexYoneda_map {X Y : CochainComplex C ℤ} (f : X ⟶ Y) :
    (complexYoneda A).map f = representablePostcompose A f := rfl

end SerrePositivity.KST.DerivedGeometry.LinearComplex
