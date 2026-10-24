module
public import SerrePositivity.EInfinity.ComplexLimits.PinchedPostcompositionFamily
public import SerrePositivity.InfinityCategories.F1B.MappingSpaces.IntervalFunctorHom
/-!
概要：元の pinched 全族の両端作用と実関手の全族像を同じ定値射で計算する。
方針：既存の区間族公式と同じ pinched 比較の全ホモトピーを使う。
規約：全パラメータ・元の射・実関手を保持する。
使われ方：同じ弱な屋根族を既存の標準単位の両端へ輸送する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory SSet MonoidalClosed SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：元の pinched 全族の前合成は同じ成分射の定値族による前合成。
方針：元の pinched/区間比較の全ホモトピーと区間前合成公式を使う。
規約：全パラメータを保持。使われ方：単位の始域端点の輸送。 -/
lemma pinchedPrecompose_intervalFamily {K C : SSet.{u}} [Quasicategory C]
    {a b c : C.obj (Opposite.op ⦋0⦌)}
    (α : (HomotopyCategory.mk a : hoFunctor.obj C) ⟶ HomotopyCategory.mk b)
    (f : K ⟶ pinchedHom b c) :
    intervalFamilyHom (f ≫ PinchedInterval.precompose c α ≫
      pinchedHomToIntervalMappingSpace a c) =
    constantFunctorHomMap K α ≫ intervalFamilyHom (f ≫ pinchedHomToIntervalMappingSpace b c) := by
  have H := FunctorIso.simplicialHomotopy
    (PinchedInterval.liftMapComparisonIso (intervalPrecompose c α))
  have h := intervalFamilyHom_eq_of_homotopy (functorHomotopyPrecomp H f)
  calc
    _ = intervalFamilyHom (f ≫ (pinchedHomToIntervalMappingSpace b c ≫
        intervalPrecompose c α)) := by
      simpa only [PinchedInterval.precompose, Category.assoc] using h
    _ = _ := by rw [← Category.assoc, intervalPrecompose_family]

/-- 概要：元の全族の両端作用は同じ二つの定値射による前後合成。
方針：同じ pinched 前後合成の全族公式を接続する。
規約：元の二射と全族を保持。使われ方：標準頂点への両端輸送。 -/
lemma pinchedTransport_intervalFamily {K C : SSet.{u}} [Quasicategory C]
    {a b c d : C.obj (Opposite.op ⦋0⦌)}
    (α : (HomotopyCategory.mk a : hoFunctor.obj C) ⟶ HomotopyCategory.mk b)
    (β : (HomotopyCategory.mk c : hoFunctor.obj C) ⟶ HomotopyCategory.mk d)
    (f : K ⟶ pinchedHom b c) :
    intervalFamilyHom ((f ≫ PinchedInterval.precompose c α) ≫
      PinchedInterval.postcompose a β ≫ pinchedHomToIntervalMappingSpace a d) =
    constantFunctorHomMap K α ≫ intervalFamilyHom (f ≫ pinchedHomToIntervalMappingSpace b c) ≫
      constantFunctorHomMap K β := by
  rw [pinchedPostcompose_intervalFamily, Category.assoc, pinchedPrecompose_intervalFamily]
  simp only [Category.assoc]

/-- 概要：元の pinched 全族の実関手による像は同じ全関手射の像。
方針：元の pinched 比較の自然性と区間の全後合成公式を使う。
規約：実関手自身を保持。使われ方：実 U の両端輸送の計算。 -/
lemma pinchedFamily_forget_formula {K C D : SSet.{u}} (U : C ⟶ D)
    {b c : C.obj (Opposite.op ⦋0⦌)} (f : K ⟶ pinchedHom b c) :
    intervalFamilyHom (f ≫ pinchedHomMap U b c ≫ pinchedHomToIntervalMappingSpace _ _) =
    (constantFunctorCompIso K b U).inv ≫
      (hoFunctor.map ((ihom K).map U)).toFunctor.map
        (intervalFamilyHom (f ≫ pinchedHomToIntervalMappingSpace b c)) ≫
      (constantFunctorCompIso K c U).hom := by
  rw [pinchedHomToIntervalMappingSpace_naturality, ← Category.assoc,
    intervalFunctorMap_familyHom]

/-- 概要：全関手射の定値両端作用は実関手の同じ成分像へ移る。
方針：既存の二つの定値後合成公式と同じ比較同型の逆則を使う。
規約：元の全関手射と二射を保持。使われ方：標準単位の全族三角形の両端計算。 -/
lemma constantFamilyPostcomp_transport {K C D : SSet.{u}} (U : C ⟶ D)
    {a b c d : C.obj (Opposite.op ⦋0⦌)}
    (α : (HomotopyCategory.mk a : hoFunctor.obj C) ⟶ HomotopyCategory.mk b)
    (β : (HomotopyCategory.mk c : hoFunctor.obj C) ⟶ HomotopyCategory.mk d)
    (h : ConstantFunctorHom K C b c) :
    (constantFunctorCompIso K a U).inv ≫
      (hoFunctor.map ((ihom K).map U)).toFunctor.map
        (constantFunctorHomMap K α ≫ h ≫ constantFunctorHomMap K β) ≫
      (constantFunctorCompIso K d U).hom =
    constantFunctorHomMap K ((hoFunctor.map U).toFunctor.map α) ≫
      ((constantFunctorCompIso K b U).inv ≫
        (hoFunctor.map ((ihom K).map U)).toFunctor.map h ≫
        (constantFunctorCompIso K c U).hom) ≫
      constantFunctorHomMap K ((hoFunctor.map U).toFunctor.map β) := by
  rw [← constantFunctorHomMap_postcomp K U α, ← constantFunctorHomMap_postcomp K U β]
  simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc]

/-- 概要：元の両端輸送後の pinched 全族の U 像は同じ元の U 像の両端輸送。
方針：全族の両端公式と定値成分の全後合成公式を接続する。
規約：同じ全族・二射・実 U を保持。使われ方：標準単位比較への全族輸送。 -/
lemma pinchedTransport_forget_family {K C D : SSet.{u}} [Quasicategory C]
    (U : C ⟶ D) {a b c d : C.obj (Opposite.op ⦋0⦌)}
    (α : (HomotopyCategory.mk a : hoFunctor.obj C) ⟶ HomotopyCategory.mk b)
    (β : (HomotopyCategory.mk c : hoFunctor.obj C) ⟶ HomotopyCategory.mk d)
    (f : K ⟶ pinchedHom b c) :
    intervalFamilyHom (((f ≫ PinchedInterval.precompose c α) ≫
      PinchedInterval.postcompose a β) ≫ pinchedHomMap U a d ≫
        pinchedHomToIntervalMappingSpace _ _) =
    constantFunctorHomMap K ((hoFunctor.map U).toFunctor.map α) ≫
      intervalFamilyHom (f ≫ pinchedHomMap U b c ≫ pinchedHomToIntervalMappingSpace _ _) ≫
      constantFunctorHomMap K ((hoFunctor.map U).toFunctor.map β) := by
  rw [pinchedFamily_forget_formula, Category.assoc, pinchedTransport_intervalFamily,
    constantFamilyPostcomp_transport, ← pinchedFamily_forget_formula U f]

end SerrePositivity.EInfinity.ComplexLimits
