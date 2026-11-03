module
public import SerrePositivity.KST.SConstruction.DGModuleConeInputIsoNaturality
public import SerrePositivity.DifferentialGraded.Module.Hom.ConeComparison

/-!
概要：同じ元 cone 入力等号の実同型が元包含・connecting を保つことを示す。
方針：同じ入力等号を消去し、元恒等則へ帰着する。
規約：指定入力同型と元実射を保持する。
使われ方：元 gluing cone 全比較の指定二単体の境界。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

/-- 概要：同じ指定 cone 入力同型は元右包含を保つ。
方針：元入力等号を消去する。規約：厳密な閉射等式。
使われ方：元包含境界の回収。 -/
lemma dgModuleConeInputIso_inr {M N : ModuleCategory R D}
    (f f' : M ⟶ N) (h : f = f') :
    moduleConeInr R D f ≫ (eqToIso (congrArg (fun t => moduleCone R D t) h)).hom =
      moduleConeInr R D f' := by
  cases h
  simp only [eqToIso_refl, Iso.refl_hom, Category.comp_id]

/-- 概要：同じ指定 cone 入力同型は元 connecting 射を保つ。
方針：元入力等号を消去する。規約：厳密な閉射等式。
使われ方：全実逆回転をつなぐ指定 connecting 境界。 -/
lemma dgModuleConeInputIso_connecting {M N : ModuleCategory R D}
    (f f' : M ⟶ N) (h : f = f') :
    moduleConeConnecting R D f =
      (eqToIso (congrArg (fun t => moduleCone R D t) h)).hom ≫ moduleConeConnecting R D f' := by
  cases h
  simp only [eqToIso_refl, Iso.refl_hom, Category.id_comp]
end SerrePositivity.KST.SConstruction
