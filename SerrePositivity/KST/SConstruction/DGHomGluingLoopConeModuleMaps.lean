module
public import SerrePositivity.KST.SConstruction.DGHomGluingLoopCone
public import SerrePositivity.KST.SConstruction.DGHomGluingConeConnectingComparison

/-!
概要：実逆回転の二つの perfect dg 関手の全 Hom 作用を元加群の表示へ照合する。
方針：同じ全 Hom の包含と dg shift の制限だけを回収する。
規約：元 cone 関手は展開しない。使われ方：共通小模型での全自然性の輸送。
-/
@[expose] public section
noncomputable section
universe u v w z
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D]
  (E : Type z) [DGCategory R E] [Small.{u} E]
  (p : DGFunctor R C E) (q : DGFunctor R D E)
local notation "L" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D (dgHomGluingBimodule R C D E p q)

/-- 概要：同じ実逆 shift cone の Hom は元加群 cone 関手の逆 shift の Hom。
方針：元包含の Hom 恒等作用だけを消去する。
規約：元 cone の全 Hom を保持。使われ方：逆回転の左全 Hom 比較。 -/
lemma dgHomGluingLoopConeFunctor_module_map (X Y : L) :
    (dgHomGluingLoopConeFunctor R C D E p q).map X Y =
      ((dgHomGluingModuleConeFunctor R C D E p q).comp (moduleShiftDG R E (-1))).map X Y := by
  change (dgHomGluingConeFunctor R C D E p q).map X Y ≫
      moduleShiftHom R E (-1) _ _ =
    ((dgHomGluingConeFunctor R C D E p q).map X Y ≫ 𝟙 _) ≫ moduleShiftHom R E (-1) _ _
  exact (congrArg (fun k => k ≫ moduleShiftHom R E (-1) _ _)
    (Category.comp_id ((dgHomGluingConeFunctor R C D E p q).map X Y))).symm

/-- 概要：元左対象の二重 shift の Hom は元 Yoneda 加群の同じ二重 dg shift の Hom。
方針：同じ perfect Yoneda と shift の全 Hom 制限を回収する。
規約：元の二重 shift を保持。使われ方：逆回転の右全 Hom 比較。 -/
lemma dgHomGluingDoubleShiftLeftFunctor_module_map (X Y : L) :
    (dgHomGluingDoubleShiftLeftFunctor R C D E p q).map X Y =
      ((dgHomGluingShiftedLeftModuleFunctor R C D E p q).comp
        (moduleShiftDG R E (-1))).map X Y := rfl
end SerrePositivity.KST.SConstruction
