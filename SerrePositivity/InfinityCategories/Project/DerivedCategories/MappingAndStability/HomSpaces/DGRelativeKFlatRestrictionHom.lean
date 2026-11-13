module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.Nerves.DGRelativeKFlatKernelRestrictionNerve
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.SimplicialFunctors.FunctorHomotopyRawTransport
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.FunctorEqIsoTransport
/-!
概要：端点を揃えた K-flat kernel 制限比較の射を、元の raw factor の射へ回収する。
方針：一般 kernel 変数の下で同じ指定同型と端点等式を先に射へ移す。
規約：合成 kernel の具体的 tensor を展開しない。使われ方：指定合成子の共通経路計算。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet DifferentialGraded
variable (R : Type u) [CommRing R] (D E : Type v)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
  (P : _root_.SerrePositivity.DifferentialGraded.Bimodule R E D) (hP : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R E D P)
/-- 同じ制限比較の順方向射は、元の raw factor の射を型付きで保つ。 -/
lemma dgRelativeKFlatKernelRestrictionNerveIso_hom_heq :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelRestrictionNerveIso R D E P hP).hom
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_rawFactorIso R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) E
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG R D E P)).hom := by
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_hom_heq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelRestrictionNerveIso R D E P hP)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_rawFactorIso R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) E
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG R D E P)) rfl
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_semifree_resolution R D E P hP)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelRestrictionNerveIso_heq R D E P hP)
/-- 任意の指定入力で制限した同じ比較の射も、元の raw factor の制限の射へ戻る。 -/
lemma dgRelativeKFlatKernelRestrictionNerveIso_precomp_hom_heq
    (X : SSet.{max (u + 1) v}) (a : X ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R D) :
    HEq ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelRestrictionNerveIso R D E P hP).precomp a).hom
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_rawFactorIso R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) E
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG R D E P)).precomp a).hom := by
  let r := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelRestrictionNerveIso R D E P hP
  let s := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_rawFactorIso R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) E
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG R D E P)
  have hs := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_semifree_resolution R D E P hP
  have hi := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.functorIso_precomp_heq_of_heq s r rfl hs.symm
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelRestrictionNerveIso_heq R D E P hP) a
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_hom_heq (r.precomp a) (s.precomp a) rfl
    (congrArg (fun m => a ≫ m) hs) hi
end SerrePositivity.InfinityCategories.Project.DerivedCategories
