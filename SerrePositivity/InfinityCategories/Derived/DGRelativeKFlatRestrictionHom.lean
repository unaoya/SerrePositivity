module
public import SerrePositivity.InfinityCategories.Derived.DGRelativeKFlatKernelRestrictionNerve
public import SerrePositivity.InfinityCategories.Derived.FunctorHomotopyRawTransport
public import SerrePositivity.InfinityCategories.F2.FunctorEqIsoTransport
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (D E : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
  (P : Bimodule R E D) (hP : Bimodule.rightRelativeKFlat R E D P)
/-- 同じ制限比較の順方向射は、元の raw factor の射を型付きで保つ。 -/
lemma dgRelativeKFlatKernelRestrictionNerveIso_hom_heq :
    HEq (dgRelativeKFlatKernelRestrictionNerveIso R D E P hP).hom
      (dgModuleResolvedInfinity_rawFactorIso R (SemifreeDGModules R D) E
        (dgSemifreeKernelModuleDG R D E P)).hom := by
  exact functorIso_hom_heq (dgRelativeKFlatKernelRestrictionNerveIso R D E P hP)
    (dgModuleResolvedInfinity_rawFactorIso R (SemifreeDGModules R D) E
      (dgSemifreeKernelModuleDG R D E P)) rfl
    (dgRelativeKFlatKernelNerve_semifree_resolution R D E P hP)
    (dgRelativeKFlatKernelRestrictionNerveIso_heq R D E P hP)
/-- 任意の指定入力で制限した同じ比較の射も、元の raw factor の制限の射へ戻る。 -/
lemma dgRelativeKFlatKernelRestrictionNerveIso_precomp_hom_heq
    (X : SSet.{max (u + 1) v}) (a : X ⟶ dgModuleDerivedInfinityCategory R D) :
    HEq ((dgRelativeKFlatKernelRestrictionNerveIso R D E P hP).precomp a).hom
      ((dgModuleResolvedInfinity_rawFactorIso R (SemifreeDGModules R D) E
        (dgSemifreeKernelModuleDG R D E P)).precomp a).hom := by
  let r := dgRelativeKFlatKernelRestrictionNerveIso R D E P hP
  let s := dgModuleResolvedInfinity_rawFactorIso R (SemifreeDGModules R D) E
    (dgSemifreeKernelModuleDG R D E P)
  have hs := dgRelativeKFlatKernelNerve_semifree_resolution R D E P hP
  have hi := F2.functorIso_precomp_heq_of_heq s r rfl hs.symm
    (dgRelativeKFlatKernelRestrictionNerveIso_heq R D E P hP) a
  exact functorIso_hom_heq (r.precomp a) (s.precomp a) rfl
    (congrArg (fun m => a ≫ m) hs) hi
end SerrePositivity.InfinityCategories
