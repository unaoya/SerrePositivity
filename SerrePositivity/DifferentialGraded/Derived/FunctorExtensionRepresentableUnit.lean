module
public import SerrePositivity.DifferentialGraded.Derived.FunctorExtensionUnitComputation

/-! # Hom準同型に沿う導来単位の代表加群上での可逆性

## 概要
Hom準同型に沿う導来単位の代表加群上での可逆性。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。固定dg圏上の導来tensor・Morita作用の基盤。
非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

lemma functorExtensionUnit_resolution_quasiIso {M : ModuleCategory A D}
    (hM : moduleHomotopicallyProjective A D M)
    (hunit : moduleQuasiIso A D
      (functorExtensionUnit A D E F (ForgetEnrichment.to (Complex A) M)))
    (P : ModuleProjectiveResolution A D M) :
    moduleQuasiIso A D (functorExtensionUnit A D E F
      (ForgetEnrichment.to (Complex A) P.obj)) := by
  have hg := moduleRestriction_quasiIso A D E F.op _
    (dgModuleExtension_projective_quasiIso A D E F P.projective hM P.π P.quasiIso)
  have hn := (dgModuleUnit A D E F).naturality P.π
  change P.π ≫ functorExtensionUnit A D E F (ForgetEnrichment.to (Complex A) M) =
    functorExtensionUnit A D E F (ForgetEnrichment.to (Complex A) P.obj) ≫
      (moduleRestriction A D E F.op).map ((dgModuleExtension A D E F).onClosed.map P.π) at hn
  have hcomp := (moduleQuasiIso A D).comp_mem _ _ P.quasiIso hunit
  rw [hn] at hcomp
  exact (moduleQuasiIso A D).of_postcomp _ _ hg hcomp

lemma dgDerivedExtensionUnit_representable_isIso (hF : HomQuasiIso F) (d : D) :
    IsIso ((dgDerivedExtensionUnit A D E F).app
      ((moduleToDerived A D).obj (ForgetEnrichment.of (Complex A) (representable A d)))) := by
  let M := ForgetEnrichment.of (Complex A) (representable A d)
  let P := moduleCanonicalProjectiveResolution A D M
  have hP := functorExtensionUnit_resolution_quasiIso A D E F
    (representable_homotopicallyProjective A D d)
    (functorExtensionUnit_representable_quasiIso A D E F hF d) P
  have hi := moduleToDerived_inverts A D _ hP
  let := hi
  have h := dgDerivedExtensionUnit_computation A D E F M
  have : IsIso ((dgDerivedExtensionUnit A D E F).app ((moduleToDerived A D).obj M) ≫
      (dgDerivedRestriction A D E F).map
        (dgDerivedExtensionResolutionComputation A D E F P).hom) := by
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_right
    ((dgDerivedExtensionUnit A D E F).app ((moduleToDerived A D).obj M))
    ((dgDerivedRestriction A D E F).map
      (dgDerivedExtensionResolutionComputation A D E F P).hom)

end SerrePositivity.DifferentialGraded
