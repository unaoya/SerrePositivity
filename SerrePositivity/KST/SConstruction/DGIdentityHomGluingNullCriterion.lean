module
public import SerrePositivity.KST.SConstruction.DGIdentityHomGluingNullDomain
public import SerrePositivity.DifferentialGraded.Derived.Basic

/-!
概要：元の実比較射の準同型性から同じ cone の可縮性を得る。
方針：実 cone の既存射影性と非輪状性に D 正本の境界判定を適用する。
規約：全関手 Γ の h-射影性や自然収縮を仮定しない。
使われ方：元厚核関手を実零化始域 V へ因子化する対象別条件の充足。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (C : Type (u + 1)) [DGCategory R C] [Small.{u} C]
local notation "I" => DGFunctor.id C
local notation "L" => DGIdentityHomGluing R C

/-- 概要：元の Yoneda 比較射が準同型なら元 gluing 対象は V の条件を満たす。
方針：同じ標準 cone の非輪状性と保持済み perfect-projective 証拠を使う。
規約：同じ cone の実 Hom 内の収縮。使われ方：元厚核上の因子化条件。 -/
lemma dgIdentityHomGluingNullProperty_of_targetModuleQuasiIso (x : L)
    (hx : moduleQuasiIso R C (dgHomGluingTargetModuleMap R C C C (I) (I) x)) :
    dgIdentityHomGluingNullProperty R C x := by
  let M := dgHomGluingTargetCone R C C C (I) (I) x
  have hA : moduleAcyclic R C (ForgetEnrichment.of (Complex R) M.val) :=
    (moduleQuasiIso_iff_acyclic_cone R C _).1 hx
  exact moduleHomotopicallyProjective_contractingElement_of_acyclic R C
    M.val M.property.1 hA

/-- 概要：元の比較射がホモトピー圏で可逆なら元実 cone は可縮。
方針：同じ Yoneda のホモトピー関手と加群ホモロジーで準同型性を得る。
規約：厳密逆や関手族全体の自然収縮は不要。使われ方：元 raw cone 比較の消費。 -/
lemma dgIdentityHomGluingNullProperty_of_targetHomotopyIso (x : L)
    (hx : IsIso ((toHomotopy R C).map (dgHomGluingTargetMap R C C C (I) (I) x))) :
    dgIdentityHomGluingNullProperty R C x := by
  apply dgIdentityHomGluingNullProperty_of_targetModuleQuasiIso R C x
  apply (moduleHomotopyQuasiIso_map_iff R C _).1
  have hi : IsIso ((moduleToHomotopy R C).map
      (dgHomGluingTargetModuleMap R C C C (I) (I) x)) := by
    change IsIso ((dgYoneda R C).onHomotopy.map
      ((toHomotopy R C).map (dgHomGluingTargetMap R C C C (I) (I) x)))
    let := hx
    infer_instance
  exact (moduleHomotopyQuasiIso R C).of_isIso _

/-- 概要：全 Hom を保つ実加群包含後の準同型性から元 cone の可縮性を反映する。
方針：対象別射影性で準同型を K(E) 同型にし、同じ充満忠実包含で反映する。
規約：元の閉比較射を保持。使われ方：小 Perf 基底内の実逆回転への接続。 -/
lemma dgIdentityHomGluingNullProperty_of_targetImageQuasiIso
    (E : Type v) [DGCategory R E] [Small.{u} E]
    (J : DGFunctor R C (RightModule R E)) (hJ : ∀ x y, IsIso (J.map x y))
    (hP : ∀ y, moduleHomotopicallyProjective R E
      (ForgetEnrichment.of (Complex R) (J.obj y))) (x : L)
    (hx : moduleQuasiIso R E
      (J.onClosed.map (dgHomGluingTargetMap R C C C (I) (I) x))) :
    dgIdentityHomGluingNullProperty R C x := by
  apply dgIdentityHomGluingNullProperty_of_targetHomotopyIso R C x
  let : J.onHomotopy.Full := J.onHomotopy_full_of_homIso hJ
  let : J.onHomotopy.Faithful := J.onHomotopy_faithful_of_homIso hJ
  have hi : IsIso (J.onHomotopy.map
      ((toHomotopy R C).map (dgHomGluingTargetMap R C C C (I) (I) x))) :=
    moduleHomotopicallyProjective_quasiIso_isIso_homotopy R E
      (hP x.left) (hP x.right) _ hx
  exact isIso_of_reflects_iso _ J.onHomotopy

end SerrePositivity.KST.SConstruction
