module
public import SerrePositivity.KST.SConstruction.DGModuleNaturalConnectingCone
public import SerrePositivity.KST.SConstruction.DGModuleConeHomotopyTriangle

/-!
概要：全 connecting cone 比較の成分を元実 square の cone 射へ戻す。
方針：元 descent 入力と終辺を回収し、元の同値性定理を使用する。
規約：同じ指定ホモトピーを保持する。
使われ方：実逆回転全比較の成分同値認証。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
private lemma descRecovery {M N M' N' : ModuleCategory R D}
    (f : M ⟶ N) (g : M' ⟶ N') (a : M ⟶ M') (b : N ⟶ N')
    (h : ModuleHomotopy R D (f ≫ b) (a ≫ g))
    (s : (moduleHom R D (ForgetEnrichment.to (Complex R) M)
      (ForgetEnrichment.to (Complex R) (moduleCone R D g))).X (-1))
    (q : N ⟶ moduleCone R D g)
    (ds : (moduleHom R D (ForgetEnrichment.to (Complex R) M)
      (ForgetEnrichment.to (Complex R) (moduleCone R D g))).d (-1) 0 s =
        (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) (f ≫ q))).val)
    (es : s = moduleConeHomotopyInput R D f g a b h)
    (eq : q = b ≫ moduleConeInr R D g) :
    moduleConeDescOfBoundary R D f s q ds = moduleConeMapOfHomotopy R D f g a b h := by
  cases es
  cases eq
  rfl
/-- 概要：指定零化元と終辺の一致から同じ元 cone 射を回収する。
方針：既存の同じ入力・終辺の回収補題を使用する。
規約：微分証拠の移送を明示入力の等式で保持。使われ方：全 cone 比較の実成分。 -/
lemma dgModuleConeDesc_recovery {M N M' N' : ModuleCategory R D}
    (f : M ⟶ N) (g : M' ⟶ N') (a : M ⟶ M') (b : N ⟶ N')
    (h : ModuleHomotopy R D (f ≫ b) (a ≫ g))
    (s : (moduleHom R D (ForgetEnrichment.to (Complex R) M)
      (ForgetEnrichment.to (Complex R) (moduleCone R D g))).X (-1))
    (q : N ⟶ moduleCone R D g)
    (ds : (moduleHom R D (ForgetEnrichment.to (Complex R) M)
      (ForgetEnrichment.to (Complex R) (moduleCone R D g))).d (-1) 0 s =
        (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) (f ≫ q))).val)
    (es : s = moduleConeHomotopyInput R D f g a b h)
    (eq : q = b ≫ moduleConeInr R D g) :
    moduleConeDescOfBoundary R D f s q ds = moduleConeMapOfHomotopy R D f g a b h := by
  exact descRecovery R D f g a b h s q ds es eq
variable {P : Type w} [DGCategory R P]
  (F G : DGFunctor R P (RightModule R D)) (η : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G)
local notation "CF" => dgModuleNaturalConeFunctor R D F G η
local notation "ν" => dgModuleNaturalConeInr R D F G η
local notation "U" => dgModuleNaturalConeFunctor R D G (CF) (ν)
local notation "j" => dgModuleNaturalConeInr R D G (CF) (ν)
local notation "V" => dgModuleNaturalConeFunctor R D (CF) (U) (j)
local notation "k" => dgModuleNaturalConeInr R D (CF) (U) (j)
local notation "FS" => F.comp (moduleShiftDG R D 1)
local notation "δ" => dgModuleNaturalConeConnecting R D F G η
local notation "γ" => dgModuleNaturalConeRotationHom R D F G η
local notation "ξ" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransComp (γ) (k)
local notation "CD" => dgModuleNaturalConeFunctor R D (CF) (FS) (δ)
local notation "θ" => dgModuleNaturalConnectingCone R D F G η

/-- 概要：同じ全 connecting cone 比較の閉成分は元実 square の cone 射。
方針：指定 descent 入力と元包含後の終辺を回収する。
規約：元の指定ホモトピーを保持。使われ方：全比較の成分同値の回収。 -/
lemma dgModuleNaturalConnectingCone_arrow (x : P) :
    dgModuleNaturalConeArrow R D (CD) (V) (θ) x =
      moduleConeMapOfHomotopy R D
        (dgModuleNaturalConeArrow R D (CF) (FS) (δ) x)
        (dgModuleNaturalConeArrow R D (CF) (U) (j) x)
        (𝟙 (ForgetEnrichment.of (Complex R) ((CF).obj x)))
        (dgModuleNaturalConeArrow R D (FS) (U) (γ) x)
        (dgModuleNaturalConeRotationSquareHomotopy R D F G η x) := by
  exact (dgModuleNaturalConeDesc_arrow R D (CF) (FS) (V) (δ) (ξ)
    (dgModuleNaturalConeRotationInput R D F G η)
    (dgModuleNaturalConnectingCone_boundary R D F G η)
    (dgModuleNaturalConeRotationInput_naturality R D F G η) x).trans
    (descRecovery R D _ _ _ _ _ _ _ _
      (dgModuleNaturalConeRotationInput_recovery R D F G η x)
      ((dgModuleNaturalConeArrow_comp R D (FS) (U) (V) (γ) (k) x).trans
        (congrArg (fun t => dgModuleNaturalConeArrow R D (FS) (U) (γ) x ≫ t)
          (dgModuleNaturalConeInr_arrow R D (CF) (U) (j) x))))

/-- 概要：元 connecting cone 全比較の各成分は K(D) の同値。
方針：同じ実 square の二縦辺の同値を元 cone 比較へ適用する。
規約：恒等辺と元回転比較を使用。使われ方：native 全比較の可逆性。 -/
lemma dgModuleNaturalConnectingCone_isIso (x : P) :
    IsIso ((moduleToHomotopy R D).map
      (dgModuleNaturalConeArrow R D (CD) (V) (θ) x)) := by
  rw [dgModuleNaturalConnectingCone_arrow]
  exact dgModuleConeMapOfHomotopy_isIso R D _ _ _ _ _
    (by infer_instance) (dgModuleNaturalConeRotationHom_isIso R D F G η x)
end SerrePositivity.KST.SConstruction
