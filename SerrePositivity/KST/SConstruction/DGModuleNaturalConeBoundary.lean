module
public import SerrePositivity.KST.SConstruction.DGModuleNaturalCone
public import SerrePositivity.KST.SConstruction.DGHomGluingConeRightRestriction
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Actions.DGModuleStrictNatTrans

/-!
概要：実 cone の標準右包含を、全次数自然な同じ dg 関手間の変換として保持する。
方針：元三成分作用の右制限式を実 Hom end へ持ち上げる。
規約：元包含を保持し、閉零次数だけの自然性に落とさない。
使われ方：実逆回転の合成比較に必要な指定境界の全関手族化。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory HomologicalComplex CochainComplex HomComplex
open DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

/-- 概要：元三成分 cone 作用の標準右包含への制限は元右成分。
方針：実 end の忠実な各評価で元 cochain 右制限式を使う。
規約：第三成分に条件を加えない。使われ方：指定右包含の全次数自然性。 -/
lemma dgGluingModuleConeElement_inr {M N P Q : ModuleCategory R D}
    (f : M ⟶ N) (g : P ⟶ Q) {n m : ℤ} (a) (b) (h) (hm : m + 1 = n) :
    (eHomWhiskerRight (Complex R) (moduleConeInr R D f) (moduleCone R D g)).f n
        (dgGluingModuleConeElement R D f g a b h hm) =
      (eHomWhiskerLeft (Complex R) N (moduleConeInr R D g)).f n b := by
  apply moduleHomElement_ext R D
    (M := ForgetEnrichment.to (Complex R) N)
    (N := ForgetEnrichment.to (Complex R) (moduleCone R D g))
  intro x
  apply (moduleHomWhiskerRight_apply_π R D (P := moduleCone R D g)
    (moduleConeInr R D f) n (dgGluingModuleConeElement R D f g a b h hm) x).trans
  apply Eq.trans _ (moduleHomWhiskerLeft_apply_π R D (T := N)
    (moduleConeInr R D g) n b x).symm
  rw [dgGluingModuleConeElement_π, moduleConeInr_eval, moduleConeInr_eval]
  exact dgGluingConeCochain_inr _ _ _ _ _ hm

variable {P : Type w} [DGCategory R P]
  (F G : DGFunctor R P (RightModule R D)) (η : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G)

/-- 概要：元の標準右包含を束ねた実厳密 dg 自然変換。
方針：元実 cone 作用の全次数右制限式を、そのまま自然性へ使う。
規約：元の包含を選び直さない。使われ方：指定 cone 境界の native 全比較。 -/
def dgModuleNaturalConeInr : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans G (dgModuleNaturalConeFunctor R D F G η) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleStrictNatTransOfHomNaturality R D
    (fun x => moduleConeInr R D (dgModuleNaturalConeArrow R D F G η x)) (fun x y => by
      apply HomologicalComplex.Hom.ext
      funext k
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      exact (dgGluingModuleConeElement_inr R D
        (dgModuleNaturalConeArrow R D F G η x) (dgModuleNaturalConeArrow R D F G η y)
        ((F.map x y).f k z) ((G.map x y).f k z)
        (0 : (moduleHom R D (F.obj x) (G.obj y)).X (k - 1)) (by omega)).symm)
end SerrePositivity.KST.SConstruction
