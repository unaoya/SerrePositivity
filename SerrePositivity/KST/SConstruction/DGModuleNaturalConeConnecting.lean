module
public import SerrePositivity.KST.SConstruction.DGModuleNaturalConeBoundary
public import SerrePositivity.KST.SConstruction.DGHomGluingModuleConeConnecting

/-!
概要：元厳密比較の実 cone から元第一関手の shift への connecting 射を全次数で束ねる。
方針：元実 cone の全 Hom 作用に、第三成分零の connecting 自然性を適用する。
規約：元 connecting 射と shift 符号を保持する。
使われ方：同じ connecting cone と逆回転後合成比較の全関手族化。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory HomologicalComplex CochainComplex HomComplex
open DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {P : Type w} [DGCategory R P] (F G : DGFunctor R P (RightModule R D)) (η : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G)
local notation "a" => dgModuleNaturalConeArrow R D F G η
local notation "T" => dgModuleNaturalConeFunctor R D F G η

/-- 概要：元 connecting 射の全 Hom 複体上での自然性。
方針：同じ三成分 cone 作用の connecting 式を第三成分零へ特殊化する。
規約：元 shift の全次数作用を保つ。使われ方：connecting 射族の厳密自然変換。 -/
lemma dgModuleNaturalConeConnecting_naturality (x y : P) :
    (T).map x y ≫ eHomWhiskerLeft (Complex R)
      (ForgetEnrichment.of (Complex R) ((T).obj x)) (moduleConeConnecting R D (a y)) =
    (F.comp (moduleShiftDG R D 1)).map x y ≫ eHomWhiskerRight (Complex R)
      (moduleConeConnecting R D (a x))
      (ForgetEnrichment.of (Complex R) ((F.comp (moduleShiftDG R D 1)).obj y)) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  exact dgGluingModuleConeElement_connecting R D (a x) (a y)
    ((F.map x y).f n z) ((G.map x y).f n z)
    (0 : (moduleHom R D (F.obj x) (G.obj y)).X (n - 1)) (by omega)

/-- 概要：元 connecting 射を束ねた全次数厳密自然変換。
方針：元の全 Hom 自然性を同じ閉零射族へ適用する。
規約：成分を選び直さない。使われ方：同じ connecting cone の全 dg 関手。 -/
def dgModuleNaturalConeConnecting : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans (T) (F.comp (moduleShiftDG R D 1)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleStrictNatTransOfHomNaturality R D (fun x => moduleConeConnecting R D (a x))
    (dgModuleNaturalConeConnecting_naturality R D F G η)

/-- 概要：実 cone 構成へ渡す閉射は元 connecting 射そのもの。
方針：同じ閉射・閉元対応の逆律を使う。
規約：元の実 connecting cone を保持。使われ方：保存済み成分の始域照合。 -/
lemma dgModuleNaturalConeConnecting_arrow (x : P) :
    dgModuleNaturalConeArrow R D (T) (F.comp (moduleShiftDG R D 1))
      (dgModuleNaturalConeConnecting R D F G η) x = moduleConeConnecting R D (a x) := by
  change (closedHomEquiv R (RightModule R D) _ _).symm
    ((closedHomEquiv R (RightModule R D) _ _) (moduleConeConnecting R D (a x))) = _
  exact (closedHomEquiv R (RightModule R D) _ _).symm_apply_apply _
end SerrePositivity.KST.SConstruction
