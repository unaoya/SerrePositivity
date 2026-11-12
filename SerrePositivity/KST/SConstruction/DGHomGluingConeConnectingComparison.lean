module
public import SerrePositivity.KST.SConstruction.DGHomGluingConeFunctor
public import SerrePositivity.KST.SConstruction.DGHomGluingModuleConeConnecting
public import SerrePositivity.DifferentialGraded.Functor.DGFunctorClosedComparison

/-!
概要：元 Hom gluing の全 cone 関手から元左対象の shift への dg 自然比較を構成する。
方針：元 connecting 射の成分と全三成分 Hom の自然性を同時に保持する。
規約：閉零射だけの自然性で代用しない。使われ方：LT 逆回転の全 Hom 比較。
-/
@[expose] public section
noncomputable section
universe u v w z
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
open DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (E : Type z) [DGCategory R E] [Small.{u} E]
  (p : DGFunctor R C E) (q : DGFunctor R D E)
local notation "L" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D (dgHomGluingBimodule R C D E p q)

/-- 概要：元実 perfect cone 関手を同じ全加群圏へ含める。
方針：元全 Hom を保つ包含を合成する。
規約：同じ実対象・写像を保持。使われ方：connecting 比較の始域。 -/
def dgHomGluingModuleConeFunctor : DGFunctor R (L) (RightModule R E) :=
  (dgHomGluingConeFunctor R C D E p q).comp (perfectDGModuleInclusion R E Set.univ)

/-- 概要：元左対象の代表加群の shift を同じ全次数で保持する。
方針：左射影・元 p・Yoneda・dg shift を合成する。
規約：同じ元左対象を保持。使われ方：connecting 比較の終域。 -/
def dgHomGluingShiftedLeftModuleFunctor : DGFunctor R (L) (RightModule R E) :=
  (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeft R C D (dgHomGluingBimodule R C D E p q)).comp p).comp
    (dgYoneda R E)).comp (moduleShiftDG R E 1)

/-- 概要：元 connecting 射は同じ全 cone dg 関手の全 Hom に関して自然。
方針：同じ Hom 元を元三成分に分け、実加群 end での等式を適用する。
規約：元第三成分を保持。使われ方：元閉射族の dg 自然変換への束ね。 -/
lemma dgHomGluingConeConnecting_hom_naturality (X Y : L) :
    (dgHomGluingModuleConeFunctor R C D E p q).map X Y ≫
      eHomWhiskerLeft (Complex R)
        (ForgetEnrichment.of (Complex R) ((dgHomGluingModuleConeFunctor R C D E p q).obj X))
        (moduleConeConnecting R E (dgHomGluingTargetModuleMap R C D E p q Y)) =
    (dgHomGluingShiftedLeftModuleFunctor R C D E p q).map X Y ≫
      eHomWhiskerRight (Complex R)
        (moduleConeConnecting R E (dgHomGluingTargetModuleMap R C D E p q X))
        (ForgetEnrichment.of (Complex R)
          ((dgHomGluingShiftedLeftModuleFunctor R C D E p q).obj Y)) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  exact dgGluingModuleConeElement_connecting R E
    (dgHomGluingTargetModuleMap R C D E p q X)
    (dgHomGluingTargetModuleMap R C D E p q Y)
    ((dgHomGluingConeLeftMap R C D E p q X Y).f n a)
    ((dgHomGluingConeRightMap R C D E p q X Y).f n a)
    ((dgHomGluingConePrimitive R C D E p q X Y).v n (n - 1) (by omega) a) (by omega)

/-- 概要：同じ実 connecting 射族を全次数自然な閉零 dg 比較へ束ねる。
方針：元全 Hom の自然性を単位パラメータの豊穣自然変換へ移す。
規約：同じ成分を保持。使われ方：逆 shift と指定 shift 比較の合成。 -/
def dgHomGluingConeConnectingComparison :
    GradedNatTrans ((Center.ofBraided (Complex R)).obj (𝟙_ (Complex R)))
      (dgHomGluingModuleConeFunctor R C D E p q)
      (dgHomGluingShiftedLeftModuleFunctor R C D E p q) :=
  dgFunctorClosedComparison R _ _
    (fun X => moduleConeConnecting R E (dgHomGluingTargetModuleMap R C D E p q X))
    (dgHomGluingConeConnecting_hom_naturality R C D E p q)
end SerrePositivity.KST.SConstruction
