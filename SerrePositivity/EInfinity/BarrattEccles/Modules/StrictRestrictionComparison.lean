module

public import SerrePositivity.EInfinity.BarrattEccles.Modules.StrictAdjunction
public import SerrePositivity.EInfinity.Modules.DGGraphNerveAdjunction
public import SerrePositivity.EInfinity.Modules.DGResolutionAdjunction
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleDerivedUnderlyingIso
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleResolvedRawFactor

/-!
# 同じ厳密 BE 制限と graph 右随伴の全関手比較

概要：HA §4.2.3 の実拡大の右随伴を、指定した解像度付き制限に比較する。
方針：包含・解像度随伴と生の graph 随伴を合成し、右随伴の一意性を使う。
規約：同じ全関手・graph 比較・解像度を保持し、H⁰ の比較では代用しない。
使われ方：一般底上の加群族に渡す native な拡大・制限随伴。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet MonoidalClosed
open SerrePositivity.DifferentialGraded
open SerrePositivity.EInfinity.Modules
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
local notation "N" => _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
variable {A : Type u} [CommRing A]

/-- 概要：同じ graph 右随伴と解像度付き制限は全関手同型（HA §4.2.3）。
方針：拡大と包含の同じ比較に沿い二つの随伴を同じ左関手へ移す。
規約：同じ右随伴の一意性と指定解像度の retract を使う。
使われ方：同じ制限を持つ native な拡大・制限随伴。 -/
def strictModuleRestrictionComparison {X Y : (operad A).Algebra} (f : X ⟶ Y) :
    FunctorIso (strictModuleAdjointRestrict f) (strictModuleRestrict f) := by
  let D := dgAlgebraCategory A ((assocForget A).obj X)
  let E := dgAlgebraCategory A ((assocForget A).obj Y)
  let F := dgAlgebraMap A ((assocForget A).map f)
  let ID := semifreeInclusion A D
  let IE := semifreeInclusion A E
  let R := dgModuleRestriction A D E F.op
  have e : FunctorIso (strictModuleExtend f ≫ N IE)
      (N ID ≫ N (dgModuleExtension A D E F)) :=
    dgModuleDerivedFunctor_underlyingIso A D E (dgModuleExtension A D E F)
      (fun _ h => dgModuleExtension_homotopicallyProjective A D E F h)
  let a := (strictModuleGraphAdjunction f).comp (moduleResolutionAdjunction A E)
  let b := (moduleResolutionAdjunction A D).comp (graphRawAdjunction A D E F)
  have r : FunctorIso (moduleResolution A E ≫ strictModuleAdjointRestrict f)
      (N R ≫ moduleResolution A D) :=
    (qcatAdjunctionChangeLeft a e).rightAdjointFunctorIso b
  have rE := r.precomp (N IE)
  have ret : FunctorIso (N IE ≫ moduleResolution A E ≫ strictModuleAdjointRestrict f)
      (strictModuleAdjointRestrict f) := by
    simpa only [Category.assoc, Category.id_comp] using
      (dgModuleResolutionRetractIso A E).postcomp (strictModuleAdjointRestrict f)
  have raw : FunctorIso (strictModuleRestrict f)
      (N IE ≫ N R ≫ moduleResolution A D) := by
    change FunctorIso (dgModuleResolvedInfinity A _ D (IE.comp R))
      (N IE ≫ N R ≫ moduleResolution A D)
    have h := dgModuleResolvedInfinity_rawFactorIso A (SemifreeDGModules A E) D (IE.comp R)
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp] at h
    exact h
  exact ret.symm ≪≫ rE ≪≫ raw.symm

/-- 概要：同じ厳密射の実拡大と指定制限の native 随伴（HA §4.2.3）。
方針：graph 随伴を指定した全関手比較に沿って移す。
規約：元の二関手と両三角式を保持。使われ方：BE 加群族の拡大・制限。 -/
def strictModuleAdjunction {X Y : (operad A).Algebra} (f : X ⟶ Y) :
    QCatAdjunction (strictModuleExtend f) (strictModuleRestrict f) :=
  qcatAdjunctionChangeRight (strictModuleGraphAdjunction f) (strictModuleRestrictionComparison f)

/-- 概要：指定制限への比較は同じ随伴単位の移送を与える（HA §4.2.3）。
方針：関手同型に沿う随伴の既存の単位公式を適用する。
規約：全関手圏の射の等式。使われ方：同じ単位による加群の降下。 -/
lemma strictModuleAdjunction_unitHom {X Y : (operad A).Algebra} (f : X ⟶ Y) :
    (strictModuleAdjunction f).unitHom = (strictModuleGraphAdjunction f).unitHom ≫
      (hoFunctor.map ((pre (strictModuleExtend f)).app (strictModuleInfinity A X))).toFunctor.map
        (strictModuleRestrictionComparison f).hom :=
  qcatAdjunctionChangeRight_unitHom (strictModuleGraphAdjunction f)
    (strictModuleRestrictionComparison f)

end SerrePositivity.EInfinity.BarrattEccles
