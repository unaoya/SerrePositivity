module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGSemifreeModules
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PinchedComplexModelComparison
public import SerrePositivity.DifferentialGraded.Module.Basic
public import SerrePositivity.DifferentialGraded.Derived.Projective

/-!
概要：半自由模型の全 Hom 複体を、固定入力ごとの実 ∞ 関手と実写像空間へ接続する。
方針：元の dg 代表関手を全 Hom のまま nerve に移し、pinched 複体模型と比較する。
規約：値域は複体の dg nerve。D(R) への移行・二変数の統合・随伴は別工程。
使われ方：β5 の導来 Hom の実モデルの入口。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
/-- 半自由対象の全 Hom 複体の値域を、始域と同じ対象宇宙に置く。 -/
abbrev dgHomComplexNerve (_D : Type v) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{u + 1, max (u + 1) v} (Complex R))
/-- 始域を固定した、全 Hom 複体の実共変 dg 関手。 -/
def dgSemifreeHomTargetDG (P : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) :
    DGFunctor R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{u + 1, max (u + 1) v} (Complex R)) :=
  (leftRepresentable R P).comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp R (Complex R))
/-- 終域を固定した、dg 反対圏からの全 Hom 複体の実 dg 関手。 -/
def dgSemifreeHomSourceDG (Q : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) :
    DGFunctor R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D)ᵒᵖ
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{u + 1, max (u + 1) v} (Complex R)) :=
  (representable R Q).toFunctor.comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp R (Complex R))
/-- 固定始域の全 Hom 複体は、全実単体を保つ共変 ∞ 関手。 -/
def dgSemifreeHomTargetInfinity (P : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R D ⟶ dgHomComplexNerve R D :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgSemifreeHomTargetDG R D P)
/-- 固定終域の全 Hom 複体は、dg 反対模型からの全実単体を保つ ∞ 関手。 -/
def dgSemifreeHomSourceInfinity (Q : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D)ᵒᵖ ⟶ dgHomComplexNerve R D :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgSemifreeHomSourceDG R D Q)
/-- 固定始域の実 ∞ 関手の値は、元の同じ全 Hom end 複体。 -/
lemma dgSemifreeHomTargetInfinity_vertex (P Q : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) :
    (dgSemifreeHomTargetInfinity R D P).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Q) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp R (Complex R)).obj (moduleHom R D P.val Q.val)) :
        (dgHomComplexNerve R D) _⦋0⦌) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex _ Q
/-- 半自由な始域の Hom は、任意の指定準同型を複体の準同型へ送る。 -/
lemma dgSemifreeHomTarget_quasiIso (P : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) {M N : ModuleCategory R D}
    (f : M ⟶ N) (hf : _root_.SerrePositivity.DifferentialGraded.moduleQuasiIso R D f) :
    QuasiIso (eHomWhiskerLeft (_root_.SerrePositivity.DifferentialGraded.Complex R) (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) P.val) f) :=
  _root_.SerrePositivity.DifferentialGraded.moduleSemifree_postcompose_quasiIso R D P.property f hf
/-- 半自由な二始域の準同型に沿う Hom の前合成も複体の準同型。 -/
lemma dgSemifreeHomSource_quasiIso (P Q : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D)
    (f : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) P.val ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) Q.val)
    (hf : _root_.SerrePositivity.DifferentialGraded.moduleQuasiIso R D f) (N : _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D) :
    QuasiIso (eHomWhiskerRight (_root_.SerrePositivity.DifferentialGraded.Complex R) f N) :=
  _root_.SerrePositivity.DifferentialGraded.moduleHomotopicallyProjective_precompose_quasiIso R D
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeModule_isProjective R D P) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeModule_isProjective R D Q) f hf N
/-- 半自由模型の実 pinched 写像空間は、同じ全 Hom 複体の実 pinched 模型と同型。 -/
def dgSemifreeHomMappingSpaceIso (P Q : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) P Q ≅
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, max (u + 1) v} (moduleHom R D P.val Q.val) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedComplexModelIso P Q
end SerrePositivity.InfinityCategories.Project.DerivedCategories
