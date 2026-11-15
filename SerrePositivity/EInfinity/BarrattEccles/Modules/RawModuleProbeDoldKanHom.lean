module

public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleProbeHomComparison
public import SerrePositivity.EInfinity.Modules.TensorDoldKanBifunctor
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.DoldKanIso
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HomotopyIsoTransport

/-!
# 元の probe 全族での選択済み Hom と dg Hom の同じ比較

概要：M10 の元の主 Hom end の実 Dold–Kan を共通 Hom へ全自然に比較する。
方針：同じ二変数同型を probe で前合成し、その逆と同じ共通 frame 比較を合成する。
規約：HA 1.3.1.13、Kerodon 2.5.9（Tag 00SC）、同じ比較射を保持する。
使われ方：モデルの選択済み Hom と指定 dg nerve Hom の全族の接続。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Opposite
open SerrePositivity.DifferentialGraded SerrePositivity.EInfinity.Modules
open SerrePositivity.InfinityCategories.HA.Section7_1_1
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes
open TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories
open DifferentialGradedCategories
variable (A : Type u) [CommRing A]

/-- 概要：同じ半自由 probe の元の dg Hom を実 Dold–Kan 二関手へ送る。
方針：元の全包含で同じ二関手を前合成する。
規約：HA 1.3.1.13、全 probe 射・全標的射。使われ方：比較の dg Hom 端点。 -/
def strictRawModuleProbeDoldKanHom (X : (operad A).Algebra) :
    (strictRawModuleProbeCategory A X)ᵒᵖ ⥤ strictRawModuleCategory A X ⥤ SSet.{u} :=
  (strictRawModuleProbeFunctor A X).op ⋙
    moduleDoldKanHomBifunctor A (dgAlgebraCategory A ((assocForget A).obj X))

/-- 概要：同じ全 probe のテンソル Hom と元の dg Hom は二変数自然に同型。
方針：同じ二変数同型を元の包含で前合成する。
規約：HA 1.3.1.13、同じ全単体。使われ方：同じ共通 Hom 比較への接続。 -/
def strictRawModuleProbeTensorDoldKanIso (X : (operad A).Algebra) :
    strictRawModuleProbeTensorHom A X ≅ strictRawModuleProbeDoldKanHom A X :=
  Functor.isoWhiskerLeft (strictRawModuleProbeFunctor A X).op
    (moduleTensorHomDoldKanBifunctorIso A (dgAlgebraCategory A ((assocForget A).obj X)))

/-- 概要：同じ dg Hom から同じ共通 frame Hom への実二変数自然変換。
方針：同じ端点同型の逆と同じ右比較を合成する。
規約：HA 1.3.1.13、元の射。使われ方：標準 Hom との全自然比較の右脚。 -/
def strictRawModuleProbeHomFromDoldKan (X : (operad A).Algebra) :
    strictRawModuleProbeDoldKanHom A X ⟶ strictRawModuleProbeCommonHom A X :=
  (strictRawModuleProbeTensorDoldKanIso A X).inv ≫ strictRawModuleProbeHomFromTensor A X

/-- 概要：元の dg Hom の同じ Dold–Kan 端点は Kan。
方針：既存の実 Dold–Kan Hom の Kan 性を使う。
規約：HA 1.3.1.13、元の主 Hom end。使われ方：実ホモトピー同値の合成。 -/
lemma strictRawModuleProbeDoldKanHom_kanComplex (X : (operad A).Algebra)
    (P : (strictRawModuleProbeCategory A X)ᵒᵖ) (N : strictRawModuleCategory A X) :
    SSet.KanComplex (((strictRawModuleProbeDoldKanHom A X).obj P).obj N) := by
  change SSet.KanComplex (doldKanHomSpace (R := A)
    (D := RightModule A (dgAlgebraCategory A ((assocForget A).obj X)))
    (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P.unop))
    (ForgetEnrichment.to (Complex A) N))
  infer_instance

/-- 概要：同じ dg Hom から同じ共通 Hom への実比較はホモトピー同値。
方針：同じ二変数同型の逆と検証済みの右比較のホモトピー逆を合成する。
規約：HA 1.3.1.13、任意の元の標的。使われ方：標準 Hom と元の dg Hom の接続。 -/
lemma strictRawModuleProbeHomFromDoldKan_homotopyEquivalence (X : (operad A).Algebra)
    (P : (strictRawModuleProbeCategory A X)ᵒᵖ) (N : strictRawModuleCategory A X) :
    IsSimplicialHomotopyEquivalence (((strictRawModuleProbeHomFromDoldKan A X).app P).app N) := by
  have := strictRawModuleProbeDoldKanHom_kanComplex A X P N
  have := strictRawModuleProbeTensorHom_kanComplex A X P N
  have := strictRawModuleProbeCommonHom_kanComplex A X P N
  let e := ((strictRawModuleProbeTensorDoldKanIso A X).app P).app N
  exact (simplicialHomotopyEquivalence_iso_hom e.symm).comp
    (strictRawModuleProbeHomFromTensor_homotopyEquivalence A X P N)

end SerrePositivity.EInfinity.BarrattEccles
