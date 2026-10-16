module
public import SerrePositivity.DifferentialGraded.Perfect.EssentiallySmall
public import SerrePositivity.DifferentialGraded.Perfect.EnhancementLinear
public import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence

/-! # 小さい射影的perfect dg代表系

Perfの小さい通常モデルの各対象を、構成済みH⁰同値の逆関手で実際の射影的dg加群へ戻す。
その像の充満dg部分圏を取るので、全次数Hom endと微分を保持する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- Perfの小さいモデルから、実際の射影的perfect dg加群の代表を選ぶ。 -/
def perfectDGModuleRepresentative (S : Set D)
    (i : SmallModel.{u} (PerfectModuleCategoryOver A D S)) : PerfectDGModuleOver A D S :=
  ForgetEnrichment.to (Complex A)
    (((perfectDGModuleHomotopyEquivalence A D S).inverse.obj
      ((equivSmallModel (PerfectModuleCategoryOver A D S)).inverse.obj i)).as)

/-- 小さい添字族で選んだ射影的代表の像による充満dg部分圏。 -/
abbrev SmallPerfectDGModuleOver (S : Set D) :=
  DGFullSubcategory (PerfectDGModuleOver A D S) (Set.range (perfectDGModuleRepresentative A D S))

/-- 小さい代表系の豊穣構造。入れ子の充満部分圏に対する既存構造を明示的に公開する。 -/
instance smallPerfectDGModuleEnrichment (S : Set D) :
    DGCategory A (SmallPerfectDGModuleOver A D S) :=
  dgFullSubcategoryEnrichment A (PerfectDGModuleOver A D S)
    (Set.range (perfectDGModuleRepresentative A D S))

/-- 代表の像は小さい。全ての射影的perfect加群の対象型をsmallとは仮定しない。 -/
instance smallPerfectDGModuleOverSmall (S : Set D) : Small.{u} (SmallPerfectDGModuleOver A D S) :=
  small_range (perfectDGModuleRepresentative A D S)

/-- 小さい代表dg圏から、全射影的perfect dg加群への包含。 -/
def smallPerfectDGModuleInclusion (S : Set D) :
    DGFunctor A (SmallPerfectDGModuleOver A D S) (PerfectDGModuleOver A D S) :=
  dgFullSubcategoryInclusion A _ (Set.range (perfectDGModuleRepresentative A D S))

/-- 小さい代表のH⁰包含は充満。全Homを制限したことから従う。 -/
instance smallPerfectDGModuleInclusionHomotopyFull (S : Set D) :
    (smallPerfectDGModuleInclusion A D S).onHomotopy.Full := by
  dsimp [smallPerfectDGModuleInclusion]
  infer_instance

/-- 小さい代表のH⁰包含は忠実。同じHom複体上の境界を使う。 -/
instance smallPerfectDGModuleInclusionHomotopyFaithful (S : Set D) :
    (smallPerfectDGModuleInclusion A D S).onHomotopy.Faithful := by
  dsimp [smallPerfectDGModuleInclusion]
  infer_instance

/-- 小さいdg代表系のH⁰から主Perfへの比較。 -/
def smallPerfectDGModuleToPerfect (S : Set D) :
    HomotopyCategory A (SmallPerfectDGModuleOver A D S) ⥤ PerfectModuleCategoryOver A D S :=
  (smallPerfectDGModuleInclusion A D S).onHomotopy ⋙ perfectDGModuleToPerfect A D S

/-- 小さい代表比較は充満。二つの充満比較の合成である。 -/
instance smallPerfectDGModuleToPerfectFull (S : Set D) :
    (smallPerfectDGModuleToPerfect A D S).Full := by
  dsimp [smallPerfectDGModuleToPerfect]
  infer_instance

/-- 小さい代表比較は忠実。全Homの包含と射影的局所化計算を継承する。 -/
instance smallPerfectDGModuleToPerfectFaithful (S : Set D) :
    (smallPerfectDGModuleToPerfect A D S).Faithful := by
  dsimp [smallPerfectDGModuleToPerfect]
  infer_instance

/-- 各小さい添字に対応する、実際の小さいdg部分圏の対象。 -/
def smallPerfectDGModuleObject (S : Set D)
    (i : SmallModel.{u} (PerfectModuleCategoryOver A D S)) : SmallPerfectDGModuleOver A D S :=
  ⟨perfectDGModuleRepresentative A D S i, ⟨i, rfl⟩⟩

/-- 選択した代表のH⁰比較は、元のPerf同値の逆関手で選んだ対象へ戻る。 -/
lemma smallPerfectDGModuleObject_comparison (S : Set D)
    (i : SmallModel.{u} (PerfectModuleCategoryOver A D S)) :
    (smallPerfectDGModuleToPerfect A D S).obj
      ((toHomotopy A (SmallPerfectDGModuleOver A D S)).obj
        (ForgetEnrichment.of (Complex A) (smallPerfectDGModuleObject A D S i))) =
    (perfectDGModuleHomotopyEquivalence A D S).functor.obj
      ((perfectDGModuleHomotopyEquivalence A D S).inverse.obj
        ((equivSmallModel (PerfectModuleCategoryOver A D S)).inverse.obj i)) := rfl

/-- 任意のPerf対象は選択した小さい射影的代表のH⁰像と同型である。 -/
instance smallPerfectDGModuleToPerfectEssSurj (S : Set D) :
    (smallPerfectDGModuleToPerfect A D S).EssSurj where
  mem_essImage X := by
    let e := equivSmallModel.{u} (PerfectModuleCategoryOver A D S)
    let i := e.functor.obj X
    refine ⟨(toHomotopy A (SmallPerfectDGModuleOver A D S)).obj
      (ForgetEnrichment.of (Complex A) (smallPerfectDGModuleObject A D S i)), ⟨?_⟩⟩
    rw [smallPerfectDGModuleObject_comparison]
    exact (perfectDGModuleHomotopyEquivalence A D S).counitIso.app (e.inverse.obj i) ≪≫
      (e.unitIso.app X).symm

/-- 小さいdg代表系のH⁰と主Perfの比較は同値となる。 -/
instance smallPerfectDGModuleToPerfectIsEquivalence (S : Set D) :
    (smallPerfectDGModuleToPerfect A D S).IsEquivalence where

/-- 小さいdg enhancementのH⁰による主Perfの同値表示。 -/
def smallPerfectDGModuleHomotopyEquivalence (S : Set D) :
    HomotopyCategory A (SmallPerfectDGModuleOver A D S) ≌ PerfectModuleCategoryOver A D S :=
  (smallPerfectDGModuleToPerfect A D S).asEquivalence

/-- 小さい代表系からの比較もA線形。全Hom包含と既存線形比較の合成から得る。 -/
instance smallPerfectDGModuleToPerfectLinear (S : Set D) :
    (smallPerfectDGModuleToPerfect A D S).Linear A := by
  dsimp [smallPerfectDGModuleToPerfect]
  infer_instance

/-- 小さい代表比較の加法性は、包含と主Perf比較の合成から従う。 -/
instance smallPerfectDGModuleToPerfectAdditive (S : Set D) :
    (smallPerfectDGModuleToPerfect A D S).Additive := by
  dsimp [smallPerfectDGModuleToPerfect]
  infer_instance

/-- 小さい代表のH⁰包含は本質的全射。主Perfでの比較同型を完全忠実関手で引き戻す。 -/
instance smallPerfectDGModuleInclusionHomotopyEssSurj (S : Set D) :
    (smallPerfectDGModuleInclusion A D S).onHomotopy.EssSurj where
  mem_essImage X := by
    obtain ⟨Y, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage
      (smallPerfectDGModuleToPerfect A D S) ((perfectDGModuleToPerfect A D S).obj X)
    exact ⟨Y, ⟨(perfectDGModuleToPerfect A D S).preimageIso e⟩⟩

/-- 小さい代表のdg包含は準同値。各Homは恒等射で、H⁰は本質的全射である。 -/
lemma smallPerfectDGModuleInclusion_quasiEquivalence (S : Set D) :
    QuasiEquivalence (smallPerfectDGModuleInclusion A D S) := by
  refine ⟨?_, inferInstance⟩
  intro X Y
  change QuasiIso (𝟙 _)
  infer_instance

/-- 小さいenhancementのH⁰同値の順関手はA線形である。 -/
instance smallPerfectDGModuleHomotopyEquivalenceFunctorLinear (S : Set D) :
    (smallPerfectDGModuleHomotopyEquivalence A D S).functor.Linear A := by
  change (smallPerfectDGModuleToPerfect A D S).Linear A
  infer_instance

/-- 小さいenhancementのH⁰同値の順関手は加法的で、逆関手にも加法性が移る。 -/
instance smallPerfectDGModuleHomotopyEquivalenceFunctorAdditive (S : Set D) :
    (smallPerfectDGModuleHomotopyEquivalence A D S).functor.Additive := by
  change (smallPerfectDGModuleToPerfect A D S).Additive
  infer_instance

end SerrePositivity.DifferentialGraded
