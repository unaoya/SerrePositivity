module
public import SerrePositivity.DifferentialGraded.Endomorphism.EssentialImageTriangles
public import SerrePositivity.DifferentialGraded.Perfect.UniversalProperty

/-! # thick生成による主Perf同値とenhancement比較の本質的全射

全Hom擬同型とは別に、正則生成対象・三角閉性・retract閉性から本質的全射を証明する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (S : Set D) (E : PerfectDGModuleOver A D S)
variable (hgen : endomorphismThickGeneratesPerfect A D S E)
include hgen

lemma perfectEndomorphismEssentialImageIsTriangulated :
    (perfectEndomorphismHomToDerived A D S E).essImage.IsTriangulated := by
  let P := (perfectEndomorphismHomToDerived A D S E).essImage
  have : P.IsTriangulatedClosed₂ :=
    perfectEndomorphismEssentialImageTriangulatedClosed₂ A D S E hgen
  have : P.IsStableUnderRetracts :=
    perfectEndomorphismEssentialImageStableUnderRetracts A D S E hgen
  have : P.Nonempty := ObjectProperty.nonempty_of_prop
    (perfectEndomorphismEssentialImage_regular A D S E)
  have : P.ContainsZero := inferInstance
  exact ⟨⟩

lemma perfectEndomorphismEssentialImage_containsPerfect :
    modulePerfect A (EndomorphismObject E.val) ≤
      (perfectEndomorphismHomToDerived A D S E).essImage := by
  have := perfectEndomorphismEssentialImageIsTriangulated A D S E hgen
  have := perfectEndomorphismEssentialImageStableUnderRetracts A D S E hgen
  apply (modulePerfect_le_iff_generators A (EndomorphismObject E.val)
    (perfectEndomorphismHomToDerived A D S E).essImage).2
  intro b
  cases b
  exact perfectEndomorphismEssentialImage_regular A D S E

instance perfectEndomorphismHomToPerfectEssSurj :
    (perfectEndomorphismHomToPerfect A D S E hgen).EssSurj where
  mem_essImage Y := by
    obtain ⟨X, ⟨e⟩⟩ := perfectEndomorphismEssentialImage_containsPerfect A D S E hgen
      Y.obj Y.property
    exact ⟨X, ⟨(modulePerfect A (EndomorphismObject E.val)).isoMk e⟩⟩

instance perfectEndomorphismHomToPerfectIsEquivalence :
    (perfectEndomorphismHomToPerfect A D S E hgen).IsEquivalence where

/-- 主導来Homの実際の制限を順関手とする、主Perf間の同値。 -/
def perfectEndomorphismEquivalence :
    PerfectModuleCategoryOver A D S ≌ PerfectModuleCategory A (EndomorphismObject E.val) :=
  (perfectEndomorphismHomToPerfect A D S E hgen).asEquivalence

/-- U13のenhancement間のdg関手は、H⁰で本質的全射。 -/
instance perfectEndomorphismDGHomotopyEssSurj :
    (perfectEndomorphismDG A D S E hgen).onHomotopy.EssSurj where
  mem_essImage Y := by
    let F := (perfectEndomorphismDG A D S E hgen).onHomotopy
    let P := perfectDGModuleToPerfect A (EndomorphismObject E.val) Set.univ
    have : (F ⋙ P).EssSurj := Functor.essSurj_of_iso
      (perfectEndomorphismDerivedComparison A D S E hgen).symm
    obtain ⟨X, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (F ⋙ P) (P.obj Y)
    exact ⟨X, ⟨P.preimageIso e⟩⟩

/-- 全Hom擬同型とH⁰本質的全射を独立の証拠から組み合わせた準同値。 -/
lemma perfectEndomorphismDG_quasiEquivalence :
    QuasiEquivalence (perfectEndomorphismDG A D S E hgen) :=
  ⟨perfectEndomorphismDG_homQuasiIso A D S E hgen,
    perfectEndomorphismDGHomotopyEssSurj A D S E hgen⟩

end SerrePositivity.DifferentialGraded
